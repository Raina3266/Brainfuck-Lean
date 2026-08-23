use brainfuck::{analysis, interpreter};

use analysis::AnalysisError;
use ariadne::{Label, Report, ReportKind, Source};
use clap::{Args, Parser, Subcommand};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Parser)]
#[command(name = "brainfuck", about = "Brainfuck to Lean tooling")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Produce a standalone Lake project embedding a Brainfuck program
    Lower(LowerArgs),
    /// Execute a Brainfuck program with the fast unverified interpreter
    Run(RunArgs),
    /// Check a Brainfuck program for errors without running it
    Analyze(AnalyzeArgs),
}

#[derive(Args)]
struct LowerArgs {
    /// Path to the Brainfuck source file
    source: PathBuf,
    /// Name for the generated Lake project (and its directory)
    #[arg(long)]
    project_name: String,
    /// Directory in which the project directory is created
    #[arg(long)]
    output_path: PathBuf,
}

#[derive(Args)]
struct RunArgs {
    /// Path to the Brainfuck source file
    source: PathBuf,
    /// Input cells: 64-bit unsigned integers separated by single spaces
    #[arg(long, default_value = "")]
    input: String,
    /// Abort with an error after this many instructions
    #[arg(long)]
    fuel: Option<u64>,
}

#[derive(Args)]
struct AnalyzeArgs {
    /// Path to the Brainfuck source file
    source: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    match Cli::parse().command {
        Commands::Lower(args) => lower(args),
        Commands::Run(args) => run(args),
        Commands::Analyze(args) => analyze(args),
    }
}

fn analyze(args: AnalyzeArgs) -> Result<(), Box<dyn Error>> {
    let filename = args.source.display().to_string();
    let source = std::fs::read_to_string(&args.source)
        .map_err(|e| format!("cannot read {filename}: {e}"))?;
    match analysis::analyze(&source) {
        Ok(()) => Ok(()),
        Err(errors) => {
            render_analysis_errors(&filename, &source, &errors, true);
            let plural = if errors.len() == 1 { "error" } else { "errors" };
            Err(format!("{filename}: {} {plural} found", errors.len()).into())
        }
    }
}

fn render_analysis_errors(filename: &str, source: &str, errors: &[AnalysisError], fatal: bool) {
    let kind = if fatal {
        ReportKind::Error
    } else {
        ReportKind::Warning
    };
    for error in errors {
        let AnalysisError::UnmatchedBracket { is_opening, span } = error;
        let which = if *is_opening { "opening" } else { "closing" };
        Report::build(kind, filename, span.start)
            .with_message(format!("unmatched {which} bracket"))
            .with_label(
                Label::new((filename, span.clone()))
                    .with_message(format!("this {which} bracket has no match")),
            )
            .finish()
            .eprint((filename, Source::from(source)))
            .expect("failed to render diagnostic");
    }
}

fn run(args: RunArgs) -> Result<(), Box<dyn Error>> {
    let filename = args.source.display().to_string();
    let source = std::fs::read_to_string(&args.source)
        .map_err(|e| format!("cannot read {filename}: {e}"))?;

    let program = match analysis::parse(&source) {
        Ok(program) => program,
        Err(errors) => {
            render_analysis_errors(&filename, &source, &errors, true);
            return Err(format!("{filename}: invalid brainfuck program").into());
        }
    };

    let input = parse_input(&args.input)?;
    let fuel = args.fuel.unwrap_or(i64::MAX as u64);
    match interpreter::run(&program, &input, fuel) {
        Ok(output) => {
            let rendered: Vec<String> = output.iter().map(u64::to_string).collect();
            println!("{}", rendered.join(" "));
            Ok(())
        }
        Err(interpreter::RunError::FuelExhausted) => {
            Err(format!("fuel exhausted after {fuel} instructions").into())
        }
    }
}

fn parse_input(input: &str) -> Result<Vec<u64>, Box<dyn Error>> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Ok(Vec::new());
    }
    trimmed
        .split(' ')
        .map(|cell| {
            cell.parse::<u64>()
                .map_err(|e| format!("invalid input cell {cell:?}: {e}").into())
        })
        .collect()
}

fn lean_workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate directory has a parent")
        .to_path_buf()
}

fn run_command(description: &str, command: &mut Command) -> Result<(), Box<dyn Error>> {
    let status = command.status()?;
    if !status.success() {
        return Err(format!("{description} failed with {status}").into());
    }
    Ok(())
}

fn find_root_module(project_dir: &Path) -> Result<PathBuf, Box<dyn Error>> {
    let mut candidates = Vec::new();
    for entry in std::fs::read_dir(project_dir)? {
        let path = entry?.path();
        let is_lean = path.extension().is_some_and(|ext| ext == "lean");
        let is_lakefile = path.file_name().is_some_and(|name| name == "lakefile.lean");
        if is_lean && !is_lakefile {
            candidates.push(path);
        }
    }
    match candidates.as_slice() {
        [only] => Ok(only.clone()),
        _ => Err(format!(
            "expected exactly one root module in {}, found {}",
            project_dir.display(),
            candidates.len()
        )
        .into()),
    }
}

fn lower(args: LowerArgs) -> Result<(), Box<dyn Error>> {
    let filename = args.source.display().to_string();
    let source_text = std::fs::read_to_string(&args.source)
        .map_err(|e| format!("cannot read {filename}: {e}"))?;

    if let Err(errors) = analysis::analyze(&source_text) {
        render_analysis_errors(&filename, &source_text, &errors, false);
        eprintln!(
            "warning: {filename} has unmatched brackets; the generated project will fail to build"
        );
    }

    let workspace_root = lean_workspace_root();
    let toolchain = std::fs::read_to_string(workspace_root.join("lean-toolchain"))?;
    let toolchain = toolchain.trim();

    std::fs::create_dir_all(&args.output_path)?;
    run_command(
        "lake new",
        Command::new("lake")
            .arg(format!("+{toolchain}"))
            .args(["new", &args.project_name, "lib"])
            .current_dir(&args.output_path),
    )?;
    let project_dir = args.output_path.join(&args.project_name);

    std::fs::write(project_dir.join("lean-toolchain"), format!("{toolchain}\n"))?;

    let lakefile = project_dir.join("lakefile.toml");
    let mut lakefile_text = std::fs::read_to_string(&lakefile)?;
    lakefile_text.push_str(&format!(
        "\n[[require]]\nname = \"brainfuck_assignment\"\npath = \"{}\"\n",
        workspace_root.display()
    ));
    std::fs::write(&lakefile, lakefile_text)?;

    let stem = args
        .source
        .file_stem()
        .ok_or("source path has no file name")?
        .to_string_lossy();
    let bf_name = format!("{stem}.bf");
    std::fs::write(project_dir.join(&bf_name), &source_text)?;

    let root_module = find_root_module(&project_dir)?;
    let module_dir = root_module.with_extension("");
    if module_dir.is_dir() {
        std::fs::remove_dir_all(&module_dir)?;
    }
    std::fs::write(
        &root_module,
        format!("import Brainfuck\n\nopen Brainfuck\n\ndef program : Program := embed_bf! \"./{bf_name}\"\n"),
    )?;

    run_command(
        "lake update",
        Command::new("lake").arg("update").current_dir(&project_dir),
    )?;
    let _ = Command::new("lake")
        .args(["exe", "cache", "get"])
        .current_dir(&project_dir)
        .status();
    run_command(
        "lake build",
        Command::new("lake").arg("build").current_dir(&project_dir),
    )?;

    println!(
        "lowered {} into {}",
        args.source.display(),
        project_dir.display()
    );
    Ok(())
}
