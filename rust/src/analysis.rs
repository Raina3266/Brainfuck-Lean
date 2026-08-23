#[cfg(feature = "fuzzing")]
use serde::{Deserialize, Serialize};
use std::ops::Range;

pub type Span = Range<usize>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnalysisError {
    UnmatchedBracket { is_opening: bool, span: Span },
}

impl AnalysisError {
    pub fn span(&self) -> &Span {
        match self {
            AnalysisError::UnmatchedBracket { span, .. } => span,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "fuzzing", derive(Serialize, Deserialize))]
pub enum Instr {
    #[cfg_attr(feature = "fuzzing", serde(rename = "+"))]
    Inc,
    #[cfg_attr(feature = "fuzzing", serde(rename = "-"))]
    Dec,
    #[cfg_attr(feature = "fuzzing", serde(rename = "<"))]
    Left,
    #[cfg_attr(feature = "fuzzing", serde(rename = ">"))]
    Right,
    #[cfg_attr(feature = "fuzzing", serde(rename = ","))]
    Input,
    #[cfg_attr(feature = "fuzzing", serde(rename = "."))]
    Output,
    #[cfg_attr(feature = "fuzzing", serde(rename = "["))]
    BeginLoop,
    #[cfg_attr(feature = "fuzzing", serde(rename = "]"))]
    EndLoop,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub instructions: Vec<Instr>,
    pub loop_jump_offset: Vec<u32>,
}

trait Builder {
    fn len(&self) -> u32;
    fn push(&mut self, instr: Instr);
    fn set_jump(&mut self, open: u32, close: u32);
}

struct CountOnly {
    count: u32,
}

impl Builder for CountOnly {
    fn len(&self) -> u32 {
        self.count
    }

    fn push(&mut self, _instr: Instr) {
        self.count += 1;
    }

    fn set_jump(&mut self, _open: u32, _close: u32) {}
}

impl Builder for Program {
    fn len(&self) -> u32 {
        self.instructions.len() as u32
    }

    fn push(&mut self, instr: Instr) {
        self.instructions.push(instr);
        self.loop_jump_offset.push(0);
    }

    fn set_jump(&mut self, open: u32, close: u32) {
        self.loop_jump_offset[open as usize] = close;
        self.loop_jump_offset[close as usize] = open;
    }
}

fn scan<B: Builder>(source: &str, builder: &mut B) -> Vec<AnalysisError> {
    let mut errors = Vec::new();
    let mut open_brackets: Vec<(u32, usize)> = Vec::new();
    for (char_offset, character) in source.chars().enumerate() {
        let instr = match character {
            '+' => Instr::Inc,
            '-' => Instr::Dec,
            '<' => Instr::Left,
            '>' => Instr::Right,
            ',' => Instr::Input,
            '.' => Instr::Output,
            '[' => Instr::BeginLoop,
            ']' => Instr::EndLoop,
            _ => continue,
        };
        let instr_offset = builder.len();
        builder.push(instr);
        match instr {
            Instr::BeginLoop => open_brackets.push((instr_offset, char_offset)),
            Instr::EndLoop => match open_brackets.pop() {
                Some((open_offset, _)) => builder.set_jump(open_offset, instr_offset),
                None => errors.push(AnalysisError::UnmatchedBracket {
                    is_opening: false,
                    span: char_offset..char_offset + 1,
                }),
            },
            _ => {}
        }
    }
    for (_, char_offset) in open_brackets {
        errors.push(AnalysisError::UnmatchedBracket {
            is_opening: true,
            span: char_offset..char_offset + 1,
        });
    }
    errors.sort_by_key(|error| error.span().start);
    errors
}

pub fn analyze(brainfuck: &str) -> Result<(), Vec<AnalysisError>> {
    let mut counter = CountOnly { count: 0 };
    let errors = scan(brainfuck, &mut counter);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

pub fn parse(brainfuck: &str) -> Result<Program, Vec<AnalysisError>> {
    let mut program = Program::default();
    let errors = scan(brainfuck, &mut program);
    if errors.is_empty() {
        Ok(program)
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_instructions_and_jumps() {
        let program = parse("+[->+<]. comment").unwrap();
        assert_eq!(
            program.instructions,
            vec![
                Instr::Inc,
                Instr::BeginLoop,
                Instr::Dec,
                Instr::Right,
                Instr::Inc,
                Instr::Left,
                Instr::EndLoop,
                Instr::Output,
            ]
        );
        assert_eq!(program.loop_jump_offset[1], 6);
        assert_eq!(program.loop_jump_offset[6], 1);
    }

    #[test]
    fn nested_loops_jump_to_their_own_match() {
        let program = parse("[[]]").unwrap();
        assert_eq!(program.loop_jump_offset, vec![3, 2, 1, 0]);
    }

    #[test]
    fn reports_unmatched_closing() {
        let errors = analyze("+]").unwrap_err();
        assert_eq!(
            errors,
            vec![AnalysisError::UnmatchedBracket {
                is_opening: false,
                span: 1..2,
            }]
        );
    }

    #[test]
    fn reports_all_errors_in_span_order() {
        let errors = analyze("][").unwrap_err();
        assert_eq!(
            errors,
            vec![
                AnalysisError::UnmatchedBracket {
                    is_opening: false,
                    span: 0..1,
                },
                AnalysisError::UnmatchedBracket {
                    is_opening: true,
                    span: 1..2,
                },
            ]
        );
    }

    fn corpus_sources(subdir: &str) -> Vec<(std::path::PathBuf, String)> {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join(subdir);
        let mut sources = Vec::new();
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|ext| ext == "bf") {
                let text = std::fs::read_to_string(&path).unwrap();
                sources.push((path, text));
            }
        }
        sources
    }

    #[test]
    fn valid_corpus_is_accepted() {
        let sources = corpus_sources("corpus");
        assert!(!sources.is_empty());
        for (path, text) in sources {
            assert!(analyze(&text).is_ok(), "{} should be valid", path.display());
        }
    }

    #[test]
    fn invalid_corpus_is_rejected() {
        let sources = corpus_sources("corpus/invalid");
        assert!(sources.len() >= 5);
        for (path, text) in sources {
            assert!(
                analyze(&text).is_err(),
                "{} should be invalid",
                path.display()
            );
        }
    }

    #[test]
    fn analyze_and_parse_agree() {
        for source in ["", "+-<>.,", "[[]]", "]", "[", "a[b]c", "[]]["] {
            assert_eq!(
                analyze(source).is_ok(),
                parse(source).is_ok(),
                "disagreement on {source:?}"
            );
        }
    }
}
