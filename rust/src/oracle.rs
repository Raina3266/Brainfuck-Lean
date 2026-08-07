use crate::interpreter::{StateSnapshot, TraceEntry};
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

#[derive(Debug, Serialize)]
pub struct OracleRequest<'a> {
    pub program: &'a str,
    pub input: &'a [u64],
    pub fuel: u64,
    pub trace: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(tag = "status")]
pub enum OracleResponse {
    #[serde(rename = "parseError")]
    ParseError,
    #[serde(rename = "fuel")]
    Fuel { nanos: u64 },
    #[serde(rename = "ok")]
    Ok {
        nanos: u64,
        state: StateSnapshot,
        #[serde(default)]
        trace: Option<Vec<TraceEntry>>,
    },
    #[serde(rename = "badRequest")]
    BadRequest { error: String },
}

pub struct OracleClient {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

pub fn default_oracle_path() -> PathBuf {
    if let Ok(path) = std::env::var("BRAINFUCK_ORACLE") {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate directory has a parent")
        .join(".lake/build/bin/oracle")
}

impl OracleClient {
    pub fn spawn() -> std::io::Result<Self> {
        Self::spawn_at(&default_oracle_path())
    }

    pub fn spawn_at(path: &std::path::Path) -> std::io::Result<Self> {
        let mut child = Command::new(path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().expect("stdin was piped");
        let stdout = BufReader::new(child.stdout.take().expect("stdout was piped"));
        Ok(OracleClient {
            child,
            stdin,
            stdout,
        })
    }

    pub fn query(&mut self, request: &OracleRequest) -> std::io::Result<OracleResponse> {
        let mut line = serde_json::to_string(request)?;
        line.push('\n');
        self.stdin.write_all(line.as_bytes())?;
        self.stdin.flush()?;
        let mut response = String::new();
        if self.stdout.read_line(&mut response)? == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "oracle process closed its stdout",
            ));
        }
        Ok(serde_json::from_str(response.trim())?)
    }
}

impl Drop for OracleClient {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
