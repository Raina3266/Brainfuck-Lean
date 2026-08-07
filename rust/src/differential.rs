use crate::analysis;
use crate::generate::FuzzCase;
use crate::interpreter::{self, RunError, StateSnapshot, TraceEntry};
use crate::oracle::{OracleClient, OracleRequest, OracleResponse};
use std::time::{Duration, Instant};

/*
  Trace comparison is skipped for runs longer than this many steps: a trace
  is quadratic in the run length (each entry carries the output so far), so
  unbounded traces cost minutes to serialize. Final states are still
  compared for every case, and the limit is on the *actual* step count
  (counted cheaply on the Rust side), not the fuel, so short runs with huge
  budgets keep full trace comparison.
*/
const TRACE_STEP_LIMIT: usize = 1_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Agree,
    Mismatch(String),
}

/// What the Rust implementation did with a case, shaped for comparison
/// against the oracle's answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RustOutcome {
    ParseError,
    Fuel,
    Halted(StateSnapshot),
}

/*
  Both timings measure only the bare (untraced) interpreter call: the Lean
  side reports its own monotonic-clock measurement (excluding JSON work),
  and the Rust side times `run_full`, excluding parsing and any traced
  re-run.
*/
#[derive(Debug, Clone)]
pub struct Timings {
    pub lean: Duration,
    pub rust: Duration,
}

/*
  The pure comparison policy, one arm per observable behaviour. The
  generator only produces balanced programs, so even a parse error must be
  bilateral; and both interpreters meter fuel identically (one unit per atom
  and per loop-guard check, `]` free), so fuel exhaustion must be bilateral
  too.
*/
pub fn outcome_verdict(lean: &OracleResponse, rust: &RustOutcome) -> Verdict {
    match (lean, rust) {
        (OracleResponse::BadRequest { error }, _) => {
            Verdict::Mismatch(format!("oracle rejected the request: {error}"))
        }
        (OracleResponse::ParseError, RustOutcome::ParseError) => Verdict::Agree,
        (OracleResponse::ParseError, _) => {
            Verdict::Mismatch("lean rejected a program rust accepted".to_string())
        }
        (_, RustOutcome::ParseError) => {
            Verdict::Mismatch("rust rejected a program lean accepted".to_string())
        }
        (OracleResponse::Fuel { .. }, RustOutcome::Fuel) => Verdict::Agree,
        (OracleResponse::Fuel { .. }, RustOutcome::Halted(state)) => Verdict::Mismatch(format!(
            "lean exhausted its fuel but rust halted with {state:?}"
        )),
        (OracleResponse::Ok { state, .. }, RustOutcome::Fuel) => Verdict::Mismatch(format!(
            "rust exhausted its fuel but lean halted with {state:?}"
        )),
        (OracleResponse::Ok { state, .. }, RustOutcome::Halted(rust_state)) => {
            if state == rust_state {
                Verdict::Agree
            } else {
                Verdict::Mismatch(format!(
                    "final states differ: lean {state:?}, rust {rust_state:?}"
                ))
            }
        }
    }
}

pub fn trace_verdict(lean: &[TraceEntry], rust: &[TraceEntry]) -> Verdict {
    for (index, (lean_entry, rust_entry)) in lean.iter().zip(rust.iter()).enumerate() {
        if lean_entry != rust_entry {
            return Verdict::Mismatch(format!(
                "traces diverge at entry {index}: lean {lean_entry:?}, rust {rust_entry:?}"
            ));
        }
    }
    if lean.len() != rust.len() {
        return Verdict::Mismatch(format!(
            "traces agree on a prefix but differ in length: lean {}, rust {}",
            lean.len(),
            rust.len()
        ));
    }
    Verdict::Agree
}

pub fn compare(oracle: &mut OracleClient, case: &FuzzCase) -> std::io::Result<(Verdict, Timings)> {
    let lean = oracle.query(&OracleRequest {
        program: &case.program,
        input: &case.input,
        fuel: case.fuel,
        trace: false,
    })?;
    let lean_nanos = match &lean {
        OracleResponse::Ok { nanos, .. } | OracleResponse::Fuel { nanos } => *nanos,
        _ => 0,
    };

    let parsed = analysis::parse(&case.program);
    let mut rust_elapsed = Duration::ZERO;
    let rust = match &parsed {
        Err(_) => RustOutcome::ParseError,
        Ok(program) => {
            let start = Instant::now();
            let result = interpreter::run_full(program, &case.input, Some(case.fuel));
            rust_elapsed = start.elapsed();
            match result {
                Err(RunError::FuelExhausted) => RustOutcome::Fuel,
                Ok(state) => RustOutcome::Halted(state),
            }
        }
    };
    let timings = Timings {
        lean: Duration::from_nanos(lean_nanos),
        rust: rust_elapsed,
    };

    let mut verdict = outcome_verdict(&lean, &rust);

    /*
      Second phase: when both sides halted in agreement and the run was
      short, re-query with tracing and compare every intermediate state.
    */
    if verdict == Verdict::Agree {
        if let (RustOutcome::Halted(_), Ok(program)) = (&rust, &parsed) {
            if interpreter::trace_len(program, &case.input, Some(case.fuel)) <= TRACE_STEP_LIMIT {
                let (rust_trace, _) =
                    interpreter::run_with_trace(program, &case.input, Some(case.fuel));
                let lean_traced = oracle.query(&OracleRequest {
                    program: &case.program,
                    input: &case.input,
                    fuel: case.fuel,
                    trace: true,
                })?;
                verdict = match &lean_traced {
                    OracleResponse::Ok {
                        trace: Some(trace), ..
                    } => trace_verdict(trace, &rust_trace.entries),
                    other => Verdict::Mismatch(format!(
                        "traced re-query answered differently: {other:?}"
                    )),
                };
            }
        }
    }
    Ok((verdict, timings))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::Instr;
    use crate::interpreter::TapeSnapshot;
    use arbitrary::{Arbitrary, Unstructured};

    fn snap(cur: u64) -> StateSnapshot {
        StateSnapshot {
            tape: TapeSnapshot {
                left: vec![],
                cur,
                right: vec![],
            },
            input: vec![],
            output: vec![],
        }
    }

    fn lean_ok(state: StateSnapshot) -> OracleResponse {
        OracleResponse::Ok {
            nanos: 0,
            state,
            trace: None,
        }
    }

    fn entry(instruction: Option<Instr>, cur: u64) -> TraceEntry {
        TraceEntry {
            instruction,
            state: snap(cur),
        }
    }

    #[test]
    fn matching_outcomes_agree() {
        assert_eq!(
            outcome_verdict(&OracleResponse::ParseError, &RustOutcome::ParseError),
            Verdict::Agree
        );
        assert_eq!(
            outcome_verdict(&OracleResponse::Fuel { nanos: 0 }, &RustOutcome::Fuel),
            Verdict::Agree
        );
        assert_eq!(
            outcome_verdict(&lean_ok(snap(7)), &RustOutcome::Halted(snap(7))),
            Verdict::Agree
        );
    }

    #[test]
    fn parse_disagreements_are_mismatches() {
        for rust in [RustOutcome::Fuel, RustOutcome::Halted(snap(0))] {
            assert!(matches!(
                outcome_verdict(&OracleResponse::ParseError, &rust),
                Verdict::Mismatch(_)
            ));
        }
        for lean in [OracleResponse::Fuel { nanos: 0 }, lean_ok(snap(0))] {
            assert!(matches!(
                outcome_verdict(&lean, &RustOutcome::ParseError),
                Verdict::Mismatch(_)
            ));
        }
    }

    #[test]
    fn fuel_disagreements_are_mismatches() {
        assert!(matches!(
            outcome_verdict(
                &OracleResponse::Fuel { nanos: 0 },
                &RustOutcome::Halted(snap(0))
            ),
            Verdict::Mismatch(_)
        ));
        assert!(matches!(
            outcome_verdict(&lean_ok(snap(0)), &RustOutcome::Fuel),
            Verdict::Mismatch(_)
        ));
    }

    #[test]
    fn differing_final_states_are_mismatches() {
        assert!(matches!(
            outcome_verdict(&lean_ok(snap(7)), &RustOutcome::Halted(snap(8))),
            Verdict::Mismatch(_)
        ));
    }

    #[test]
    fn bad_request_is_a_mismatch() {
        let bad = OracleResponse::BadRequest {
            error: "nope".to_string(),
        };
        assert!(matches!(
            outcome_verdict(&bad, &RustOutcome::Fuel),
            Verdict::Mismatch(_)
        ));
    }

    #[test]
    fn differing_traces_are_mismatches() {
        let base = vec![entry(None, 0), entry(Some(Instr::Inc), 1)];
        let differing = vec![entry(None, 0), entry(Some(Instr::Inc), 2)];
        let longer = vec![
            entry(None, 0),
            entry(Some(Instr::Inc), 1),
            entry(Some(Instr::Inc), 2),
        ];
        assert_eq!(trace_verdict(&base, &base), Verdict::Agree);
        assert!(matches!(
            trace_verdict(&base, &differing),
            Verdict::Mismatch(_)
        ));
        assert!(matches!(
            trace_verdict(&base, &longer),
            Verdict::Mismatch(_)
        ));
        assert!(matches!(
            trace_verdict(&longer, &base),
            Verdict::Mismatch(_)
        ));
    }

    /*
      Requires the Lean oracle: build it first with `lake build oracle` in the
      workspace root, then run `cargo test -- --ignored`.

      Divergent cases cost the whole fuel budget on both sides (they must,
      to agree on divergence), so the pool size is tuned against MAX_FUEL.
    */
    #[test]
    #[ignore]
    fn seeded_differential() {
        let mut oracle = OracleClient::spawn()
            .expect("failed to spawn the lean oracle; run `lake build oracle` first");
        let mut bytes = Vec::new();
        let mut state = 0x243F6A8885A308D3u64;
        for _ in 0..(1 << 15) {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            bytes.extend_from_slice(&state.to_le_bytes());
        }
        let mut compared = 0u32;
        for window in bytes.chunks(211) {
            let mut u = Unstructured::new(window);
            let Ok(case) = FuzzCase::arbitrary(&mut u) else {
                continue;
            };
            let (verdict, _) = compare(&mut oracle, &case).expect("oracle io failed");
            match verdict {
                Verdict::Agree => compared += 1,
                Verdict::Mismatch(reason) => {
                    panic!("interpreters disagree on {case:?}: {reason}")
                }
            }
        }
        println!("compared {compared} cases");
        assert!(compared > 50, "too few cases actually compared");
    }
}
