use super::{exec, Program, RunError, StateSnapshot, Tape};
use crate::analysis::Instr;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceEntry {
    pub instruction: Option<Instr>,
    pub state: StateSnapshot,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Trace {
    pub entries: Vec<TraceEntry>,
}

pub(super) trait Tracer {
    fn record(&mut self, instruction: Option<Instr>, tape: &Tape, input: &[u64], output: &[u64]);
}

pub(super) struct NoTrace;

impl Tracer for NoTrace {
    #[inline(always)]
    fn record(&mut self, _: Option<Instr>, _: &Tape, _: &[u64], _: &[u64]) {}
}

#[derive(Default)]
struct CountEntries(usize);

impl Tracer for CountEntries {
    #[inline(always)]
    fn record(&mut self, _: Option<Instr>, _: &Tape, _: &[u64], _: &[u64]) {
        self.0 += 1;
    }
}

impl Tracer for Trace {
    fn record(&mut self, instruction: Option<Instr>, tape: &Tape, input: &[u64], output: &[u64]) {
        self.entries.push(TraceEntry {
            instruction,
            state: StateSnapshot {
                tape: tape.snapshot(),
                input: input.to_vec(),
                output: output.to_vec(),
            },
        });
    }
}

pub fn run_with_trace(
    program: &Program,
    input: &[u64],
    fuel: u64,
) -> (Trace, Result<StateSnapshot, RunError>) {
    let mut trace = Trace::default();
    let result = exec(program, input, fuel, &mut trace);
    (trace, result)
}

/// The number of entries `run_with_trace` would record, without paying for
/// the snapshots (a trace's size is quadratic in the run length when the
/// output grows, so callers check this before tracing).
pub fn trace_len(program: &Program, input: &[u64], fuel: u64) -> usize {
    let mut counter = CountEntries::default();
    let _ = exec(program, input, fuel, &mut counter);
    counter.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::parse;
    use crate::interpreter::run_full;

    #[test]
    fn trace_records_all_states() {
        let program = parse(",[-]").unwrap();
        let (trace, result) = run_with_trace(&program, &[1], 1_000_000);
        assert!(result.is_ok());
        let simplified: Vec<(Option<Instr>, u64, Vec<u64>)> = trace
            .entries
            .iter()
            .map(|e| (e.instruction, e.state.tape.cur, e.state.input.clone()))
            .collect();
        assert_eq!(
            simplified,
            vec![
                (None, 0, vec![1]),
                (Some(Instr::Input), 1, vec![]),
                (Some(Instr::BeginLoop), 1, vec![]),
                (Some(Instr::Dec), 0, vec![]),
                (Some(Instr::BeginLoop), 0, vec![]),
            ]
        );
    }

    #[test]
    fn trace_final_entry_matches_run_full() {
        let program = parse(",>,[-<+>]<.").unwrap();
        let (trace, traced_result) = run_with_trace(&program, &[3, 4], 1_000_000);
        let full = run_full(&program, &[3, 4], 1_000_000).unwrap();
        assert_eq!(traced_result.unwrap(), full);
        assert_eq!(trace.entries.last().unwrap().state, full);
    }
}
