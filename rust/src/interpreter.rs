use crate::analysis::{Instr, Program};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    FuelExhausted,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TapeSnapshot {
    pub left: Vec<u64>,
    pub cur: u64,
    pub right: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateSnapshot {
    pub tape: TapeSnapshot,
    pub input: Vec<u64>,
    pub output: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceEntry {
    pub instruction: Option<Instr>,
    pub state: StateSnapshot,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Trace {
    pub entries: Vec<TraceEntry>,
}

trait Tracer {
    fn record(&mut self, instruction: Option<Instr>, tape: &Tape, input: &[u64], output: &[u64]);
}

struct NoTrace;

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

struct Tape {
    negative: Vec<u64>,
    nonnegative: Vec<u64>,
    head: i64,
}

impl Tape {
    fn new() -> Self {
        Tape {
            negative: Vec::new(),
            nonnegative: vec![0],
            head: 0,
        }
    }

    fn current(&mut self) -> &mut u64 {
        if self.head >= 0 {
            let index = self.head as usize;
            if index >= self.nonnegative.len() {
                self.nonnegative.resize(index + 1, 0);
            }
            &mut self.nonnegative[index]
        } else {
            let index = (-self.head - 1) as usize;
            if index >= self.negative.len() {
                self.negative.resize(index + 1, 0);
            }
            &mut self.negative[index]
        }
    }

    fn get(&self, position: i64) -> u64 {
        if position >= 0 {
            self.nonnegative
                .get(position as usize)
                .copied()
                .unwrap_or(0)
        } else {
            self.negative
                .get((-position - 1) as usize)
                .copied()
                .unwrap_or(0)
        }
    }

    fn snapshot(&self) -> TapeSnapshot {
        let lowest = -(self.negative.len() as i64);
        let highest = self.nonnegative.len() as i64 - 1;
        let mut left: Vec<u64> = (lowest..self.head).rev().map(|p| self.get(p)).collect();
        let mut right: Vec<u64> = (self.head + 1..=highest).map(|p| self.get(p)).collect();
        trim_trailing_zeros(&mut left);
        trim_trailing_zeros(&mut right);
        TapeSnapshot {
            left,
            cur: self.get(self.head),
            right,
        }
    }
}

fn trim_trailing_zeros(cells: &mut Vec<u64>) {
    while cells.last() == Some(&0) {
        cells.pop();
    }
}

fn exec<T: Tracer>(
    program: &Program,
    input: &[u64],
    fuel: Option<u64>,
    tracer: &mut T,
) -> Result<StateSnapshot, RunError> {
    let mut tape = Tape::new();
    let mut pc: usize = 0;
    let mut next_input: usize = 0;
    let mut output = Vec::new();
    let mut remaining = fuel;
    tracer.record(None, &tape, input, &output);
    while pc < program.instructions.len() {
        let instr = program.instructions[pc];
        if instr == Instr::EndLoop {
            pc = program.loop_jump_offset[pc] as usize;
            continue;
        }
        if let Some(budget) = remaining.as_mut() {
            if *budget == 0 {
                return Err(RunError::FuelExhausted);
            }
            *budget -= 1;
        }
        match instr {
            Instr::Inc => {
                let cell = tape.current();
                *cell = cell.wrapping_add(1);
            }
            Instr::Dec => {
                let cell = tape.current();
                *cell = cell.wrapping_sub(1);
            }
            Instr::Left => tape.head -= 1,
            Instr::Right => tape.head += 1,
            Instr::Input => {
                let value = input.get(next_input).copied().unwrap_or(0);
                next_input = (next_input + 1).min(input.len());
                *tape.current() = value;
            }
            Instr::Output => output.push(*tape.current()),
            Instr::BeginLoop => {
                if *tape.current() == 0 {
                    pc = program.loop_jump_offset[pc] as usize;
                }
            }
            Instr::EndLoop => unreachable!(),
        }
        tracer.record(Some(instr), &tape, &input[next_input..], &output);
        pc += 1;
    }
    Ok(StateSnapshot {
        tape: tape.snapshot(),
        input: input[next_input..].to_vec(),
        output,
    })
}

pub fn run(program: &Program, input: &[u64], fuel: Option<u64>) -> Result<Vec<u64>, RunError> {
    run_full(program, input, fuel).map(|state| state.output)
}

pub fn run_full(
    program: &Program,
    input: &[u64],
    fuel: Option<u64>,
) -> Result<StateSnapshot, RunError> {
    exec(program, input, fuel, &mut NoTrace)
}

pub fn run_with_trace(
    program: &Program,
    input: &[u64],
    fuel: Option<u64>,
) -> (Trace, Result<StateSnapshot, RunError>) {
    let mut trace = Trace::default();
    let result = exec(program, input, fuel, &mut trace);
    (trace, result)
}

/// The number of entries `run_with_trace` would record, without paying for
/// the snapshots (a trace's size is quadratic in the run length when the
/// output grows, so callers check this before tracing).
pub fn trace_len(program: &Program, input: &[u64], fuel: Option<u64>) -> usize {
    let mut counter = CountEntries::default();
    let _ = exec(program, input, fuel, &mut counter);
    counter.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::parse;

    fn run_source(source: &str, input: &[u64], fuel: Option<u64>) -> Result<Vec<u64>, RunError> {
        run(&parse(source).unwrap(), input, fuel)
    }

    #[test]
    fn addition() {
        assert_eq!(run_source(",>,[-<+>]<.", &[3, 4], None), Ok(vec![7]));
    }

    #[test]
    fn clear_loop_and_echo() {
        assert_eq!(run_source(",[-].", &[5], None), Ok(vec![0]));
    }

    #[test]
    fn eof_reads_zero() {
        assert_eq!(run_source(",.,.", &[9], None), Ok(vec![9, 0]));
    }

    #[test]
    fn wrapping_arithmetic() {
        assert_eq!(run_source("-.", &[], None), Ok(vec![u64::MAX]));
    }

    #[test]
    fn moves_are_bi_infinite() {
        assert_eq!(run_source("+<<+>>.<<.", &[], None), Ok(vec![1, 1]));
    }

    #[test]
    fn skipped_loop() {
        assert_eq!(run_source("[+].", &[], None), Ok(vec![0]));
    }

    #[test]
    fn infinite_loop_exhausts_fuel() {
        assert_eq!(
            run_source("+[]", &[], Some(1000)),
            Err(RunError::FuelExhausted)
        );
    }

    /*
      Pins the exact fuel meter to the same budgets the Lean smoke tests
      assert by `rfl` (one unit per atom and per guard check, `]` free), so
      the two interpreters' metering cannot drift apart silently.
    */
    #[test]
    fn exact_fuel_metering() {
        assert!(run_source("++", &[], Some(2)).is_ok());
        assert_eq!(run_source("++", &[], Some(1)), Err(RunError::FuelExhausted));
        assert!(run_source(",[-].", &[5], Some(13)).is_ok());
        assert_eq!(
            run_source(",[-].", &[5], Some(12)),
            Err(RunError::FuelExhausted)
        );
        assert!(run_source(",>,[-<+>]<.", &[3, 4], Some(26)).is_ok());
        assert_eq!(
            run_source(",>,[-<+>]<.", &[3, 4], Some(25)),
            Err(RunError::FuelExhausted)
        );
    }

    #[test]
    fn sufficient_fuel_succeeds() {
        assert_eq!(
            run_source(",>,[-<+>]<.", &[200, 300], Some(3000)),
            Ok(vec![500])
        );
    }

    #[test]
    fn final_state_snapshot() {
        let program = parse(",>,[-<+>]<.").unwrap();
        let state = run_full(&program, &[3, 4, 9], None).unwrap();
        assert_eq!(
            state,
            StateSnapshot {
                tape: TapeSnapshot {
                    left: vec![],
                    cur: 7,
                    right: vec![]
                },
                input: vec![9],
                output: vec![7],
            }
        );
    }

    #[test]
    fn snapshot_trims_trailing_zeros() {
        let program = parse("+>+>>><<").unwrap();
        let state = run_full(&program, &[], None).unwrap();
        assert_eq!(
            state.tape,
            TapeSnapshot {
                left: vec![1, 1],
                cur: 0,
                right: vec![]
            }
        );
    }

    #[test]
    fn snapshot_left_is_nearest_first() {
        let program = parse("+++>++>+").unwrap();
        let state = run_full(&program, &[], None).unwrap();
        assert_eq!(
            state.tape,
            TapeSnapshot {
                left: vec![2, 3],
                cur: 1,
                right: vec![]
            }
        );
    }

    #[test]
    fn trace_records_all_states() {
        let program = parse(",[-]").unwrap();
        let (trace, result) = run_with_trace(&program, &[1], None);
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
        let (trace, traced_result) = run_with_trace(&program, &[3, 4], None);
        let full = run_full(&program, &[3, 4], None).unwrap();
        assert_eq!(traced_result.unwrap(), full);
        assert_eq!(trace.entries.last().unwrap().state, full);
    }
}
