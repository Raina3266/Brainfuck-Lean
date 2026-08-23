#[cfg(feature = "fuzzing")]
pub mod trace;

use crate::analysis::{Instr, Program};

#[cfg(feature = "fuzzing")]
pub use trace::{run_with_trace, trace_len, Trace, TraceEntry};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    FuelExhausted,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "fuzzing", derive(serde::Serialize, serde::Deserialize))]
pub struct TapeSnapshot {
    pub left: Vec<u64>,
    pub cur: u64,
    pub right: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "fuzzing", derive(serde::Serialize, serde::Deserialize))]
pub struct StateSnapshot {
    pub tape: TapeSnapshot,
    pub input: Vec<u64>,
    pub output: Vec<u64>,
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
        if let Ok(index) = usize::try_from(self.head) {
            if index >= self.nonnegative.len() {
                self.nonnegative.resize(index + 1, 0);
            }
            &mut self.nonnegative[index]
        } else {
            let flipped = negative_index(self.head);
            let index = usize::try_from(flipped).expect("negative head index fits in usize");
            if index >= self.negative.len() {
                self.negative.resize(index + 1, 0);
            }
            &mut self.negative[index]
        }
    }

    fn get(&self, position: i64) -> u64 {
        if let Ok(index) = usize::try_from(position) {
            self.nonnegative.get(index).copied().unwrap_or(0)
        } else {
            let flipped = negative_index(position);
            let index = usize::try_from(flipped).expect("negative position index fits in usize");
            self.negative.get(index).copied().unwrap_or(0)
        }
    }

    fn snapshot(&self) -> TapeSnapshot {
        let lowest = i64::try_from(self.negative.len())
            .ok()
            .and_then(i64::checked_neg)
            .expect("negative tape length fits in i64");
        let highest = i64::try_from(self.nonnegative.len()).expect("tape length fits in i64") - 1;
        let mut left = Vec::new();
        let mut position = self.head.checked_sub(1).expect("head - 1 fits in i64");
        while position >= lowest {
            left.push(self.get(position));
            position -= 1;
        }
        let mut right = Vec::new();
        let mut position = self.head.checked_add(1).expect("head + 1 fits in i64");
        while position <= highest {
            right.push(self.get(position));
            position += 1;
        }
        trim_trailing_zeros(&mut left);
        trim_trailing_zeros(&mut right);
        TapeSnapshot {
            left,
            cur: self.get(self.head),
            right,
        }
    }
}

fn negative_index(position: i64) -> i64 {
    position
        .checked_neg()
        .expect("position negation overflow")
        .checked_sub(1)
        .expect("position index overflow")
}

fn trim_trailing_zeros(cells: &mut Vec<u64>) {
    while let Some(value) = cells.pop() {
        if value != 0 {
            cells.push(value);
            break;
        }
    }
}

fn exec(
    program: &Program,
    input: &[u64],
    fuel: u64,
    #[cfg(feature = "fuzzing")] tracer: &mut dyn trace::Tracer,
) -> Result<StateSnapshot, RunError> {
    assert!(
        fuel <= i64::MAX as u64,
        "fuel budgets above i64::MAX are unsupported"
    );
    let mut tape = Tape::new();
    let mut pc: usize = 0;
    let mut next_input: usize = 0;
    let mut output = Vec::new();
    let mut remaining = fuel;
    #[cfg(feature = "fuzzing")]
    tracer.record(None, &tape, input, &output);
    while pc < program.instructions.len() {
        let instr = program.instructions[pc];
        if instr == Instr::EndLoop {
            pc = program.loop_jump_offset[pc] as usize;
            continue;
        }
        if remaining == 0 {
            return Err(RunError::FuelExhausted);
        }
        remaining -= 1;
        match instr {
            Instr::Inc => {
                let cell = tape.current();
                *cell = cell.wrapping_add(1);
            }
            Instr::Dec => {
                let cell = tape.current();
                *cell = cell.wrapping_sub(1);
            }
            Instr::Left => tape.head = tape.head.checked_sub(1).expect("tape head underflow"),
            Instr::Right => tape.head = tape.head.checked_add(1).expect("tape head overflow"),
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
        #[cfg(feature = "fuzzing")]
        tracer.record(Some(instr), &tape, &input[next_input..], &output);
        pc += 1;
    }
    Ok(StateSnapshot {
        tape: tape.snapshot(),
        input: input[next_input..].to_vec(),
        output,
    })
}

pub fn run(program: &Program, input: &[u64], fuel: u64) -> Result<Vec<u64>, RunError> {
    run_full(program, input, fuel).map(|state| state.output)
}

pub fn run_full(program: &Program, input: &[u64], fuel: u64) -> Result<StateSnapshot, RunError> {
    #[cfg(not(feature = "fuzzing"))]
    return exec(program, input, fuel);
    #[cfg(feature = "fuzzing")]
    return exec(program, input, fuel, &mut trace::NoTrace);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::parse;

    fn run_source(source: &str, input: &[u64], fuel: u64) -> Result<Vec<u64>, RunError> {
        run(&parse(source).unwrap(), input, fuel)
    }

    #[test]
    fn addition() {
        assert_eq!(run_source(",>,[-<+>]<.", &[3, 4], 1_000_000), Ok(vec![7]));
    }

    #[test]
    fn clear_loop_and_echo() {
        assert_eq!(run_source(",[-].", &[5], 1_000_000), Ok(vec![0]));
    }

    #[test]
    fn eof_reads_zero() {
        assert_eq!(run_source(",.,.", &[9], 1_000_000), Ok(vec![9, 0]));
    }

    #[test]
    fn wrapping_arithmetic() {
        assert_eq!(run_source("-.", &[], 1_000_000), Ok(vec![u64::MAX]));
    }

    #[test]
    fn moves_are_bi_infinite() {
        assert_eq!(run_source("+<<+>>.<<.", &[], 1_000_000), Ok(vec![1, 1]));
    }

    #[test]
    fn skipped_loop() {
        assert_eq!(run_source("[+].", &[], 1_000_000), Ok(vec![0]));
    }

    #[test]
    fn infinite_loop_exhausts_fuel() {
        assert_eq!(run_source("+[]", &[], 1000), Err(RunError::FuelExhausted));
    }

    /*
      Pins the exact fuel meter to the same budgets the Lean smoke tests
      assert by `rfl` (one unit per atom and per guard check, `]` free), so
      the two interpreters' metering cannot drift apart silently.
    */
    #[test]
    fn exact_fuel_metering() {
        assert!(run_source("++", &[], 2).is_ok());
        assert_eq!(run_source("++", &[], 1), Err(RunError::FuelExhausted));
        assert!(run_source(",[-].", &[5], 13).is_ok());
        assert_eq!(run_source(",[-].", &[5], 12), Err(RunError::FuelExhausted));
        assert!(run_source(",>,[-<+>]<.", &[3, 4], 26).is_ok());
        assert_eq!(
            run_source(",>,[-<+>]<.", &[3, 4], 25),
            Err(RunError::FuelExhausted)
        );
    }

    #[test]
    fn sufficient_fuel_succeeds() {
        assert_eq!(run_source(",>,[-<+>]<.", &[200, 300], 3000), Ok(vec![500]));
    }

    #[test]
    fn final_state_snapshot() {
        let program = parse(",>,[-<+>]<.").unwrap();
        let state = run_full(&program, &[3, 4, 9], 1_000_000).unwrap();
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
        let state = run_full(&program, &[], 1_000_000).unwrap();
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
        let state = run_full(&program, &[], 1_000_000).unwrap();
        assert_eq!(
            state.tape,
            TapeSnapshot {
                left: vec![2, 3],
                cur: 1,
                right: vec![]
            }
        );
    }
}
