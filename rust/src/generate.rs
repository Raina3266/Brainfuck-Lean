use arbitrary::{Arbitrary, Unstructured};

const MAX_INPUT_LEN: usize = 8;
const MAX_FUEL: u64 = 1_000_000;
const MAX_COMMENT_LEN: usize = 30;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuzzCase {
    pub program: String,
    pub input: Vec<u64>,
    pub fuel: u64,
}

impl<'a> Arbitrary<'a> for FuzzCase {
    /*
      Fuel and input are drawn first: program generation is entropy-bounded
      (its grammar only stops early with probability 5% per step) and would
      otherwise leave nothing behind, pinning fuel to 0 and input to [].
    */
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let fuel = u.int_in_range(0..=MAX_FUEL)?;
        let input = arbitrary_input(u)?;
        let program = arbitrary_program(u)?;
        Ok(FuzzCase {
            program,
            input,
            fuel,
        })
    }
}

const ATOMS: [char; 6] = ['+', '-', '<', '>', ',', '.'];

const COMMENT_CHARS: &[u8] =
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 \n#!?:;'()*=@_";

/*
  A recursive grammar rather than a target length. Each step chooses:
  - 50%: an atom (uniform among the six)
  - 25%: a loop, with its body generated recursively
  - 20%: a run of 0..=30 non-brainfuck characters (a comment)
  -  5%: end this block
  Running out of entropy also ends the block, so generation always
  terminates and programs are balanced by construction.
*/
fn arbitrary_program(u: &mut Unstructured) -> arbitrary::Result<String> {
    let mut program = String::new();
    arbitrary_block(u, &mut program)?;
    Ok(program)
}

fn arbitrary_block(u: &mut Unstructured, out: &mut String) -> arbitrary::Result<()> {
    loop {
        if u.is_empty() {
            return Ok(());
        }
        match u.int_in_range(0u32..=99)? {
            0..=49 => out.push(*u.choose(&ATOMS)?),
            50..=74 => {
                out.push('[');
                arbitrary_block(u, out)?;
                out.push(']');
            }
            75..=94 => {
                let len = u.int_in_range(0..=MAX_COMMENT_LEN)?;
                for _ in 0..len {
                    if u.is_empty() {
                        break;
                    }
                    out.push(*u.choose(COMMENT_CHARS)? as char);
                }
            }
            _ => return Ok(()),
        }
    }
}

fn arbitrary_input(u: &mut Unstructured) -> arbitrary::Result<Vec<u64>> {
    let len = u.int_in_range(0..=MAX_INPUT_LEN)?;
    let mut input = Vec::with_capacity(len);
    for _ in 0..len {
        let cell = if u.ratio(7, 8)? {
            u.int_in_range(0..=16)?
        } else {
            u64::arbitrary(u)?
        };
        input.push(cell);
    }
    Ok(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::analyze;

    #[test]
    fn generated_programs_are_balanced() {
        let mut seed = Vec::new();
        for i in 0..4096u32 {
            seed.extend_from_slice(&i.to_le_bytes());
            seed.extend_from_slice(&i.wrapping_mul(2654435761).to_le_bytes());
        }
        for window in seed.chunks(97) {
            let mut u = Unstructured::new(window);
            if let Ok(case) = FuzzCase::arbitrary(&mut u) {
                assert!(
                    analyze(&case.program).is_ok(),
                    "unbalanced program generated: {:?}",
                    case.program
                );
            }
        }
    }
}
