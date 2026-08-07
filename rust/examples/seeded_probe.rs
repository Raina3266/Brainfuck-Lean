use arbitrary::{Arbitrary, Unstructured};
use brainfuck::differential::{compare, Verdict};
use brainfuck::generate::FuzzCase;
use brainfuck::oracle::OracleClient;
use std::time::Instant;

fn main() {
    let mut oracle = OracleClient::spawn().expect("spawn oracle");
    let mut bytes = Vec::new();
    let mut state = 0x243F6A8885A308D3u64;
    for _ in 0..(1 << 15) {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        bytes.extend_from_slice(&state.to_le_bytes());
    }
    let start = Instant::now();
    let mut agreed = 0u32;
    for (i, window) in bytes.chunks(211).enumerate() {
        let mut u = Unstructured::new(window);
        let Ok(mut case) = FuzzCase::arbitrary(&mut u) else {
            continue;
        };
        /*
          Clamped for this validation run: `.` inside a divergent loop is
          quadratic in the Lean interpreter (output is appended as
          `output ++ [value]`), so full 10^6-fuel cases can cost minutes.
        */
        case.fuel = case.fuel.min(20_000);
        let case_start = Instant::now();
        let (verdict, timings) = compare(&mut oracle, &case).expect("oracle io");
        let elapsed = case_start.elapsed();
        if elapsed.as_millis() > 200 || matches!(verdict, Verdict::Mismatch(_)) {
            println!(
                "case {i}: wall {elapsed:?} (lean {:?}, rust {:?}) fuel={} verdict={}",
                timings.lean,
                timings.rust,
                case.fuel,
                match &verdict {
                    Verdict::Agree => "agree".to_string(),
                    Verdict::Mismatch(m) => format!("MISMATCH: {m}"),
                },
            );
        }
        if matches!(verdict, Verdict::Agree) {
            agreed += 1;
        }
        if i % 200 == 0 {
            println!("... case {i}, total {:?}", start.elapsed());
        }
    }
    println!("done in {:?}, {agreed} cases agreed", start.elapsed());
}
