#![no_main]

use brainfuck::differential::{compare, Verdict};
use brainfuck::generate::FuzzCase;
use brainfuck::oracle::OracleClient;
use libfuzzer_sys::fuzz_target;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

static ORACLE: OnceLock<Mutex<OracleClient>> = OnceLock::new();
static LEAN_NANOS: AtomicU64 = AtomicU64::new(0);
static RUST_NANOS: AtomicU64 = AtomicU64::new(0);
static EXECUTIONS: AtomicU64 = AtomicU64::new(0);

const REPORT_EVERY: u64 = 4096;

fuzz_target!(|case: FuzzCase| {
    let oracle = ORACLE.get_or_init(|| {
        Mutex::new(OracleClient::spawn().expect(
            "failed to spawn the lean oracle; run `lake build oracle` in the workspace root",
        ))
    });
    let mut oracle = oracle.lock().expect("oracle mutex poisoned");
    let (verdict, timings) = compare(&mut oracle, &case).expect("oracle io failed");
    drop(oracle);

    if let Verdict::Mismatch(reason) = verdict {
        panic!("interpreters disagree on {case:?}: {reason}");
    }

    /*
      Both interpreters now run with the same exact fuel meter, so every
      case is a timing-comparable pair of runs.
    */
    LEAN_NANOS.fetch_add(timings.lean.as_nanos() as u64, Ordering::Relaxed);
    RUST_NANOS.fetch_add(timings.rust.as_nanos() as u64, Ordering::Relaxed);

    let executions = EXECUTIONS.fetch_add(1, Ordering::Relaxed) + 1;
    if executions % REPORT_EVERY == 0 {
        let lean = LEAN_NANOS.load(Ordering::Relaxed);
        let rust = RUST_NANOS.load(Ordering::Relaxed);
        let ratio = lean as f64 / rust.max(1) as f64;
        eprintln!(
            "[timing] {executions} execs: lean {:.3}s, rust {:.3}s, lean/rust ratio {ratio:.1}x",
            lean as f64 / 1e9,
            rust as f64 / 1e9,
        );
    }
});
