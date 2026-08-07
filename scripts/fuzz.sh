#!/usr/bin/env bash
# Differential fuzzing driver: builds the Lean oracle (release, the Lake
# default, made explicit in the lakefile) and runs the cargo-fuzz harness
# (cargo-fuzz builds optimized targets by default).
#
# Usage: scripts/fuzz.sh [--cases N] [--seed VALUE]
#   --cases N     stop after N cases (default: run until interrupted)
#   --seed VALUE  seed libFuzzer's RNG for reproducible mutation order

set -euo pipefail

usage() {
  grep '^#' "$0" | sed 's/^# \{0,1\}//'
}

cases=""
seed=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --cases)
      [[ $# -ge 2 ]] || { echo "error: --cases requires a value" >&2; exit 1; }
      cases="$2"
      shift 2
      ;;
    --seed)
      [[ $# -ge 2 ]] || { echo "error: --seed requires a value" >&2; exit 1; }
      seed="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

root="$(cd "$(dirname "$0")/.." && pwd)"

echo "==> building lean oracle (release)"
(cd "$root" && lake build oracle)

fuzz_args=()
if [[ -n "$cases" ]]; then
  fuzz_args+=("-runs=$cases")
fi
if [[ -n "$seed" ]]; then
  fuzz_args+=("-seed=$seed")
fi

# The sanitizer is disabled: the harness compares two interpreters, not
# memory safety, and instrumentation would skew the reported Rust timings.
# libFuzzer's coverage feedback is unaffected.
echo "==> running differential fuzzer"
cd "$root/rust"
exec cargo +nightly fuzz run -s none differential -- ${fuzz_args[@]+"${fuzz_args[@]}"}
