#!/usr/bin/env bash
#
# Regenerate BrainfuckCore.lean from the Rust interpreter via Charon + Aeneas.
#
# Requires `charon` and `aeneas` on PATH, built from the aeneas commit pinned
# in lakefile.lean (the aeneas repo pins its matching charon in `charon-pin`).

set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT

cd "$root/rust"
charon cargo --preset=aeneas \
  --start-from crate::interpreter::run_full \
  --dest-file "$out/brainfuck_core.llbc" \
  -- --lib --no-default-features
aeneas -backend lean "$out/brainfuck_core.llbc" -dest "$out"

cp "$out/BrainfuckCore.lean" "$root/BrainfuckCore.lean"
echo "regenerated $root/BrainfuckCore.lean"
