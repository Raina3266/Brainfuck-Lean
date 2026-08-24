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
aeneas -backend lean -split-files "$out/brainfuck_core.llbc" -dest "$out"

# Only Types.lean and Funs.lean are generated; the *External.lean files are
# hand-written models of the std leaves. The templates are copied alongside
# so signature changes show up in the diff.
cp "$out/Types.lean" "$out/Funs.lean" "$root/BrainfuckCore/"
cp "$out/TypesExternal_Template.lean" "$out/FunsExternal_Template.lean" \
  "$root/BrainfuckCore/"
echo "regenerated $root/BrainfuckCore/{Types,Funs}.lean"
