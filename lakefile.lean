import Lake
open Lake DSL

package "brainfuck_assignment" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib" @ git "v4.31.0"

/-
  The Lean support library for Aeneas-generated code. Pinned to the same
  commit as the installed `aeneas`/`charon` binaries (see
  `scripts/extract-rust.sh`); this in turn pins Lean v4.31.0 and Mathlib
  v4.31.0 for the whole workspace.
-/
require aeneas from
  git "https://github.com/AeneasVerif/aeneas" @
    "74a460a2f80ecea481bbdf1a08f881633c3bb097" / "backends/lean"

@[default_target]
lean_lib «Brainfuck» where
  -- add any library configuration options here

/-- The Aeneas-generated pure model of the Rust interpreter. -/
lean_lib «BrainfuckCore» where

/-- The bridge proofs between `Brainfuck` and `BrainfuckCore`. -/
lean_lib «Verification» where

lean_exe oracle where
  root      := `Oracle
  buildType := .release
