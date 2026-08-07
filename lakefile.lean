import Lake
open Lake DSL

package "brainfuck_assignment" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib" @ git "v4.32.2"

@[default_target]
lean_lib «Brainfuck» where
  -- add any library configuration options here

lean_exe oracle where
  root      := `Oracle
  buildType := .release
