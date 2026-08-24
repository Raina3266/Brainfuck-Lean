/-
  Standing platform assumption for the verification: the target is 64-bit,
  i.e. `usize` is 64 bits wide. The Rust crate enforces this with a
  `compile_error!` guard, so the assumption is sound for every binary the
  proofs are meant to describe.

  The assumption is threaded through the development as the typeclass
  hypothesis `Fact (Usize.numBits = 64)`: downstream files declare
  `variable [Fact (Usize.numBits = 64)]` once and everything else is
  picked up by instance resolution (in particular by `simp` and
  `scalar_tac` via the lemmas below).
-/
import Aeneas
import Mathlib.Tactic

namespace Verification

  open Aeneas Aeneas.Std

  @[simp, scalar_tac_simps]
  theorem usize_numBits_eq [Fact (Usize.numBits = 64)] : Usize.numBits = 64 :=
    Fact.out

  @[simp, scalar_tac_simps]
  theorem usize_max_eq [Fact (Usize.numBits = 64)] : Usize.max = 2 ^ 64 - 1 := by
    rw [Usize.max_def, usize_numBits_eq]

  theorem usize_max_eq_u64 [Fact (Usize.numBits = 64)] : Usize.max = U64.max := by
    rw [usize_max_eq]
    scalar_tac

  /-- On 64-bit targets every `i64` value fits strictly below `usize::MAX`. -/
  theorem i64_val_lt_usize_max [Fact (Usize.numBits = 64)] (p : I64) :
      p.val < (Usize.max : Int) := by
    scalar_tac

  /-- On 64-bit targets every `i64` value is at least `-usize::MAX`. -/
  theorem neg_usize_max_le_i64_val [Fact (Usize.numBits = 64)] (p : I64) :
      -(Usize.max : Int) ≤ p.val := by
    scalar_tac

end Verification
