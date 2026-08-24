/-
  Conversion layer between the Aeneas scalar `Std.U64` (used by the generated
  model in `BrainfuckCore`) and `Brainfuck.Cell` (= `UInt64`, used by the
  abstract semantics in `Brainfuck`).

  Both types are 64-bit machine integers with wrapping arithmetic, so the
  conversion `toCell` is a ring isomorphism in spirit; here we only prove the
  facts the bridge needs: `toCell` is injective (reflects `.val` equality),
  preserves zero, and commutes with wrapping increment/decrement by one.
-/
import Brainfuck.Tape
import BrainfuckCore.Funs

namespace Verification

  open Aeneas Aeneas.Std
  open Brainfuck (Cell)

  /-- Convert an Aeneas 64-bit scalar to an abstract tape cell. -/
  def toCell (u : U64) : Cell :=
    UInt64.ofNat u.val

  @[simp] theorem toNat_toCell (u : U64) : (toCell u).toNat = u.val := by
    have h : u.val < 2 ^ 64 := by scalar_tac
    simp only [toCell, UInt64.toNat_ofNat']
    omega

  theorem toCell_val_inj {u v : U64} (h : toCell u = toCell v) : u.val = v.val := by
    have h' := congrArg UInt64.toNat h
    simpa using h'

  theorem toCell_eq_iff (u v : U64) : toCell u = toCell v ↔ u.val = v.val := by
    constructor
    · exact toCell_val_inj
    · intro h
      simp [toCell, h]

  @[simp] theorem toCell_eq_zero_iff (u : U64) : toCell u = 0 ↔ u.val = 0 := by
    rw [← UInt64.toNat_inj]
    simp

  @[simp] theorem toCell_zero : toCell 0#u64 = 0 := by
    simp

  /-- `toCell` commutes with the wrapping increment used by `Instr.Inc`. -/
  theorem toCell_wrapping_add_one (u : U64) :
      toCell (core.num.U64.wrapping_add u 1#u64) = toCell u + 1 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_add]
    simp only [toNat_toCell, core.num.U64.wrapping_add_val_eq]
    have h : UScalar.size .U64 = 2 ^ 64 := by
      simp [U64.size_def, U64.numBits]
    rw [h]
    simp

  /-- `toCell` commutes with the wrapping decrement used by `Instr.Dec`. -/
  theorem toCell_wrapping_sub_one (u : U64) :
      toCell (core.num.U64.wrapping_sub u 1#u64) = toCell u - 1 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_sub]
    simp only [toNat_toCell, core.num.U64.wrapping_sub_val_eq]
    have h : UScalar.size .U64 = 2 ^ 64 := by
      simp [U64.size_def, U64.numBits]
    rw [h]
    have hu : u.val < 2 ^ 64 := by scalar_tac
    simp
    omega

end Verification
