import Brainfuck.Execution
import Mathlib.Data.UInt

/-!
  # Example: non-termination

  `+ [ ]` increments the cell under the head and enters an empty loop. From
  any *initial* state the cell is then `1`, the guard never changes, and the
  program diverges — there is no execution derivation at all
  (`plus_empty_loop_diverges`).

  Divergence is only certain from initial states: cell arithmetic wraps, so
  from a state whose current cell is `2⁶⁴ - 1` the `+` overflows to `0` and
  the loop is skipped (`halts_from_max`). The naive statement
  `∀ stateI, program.Diverges stateI` is false.
-/

open scoped UInt64.CommRing

namespace Brainfuck.Examples.InfiniteLoop

  private def program : Program := bf! { + [ ] }

  /-- `+ [ ]` diverges from every initial state. -/
  theorem plus_empty_loop_diverges (input : List Cell) :
      program.Diverges (State.initial input) := by
    refine Program.diverges_append (q := bf! { [ ] })
      (Program.Execution.inc (State.initial input)) ?_
    apply Program.empty_loop_diverges
    -- after the `+` the cell is 1, not 0
    simp

  /--
    The wrap-around caveat: from a state whose cell holds `2⁶⁴ - 1`, the `+`
    overflows to `0` and the "infinite" loop is skipped. This is why
    `plus_empty_loop_diverges` quantifies over initial states rather than
    all states.
  -/
  theorem halts_from_max :
      program.Halts ⟨Tape.empty.setCurrent (0 - 1), [], []⟩ := by
    set s0 : State := ⟨Tape.empty.setCurrent (0 - 1), [], []⟩ with hs0
    refine ⟨s0.inc, ?_⟩
    calc s0
        ==[ bf! { + } ]=>   s0.inc := Program.Execution.inc s0
      _ ==[ bf! { [ ] } ]=> s0.inc :=
          Fragment.execution_loop_empty_iff.mpr ⟨by simp [hs0], rfl⟩

  /--
    The wrap-proof variant: clear the cell first, so the `+` lands on `0`
    from *any* starting state.
  -/
  private def strongerProgram : Program := bf! { [ - ] + [ ] }

  /--
    `[ - ] + [ ]` diverges from every state, no exceptions: the clear loop
    terminates (by `loop_dec` with the trivial invariant) leaving the cell
    at `0`, the `+` makes it `1`, and the empty loop diverges from any
    nonzero guard. Divergence of the tail lifts to the whole program via
    `Program.diverges_append`.
  -/
  theorem strongerProgram_diverges_everywhere (s : State) :
      strongerProgram.Diverges s := by
    obtain ⟨s1, hclear, -, hzero⟩ := Program.Execution.loop_dec
      (body := bf! { - }) (Inv := fun _ => True)
      (fun t _ hne =>
        ⟨t.dec, by simp, trivial, by simpa using Program.Execution.toNat_pred_lt hne⟩)
      trivial
    have hprefix : s ==[ bf! { [ - ] + } ]=> s1.inc := by
      calc s
          ==[ .loop (bf! { - }) ]=> s1 := hclear
        _ ==[ bf! { + } ]=>       s1.inc := Program.Execution.inc s1
    refine Program.diverges_append (q := bf! { [ ] }) hprefix ?_
    apply Program.empty_loop_diverges
    -- after the `+` the cell is 0 + 1 = 1
    simp [show s1.tape.read 0 = 0 by simpa using hzero]

end Brainfuck.Examples.InfiniteLoop
