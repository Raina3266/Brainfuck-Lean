import Brainfuck.Execution
import Mathlib.Data.UInt

/-!
  # Example: modular addition

  `add.bf` (see `corpus/add.bf`) reads two cells `[a, b]`, adds them
  (wrapping, i.e. in the ring `ℤ/2⁶⁴`), and prints the sum.

  The proofs are written against the library's proof API: `calc` chains of
  `==[p]=> ` steps for straight-line code, and `Program.Execution.loop_dec`
  with a conservation-law invariant for the loop. I/O preservation comes
  from the frame lemmas rather than being carried through the invariant.

  Where a straight-line run is plumbing rather than narrative, `simp` proves
  it outright: the library's `simp` set normalizes an execution of a concrete
  loop-free program down to the state equations.
-/

open scoped UInt64.CommRing

namespace Brainfuck.Examples.Add

  private def program : Program := embed_bf! "corpus/add.bf"

  /--
    This spec claims that:
    - If the input has exactly two elements, then the output will contain
      one value, which will be the modular sum of those two input elements.
    - If the input length is not two, this spec makes no claims about the
      behaviour (not even termination or non-termination).
  -/
  private def addSpec : Program.Spec 
    | [x, y] => .some [x + y]
    | _      => .none

  /-- The body of the add loop: move one unit from the current cell leftward. -/
  private def loopBody : Program := bf! { - < + > }

  /--
    The add loop `[ - < + > ]` drains the current cell into its left
    neighbour: the conserved quantity is the *sum* of the two cells, and the
    loop exits with the guard at zero, so the whole sum ends up on the left.
  -/
  private theorem loop_add (x y : Cell) (s0 : State)
      (hsum : s0.tape.read (-1) + s0.tape.read 0 = x + y) :
      ∃ s1, (s0 ==[ .loop loopBody ]=> s1)
        ∧ s1.tape.read (-1) = x + y
        ∧ s1.input = s0.input
        ∧ s1.output = s0.output := by
    obtain ⟨s1, hrun, hinv, hzero⟩ := Program.Execution.loop_dec
      (body := loopBody)
      (Inv := fun t => t.tape.read (-1) + t.tape.read 0 = x + y)
      (fun t hinv hne => ⟨t.dec.moveLeft.inc.moveRight,
        by simp [loopBody],
        by simpa using hinv,
        by simpa using Program.Execution.toNat_pred_lt hne⟩)
      hsum
    have hz : s1.tape.read 0 = 0 := by
      simpa using hzero
    refine ⟨s1, hrun, ?_, ?_, ?_⟩
    · simpa [hz] using hinv
    · exact Program.Execution.input_frame (by rfl) hrun
    · exact Program.Execution.output_frame (by rfl) hrun

  /--
    The skeleton of *every* run of `add.bf`: read two cells, run the loop,
    step back and print. Shared by `add_correct` and `add_halts`, which
    differ only in what they then say about `s1`.
  -/
  private theorem run_of_loop {s0 s1 : State}
      (hloop : s0.consumeInput.moveRight.consumeInput ==[ .loop loopBody ]=> s1) :
      s0 ==[ program ]=> s1.moveLeft.writeOutput := by
    set r0 := s0.consumeInput with hr0
    set r1 := r0.moveRight    with hr1
    set r2 := r1.consumeInput with hr2
    calc s0
        ==[ bf! { , } ]=>      r0 := Program.Execution.input s0
      _ ==[ bf! { > } ]=>      r1 := Program.Execution.right r0
      _ ==[ bf! { , } ]=>      r2 := Program.Execution.input r1
      _ ==[ .loop loopBody ]=> s1 := hloop
      _ ==[ bf! { < } ]=>      s1.moveLeft := Program.Execution.left s1
      _ ==[ bf! { . } ]=>      s1.moveLeft.writeOutput := Program.Execution.output s1.moveLeft

  /--
    `add.bf` computes modular addition: on any two-cell input it halts with
    exactly the sum as output and the input exhausted. (The `| _ => none`
    arm is the disclosure that this theorem claims nothing about inputs of
    any other shape.)
  -/
  theorem add_correct : program.Computes addSpec := by
    intro input output hf
    -- every other shape sends `addSpec` to `none`, so `hf` cannot be `rfl`
    -- there and the match compiler discharges those arms itself
    match input, hf with
    | [x, y], rfl =>
    obtain ⟨s1, hloop, hread, hin, hout⟩ :=
      loop_add x y (State.initial [x, y]).consumeInput.moveRight.consumeInput (by simp)

    exact ⟨_, run_of_loop hloop, by simp [hread, hout], by simp [hin]⟩

  /--
    `add.bf` terminates from *every* state — arbitrary tape contents, head
    position, input (including too little of it: `,` writes `0` on EOF), and
    output. Contrast with `add_correct`, which starts from `State.initial`.

    This is unconditional because the program's only loop strictly decreases
    the cell it guards on, and every primitive instruction is total.
  -/
  theorem add_halts (s0 : State) : program.Halts s0 := by
    set s3 := s0.consumeInput.moveRight.consumeInput

    obtain ⟨s4, hloop, -, -, -⟩ :=
      loop_add (s3.tape.read (-1)) (s3.tape.read 0) s3 rfl

    exact ⟨_, run_of_loop hloop⟩

end Brainfuck.Examples.Add

