import Brainfuck.Tape

namespace Brainfuck

  /--
    A machine state: the tape, the input not yet consumed by `,`, and the
    output produced so far by `.` (in emission order).

    There is deliberately no program counter here: with a tree-structured program
    representation and a big-step semantics, the position in the program lives in
    the derivation, not in the state.
  -/
  structure State where
    tape   : Tape
    input  : List Cell
    output : List Cell

  namespace State

    /-- The state a program starts in: zeroed tape, the given input, no output. -/
    def initial (input : List Cell) : State where
      tape   := .empty
      input  := input
      output := []

    instance : Inhabited State := ⟨initial []⟩

    private def withTape (state : State) (tape : Tape) : State where
      tape   := tape
      input  := state.input
      output := state.output

    def inc (state : State) : State := state.withTape (state.tape.increment)
    def dec (state : State) : State := state.withTape (state.tape.decrement)
    def moveLeft  (state : State) : State := state.withTape (state.tape.moveLeft)
    def moveRight (state : State) : State := state.withTape (state.tape.moveRight)

    /--
      Consume one input cell into the cell under the head (`,`).

      EOF policy: when the input is exhausted, this writes `0`.
    -/
    def consumeInput (state : State) : State :=
      let value     := state.input.headD 0
      let newInput  := state.input.drop 1
      let newOutput := state.output
      let newTape   := state.tape.setCurrent value

      { tape := newTape, input := newInput, output := newOutput }

    /--
      Emit the cell under the head (`.`). Output is kept in emission order,
      hence the append.
    -/
    def writeOutput (state : State) : State :=
      let value     := state.tape.current
      let newInput  := state.input
      let newOutput := state.output ++ [value]
      let newTape   := state.tape

      { tape := newTape, input := newInput, output := newOutput }

    /-!
      ### Specification

      How each operation affects the three fields, as `@[simp]` lemmas (all
      definitional). `withTape` is private, so these lemmas are the public
      interface for reasoning about the operations; proofs outside this file
      should never need to unfold the definitions.
    -/

    @[simp] theorem tape_initial (input : List Cell) : (initial input).tape = Tape.empty := by rfl
    @[simp] theorem input_initial (input : List Cell) : (initial input).input = input := by rfl
    @[simp] theorem output_initial (input : List Cell) : (initial input).output = [] := by rfl

    @[simp] theorem tape_inc (s : State) : s.inc.tape = s.tape.increment := by rfl
    @[simp] theorem input_inc (s : State) : s.inc.input = s.input := by rfl
    @[simp] theorem output_inc (s : State) : s.inc.output = s.output := by rfl

    @[simp] theorem tape_dec (s : State) : s.dec.tape = s.tape.decrement := by rfl
    @[simp] theorem input_dec (s : State) : s.dec.input = s.input := by rfl
    @[simp] theorem output_dec (s : State) : s.dec.output = s.output := by rfl

    @[simp] theorem tape_moveLeft (s : State) : s.moveLeft.tape = s.tape.moveLeft := by rfl
    @[simp] theorem input_moveLeft (s : State) : s.moveLeft.input = s.input := by rfl
    @[simp] theorem output_moveLeft (s : State) : s.moveLeft.output = s.output := by rfl

    @[simp] theorem tape_moveRight (s : State) : s.moveRight.tape = s.tape.moveRight := by rfl
    @[simp] theorem input_moveRight (s : State) : s.moveRight.input = s.input := by rfl
    @[simp] theorem output_moveRight (s : State) : s.moveRight.output = s.output := by rfl

    @[simp] theorem tape_consumeInput (s : State) :
        s.consumeInput.tape = s.tape.setCurrent (s.input.headD 0) := by rfl
    @[simp] theorem input_consumeInput (s : State) :
        s.consumeInput.input = s.input.drop 1 := by rfl
    @[simp] theorem output_consumeInput (s : State) :
        s.consumeInput.output = s.output := by rfl

    @[simp] theorem tape_writeOutput (s : State) : s.writeOutput.tape = s.tape := by rfl
    @[simp] theorem input_writeOutput (s : State) : s.writeOutput.input = s.input := by rfl
    @[simp] theorem output_writeOutput (s : State) :
        s.writeOutput.output = s.output ++ [s.tape.current] := by rfl

    theorem inc_dec_id (state : State) : state.inc.dec = state := by
      simp [inc, dec, withTape]

    theorem move_right_left_id (state : State) : state.moveRight.moveLeft = state := by
      simp [moveRight, moveLeft, withTape]

  end State

end Brainfuck
