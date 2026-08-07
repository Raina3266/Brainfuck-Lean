import Brainfuck.Tape
import Brainfuck.State

namespace Brainfuck

  /--
    The six primitive (non-control-flow) instructions.

    The loop brackets are deliberately not here: a bracket is control flow,
    not a state transition — `State` has no program counter, so a single
    bracket has no meaning as a `State -> State` step. Loops live in the
    program representation (`Fragment.loop`) and get their semantics from
    the program-level execution relation; at this layer they are
    unrepresentable by construction.
  -/
  inductive Atom where
    | inc
    | dec
    | left
    | right
    | input
    | output
    deriving Repr, DecidableEq

  /--
    A (potentially invalid) state transition
  -/
  structure Transition where
    atom : Atom
    old  : State
    new  : State

  /--
    The transitions the machine can actually take: one constructor per
    primitive instruction, each pinning `new` to the effect of that
    instruction on `old`.
  -/
  inductive Transition.IsValid (trans : Transition) : Prop where
    | ofInc
      (atom_eq  : trans.atom = .inc)
      (state_eq : trans.old.inc = trans.new)
      : trans.IsValid
    | ofDec
      (atom_eq  : trans.atom = .dec)
      (state_eq : trans.old.dec = trans.new)
      : trans.IsValid
    | ofLeft
      (atom_eq  : trans.atom = .left)
      (state_eq : trans.old.moveLeft = trans.new)
      : trans.IsValid
    | ofRight
      (atom_eq  : trans.atom = .right)
      (state_eq : trans.old.moveRight = trans.new)
      : trans.IsValid
    | ofInput
      (atom_eq  : trans.atom = .input)
      (state_eq : trans.old.consumeInput = trans.new)
      : trans.IsValid
    | ofOutput
      (atom_eq  : trans.atom = .output)
      (state_eq : trans.old.writeOutput = trans.new)
      : trans.IsValid

  /-!
    ### Notation

    `s >-[a]-> s'` is `Transition.IsValid ⟨a, s, s'⟩`: executing the single
    instruction `a` in state `s` produces state `s'`. The program-level
    counterpart is `s ==[p]=> s'` in `Execution.lean`.
  -/
  /-- `s >-[a]-> s'`: executing the single instruction `a` in state `s` produces state `s'`. -/
  scoped notation:50 s:51 " >-[" a "]-> " s':51 => Transition.IsValid (Transition.mk a s s')

  namespace Transition

    /-!
      ### Introduction lemmas

      For each primitive instruction, the transition to its effect is valid.
      These are the lemmas you apply when *building* an execution.
    -/

    theorem isValid_inc (s : State) : s >-[.inc]-> s.inc := by
      exact .ofInc rfl rfl

    theorem isValid_dec (s : State) : s >-[.dec]-> s.dec := by
      exact .ofDec rfl rfl

    theorem isValid_left (s : State) : s >-[.left]-> s.moveLeft := by
      exact .ofLeft rfl rfl

    theorem isValid_right (s : State) : s >-[.right]-> s.moveRight := by
      exact .ofRight rfl rfl

    theorem isValid_input (s : State) : s >-[.input]-> s.consumeInput := by
      exact .ofInput rfl rfl

    theorem isValid_output (s : State) : s >-[.output]-> s.writeOutput := by
      exact .ofOutput rfl rfl

    /-!
      ### Inversion lemmas

      For each instruction, validity is *equivalent* to the state equation —
      knowing a transition is valid tells you exactly what `new` is. These are
      the lemmas `simp` uses when *consuming* an execution. Marked `@[simp]`
      so that validity goals and hypotheses about concrete instructions reduce
      to state equations automatically.
    -/

    @[simp] theorem isValid_inc_iff {old new : State} :
        (old >-[.inc]-> new) ↔ old.inc = new := by
      constructor
      · intro h
        cases h <;> simp_all
      · intro h
        exact .ofInc rfl h

    @[simp] theorem isValid_dec_iff {old new : State} :
        (old >-[.dec]-> new) ↔ old.dec = new := by
      constructor
      · intro h
        cases h <;> simp_all
      · intro h
        exact .ofDec rfl h

    @[simp] theorem isValid_left_iff {old new : State} :
        (old >-[.left]-> new) ↔ old.moveLeft = new := by
      constructor
      · intro h
        cases h <;> simp_all
      · intro h
        exact .ofLeft rfl h

    @[simp] theorem isValid_right_iff {old new : State} :
        (old >-[.right]-> new) ↔ old.moveRight = new := by
      constructor
      · intro h
        cases h <;> simp_all
      · intro h
        exact .ofRight rfl h

    @[simp] theorem isValid_input_iff {old new : State} :
        (old >-[.input]-> new) ↔ old.consumeInput = new := by
      constructor
      · intro h
        cases h <;> simp_all
      · intro h
        exact .ofInput rfl h

    @[simp] theorem isValid_output_iff {old new : State} :
        (old >-[.output]-> new) ↔ old.writeOutput = new := by
      constructor
      · intro h
        cases h <;> simp_all
      · intro h
        exact .ofOutput rfl h

    /-!
      ### Properties

      The transition relation is deterministic (a machine, not just a
      relation), and total: every atom can step from every state.
    -/

    /-- From the same instruction and old state, only one new state is valid. -/
    theorem IsValid.deterministic {atom : Atom} {old new₁ new₂ : State}
        (h₁ : old >-[atom]-> new₁)
        (h₂ : old >-[atom]-> new₂) :
        new₁ = new₂ := by
      cases h₁ <;> cases h₂ <;> simp_all

    /-- Every atom can step from every state. -/
    theorem exists_isValid (atom : Atom) (old : State) :
        ∃ new, old >-[atom]-> new := by
      cases atom with
      | inc    => exact ⟨old.inc, isValid_inc old⟩
      | dec    => exact ⟨old.dec, isValid_dec old⟩
      | left   => exact ⟨old.moveLeft, isValid_left old⟩
      | right  => exact ⟨old.moveRight, isValid_right old⟩
      | input  => exact ⟨old.consumeInput, isValid_input old⟩
      | output => exact ⟨old.writeOutput, isValid_output old⟩

  end Transition

end Brainfuck
