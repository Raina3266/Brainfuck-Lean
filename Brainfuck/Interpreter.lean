import Brainfuck.Execution

namespace Brainfuck

  /-!
    # The fuel interpreter

    An executable counterpart to the `Program.Execution` relation. Brainfuck is
    Turing-complete, so a total fuel-free interpreter cannot exist (it would
    decide the halting problem); `fuel` bounds the number of instructions the
    interpreter is willing to execute, and `none` means the budget ran out.

    Fuel is an exact linear meter: one unit per executed instruction, where
    the instructions are atoms and loop-guard checks (each re-check included;
    the jump back from the end of a loop body is fused into the next guard
    check and is free). This is the same discipline as a flat
    program-counter interpreter over the compiled instruction sequence, so
    fuel-exhaustion itself is comparable across implementations.

    To keep exact metering *and* structural recursion (so the interpreter
    reduces definitionally and `rfl` works), the interpreter is an explicit
    machine: `code` is what remains of the current block and `frames` is the
    stack of enclosing loops, each frame holding the loop body (to re-enter)
    and the code after the loop (to fall through to). Every recursive call
    consumes exactly one fuel.

    The agreement theorems connect the two formulations:
    - `Fragment.executionList_of_runStack` (soundness): whatever the
      interpreter produces, the semantics sanctions;
    - `Fragment.runStack_of_executionList` (completeness): every execution
      is reachable with enough fuel;
    - `Program.run_iff_execution`: the combined iff.
  -/

  /-- The effect of a single primitive instruction on the state. -/
  def Atom.apply : Atom -> State -> State
    | .inc,    s => s.inc
    | .dec,    s => s.dec
    | .left,   s => s.moveLeft
    | .right,  s => s.moveRight
    | .input,  s => s.consumeInput
    | .output, s => s.writeOutput

  /-- The transition relation is the graph of `Atom.apply`. -/
  theorem Transition.isValid_iff_apply {a : Atom} {s s' : State} :
      (s >-[a]-> s') ↔ a.apply s = s' := by
    cases a <;> simp [Atom.apply]

  namespace Fragment

    /--
      One machine frame: the body of an enclosing loop (to jump back to) and
      the code after that loop (to fall through to on exit).
    -/
    abbrev Frame := Program × List Fragment

    /--
      Run the machine: execute `code`, then the continuation described by
      `frames`. Exactly one fuel per executed instruction; reaching the end
      of a loop body jumps back to its guard for free (the re-check itself
      is the next charged instruction).
    -/
    def runStack : Nat -> List Fragment -> List Frame -> State -> Option State
      | _, [], [], s => some s
      | 0, [], _ :: _, _ => none
      | fuel + 1, [], (body, rest) :: frames, s =>
        if s.tape.current = 0 then
          runStack fuel rest frames s
        else
          runStack fuel body.inner ((body, rest) :: frames) s
      | 0, _ :: _, _, _ => none
      | fuel + 1, .atom a :: code, frames, s =>
        runStack fuel code frames (a.apply s)
      | fuel + 1, .loop body :: code, frames, s =>
        if s.tape.current = 0 then
          runStack fuel code frames s
        else
          runStack fuel body.inner ((body, code) :: frames) s

  end Fragment

  /-- Run a program with the given instruction budget. -/
  def Program.run (p : Program) (fuel : Nat) (s : State) : Option State :=
    Fragment.runStack fuel p.inner [] s

  namespace Fragment

    /-- More fuel never hurts: a successful run stays successful. -/
    theorem runStack_mono :
        ∀ {fuel fuel' : Nat} {code : List Fragment} {frames : List Frame} {s s' : State},
          fuel <= fuel' ->
          runStack fuel code frames s = some s' -> runStack fuel' code frames s = some s' := by
      intro fuel
      induction fuel with
      | zero =>
        intro fuel' code frames s s' hle h
        cases code with
        | nil =>
          cases frames with
          | nil          => simpa [runStack] using h
          | cons fr frs  => simp [runStack] at h
        | cons f rest => simp [runStack] at h
      | succ n ih =>
        intro fuel' code frames s s' hle h
        obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
        have hnm : n <= m := by omega
        cases code with
        | nil =>
          cases frames with
          | nil => simpa [runStack] using h
          | cons fr frs =>
            obtain ⟨body, rest⟩ := fr
            simp only [runStack] at h ⊢
            by_cases hz : s.tape.current = 0
            · rw [if_pos hz] at h ⊢
              exact ih hnm h
            · rw [if_neg hz] at h ⊢
              exact ih hnm h
        | cons f rest =>
          cases f with
          | atom a =>
            simp only [runStack] at h ⊢
            exact ih hnm h
          | loop body =>
            simp only [runStack] at h ⊢
            by_cases hz : s.tape.current = 0
            · rw [if_pos hz] at h ⊢
              exact ih hnm h
            · rw [if_neg hz] at h ⊢
              exact ih hnm h

    /--
      The whole remaining program of a machine configuration: each frame
      contributes re-entering its loop and then its trailing code.
    -/
    def frameSuffix : List Frame -> List Fragment
      | []                      => []
      | (body, rest) :: frames  => (.loop body :: rest) ++ frameSuffix frames

    /-- Soundness: whatever the interpreter produces, the semantics sanctions. -/
    theorem executionList_of_runStack :
        ∀ {fuel : Nat} {code : List Fragment} {frames : List Frame} {s s' : State},
          runStack fuel code frames s = some s' ->
          ExecutionList (code ++ frameSuffix frames) s s' := by
      intro fuel
      induction fuel with
      | zero =>
        intro code frames s s' h
        cases code with
        | nil =>
          cases frames with
          | nil =>
            simp only [runStack, Option.some.injEq] at h
            subst h
            exact .nil
          | cons fr frs => simp [runStack] at h
        | cons f rest => simp [runStack] at h
      | succ n ih =>
        intro code frames s s' h
        cases code with
        | nil =>
          cases frames with
          | nil =>
            simp only [runStack, Option.some.injEq] at h
            subst h
            exact .nil
          | cons fr frs =>
            obtain ⟨body, rest⟩ := fr
            simp only [runStack] at h
            simp only [List.nil_append, frameSuffix]
            by_cases hz : s.tape.current = 0
            · rw [if_pos hz] at h
              exact .loopDone hz (ih h)
            · rw [if_neg hz] at h
              have hall := ih h
              rw [frameSuffix] at hall
              obtain ⟨t, hbody, hagain⟩ := executionList_append_iff.mp hall
              exact .loopStep hz hbody hagain
        | cons f rest =>
          cases f with
          | atom a =>
            simp only [runStack] at h
            exact .atom (Transition.isValid_iff_apply.mpr rfl) (ih h)
          | loop body =>
            simp only [runStack] at h
            by_cases hz : s.tape.current = 0
            · rw [if_pos hz] at h
              exact .loopDone hz (ih h)
            · rw [if_neg hz] at h
              have hall := ih h
              rw [frameSuffix] at hall
              obtain ⟨t, hbody, hagain⟩ := executionList_append_iff.mp hall
              exact .loopStep hz hbody hagain

    /--
      Completeness, in continuation form: if the machine finishes the
      continuation `frames` from `s'`, and the semantics runs `fs` from `s`
      to `s'`, then with enough fuel the machine runs `fs` and then the
      continuation from `s`.
    -/
    theorem runStack_of_executionList {fs : List Fragment} {s s' : State}
        (h : ExecutionList fs s s') :
        ∀ {frames : List Frame} {fuel₀ : Nat} {out : State},
          runStack fuel₀ [] frames s' = some out ->
          ∃ fuel, runStack fuel fs frames s = some out := by
      induction h with
      | nil =>
        intro frames fuel₀ out hcont
        exact ⟨fuel₀, hcont⟩
      | atom valid rest ih =>
        intro frames fuel₀ out hcont
        obtain ⟨fuel, hfuel⟩ := ih hcont
        refine ⟨fuel + 1, ?_⟩
        simp only [runStack]
        rw [Transition.isValid_iff_apply.mp valid]
        exact hfuel
      | loopDone cell_zero rest ih =>
        intro frames fuel₀ out hcont
        obtain ⟨fuel, hfuel⟩ := ih hcont
        refine ⟨fuel + 1, ?_⟩
        simp only [runStack]
        rw [if_pos cell_zero]
        exact hfuel
      | @loopStep bodyP fsL sA sB sC cell_nonzero body_run again ih_body ih_again =>
        intro frames fuel₀ out hcont
        obtain ⟨f₂, hf₂⟩ := ih_again hcont
        cases f₂ with
        | zero => simp [runStack] at hf₂
        | succ g =>
          /-
            Re-fold the continuation: at the end of a body, the machine's
            `[] / (bodyP, fsL) :: frames` configuration unfolds to exactly
            the same expression as `loop bodyP :: fsL / frames`.
          -/
          have hcont' : runStack (g + 1) [] ((bodyP, fsL) :: frames) sB = some out := by
            simp only [runStack] at hf₂ ⊢
            exact hf₂
          obtain ⟨f₁, hf₁⟩ := ih_body hcont'
          refine ⟨f₁ + 1, ?_⟩
          simp only [runStack]
          rw [if_neg cell_nonzero]
          exact hf₁

  end Fragment

  namespace Program

    /--
      The agreement theorem: the fuel interpreter and the big-step semantics
      describe exactly the same executions.
    -/
    theorem run_iff_execution {p : Program} {s s' : State} :
        (∃ fuel, p.run fuel s = some s') ↔ (s ==[p]=> s') := by
      constructor
      · intro ⟨fuel, h⟩
        have := Fragment.executionList_of_runStack h
        simpa [Fragment.frameSuffix] using this
      · intro h
        exact Fragment.runStack_of_executionList h (fuel₀ := 0) rfl

    /-- A program halts iff the interpreter succeeds on some budget. -/
    theorem halts_iff_run {p : Program} {s : State} :
        p.Halts s ↔ ∃ fuel s', p.run fuel s = some s' := by
      constructor
      · intro ⟨s', h⟩
        obtain ⟨fuel, hfuel⟩ := run_iff_execution.mpr h
        exact ⟨fuel, s', hfuel⟩
      · intro ⟨fuel, s', h⟩
        exact ⟨s', run_iff_execution.mp ⟨fuel, h⟩⟩

    /-- A program diverges iff the interpreter fails on every budget. -/
    theorem diverges_iff_run {p : Program} {s : State} :
        p.Diverges s ↔ ∀ fuel, p.run fuel s = none := by
      rw [Program.Diverges, halts_iff_run]
      constructor
      · intro h fuel
        cases hrun : p.run fuel s with
        | none => rfl
        | some s' => exact absurd ⟨fuel, s', hrun⟩ h
      · intro h ⟨fuel, s', hrun⟩
        rw [h fuel] at hrun
        cases hrun

    /--
      Run a program on an input, observing only the output. `none` means the
      fuel ran out (never that the program is somehow invalid: execution is
      total apart from non-termination).
    -/
    def interpret (p : Program) (input : List Cell) (fuel : Nat) : Option (List Cell) :=
      (p.run fuel (State.initial input)).map State.output

    /--
      If (per the big-step semantics) a program terminates on an input with
      an expected output, then some finite fuel makes the interpreter produce
      exactly that output.
    -/
    theorem interpret_complete {p : Program} {input expected : List Cell} {stateT : State}
        (hexec : State.initial input ==[p]=> stateT)
        (hout : stateT.output = expected) :
        ∃ fuel, p.interpret input fuel = some expected := by
      obtain ⟨fuel, hfuel⟩ := run_iff_execution.mpr hexec
      refine ⟨fuel, ?_⟩
      simp [interpret, hfuel, hout]

    /--
      If a program does not terminate on an input then no fuel is enough:
      the interpreter always reports `none`.
    -/
    theorem interpret_none_of_diverges {p : Program} {input : List Cell}
        (h : p.Diverges (State.initial input)) :
        ∀ fuel, p.interpret input fuel = none := by
      intro fuel
      simp [interpret, diverges_iff_run.mp h fuel]

  end Program

  /-!
    ### Smoke tests

    The interpreter is structural in fuel, so these reduce by `rfl`. The
    budgets are now exact instruction counts, so the tests double as checks
    of the metering: each program's cost is written next to it.
  -/

  /- two increments leave 2 under the head (cost: exactly 2) -/
  example : ((bf! { + + }).run 2 (State.initial [])).map (·.tape.current) = some 2 := by
    rfl

  /- one fuel short: the second `+` does not fit -/
  example : (bf! { + + }).run 1 (State.initial []) = none := by
    rfl

  /- read 5, clear it (cost: 1 + 6 guards + 5 decs + 1 = 13) -/
  example : (bf! { , [ - ] . }).interpret [5] 13 = some [0] := by
    rfl

  example : (bf! { , [ - ] . }).interpret [5] 12 = none := by
    rfl

  /- addition, as in `corpus/add.bf` (cost: 3 + 5 guards + 16 body + 2 = 26) -/
  example : (bf! { , > , [ - < + > ] < . }).interpret [3, 4] 26 = some [7] := by
    rfl

  /- the infinite loop exhausts any budget -/
  example : (bf! { + [ ] }).interpret [] 100 = none := by
    rfl

end Brainfuck
