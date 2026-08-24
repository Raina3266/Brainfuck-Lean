import Brainfuck.Program

namespace Brainfuck

  /-!
    ### Big-step execution

    `Program.Execution p s s'` says: running `p` from state `s` terminates in
    state `s'`. Divergence is the absence of a derivation: for a program
    that loops forever from `s`, no `s'` satisfies the relation.

    There is no program counter anywhere: the position in the program is
    encoded by which subterm of the derivation you are in. Primitive
    instructions bottom out in `Transition.IsValid` (the instruction-local
    semantics); the rules here contribute only control flow.

    The relation is a single inductive over `List Fragment` rather than a
    mutual family mirroring `Program`/`Fragment`: proofs by induction on
    derivations (determinism, interpreter equivalence, ...) are far smoother
    with a single relation, and Lean's support for structural recursion over
    mutual `Prop` families is limited. The per-fragment and per-program views
    are recovered as definitions and `iff` lemmas below.
  -/

  /--
    Big-step execution of a sequence of fragments.

    `nil` finishes; `atom` performs one valid transition and continues;
    `loopDone` skips a loop whose guard cell is zero; `loopStep` runs the
    body once and re-enters the loop.
  -/
  inductive Fragment.ExecutionList : List Fragment -> State -> State -> Prop where
    | nil
      {s : State}
      : Fragment.ExecutionList [] s s
    | atom
      {a : Atom} {fs : List Fragment} {s s' s'' : State}
      (valid : s >-[a]-> s')
      (rest  : Fragment.ExecutionList fs s' s'')
      : Fragment.ExecutionList (.atom a :: fs) s s''
    | loopDone
      {body : Program} {fs : List Fragment} {s s' : State}
      (cell_zero : s.tape.current = 0)
      (rest      : Fragment.ExecutionList fs s s')
      : Fragment.ExecutionList (.loop body :: fs) s s'
    | loopStep
      {body : Program} {fs : List Fragment} {s s' s'' : State}
      (cell_nonzero : s.tape.current ≠ 0)
      (body_run     : Fragment.ExecutionList body.inner s s')
      (again        : Fragment.ExecutionList (.loop body :: fs) s' s'')
      : Fragment.ExecutionList (.loop body :: fs) s s''

  /-- Executing a single fragment. -/
  def Fragment.Execution (frag : Fragment) (old new : State) : Prop :=
    Fragment.ExecutionList [frag] old new

  /-- Running a program is running its fragments in sequence. -/
  def Program.Execution (prog : Program) (old new : State) : Prop :=
    Fragment.ExecutionList prog.inner old new

  /-!
    ### Notation

    `s ==[p]=> s'` is `Program.Execution p s s'`: running `p` from `s`
    terminates in `s'`. Sequential composition (`Program.Execution.seq`,
    below) is registered as a `Trans` instance, so `calc` blocks can chain
    program segments:

    ```
    calc s ==[ bf! { , > , } ]=> s₁ := …
      _  ==[ bf! { [ - < + > ] } ]=> s₂ := …
      _  ==[ bf! { < . } ]=> s₃ := …
    ```

    proving `s ==[ bf! { , > , [ - < + > ] < . } ]=> s₃`.
  -/

  /-- `s ==[p]=> s'`: running the program `p` from state `s` terminates in state `s'`. -/
  scoped notation:50 s:51 " ==[" p "]=> " s':51 => Program.Execution p s s'

  namespace Fragment

    /-!
      ### Decomposition lemmas

      Executions decompose along the program structure: these are the lemmas
      that let a proof about `X Y` split into a proof about `X` chained with a
      proof about `Y`. The `simp` set normalizes executions of concrete
      programs down to transitions; the loop unfolding is deliberately not
      `simp` (its right-hand side mentions itself).
    -/

    @[simp] theorem executionList_nil_iff {s s' : State} :
        ExecutionList [] s s' ↔ s' = s := by
      constructor
      · intro h
        cases h
        rfl
      · intro h
        subst h
        exact .nil

    private theorem executionList_cons_split {l : List Fragment} {s s'' : State}
        (h : ExecutionList l s s'') :
        ∀ {f : Fragment} {fs : List Fragment}, l = f :: fs ->
          ∃ s', ExecutionList [f] s s' ∧ ExecutionList fs s' s'' := by
      induction h with
      | nil =>
        intro f fs hl
        cases hl
      | atom valid rest ih =>
        intro f fs hl
        cases hl
        exact ⟨_, .atom valid .nil, rest⟩
      | loopDone cell_zero rest ih =>
        intro f fs hl
        cases hl
        exact ⟨_, .loopDone cell_zero .nil, rest⟩
      | loopStep cell_nonzero body_run again ih_body ih_again =>
        intro f fs hl
        cases hl
        obtain ⟨m, hloop, htail⟩ := ih_again rfl
        exact ⟨m, .loopStep cell_nonzero body_run hloop, htail⟩

    private theorem executionList_cons_join {l : List Fragment} {s m : State}
        (h : ExecutionList l s m) :
        ∀ {f : Fragment} {fs : List Fragment} {s'' : State}, l = [f] ->
          ExecutionList fs m s'' -> ExecutionList (f :: fs) s s'' := by
      induction h with
      | nil =>
        intro f fs s'' hl
        cases hl
      | atom valid rest ih =>
        intro f fs s'' hl h₂
        cases hl
        cases rest
        exact .atom valid h₂
      | loopDone cell_zero rest ih =>
        intro f fs s'' hl h₂
        cases hl
        cases rest
        exact .loopDone cell_zero h₂
      | loopStep cell_nonzero body_run again ih_body ih_again =>
        intro f fs s'' hl h₂
        cases hl
        exact .loopStep cell_nonzero body_run (ih_again rfl h₂)

    /-- Sequencing: the head fragment runs, then the rest from where it left off. -/
    @[simp] theorem executionList_cons_iff {f : Fragment} {fs : List Fragment} {s s'' : State} :
        ExecutionList (f :: fs) s s'' ↔ ∃ s', Execution f s s' ∧ ExecutionList fs s' s'' := by
      constructor
      · intro h
        exact executionList_cons_split h rfl
      · intro h
        obtain ⟨s', head, tail⟩ := h
        exact executionList_cons_join head rfl tail

    /-- Concatenation: run the two halves in order. -/
    theorem executionList_append_iff {xs ys : List Fragment} {s s'' : State} :
        ExecutionList (xs ++ ys) s s'' ↔ ∃ s', ExecutionList xs s s' ∧ ExecutionList ys s' s'' := by
      induction xs generalizing s with
      | nil => simp
      | cons f fs ih =>
        simp only [List.cons_append, executionList_cons_iff, ih]
        constructor
        · intro h
          obtain ⟨t, head, u, mid, tail⟩ := h
          exact ⟨u, ⟨t, head, mid⟩, tail⟩
        · intro h
          obtain ⟨u, ⟨t, head, mid⟩, tail⟩ := h
          exact ⟨t, head, u, mid, tail⟩

    /-- A primitive fragment performs exactly one valid transition. -/
    @[simp] theorem execution_atom_iff {a : Atom} {s s' : State} :
        Execution (.atom a) s s' ↔ (s >-[a]-> s') := by
      constructor
      · intro h
        cases h with
        | atom valid rest =>
          cases rest
          exact valid
      · intro h
        exact .atom h .nil

    /--
      Unfolding a loop: either the guard is zero and nothing happens, or the
      body runs once and the loop re-executes. Not `@[simp]`: the right-hand
      side mentions the left-hand side, so `simp` would unfold forever. Apply
      it manually, or use the `ExecutionList` constructors directly.
    -/
    theorem execution_loop_iff {body : Program} {s s'' : State} :
        Execution (.loop body) s s'' ↔
          (s.tape.current = 0 ∧ s'' = s) ∨
          (s.tape.current ≠ 0 ∧
            ∃ s', (s ==[body]=> s') ∧ Execution (.loop body) s' s'') := by
      constructor
      · intro h
        cases h with
        | loopDone cell_zero rest =>
          cases rest
          exact .inl ⟨cell_zero, rfl⟩
        | loopStep cell_nonzero body_run again =>
          exact .inr ⟨cell_nonzero, _, body_run, again⟩
      · intro h
        obtain ⟨cell_zero, rfl⟩ | ⟨cell_nonzero, s', body_run, again⟩ := h
        · exact .loopDone cell_zero .nil
        · exact .loopStep cell_nonzero body_run again

    /--
      A loop can only finish by observing a zero guard: whatever the body,
      a completed loop execution ends with `0` under the head.

      The `generalize` before `induction` replaces the fixed index by a
      variable plus an equation ("fording"), since `induction` requires the
      major premise's indices to be variables. The same pattern appears in
      `Transition.IsValid`'s `atom_eq` fields.
    -/
    theorem execution_loop_exit_zero {body : Program} {s s' : State}
        (h : Execution (.loop body) s s') : s'.tape.current = 0 := by
      -- `generalize` is syntactic: expose the `ExecutionList` form first
      have h' : ExecutionList [Fragment.loop body] s s' := h
      generalize hfs : [Fragment.loop body] = fs at h'
      clear h
      induction h' with
      | nil => cases hfs
      | atom valid rest ih => cases hfs
      | loopDone cell_zero rest ih =>
        cases hfs
        have := executionList_nil_iff.mp rest
        subst this
        exact cell_zero
      | loopStep cell_nonzero body_run again ih_body ih_again =>
        cases hfs
        exact ih_again rfl

    /--
      The empty loop executes exactly from a zero guard, and then does
      nothing. In particular there is *no* execution from a nonzero guard:
      each `loopStep` runs the empty body — changing nothing — and re-enters
      the loop from the same state, so no derivation can bottom out.
    -/
    theorem execution_loop_empty_iff {s s' : State} :
        Execution (.loop (Program.mk [])) s s' ↔ s.tape.current = 0 ∧ s' = s := by
      constructor
      · intro h
        have h' : ExecutionList [Fragment.loop (Program.mk [])] s s' := h
        generalize hfs : [Fragment.loop (Program.mk [])] = fs at h'
        clear h
        induction h' with
        | nil => cases hfs
        | atom valid rest ih => cases hfs
        | loopDone cell_zero rest ih =>
          cases hfs
          exact ⟨cell_zero, executionList_nil_iff.mp rest⟩
        | loopStep cell_nonzero body_run again ih_body ih_again =>
          cases hfs
          have mid_eq := executionList_nil_iff.mp body_run
          subst mid_eq
          exact ih_again rfl
      · intro ⟨cell_zero, hs⟩
        subst hs
        exact .loopDone cell_zero .nil

  end Fragment

  namespace Program

    @[simp] theorem execution_iff {p : Program} {s s' : State} :
        (s ==[p]=> s') ↔ Fragment.ExecutionList p.inner s s' := by
      exact Iff.rfl

    /-- `p` halts from `s`: some terminating execution exists. -/
    def Halts (p : Program) (s : State) : Prop :=
      ∃ s', s ==[p]=> s'

    /--
      `p` diverges from `s`: no terminating execution exists.

      In this big-step semantics divergence really is "runs forever": no
      configuration is ever stuck (primitive transitions are total, and a
      loop always has an applicable rule), so the absence of a final state
      cannot mean anything else.
    -/
    def Diverges (p : Program) (s : State) : Prop :=
      ¬ p.Halts s

    /--
      An I/O specification: for each input, either `some` expected output or
      `none` for "no claim about this input". Consumed by `Program.Computes`.
    -/
    abbrev Spec := List Cell -> Option (List Cell)

    /--
      `p.Computes spec`: on every input where the specification `spec` is
      defined, the program terminates from `State.initial input`, consumes
      the whole input, and produces exactly `spec input` as output.

      `spec input = none` means *no claim* about that input — not divergence
      (use `Diverges` for that). Consequently two `Computes` specifications
      for the same program need only agree where both are `some`.

      Deliberately says nothing about the final tape.
    -/
    def Computes (p : Program) (spec : Spec) : Prop :=
      ∀ input output, spec input = some output ->
        ∃ s', (State.initial input ==[p]=> s')
          ∧ s'.output = output
          ∧ s'.input = []

  end Program

  /-- Sequential composition: run `p`, then `q` from where it left off. -/
  theorem Program.Execution.seq {p q : Program} {s s' s'' : State}
      (h₁ : s ==[p]=> s') (h₂ : s' ==[q]=> s'') : s ==[p ++ q]=> s'' := by
    exact Fragment.executionList_append_iff.mpr ⟨s', h₁, h₂⟩

  instance {p q : Program} :
      Trans (Program.Execution p) (Program.Execution q) (Program.Execution (p ++ q)) where
    trans h₁ h₂ := Program.Execution.seq h₁ h₂

  namespace Program.Execution

    /-!
      ### Single-instruction programs

      One lemma per primitive instruction: the building blocks for `calc`
      chains. Each is the corresponding `State` operation, packaged as a
      one-instruction program execution.
    -/

    theorem inc (s : State) : s ==[ bf! { + } ]=> s.inc := by
      exact Fragment.ExecutionList.atom (Transition.isValid_inc s) Fragment.ExecutionList.nil

    theorem dec (s : State) : s ==[ bf! { - } ]=> s.dec := by
      exact Fragment.ExecutionList.atom (Transition.isValid_dec s) Fragment.ExecutionList.nil

    theorem left (s : State) : s ==[ bf! { < } ]=> s.moveLeft := by
      exact Fragment.ExecutionList.atom (Transition.isValid_left s) Fragment.ExecutionList.nil

    theorem right (s : State) : s ==[ bf! { > } ]=> s.moveRight := by
      exact Fragment.ExecutionList.atom (Transition.isValid_right s) Fragment.ExecutionList.nil

    theorem input (s : State) : s ==[ bf! { , } ]=> s.consumeInput := by
      exact Fragment.ExecutionList.atom (Transition.isValid_input s) Fragment.ExecutionList.nil

    theorem output (s : State) : s ==[ bf! { . } ]=> s.writeOutput := by
      exact Fragment.ExecutionList.atom (Transition.isValid_output s) Fragment.ExecutionList.nil

    /-!
      ### Loop reasoning

      `Program.Execution.loop_inv` is the classical total-correctness while
      rule: if the loop
      body preserves an invariant `Inv` while strictly decreasing a natural
      measure `μ`, then from any `Inv`-state the loop terminates in a state
      satisfying `Inv` *and* with a zero guard. The postcondition you
      actually want typically follows from that conjunction: the invariant
      says what is conserved, the zero guard says where it ended up.

      `Program.Execution.loop_dec` is the common special case where the
      measure is the guard cell itself.
    -/

    /--
      The total-correctness while rule: invariant + strictly decreasing
      measure gives termination with the invariant and a zero guard.
    -/
    theorem loop_inv {body : Program} {Inv : State -> Prop} {μ : State -> Nat}
        (hbody : ∀ t, Inv t -> t.tape.current ≠ 0 ->
          ∃ t', (t ==[body]=> t') ∧ Inv t' ∧ μ t' < μ t)
        {s : State} (hs : Inv s) :
        ∃ s', (s ==[ ⟨[.loop body]⟩ ]=> s') ∧ Inv s' ∧ s'.tape.current = 0 := by
      have aux : ∀ (n : Nat) (t : State), μ t ≤ n -> Inv t ->
          ∃ t', (t ==[ ⟨[.loop body]⟩ ]=> t') ∧ Inv t' ∧ t'.tape.current = 0 := by
        intro n
        induction n with
        | zero =>
          intro t hle hinv
          by_cases hz : t.tape.current = 0
          · exact ⟨t, Fragment.ExecutionList.loopDone hz Fragment.ExecutionList.nil, hinv, hz⟩
          · obtain ⟨t', -, -, hdec⟩ := hbody t hinv hz
            omega
        | succ n ih =>
          intro t hle hinv
          by_cases hz : t.tape.current = 0
          · exact ⟨t, Fragment.ExecutionList.loopDone hz Fragment.ExecutionList.nil, hinv, hz⟩
          · obtain ⟨t', hbody_run, hinv', hdec⟩ := hbody t hinv hz
            obtain ⟨t'', hloop, hinv'', hz''⟩ := ih t' (by omega) hinv'
            exact ⟨t'', Fragment.ExecutionList.loopStep hz hbody_run hloop, hinv'', hz''⟩
      exact aux (μ s) s (Nat.le_refl _) hs

    /--
      The measure obligation for the common case: decrementing a nonzero
      cell strictly decreases its numeric value. Stated at the `Cell` level
      so it applies whatever shape `simp` has left the state in.
    -/
    theorem toNat_pred_lt {c : Cell} (h : c ≠ 0) : (c - 1).toNat < c.toNat := by
      have hne : c.toNat ≠ 0 := by
        intro h0
        exact h (UInt64.toNat_inj.mp h0)
      have h1 : (1 : UInt64).toNat = 1 := by
        rfl
      have hone : (1 : UInt64) ≤ c := by
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [UInt64.toNat_sub_of_le _ _ hone]
      omega

    /--
      The while rule specialized to the most common measure: the guard cell
      itself. If the body preserves `Inv` and strictly decreases the guard,
      the loop terminates with `Inv` and a zero guard.
    -/
    theorem loop_dec {body : Program} {Inv : State -> Prop}
        (hbody : ∀ t, Inv t -> t.tape.current ≠ 0 ->
          ∃ t', (t ==[body]=> t') ∧ Inv t'
            ∧ t'.tape.current.toNat < t.tape.current.toNat)
        {s : State} (hs : Inv s) :
        ∃ s', (s ==[ ⟨[.loop body]⟩ ]=> s') ∧ Inv s' ∧ s'.tape.current = 0 := by
      exact loop_inv (μ := fun t => t.tape.current.toNat) hbody hs

  end Program.Execution

  /-!
    ### Frame lemmas

    What executions can and cannot do to the I/O streams:
    - output is append-only, and input is consumed suffix-wise, for *every*
      program (`Program.Execution.output_extends`, `Program.Execution.input_suffix`);
    - a program with no `.` (resp. `,`) leaves the output (resp. input)
      exactly unchanged (`Program.Execution.output_frame`, `Program.Execution.input_frame`).

    These remove the need to carry I/O conjuncts through loop invariants.
  -/


  theorem Transition.IsValid.input_eq {a : Atom} {s s' : State}
      (h : s >-[a]-> s') (ha : a ≠ .input) : s'.input = s.input := by
    cases h <;> dsimp only at *
    case ofInput atom_eq _ => exact absurd atom_eq ha
    all_goals
      rename_i state_eq
      subst state_eq
      simp

  theorem Transition.IsValid.output_eq {a : Atom} {s s' : State}
      (h : s >-[a]-> s') (ha : a ≠ .output) : s'.output = s.output := by
    cases h <;> dsimp only at *
    case ofOutput atom_eq _ => exact absurd atom_eq ha
    all_goals
      rename_i state_eq
      subst state_eq
      simp

  theorem Transition.IsValid.output_extends {a : Atom} {s s' : State}
      (h : s >-[a]-> s') : ∃ tail, s'.output = s.output ++ tail := by
    cases h <;> dsimp only at *
    case ofOutput _ state_eq =>
      subst state_eq
      exact ⟨[s.tape.current], by simp⟩
    all_goals
      rename_i state_eq
      subst state_eq
      exact ⟨[], by simp⟩

  theorem Transition.IsValid.input_suffix {a : Atom} {s s' : State}
      (h : s >-[a]-> s') : s'.input.IsSuffix s.input := by
    cases h <;> dsimp only at *
    case ofInput _ state_eq =>
      subst state_eq
      rw [State.input_consumeInput]
      exact List.drop_suffix 1 _
    all_goals
      rename_i state_eq
      subst state_eq
      simp

  theorem Fragment.ExecutionList.output_extends {fs : List Fragment} {s s' : State}
      (h : ExecutionList fs s s') : ∃ tail, s'.output = s.output ++ tail := by
    induction h with
    | nil =>
      exact ⟨[], by simp⟩
    | atom valid rest ih =>
      obtain ⟨t₁, h₁⟩ := valid.output_extends
      obtain ⟨t₂, h₂⟩ := ih
      exact ⟨t₁ ++ t₂, by rw [h₂, h₁, List.append_assoc]⟩
    | loopDone _ rest ih =>
      exact ih
    | loopStep _ body_run again ih_body ih_again =>
      obtain ⟨t₁, h₁⟩ := ih_body
      obtain ⟨t₂, h₂⟩ := ih_again
      exact ⟨t₁ ++ t₂, by rw [h₂, h₁, List.append_assoc]⟩

  theorem Fragment.ExecutionList.input_suffix {fs : List Fragment} {s s' : State}
      (h : ExecutionList fs s s') : s'.input.IsSuffix s.input := by
    induction h with
    | nil =>
      exact List.suffix_refl _
    | atom valid rest ih =>
      exact ih.trans valid.input_suffix
    | loopDone _ rest ih =>
      exact ih
    | loopStep _ body_run again ih_body ih_again =>
      exact ih_again.trans ih_body

  theorem Fragment.ExecutionList.input_frame :
      ∀ {fs : List Fragment} {s s' : State},
        Fragment.readsInputList fs = false -> ExecutionList fs s s' ->
        s'.input = s.input := by
    intro fs s s' hf h
    induction h with
    | nil =>
      rfl
    | @atom a fs s s' s'' valid rest ih =>
      rw [Fragment.readsInputList, Bool.or_eq_false_iff] at hf
      have ha : a ≠ .input := by
        intro haeq
        subst haeq
        simp [Fragment.readsInput] at hf
      rw [ih hf.2, valid.input_eq ha]
    | @loopDone body fs s s' _ rest ih =>
      rw [Fragment.readsInputList, Bool.or_eq_false_iff] at hf
      exact ih hf.2
    | @loopStep body fs s s' s'' _ body_run again ih_body ih_again =>
      have hf' := hf
      rw [Fragment.readsInputList, Bool.or_eq_false_iff] at hf'
      obtain ⟨bfs⟩ := body
      rw [show Fragment.readsInput (.loop ⟨bfs⟩) = Fragment.readsInputList bfs from rfl]
        at hf'
      rw [ih_again hf, ih_body hf'.1]

  theorem Fragment.ExecutionList.output_frame :
      ∀ {fs : List Fragment} {s s' : State},
        Fragment.writesOutputList fs = false -> ExecutionList fs s s' ->
        s'.output = s.output := by
    intro fs s s' hf h
    induction h with
    | nil =>
      rfl
    | @atom a fs s s' s'' valid rest ih =>
      rw [Fragment.writesOutputList, Bool.or_eq_false_iff] at hf
      have ha : a ≠ .output := by
        intro haeq
        subst haeq
        simp [Fragment.writesOutput] at hf
      rw [ih hf.2, valid.output_eq ha]
    | @loopDone body fs s s' _ rest ih =>
      rw [Fragment.writesOutputList, Bool.or_eq_false_iff] at hf
      exact ih hf.2
    | @loopStep body fs s s' s'' _ body_run again ih_body ih_again =>
      have hf' := hf
      rw [Fragment.writesOutputList, Bool.or_eq_false_iff] at hf'
      obtain ⟨bfs⟩ := body
      rw [show Fragment.writesOutput (.loop ⟨bfs⟩) = Fragment.writesOutputList bfs from rfl]
        at hf'
      rw [ih_again hf, ih_body hf'.1]

  namespace Program.Execution

    /-- Output is append-only: no program can unsay what it has printed. -/
    theorem output_extends {p : Program} {s s' : State} (h : s ==[p]=> s') :
        ∃ tail, s'.output = s.output ++ tail := by
      exact Fragment.ExecutionList.output_extends h

    /-- Input is consumed in order: what remains is a suffix of what was there. -/
    theorem input_suffix {p : Program} {s s' : State} (h : s ==[p]=> s') :
        s'.input.IsSuffix s.input := by
      exact Fragment.ExecutionList.input_suffix h

    /-- A program with no `,` leaves the input exactly unchanged. -/
    theorem input_frame {p : Program} {s s' : State}
        (hp : p.readsInput = false) (h : s ==[p]=> s') : s'.input = s.input := by
      exact Fragment.ExecutionList.input_frame hp h

    /-- A program with no `.` leaves the output exactly unchanged. -/
    theorem output_frame {p : Program} {s s' : State}
        (hp : p.writesOutput = false) (h : s ==[p]=> s') : s'.output = s.output := by
      exact Fragment.ExecutionList.output_frame hp h

  end Program.Execution

  /-!
    Brainfuck is deterministic: a program admits at most one final state from
    a given start state. (There is deliberately no totality counterpart —
    `[+]`-style programs admit *no* final state, which is how divergence is
    modelled.)
  -/
  theorem Fragment.ExecutionList.deterministic
      {fs : List Fragment} {s s₁ s₂ : State}
      (h₁ : ExecutionList fs s s₁)
      (h₂ : ExecutionList fs s s₂)
      : s₁ = s₂ := by
    induction h₁ generalizing s₂ with
    | nil =>
      cases h₂
      rfl
    | atom valid rest ih =>
      cases h₂ with
      | atom valid₂ rest₂ =>
        have mid_eq := Transition.IsValid.deterministic valid valid₂
        subst mid_eq
        exact ih rest₂
    | loopDone cell_zero rest ih =>
      cases h₂ with
      | loopDone cell_zero₂ rest₂ => exact ih rest₂
      | loopStep cell_nonzero₂ _ _ => exact absurd cell_zero cell_nonzero₂
    | loopStep cell_nonzero body_run again ih_body ih_again =>
      cases h₂ with
      | loopDone cell_zero₂ _ => exact absurd cell_zero₂ cell_nonzero
      | loopStep cell_nonzero₂ body_run₂ again₂ =>
        have mid_eq := ih_body body_run₂
        subst mid_eq
        exact ih_again again₂

  theorem Fragment.Execution.deterministic {f : Fragment} {s s₁ s₂ : State}
      (h₁ : Execution f s s₁) (h₂ : Execution f s s₂) : s₁ = s₂ := by
    exact Fragment.ExecutionList.deterministic h₁ h₂

  theorem Program.Execution.deterministic {p : Program} {s s₁ s₂ : State}
      (h₁ : s ==[p]=> s₁) (h₂ : s ==[p]=> s₂) : s₁ = s₂ := by
    exact Fragment.ExecutionList.deterministic h₁ h₂

  namespace Program

    /--
      Divergence composes with execution: if `p` runs from `s` to `s'` and
      `q` diverges from `s'`, then `p ++ q` diverges from `s`. (Uses
      determinism: any complete run of `p ++ q` must pass through `s'`.)
    -/
    theorem diverges_append {p q : Program} {s s' : State}
        (hp : s ==[p]=> s') (hq : q.Diverges s') : (p ++ q).Diverges s := by
      intro ⟨sT, hexec⟩
      rw [Program.execution_iff, Program.append_inner,
        Fragment.executionList_append_iff] at hexec
      obtain ⟨mid, hp', hq'⟩ := hexec
      have hmid : mid = s' := Fragment.ExecutionList.deterministic hp' hp
      subst hmid
      exact hq ⟨sT, hq'⟩

    /-- The empty loop diverges from any state with a nonzero guard. -/
    theorem empty_loop_diverges {s : State} (h : s.tape.current ≠ 0) :
        (Program.loop (Program.mk [])).Diverges s := by
      intro ⟨sT, hexec⟩
      exact h (Fragment.execution_loop_empty_iff.mp hexec).1

  end Program

end Brainfuck
