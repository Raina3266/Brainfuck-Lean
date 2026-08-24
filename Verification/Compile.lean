import Brainfuck.Program
import BrainfuckCore.Types

/-!
  # Compilation from tree programs to the flat Rust representation

  The Rust interpreter runs a flat `Vec<Instr>` plus a jump table
  `loop_jump_offset`, where for each `[` at index `i` with matching `]` at
  index `j` we have `loop_jump_offset[i] = j` and `loop_jump_offset[j] = i`
  (all other entries are `0`). This file defines that flattening for the
  verified tree `Program`, over plain lists with `Nat` offsets; the bridge
  to `Vec`/`U32` happens elsewhere.
-/

namespace Brainfuck

  /-- The generated instruction type of the Rust interpreter. -/
  abbrev Instr := brainfuck.analysis.Instr

  /-- Is this instruction one of the two loop brackets? -/
  def Instr.isBracket : Instr -> Bool
    | .BeginLoop => true
    | .EndLoop   => true
    | _          => false

  /-- The flat instruction corresponding to a primitive. -/
  def Atom.toInstr : Atom -> Instr
    | .inc    => .Inc
    | .dec    => .Dec
    | .left   => .Left
    | .right  => .Right
    | .input  => .Input
    | .output => .Output

  @[simp] theorem Atom.toInstr_not_bracket (a : Atom) :
      Instr.isBracket (Atom.toInstr a) = false := by
    cases a <;> rfl

  /-!
    ### Sizes

    The number of flat instructions a fragment compiles to: one per atom,
    and two brackets plus the body for a loop.
  -/

  mutual

    /-- Compiled length of a fragment. -/
    def Fragment.size : Fragment -> Nat
      | .atom _    => 1
      | .loop ⟨fs⟩ => Fragment.sizeList fs + 2

    /-- Compiled length of a fragment list. -/
    def Fragment.sizeList : List Fragment -> Nat
      | []      => 0
      | f :: fs => f.size + Fragment.sizeList fs

  end

  /-- Compiled length of a program. -/
  def Program.size (p : Program) : Nat :=
    Fragment.sizeList p.inner

  /-!
    ### Compilation

    Instruction emission does not depend on where the code is placed, so it
    is defined separately from offset emission; `compile` pairs them up.
    The `base` argument is the absolute index at which the emitted code
    starts, and all jump offsets are absolute. Non-bracket instructions get
    a `0` placeholder offset, matching the Rust parser.
  -/

  mutual

    /-- The flat instructions a fragment compiles to. -/
    def Fragment.instrs : Fragment -> List Instr
      | .atom a    => [Atom.toInstr a]
      | .loop ⟨fs⟩ => .BeginLoop :: (Fragment.instrsList fs ++ [.EndLoop])

    /-- The flat instructions a fragment list compiles to. -/
    def Fragment.instrsList : List Fragment -> List Instr
      | []      => []
      | f :: fs => f.instrs ++ Fragment.instrsList fs

  end

  mutual

    /-- The jump-offset table of a fragment compiled at absolute index `base`. -/
    def Fragment.offsets : Fragment -> Nat -> List Nat
      | .atom _,    _    => [0]
      | .loop ⟨fs⟩, base =>
        (base + Fragment.sizeList fs + 1)
          :: (Fragment.offsetsList fs (base + 1) ++ [base])

    /-- The jump-offset table of a fragment list compiled at absolute index `base`. -/
    def Fragment.offsetsList : List Fragment -> Nat -> List Nat
      | [],      _    => []
      | f :: fs, base => f.offsets base ++ Fragment.offsetsList fs (base + f.size)

  end

  /-- Compile one fragment at absolute index `base`. -/
  def Fragment.compile (f : Fragment) (base : Nat) : List Instr × List Nat :=
    (f.instrs, f.offsets base)

  /-- Compile a fragment list at absolute index `base`. -/
  def Fragment.compileList (fs : List Fragment) (base : Nat) : List Instr × List Nat :=
    (Fragment.instrsList fs, Fragment.offsetsList fs base)

  /-- Compile a whole program, starting at index `0`. -/
  def Program.compile (p : Program) : List Instr × List Nat :=
    Fragment.compileList p.inner 0

  /-!
    ### Lengths
  -/

  mutual

    @[simp] theorem Fragment.instrs_length :
        ∀ (f : Fragment), (Fragment.instrs f).length = f.size
      | .atom _    => by simp [Fragment.instrs, Fragment.size]
      | .loop ⟨fs⟩ => by
        simp [Fragment.instrs, Fragment.size, Fragment.instrsList_length fs]

    @[simp] theorem Fragment.instrsList_length :
        ∀ (fs : List Fragment), (Fragment.instrsList fs).length = Fragment.sizeList fs
      | []      => by simp [Fragment.instrsList, Fragment.sizeList]
      | f :: fs => by
        simp [Fragment.instrsList, Fragment.sizeList, Fragment.instrs_length f,
              Fragment.instrsList_length fs]

  end

  mutual

    @[simp] theorem Fragment.offsets_length :
        ∀ (f : Fragment) (base : Nat), (Fragment.offsets f base).length = f.size
      | .atom _,    base => by simp [Fragment.offsets, Fragment.size]
      | .loop ⟨fs⟩, base => by
        simp [Fragment.offsets, Fragment.size,
              Fragment.offsetsList_length fs (base + 1)]

    @[simp] theorem Fragment.offsetsList_length :
        ∀ (fs : List Fragment) (base : Nat),
          (Fragment.offsetsList fs base).length = Fragment.sizeList fs
      | [],      base => by simp [Fragment.offsetsList, Fragment.sizeList]
      | f :: fs, base => by
        simp [Fragment.offsetsList, Fragment.sizeList, Fragment.offsets_length f base,
              Fragment.offsetsList_length fs (base + f.size)]

  end

  @[simp] theorem Fragment.compile_fst (f : Fragment) (base : Nat) :
      (Fragment.compile f base).1 = f.instrs := by
    rfl

  @[simp] theorem Fragment.compile_snd (f : Fragment) (base : Nat) :
      (Fragment.compile f base).2 = f.offsets base := by
    rfl

  @[simp] theorem Fragment.compileList_fst (fs : List Fragment) (base : Nat) :
      (Fragment.compileList fs base).1 = Fragment.instrsList fs := by
    rfl

  @[simp] theorem Fragment.compileList_snd (fs : List Fragment) (base : Nat) :
      (Fragment.compileList fs base).2 = Fragment.offsetsList fs base := by
    rfl

  theorem Fragment.compile_lengths (f : Fragment) (base : Nat) :
      (Fragment.compile f base).1.length = f.size ∧
      (Fragment.compile f base).2.length = f.size := by
    simp

  theorem Program.compile_fst_length (p : Program) :
      (Program.compile p).1.length = p.size := by
    simp [Program.compile, Program.size]

  theorem Program.compile_snd_length (p : Program) :
      (Program.compile p).2.length = p.size := by
    simp [Program.compile, Program.size]

  /-!
    ### Decomposition and base independence
  -/

  /-- Compiling `f :: fs` is compiling `f`, then `fs` shifted past it. -/
  theorem Fragment.compileList_cons (f : Fragment) (fs : List Fragment) (base : Nat) :
      Fragment.compileList (f :: fs) base =
        ((Fragment.compile f base).1 ++ (Fragment.compileList fs (base + f.size)).1,
         (Fragment.compile f base).2 ++ (Fragment.compileList fs (base + f.size)).2) := by
    simp [Fragment.compileList, Fragment.compile, Fragment.instrsList, Fragment.offsetsList]

  /-- The instructions component does not depend on the base offset. -/
  theorem Fragment.compile_fst_base_irrel (f : Fragment) (b1 b2 : Nat) :
      (Fragment.compile f b1).1 = (Fragment.compile f b2).1 := by
    rfl

  /-!
    ### Base shift

    A uniform `map (+ base)` law is false because non-bracket instructions
    carry a `0` placeholder rather than a jump target. Instead: shifting the
    base adds `base` exactly at the bracket positions. This is the workhorse
    for relating a fragment's local offset table to its placement inside a
    larger program.
  -/

  mutual

    theorem Fragment.offsets_shift :
        ∀ (f : Fragment) (base k : Nat),
          Fragment.offsets f (base + k) =
            List.zipWith (fun ins o => if Instr.isBracket ins then base + o else o)
              (Fragment.instrs f) (Fragment.offsets f k)
      | .atom a,    base, k => by
        simp [Fragment.offsets, Fragment.instrs]
      | .loop ⟨fs⟩, base, k => by
        have hlen : (Fragment.instrsList fs).length =
            (Fragment.offsetsList fs (k + 1)).length := by
          rw [Fragment.instrsList_length, Fragment.offsetsList_length]
        have e1 : base + k + Fragment.sizeList fs + 1 =
            base + (k + Fragment.sizeList fs + 1) := by omega
        have e2 : base + k + 1 = base + (k + 1) := by omega
        simp only [Fragment.offsets, Fragment.instrs,
                   List.zipWith_cons_cons, List.zipWith_append hlen]
        rw [e2, Fragment.offsetsList_shift fs base (k + 1)]
        simp [Instr.isBracket, e1]

    theorem Fragment.offsetsList_shift :
        ∀ (fs : List Fragment) (base k : Nat),
          Fragment.offsetsList fs (base + k) =
            List.zipWith (fun ins o => if Instr.isBracket ins then base + o else o)
              (Fragment.instrsList fs) (Fragment.offsetsList fs k)
      | [],      base, k => by simp [Fragment.offsetsList, Fragment.instrsList]
      | f :: fs, base, k => by
        have hlen : (Fragment.instrs f).length = (Fragment.offsets f k).length := by
          rw [Fragment.instrs_length, Fragment.offsets_length]
        have e : base + k + f.size = base + (k + f.size) := by omega
        simp only [Fragment.offsetsList, Fragment.instrsList, List.zipWith_append hlen]
        rw [Fragment.offsets_shift f base k, e,
            Fragment.offsetsList_shift fs base (k + f.size)]

  end

  /-!
    ### Bounds

    Every offset sitting under a bracket instruction points inside the
    fragment that emitted it: jump targets are internal.
  -/

  mutual

    theorem Fragment.offsets_bounded :
        ∀ (f : Fragment) (base : Nat) (ins : Instr) (o : Nat),
          (ins, o) ∈ List.zip (Fragment.instrs f) (Fragment.offsets f base) ->
          Instr.isBracket ins = true ->
          base ≤ o ∧ o < base + f.size
      | .atom a,    base, ins, o => by
        intro hmem hbr
        simp [Fragment.instrs, Fragment.offsets] at hmem
        rw [hmem.1] at hbr
        simp at hbr
      | .loop ⟨fs⟩, base, ins, o => by
        intro hmem hbr
        have hlen : (Fragment.instrsList fs).length =
            (Fragment.offsetsList fs (base + 1)).length := by
          rw [Fragment.instrsList_length, Fragment.offsetsList_length]
        simp only [Fragment.instrs, Fragment.offsets] at hmem
        rw [List.zip_cons_cons, List.zip_append hlen] at hmem
        simp only [List.mem_cons, List.mem_append, List.zip_cons_cons,
                   List.zip_nil_left, List.not_mem_nil, or_false,
                   Prod.mk.injEq] at hmem
        simp only [Fragment.size]
        rcases hmem with ⟨rfl, rfl⟩ | h | ⟨rfl, rfl⟩
        · omega
        · have := Fragment.offsetsList_bounded fs (base + 1) ins o h hbr
          omega
        · omega

    theorem Fragment.offsetsList_bounded :
        ∀ (fs : List Fragment) (base : Nat) (ins : Instr) (o : Nat),
          (ins, o) ∈ List.zip (Fragment.instrsList fs) (Fragment.offsetsList fs base) ->
          Instr.isBracket ins = true ->
          base ≤ o ∧ o < base + Fragment.sizeList fs
      | [],      base, ins, o => by
        intro hmem _
        simp [Fragment.instrsList, Fragment.offsetsList] at hmem
      | f :: fs, base, ins, o => by
        intro hmem hbr
        have hlen : (Fragment.instrs f).length = (Fragment.offsets f base).length := by
          rw [Fragment.instrs_length, Fragment.offsets_length]
        simp only [Fragment.instrsList, Fragment.offsetsList] at hmem
        rw [List.zip_append hlen] at hmem
        simp only [List.mem_append] at hmem
        simp only [Fragment.sizeList]
        rcases hmem with h | h
        · have := Fragment.offsets_bounded f base ins o h hbr
          omega
        · have := Fragment.offsetsList_bounded fs (base + f.size) ins o h hbr
          omega

  end

  /-!
    ### Pointing lemmas

    For a loop compiled at absolute index `k` with body of compiled length
    `n`: relative index `0` holds `BeginLoop` with offset `k + n + 1`, and
    relative index `n + 1` holds `EndLoop` with offset `k`. In absolute
    terms the two brackets point exactly at each other.
  -/

  theorem Fragment.loop_instr_begin (b : Program) :
      (Fragment.instrs (.loop b))[0]? = some .BeginLoop := by
    obtain ⟨fs⟩ := b
    simp [Fragment.instrs]

  theorem Fragment.loop_offset_begin (b : Program) (k : Nat) :
      (Fragment.offsets (.loop b) k)[0]? =
        some (k + Fragment.sizeList b.inner + 1) := by
    obtain ⟨fs⟩ := b
    simp [Fragment.offsets]

  theorem Fragment.loop_instr_end (b : Program) :
      (Fragment.instrs (.loop b))[Fragment.sizeList b.inner + 1]? =
        some .EndLoop := by
    obtain ⟨fs⟩ := b
    simp [Fragment.instrs]

  theorem Fragment.loop_offset_end (b : Program) (k : Nat) :
      (Fragment.offsets (.loop b) k)[Fragment.sizeList b.inner + 1]? =
        some k := by
    obtain ⟨fs⟩ := b
    simp [Fragment.offsets]

  /-!
    ### Balanced brackets

    `Matched` is the Dyck language over instruction lists: brackets nest and
    match, and in particular an `EndLoop` only ever appears as the closer of
    a `BeginLoop`. Compiled programs are matched.
  -/

  /-- Well-bracketed flat instruction lists. -/
  inductive Matched : List Instr -> Prop where
    | nil  : Matched []
    | cons (ins : Instr) {l : List Instr} :
        Instr.isBracket ins = false -> Matched l -> Matched (ins :: l)
    | loop {b l : List Instr} :
        Matched b -> Matched l -> Matched (.BeginLoop :: (b ++ .EndLoop :: l))

  mutual

    theorem Fragment.instrs_matched_append :
        ∀ (f : Fragment) (l : List Instr),
          Matched l -> Matched (Fragment.instrs f ++ l)
      | .atom a,    l, hl => by
        simpa [Fragment.instrs]
          using Matched.cons (Atom.toInstr a) (Atom.toInstr_not_bracket a) hl
      | .loop ⟨fs⟩, l, hl => by
        have hb : Matched (Fragment.instrsList fs) := by
          simpa using Fragment.instrsList_matched_append fs [] Matched.nil
        simpa [Fragment.instrs] using Matched.loop hb hl

    theorem Fragment.instrsList_matched_append :
        ∀ (fs : List Fragment) (l : List Instr),
          Matched l -> Matched (Fragment.instrsList fs ++ l)
      | [],      l, hl => by simpa [Fragment.instrsList] using hl
      | f :: fs, l, hl => by
        have h2 := Fragment.instrsList_matched_append fs l hl
        have h1 := Fragment.instrs_matched_append f _ h2
        simpa [Fragment.instrsList] using h1

  end

  /-- The compiled instruction stream of any program is well-bracketed. -/
  theorem Program.compile_matched (p : Program) : Matched (Program.compile p).1 := by
    have h := Fragment.instrsList_matched_append p.inner [] Matched.nil
    simpa [Program.compile] using h

  /-!
    ### Sanity checks

    These mirror the Rust tests `parses_instructions_and_jumps` and
    `nested_loops_jump_to_their_own_match` in `rust/src/analysis.rs`.
  -/

  section SanityChecks

    /- `+[->+<].` -/
    private def exampleProgram : Program :=
      Program.mk
        [.atom .inc,
         .loop (Program.mk [.atom .dec, .atom .right, .atom .inc, .atom .left]),
         .atom .output]

    example : (Program.compile exampleProgram).1 =
        [.Inc, .BeginLoop, .Dec, .Right, .Inc, .Left, .EndLoop, .Output] := by
      rfl

    example : (Program.compile exampleProgram).2 = [0, 6, 0, 0, 0, 0, 1, 0] := by
      rfl

    /- `[[]]` -/
    example :
        (Program.compile
          (Program.mk [.loop (Program.mk [.loop (Program.mk [])])])).2 =
          [3, 2, 1, 0] := by
      rfl

  end SanityChecks

end Brainfuck
