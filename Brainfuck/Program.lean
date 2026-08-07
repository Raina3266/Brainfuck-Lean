import Brainfuck.Trans

namespace Brainfuck

  mutual

    /--
      A brainfuck program: a sequence of fragments.

      Loops contain their bodies (rather than being bracket tokens), so
      well-bracketedness holds by construction and the position during
      execution can live in the derivation of the execution relation.
    -/
    structure Program where
      inner : List Fragment
      deriving BEq

    /-- A single executable piece of a program: a primitive or a loop. -/
    inductive Fragment where
      | atom (inner : Atom)
      | loop (inner : Program)
      deriving BEq

  end

  /-!
    ### Syntactic I/O predicates

    Whether a program contains a `,` (respectively `.`) anywhere, including
    inside loops. Consumed by the frame lemmas in `Execution.lean`: a program
    that cannot read leaves the input untouched, and one that cannot write
    leaves the output untouched.
  -/

  mutual

    /-- Does this fragment contain a `,` anywhere? -/
    def Fragment.readsInput : Fragment -> Bool
      | .atom .input => true
      | .atom _      => false
      | .loop ⟨fs⟩   => Fragment.readsInputList fs

    /-- Does any fragment in the list contain a `,`? -/
    def Fragment.readsInputList : List Fragment -> Bool
      | []      => false
      | f :: fs => f.readsInput || Fragment.readsInputList fs

  end

  mutual

    /-- Does this fragment contain a `.` anywhere? -/
    def Fragment.writesOutput : Fragment -> Bool
      | .atom .output => true
      | .atom _       => false
      | .loop ⟨fs⟩    => Fragment.writesOutputList fs

    /-- Does any fragment in the list contain a `.`? -/
    def Fragment.writesOutputList : List Fragment -> Bool
      | []      => false
      | f :: fs => f.writesOutput || Fragment.writesOutputList fs

  end

  /-- The program consisting of a single loop with the given body. -/
  def Program.loop (body : Program) : Program :=
    Program.mk [Fragment.loop body]

  /-- Does the program contain a `,` anywhere? -/
  def Program.readsInput (p : Program) : Bool :=
    Fragment.readsInputList p.inner

  /-- Does the program contain a `.` anywhere? -/
  def Program.writesOutput (p : Program) : Bool :=
    Fragment.writesOutputList p.inner

  /-- Programs concatenate by concatenating their fragments. -/
  instance : Append Program where
    append p q := ⟨p.inner ++ q.inner⟩

  @[simp] theorem Program.append_inner (p q : Program) :
      (p ++ q).inner = p.inner ++ q.inner := by
    rfl

  /-- Is this one of the eight meaningful brainfuck characters? -/
  def isInstructionChar (c : Char) : Bool :=
    c == '+' || c == '-' || c == '<' || c == '>' ||
    c == ',' || c == '.' || c == '[' || c == ']'

  /-- Is this a loop bracket? -/
  def isBracketChar (c : Char) : Bool :=
    c == '[' || c == ']'

  namespace Program

    /-- What the parser does with one source character. -/
    private inductive ParseToken where
      | atom (a : Atom)
      | beginLoop
      | endLoop
      | comment

    /--
      Classify one source character. An if-chain rather than a pattern match:
      the conditions show up as clean `c = '+'`-style hypotheses under
      `split_ifs`, which the parser facts below rely on.
    -/
    private def tokenOf (c : Char) : ParseToken :=
      if c = '+' then .atom .inc
      else if c = '-' then .atom .dec
      else if c = '<' then .atom .left
      else if c = '>' then .atom .right
      else if c = ',' then .atom .input
      else if c = '.' then .atom .output
      else if c = '[' then .beginLoop
      else if c = ']' then .endLoop
      else .comment

    /--
      The parser's small-step engine. `cur` is the (reversed) sequence being
      built at the innermost level; `stack` holds, for each enclosing `[`
      still open, the partially-built (reversed) sequence it suspended — the
      bottom entry being the top level of the program. Returns the final
      `(stack, cur)` state, or `none` on a `]` with no open loop.

      Kept separate from the final-state check (`parseImpl`) so that the
      parser facts below can do induction over it.
    -/
    private def consume :
        List Char -> List (List Fragment) -> List Fragment ->
          Option (List (List Fragment) × List Fragment)
      | [], stack, cur => some (stack, cur)
      | c :: rest, stack, cur =>
        match tokenOf c with
        | .atom a    => consume rest stack (.atom a :: cur)
        | .beginLoop => consume rest (cur :: stack) []
        | .endLoop   =>
          match stack with
          | []              => none
          | parent :: stack => consume rest stack (.loop ⟨cur.reverse⟩ :: parent)
        | .comment   => consume rest stack cur

    /--
      Parse brainfuck source. Non-instruction characters are comments and are
      skipped. Returns `none` exactly when the brackets are unbalanced: a
      stray `]` fails inside `consume`, an unclosed `[` fails the final
      empty-stack check.
    -/
    private def parseImpl (cs : List Char)
        (stack : List (List Fragment)) (cur : List Fragment) : Option Program :=
      match consume cs stack cur with
      | some ([], done) => some ⟨done.reverse⟩
      | _               => none

    /--
      Parse brainfuck source into a `Program`. Every character other than the
      eight instructions is a comment. `none` iff the brackets are unbalanced.
    -/
    def parse (source : String) : Option Program :=
      parseImpl source.toList [] []

    /--
      Read and parse a brainfuck source file. Throws an `IO` error if the
      file cannot be read or its brackets are unbalanced.
    -/
    def fromFile (path : System.FilePath) : IO Program := do
      let source <- IO.FS.readFile path
      match parse source with
      | some program => return program
      | none => throw (IO.userError s!"{path}: unbalanced brackets in brainfuck program")

    /-!
      ### Parser facts

      The parser is a fold of `consume` over the source characters, so each
      fact below is an induction over `consume`:
      - the parse *result* depends only on the instruction characters
        (`parse_eq_of_filter_eq`), so comments may be inserted anywhere
        without changing the parse (`parse_insert_comment`);
      - parse *success* depends only on the brackets
        (`parse_isSome_iff_of_bracket_filter_eq`), so inserting non-bracket
        characters may change the program but never whether it parses
        (`parse_isSome_insert_nonbracket`);
      - parsing concatenates (`parse_append`).
    -/

    private theorem tokenOf_eq_comment {c : Char} (h : isInstructionChar c = false) :
        tokenOf c = .comment := by
      simp only [isInstructionChar, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩ := h
      simp [tokenOf, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

    private theorem tokenOf_not_bracket {c : Char} (h : isBracketChar c = false) :
        tokenOf c ≠ .beginLoop ∧ tokenOf c ≠ .endLoop := by
      simp only [isBracketChar, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      unfold tokenOf
      split_ifs <;> simp_all

    /-- Comment characters do not affect the parser state. -/
    private theorem consume_filter {cs : List Char} :
        ∀ {stack cur},
          consume cs stack cur = consume (cs.filter isInstructionChar) stack cur := by
      induction cs with
      | nil => intro stack cur; rfl
      | cons c rest ih =>
        intro stack cur
        by_cases h : isInstructionChar c
        · rw [List.filter_cons_of_pos h]
          simp only [consume]
          cases tokenOf c with
          | atom a    => exact ih
          | beginLoop => exact ih
          | endLoop   =>
            cases stack with
            | nil           => rfl
            | cons parent s => exact ih
          | comment   => exact ih
        · have hc : isInstructionChar c = false := by simpa using h
          rw [List.filter_cons_of_neg (by simp [hc])]
          simp only [consume, tokenOf_eq_comment hc]
          exact ih

    /--
      The evolution of the stack *depth* ignores the accumulated fragments:
      two runs over the same source from equally-deep states stay equally
      deep (and fail together).
    -/
    private theorem consume_length_congr {cs : List Char} :
        ∀ {stack₁ cur₁ stack₂ cur₂}, stack₁.length = stack₂.length →
          (consume cs stack₁ cur₁).map (fun r => r.1.length)
            = (consume cs stack₂ cur₂).map (fun r => r.1.length) := by
      induction cs with
      | nil => intro _ _ _ _ h; simp [consume, h]
      | cons c rest ih =>
        intro stack₁ cur₁ stack₂ cur₂ h
        simp only [consume]
        cases tokenOf c with
        | atom a    => exact ih h
        | beginLoop => exact ih (by simp [h])
        | endLoop   =>
          cases stack₁ with
          | nil =>
            cases stack₂ with
            | nil        => rfl
            | cons p₂ s₂ => simp at h
          | cons p₁ s₁ =>
            cases stack₂ with
            | nil        => simp at h
            | cons p₂ s₂ => exact ih (by simpa using h)
        | comment   => exact ih h

    /-- Non-bracket characters do not affect the stack depth's evolution. -/
    private theorem consume_length_filter {cs : List Char} :
        ∀ {stack cur},
          (consume cs stack cur).map (fun r => r.1.length)
            = (consume (cs.filter isBracketChar) stack cur).map (fun r => r.1.length) := by
      induction cs with
      | nil => intro stack cur; rfl
      | cons c rest ih =>
        intro stack cur
        by_cases h : isBracketChar c
        · have hc : c = '[' ∨ c = ']' := by
            simpa [isBracketChar] using h
          rw [List.filter_cons_of_pos h]
          rcases hc with rfl | rfl
          · simp only [consume]
            exact ih
          · simp only [consume]
            cases stack with
            | nil           => rfl
            | cons parent s => exact ih
        · have hc : isBracketChar c = false := by simpa using h
          rw [List.filter_cons_of_neg (by simp [hc])]
          obtain ⟨hb, he⟩ := tokenOf_not_bracket hc
          simp only [consume]
          cases htok : tokenOf c with
          | atom a    =>
            rw [ih]
            exact consume_length_congr rfl
          | beginLoop => exact absurd htok hb
          | endLoop   => exact absurd htok he
          | comment   => exact ih

    /-- `consume` composes over concatenation of sources. -/
    private theorem consume_append {cs₁ cs₂ : List Char} :
        ∀ {stack cur},
          consume (cs₁ ++ cs₂) stack cur
            = (consume cs₁ stack cur).bind (fun r => consume cs₂ r.1 r.2) := by
      induction cs₁ with
      | nil => intro stack cur; rfl
      | cons c rest ih =>
        intro stack cur
        simp only [List.cons_append, consume]
        cases tokenOf c with
        | atom a    => exact ih
        | beginLoop => exact ih
        | endLoop   =>
          cases stack with
          | nil           => rfl
          | cons parent s => exact ih
        | comment   => exact ih

    /-- Append `extra` to the last (bottom-most) level of the stack. -/
    private def extendLast (extra : List Fragment) :
        List (List Fragment) -> List (List Fragment)
      | []             => []
      | [s]            => [s ++ extra]
      | s :: r :: rest => s :: extendLast extra (r :: rest)

    /--
      Append `extra` to the *bottom* level of the parser state — the level
      that becomes the final program once all open loops above it close.
    -/
    private def extendState (extra : List Fragment) :
        List (List Fragment) × List Fragment -> List (List Fragment) × List Fragment
      | ([], cur)         => ([], cur ++ extra)
      | (s :: stack, cur) => (extendLast extra (s :: stack), cur)

    /--
      The parser never looks at fragments it has already built: running from
      a state with `extra` pre-planted at the bottom is the same as running
      from the plain state and planting `extra` afterwards.
    -/
    private theorem consume_extendState {extra : List Fragment} :
        ∀ {cs : List Char} {stack : List (List Fragment)} {cur : List Fragment},
          consume cs (extendState extra (stack, cur)).1 (extendState extra (stack, cur)).2
            = (consume cs stack cur).map (extendState extra) := by
      intro cs
      induction cs with
      | nil =>
        intro stack cur
        simp [consume]
      | cons c rest ih =>
        intro stack cur
        cases stack with
        | nil =>
          show consume (c :: rest) [] (cur ++ extra) = _
          simp only [consume]
          cases tokenOf c with
          | atom a    =>
            show consume rest [] ((.atom a :: cur) ++ extra) = _
            exact ih (stack := []) (cur := .atom a :: cur)
          | beginLoop =>
            show consume rest (extendLast extra [cur]) [] = _
            exact ih (stack := [cur]) (cur := [])
          | endLoop   => rfl
          | comment   =>
            show consume rest [] (cur ++ extra) = _
            exact ih (stack := []) (cur := cur)
        | cons s stack' =>
          cases stack' with
          | nil =>
            show consume (c :: rest) [s ++ extra] cur = _
            simp only [consume]
            cases tokenOf c with
            | atom a    =>
              show consume rest [s ++ extra] (.atom a :: cur) = _
              exact ih (stack := [s]) (cur := .atom a :: cur)
            | beginLoop =>
              show consume rest (extendLast extra [cur, s]) [] = _
              exact ih (stack := [cur, s]) (cur := [])
            | endLoop   =>
              show consume rest [] ((.loop ⟨cur.reverse⟩ :: s) ++ extra) = _
              exact ih (stack := []) (cur := .loop ⟨cur.reverse⟩ :: s)
            | comment   =>
              show consume rest [s ++ extra] cur = _
              exact ih (stack := [s]) (cur := cur)
          | cons r stack'' =>
            show consume (c :: rest) (s :: extendLast extra (r :: stack'')) cur = _
            simp only [consume]
            cases tokenOf c with
            | atom a    =>
              exact ih (stack := s :: r :: stack'') (cur := .atom a :: cur)
            | beginLoop =>
              show consume rest (extendLast extra (cur :: s :: r :: stack'')) [] = _
              exact ih (stack := cur :: s :: r :: stack'') (cur := [])
            | endLoop   =>
              exact ih (stack := r :: stack'') (cur := .loop ⟨cur.reverse⟩ :: s)
            | comment   =>
              exact ih (stack := s :: r :: stack'') (cur := cur)

    private theorem parseImpl_eq_some_iff {cs : List Char} {p : Program} :
        parseImpl cs [] [] = some p ↔ consume cs [] [] = some ([], p.inner.reverse) := by
      unfold parseImpl
      cases h : consume cs [] [] with
      | none => simp
      | some r =>
        obtain ⟨stack, done⟩ := r
        cases stack with
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq, true_and]
          constructor
          · intro hp
            rw [← hp]
            simp
          · intro hd
            rw [hd]
            simp only [List.reverse_reverse]
            cases p
            rfl
        | cons s st => simp

    private theorem parseImpl_isSome_iff {cs : List Char} :
        (parseImpl cs [] []).isSome
          ↔ (consume cs [] []).map (fun r => r.1.length) = some 0 := by
      unfold parseImpl
      cases h : consume cs [] [] with
      | none => simp
      | some r =>
        obtain ⟨stack, done⟩ := r
        cases stack <;> simp

    /--
      The parse depends only on the meaningful characters: sources that agree
      after discarding comments parse identically. Inserting, removing, or
      moving comment characters can never change the result.
    -/
    theorem parse_eq_of_filter_eq {s₁ s₂ : String}
        (h : s₁.toList.filter isInstructionChar = s₂.toList.filter isInstructionChar) :
        parse s₁ = parse s₂ := by
      unfold parse parseImpl
      rw [consume_filter, h, ← consume_filter]

    /--
      Comments are invisible: inserting any string of non-instruction
      characters anywhere in a source does not change how it parses.
    -/
    theorem parse_insert_comment {pre mid post : String}
        (h : ∀ c ∈ mid.toList, isInstructionChar c = false) :
        parse (pre ++ mid ++ post) = parse (pre ++ post) := by
      apply parse_eq_of_filter_eq
      have hmid : mid.toList.filter isInstructionChar = [] := by
        exact List.filter_eq_nil_iff.mpr (by simpa using h)
      simp [List.filter_append, hmid]

    /--
      Whether a source parses depends only on its brackets: sources that
      agree after discarding everything but `[` and `]` succeed or fail
      together (their programs may of course differ).
    -/
    theorem parse_isSome_iff_of_bracket_filter_eq {s₁ s₂ : String}
        (h : s₁.toList.filter isBracketChar = s₂.toList.filter isBracketChar) :
        (parse s₁).isSome ↔ (parse s₂).isSome := by
      unfold parse
      rw [parseImpl_isSome_iff, parseImpl_isSome_iff,
        consume_length_filter, h, ← consume_length_filter]

    /--
      Inserting non-bracket characters anywhere cannot make a parse fail,
      nor rescue a failing one.
    -/
    theorem parse_isSome_insert_nonbracket {pre mid post : String}
        (h : ∀ c ∈ mid.toList, isBracketChar c = false) :
        (parse (pre ++ mid ++ post)).isSome ↔ (parse (pre ++ post)).isSome := by
      apply parse_isSome_iff_of_bracket_filter_eq
      have hmid : mid.toList.filter isBracketChar = [] := by
        exact List.filter_eq_nil_iff.mpr (by simpa using h)
      simp [List.filter_append, hmid]

    /-- Parsing concatenates: valid programs compose by appending sources. -/
    theorem parse_append {s₁ s₂ : String} {p₁ p₂ : Program}
        (h₁ : parse s₁ = some p₁) (h₂ : parse s₂ = some p₂) :
        parse (s₁ ++ s₂) = some (p₁ ++ p₂) := by
      rw [parse, parseImpl_eq_some_iff] at h₁ h₂
      rw [parse, parseImpl_eq_some_iff]
      rw [String.toList_append, consume_append, h₁, Option.bind_some]
      have hext := consume_extendState (extra := p₁.inner.reverse)
        (cs := s₂.toList) (stack := []) (cur := [])
      rw [h₂] at hext
      simpa [extendState, List.reverse_append] using hext

  end Program

  /-!
    ### The `bf! { ... }` macro

    `bf! { + - [ - > + < ] }` elaborates, at compile time, to the explicit
    `Program` term. Instructions must be whitespace-separated (so that Lean's
    tokenizer sees them as individual tokens). Loops are grammar rules, so
    unbalanced brackets are a parse error.

    Comments: Lean's own comments work inside the braces (`-- ...` and
    `/- ... -/`), and bare words/numbers are also skipped. Note that an
    *unspaced* `--` really is a Lean comment — matching how editors
    highlight it.
  -/

  section BfMacro

    open Lean

    declare_syntax_cat bf_frag

    syntax "+" : bf_frag
    syntax "-" : bf_frag
    syntax "<" : bf_frag
    syntax ">" : bf_frag
    syntax "," : bf_frag
    syntax "." : bf_frag
    syntax "[" bf_frag* "]" : bf_frag
    /-- Bare words and numbers are brainfuck comments. -/
    syntax ident : bf_frag
    syntax num : bf_frag

    /--
      Translate one fragment of brainfuck syntax to a term, or `none` for
      comment fragments.
    -/
    private partial def bfFragToTerm? :
        TSyntax `bf_frag -> MacroM (Option (TSyntax `term))
      | `(bf_frag| +) => return some (<- `(Fragment.atom Atom.inc))
      | `(bf_frag| -) => return some (<- `(Fragment.atom Atom.dec))
      | `(bf_frag| <) => return some (<- `(Fragment.atom Atom.left))
      | `(bf_frag| >) => return some (<- `(Fragment.atom Atom.right))
      | `(bf_frag| ,) => return some (<- `(Fragment.atom Atom.input))
      | `(bf_frag| .) => return some (<- `(Fragment.atom Atom.output))
      | `(bf_frag| [ $body:bf_frag* ]) => do
        let terms <- body.raw.filterMapM
          (fun stx => bfFragToTerm? ⟨stx⟩)
        return some (<- `(Fragment.loop (Program.mk [$terms,*])))
      | `(bf_frag| $_:ident) => return none
      | `(bf_frag| $_:num) => return none
      | _ => Macro.throwUnsupported

    /--
      `bf! { + - [ - > + < ] }`: a `Program` literal in brainfuck syntax.
      A pure syntax transformation; see the section docstring for the
      spacing and comment rules.
    -/
    macro "bf!" "{" frags:bf_frag* "}" : term => do
      let terms <- frags.raw.filterMapM
        (fun stx => bfFragToTerm? ⟨stx⟩)
      `(Program.mk [$terms,*])

    private def atomToSyntax : Atom -> MacroM (TSyntax `term)
      | .inc    => `(Atom.inc)
      | .dec    => `(Atom.dec)
      | .left   => `(Atom.left)
      | .right  => `(Atom.right)
      | .input  => `(Atom.input)
      | .output => `(Atom.output)

    mutual

      private partial def fragmentToSyntax : Fragment -> MacroM (TSyntax `term)
        | .atom a => do `(Fragment.atom $(<- atomToSyntax a))
        | .loop p => do `(Fragment.loop $(<- programToSyntax p))

      private partial def programToSyntax : Program -> MacroM (TSyntax `term)
        | ⟨frags⟩ => do
          let elems <- frags.toArray.mapM fragmentToSyntax
          `(Program.mk [$elems,*])

    end

    /--
      String-literal form: `bf! "+-[->+<]"`.

      Unlike `bf! {...}`, the content is raw characters via `Program.parse`:
      no spacing requirements, and arbitrary comment characters are filtered
      out. Use this form for programs pasted from files; `"` and `\` need
      escaping (or use a raw literal, `bf! r"..."`).
    -/
    macro "bf!" s:str : term => do
      match Program.parse s.getString with
      | some p => programToSyntax p
      | none => Macro.throwErrorAt s "bf!: unbalanced brackets in brainfuck program"

    /--
      `embed_bf! "path/to/file.bf"`: read and parse a brainfuck source file
      at *compile time*, elaborating to the explicit `Program` term — the
      generated code does not depend on the file at runtime. Relative paths
      resolve against the directory `lake` is invoked from (the workspace
      root). Unreadable files and unbalanced brackets are compile errors.

      Caveat: Lake does not track the file as a build input, so editing it
      does not trigger recompilation of the embedding module.
    -/
    elab "embed_bf!" path:str : term => do
      let source <- IO.FS.readFile path.getString
      match Program.parse source with
      | some p =>
        let stx <- Lean.Elab.liftMacroM (programToSyntax p)
        Lean.Elab.Term.elabTerm stx (some (Lean.mkConst ``Program))
      | none =>
        Lean.throwErrorAt path s!"embed_bf!: unbalanced brackets in {path.getString}"

  end BfMacro

  #guard bf! { + }   == ⟨ [.atom .inc] ⟩ 
  #guard bf! { - }   == ⟨ [.atom .dec] ⟩ 
  #guard bf! { + - } == ⟨ [.atom .inc, .atom .dec] ⟩ 

  -- Two "-" symbols are interpreted by Lean as comments. These cause the macro
  -- to fail, but we should check that the parser still parses them when passed
  -- via string literal.
  #guard match Program.parse "--" with 
  | .none         => false
  | .some program => program == ⟨ [.atom .dec, .atom .dec] ⟩ 

end Brainfuck

