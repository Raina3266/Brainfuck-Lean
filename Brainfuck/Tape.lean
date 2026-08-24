import Mathlib.Tactic

namespace Brainfuck

  /--
    A single tape cell: a 64-bit machine integer with wrapping arithmetic
    (the ring `ℤ/2⁶⁴`).

    Why 64-bit: wide enough that theorems over all cells cannot be settled by
    enumeration, while keeping the concrete executable arithmetic that `simp`,
    `omega` and friends understand (vs. parameterizing the semantics over an
    abstract cell type).
  -/
  abbrev Cell := UInt64

  /-- Cells serialize as JSON numbers (via `toNat`; JSON numbers are
  arbitrary-precision, so the full 64-bit range is safe). -/
  instance : Lean.ToJson Cell where
    toJson c := Lean.toJson c.toNat

  /--
    The raw tape state. The tape is infinite in both directions.

    `left` and `right` represent "the cells to the left/right of the current
    cell". Since the tape is infinite, all cells beyond these are assumed to
    contain `0`. I.e. `left := [1, 2, 3]` is equivalent to `left := [1, 2, 3, 0,
    0]`
  -/
  private structure RawTape where
    left  : List Cell
    cur   : Cell
    right : List Cell

  namespace RawTape

    /--
      The denotation of a raw tape: the cell value at a signed offset from the
      head (`0` is the head itself). Two raw tapes that `read` equally are
      observationally indistinguishable.
    -/
    private def read (t : RawTape) : Int -> Cell
      | .ofNat 0       => t.cur
      | .ofNat (n + 1) => t.right.getD n 0
      | .negSucc n     => t.left.getD n 0

    private def setCurrent (t : RawTape) (c : Cell) : RawTape :=
      { t with cur := c }

    private def moveRight (t : RawTape) : RawTape :=
      match t.right with
      | []        => ⟨t.cur :: t.left, 0, []⟩
      | c :: rest => ⟨t.cur :: t.left, c, rest⟩

    private def moveLeft (t : RawTape) : RawTape :=
      match t.left with
      | []        => ⟨[], 0, t.cur :: t.right⟩
      | c :: rest => ⟨rest, c, t.cur :: t.right⟩

    private theorem read_write (t : RawTape) (c : Cell) (i : Int) :
        (t.setCurrent c).read i = if i = 0 then c else t.read i := by
      cases i with
      | ofNat n => cases n with
        | zero => simp [read, setCurrent]
        | succ m =>
          simp [read, setCurrent]
          omega
      | negSucc n => simp [read, setCurrent]

    private theorem read_moveRight (t : RawTape) (i : Int) :
        t.moveRight.read i = t.read (i + 1) := by
      obtain ⟨l, c, r⟩ := t
      cases r with
      | nil => cases i with
        | ofNat n   => cases n <;> rfl
        | negSucc n => cases n <;> rfl
      | cons c' rest => cases i with
        | ofNat n   => cases n <;> rfl
        | negSucc n => cases n <;> rfl

    /--
      `moveLeft` shifts the denotation: stated in `+ 1` form so that both
      sides reduce definitionally in every case (subtraction on `Int.ofNat`
      patterns does not). The subtraction form is `Tape.read_moveLeft`.
    -/
    private theorem read_moveLeft_add (t : RawTape) (i : Int) :
        t.moveLeft.read (i + 1) = t.read i := by
      obtain ⟨l, c, r⟩ := t
      cases l with
      | nil => cases i with
        | ofNat n   => cases n <;> rfl
        | negSucc n => cases n <;> rfl
      | cons c' rest => cases i with
        | ofNat n   => cases n <;> rfl
        | negSucc n => cases n <;> rfl

    /-!
      #### Canonical representatives

      Serialization must respect the quotient: equivalent zippers have to
      produce identical output. `normalize` trims trailing zeros, and
      `normalize_eq_of_read_eq` shows equivalent tapes normalize to the same
      representative — exactly the respect obligation a lifted serializer
      needs.
    -/

    /-- Drop trailing zeros from a cell list. -/
    private def trimZeros : List Cell -> List Cell
      | [] => []
      | c :: rest =>
        match trimZeros rest with
        | [] => if c = 0 then [] else [c]
        | trimmed => c :: trimmed

    private theorem trimZeros_nil_of_zero {l : List Cell}
        (h : ∀ n, l.getD n 0 = 0) : trimZeros l = [] := by
      induction l with
      | nil => rfl
      | cons c rest ih =>
        have hc : c = 0 := h 0
        have hrest : trimZeros rest = [] := ih (fun n => h (n + 1))
        simp [trimZeros, hrest, hc]

    private theorem trimZeros_congr {l₁ l₂ : List Cell}
        (h : ∀ n, l₁.getD n 0 = l₂.getD n 0) : trimZeros l₁ = trimZeros l₂ := by
      induction l₁ generalizing l₂ with
      | nil =>
        rw [trimZeros_nil_of_zero (fun n => (h n).symm)]
        rfl
      | cons c rest ih =>
        cases l₂ with
        | nil =>
          rw [trimZeros_nil_of_zero (fun n => h n)]
          rfl
        | cons c₂ rest₂ =>
          have hc : c = c₂ := h 0
          have hrest := ih (fun n => h (n + 1))
          simp [trimZeros, hrest, hc]

    /-- The canonical representative of a tape: trailing zeros trimmed. -/
    private def normalize (t : RawTape) : RawTape :=
      { left := trimZeros t.left, cur := t.cur, right := trimZeros t.right }

    /-- Observationally equal tapes have equal canonical representatives. -/
    private theorem normalize_eq_of_read_eq {a b : RawTape} (h : a.read = b.read) :
        a.normalize = b.normalize := by
      have hcur : a.cur = b.cur := congrFun h 0
      have hleft : ∀ n, a.left.getD n 0 = b.left.getD n 0 :=
        fun n => congrFun h (.negSucc n)
      have hright : ∀ n, a.right.getD n 0 = b.right.getD n 0 :=
        fun n => congrFun h (.ofNat (n + 1))
      simp [normalize, hcur, trimZeros_congr hleft, trimZeros_congr hright]

  end RawTape

  /-- Raw tapes are equivalent when they read equally at every offset. -/
  private instance tapeSetoid : Setoid RawTape where
    r a b := a.read = b.read
    iseqv := by
      constructor
      · intro a
        rfl
      · intro a b h
        exact h.symm
      · intro a b c h₁ h₂
        exact h₁.trans h₂

  /--
    A bi-infinite tape of cells with a head position.

    Defined as a quotient of the private zipper representation by observational
    equivalence (`RawTape.read`), so equality of `Tape`s is equality of the
    abstract tape, not of any particular representation. The public API below is
    fully characterized by `Tape.read` via the `@[simp]` lemmas and `Tape.ext`;
    the representation is not otherwise observable.
  -/
  def Tape : Type := Quotient tapeSetoid

  /-- The `Tape` represented by a given raw zipper (its equivalence class). -/
  private def RawTape.toTape (t : RawTape) : Tape :=
    Quotient.mk tapeSetoid t

  namespace Tape

    /-- The all-zero tape. -/
    def empty : Tape := RawTape.toTape { left := [], cur := 0, right := [] }

    instance : Inhabited Tape where
      default := empty

    /--
      The tape holding `cells` at absolute positions `0, 1, ...` (zero
      elsewhere), with the head placed at absolute position `initialPosition`.

      The position may lie outside the cells: `fromCells [1, 2, 3] 5` puts the
      head on a zero cell with the `1, 2, 3` further away to its left, and a
      negative position puts the head left of all the cells.
    -/
    def fromCells (cells : List Cell) (initialPosition : Int) : Tape :=
      match initialPosition with
      | .ofNat n =>
        RawTape.toTape {
          left   := List.replicate (n - cells.length) 0 ++ (cells.take n).reverse
          cur    := cells.getD n 0
          right  := cells.drop (n + 1)
        }
      | .negSucc n =>
        RawTape.toTape {
          left   := []
          cur    := 0
          right  := List.replicate n 0 ++ cells
        }

    /--
      The cell value at a signed offset from the head (`0` is the head).

      This is the one primitive observation on tapes: every other operation is
      specified by how it affects `read`.
    -/
    def read (t : Tape) (i : Int) : Cell :=
      Quotient.lift RawTape.read (fun _ _ h => h) t i

    /--
      `t[i]` notation for `read`. Every index is valid (the tape is
      bi-infinite), hence the trivial validity predicate.
    -/
    instance : GetElem Tape Int Cell fun _ _ => True where
      getElem t i _ := t.read i

    /--
      `Nat`-indexed variant so that numeric literals work: a bare `tape[0]`
      defaults its index to `Nat`. Negative offsets need an `Int` index, e.g.
      `tape[(-1 : Int)]`.
    -/
    instance : GetElem Tape Nat Cell fun _ _ => True where
      getElem t i _ := t.read i

    @[simp] theorem getElem_int_eq_read (t : Tape) (i : Int) : t[i] = t.read i := by
      rfl

    @[simp] theorem getElem_nat_eq_read (t : Tape) (n : Nat) : t[n] = t.read n := by
      rfl

    /--
      The tape with `left`/`right` around `cur`, nearest-the-head-first
      (cells beyond the lists are zero). The public counterpart of the
      private zipper representation, for building tapes from concrete
      lists (e.g. abstraction functions in verification code).
    -/
    def ofParts (left : List Cell) (cur : Cell) (right : List Cell) : Tape :=
      RawTape.toTape { left := left, cur := cur, right := right }

    @[simp] theorem read_ofParts_zero (l : List Cell) (c : Cell) (r : List Cell) :
        (ofParts l c r).read 0 = c := by
      rfl

    @[simp] theorem read_ofParts_pos (l : List Cell) (c : Cell) (r : List Cell) (n : Nat) :
        (ofParts l c r).read (Int.ofNat (n + 1)) = r.getD n 0 := by
      rfl

    @[simp] theorem read_ofParts_neg (l : List Cell) (c : Cell) (r : List Cell) (n : Nat) :
        (ofParts l c r).read (Int.negSucc n) = l.getD n 0 := by
      rfl

    /-- Drop trailing zeros from a cell list (public face of the
    canonicalization used by `toParts` and serialization). -/
    def trimZeros : List Cell -> List Cell :=
      RawTape.trimZeros

    @[simp] theorem trimZeros_nil : trimZeros [] = [] := by
      rfl

    theorem trimZeros_cons (c : Cell) (rest : List Cell) :
        trimZeros (c :: rest) =
          match trimZeros rest with
          | [] => if c = 0 then [] else [c]
          | trimmed => c :: trimmed := by
      rfl

    /--
      The canonical parts of a tape: `left`/`right` nearest-the-head-first
      with trailing zeros trimmed. Well-defined on the quotient because
      equivalent zippers normalize identically.
    -/
    def toParts (t : Tape) : List Cell × Cell × List Cell :=
      Quotient.lift
        (fun raw => ((raw.normalize).left, (raw.normalize).cur, (raw.normalize).right))
        (by
          intro a b hab
          simp [RawTape.normalize_eq_of_read_eq hab])
        t

    @[simp] theorem toParts_ofParts (l : List Cell) (c : Cell) (r : List Cell) :
        toParts (ofParts l c r) = (trimZeros l, c, trimZeros r) := by
      rfl

    /-- The cell under the head. -/
    def current (t : Tape) : Cell :=
      t.read 0

    /-- Replace the cell under the head. -/
    def setCurrent (t : Tape) (value : Cell) : Tape :=
      Quotient.map (fun raw => raw.setCurrent value)
        (by
          intro a b hab
          show (RawTape.setCurrent a value).read = (RawTape.setCurrent b value).read
          funext i
          rw [RawTape.read_write, RawTape.read_write, show a.read = b.read from hab])
        t

    /-- Increment the cell under the head (wrapping). -/
    def increment (t : Tape) : Tape :=
      t.setCurrent (t.current + 1)

    /-- Decrement the cell under the head (wrapping). -/
    def decrement (t : Tape) : Tape :=
      t.setCurrent (t.current - 1)

    /-- Move the head one cell to the right. -/
    def moveRight (t : Tape) : Tape :=
      Quotient.map RawTape.moveRight
        (by
          intro a b hab
          show a.moveRight.read = b.moveRight.read
          funext i
          rw [RawTape.read_moveRight, RawTape.read_moveRight,
            show a.read = b.read from hab])
        t

    /-- Move the head one cell to the left. -/
    def moveLeft (t : Tape) : Tape :=
      Quotient.map RawTape.moveLeft
        (by
          intro a b hab
          show a.moveLeft.read = b.moveLeft.read
          funext i
          rw [show i = i - 1 + 1 from by omega, RawTape.read_moveLeft_add,
            RawTape.read_moveLeft_add, show a.read = b.read from hab])
        t

    /-!
      ### Specification

      `read` fully characterizes every operation; together with `ext` these
      lemmas are the complete interface for reasoning about tapes.
    -/

    /-- Tapes that read equally everywhere are equal. -/
    @[ext] theorem ext {t₁ t₂ : Tape} (h : ∀ i, t₁.read i = t₂.read i) : t₁ = t₂ := by
      induction t₁ using Quotient.inductionOn with
      | h a =>
        induction t₂ using Quotient.inductionOn with
        | h b => exact Quotient.sound (funext h)


    @[simp] theorem read_empty (i : Int) : empty.read i = 0 := by
      cases i with
      | ofNat n   => cases n <;> rfl
      | negSucc n => rfl

    @[simp] theorem current_eq_read_zero (t : Tape) : t.current = t.read 0 := by
      rfl

    @[simp] theorem read_setCurrent (t : Tape) (value : Cell) (i : Int) :
        (t.setCurrent value).read i = if i = 0 then value else t.read i := by
      induction t using Quotient.inductionOn with
      | h a => exact RawTape.read_write a value i

    @[simp] theorem read_moveRight (t : Tape) (i : Int) :
        t.moveRight.read i = t.read (i + 1) := by
      induction t using Quotient.inductionOn with
      | h a => exact RawTape.read_moveRight a i

    @[simp] theorem read_moveLeft (t : Tape) (i : Int) :
        t.moveLeft.read i = t.read (i - 1) := by
      induction t using Quotient.inductionOn with
      | h a =>
        have h := RawTape.read_moveLeft_add a (i - 1)
        rw [show i - 1 + 1 = i from by omega] at h
        exact h

    @[simp] theorem read_increment (t : Tape) (i : Int) :
        t.increment.read i = if i = 0 then t.read 0 + 1 else t.read i := by
      simp [increment]

    @[simp] theorem read_decrement (t : Tape) (i : Int) :
        t.decrement.read i = if i = 0 then t.read 0 - 1 else t.read i := by
      simp [decrement]

    @[simp] theorem increment_decrement (t : Tape) : t.increment.decrement = t := by
      ext i
      simp only [read_decrement, read_increment]
      split
      · next h => simp [h]
      · rfl

    @[simp] theorem decrement_increment (t : Tape) : t.decrement.increment = t := by
      ext i
      simp only [read_increment, read_decrement]
      split
      · next h => simp [h]
      · rfl

    /-!
      ### Sanity checks

      The theorems that motivated the quotient: moving right then left (or left
      then right) is the identity, on the nose.
    -/

    @[simp] theorem moveRight_moveLeft (t : Tape) : t.moveRight.moveLeft = t := by
      ext i
      have h : i - 1 + 1 = i := by omega
      simp [h]

    @[simp] theorem moveLeft_moveRight (t : Tape) : t.moveLeft.moveRight = t := by
      ext i
      have h : i + 1 - 1 = i := by omega
      simp [h]

  end Tape

  /-!
    ### Serialization

    JSON format: `{"left": [...], "cur": n, "right": [...]}` with cells as
    numbers and the side lists nearest-the-head-first, trailing zeros
    trimmed. Serialization goes through the canonical representative, so
    equal tapes produce equal JSON (the respect proof for the quotient lift
    is `RawTape.normalize_eq_of_read_eq`).
  -/

  deriving instance Lean.ToJson for RawTape

  instance : Lean.ToJson Tape where
    toJson := Quotient.lift (fun raw => Lean.toJson raw.normalize)
      (by
        intro a b hab
        exact congrArg Lean.toJson (RawTape.normalize_eq_of_read_eq hab))

end Brainfuck
