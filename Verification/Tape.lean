/-
  The abstraction bridge between the Aeneas-generated interpreter tape
  (`brainfuck.interpreter.Tape`: two growable arrays plus a head position)
  and the abstract bi-infinite `Brainfuck.Tape`.

  The key definitions are `cellAt` (the abstract cell at an absolute
  position) and `absTape` (the abstraction function); the fundamental lemma
  `read_absTape` characterizes `absTape` entirely in terms of `cellAt`.
  On top of these we prove spec lemmas for the generated tape operations.
-/
import Verification.Cell
import Verification.Platform

namespace Verification

  open Aeneas Aeneas.Std Result
  open Brainfuck (Cell)
  open brainfuck

  /-
    The whole bridge assumes a 64-bit target; see `Verification.Platform`.
    The linter is silenced because the standing assumption is deliberately
    included in every declaration, used or not.
  -/
  set_option linter.unusedSectionVars false
  variable [Fact (Usize.numBits = 64)]

  /-! ### List helpers -/

  private theorem getD_map_range {α : Type} (f : Nat -> α) (m n : Nat) (d : α) :
      ((List.range m).map f).getD n d = if n < m then f n else d := by
    by_cases h : n < m
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
      simp [h]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [h]

  private theorem getD_set {α : Type} (l : List α) (i k : Nat) (x d : α)
      (hi : i < l.length) :
      (l.set i x).getD k d = if k = i then x else l.getD k d := by
    rcases eq_or_ne k i with h | h
    · subst h
      rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      simp [hi]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_neg (Ne.symm h),
        List.getD_eq_getElem?_getD, if_neg h]

  private theorem getD_resize_of_le {α : Type} (l : List α) (m k : Nat) (d : α)
      (h : l.length ≤ m) :
      (l.resize m d).getD k d = l.getD k d := by
    rw [List.resize, if_pos (by omega), List.take_of_length_le h]
    rcases Nat.lt_or_ge k l.length with hk | hk
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hk]
    · rw [List.getD_eq_default _ _ hk, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hk, List.getElem?_replicate]
      split <;> simp

  private theorem unwrap_or_getD (l : List U64) (n : Nat) (d : U64) :
      core.option.Option.unwrap_or l[n]? d = l.getD n d := by
    rw [List.getD_eq_getElem?_getD]
    cases l[n]? <;> rfl

  /-! ### The abstraction function -/

  /--
    The abstract cell stored at absolute position `p` by the concrete tape:
    nonnegative positions live in `nonnegative`, negative position `p` lives
    at index `-p - 1` of `negative`, and cells beyond either array are `0`.
  -/
  def cellAt (t : interpreter.Tape) (p : Int) : Cell :=
    if 0 <= p then toCell (t.nonnegative.val.getD p.toNat 0#u64)
    else toCell (t.negative.val.getD (-p - 1).toNat 0#u64)

  private theorem cellAt_oob (t : interpreter.Tape) (p : Int)
      (h₁ : 0 ≤ p → (t.nonnegative.val.length : Int) ≤ p)
      (h₂ : p < 0 → (t.negative.val.length : Int) ≤ -p - 1) :
      cellAt t p = 0 := by
    unfold cellAt
    split
    · next hp =>
      rw [List.getD_eq_default _ _ (by have := h₁ hp; omega)]
      simp
    · next hp =>
      rw [List.getD_eq_default _ _ (by have := h₂ (by omega); omega)]
      simp

  /--
    The abstraction function: the tape denoted by the interpreter state,
    with the head-relative view demanded by `Brainfuck.Tape`. The side lists
    are long enough to cover both arrays as seen from the head.
  -/
  def absTape (t : interpreter.Tape) : Brainfuck.Tape :=
    Brainfuck.Tape.ofParts
      ((List.range (t.negative.val.length + t.head.val.toNat)).map
        (fun (k : Nat) => cellAt t (t.head.val - 1 - (k : Int))))
      (cellAt t t.head.val)
      ((List.range (t.nonnegative.val.length + (-t.head.val).toNat)).map
        (fun (k : Nat) => cellAt t (t.head.val + 1 + (k : Int))))

  /--
    The fundamental lemma: reading the abstract tape at offset `i` is
    reading the concrete tape at absolute position `head + i`.
  -/
  theorem read_absTape (t : interpreter.Tape) (i : Int) :
      (absTape t).read i = cellAt t (t.head.val + i) := by
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        show (absTape t).read 0 = _
        unfold absTape
        rw [Brainfuck.Tape.read_ofParts_zero]
        simp
      | succ m =>
        unfold absTape
        rw [Brainfuck.Tape.read_ofParts_pos, getD_map_range]
        simp only [Int.ofNat_eq_natCast]
        split
        · next h =>
          congr 1
          omega
        · next h =>
          refine (cellAt_oob t _ ?_ ?_).symm <;> intro hp <;> omega
    | negSucc n =>
      unfold absTape
      rw [Brainfuck.Tape.read_ofParts_neg, getD_map_range]
      simp only [Int.negSucc_eq]
      split
      · next h =>
        congr 1
        omega
      · next h =>
        refine (cellAt_oob t _ ?_ ?_).symm <;> intro hp <;> omega

  /--
    If a concrete tape agrees with `t` everywhere except at the head
    position (where it holds `c`), then it abstracts to
    `(absTape t).setCurrent c`.
  -/
  private theorem absTape_setCurrent_of_cellAt (t t' : interpreter.Tape) (c : Cell)
      (hhead : t'.head = t.head)
      (hcell : ∀ p : Int, cellAt t' p = if p = t.head.val then c else cellAt t p) :
      absTape t' = (absTape t).setCurrent c := by
    apply Brainfuck.Tape.ext
    intro i
    rw [read_absTape, Brainfuck.Tape.read_setCurrent, read_absTape, hhead, hcell]
    by_cases h : i = 0
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

  /-! ### The invariant on reachable tape states -/

  /--
    Well-formedness of interpreter tape states: the head is strictly above
    `i64::MIN`, which protects `checked_neg` in `negative_index`. All the
    `Usize` index bounds that used to live here follow from the 64-bit
    platform assumption (see `Verification.Platform`).
  -/
  structure TapeInv (t : interpreter.Tape) : Prop where
    head_lb : I64.min < t.head.val

  /-! ### Scalar helpers -/

  private theorem hcast_val (p : I64) (h0 : 0 ≤ p.val)
      (h1 : p.val ≤ (Usize.max : Int)) :
      ((IScalar.hcast .Usize p).val : Int) = p.val := by
    have h := IScalar.hcast_inBounds_spec .Usize p (by scalar_tac)
    simpa only [Aeneas.Std.lift, WP.spec_ok] using h

  /-! ### `Tape.new` -/

  private theorem cellAt_zero_lists (t : interpreter.Tape)
      (hneg : t.negative.val = []) (hnn : t.nonnegative.val = [0#u64]) (p : Int) :
      cellAt t p = 0 := by
    unfold cellAt
    split
    · rw [hnn]
      rcases Nat.eq_zero_or_pos p.toNat with h | h
      · rw [h]
        simp
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp
    · rw [hneg]
      simp

  theorem new_spec :
      ∃ t0, interpreter.Tape.new = ok t0 ∧
        absTape t0 = Brainfuck.Tape.empty ∧
        t0.head.val = 0 ∧ TapeInv t0 := by
    unfold interpreter.Tape.new
    simp only [Aeneas.Std.lift, bind_tc_ok]
    refine ⟨_, rfl, ?_, by simp, ?_⟩
    · apply Brainfuck.Tape.ext
      intro i
      rw [read_absTape, Brainfuck.Tape.read_empty]
      exact cellAt_zero_lists _ rfl rfl _
    · exact ⟨by scalar_tac⟩

  /-! ### `negative_index` -/

  theorem negative_index_spec (p : I64) (hneg : p.val < 0) (hmin : I64.min < p.val) :
      ∃ f, interpreter.negative_index p = ok f ∧ f.val = -p.val - 1 := by
    have h1 := I64.checked_sub_bv_spec 0#i64 p
    cases hc : core.num.checked_sub_IScalar 0#i64 p with
    | none =>
      rw [hc] at h1
      exfalso
      simp at h1
      scalar_tac
    | some z =>
      rw [hc] at h1
      obtain ⟨-, -, hz, -⟩ := h1
      simp at hz
      have h2 := I64.checked_sub_bv_spec z 1#i64
      cases hc2 : core.num.checked_sub_IScalar z 1#i64 with
      | none =>
        rw [hc2] at h2
        exfalso
        simp at h2
        scalar_tac
      | some f =>
        rw [hc2] at h2
        obtain ⟨-, -, hf, -⟩ := h2
        refine ⟨f, ?_, by scalar_tac⟩
        unfold interpreter.negative_index core.num.I64.checked_neg I64.checked_sub
        rw [hc]
        simp only [bind_tc_ok, core.option.Option.expect, Result.ofOption,
          Aeneas.Std.lift]
        rw [hc2]

  /-! ### `Tape.get` -/

  private theorem slice_get_eq (v : alloc.vec.Vec U64) (i : Usize) :
      core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice U64)
        (alloc.vec.Vec.deref v) i = ok v.val[i.val]? := by
    simp only [core.slice.Slice.get, core.slice.index.Usize.get,
      Slice.getElem?_Usize_eq, alloc.vec.Vec.deref]

  theorem get_spec (t : interpreter.Tape) (p : I64)
      (hmin : I64.min < p.val) :
      ∃ v, interpreter.Tape.get t p = ok v ∧ toCell v = cellAt t p.val := by
    have hhi : p.val ≤ (Usize.max : Int) := le_of_lt (i64_val_lt_usize_max p)
    have hlo : -(Usize.max : Int) ≤ p.val := neg_usize_max_le_i64_val p
    unfold interpreter.Tape.get
      Usize.Insts.CoreConvertTryFromI64TryFromIntError.try_from
    by_cases hp : 0 ≤ p.val
    · rw [if_pos ⟨hp, hhi⟩]
      simp only [bind_tc_ok]
      have hidxv : ((IScalar.hcast .Usize p).val : Int) = p.val := hcast_val p hp hhi
      set idx : Usize := IScalar.hcast .Usize p with hidxdef
      rw [slice_get_eq]
      simp only [bind_tc_ok, core.option.OptionShared0T.copied]
      refine ⟨_, rfl, ?_⟩
      rw [unwrap_or_getD]
      unfold cellAt
      rw [if_pos hp]
      have h : idx.val = p.val.toNat := by omega
      rw [h]
    · rw [if_neg (fun hc => hp hc.1)]
      simp only [bind_tc_ok]
      have hneg : p.val < 0 := by omega
      obtain ⟨f, hf, hfv⟩ := negative_index_spec p hneg hmin
      rw [hf]
      simp only [bind_tc_ok]
      rw [if_pos ⟨by omega, by omega⟩]
      simp only [bind_tc_ok, core.result.Result.expect]
      have hidxv : ((IScalar.hcast .Usize f).val : Int) = f.val :=
        hcast_val f (by omega) (by omega)
      set idx : Usize := IScalar.hcast .Usize f with hidxdef
      rw [slice_get_eq]
      simp only [bind_tc_ok, core.option.OptionShared0T.copied]
      refine ⟨_, rfl, ?_⟩
      rw [unwrap_or_getD]
      unfold cellAt
      rw [if_neg hp]
      have h : idx.val = (-p.val - 1).toNat := by omega
      rw [h]

  /-! ### `Tape.current` -/

  private theorem vec_index_mut_eq (w : alloc.vec.Vec U64) (idx : Usize)
      (h : idx.val < w.val.length) :
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U64) w idx =
        ok (w.val.getD idx.val 0#u64, alloc.vec.Vec.set w idx) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    unfold alloc.vec.Vec.index_mut_usize alloc.vec.Vec.index_usize
    have h1 : w[idx.val]? = some (w.val.getD idx.val 0#u64) := by
      rw [alloc.vec.Vec.getElem?_Nat_eq, List.getElem?_eq_getElem h,
        List.getD_eq_getElem w.val _ h]
    rw [h1]

  private theorem cellAt_set_nonneg (t : interpreter.Tape) (w : alloc.vec.Vec U64)
      (idx : Usize) (v' : U64)
      (hp : 0 ≤ t.head.val) (hidxv : (idx.val : Int) = t.head.val)
      (hwlen : idx.val < w.val.length)
      (hwsame : ∀ k, w.val.getD k 0#u64 = t.nonnegative.val.getD k 0#u64)
      (p : Int) :
      cellAt { t with nonnegative := alloc.vec.Vec.set w idx v' } p =
        if p = t.head.val then toCell v' else cellAt t p := by
    by_cases hph : p = t.head.val
    · rw [if_pos hph]
      unfold cellAt
      rw [if_pos (by omega)]
      simp only [alloc.vec.Vec.set_val_eq]
      rw [getD_set _ _ _ _ _ hwlen, if_pos (by omega)]
    · rw [if_neg hph]
      unfold cellAt
      by_cases hp0 : 0 ≤ p
      · rw [if_pos hp0, if_pos hp0]
        simp only [alloc.vec.Vec.set_val_eq]
        rw [getD_set _ _ _ _ _ hwlen, if_neg (by omega), hwsame]
      · rw [if_neg hp0, if_neg hp0]

  private theorem cellAt_set_neg (t : interpreter.Tape) (w : alloc.vec.Vec U64)
      (idx : Usize) (v' : U64)
      (hp : t.head.val < 0) (hidxv : (idx.val : Int) = -t.head.val - 1)
      (hwlen : idx.val < w.val.length)
      (hwsame : ∀ k, w.val.getD k 0#u64 = t.negative.val.getD k 0#u64)
      (p : Int) :
      cellAt { t with negative := alloc.vec.Vec.set w idx v' } p =
        if p = t.head.val then toCell v' else cellAt t p := by
    by_cases hph : p = t.head.val
    · rw [if_pos hph]
      unfold cellAt
      rw [if_neg (by omega)]
      simp only [alloc.vec.Vec.set_val_eq]
      rw [getD_set _ _ _ _ _ hwlen, if_pos (by omega)]
    · rw [if_neg hph]
      unfold cellAt
      by_cases hp0 : 0 ≤ p
      · rw [if_pos hp0, if_pos hp0]
      · rw [if_neg hp0, if_neg hp0]
        simp only [alloc.vec.Vec.set_val_eq]
        rw [getD_set _ _ _ _ _ hwlen, if_neg (by omega), hwsame]

  private theorem current_post_nonneg (t : interpreter.Tape) (idx : Usize)
      (w : alloc.vec.Vec U64)
      (hlb : I64.min < t.head.val)
      (hp : 0 ≤ t.head.val) (hidxv : (idx.val : Int) = t.head.val)
      (hwlen : idx.val < w.val.length)
      (hwsame : ∀ k, w.val.getD k 0#u64 = t.nonnegative.val.getD k 0#u64) :
      toCell (w.val.getD idx.val 0#u64) = (absTape t).current ∧
      (∀ v', absTape { t with nonnegative := alloc.vec.Vec.set w idx v' } =
        (absTape t).setCurrent (toCell v')) ∧
      (∀ v', ({ t with nonnegative := alloc.vec.Vec.set w idx v' } :
        interpreter.Tape).head = t.head) ∧
      (∀ v', TapeInv { t with nonnegative := alloc.vec.Vec.set w idx v' }) := by
    refine ⟨?_, ?_, fun v' => rfl, fun v' => ⟨hlb⟩⟩
    · rw [hwsame]
      have h0 : (absTape t).current = cellAt t t.head.val := by
        rw [Brainfuck.Tape.current_eq_read_zero, read_absTape]
        congr 1
        omega
      rw [h0]
      unfold cellAt
      rw [if_pos hp]
      have h : idx.val = t.head.val.toNat := by omega
      rw [h]
    · intro v'
      apply absTape_setCurrent_of_cellAt
      · rfl
      · exact cellAt_set_nonneg t w idx v' hp hidxv hwlen hwsame

  private theorem current_post_neg (t : interpreter.Tape) (idx : Usize)
      (w : alloc.vec.Vec U64)
      (hlb : I64.min < t.head.val)
      (hp : t.head.val < 0) (hidxv : (idx.val : Int) = -t.head.val - 1)
      (hwlen : idx.val < w.val.length)
      (hwsame : ∀ k, w.val.getD k 0#u64 = t.negative.val.getD k 0#u64) :
      toCell (w.val.getD idx.val 0#u64) = (absTape t).current ∧
      (∀ v', absTape { t with negative := alloc.vec.Vec.set w idx v' } =
        (absTape t).setCurrent (toCell v')) ∧
      (∀ v', ({ t with negative := alloc.vec.Vec.set w idx v' } :
        interpreter.Tape).head = t.head) ∧
      (∀ v', TapeInv { t with negative := alloc.vec.Vec.set w idx v' }) := by
    refine ⟨?_, ?_, fun v' => rfl, fun v' => ⟨hlb⟩⟩
    · rw [hwsame]
      have h0 : (absTape t).current = cellAt t t.head.val := by
        rw [Brainfuck.Tape.current_eq_read_zero, read_absTape]
        congr 1
        omega
      rw [h0]
      unfold cellAt
      rw [if_neg (by omega)]
      have h : idx.val = (-t.head.val - 1).toNat := by omega
      rw [h]
    · intro v'
      apply absTape_setCurrent_of_cellAt
      · rfl
      · exact cellAt_set_neg t w idx v' hp hidxv hwlen hwsame

  theorem current_spec (t : interpreter.Tape) (hInv : TapeInv t) :
      ∃ v back, interpreter.Tape.current t = ok (v, back) ∧
        toCell v = (absTape t).current ∧
        (∀ v', absTape (back v') = (absTape t).setCurrent (toCell v')) ∧
        (∀ v', (back v').head = t.head) ∧
        (∀ v', TapeInv (back v')) := by
    obtain ⟨hlb⟩ := hInv
    have hnlb : -(Usize.max : Int) ≤ t.head.val := neg_usize_max_le_i64_val t.head
    have hub : t.head.val < (Usize.max : Int) := i64_val_lt_usize_max t.head
    unfold interpreter.Tape.current
      Usize.Insts.CoreConvertTryFromI64TryFromIntError.try_from
    by_cases hp : 0 ≤ t.head.val
    · rw [if_pos ⟨hp, by omega⟩]
      simp only [bind_tc_ok]
      have hidxv : ((IScalar.hcast .Usize t.head).val : Int) = t.head.val :=
        hcast_val t.head hp (by omega)
      set idx : Usize := IScalar.hcast .Usize t.head with hidxdef
      by_cases hge : t.nonnegative.val.length ≤ idx.val
      · rw [if_pos ((UScalar.le_equiv _ _).mpr (by simpa using hge))]
        obtain ⟨i1, hi1, hi1v⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := idx) (y := 1#usize) (by scalar_tac))
        simp only [UScalar.val] at hi1v
        rw [hi1]
        simp only [bind_tc_ok]
        obtain ⟨w, hw, hwv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.resize_spec core.clone.CloneU64 t.nonnegative i1 0#u64
            (by rfl))
        rw [hw]
        simp only [bind_tc_ok]
        have hi1v' : i1.val = idx.val + 1 := by simpa using hi1v
        have hwlen : idx.val < w.val.length := by
          rw [hwv, List.resize_length]
          omega
        have hwsame : ∀ k, w.val.getD k 0#u64 = t.nonnegative.val.getD k 0#u64 := by
          intro k
          rw [hwv]
          exact getD_resize_of_le _ _ _ _ (by omega)
        rw [vec_index_mut_eq _ _ hwlen]
        simp only [bind_tc_ok]
        obtain ⟨h1, h2, h3, h4⟩ :=
          current_post_nonneg t idx w hlb hp hidxv hwlen hwsame
        exact ⟨_, _, rfl, h1, h2, h3, h4⟩
      · rw [if_neg (fun hc => hge (by simpa using (UScalar.le_equiv _ _).mp hc))]
        simp only [bind_tc_ok]
        have hwlen : idx.val < t.nonnegative.val.length := by omega
        rw [vec_index_mut_eq _ _ hwlen]
        simp only [bind_tc_ok]
        obtain ⟨h1, h2, h3, h4⟩ :=
          current_post_nonneg t idx t.nonnegative hlb hp hidxv hwlen
            (fun k => rfl)
        exact ⟨_, _, rfl, h1, h2, h3, h4⟩
    · rw [if_neg (fun hc => hp hc.1)]
      simp only [bind_tc_ok]
      have hneg : t.head.val < 0 := by omega
      obtain ⟨f, hf, hfv⟩ := negative_index_spec t.head hneg hlb
      rw [hf]
      simp only [bind_tc_ok]
      rw [if_pos ⟨by omega, by omega⟩]
      simp only [bind_tc_ok, core.result.Result.expect]
      have hidxv : ((IScalar.hcast .Usize f).val : Int) = -t.head.val - 1 := by
        rw [hcast_val f (by omega) (by omega)]
        omega
      set idx : Usize := IScalar.hcast .Usize f with hidxdef
      by_cases hge : t.negative.val.length ≤ idx.val
      · rw [if_pos ((UScalar.le_equiv _ _).mpr (by simpa using hge))]
        obtain ⟨i1, hi1, hi1v⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := idx) (y := 1#usize) (by scalar_tac))
        rw [hi1]
        simp only [bind_tc_ok]
        obtain ⟨w, hw, hwv⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.resize_spec core.clone.CloneU64 t.negative i1 0#u64
            (by rfl))
        rw [hw]
        simp only [bind_tc_ok]
        have hi1v' : i1.val = idx.val + 1 := by simpa using hi1v
        have hwlen : idx.val < w.val.length := by
          rw [hwv, List.resize_length]
          omega
        have hwsame : ∀ k, w.val.getD k 0#u64 = t.negative.val.getD k 0#u64 := by
          intro k
          rw [hwv]
          exact getD_resize_of_le _ _ _ _ (by omega)
        rw [vec_index_mut_eq _ _ hwlen]
        simp only [bind_tc_ok]
        obtain ⟨h1, h2, h3, h4⟩ :=
          current_post_neg t idx w hlb hneg hidxv hwlen hwsame
        exact ⟨_, _, rfl, h1, h2, h3, h4⟩
      · rw [if_neg (fun hc => hge (by simpa using (UScalar.le_equiv _ _).mp hc))]
        simp only [bind_tc_ok]
        have hwlen : idx.val < t.negative.val.length := by omega
        rw [vec_index_mut_eq _ _ hwlen]
        simp only [bind_tc_ok]
        obtain ⟨h1, h2, h3, h4⟩ :=
          current_post_neg t idx t.negative hlb hneg hidxv hwlen
            (fun k => rfl)
        exact ⟨_, _, rfl, h1, h2, h3, h4⟩

  /-! ### `trim_trailing_zeros` -/

  /--
    The functional model of `trim_trailing_zeros`: drop the trailing zeros
    of a cell list. Mirrors the recursion of `Brainfuck.Tape.trimZeros`
    so that `map_toCell_dropTrailingZeros` is a simple induction.
  -/
  def dropTrailingZeros : List U64 -> List U64
    | []        => []
    | c :: rest =>
      match dropTrailingZeros rest with
      | []      => if c = 0#u64 then [] else [c]
      | trimmed => c :: trimmed

  theorem map_toCell_dropTrailingZeros (l : List U64) :
      (dropTrailingZeros l).map toCell = Brainfuck.Tape.trimZeros (l.map toCell) := by
    induction l with
    | nil => simp [dropTrailingZeros]
    | cons c rest ih =>
      rw [List.map_cons, Brainfuck.Tape.trimZeros_cons, ← ih]
      show (match dropTrailingZeros rest with
            | []      => if c = 0#u64 then [] else [c]
            | trimmed => c :: trimmed).map toCell = _
      cases h : dropTrailingZeros rest with
      | nil =>
        simp only [List.map_nil]
        by_cases hc : c = 0#u64
        · subst hc
          simp
        · have hc' : ¬ toCell c = 0 := by
            simp only [toCell_eq_zero_iff]
            intro hv
            exact hc (by scalar_tac)
          simp [hc, hc']
      | cons d ds =>
        simp only [List.map_cons]

  private theorem dropTrailingZeros_concat_ne (ys : List U64) (x : U64)
      (hx : x ≠ 0#u64) :
      dropTrailingZeros (ys ++ [x]) = ys ++ [x] := by
    induction ys with
    | nil => simp [dropTrailingZeros, hx]
    | cons c ys ih =>
      rw [List.cons_append, dropTrailingZeros, ih]
      cases h2 : ys ++ [x] with
      | nil       => simp at h2
      | cons d ds => rfl

  private theorem dropTrailingZeros_concat_zero (ys : List U64) :
      dropTrailingZeros (ys ++ [0#u64]) = dropTrailingZeros ys := by
    induction ys with
    | nil => simp [dropTrailingZeros]
    | cons c ys ih =>
      rw [List.cons_append, dropTrailingZeros, ih, dropTrailingZeros]

  private theorem trim_loop_nil (cells : alloc.vec.Vec U64) (h : cells.val = []) :
      ∃ v, interpreter.trim_trailing_zeros_loop cells = ok v ∧
        v.val = dropTrailingZeros cells.val := by
    obtain ⟨l, hl⟩ := cells
    replace h : l = [] := h
    subst h
    have hpop : alloc.vec.Vec.pop Global (⟨[], hl⟩ : alloc.vec.Vec U64) =
        ok (none, ⟨[], hl⟩) := by
      unfold alloc.vec.Vec.pop
      simp
    unfold interpreter.trim_trailing_zeros_loop
    rw [Aeneas.Std.loop]
    unfold interpreter.trim_trailing_zeros_loop.body
    rw [hpop]
    simp only [bind_tc_ok]
    exact ⟨⟨[], hl⟩, rfl, by simp [dropTrailingZeros]⟩

  private theorem trim_loop_spec_aux (n : Nat) :
      ∀ cells : alloc.vec.Vec U64, cells.val.length ≤ n →
        ∃ v, interpreter.trim_trailing_zeros_loop cells = ok v ∧
          v.val = dropTrailingZeros cells.val := by
    induction n with
    | zero =>
      intro cells hlen
      apply trim_loop_nil
      cases h : cells.val with
      | nil       => rfl
      | cons c cs => rw [h] at hlen; simp at hlen
    | succ n ih =>
      intro cells hlen
      obtain ⟨l, hl⟩ := cells
      rcases List.eq_nil_or_concat l with hnil | ⟨ys, x, hcat⟩
      · exact trim_loop_nil _ hnil
      · rw [List.concat_eq_append] at hcat
        subst hcat
        replace hlen : ys.length + 1 ≤ n + 1 := by simpa using hlen
        have hys : ys.length ≤ Usize.max := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hl
          omega
        have hpop : alloc.vec.Vec.pop Global (⟨ys ++ [x], hl⟩ : alloc.vec.Vec U64) =
            ok (some x, ⟨ys, hys⟩) := by
          unfold alloc.vec.Vec.pop
          simp
        unfold interpreter.trim_trailing_zeros_loop
        rw [Aeneas.Std.loop]
        unfold interpreter.trim_trailing_zeros_loop.body
        rw [hpop]
        simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
        by_cases hx : x = 0#u64
        · subst hx
          rw [if_neg (by simp)]
          obtain ⟨v, hv, hvv⟩ := ih ⟨ys, hys⟩ (by simpa using Nat.lt_succ_iff.mp hlen)
          unfold interpreter.trim_trailing_zeros_loop at hv
          refine ⟨v, hv, ?_⟩
          rw [hvv]
          show dropTrailingZeros ys = dropTrailingZeros (ys ++ [0#u64])
          rw [dropTrailingZeros_concat_zero]
        · have hbne : (x != 0#u64) = true := by simp [hx]
          rw [if_pos hbne]
          obtain ⟨v2, hpush, hpushv⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec (⟨ys, hys⟩ : alloc.vec.Vec U64) x
              (by simp only [List.length_append, List.length_cons,
                    List.length_nil] at hl
                  scalar_tac))
          rw [hpush]
          simp only [bind_tc_ok]
          refine ⟨v2, rfl, ?_⟩
          rw [hpushv]
          show ys ++ [x] = dropTrailingZeros (ys ++ [x])
          rw [dropTrailingZeros_concat_ne ys x hx]

  theorem trim_trailing_zeros_spec (cells : alloc.vec.Vec U64) :
      ∃ v, interpreter.trim_trailing_zeros cells = ok v ∧
        v.val = dropTrailingZeros cells.val :=
    trim_loop_spec_aux cells.val.length cells (Nat.le_refl _)

end Verification
