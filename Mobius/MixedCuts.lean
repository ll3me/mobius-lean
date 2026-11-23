import Mobius.Bounded
import Mobius.EightSquare

/-!
# Turning the proof cut does not shrink an unsigned crossing

The four-legged wire W requires x=v and y=u. A proof label may select *either*
of the two alternative cuts, and carry an arbitrary local predicate on each
side. Each sound rectangle covers at most one of the q² positive wire entries.
The signed eight-square construction evades this bound by cancellation.
-/

namespace Mobius.MixedCuts

def Wire (x y u v : α) : Prop := x = v ∧ y = u

inductive Grouping where
  | row       -- (x,y) | (v,u)
  | column    -- (x,u) | (v,y)
  deriving DecidableEq, Repr

structure Rectangle (α : Type) where
  grouping : Grouping
  left : α → α → Prop
  right : α → α → Prop

def Rectangle.Covers (r : Rectangle α) (x y u v : α) : Prop :=
  match r.grouping with
  | .row => r.left x y ∧ r.right v u
  | .column => r.left x u ∧ r.right v y

def IsCover (rects : Fin s → Rectangle α) : Prop :=
  ∀ x y u v, (∃ i, (rects i).Covers x y u v) ↔ Wire x y u v

/-- Splice *left* from one diagonal proof and *right* from another. The two
    possible cuts disagree about which middle leg is taken from which proof. -/
theorem singleton_on_diagonal (r : Rectangle α)
    (sound : ∀ x y u v, r.Covers x y u v → Wire x y u v)
    (h : r.Covers x y y x) (h' : r.Covers x' y' y' x') : x = x' ∧ y = y' := by
  obtain ⟨cut, left, right⟩ := r
  cases cut with
  | row => exact sound x y y' x' ⟨h.1, h'.2⟩
  | column =>
    have crossed := sound x y' y x' ⟨h.1, h'.2⟩
    exact ⟨crossed.1, crossed.2.symm⟩

private theorem nonempty_side (i : Fin (q * q)) : 0 < q := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q => omega

/-- Enumerate the q² wire entries by quotient and remainder. -/
def decode (i : Fin (q * q)) : Fin q × Fin q :=
  (⟨i.val / q, (Nat.div_lt_iff_lt_mul (nonempty_side i)).mpr i.isLt⟩,
   ⟨i.val % q, Nat.mod_lt _ (nonempty_side i)⟩)

/-- Inverse of the finite wire-entry enumeration. -/
def encode (x y : Fin q) : Fin (q * q) :=
  ⟨y.val + q * x.val, calc
    y.val + q * x.val < q + q * x.val := Nat.add_lt_add_right y.isLt _
    _ = q * (x.val + 1) := by simp [Nat.mul_add, Nat.add_comm]
    _ ≤ q * q := Nat.mul_le_mul_left q x.isLt⟩

theorem encode_decode (i : Fin (q * q)) :
    encode (decode i).1 (decode i).2 = i :=
  Fin.ext (Nat.mod_add_div _ _)

private theorem decode_encode (x y : Fin q) : decode (encode x y) = (x,y) := by
  have hq : 0 < q := Nat.zero_lt_of_lt x.isLt
  apply Prod.ext
  · apply Fin.ext
    change (y.val + q * x.val) / q = x.val
    simp [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt y.isLt]
  · apply Fin.ext
    change (y.val + q * x.val) % q = y.val
    simp [Nat.mod_eq_of_lt y.isLt]

/-- General alphabet form; only an embedded q-element subset is needed. -/
theorem cover_lower_bound (embed : Fin q → α)
    (inj : ∀ x y, embed x = embed y → x = y) (rects : Fin s → Rectangle α)
    (cover : IsCover rects) : q * q ≤ s := by
  classical
  have diagonal (x y : α) : ∃ i, (rects i).Covers x y y x :=
    (cover x y y x).mpr ⟨rfl, rfl⟩
  let tag (i : Fin (q*q)) :=
    Classical.choose (diagonal (embed (decode i).1) (embed (decode i).2))
  have spec (i : Fin (q*q)) :=
    Classical.choose_spec (diagonal (embed (decode i).1) (embed (decode i).2))
  apply Bounded.fin_size_le tag
  intro i j eq
  have hj := spec j
  change (rects (tag j)).Covers _ _ _ _ at hj
  rw [← eq] at hj
  have h := singleton_on_diagonal (rects (tag i))
    (fun x y u v hh => (cover x y u v).mp ⟨_, hh⟩) (spec i) hj
  have pair : decode i = decode j := Prod.ext (inj _ _ h.1) (inj _ _ h.2)
  calc
    i = encode (decode i).1 (decode i).2 := (encode_decode i).symm
    _ = encode (decode j).1 (decode j).2 := congrArg (fun a => encode a.1 a.2) pair
    _ = j := encode_decode j

/-- One rectangle per wire entry meets the lower bound. -/
def singletonCover (i : Fin (q*q)) : Rectangle (Fin q) :=
  ⟨.row, fun x y => (x,y) = decode i, fun v u => (v,u) = decode i⟩

theorem singletonCover_correct (q : Nat) : IsCover (singletonCover (q := q)) := by
  intro x y u v
  constructor
  · rintro ⟨i, h⟩
    have xy : (x,y) = decode i := h.1
    have vu : (v,u) = decode i := h.2
    exact ⟨congrArg Prod.fst (xy.trans vu.symm), congrArg Prod.snd (xy.trans vu.symm)⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨encode x y, (decode_encode x y).symm, (decode_encode x y).symm⟩

theorem eight_symbol_cover_needs_64 (rects : Fin s → Rectangle EightSquare.Block)
    (cover : IsCover rects) : 64 ≤ s :=
  cover_lower_bound (q := 8) (fun i : Fin 8 => (BitVec.ofFin i : EightSquare.Block)) (fun _ _ h => congrArg BitVec.toFin h) rects cover

/-- Integer terms may cancel. Their nonzero support *individually* is always
    a rectangle. A different cut is permitted for every term. -/
structure Separated (α : Type) where
  grouping : Grouping
  left : α → α → Int
  right : α → α → Int

def Separated.value (t : Separated α) (x y u v : α) : Int :=
  match t.grouping with
  | .row => t.left x y * t.right v u
  | .column => t.left x u * t.right v y

def Separated.support (t : Separated α) : Rectangle α :=
  ⟨t.grouping, fun a b => t.left a b ≠ 0, fun a b => t.right a b ≠ 0⟩

theorem Separated.support_iff (t : Separated α) (x y u v : α) :
    t.support.Covers x y u v ↔ t.value x y u v ≠ 0 := by
  cases t with
  | mk grouping left right =>
    cases grouping <;> simp [support, Rectangle.Covers, value]

def total (terms : Fin s → Separated α) (x y u v : α) : Int :=
  (List.ofFn (fun i => (terms i).value x y u v)).sum

private theorem sum_nonneg_and_strict (xs : List Int) (h : ∀ a ∈ xs, 0 ≤ a) :
    0 ≤ xs.sum ∧ ∀ a ∈ xs, a ≠ 0 → 0 < xs.sum := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
    have hz := h z (by simp)
    obtain ⟨hn, hs⟩ := ih (fun a ha => h a (by simp [ha]))
    simp only [List.sum_cons]
    refine ⟨by omega, ?_⟩
    intro a ha ha0
    rcases List.mem_cons.mp ha with rfl | hm
    · omega
    · have := hs _ hm ha0; omega

private theorem sum_zero_of_all_zero (xs : List Int) (h : ∀ a ∈ xs, a = 0) :
    xs.sum = 0 := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.sum_cons]
    rw [h z (by simp), ih (fun a ha => h a (by simp [ha])), Int.zero_add]

/-- Nonnegativity is needed only on entries *outside* the wire. Even negative
    coefficients on positive entries do not reduce the rectangle bound. -/
theorem support_cover_of_nonnegative_off_wire (terms : Fin s → Separated α)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v)
    (off : ∀ x y u v, ¬ Wire x y u v → ∀ i, 0 ≤ (terms i).value x y u v) :
    IsCover (fun i => (terms i).support) := by
  classical
  intro x y u v
  let entries := List.ofFn (fun i => (terms i).value x y u v)
  constructor
  · rintro ⟨i, hi⟩
    by_cases on : Wire x y u v
    · exact on
    · exfalso
      have nonneg (z : Int) (hz : z ∈ entries) : 0 ≤ z := by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
        exact off _ _ _ _ on i
      have positive := (sum_nonneg_and_strict entries nonneg).2 _
        (List.mem_ofFn.mpr ⟨i,rfl⟩) (((terms i).support_iff _ _ _ _).mp hi)
      have ne : total terms x y u v ≠ 0 := Int.ne_of_gt positive
      exact on ((wire x y u v).mp ne)
  · intro on
    apply Classical.byContradiction
    intro none
    have zeros (z : Int) (hz : z ∈ entries) : z = 0 := by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      apply Classical.byContradiction
      intro ne
      exact none ⟨i, ((terms i).support_iff _ _ _ _).mpr ne⟩
    exact ((wire x y u v).mpr on) (sum_zero_of_all_zero entries zeros)

theorem short_decomposition_has_negative_off_wire (embed : Fin q → α)
    (inj : ∀ x y, embed x = embed y → x = y) (terms : Fin s → Separated α)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v)
    (short : s < q*q) :
    ∃ x y u v i, ¬ Wire x y u v ∧ (terms i).value x y u v < 0 := by
  classical
  apply Classical.byContradiction
  intro noNegative
  have off x y u v (hw : ¬ Wire x y u v) i : 0 ≤ (terms i).value x y u v := by
    apply Int.le_of_not_gt
    exact fun neg => noNegative ⟨x,y,u,v,i,hw,neg⟩
  have big := cover_lower_bound embed inj _ (support_cover_of_nonnegative_off_wire terms wire off)
  omega

/-- The concrete sixteen rank-one terms from the signed eight-square identity. -/
def signed16 (i : Fin 16) : Separated EightSquare.Block :=
  let k := BitVec.ofNat 3 i.val
  ⟨if i.val < 8 then .row else .column, EightSquare.bond k, EightSquare.bond k⟩

private theorem paired_sums (f g : EightSquare.Block → Int) :
    (List.ofFn fun i : Fin 16 =>
       if i.val < 8 then f (BitVec.ofNat 3 i.val) else g (BitVec.ofNat 3 i.val)).sum =
      EightSquare.sum8 f + EightSquare.sum8 g := by
  have expanded : (List.ofFn fun i : Fin 16 =>
      if i.val < 8 then f (BitVec.ofNat 3 i.val) else g (BitVec.ofNat 3 i.val)) =
      [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
       g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7] := by rfl
  rw [expanded]
  simp [EightSquare.sum8, EightSquare.blocks, Int.add_assoc]

theorem signed16_exact (x y u v : EightSquare.Block) :
    total signed16 x y u v = 2 * EightSquare.crossing x y u v := by
  rw [EightSquare.crossing_factorizations]
  let f k := EightSquare.bond k x y * EightSquare.bond k v u
  let g k := EightSquare.bond k x u * EightSquare.bond k v y
  have terms (i : Fin 16) : (signed16 i).value x y u v =
      (if i.val < 8 then f (.ofNat 3 i.val) else g (.ofNat 3 i.val)) := by
    by_cases hi : i.val < 8 <;> simp [signed16, Separated.value, hi, f, g]
  simpa only [total, terms] using paired_sums f g

/-- A particular signed decomposition necessarily uses a negative summand
    where its total is zero. This follows from the lower bound, independently
    of inspecting any sign table. -/
theorem signed16_cancels_off_wire :
    ∃ x y u v i, ¬ Wire x y u v ∧ (signed16 i).value x y u v < 0 := by
  apply short_decomposition_has_negative_off_wire (q := 8)
    (fun i : Fin 8 => (BitVec.ofFin i : EightSquare.Block))
    (fun _ _ h => congrArg BitVec.toFin h) signed16 _ (by decide)
  intro x y u v
  rw [signed16_exact]
  by_cases h : Wire x y u v <;> simp_all [Wire, EightSquare.crossing]

/-- A small explicit zero entry: label zero contributes -1 on the row cut,
    while label nine contributes +1 on the column cut. -/
theorem cancellation_witness :
    ¬ Wire (0 : EightSquare.Block) 0 1 1 ∧
    (signed16 0).value 0 0 1 1 = -1 ∧
    (signed16 9).value 0 0 1 1 = 1 ∧ total signed16 0 0 1 1 = 0 := by
  unfold Wire
  decide

end Mobius.MixedCuts
