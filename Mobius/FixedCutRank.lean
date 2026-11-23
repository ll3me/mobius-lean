import Mobius.MixedCuts

/-!
# Signed rank on one fixed cut

An integer matrix supported on the diagonal, with all diagonal entries
nonzero, needs at least as many rank-one summands as diagonal entries.
We prove this by eliminating a pivot without division. Applied to the
four-legged wire, either fixed cut needs q² terms, even with cancellation.
-/

namespace Mobius.FixedCutRank

open MixedCuts

structure Factor (α : Type) where
  left : α → Int
  right : α → Int

def eval : List (Factor α) → α → α → Int
  | [], _, _ => 0
  | t :: ts, i, j => t.left i * t.right j + eval ts i j

/-- Multiply by the pivot coefficient before subtracting row r, so all
    calculations stay in the integers, with no field or division assumptions. -/
private def eliminate (head : Factor α) (r : α) (t : Factor α) : Factor α :=
  ⟨fun i => head.left r * t.left i - head.left i * t.left r, t.right⟩

private theorem elimination_entry (head : Factor α) (r i j : α) (ts : List (Factor α)) :
    eval (ts.map (eliminate head r)) i j =
      head.left r * eval (head :: ts) i j - head.left i * eval (head :: ts) r j := by
  have aux : eval (ts.map (eliminate head r)) i j =
      head.left r * eval ts i j - head.left i * eval ts r j := by
    induction ts with
    | nil => simp [eval]
    | cons t ts ih =>
      simp only [List.map_cons, eval, eliminate, ih]
      grind
  rw [aux]
  simp only [eval]
  grind

/-- The familiar diagonal rank lower bound, stated for finite lists of
    distinct row/column indices and proved without the linear algebra library. -/
theorem diagonal_rank (ts : List (Factor α)) (sites : List α) (unique : sites.Nodup)
    (wire : ∀ i ∈ sites, ∀ j ∈ sites, eval ts i j ≠ 0 ↔ i = j) :
    sites.length ≤ ts.length := by
  classical
  generalize hlen : ts.length = k
  induction k generalizing ts sites with
  | zero =>
    cases ts with
    | nil =>
      cases sites with
      | nil => simp
      | cons i xs =>
        exact False.elim (((wire i (by simp) i (by simp)).mpr rfl) rfl)
    | cons head tail => simp at hlen
  | succ k ih =>
    cases ts with
    | nil => simp at hlen
    | cons head tail =>
      have lengthTail : tail.length = k := by simpa using hlen
      by_cases hasPivot : ∃ r ∈ sites, head.left r ≠ 0
      · obtain ⟨r, mem, nonzero⟩ := hasPivot
        let shortened := tail.map (eliminate head r)
        have minor (i) (hi : i ∈ sites.erase r) (j) (hj : j ∈ sites.erase r) :
            eval shortened i j ≠ 0 ↔ i = j := by
          have hi' := unique.mem_erase_iff.mp hi
          have hj' := unique.mem_erase_iff.mp hj
          have gone : eval (head :: tail) r j = 0 := by
            apply Classical.byContradiction
            intro ne
            exact hj'.1 ((wire r mem j hj'.2).mp ne).symm
          simp only [shortened, elimination_entry, gone, Int.mul_zero, Int.sub_zero,
            Int.mul_ne_zero_iff]
          exact (and_iff_right nonzero).trans (wire i hi'.2 j hj'.2)
        have smaller := ih shortened (sites.erase r) (unique.erase r) minor
          (by simpa [shortened] using lengthTail)
        rw [List.length_erase_of_mem mem] at smaller
        omega
      · have minor (i) (hi : i ∈ sites) (j) (hj : j ∈ sites) :
            eval tail i j ≠ 0 ↔ i = j := by
          have zero : head.left i = 0 := by
            apply Classical.byContradiction
            exact fun ne => hasPivot ⟨i, hi, ne⟩
          simpa only [eval, zero, Int.zero_mul, Int.zero_add] using wire i hi j hj
        exact Nat.le_succ_of_le (ih tail sites unique minor lengthTail)

private def flatten (labels : ι → α × α) (t : Separated α) : Factor ι :=
  ⟨fun i => t.left (labels i).1 (labels i).2,
   fun j => t.right (labels j).1 (labels j).2⟩

private def reshape (g : Grouping) (value : α → α → α → α → Int)
    (i j : α × α) : Int :=
  match g with
  | .row => value i.1 i.2 j.2 j.1
  | .column => value i.1 j.2 i.2 j.1

private theorem flatten_eval (g : Grouping) (labels : ι → α × α)
    (ts : List (Separated α)) (fixed : ∀ t ∈ ts, t.grouping = g) (i j : ι) :
    eval (ts.map (flatten labels)) i j =
      (ts.map (fun t => reshape g t.value (labels i) (labels j))).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have head := fixed t (by simp)
    have next := ih (fun a ha => fixed a (by simp [ha]))
    simp only [List.map_cons, eval, List.sum_cons, next]
    cases g <;> simp only [flatten, reshape, Separated.value, head]

/-- Any rank-one integer decomposition using one cut has at least q² terms.
    It suffices that the *support* of the total is the wire; diagonal entries
    may have unrelated nonzero weights of either sign. -/
theorem fixed_cut_lower_bound (embed : Fin q → α)
    (inj : ∀ i j, embed i = embed j → i = j) (g : Grouping)
    (terms : Fin s → Separated α) (fixed : ∀ t, (terms t).grouping = g)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v) : q * q ≤ s := by
  let labels (i : Fin (q*q)) := (embed (decode i).1, embed (decode i).2)
  let raw := List.ofFn terms
  let ts := raw.map (flatten labels)
  have shape t (ht : t ∈ raw) : t.grouping = g := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact fixed i
  have entries (i j : Fin (q*q)) : eval ts i j = reshape g (total terms) (labels i) (labels j) := by
    rw [show eval ts i j = _ from flatten_eval g labels raw shape i j]
    cases g <;> simp [reshape, total, raw, List.map_ofFn, Function.comp_def]
  have equalLabel (i j : Fin (q*q)) :
      ((labels i).1 = (labels j).1 ∧ (labels i).2 = (labels j).2) ↔ i = j := by
    constructor
    · rintro ⟨e1,e2⟩
      have pair : decode i = decode j := Prod.ext (inj _ _ e1) (inj _ _ e2)
      exact (encode_decode i).symm.trans ((congrArg (fun p => encode p.1 p.2) pair).trans
        (encode_decode j))
    · rintro rfl; exact ⟨rfl,rfl⟩
  have condition (i j : Fin (q*q)) : eval ts i j ≠ 0 ↔ i = j := by
    rw [entries]
    cases g with
    | row => simpa only [reshape, wire, Wire] using equalLabel i j
    | column =>
      simp only [reshape, wire, Wire]
      exact (and_congr_right fun _ => eq_comm).trans (equalLabel i j)
  have bound := diagonal_rank ts (List.finRange (q*q)) (List.nodup_finRange _)
    (fun i _ j _ => condition i j)
  simpa [ts, raw] using bound

theorem eight_symbol_fixed_cut_needs_64 (g : Grouping)
    (terms : Fin s → Separated EightSquare.Block) (fixed : ∀ i, (terms i).grouping = g)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v) : 64 ≤ s :=
  fixed_cut_lower_bound (q := 8) (fun i : Fin 8 => (BitVec.ofFin i : EightSquare.Block))
    (fun _ _ h => congrArg BitVec.toFin h) g terms fixed wire

/-- Fix x=v. On this slice both possible cut orientations give an ordinary
    rank-one matrix on (y,u), exchanging row and column factors when needed. -/
private def middleSlice (a : α) (embed : ι → α) (t : Separated α) : Factor ι :=
  match t.grouping with
  | .row => ⟨fun i => t.left a (embed i), fun j => t.right a (embed j)⟩
  | .column => ⟨fun i => t.right a (embed i), fun j => t.left a (embed j)⟩

private theorem middle_slice_eval (a : α) (embed : ι → α) (ts : List (Separated α))
    (i j : ι) : eval (ts.map (middleSlice a embed)) i j =
      (ts.map (fun t => t.value a (embed i) (embed j) a)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, eval, List.sum_cons, ih]
    cases h : t.grouping <;> simp [middleSlice, Separated.value, h, Int.mul_comm]

/-- The mixed signed model also has a general rank lower bound. The gap between
    q and the explicit signed upper bound is not settled by this slice. -/
theorem signed_mixed_lower_bound (embed : Fin q → α)
    (inj : ∀ i j, embed i = embed j → i = j) (terms : Fin s → Separated α)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v) : q ≤ s := by
  cases q with
  | zero => exact Nat.zero_le _
  | succ q =>
    let a := embed 0
    let ts := (List.ofFn terms).map (middleSlice a embed)
    have condition (i j) : eval ts i j ≠ 0 ↔ i = j := by
      rw [show eval ts i j = _ from middle_slice_eval a embed (List.ofFn terms) i j]
      simp only [List.map_ofFn, Function.comp_def]
      change total terms a (embed i) (embed j) a ≠ 0 ↔ i = j
      rw [wire]
      simp only [Wire, true_and]
      exact ⟨inj i j, congrArg embed⟩
    have bound := diagonal_rank ts (List.finRange (q+1)) (List.nodup_finRange _)
      (fun i _ j _ => condition i j)
    simpa [ts] using bound

theorem eight_symbol_signed_mixed_needs_8 (terms : Fin s → Separated EightSquare.Block)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v) : 8 ≤ s :=
  signed_mixed_lower_bound (q := 8) (fun i : Fin 8 => (BitVec.ofFin i : EightSquare.Block))
    (fun _ _ h => congrArg BitVec.toFin h) terms wire

private def opposite : Grouping → Grouping
  | .row => .column
  | .column => .row

private def onlyCut (g : Grouping) (t : Separated α) : Separated α :=
  if t.grouping = g then t else ⟨g, fun _ _ => 0, fun _ _ => 0⟩

/-- Dummy zero terms in the other cut cannot explain a short decomposition:
    both cuts must make a nonzero contribution on some entry. -/
theorem short_needs_active_cut (embed : Fin q → α)
    (inj : ∀ i j, embed i = embed j → i = j) (terms : Fin s → Separated α)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v) (short : s < q*q)
    (wanted : Grouping) :
    ∃ i x y u v, (terms i).grouping = wanted ∧ (terms i).value x y u v ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro inactive
  let keep i := onlyCut (opposite wanted) (terms i)
  have fixed (i) : (keep i).grouping = opposite wanted := by
    unfold keep onlyCut
    split <;> simp_all
  have same (i : Fin s) (x y u v : α) : (keep i).value x y u v = (terms i).value x y u v := by
    by_cases kept : (terms i).grouping = opposite wanted
    · simp [keep, onlyCut, kept]
    · have dropped : (terms i).grouping = wanted := by
        cases wanted <;> cases e : (terms i).grouping <;> simp_all [opposite]
      have zero : (terms i).value x y u v = 0 := by
        apply Classical.byContradiction
        exact fun ne => inactive ⟨i,x,y,u,v,dropped,ne⟩
      cases wanted <;> simp [keep, onlyCut, opposite, Separated.value, dropped] at *
      all_goals omega
  have sameTotal x y u v : total keep x y u v = total terms x y u v := by
    simp only [total, same]
  have bound := fixed_cut_lower_bound embed inj _ keep fixed
    (fun x y u v => (sameTotal x y u v) ▸ wire x y u v)
  omega

/-- One statement with both ablations for the same 3-bit wire. A short
    decomposition needs a *live* term from each cut and genuine cancellation
    at an input where the target value is zero. -/
theorem short_eight_requires_turn_and_cancellation (terms : Fin s → Separated EightSquare.Block)
    (wire : ∀ x y u v, total terms x y u v ≠ 0 ↔ Wire x y u v) (short : s < 64) :
    (∀ cut, ∃ i x y u v, (terms i).grouping = cut ∧ (terms i).value x y u v ≠ 0) ∧
    (∃ x y u v i, ¬ Wire x y u v ∧ (terms i).value x y u v < 0) := by
  let emb (i : Fin 8) : EightSquare.Block := BitVec.ofFin i
  have inj (i j : Fin 8) (h : emb i = emb j) : i = j := congrArg BitVec.toFin h
  exact ⟨short_needs_active_cut emb inj terms wire short,
    short_decomposition_has_negative_off_wire emb inj terms wire short⟩

end Mobius.FixedCutRank
