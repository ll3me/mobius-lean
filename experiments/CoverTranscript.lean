import HamiltonianInterface
import Nc.Final.CClasses

/-! Compile the signed, partially assigned terminal paths of a Boolean
transcript into the gate model of the published VP/VNP theorem. -/
namespace BoardCoverTranscript
open MvPolynomial Finset BoardHamiltonianInterface
noncomputable section

variable {V : Type} [DecidableEq V] {F : Type*} [Field F]
private abbrev P := MvPolynomial V F

private def onBit (b : Bool) : F := if b then 1 else 0

private def entry (s : Finset V) (b : V → Bool) (e : V) : P (V := V) (F := F) :=
  if e ∈ s then C (onBit (b e)) else X e

private def replay (s : Finset V) (b : V → Bool) (p : MvPolynomial V F) : MvPolynomial V F :=
  aeval (entry (F := F) s b) p

/-- The same gate indices still work after replacing inputs by constants. -/
theorem replay_cost (s : Finset V) (b : V → Bool) {p : MvPolynomial V F} {n : ℕ}
    (h : Statement.Computes p n) : Statement.Computes (replay s b p) n := by
  obtain ⟨l, ok, k, hk, output⟩ := h
  refine ⟨fun i => replay s b (l i), fun i hi => ?_, k, hk, congrArg _ output⟩
  rcases ok i hi with ⟨e, eq⟩ | ⟨c, eq⟩ | ⟨j, hj, k, hk, eq⟩ | ⟨j, hj, k, hk, eq⟩
  · by_cases he : e ∈ s
    · exact Or.inr (Or.inl ⟨onBit (b e), by simp [eq, replay, entry, he]⟩)
    · exact Or.inl ⟨e, by simp [eq, replay, entry, he]⟩
  · exact Or.inr (Or.inl ⟨c, by simp [eq, replay]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, hk, by simp [eq, replay]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, k, hk, by simp [eq, replay]⟩))

private theorem replay_degree (s : Finset V) (b : V → Bool) (p : MvPolynomial V F) (e : V) :
    (replay s b p).degreeOf e ≤ if e ∈ s then 0 else p.degreeOf e := by
  have mon (w : V →₀ ℕ) (a : F) :
      (replay s b (monomial w a)).degreeOf e ≤ if e ∈ s then 0 else w e := by
    rw [monomial_eq, replay, map_mul, aeval_C]
    apply (degreeOf_mul_le ..).trans
    simp only [MvPolynomial.algebraMap_eq, degreeOf_C, zero_add, Finsupp.prod, map_prod, map_pow, aeval_X]
    apply (degreeOf_prod_le ..).trans
    have bounds (j : V) : (((entry s b j : MvPolynomial V F) ^ w j).degreeOf e)
        ≤ if e ∈ s then 0 else if e = j then w j else 0 := by
      apply (degreeOf_pow_le ..).trans
      by_cases h : e = j
      · subst j; by_cases he : e ∈ s <;> simp [entry, he]
      · by_cases he : e ∈ s <;> by_cases hj : j ∈ s <;> simp [entry, he, hj, degreeOf_X, h]
    apply (Finset.sum_le_sum (fun j _ => bounds j)).trans
    by_cases he : e ∈ s <;> simp [he]
    split <;> omega
  have expand : replay s b p = ∑ w ∈ p.support, replay s b (monomial w (p.coeff w)) := by
    exact (congrArg (replay s b) p.as_sum).trans (map_sum (aeval (entry (F := F) s b)) _ _)
  rw [expand]
  apply (degreeOf_sum_le ..).trans (Finset.sup_le ?_)
  intro w hw
  apply (mon w (p.coeff w)).trans
  split <;> simp_all [monomial_le_degreeOf e hw]

private def literal (e : V) (b : Bool) : MvPolynomial V F := if b then X e else 1-X e
private def selector (s : Finset V) (b : V → Bool) : MvPolynomial V F :=
  ∏ e ∈ s, literal e (b e)

private theorem selector_degree (s : Finset V) (b : V → Bool) (e : V) :
    (selector s b : MvPolynomial V F).degreeOf e ≤ if e ∈ s then 1 else 0 := by
  apply (degreeOf_prod_le ..).trans
  have each (j : V) : (literal j (b j) : MvPolynomial V F).degreeOf e ≤ if e = j then 1 else 0 := by
    cases h : b j
    · apply (degreeOf_sub_le ..).trans
      simp [degreeOf_X]
    · simp [literal, degreeOf_X]
  exact (Finset.sum_le_sum (fun j _ => each j)).trans (by simp)

omit [DecidableEq V] in
private theorem atom (p : MvPolynomial V F) (h : (∃ i, p = X i) ∨ ∃ a, p = C a) :
    Nc.Computes p 1 := by
  refine ⟨fun _ => p, fun _ _ => ?_, 0, by decide, rfl⟩
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

omit [DecidableEq V] in
private theorem literal_cost (e : V) (b : Bool) : Nc.Computes (literal e b : MvPolynomial V F) 5 := by
  have x := atom (X e : MvPolynomial V F) (Or.inl ⟨e,rfl⟩)
  cases b with
  | true => exact x.mono (by decide)
  | false =>
    have neg := (atom (C (-1 : F)) (Or.inr ⟨_,rfl⟩)).join x (Or.inr rfl)
    exact (atom (1 : MvPolynomial V F) (Or.inr ⟨1, by simp⟩)).join neg
      (Or.inl (by simp [literal, sub_eq_add_neg]))

private theorem selector_cost (s : Finset V) (b : V → Bool) :
    Nc.Computes (selector s b : MvPolynomial V F) (1+6*s.card) := by
  induction s using Finset.induction_on with
  | empty => simpa [selector] using atom (1 : MvPolynomial V F) (Or.inr ⟨1, by simp⟩)
  | @insert e s fresh ih =>
    have add := (literal_cost (F := F) e (b e)).join ih (Or.inr rfl)
    simp only [selector, Finset.prod_insert fresh, Finset.card_insert_of_notMem fresh]
    exact add.mono (by omega)

/-- One signed term after expanding negative answers and fixing exceptional variables. -/
structure Piece (V : Type) (F : Type*) [Field F] where
  fixed : Finset V
  bit : V → Bool
  weight : F
  output : MvPolynomial V F
  steps : ℕ
  circuit : Statement.Computes output steps
  free_degree : ∀ e ∉ fixed, output.degreeOf e ≤ 1

def Piece.poly (u : Piece V F) :=
  C u.weight * selector u.fixed u.bit * replay u.fixed u.bit u.output

theorem Piece.multilinear (u : Piece V F) (e : V) : u.poly.degreeOf e ≤ 1 := by
  apply (degreeOf_mul_le ..).trans
  have left := (degreeOf_mul_le e (C u.weight) (selector u.fixed u.bit)).trans
    (Nat.add_le_add (Nat.le_refl _) (selector_degree (F := F) u.fixed u.bit e))
  rw [degreeOf_C, zero_add] at left
  have right := replay_degree u.fixed u.bit u.output e
  by_cases h : e ∈ u.fixed
  · simp [h] at left right; omega
  · have free := u.free_degree e h
    simp [h] at left right; omega

theorem Piece.cost (u : Piece V F) : Statement.Computes u.poly (u.steps+6*u.fixed.card+4) := by
  have weighted := (atom (C u.weight : MvPolynomial V F) (Or.inr ⟨_,rfl⟩)).join
    (selector_cost (F := F) u.fixed u.bit) (Or.inr rfl)
  have hp : Nc.Computes (replay u.fixed u.bit u.output) u.steps := replay_cost _ _ u.circuit
  exact (weighted.join hp (Or.inr rfl)).mono (by omega)

def total (ts : List (Piece V F)) : MvPolynomial V F := (ts.map Piece.poly).sum
def budget (ts : List (Piece V F)) := 1 + (ts.map (fun u => u.steps+6*u.fixed.card+5)).sum

theorem total_circuit (ts : List (Piece V F)) : Statement.Computes (total ts) (budget ts) := by
  change Nc.Computes (total ts) (budget ts)
  induction ts with
  | nil => simpa [total, budget] using atom (0 : MvPolynomial V F) (Or.inr ⟨0, by simp⟩)
  | cons u ts ih =>
    have first : Nc.Computes u.poly _ := u.cost
    have rest : Nc.Computes (total ts) _ := ih
    exact (first.join rest (Or.inl rfl)).mono (by simp [budget]; omega)

theorem total_multilinear (ts : List (Piece V F)) (e : V) : (total ts).degreeOf e ≤ 1 := by
  induction ts with
  | nil => simp [total]
  | cons u ts ih => exact (degreeOf_add_le ..).trans (max_le (u.multilinear e) ih)

def Piece.contribution (u : Piece V F) (mask : Finset V) : F :=
  if ∀ e ∈ u.fixed, u.bit e = decide (e ∈ mask)
  then u.weight * eval (fun e => if e ∈ mask then (1:F) else 0) u.output else 0

theorem Piece.eval_poly (u : Piece V F) (mask : Finset V) :
    eval (fun e => if e ∈ mask then (1:F) else 0) u.poly = u.contribution mask := by
  classical
  let x : V → F := fun e => if e ∈ mask then 1 else 0
  have lit (e : V) : eval x (literal e (u.bit e) : MvPolynomial V F) =
      if u.bit e = decide (e ∈ mask) then 1 else 0 := by
    by_cases he : e ∈ mask <;> cases u.bit e <;> simp [literal, x, he]
  change eval x u.poly = _
  rw [Piece.poly, map_mul, map_mul, eval_C, selector, map_prod]
  simp_rw [lit]
  by_cases hit : ∀ e ∈ u.fixed, u.bit e = decide (e ∈ mask)
  · have active : (∏ e ∈ u.fixed, (if u.bit e = decide (e ∈ mask) then (1:F) else 0)) = 1 :=
      Finset.prod_eq_one (fun e he => if_pos (hit e he))
    have same (e : V) : eval x (entry (F := F) u.fixed u.bit e) = x e := by
      by_cases he : e ∈ u.fixed
      · by_cases hm : e ∈ mask <;> simp [entry, he, hit e he, onBit, x, hm]
      · simp [entry, he]
    have revaluation : eval x (replay u.fixed u.bit u.output) = eval x u.output := by
      change eval₂Hom (RingHom.id F) x (bind₁ (entry u.fixed u.bit) u.output) = _
      rw [eval₂Hom_bind₁]
      change eval (fun i => eval x (entry (F := F) u.fixed u.bit i)) u.output = _
      simp_rw [same]
    rw [active, mul_one, revaluation, Piece.contribution, if_pos hit]
  · obtain ⟨e, he, bad⟩ := by simpa using hit
    rw [Finset.prod_eq_zero he (if_neg bad), mul_zero, zero_mul, Piece.contribution, if_neg hit]

theorem total_eval (ts : List (Piece V F)) (mask : Finset V) :
    eval (fun e => if e ∈ mask then (1:F) else 0) (total ts) =
      (ts.map (fun u => u.contribution mask)).sum := by
  induction ts with
  | nil => simp [total]
  | cons u ts ih =>
    change eval _ (u.poly + total ts) = _
    rw [map_add, u.eval_poly, ih, List.map_cons, List.sum_cons]

open Classical in
def Correct {m : ℕ} (ts : List (Piece (Arc m) F)) : Prop :=
  ∀ mask : Finset (Arc m), (ts.map (fun u => u.contribution mask)).sum =
      if ∃ σ : Equiv.Perm (Fin m), σ.IsCycleOn Set.univ ∧
        ∀ i, σ i ≠ i ∧ (i, σ i) ∈ mask then 1 else 0

/-- A correct signed sum of terminal paths supplies the upstream gate certificate. -/
theorem hc_of_transcript {m : ℕ} (hm : 2 ≤ m) (ts : List (Piece (Arc m) F))
    (correct : Correct ts) :
    ∃ t ≤ budget ts*((m+1)*(2*(m+1)+1)), Statement.Computes (Statement.hc F m) t :=
  hc_circuit_of_masks F hm _ (total_circuit ts) (total_multilinear ts)
    (fun mask => (total_eval ts mask).trans (correct mask))

universe u

/-- The argument has exactly the type of Solution.mainTheorem from the release. -/
theorem beyond_of_transcript (lower : Statement.MainTheorem.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀, ∀ (K : Type u) [Field K] [CharP K p], ∀ m ≥ m₀,
      ∀ ts : List (Piece (Arc m) K), Correct ts → Statement.Beyond c m
        (budget ts*((m+1)*(2*(m+1)+1))) := by
  obtain ⟨c, pos, perChar⟩ := lower
  refine ⟨c, pos, fun p => ?_⟩
  obtain ⟨cut, h⟩ := perChar p
  refine ⟨max 2 cut, fun K _ _ m hm ts valid => ?_⟩
  obtain ⟨t, bound, circuit⟩ := hc_of_transcript ((le_max_left 2 cut).trans hm) ts valid
  have need := (h K m ((le_max_right 2 cut).trans hm) t).1 circuit
  exact lt_of_lt_of_le need (by exact_mod_cast bound)

end
end BoardCoverTranscript

#print axioms BoardCoverTranscript.hc_of_transcript
#print axioms BoardCoverTranscript.beyond_of_transcript
