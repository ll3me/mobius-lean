import Statement

/-! Check this file in the published vp-vnp project, with its own toolchain.
It uses the actual Statement.hc and MvPolynomial.homogeneousComponent. -/
namespace BoardHamiltonianInterface
open MvPolynomial Finset
open scoped BigOperators
noncomputable section

variable {E : Type*} [DecidableEq E] (F : Type*) [Field F]

private def word (s : Finset E) : MvPolynomial E F := ∏ e ∈ s, X e

omit [DecidableEq E] in
private theorem word_hom (s : Finset E) : (word F s).IsHomogeneous s.card := by
  simpa [word] using IsHomogeneous.prod s (fun e : E => (X e : MvPolynomial E F))
    (fun _ => 1) (fun e _ => isHomogeneous_X F e)

private theorem word_degree (s : Finset E) (e : E) : (word F s).degreeOf e ≤ 1 := by
  apply (degreeOf_prod_le e s (fun i => (X i : MvPolynomial E F))).trans
  simp [degreeOf_X]
  split <;> omega

private theorem word_eval (s mask : Finset E) :
    eval (fun e => if e ∈ mask then (1:F) else 0) (word F s) =
      if s ⊆ mask then 1 else 0 := by
  classical
  rw [word, map_prod]
  simp only [eval_X]
  by_cases h : s ⊆ mask
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun e he => if_pos (h he))
  · obtain ⟨e, he, hm⟩ := Finset.not_subset.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero he (if_neg hm)

/-- Squarefree inclusion-exclusion for the OR of monomial witnesses,
with an additional set of edges that must all be open. -/
private def unionExtension : List (Finset E) → Finset E → MvPolynomial E F
  | [], _ => 0
  | c :: cs, s => word F (s ∪ c) + unionExtension cs s - unionExtension cs (s ∪ c)

private theorem extension_degree (cs : List (Finset E)) (s : Finset E) (e : E) :
    (unionExtension F cs s).degreeOf e ≤ 1 := by
  induction cs generalizing s with
  | nil => simp [unionExtension]
  | cons c cs ih =>
    exact (degreeOf_sub_le ..).trans (max_le ((degreeOf_add_le ..).trans
      (max_le (word_degree F (s ∪ c) e) (ih s))) (ih (s ∪ c)))

open Classical in
private theorem extension_eval (cs : List (Finset E)) (s mask : Finset E) :
    eval (fun e => if e ∈ mask then (1:F) else 0) (unionExtension F cs s) =
      if s ⊆ mask ∧ ∃ c ∈ cs, c ⊆ mask then 1 else 0 := by
  induction cs generalizing s with
  | nil => simp [unionExtension]
  | cons c cs ih =>
    rw [unionExtension, map_sub, map_add, word_eval, ih, ih]
    by_cases hs : s ⊆ mask <;> by_cases hc : c ⊆ mask <;> by_cases rest : ∃ d ∈ cs, d ⊆ mask <;>
      simp [Finset.union_subset_iff, hs, hc, rest]

private theorem component_above (cs : List (Finset E)) (s : Finset E) (n : ℕ)
    (above : ∀ c ∈ cs, n < (s ∪ c).card) :
    homogeneousComponent n (unionExtension F cs s) = 0 := by
  induction cs generalizing s with
  | nil => simp [unionExtension]
  | cons c cs ih =>
    have high := above c (by simp)
    have rest : ∀ d ∈ cs, n < (s ∪ d).card := fun d hd => above d (by simp [hd])
    have larger : ∀ d ∈ cs, n < (s ∪ c ∪ d).card := fun d hd => (rest d hd).trans_le
      (Finset.card_le_card (Finset.union_subset_union_left (Finset.subset_union_left : s ⊆ s ∪ c)))
    simp [unionExtension, homogeneousComponent_of_mem (word_hom F (s ∪ c)),
      ne_of_lt high, ih s rest, ih (s ∪ c) larger]

private theorem first_component (cs : List (Finset E)) (n : ℕ) (distinct : cs.Nodup)
    (sizes : ∀ c ∈ cs, c.card = n) :
    homogeneousComponent n (unionExtension F cs ∅) = (cs.map (word F)).sum := by
  induction cs with
  | nil => simp [unionExtension]
  | cons c cs ih =>
    obtain ⟨fresh, nodup⟩ := List.nodup_cons.mp distinct
    have hc := sizes c (by simp)
    have rest : ∀ d ∈ cs, d.card = n := fun d hd => sizes d (by simp [hd])
    have larger (d) (hd : d ∈ cs) : n < (c ∪ d).card := by
      by_contra! h
      have eq := Finset.eq_of_subset_of_card_le (Finset.subset_union_left : c ⊆ c ∪ d) (h.trans hc.ge)
      have dc : d ⊆ c := eq.symm ▸ (Finset.subset_union_right : d ⊆ c ∪ d)
      have same := Finset.eq_of_subset_of_card_le dc (by rw [hc, rest d hd])
      exact fresh (same ▸ hd)
    simp [unionExtension, ih nodup rest, component_above F cs c n larger,
      homogeneousComponent_of_mem (word_hom F c), hc]

abbrev Arc (m : ℕ) := Fin m × Fin m

private def supportOf {m : ℕ} (σ : Equiv.Perm (Fin m)) : Finset (Arc m) :=
  univ.image fun i => (i, σ i)

private theorem mem_support {m : ℕ} (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    (i, j) ∈ supportOf σ ↔ σ i = j := by simp [supportOf]

private theorem support_injective {m : ℕ} : Function.Injective (@supportOf m) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi := (mem_support σ i (σ i)).mpr rfl
  rw [h] at hi
  exact ((mem_support τ i (σ i)).mp hi).symm

private theorem support_card {m : ℕ} (σ : Equiv.Perm (Fin m)) : (supportOf σ).card = m := by
  rw [supportOf, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

open Classical in
private def cycles (m : ℕ) := (univ : Finset (Equiv.Perm (Fin m))).filter (·.IsCycleOn Set.univ)

def decisionExtension (m : ℕ) : MvPolynomial (Arc m) F :=
  unionExtension F ((cycles m).toList.map supportOf) ∅

theorem decision_multilinear (m : ℕ) (e : Arc m) : (decisionExtension F m).degreeOf e ≤ 1 :=
  extension_degree F _ _ _

open Classical in
/-- Allowing diagonal positions in the upstream matrix has no effect for m ≥ 2. -/
theorem decision_on_mask {m : ℕ} (hm : 2 ≤ m) (mask : Finset (Arc m)) :
    eval (fun e => if e ∈ mask then (1:F) else 0) (decisionExtension F m) =
      if ∃ σ : Equiv.Perm (Fin m), σ.IsCycleOn Set.univ ∧
        ∀ i, σ i ≠ i ∧ (i, σ i) ∈ mask then 1 else 0 := by
  rw [decisionExtension, extension_eval]
  congr 1
  apply propext
  simp only [Finset.empty_subset, true_and]
  constructor
  · rintro ⟨c, hc, hs⟩
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hc
    have single : σ.IsCycleOn Set.univ := by simpa [cycles] using hσ
    have nontriv : (Set.univ : Set (Fin m)).Nontrivial :=
      ⟨⟨0, by omega⟩, Set.mem_univ _, ⟨1, by omega⟩, Set.mem_univ _, by
        intro h; have := congrArg Fin.val h; simp at this⟩
    exact ⟨σ, single, fun i => ⟨single.apply_ne nontriv (Set.mem_univ i), hs ((mem_support ..).mpr rfl)⟩⟩
  · rintro ⟨σ, hσ, hs⟩
    refine ⟨supportOf σ, List.mem_map.mpr ⟨σ, ?_, rfl⟩, ?_⟩
    · simpa [cycles] using hσ
    · rintro ⟨i, j⟩ hij
      rw [← (mem_support σ i j).mp hij]
      exact (hs i).2

theorem component_eq_hc (m : ℕ) :
    homogeneousComponent m (decisionExtension F m) = Statement.hc F m := by
  classical
  let cs := (cycles m).toList.map supportOf
  have distinct : cs.Nodup := (cycles m).nodup_toList.map support_injective
  have sizes : ∀ c ∈ cs, c.card = m := by
    intro c hc
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hc
    exact support_card σ
  rw [decisionExtension, first_component F _ m distinct sizes, List.map_map, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro σ _
  change word F (supportOf σ) = _
  unfold word supportOf
  rw [Finset.prod_image]
  intro i _ j _ h
  exact congrArg Prod.fst h

/-! A gate schedule for all homogeneous pieces up to a cutoff. The registers
for both predecessors stay available throughout a multiplication gate. -/
namespace Homogenize

variable {V : Type} {K : Type*} [Field K]
private abbrev P := MvPolynomial V K

private def scale : P (V := V) (K := K) →+* Polynomial (MvPolynomial V K) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun i => Polynomial.C (X i) * Polynomial.X)

private theorem scale_coeff (d : ℕ) (p : MvPolynomial V K) :
    (scale p).coeff d = homogeneousComponent d p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial k a =>
    have eq : scale (monomial k a) = Polynomial.C (monomial k a) * Polynomial.X ^ k.degree := by
      rw [scale, eval₂Hom_monomial, RingHom.comp_apply, monomial_eq]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        map_mul, map_prod, map_pow, Finsupp.degree_apply, mul_assoc]
    rw [eq, Polynomial.coeff_C_mul_X_pow, homogeneousComponent_of_mem
      (isHomogeneous_monomial a rfl : (monomial k a : MvPolynomial V K).IsHomogeneous k.degree)]
  | add p q hp hq => simp [map_add, hp, hq]

private def Step (l : ℕ → MvPolynomial V K) (k : ℕ) : Prop :=
  (∃ e, l k = X e) ∨ (∃ a, l k = C a) ∨
  (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

private structure Tape (V : Type) (K : Type*) [Field K] where
  size : ℕ
  reg : ℕ → MvPolynomial V K
  valid : ∀ k < size, Step reg k

private def Has (t : Tape V K) (p : MvPolynomial V K) := ∃ i < t.size, t.reg i = p
private def Keeps (t u : Tape V K) := ∀ p, Has t p → Has u p

private def Next (t : Tape V K) (p : MvPolynomial V K) : Prop :=
  (∃ e, p = X e) ∨ (∃ a, p = C a) ∨
  ∃ f g, Has t f ∧ Has t g ∧ (p = f + g ∨ p = f * g)

private theorem emit (t : Tape V K) (p : MvPolynomial V K) (ok : Next t p) :
    ∃ u, Keeps t u ∧ Has u p ∧ u.size = t.size + 1 := by
  let reg i := if i < t.size then t.reg i else p
  have old (i) (hi : i < t.size) : reg i = t.reg i := if_pos hi
  have last : reg t.size = p := if_neg (Nat.lt_irrefl _)
  have valid (i) (hi : i < t.size+1) : Step reg i := by
    rcases lt_or_ge i t.size with lt | ge
    · rcases t.valid i lt with ⟨e, h⟩ | ⟨a, h⟩ | ⟨j, hj, k, hk, h⟩ | ⟨j, hj, k, hk, h⟩
      · exact Or.inl ⟨e, (old i lt).trans h⟩
      · exact Or.inr (Or.inl ⟨a, (old i lt).trans h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, hk, by rw [old i lt, old j (by omega), old k (by omega), h]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨j, hj, k, hk, by rw [old i lt, old j (by omega), old k (by omega), h]⟩))
    · have eq : i = t.size := by omega
      subst i
      rcases ok with ⟨e, h⟩ | ⟨a, h⟩ | ⟨f, g, ⟨j, hj, fj⟩, ⟨k, hk, gk⟩, h | h⟩
      · exact Or.inl ⟨e, last.trans h⟩
      · exact Or.inr (Or.inl ⟨a, last.trans h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨j, hj, k, hk, by rw [last, old j hj, old k hk, fj, gk, h]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨j, hj, k, hk, by rw [last, old j hj, old k hk, fj, gk, h]⟩))
  refine ⟨⟨t.size+1, reg, valid⟩, ?_, ⟨t.size, by simp, last⟩, rfl⟩
  rintro _ ⟨i, hi, h⟩
  exact ⟨i, Nat.lt_succ_of_lt hi, (old i hi).trans h⟩

private theorem dot (t : Tape V K) (f g : ℕ → MvPolynomial V K) (n : ℕ)
    (known : ∀ i < n, Has t (f i) ∧ Has t (g i)) :
    ∃ u, Keeps t u ∧ Has u (∑ i ∈ range n, f i * g i) ∧ u.size ≤ t.size + (2*n+1) := by
  induction n with
  | zero =>
    obtain ⟨u, keep, h, size⟩ := emit t 0 (Or.inr (Or.inl ⟨0, by simp⟩))
    exact ⟨u, keep, by simpa using h, by omega⟩
  | succ n ih =>
    obtain ⟨u, ku, sum, su⟩ := ih (fun i hi => known i (by omega))
    obtain ⟨hf, hg⟩ := known n (by omega)
    obtain ⟨v, kv, prod, sv⟩ := emit u (f n * g n) (Or.inr (Or.inr
      ⟨_, _, ku _ hf, ku _ hg, Or.inr rfl⟩))
    rw [Finset.sum_range_succ]
    obtain ⟨w, kw, both, sw⟩ := emit v _ (Or.inr (Or.inr ⟨_, _, kv _ sum, prod, Or.inl rfl⟩))
    exact ⟨w, fun p h => kw _ (kv _ (ku p h)), both, by omega⟩

private theorem tabulate (t : Tape V K) (f : ℕ → MvPolynomial V K) (n cost : ℕ)
    (one : ∀ j < n, ∀ u, Keeps t u → ∃ v, Keeps u v ∧ Has v (f j) ∧ v.size ≤ u.size+cost) :
    ∃ v, Keeps t v ∧ (∀ j < n, Has v (f j)) ∧ v.size ≤ t.size+n*cost := by
  induction n with
  | zero => exact ⟨t, fun _ h => h, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨u, ku, got, su⟩ := ih (fun j hj => one j (by omega))
    obtain ⟨v, kv, last, sv⟩ := one n (by omega) u ku
    refine ⟨v, fun p h => kv _ (ku p h), ?_, by rw [Nat.succ_mul]; omega⟩
    intro j hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with lt | rfl
    · exact kv _ (got j lt)
    · exact last

private theorem build (l : ℕ → MvPolynomial V K) (n d : ℕ) (valid : ∀ i < n, Step l i) :
    ∃ t : Tape V K, t.size ≤ n*((d+1)*(2*(d+1)+1)) ∧
      ∀ i < n, ∀ j ≤ d, Has t ((scale (l i)).coeff j) := by
  induction n with
  | zero => exact ⟨⟨0, fun _ => 0, by simp⟩, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨t, size, prev⟩ := ih (fun i hi => valid i (by omega))
    have one (j) (hj : j < d+1) (u : Tape V K) (keep : Keeps t u) :
        ∃ v, Keeps u v ∧ Has v ((scale (l n)).coeff j) ∧ v.size ≤ u.size+(2*(d+1)+1) := by
      rcases valid n (by omega) with ⟨e, eq⟩ | ⟨a, eq⟩ | ⟨i, hi, k, hk, eq⟩ | ⟨i, hi, k, hk, eq⟩
      · rw [eq]
        have nx : Next u ((scale (X e)).coeff j) := by
          rw [scale_coeff, homogeneousComponent_of_mem (isHomogeneous_X K e)]
          by_cases h : j = 1
          · exact Or.inl ⟨e, if_pos h⟩
          · exact Or.inr (Or.inl ⟨0, by simp [h]⟩)
        obtain ⟨v, kv, h, sv⟩ := emit u _ nx
        exact ⟨v, kv, h, by omega⟩
      · rw [eq]
        have nx : Next u ((scale (C a)).coeff j) := by
          rw [scale_coeff, homogeneousComponent_of_mem (isHomogeneous_C V a)]
          by_cases h : j = 0
          · exact Or.inr (Or.inl ⟨a, if_pos h⟩)
          · exact Or.inr (Or.inl ⟨0, by simp [h]⟩)
        obtain ⟨v, kv, h, sv⟩ := emit u _ nx
        exact ⟨v, kv, h, by omega⟩
      · rw [eq, map_add, Polynomial.coeff_add]
        obtain ⟨v, kv, h, sv⟩ := emit u _ (Or.inr (Or.inr ⟨_, _,
          keep _ (prev i hi j (by omega)), keep _ (prev k hk j (by omega)), Or.inl rfl⟩))
        exact ⟨v, kv, h, by omega⟩
      · rw [eq, map_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        obtain ⟨v, kv, h, sv⟩ := dot u (fun z => (scale (l i)).coeff z)
          (fun z => (scale (l k)).coeff (j-z)) (j+1) (fun z hz =>
            ⟨keep _ (prev i hi z (by omega)), keep _ (prev k hk (j-z) (by omega))⟩)
        exact ⟨v, kv, h, by omega⟩
    obtain ⟨v, kv, got, sv⟩ := tabulate t _ (d+1) _ one
    refine ⟨v, by rw [Nat.succ_mul]; omega, ?_⟩
    intro i hi j hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with lt | rfl
    · exact kv _ (prev i lt j hj)
    · exact got j (by omega)

/-- Extract degree d over the original field, even in small characteristic. -/
theorem component_circuit {p : MvPolynomial V K} {s : ℕ} (d : ℕ)
    (circuit : Statement.Computes p s) :
    ∃ t ≤ s*((d+1)*(2*(d+1)+1)), Statement.Computes (homogeneousComponent d p) t := by
  obtain ⟨l, hl, k, hk, output⟩ := circuit
  obtain ⟨t, size, got⟩ := build l s d hl
  obtain ⟨i, hi, eq⟩ := got k hk d (by omega)
  exact ⟨t.size, size, t.reg, t.valid, i, hi, by rw [eq, output, scale_coeff]⟩

end Homogenize

theorem hc_circuit_of_extension (m s : ℕ) (h : Statement.Computes (decisionExtension F m) s) :
    ∃ t ≤ s*((m+1)*(2*(m+1)+1)), Statement.Computes (Statement.hc F m) t := by
  simpa [component_eq_hc] using Homogenize.component_circuit m h

open Classical in
/-- The compiler may produce any multilinear circuit with the right output on masks. -/
theorem hc_circuit_of_masks {m s : ℕ} (hm : 2 ≤ m) (p : MvPolynomial (Arc m) F)
    (circuit : Statement.Computes p s) (multi : ∀ e, p.degreeOf e ≤ 1)
    (correct : ∀ mask : Finset (Arc m), eval (fun e => if e ∈ mask then (1:F) else 0) p =
      if ∃ σ : Equiv.Perm (Fin m), σ.IsCycleOn Set.univ ∧
        ∀ i, σ i ≠ i ∧ (i, σ i) ∈ mask then 1 else 0) :
    ∃ t ≤ s*((m+1)*(2*(m+1)+1)), Statement.Computes (Statement.hc F m) t := by
  have equal : p = decisionExtension F m := by
    apply sub_eq_zero.mp
    apply eq_zero_of_eval_zero_at_prod_finset _ (fun _ => ({0, 1} : Finset F))
    · intro e
      have b := (degreeOf_sub_le e p (decisionExtension F m)).trans
        (max_le (multi e) (decision_multilinear F m e))
      simpa using Nat.lt_succ_of_le b
    · intro x hx
      let mask := univ.filter (fun e => x e = 1)
      have repr : x = fun e => if e ∈ mask then (1:F) else 0 := by
        funext e
        rcases (by simpa using hx e : x e = 0 ∨ x e = 1) with h | h <;> simp [mask, h]
      rw [map_sub, repr, correct, decision_on_mask F hm mask, sub_self]
  exact hc_circuit_of_extension F m s (equal ▸ circuit)

end
end BoardHamiltonianInterface

#print axioms BoardHamiltonianInterface.component_eq_hc
#print axioms BoardHamiltonianInterface.hc_circuit_of_masks
