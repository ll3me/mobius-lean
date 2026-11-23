import Mobius.SATSeam

/-!
# Count the proof tours, including their boundary ports

A tour is indexed by *one finite assignment*. It enters the certificate
checker once, discharges the clauses in their specified order, and returns
through the unique crossed seam. The graph also admits arbitrarily repeated
walks on satisfiable inputs; counting those would define a different object.

The enumeration covers all variables below the library's `variableBound`,
including unused indices in that range. `declared_count` accounts for extra
declared variables, as in variable-count bounds for exact #SAT.
-/
namespace Mobius.TourCount

open Complexity.SAT Mobius.SATSeam Mobius.Transport

private def snoc (b : Bool) (w : Fin n → Bool) : Fin (n+1) → Bool := Fin.lastCases b w

def assignments : (n : Nat) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n+1 => (assignments n).map (snoc false) ++ (assignments n).map (snoc true)

theorem assignments_complete (w : Fin n → Bool) : w ∈ assignments n := by
  induction n with
  | zero =>
    have eq : w = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [assignments, eq]
  | succ n ih =>
    let old := fun i : Fin n => w i.castSucc
    have same : snoc (w (Fin.last n)) old = w := by
      funext i
      induction i using Fin.lastCases with
      | last => simp [snoc]
      | cast i => simp [snoc, old]
    rw [assignments, List.mem_append]
    cases bit : w (Fin.last n) <;> rw [bit] at same
    · exact Or.inl (List.mem_map.mpr ⟨old, ih old, same⟩)
    · exact Or.inr (List.mem_map.mpr ⟨old, ih old, same⟩)

theorem assignments_nodup (n : Nat) : (assignments n).Nodup := by
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
    have oneSide (b : Bool) : ((assignments n).map (snoc b)).Nodup := by
      apply ih.map
      intro a c ne eq
      apply ne
      funext i
      simpa [snoc] using congrFun eq i.castSucc
    rw [assignments, List.nodup_append]
    refine ⟨oneSide false, oneSide true, ?_⟩
    intro x hx y hy same
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hx
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hy
    have e := congrFun (ha.trans (same.trans hb.symm)) (Fin.last n)
    simp [snoc] at e

theorem assignments_length (n : Nat) : (assignments n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [assignments, ih, Nat.pow_succ]; omega

private def asAssignment (w : Fin n → Bool) (i : Nat) : Bool :=
  if h : i<n then w ⟨i,h⟩ else false

def countWith (n : Nat) (f : CNF) : Nat :=
  (assignments n).countP fun w => evalCNF (asAssignment w) f

def sharp (f : CNF) := countWith (variableBound f) f

theorem sharp_pos_iff (f : CNF) : 0 < sharp f ↔ Satisfiable f := by
  rw [sharp, countWith, List.countP_pos_iff]
  constructor
  · rintro ⟨w, _, ok⟩; exact ⟨asAssignment w,ok⟩
  · intro sat
    obtain ⟨w, hw⟩ := witness_of_sat sat
    exact ⟨w, assignments_complete w, (full_prefix w).mp hw⟩

private theorem snoc_same_eval {f : CNF} (below : Complexity.ThreeSAT.CNFBelow n f)
    (b : Bool) (w : Fin n → Bool) :
    evalCNF (asAssignment (snoc b w)) f = evalCNF (asAssignment w) f := by
  apply Complexity.ThreeSAT.evalCNF_agrees below
  intro i hi
  simp only [asAssignment, show i < n+1 by omega, hi, dite_true]
  exact Fin.lastCases_castSucc (motive := fun _ => Bool) (last := b) (cast := w) ⟨i,hi⟩

private theorem countWith_succ {f : CNF} (below : Complexity.ThreeSAT.CNFBelow n f) :
    countWith (n+1) f = 2 * countWith n f := by
  simp only [countWith, assignments, List.countP_append, List.countP_map]
  have same (b : Bool) :
      ((fun w => evalCNF (asAssignment w) f) ∘ snoc b) =
      (fun w : Fin n → Bool => evalCNF (asAssignment w) f) := by
    funext w; exact snoc_same_eval below b w
  rw [same, same]
  omega

theorem declared_count (f : CNF) (extra : Nat) :
    countWith (variableBound f + extra) f = 2^extra * sharp f := by
  induction extra with
  | zero => simp [sharp]
  | succ k ih =>
    have below : Complexity.ThreeSAT.CNFBelow (variableBound f + k) f := by
      intro c hc l hl
      have hi := literal_lt_variableBound hc hl
      omega
    rw [Nat.add_succ, countWith_succ below, ih, Nat.pow_succ]
    ac_rfl

/-- This is data: different finite witnesses label different proof tours,
even if Lean identifies proofs of equality or of a walk proposition. -/
def CanonicalTour (f : CNF) (source target : Bool) :=
  { w : Witness f // PrefixOK w f.length ∧ target = !source }

theorem lifted_return {f : CNF} {source target : Bool} (t : CanonicalTour f source target) :
    Walk (Cover (Step f)) (.root,source) (.root,target) true := by
  have base : Walk (Step f) .root .root true :=
    ((Walk.single (Step.enter t.val)).append (discharge_all t.val _ (by omega) t.property.1)).snoc
      (Step.close t.val)
  apply cover_walk_iff.mpr
  exact ⟨base, by rw [t.property.2]; cases source <;> rfl⟩

/-- Executable test of exactly those clause-discharge obligations in
descending order. The role exchange occurs at the very end. -/
def testTour (f : CNF) (source target : Bool) (w : Witness f) : Bool :=
  (List.finRange f.length).reverse.all (fun i => evalClause (assign w) f[i]) &&
    (target == !source)

theorem testTour_spec (f : CNF) (source target : Bool) (w : Witness f) :
    testTour f source target w = true ↔ PrefixOK w f.length ∧ target = !source := by
  simp [testTour, PrefixOK, List.all_eq_true]

def tours (f : CNF) (source target : Bool) : Nat :=
  (assignments (variableBound f)).countP (testTour f source target)

theorem transfer_entry (f : CNF) (source target : Bool) :
    tours f source target = if target = !source then sharp f else 0 := by
  unfold tours sharp countWith
  split
  · next opposite =>
      apply List.countP_congr
      intro w _
      rw [testTour_spec, (full_prefix w)]
      simp only [opposite, and_true]
      rfl
  · next same =>
      apply List.countP_eq_zero.mpr
      intro w _ ok
      exact same ((testTour_spec f source target w).mp ok).2

def twoTours (f : CNF) (source target : Bool) : Nat :=
  tours f source false * tours f false target + tours f source true * tours f true target

theorem two_tours_diagonal (f : CNF) (source target : Bool) :
    twoTours f source target = if source = target then (sharp f)^2 else 0 := by
  cases source <;> cases target <;> simp [twoTours, transfer_entry, Nat.pow_succ]

theorem trace_zero (f : CNF) : tours f false false + tours f true true = 0 := by
  simp [transfer_entry]

theorem off_diagonal_detects_sat (f : CNF) : 0 < tours f false true ↔ Satisfiable f := by
  simpa [transfer_entry] using sharp_pos_iff f

example : sharp [] = 1 ∧ tours [] false true = 1 := by decide +kernel
example : sharp [[]] = 0 ∧ twoTours [[]] false false = 0 := by decide +kernel
example : sharp [[⟨0,true⟩, ⟨0,false⟩]] = 2 ∧
    twoTours [[⟨0,true⟩, ⟨0,false⟩]] true true = 4 := by decide +kernel

end Mobius.TourCount
