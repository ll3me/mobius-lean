import Mobius.BoundaryThreshold
import Mobius.BoundarySemantics
import Mobius.BoundaryDecision

/-! Two fixed raw contractions recover exact closed CNF model counts. One
arbitrary independent-table raw contraction has genuine yes/no collisions,
even under unrestricted postprocessing of its scalar total. Entrywise
positive clipping before summation gives a separate one-template scheme. -/
namespace Mobius.BoundaryTwoSums
open Complexity.SAT
open Mobius.BoundarySemantics (B Phase Key Ports glue contract sumI)
open Mobius.BoundaryChoice (Context)
open Mobius.BoundaryDecision (raw measure)
open Mobius.BoundaryThreshold (pairSum shiftedW thresholdPhase S)
open Mobius.SignObstruction (repairPhase)
open Mobius.RankTradeGauge (kernel sig)

private theorem untwist_term (x y u v : B) :
    kernel repairPhase x y u v = if x.getLsbD 3 = v.getLsbD 3 then
      kernel thresholdPhase x y u v else -kernel thresholdPhase x y u v := by
  by_cases bal : x ^^^ y = v ^^^ u
  · simp only [kernel,bal,ite_true,thresholdPhase]
    cases x.getLsbD 3 <;> cases v.getLsbD 3 <;> cases repairPhase x y <;> cases repairPhase v u <;> decide
  · simp only [kernel,bal,ite_false,Int.neg_zero,ite_self]

private theorem untwist (x y u v : B) : pairSum repairPhase x y u v =
    if x.getLsbD 3 = v.getLsbD 3 then S x y u v else -S x y u v := by
  unfold S pairSum
  rw [untwist_term x y u v,untwist_term x u y v]
  split <;> omega

/-- The quotient table and its row-signed variant are both fixed before
seeing any boundary values. Their signed errors cancel at every entry. -/
theorem two_sums (x y u v : B) :
    pairSum repairPhase x y u v + S x y u v = 4 * Mobius.BoundaryThreshold.W x y u v := by
  rw [untwist,Mobius.BoundaryThreshold.fixed_sum]
  by_cases closes : x = v ∧ y = u
  · obtain ⟨rfl,rfl⟩ := closes
    have no : ¬(y = y ^^^ 8 ∧ x = x ^^^ 8) := by
      intro h
      have impossible : (8:B) = 0 := (BitVec.xor_right_inj y).1 (by simpa using h.1.symm)
      contradiction
    unfold Mobius.BoundaryThreshold.W shiftedW
    rw [ite_eq_left rfl,ite_eq_left ⟨rfl,rfl⟩,ite_eq_right no]; decide
  · unfold Mobius.BoundaryThreshold.W shiftedW
    rw [ite_eq_right closes]
    by_cases shift : u = y ^^^ 8 ∧ v = x ^^^ 8
    · obtain ⟨rfl,rfl⟩ := shift
      have changed : ∀ z : B, z.getLsbD 3 ≠ (z ^^^ 8).getLsbD 3 := by decide
      rw [ite_eq_right (changed x),ite_eq_left (And.intro rfl rfl)]; decide
    · rw [ite_eq_right shift]; split <;> decide

/-- The original quotient table has the positive translated-crossing error. -/
theorem positive_sum (x y u v : B) : pairSum repairPhase x y u v =
    2 * Mobius.BoundaryThreshold.W x y u v + 2 * shiftedW 8 x y u v := by
  have h := two_sums x y u v
  rw [Mobius.BoundaryThreshold.fixed_sum] at h
  omega

/-- Entrywise clipping uses the same fixed table on all queries. -/
theorem clip_entry (x y u v : B) : max (S x y u v) 0 = 2 * Mobius.BoundaryThreshold.W x y u v := by
  by_cases h : x = v ∧ y = u
  · have pos := (Mobius.BoundaryThreshold.positive_iff x y u v).mpr h
    rw [Int.max_eq_left (by omega), Mobius.BoundaryThreshold.fixed_sum]
    obtain ⟨rfl,rfl⟩ := h
    have no : ¬(y = y ^^^ 8 ∧ x = x ^^^ 8) := by
      intro t
      have impossible : (8:B) = 0 := (BitVec.xor_right_inj y).1 (by simpa using t.1.symm)
      contradiction
    unfold shiftedW; rw [ite_eq_right no]; omega
  · have hn : ¬0 < S x y u v := fun hpos => h ((Mobius.BoundaryThreshold.positive_iff ..).mp hpos)
    rw [Int.max_eq_right (by omega),Mobius.BoundaryThreshold.W,ite_eq_right h]; decide

/-- The two histogram kernels are the publicly defined raw measurements. -/
abbrev plusRaw := raw repairPhase repairPhase
abbrev minusRaw := raw thresholdPhase thresholdPhase

private theorem sameW (q : Key) : Mobius.BoundaryThreshold.W q.x q.y q.u q.v = Mobius.BoundarySemantics.W q := by
  simp [Mobius.BoundaryThreshold.W,Mobius.BoundarySemantics.W,Mobius.BoundarySemantics.closes]

theorem raw_sum (q : Key) : plusRaw q + minusRaw q = 4 * Mobius.BoundarySemantics.W q :=
  (two_sums q.x q.y q.u q.v).trans (congrArg (4*·) (sameW q))

theorem raw_clip (q : Key) : max (minusRaw q) 0 = 2 * Mobius.BoundarySemantics.W q :=
  (clip_entry q.x q.y q.u q.v).trans (congrArg (2*·) (sameW q))

private theorem list_sum (qs : List Key) :
    sumI qs plusRaw + sumI qs minusRaw = 4 * sumI qs Mobius.BoundarySemantics.W := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have h := raw_sum q
    change (plusRaw q + sumI qs _) + (minusRaw q + sumI qs _) = 4 * (Mobius.BoundarySemantics.W q + sumI qs _)
    omega

private theorem list_clip (qs : List Key) :
    sumI qs (fun q => max (minusRaw q) 0) = 2 * sumI qs Mobius.BoundarySemantics.W := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have h := raw_clip q
    change max (minusRaw q) 0 + sumI qs _ = 2 * (Mobius.BoundarySemantics.W q + sumI qs _)
    omega

/-- Counts all assignments with multiplicity, allowing arbitrary shared
variables, repeated ports and interior CNF constraints. -/
theorem count_from_two (n : Nat) (f : CNF) (p : Ports) :
    contract n f p plusRaw + contract n f p minusRaw = 4 * (Mobius.TourCount.countWith n (glue f p) : Int) := by
  rw [←Mobius.BoundarySemantics.countWith_crossing]
  simp only [Mobius.BoundarySemantics.contract_unfold]
  exact list_sum _

/-- The nonlinearity here is applied before summing over the boundary. -/
theorem count_from_clipped (n : Nat) (f : CNF) (p : Ports) :
    contract n f p (fun q => max (minusRaw q) 0) = 2 * (Mobius.TourCount.countWith n (glue f p) : Int) := by
  rw [←Mobius.BoundarySemantics.countWith_crossing]
  simp only [Mobius.BoundarySemantics.contract_unfold]
  exact list_clip _

theorem tours_from_two (f : CNF) (p : Ports) (s : Bool) :
    let n := variableBound (glue f p)
    contract n f p plusRaw + contract n f p minusRaw = 4 * (Mobius.TourCount.tours (glue f p) s (!s) : Int) := by
  rw [Mobius.BoundarySemantics.canonical_tours, Mobius.BoundarySemantics.countWith_crossing]
  exact count_from_two _ _ _

/-- The two probes are fixed independently of the encoded input. -/
theorem measure_count (g : Context) :
    measure g plusRaw + measure g minusRaw = 4 * (Mobius.TourCount.sharp (glue g.base g.ports) : Int) :=
  count_from_two _ _ _

private theorem context_sat (g : Context) :
    ThreeSAT g.word ↔ 0 < Mobius.TourCount.sharp (glue g.base g.ports) := by
  rw [Mobius.BoundaryChoice.Context.word,ThreeSAT_encode_iff, Mobius.TourCount.sharp_pos_iff]
  exact and_iff_right g.glue_three

theorem encoded_decision (g : Context) :
    ThreeSAT g.word ↔ 0 < measure g plusRaw + measure g minusRaw := by
  rw [context_sat,measure_count]; omega

/-- In this encoded example, a positive and a negative contribution
cancel in the raw total. Clipping the two contributions first gives 2. -/
theorem clipping_order_example :
    ∃ g : Context, ThreeSAT g.word ∧ measure g minusRaw = 0 ∧
      measure g (fun q => max (minusRaw q) 0) = 2 := by
  let a : Key := ⟨0,0,0,0⟩
  let b : Key := ⟨0,0,8,8⟩
  let g := Mobius.BoundaryChoice.pair a b
  have measurements (f : Key → Int) : measure g f = f a + f b := by
    unfold Mobius.BoundaryDecision.measure
    rw [Mobius.BoundaryChoice.pair_bound a b]
    exact Mobius.BoundaryChoice.score_pair a b f
  have pos : minusRaw a = 2 := by decide
  have neg : minusRaw b = -2 := by decide
  refine ⟨g,(Mobius.BoundaryChoice.threeSAT_pair a b).mpr (Or.inl rfl),?_,?_⟩
  · rw [measurements,pos,neg]; decide
  · rw [measurements]; simp only [pos,neg]; decide

/-- Only raw integer totals are supplied to the readout. The row and
column tables may be independent; the readout may be arbitrary. -/
def CanDecide (k : Nat) := ∃ (r c : Fin k → Phase) (out : (Fin k → Int) → Bool), ∀ g : Context,
  ThreeSAT g.word ↔ out (fun i => measure g (raw (r i) (c i))) = true

def CanCount (k : Nat) := ∃ (r c : Fin k → Phase) (out : (Fin k → Int) → Int), ∀ g : Context,
  out (fun i => measure g (raw (r i) (c i))) = (Mobius.TourCount.sharp (glue g.base g.ports) : Int)

private def tables (i : Fin 2) : Phase := if i.val=0 then repairPhase else thresholdPhase

theorem two_count : CanCount 2 := by
  refine ⟨tables,tables,fun v => (v 0+v 1)/4,?_⟩
  intro g
  change (measure g plusRaw + measure g minusRaw)/4 = _
  rw [measure_count]
  omega

private theorem count_decides {k : Nat} (h : CanCount k) : CanDecide k := by
  obtain ⟨r,c,out,ho⟩ := h
  refine ⟨r,c,fun values => decide (0 < out values),?_⟩
  intro g
  rw [context_sat,decide_eq_true_eq,ho]
  omega

private theorem at_least_two {k : Nat} (works : CanDecide k) : 2 ≤ k := by
  obtain ⟨r,c,out,all⟩ := works
  by_cases small : k < 2
  · exfalso
    cases k with
    | zero =>
      obtain ⟨yes,no,hy,hn,_⟩ := Mobius.BoundaryDecision.opposite_answers_same_measure repairPhase repairPhase
      have eq : (fun i : Fin 0 => measure yes (raw (r i) (c i))) =
          (fun i => measure no (raw (r i) (c i))) := funext (fun i => Fin.elim0 i)
      exact hn ((all no).2 (eq ▸ (all yes).1 hy))
    | succ k =>
      have eqk : k=0 := by omega
      subst k
      obtain ⟨yes,no,hy,hn,eq⟩ := Mobius.BoundaryDecision.opposite_answers_same_measure (r 0) (c 0)
      have e : (fun i : Fin 1 => measure yes (raw (r i) (c i))) =
          (fun i => measure no (raw (r i) (c i))) := by
        funext i
        have single : i = 0 := Fin.ext (by have := i.isLt; omega)
        simpa only [single] using eq
      exact hn ((all no).2 (e ▸ (all yes).1 hy))
  · omega

/-- Two is the minimum number for both SAT and exact #SAT in this raw-total model. -/
theorem exact_measurement_number :
    (CanCount 2 ∧ ∀ k, CanCount k → 2 ≤ k) ∧ (CanDecide 2 ∧ ∀ k, CanDecide k → 2 ≤ k) :=
  ⟨⟨two_count,fun _ h => at_least_two (count_decides h)⟩,⟨count_decides two_count,fun _ h => at_least_two h⟩⟩

end Mobius.BoundaryTwoSums
