import Mobius.BoundaryDecision

/-! Boolean errors on an explicitly weighted list of ordinary CNF inputs.
The first 7680 indices consist of two contexts for each ordered anchor and
nonzero direction. The extended list repeats two calibration inputs 256
times each. All rates here refer to those lists, with repetitions. -/
namespace Mobius.BoundaryBooleanRate

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

open Complexity.SAT
open Mobius.BoundarySemantics (B Key Phase closes)
open Mobius.BoundaryChoice (Context point pair empty)
open Mobius.BoundaryDecision (raw measure off diagonal)
open Mobius.SignObstruction (Cell shifts directions)
open Mobius.Rigidity (oneIf)

structure Test where
  context : Context
  expected : Bool
  correct : expected = true ↔ ThreeSAT context.word

def pointTest (q : Key) : Test := ⟨point q, closes q, (Mobius.BoundaryChoice.threeSAT_point q).symm⟩

def pairTest (q : Key) : Test := ⟨pair diagonal q, true, by
  constructor
  · intro _; exact (Mobius.BoundaryChoice.threeSAT_pair ..).2 (Or.inl rfl)
  · intro _; rfl⟩

def emptyTest : Test := ⟨empty, false, by
  simp [Mobius.BoundaryChoice.not_threeSAT_empty]⟩

def block (xy : Cell) (d : B) : List Test :=
  [pointTest (off xy.1 xy.2 d), pairTest (off xy.1 xy.2 d)]

def probes : List Test := directions.flatMap fun d => shifts.flatMap fun xy => block xy d

def tests : List Test := probes ++
  (List.replicate 256 emptyTest ++ List.replicate 256 (pointTest diagonal))

def positive (z : Int) : Bool := decide (0 < z)

def mistake (r c : Phase) (D : Int → Bool) (t : Test) : Nat :=
  oneIf (D (measure t.context (raw r c)) != t.expected)

def errorCount (r c : Phase) (D : Int → Bool) (xs : List Test) : Nat :=
  (xs.map (mistake r c D)).sum

private def tally (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

private theorem tally_flat (xs : List α) (build : α → List β) (w : β → Nat) :
    tally (xs.flatMap build) w = tally xs (fun a => tally (build a) w) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [tally, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] using congrArg (tally (build a) w + ·) ih

private theorem tally_congr (xs : List α) {f g : α → Nat}
    (h : ∀ x ∈ xs, f x = g x) : tally xs f = tally xs g :=
  congrArg List.sum (List.map_congr_left h)

private theorem tally_le (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    tally xs f ≤ tally xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a xs ih =>
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

private theorem probes_by_block (r c : Phase) (D : Int → Bool) :
    errorCount r c D probes = tally directions (fun d =>
      tally shifts (fun xy => errorCount r c D (block xy d))) := by
  change tally (directions.flatMap _) _ = _
  rw [tally_flat]
  exact tally_congr directions (fun d _ => tally_flat shifts _ _)

private theorem bound_point (q : Key) (r c : Phase) :
    measure (point q) (raw r c) = raw r c q := by
  rw [Mobius.BoundaryDecision.measure_at_four _ _ (Mobius.BoundaryChoice.point_bound _),
    Mobius.BoundaryChoice.score_point]

private theorem bound_pair (q : Key) (r c : Phase) :
    measure (pair diagonal q) (raw r c) = 2 + raw r c q := by
  rw [Mobius.BoundaryDecision.measure_at_four _ _ (Mobius.BoundaryChoice.pair_bound ..),
    Mobius.BoundaryChoice.score_pair, Mobius.BoundaryDecision.raw_diagonal]

private theorem bound_empty (r c : Phase) :
    measure empty (raw r c) = 0 := by
  rw [Mobius.BoundaryDecision.measure_at_four _ _ Mobius.BoundaryChoice.empty_bound,
    Mobius.BoundaryChoice.score_empty]

private theorem block_errors (r c : Phase) (D : Int → Bool) (x y d : B) (hd : d ≠ 0) :
    errorCount r c D (block (x,y) d) =
      oneIf (D (raw r c (off x y d))) + oneIf (!(D (2 + raw r c (off x y d)))) := by
  simp [block, errorCount, mistake, pointTest, pairTest, bound_point, bound_pair,
    Mobius.BoundaryDecision.closes_off x y d hd]

private theorem raw_values (r c : Phase) (x y d : B) :
    raw r c (off x y d) = 0 ∨ raw r c (off x y d) = 2 ∨ raw r c (off x y d) = -2 := by
  by_cases z : raw r c (off x y d) = 0
  · exact Or.inl z
  · right
    rw [Mobius.BoundaryDecision.raw_off] at z ⊢
    exact (Mobius.BoundaryDecision.unit_signs _ _ _ _).2 z

private theorem scalar_positive (z : Int) (values : z = 0 ∨ z = 2 ∨ z = -2) :
    oneIf (positive z) + oneIf (!(positive (2+z))) = oneIf (decide (z ≠ 0)) := by
  rcases values with rfl | rfl | rfl <;> decide

private theorem scalar_calibrated (D : Int → Bool) (h₀ : D 0 = false) (h₂ : D 2 = true)
    (z : Int) (values : z = 0 ∨ z = 2 ∨ z = -2) :
    oneIf (decide (z ≠ 0)) ≤ oneIf (D z) + oneIf (!(D (2+z))) := by
  rcases values with rfl | rfl | rfl
  · exact Nat.zero_le _
  · simp [oneIf,h₂]
  · rw [show (2 : Int)+ -2 = 0 by decide,h₀]
    simp [oneIf]

private theorem nonzero_dirs (d : B) (h : d ∈ directions) : d ≠ 0 := by
  revert d h; decide

theorem block_threshold (r c : Phase) (x y d : B) (hd : d ≠ 0) :
    errorCount r c positive (block (x,y) d) = oneIf (!Mobius.TwoPhases.score r c (x,y,d)) := by
  rw [block_errors _ _ _ _ _ _ hd,scalar_positive _ (raw_values r c x y d),
    Mobius.BoundaryDecision.mismatch]

theorem threshold_errors_eq_failures (r c : Phase) :
    errorCount r c positive probes = Mobius.TwoPhases.failures r c := by
  rw [probes_by_block, Mobius.Rigidity.two_count]
  change tally directions _ = tally directions (fun d => tally shifts (fun xy =>
    oneIf (!Mobius.TwoPhases.score r c (xy.1,xy.2,d))))
  apply tally_congr directions
  intro d hd
  apply tally_congr shifts
  intro xy _
  obtain ⟨x,y⟩ := xy
  exact block_threshold r c x y d (nonzero_dirs _ hd)

/-- At the best possible Boolean error count the failed pairs of encoded
SAT instances identify one nonzero direction, read directly from their labels. -/
theorem optimal_error_direction (r c : Phase) (opt : errorCount r c positive probes = 256) :
    ∃ d : B, d ≠ 0 ∧ ∀ x y e : B, e ≠ 0 →
      errorCount r c positive (block (x,y) e) = if e = d then 1 else 0 := by
  rw [threshold_errors_eq_failures] at opt
  obtain ⟨d,pat,_⟩ := Mobius.Rigidity.optimal_direction r c opt
  refine ⟨d,pat.1,?_⟩
  intro x y e he
  rw [block_threshold r c x y e he, pat.2 x y e he]
  by_cases h : e = d <;> simp [h,oneIf]

private theorem calibrated_lower (r c : Phase) (D : Int → Bool)
    (h₀ : D 0 = false) (h₂ : D 2 = true) :
    Mobius.TwoPhases.failures r c ≤ errorCount r c D probes := by
  rw [probes_by_block, Mobius.Rigidity.two_count]
  change tally directions (fun d => tally shifts (fun xy =>
    oneIf (!Mobius.TwoPhases.score r c (xy.1,xy.2,d)))) ≤ tally directions _
  apply tally_le
  intro d hd
  apply tally_le
  intro xy _
  obtain ⟨x,y⟩ := xy
  rw [block_errors _ _ _ _ _ _ (nonzero_dirs _ hd), ←Mobius.BoundaryDecision.mismatch]
  exact scalar_calibrated D h₀ h₂ _ (raw_values r c x y d)

/-- The two repeated calibration inputs contribute their explicit multiplicities. -/
theorem errors_with_calibration (r c : Phase) (D : Int → Bool) :
    errorCount r c D tests = errorCount r c D probes + (256*oneIf (D 0) + 256*oneIf (!(D 2))) := by
  have low : mistake r c D emptyTest = oneIf (D 0) := by
    simp [mistake, emptyTest, bound_empty]
  have high : mistake r c D (pointTest diagonal) = oneIf (!(D 2)) := by
    simp [mistake, pointTest, bound_point, Mobius.BoundaryDecision.raw_diagonal,
      show closes diagonal = true by rfl]
  simp only [errorCount, tests, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate_nat, low, high]

theorem decoder_lower (r c : Phase) (D : Int → Bool) : 256 ≤ errorCount r c D tests := by
  rw [errors_with_calibration]
  cases h₀ : D 0 <;> cases h₂ : D 2
  · simp [oneIf]
  · have h := Nat.le_trans (Mobius.TwoPhases.failures_lower r c) (calibrated_lower r c D h₀ h₂)
    simpa [oneIf] using h
  · simp [oneIf]
  · simp [oneIf]

theorem threshold_with_calibration (r c : Phase) :
    errorCount r c positive tests = Mobius.TwoPhases.failures r c := by
  rw [errors_with_calibration,threshold_errors_eq_failures]
  have cal : 256*oneIf (positive 0) + 256*oneIf (!(positive 2)) = 0 := by decide
  rw [cal,Nat.add_zero]

private theorem length_flat_const (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x, (f x).length = n) : (xs.flatMap f).length = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, h, ih, List.length_cons, Nat.succ_mul]
    omega

theorem probes_length : probes.length = 7680 := by
  have inner (d : B) : (shifts.flatMap fun x => block x d).length = 512 := by
    rw [length_flat_const _ _ 2 (fun _ => rfl)]; decide
  rw [probes, length_flat_const _ _ 512 inner]; decide

theorem tests_length : tests.length = 8192 := by
  rw [tests,List.length_append,probes_length,List.length_append,List.length_replicate,List.length_replicate]

theorem sharp_threshold :
    probes.length = 7680 ∧
    (∀ r c, 256 ≤ errorCount r c positive probes) ∧
    errorCount Mobius.BoundaryThreshold.thresholdPhase Mobius.BoundaryThreshold.thresholdPhase
      positive probes = 256 := by
  exact ⟨probes_length,fun r c => by rw [threshold_errors_eq_failures]; exact Mobius.TwoPhases.failures_lower ..,
    (threshold_errors_eq_failures ..).trans Mobius.BoundaryThreshold.thresholdPhase_optimal⟩

theorem sharp_all_decoders :
    tests.length = 8192 ∧
    (∀ r c D, 256 ≤ errorCount r c D tests) ∧
    errorCount Mobius.BoundaryThreshold.thresholdPhase Mobius.BoundaryThreshold.thresholdPhase
      positive tests = 256 :=
  ⟨tests_length,decoder_lower,(threshold_with_calibration ..).trans Mobius.BoundaryThreshold.thresholdPhase_optimal⟩

end Mobius.BoundaryBooleanRate
