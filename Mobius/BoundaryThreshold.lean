import Mobius.RigidityEnumeration
import Mobius.RankTradeGauge
import Mobius.Residual

/-! Exact tensor synthesis and Boolean recognition on the same crossing.
Multiplying a fixed optimal table by a row sign makes all its exceptional
entries negative. The positive support therefore recognizes the crossing
with zero decision errors, despite 256 failed numerical identities.
Two fixed optimal table pairs also suffice for pointwise exact synthesis if
one permits the table choice to depend on the queried entry. -/
namespace Mobius.BoundaryThreshold
open Mobius.SignObstruction (B repairPhase)
open Mobius.RankTradeGauge (kernel sig)
open Mobius.Rigidity.Enumeration (Phase)
open Mobius.TwoPhases (score)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Four-legged equality crossing as an integer-valued indicator. -/
def W (x y u v : B) : Int := if x = v ∧ y = u then 1 else 0

def shiftedW (h x y u v : B) : Int := if u = y ^^^ h ∧ v = x ^^^ h then 1 else 0

/-- The same single phase table is used for both pairings. -/
def pairSum (p : Phase) (x y u v : B) : Int := kernel p x y u v + kernel p x u y v

def thresholdPhase (x y : B) := repairPhase x y ^^ x.getLsbD 3

def S := pairSum thresholdPhase

private theorem four (a b c e : Bool) : sig a * sig b + sig c * sig e =
    (if a ^^ (b ^^ (c ^^ (e ^^ false))) then 0 else 2 * sig (a ^^ b)) := by
  cases a <;> cases b <;> cases c <;> cases e <;> decide

private theorem fiber_eq (x y d : B) : x ^^^ y = (x ^^^ d) ^^^ (y ^^^ d) := by
  calc
    _ = (x ^^^ y) ^^^ (d ^^^ d) := by simp
    _ = _ := by ac_rfl

private theorem fiber_value (p : Phase) (x y d : B) :
    pairSum p x y (y ^^^ d) (x ^^^ d) =
      if score p p (x,y,d) then 0 else 2 * sig (p x y ^^ p (x ^^^ d) (y ^^^ d)) := by
  have first := fiber_eq x y d
  have second : x ^^^ (y ^^^ d) = (x ^^^ d) ^^^ y := by ac_rfl
  simp only [pairSum,kernel,first,second,ite_true,score,Mobius.TwoPhases.corners,Mobius.SignObstruction.total]
  exact four _ _ _ _

private theorem off_fiber (p : Phase) (x y u v : B) (h : x ^^^ y ≠ v ^^^ u) :
    pairSum p x y u v = 0 := by
  have k := Mobius.RankTradeGauge.off_block p p x y u v h
  have no : ¬(x = v ∧ y = u) := by rintro ⟨rfl,rfl⟩; exact h rfl
  simpa only [Mobius.RankTradeGauge.physical,no,ite_false,Int.mul_zero,Int.sub_zero,pairSum] using k

private theorem signature (x y d : B) (hd : d ≠ 0) : score thresholdPhase thresholdPhase (x,y,d) = decide (d ≠ 8) := by
  have original := Mobius.SignObstruction.repair_signature x y d hd
  simpa [thresholdPhase,score,Mobius.TwoPhases.corners,Mobius.SignObstruction.corners,
    Mobius.SignObstruction.total,Bool.xor_comm,Bool.xor_left_comm] using original

private theorem neg_at_eight : ∀ x y : B, (thresholdPhase x y ^^ thresholdPhase (x ^^^ 8) (y ^^^ 8)) = true := by decide +kernel

theorem thresholdPhase_optimal : Mobius.TwoPhases.failures thresholdPhase thresholdPhase = 256 :=
  Mobius.Rigidity.optimal_of_direction (d := 8) ⟨by decide,signature⟩

/-- Exact integer values of the fixed two-term approximation. -/
theorem fixed_sum (x y u v : B) : S x y u v = 2 * W x y u v - 2 * shiftedW 8 x y u v := by
  by_cases same : x ^^^ y = v ^^^ u
  · obtain ⟨d,rfl,rfl⟩ := Mobius.SignObstruction.fiber_parameter x y u v same
    change pairSum thresholdPhase _ _ _ _ = _
    rw [fiber_value]
    have eq0 : (x = x ^^^ d ∧ y = y ^^^ d) ↔ d = 0 := by
      constructor
      · intro h; apply (BitVec.xor_right_inj x).1; simpa using h.1.symm
      · rintro rfl; simp
    have eq8 : (y ^^^ d = y ^^^ 8 ∧ x ^^^ d = x ^^^ 8) ↔ d = 8 := by simp only [BitVec.xor_right_inj,and_self]
    unfold W shiftedW
    simp only [eq0, eq8]
    by_cases dz : d=0
    · subst d
      rw [ite_eq_left rfl,ite_eq_right (by decide : (0:B) ≠ 8)]
      simp [score,Mobius.TwoPhases.corners,Mobius.SignObstruction.total,sig]
    · rw [signature _ _ _ dz,ite_eq_right dz]
      by_cases dh : d = 8
      · subst d
        rw [ite_eq_left rfl,neg_at_eight]
        decide
      · rw [ite_eq_right dh,decide_eq_true dh]
        rfl
  · change pairSum thresholdPhase _ _ _ _ = _
    rw [off_fiber _ _ _ _ _ same]
    have no : ¬(x = v ∧ y = u) := by rintro ⟨rfl,rfl⟩; exact same rfl
    have ns : ¬(u = y ^^^ 8 ∧ v = x ^^^ 8) := by rintro ⟨rfl,rfl⟩; exact same (fiber_eq x y 8)
    unfold W shiftedW
    rw [ite_eq_right no,ite_eq_right ns]; decide

/-- One global fixed pair gives exact Boolean decisions on every entry. -/
theorem positive_iff (x y u v : B) : 0 < S x y u v ↔ x = v ∧ y = u := by
  rw [fixed_sum]
  by_cases w : x = v ∧ y = u
  · obtain ⟨rfl,rfl⟩ := w
    have notShift : ¬(y = y ^^^ 8 ∧ x = x ^^^ 8) := by
      intro h
      have wrong : (8 : B) = 0 := (BitVec.xor_right_inj y).1 (by simpa using h.1.symm)
      contradiction
    unfold W shiftedW
    rw [ite_eq_right notShift,ite_eq_left (And.intro rfl rfl)]
    simp
  · simp only [W,w,ite_false,shiftedW]
    split <;> decide

/-- An alternative optimum with exceptional direction 1. -/
def sparePhase := (Mobius.Rigidity.Enumeration.ground ⟨1,by decide⟩).1

theorem sparePhase_optimal : Mobius.TwoPhases.failures sparePhase sparePhase = 256 :=
  Mobius.Rigidity.optimal_of_direction (Mobius.Rigidity.Enumeration.ground_pattern ⟨1,by decide⟩)

def select (x v : B) : Phase := if x ^^^ v = 8 then sparePhase else thresholdPhase

/-- One bit selects between the two tables before evaluating a queried entry. -/
theorem adaptive_exact (x y u v : B) : pairSum (select x v) x y u v = 2 * W x y u v := by
  by_cases h : x ^^^ v = 8
  · rw [select,ite_eq_left h]
    have ne : x ≠ v := by rintro rfl; simp at h
    have no : ¬(x = v ∧ y = u) := fun k => ne k.1
    simp only [W,no,ite_false,Int.mul_zero]
    by_cases eqn : x ^^^ y = v ^^^ u
    · obtain ⟨d,rfl,rfl⟩ := Mobius.SignObstruction.fiber_parameter x y u v eqn
      have eq8 : d = 8 := by simpa [←BitVec.xor_assoc] using h
      subst d
      rw [fiber_value]
      have pat := (Mobius.Rigidity.Enumeration.ground_pattern ⟨1,by decide⟩).2 x y 8 (by decide)
      change score sparePhase sparePhase (x,y,8) = true at pat
      rw [pat]; rfl
    · exact off_fiber _ _ _ _ _ eqn
  · rw [select,ite_eq_right h]
    change S _ _ _ _ = _
    rw [fixed_sum]
    have noShift : ¬(u = y ^^^ 8 ∧ v = x ^^^ 8) := by
      rintro ⟨_,rfl⟩; apply h; simp [←BitVec.xor_assoc]
    unfold shiftedW
    rw [ite_eq_right noShift]; omega

end Mobius.BoundaryThreshold
