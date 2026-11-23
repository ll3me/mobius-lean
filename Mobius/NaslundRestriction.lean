import Mobius.LockedGap

/-! A 15-letter crossing minor of the concrete first nonoptimal residual.
The indices live on the two surviving 15-letter alphabets. The factor two
is the integer normalization of the residual. -/
namespace Mobius.NaslundRestriction
open Mobius.SignObstruction (B repairPhase)
open Mobius.LockedGap (flipOrigin witnessResidual)

private theorem origin_unchanged (x y : B) (h : x ≠ 0 ∨ y ≠ 0) :
    flipOrigin x y = repairPhase x y := by
  simp only [flipOrigin]
  split
  next eq => rcases h with bad | bad <;> simp_all
  next _ => rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem base_residual (x y u v : B) :
    Mobius.SignObstruction.contraction repairPhase x y u v -
    (if x=v ∧ y=u then 2 else 0) =
    (if v=x ^^^ 8 ∧ u=y ^^^ 8 then 2 else 0) := by
  by_cases bal : x ^^^ y = v ^^^ u
  · obtain ⟨d,rfl,rfl⟩ := Mobius.SignObstruction.fiber_parameter _ _ _ _ bal
    clear bal
    revert x y d
    decide
  · rw [Mobius.SignObstruction.off_fiber_zero _ _ _ _ _ bal]
    have a : ¬(x=v ∧ y=u) := by rintro ⟨rfl,rfl⟩; exact bal rfl
    have b : ¬(v=x ^^^ 8 ∧ u=y ^^^ 8) := by
      rintro ⟨rfl,rfl⟩; apply bal
      calc x ^^^ y = (x ^^^ y) ^^^ ((8:B) ^^^ 8) := by simp
           _ = _ := by ac_rfl
    simp only [a,b,ite_false,Int.sub_zero]

theorem witness_minor (x y u v : B) (hx : x ≠ 0) (hu : u ≠ 0) :
    witnessResidual x y u v = (if v=x ^^^ 8 ∧ u=y ^^^ 8 then 2 else 0) := by
  unfold witnessResidual
  rw [origin_unchanged _ _ (Or.inl hx), origin_unchanged _ _ (Or.inr hu)]
  exact base_residual x y u v

/-- On these clean slices both outer legs still range over all 16 letters. -/
theorem witness_strip (x y u v : B) (hy : y ≠ 0) (hu : u ≠ 0) :
    witnessResidual x y u v = (if v=x ^^^ 8 ∧ u=y ^^^ 8 then 2 else 0) := by
  unfold witnessResidual
  rw [origin_unchanged _ _ (Or.inr hy), origin_unchanged _ _ (Or.inr hu)]
  exact base_residual x y u v

end Mobius.NaslundRestriction
