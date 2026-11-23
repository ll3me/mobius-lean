import Mobius.Defect

/-! Signed tensor entries corresponding to the four-bit phase tests.
Indices are ordered x,y,u,v; the correct doubled crossing is
2*[x=v]*[y=u]. The only errors possible for a shared ±1 phase are
±2 on the off-diagonal equal-XOR positions. -/
namespace Mobius.SignObstruction

def signed (b : Bool) : Int := if b then -1 else 1

def contraction (phase : B → B → Bool) (x y u v : B) : Int :=
  if x ^^^ y = v ^^^ u then
    signed (phase x y) * signed (phase v u) + signed (phase x u) * signed (phase v y)
  else 0

private theorem sign_sum_zero (a b c d : Bool) :
    signed a * signed d + signed c * signed b = 0 ↔
      (a ^^ (b ^^ (c ^^ d))) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem valid_rectangle_iff_zero (p : B → B → Bool) (x y d : B) :
    oddAt p (x,y,d) ↔ contraction p x y (y ^^^ d) (x ^^^ d) = 0 := by
  have bal : x ^^^ y = (x ^^^ d) ^^^ (y ^^^ d) := by
    calc x ^^^ y = (x ^^^ y) ^^^ (d ^^^ d) := by simp
         _ = _ := by ac_rfl
  simp [oddAt, total, corners, contraction, bal, sign_sum_zero]

theorem exact_on_diagonal (p : B → B → Bool) (x y : B) : contraction p x y y x = 2 := by
  cases h : p x y <;> simp [contraction, h, signed]

theorem off_fiber_zero (p : B → B → Bool) (x y u v : B) (h : x ^^^ y ≠ v ^^^ u) :
    contraction p x y u v = 0 := by simp [contraction,h]

theorem fiber_parameter (x y u v : B) (h : x ^^^ y = v ^^^ u) :
    ∃ d : B, u = y ^^^ d ∧ v = x ^^^ d := by
  refine ⟨y ^^^ u, ?_, ?_⟩
  · simp [← BitVec.xor_assoc]
  · calc v = (v ^^^ u) ^^^ u := by simp [BitVec.xor_assoc]
         _ = x ^^^ (y ^^^ u) := by rw [←h, BitVec.xor_assoc]

/-- Reindexing x,y,d ↦ x,y,y⊕d,x⊕d does not identify different entries. -/
theorem entry_injective (x y d a b e : B)
    (h : (x,y,y ^^^ d,x ^^^ d) = (a,b,b ^^^ e,a ^^^ e)) :
    (x,y,d) = (a,b,e) := by
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨rfl,rfl,h,_⟩ := h
  have e := congrArg (fun z => y ^^^ z) h
  simpa [← BitVec.xor_assoc] using e

end Mobius.SignObstruction
