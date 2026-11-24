import Mobius.PairContraction

namespace HamiltonianAffineCut

/-- On the coordinates selected by p, the two extreme assignments enclose x.
If f is invariant under flipping those coordinates, f cannot distinguish x
from any other assignment with the same outside bits. -/
theorem invariant_interval {ι : Type} (f : (ι → Bool) → Bool) (p : ι → Bool)
    (mono : ∀ x y, (∀ i, x i ≤ y i) → f x ≤ f y)
    (inv : ∀ x, f (fun i => if p i then !(x i) else x i) = f x)
    (x y : ι → Bool) (outside : ∀ i, p i = false → x i = y i) : f x = f y := by
  let lo : ι → Bool := fun i => if p i then false else x i
  let hi : ι → Bool := fun i => if p i then true else x i
  have extremes : f hi = f lo := by
    rw [← inv lo]
    apply congrArg f
    funext i
    cases hp : p i <;> simp [lo, hi, hp]
  have middle (z : ι → Bool) (hz : ∀ i, p i = false → x i = z i) : f z = f lo := by
    apply Bool.le_antisymm
    · rw [← extremes]
      apply mono
      intro i
      cases hp : p i <;> simp [hi, hp, hz i]
    · apply mono
      intro i
      cases hp : p i <;> simp [lo, hp, hz i]
  exact (middle x (fun _ _ => rfl)).trans (middle y outside).symm

end HamiltonianAffineCut
