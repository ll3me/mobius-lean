import Mobius.Endpoint

/-! A standalone formulation of P ≠ NP using ordinary binary 3-SAT and a
fixed graph. The conjecture is a proposition; the theorem below proves
its equivalence to separation. -/
namespace Mobius.FixedGraphConjecture
open Complexity Mobius.Clock Mobius.Transport

/-- One vertex with a single edge that changes the sign. -/
def flipLoop : SignedEdges Unit := fun _ _ flip => flip = true

theorem odd_return : Walk flipLoop () () true :=
  Walk.single (show flipLoop () () true from rfl)

theorem no_orientation : ¬ Orientable flipLoop :=
  oddLoop_forbids_orientation odd_return

/-- Every correct polynomial-time 3-SAT decider would imply a consistent
labeling of the fixed flip loop. -/
def statement : Prop :=
  ∀ (M : Machine) (c k : Nat),
    (∀ x, CorrectBy SAT.ThreeSAT M (powerBound c k x.length) x) →
    Orientable flipLoop

theorem iff_separation : statement ↔ InP ≠ InNP := by
  unfold statement
  rw [← Mobius.SATSeam.seam_eq_threeSAT]
  exact Mobius.Endpoint.extraction_iff_separation odd_return

end Mobius.FixedGraphConjecture
