import Mobius.Clock
import Mobius.Inclusion
import Mobius.TourCount

/-! Quantifier check on the last proposed bridge. Even an abstract extractor
is precisely as strong as separation when the target graph already has an
odd return. It becomes mathematical progress only if one supplies an
independent construction of the extractor for a specific machine model. -/
namespace Mobius.Endpoint
open Complexity Mobius.Transport Mobius.Clock Mobius.SATSeam

theorem extraction_iff_separation {V : Type} {E : SignedEdges V} {v : V}
    (odd : Walk E v v true) :
    (∀ M c k, (∀ x, CorrectBy SeamLanguage M (powerBound c k x.length) x) →
      Orientable E) ↔ InP ≠ InNP := by
  constructor
  · intro extract same
    exact separation_of_orientation_extraction odd extract
      (Mobius.Inclusion.collapse_iff_eq.mpr same)
  · intro different M c k fast
    have inP := (inP_iff_clock _).mpr ⟨M,c,k,fast⟩
    exact False.elim (different (Mobius.Inclusion.collapse_iff_eq.mp
      (collapse_iff_fast_seam.mpr inP)))

open Complexity.SAT Mobius.TourCount
example : sharp [[⟨3, true⟩]] = 8 := by decide
example : countWith 6 [[⟨3,true⟩]] = 32 := by decide
example : encode ([] : CNF) = [false] := by decide
example : decode ([] : List Bool) = none := by decide

end Mobius.Endpoint
