import Mobius.SATSeam
import Mobius.Pullback

/-!
Tie the quantifiers in the proposed obstruction to an actual finite-control
single-tape machine, including timeouts on no-instances. A polynomial clock
counts machine transitions, not recursive calls of the proof checker.
-/
namespace Mobius.Clock
open Complexity Mobius.SATSeam

def CorrectBy (L : Language) (M : Machine) (fuel : Nat) (x : Word) : Prop :=
  ∃ b tape, runInput M fuel x = some (b, tape) ∧ (L x ↔ b = true)

private theorem agree {M : Machine} {x : Word} {t : Nat} {b : Bool} {out : Tape}
    (run : runInput M t x = some (b, out)) : Accepts M x ↔ b = true := by
  constructor
  · rintro ⟨s, tape, other⟩
    exact congrArg Prod.fst (run_deterministic M (initial M x) run other)
  · rintro rfl
    exact ⟨t, out, run⟩

theorem inP_iff_clock (L : Language) :
    InP L ↔ ∃ M c k, ∀ x, CorrectBy L M (powerBound c k x.length) x := by
  constructor
  · rintro ⟨M, ⟨c, k, halts⟩, accepts⟩
    refine ⟨M, c, k, fun x => ?_⟩
    obtain ⟨t, b, tape, ht, hr⟩ := halts x
    exact ⟨b, tape, run_mono M ht (initial M x) _ hr, (accepts x).trans (agree hr)⟩
  · rintro ⟨M, c, k, all⟩
    refine ⟨M, ⟨c, k, fun x => ?_⟩, fun x => ?_⟩
    · obtain ⟨b, tape, hr, _⟩ := all x
      exact ⟨_, b, tape, Nat.le_refl _, hr⟩
    · obtain ⟨b, tape, hr, hL⟩ := all x
      exact hL.trans (agree hr).symm

/-- The usual collapse question in the direction NP ⊆ P. -/
def Collapse : Prop := ∀ L : Language, InNP L → InP L

theorem collapse_iff_fast_seam : Collapse ↔ InP SeamLanguage :=
  ⟨fun h => h _ seam_np_complete.1,
   fun h L np => Mobius.Pullback.inP_of_reduction (seam_np_complete.2 L np) h⟩

/-- This target is equivalent to separation; no unproved bridge is installed
as an axiom. It covers arbitrary machines, coefficients and exponents. -/
theorem separation_iff_clock_failure :
    ¬ Collapse ↔ ∀ (M : Machine) (c k : Nat), ∃ x,
      ¬ CorrectBy SeamLanguage M (powerBound c k x.length) x := by
  rw [collapse_iff_fast_seam, inP_iff_clock]
  constructor
  · intro none M c k
    apply Classical.byContradiction
    intro noFailure
    exact none ⟨M, c, k, fun x => Classical.byContradiction
      (fun bad => noFailure ⟨x, bad⟩)⟩
  · intro fails ⟨M, c, k, h⟩
    obtain ⟨x, bad⟩ := fails M c k
    exact bad (h x)

end Mobius.Clock
