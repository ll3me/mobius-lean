import Mobius.Clock
import Complexity.NTM.Verifier

/-! Deterministic machines embed into the certificate definition of NP.
The concrete one-tape verifier unpacks its input and simulates the deterministic
machine with both nondeterministic choices set to its sole transition table.
Its certificate length bound is zero, including on the empty input. -/
namespace Mobius.Inclusion
open Complexity Complexity.NTM

/-- The concrete verifier is polynomial on every binary input. On a valid
pair it decides the original language, independently of the certificate. -/
theorem verifier_of_inP {L : Language} (hp : InP L) :
    ∃ V : Machine, PolynomialTimeMachine V ∧
      ∀ x w, L x ↔ Accepts V (pairWords x w) := by
  obtain ⟨D, c, k, clock⟩ := (Mobius.Clock.inP_iff_clock L).mp hp
  have halts : ∀ x : Word, ∀ cs : List Bool, cs.length = powerBound c k x.length →
      (lift D).run cs (lift D).start (Tape.ofInput x) ≠ none := by
    intro x cs len
    obtain ⟨b, tape, hr, _⟩ := clock x
    change (lift D).run cs D.start (Tape.ofInput x) ≠ none
    rw [lift_run D cs D.start (Tape.ofInput x), len]
    change runInput D (powerBound c k x.length) x ≠ none
    rw [hr]
    exact Option.some_ne_none _
  obtain ⟨hpoly, hpair⟩ := verifierMachine_spec (lift D) c k halts
  refine ⟨verifierMachine (lift D), hpoly, ?_⟩
  intro x w
  obtain ⟨b, tape, hr, correct⟩ := clock x
  rw [hpair, correct]
  change b = true ↔ ∃ out, (lift D).run (padChoices _ w) D.start (Tape.ofInput x) = some (true, out)
  rw [lift_run D _ D.start (Tape.ofInput x), padChoices_length]
  change b = true ↔ ∃ out, runInput D (powerBound c k x.length) x = some (true, out)
  rw [hr]
  simp

/-- Choosing the empty certificate suffices for every yes-instance. -/
theorem inNP_of_inP {L : Language} (hp : InP L) : InNP L := by
  obtain ⟨V, hpoly, hpair⟩ := verifier_of_inP hp
  refine ⟨V, 0, 0, hpoly, ?_⟩
  intro x
  exact ⟨fun hx => ⟨[], Nat.zero_le _, (hpair x []).mp hx⟩,
    fun ⟨w, _, hw⟩ => (hpair x w).mpr hw⟩

/-- Extensional equality of the two concrete predicates on binary languages. -/
theorem collapse_iff_eq : Mobius.Clock.Collapse ↔ InP = InNP := by
  constructor
  · intro collapse
    funext L
    exact propext ⟨inNP_of_inP, collapse L⟩
  · intro equal L hL
    rw [equal]
    exact hL

end Mobius.Inclusion
