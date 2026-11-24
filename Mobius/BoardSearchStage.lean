/-! Finite stages of a universal witness search. The simulator is a
    parameter; the complexity of ordinary deterministic machine simulation
    and NP-completeness of the board language are used in the written proof. -/
namespace Mobius.BoardSearchStage

def hit (run : Nat → I → Nat → Option W) (verify : I → W → Bool)
    (x : I) (budget index : Nat) : Bool :=
  match run index x budget with
  | some w => verify x w
  | none => false

def stage (run : Nat → I → Nat → Option W) (verify : I → W → Bool)
    (x : I) (s : Nat) : Bool :=
  (List.range s).any (hit run verify x s)

theorem stage_iff (run : Nat → I → Nat → Option W) (verify : I → W → Bool) :
    stage run verify x s = true ↔
      ∃ i < s, ∃ w, run i x s = some w ∧ verify x w = true := by
  simp only [stage, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, passed⟩
    cases h : run i x s with
    | none => simp [hit, h] at passed
    | some w => exact ⟨i, hi, w, h, by simpa [hit, h] using passed⟩
  · rintro ⟨i, hi, w, hw, ok⟩
    exact ⟨i, hi, by simp [hit, hw, ok]⟩

/-- If a fixed program halts, every sufficiently large stage includes
    it with enough steps. This also applies to programs that fail on
    other inputs. -/
theorem captures (run : Nat → I → Nat → Option W) (verify : I → W → Bool)
    (stable : ∀ i x t s w, t ≤ s → run i x t = some w → run i x s = some w)
    (hi : i < s) (time : t ≤ s) (printed : run i x t = some w) (ok : verify x w = true) :
    stage run verify x s = true :=
  (stage_iff run verify).mpr ⟨i, hi, w, stable i x t s w time printed, ok⟩

theorem cutoff_correct (run : Nat → I → Nat → Option W) (verify : I → W → Bool)
    (budget : I → Nat)
    (covers : ∀ x, (∃ w, verify x w = true) → stage run verify x (budget x) = true) :
    ∀ x, stage run verify x (budget x) = true ↔ ∃ w, verify x w = true := by
  intro x
  constructor
  · intro yes
    obtain ⟨_, _, w, _, ok⟩ := (stage_iff run verify).mp yes
    exact ⟨w, ok⟩
  · exact covers x

end Mobius.BoardSearchStage
