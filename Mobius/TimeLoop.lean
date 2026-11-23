import Std

/-!
# A polarity reversal that spends an actual time budget

This file checks the finite checkpoint argument, the exponent arithmetic and
the assembly of a strict alternating-hierarchy contradiction. The RAM models,
locally computable quasilinear reduction of nondeterministic linear time to
3-SAT, padded slowdown simulation, timed checkpoint implementation, and
alternating hierarchy theorem are **external**. `ExternalRules` takes their
relevant consequences as hypotheses. This module does not turn a polynomial
Karp reduction into a fine-grained reduction.

The reference pattern is the Lipton–Viglas strict bound: on deterministic
random-access machines an algorithm deciding 3-SAT in time n^(c+o(1)) and
simultaneous workspace n^o(1) cannot have 1 ≤ c < sqrt(2). The integer tours
here cover rational c = p/q and ignore subpolynomial overhead only across a
strict exponent gap.

References: R. Williams, *Alternation-Trading Proofs, Linear Programming, and
Lower Bounds*, §3, Thm 3.1, Lemmas 3.3–3.4, Thm 3.5 and the first example
(https://people.csail.mit.edu/rrw/automated-lbs.pdf);
R. Williams, *Inductive Time-Space Lower Bounds for SAT and Related Problems*,
§2, including the fine-grained 3-SAT transfer
(https://people.csail.mit.edu/rrw/sat-journal-final.pdf).
-/

namespace Mobius.TimeLoop

universe u

/-- An exact, finite deterministic computation segment. -/
def advance {S : Type u} (step : S → S) (time : Nat) (start : S) : S :=
  match time with
  | 0 => start
  | n + 1 => step (advance step n start)

theorem advance_add {S : Type u} (step : S → S) (a b : Nat) (start : S) :
    advance step (a + b) start = advance step b (advance step a start) := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg step ih

def ValidTable {S : Type u} (step : S → S) {blocks : Nat} (span : Nat)
    (start : S) (rows : Fin (blocks + 1) → S) : Prop :=
  rows 0 = start ∧ ∀ i : Fin blocks,
    rows i.succ = advance step span (rows i.castSucc)

private def exactTable {S : Type u} (step : S → S) (blocks span : Nat) (start : S) :
    Fin (blocks + 1) → S :=
  fun i => advance step (i.val * span) start

private theorem exactTable_valid {S : Type u} (step : S → S) (blocks span : Nat) (start : S) :
    ValidTable step span start (exactTable step blocks span start) := by
  constructor
  · simp [exactTable, advance]
  · intro i
    simp [exactTable, Fin.val_succ, Nat.succ_mul, advance_add]

theorem table_unique {S : Type u} (step : S → S) {blocks span : Nat} {start : S}
    {rows : Fin (blocks + 1) → S} (valid : ValidTable step span start rows) :
    rows = exactTable step blocks span start := by
  funext i
  induction i using Fin.induction with
  | zero => simpa [exactTable, advance] using valid.1
  | succ i ih =>
    rw [valid.2 i, ih, (exactTable_valid step blocks span start).2 i]

/-- Existentially guessing checkpoints, universally checking a segment. -/
theorem existential_checkpoints {S : Type u} (step : S → S) (blocks span : Nat)
    (start : S) (accept : S → Prop) :
    accept (advance step (blocks * span) start) ↔
    ∃ rows : Fin (blocks+1) → S, ValidTable step span start rows ∧ accept (rows (Fin.last blocks)) := by
  constructor
  · intro h
    exact ⟨_, exactTable_valid step blocks span start, h⟩
  · rintro ⟨rows, valid, last⟩
    rw [table_unique step valid] at last
    exact last

/-- The flipped proof: for every proposed table with the right start and a
rejecting end, exhibit a bad segment. Only the index must be guessed after
the universal block. This theorem concerns logical witnesses, not RAM time. -/
theorem universal_checkpoints {S : Type u} (step : S → S) (blocks span : Nat)
    (start : S) (accept : S → Prop) :
    accept (advance step (blocks * span) start) ↔
      ∀ rows : Fin (blocks+1) → S, rows 0 = start → ¬ accept (rows (Fin.last blocks)) →
        ∃ i : Fin blocks, rows i.succ ≠ advance step span (rows i.castSucc) := by
  classical
  constructor
  · intro yes rows first last
    apply Classical.byContradiction
    intro none
    have valid : ValidTable step span start rows := ⟨first, fun i =>
      Classical.byContradiction (fun bad => none ⟨i, bad⟩)⟩
    rw [table_unique step valid] at last
    exact last yes
  · intro h
    apply Classical.byContradiction
    intro bad
    have table := exactTable_valid step blocks span start
    obtain ⟨i, invalid⟩ := h _ table.1 bad
    exact invalid (table.2 i)

/-- With n^x checkpoints of n^s bits each, their total size has exponent
x+s. A transition block has time exponent t−x. All exponents here are
nonnegative integers after scaling, with n the original input length. -/
def Fits (t s x e : Nat) : Prop :=
  1 ≤ e ∧ x ≤ t ∧ x + s ≤ e ∧ t - x ≤ e

theorem split_exists_iff (t s e : Nat) :
    (∃ x, Fits t s x e) ↔ 1 ≤ e ∧ s ≤ e ∧ t + s ≤ 2*e := by
  constructor
  · rintro ⟨x, h⟩
    unfold Fits at h
    omega
  · intro h
    exact ⟨t-e, by unfold Fits; omega⟩

/-- If a configuration can be as large as the whole time budget, this very
same argument cannot reduce the time exponent. -/
theorem no_checkpoint_gain_full_space (t e : Nat) :
    (∃ x, Fits t t x e) ↔ 1 ≤ e ∧ t ≤ e := by
  rw [split_exists_iff]
  omega

/-- Four successive class lines: Σ₂(n^start), ∃-guess of exponent start
followed by DTS(n^inner), DTS(n^tapeTime), Π₂(n^finish). DTS has
subpolynomial workspace. The head quantifier changes direction in one tour. -/
structure Tour where
  start : Nat
  inner : Nat
  tapeTime : Nat
  finish : Nat
deriving Repr, DecidableEq

/-- Syntactic certificate for two slowdowns (factor p/q each) and a
balanced checkpoint speedup. The strict hierarchy gap is checked. -/
def Checks (p q : Nat) (c : Tour) : Prop :=
  0 < q ∧ q ≤ p ∧ 0 < c.finish ∧ c.start ≤ c.inner ∧
  c.inner * q = c.start * p ∧ c.tapeTime * q = c.inner * p ∧
  c.tapeTime = 2*c.finish ∧ c.finish < c.start

instance (p q : Nat) (c : Tour) : Decidable (Checks p q c) := inferInstanceAs (Decidable
  (0 < q ∧ q ≤ p ∧ 0 < c.finish ∧ c.start ≤ c.inner ∧
   c.inner * q = c.start * p ∧ c.tapeTime * q = c.inner * p ∧
   c.tapeTime = 2*c.finish ∧ c.finish < c.start))

def balanced (p q : Nat) : Tour := ⟨2*q*q, 2*q*p, 2*p*p, p*p⟩

theorem strict_threshold (p q : Nat) :
    (∃ c, Checks p q c) ↔ 0 < q ∧ q ≤ p ∧ p*p < 2*(q*q) := by
  constructor
  · rintro ⟨c, hq, hp, hf, _, h1, h2, h3, gap⟩
    refine ⟨hq, hp, ?_⟩
    have ht : c.start * (p*p) = c.tapeTime * (q*q) := calc
      c.start * (p*p) = (c.start*p)*p := by ac_rfl
      _ = (c.inner*q)*p := by rw [h1]
      _ = (c.inner*p)*q := by ac_rfl
      _ = (c.tapeTime*q)*q := by rw [h2]
      _ = c.tapeTime*(q*q) := by ac_rfl
    apply Nat.lt_of_mul_lt_mul_left (a := c.start)
    calc
      c.start * (p*p) = (2*c.finish)*(q*q) := by rw [ht, h3]
      _ < (2*c.start)*(q*q) := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left gap (by decide)) (Nat.mul_pos hq hq)
      _ = c.start*(2*(q*q)) := by ac_rfl
  · rintro ⟨hq, hp, gap⟩
    refine ⟨balanced p q, hq, hp, Nat.mul_pos (by omega) (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · exact Nat.mul_le_mul_left (2*q) hp
    · change (2*q*p)*q = (2*q*q)*p
      ac_rfl
    · change (2*p*p)*q = (2*q*p)*p
      ac_rfl
    · exact Nat.mul_assoc 2 p p
    · simpa [balanced, Nat.mul_assoc] using gap

/-- Example with n^(7/5) time. The exponents are 50, 70, 98, 49. -/
example : Checks 7 5 ⟨50, 70, 98, 49⟩ := by decide

/-- 3/2 lies above sqrt(2); no certificate with this fixed shape closes. -/
example : ¬ ∃ c, Checks 3 2 c := by rw [strict_threshold]; decide

/-- Semantic boundary. Class predicates can be given any interpretation.
For the literature's interpretation, the two slowdowns assume a 3-SAT
algorithm with time n^(p/q+o(1)) *and* subpolynomial workspace, including
the model-specific reduction, padding and deterministic complementation.
The faster simulation uses short checkpoints and the alternating hierarchy
separates opposite leading quantifiers across a strict gap. None of these
machine-level theorems is introduced as an axiom of this project. -/
structure Classes (L : Type u) where
  sigmaTwo : Nat → L → Prop
  existsDTS : Nat → Nat → L → Prop
  dts : Nat → L → Prop
  piTwo : Nat → L → Prop

abbrev Included {L : Type u} (a b : L → Prop) : Prop := ∀ x, a x → b x

structure ExternalRules {L : Type u} (classes : Classes L) (fastSAT : Prop) (p q : Nat) : Prop where
  innerSlowdown : fastSAT → ∀ a b, 0 < a → a ≤ b → b*q = a*p →
    Included (classes.sigmaTwo a) (classes.existsDTS a b)
  outerSlowdown : fastSAT → ∀ a b t, 0 < a → a ≤ b → t*q = b*p →
    Included (classes.existsDTS a b) (classes.dts t)
  checkpointSpeedup : ∀ t e, 0 < e → Fits t 0 e e →
    Included (classes.dts t) (classes.piTwo e)
  hierarchy : ∀ a e, 0 < e → e < a → ¬ Included (classes.sigmaTwo a) (classes.piTwo e)

theorem excludes_fast_solver {L : Type u} {classes : Classes L} {fastSAT : Prop} {p q : Nat}
    (external : ExternalRules classes fastSAT p q) {c : Tour} (check : Checks p q c) :
    ¬fastSAT := by
  obtain ⟨_, _, hf, hab, h1, h2, h3, gap⟩ := check
  intro fast
  have ha : 0 < c.start := by omega
  have bound : Fits c.tapeTime 0 c.finish c.finish := by unfold Fits; omega
  apply external.hierarchy c.start c.finish hf gap
  intro lang langIn
  exact external.checkpointSpeedup _ _ hf bound lang
    (external.outerSlowdown fast _ _ _ ha hab h2 lang
      (external.innerSlowdown fast _ _ ha hab h1 lang langIn))

end Mobius.TimeLoop
