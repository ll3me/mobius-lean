import Std

/-!
# Flipping entire derivations

Two distinguished atoms are specified to be complementary. Other atoms are
parameters in a fixed base language. The flip is defined on all syntax and
all annotated deduction trees, including trees rejected by the checker.
This lets us verify the transformation independently of whether a proof
of either distinguished atom exists.
-/

namespace Mobius.Duality

inductive Formula where
  | side (index : Bool)
  | base (index : Nat)
  | bot
  | imp (antecedent consequent : Formula)
  deriving DecidableEq, Repr

namespace Formula

def neg (a : Formula) : Formula := .imp a .bot

def flip : Formula → Formula
  | .side i => .side (!i)
  | .base i => .base i
  | .bot => .bot
  | .imp a b => .imp a.flip b.flip

@[simp] theorem flip_flip (a : Formula) : a.flip.flip = a := by
  induction a <;> simp_all [flip]

@[simp] theorem flip_inj (a b : Formula) : a.flip = b.flip ↔ a = b := by
  constructor
  · intro h
    simpa using congrArg flip h
  · exact congrArg flip

/-- The side swap leaves every formula over the base language syntactically fixed. -/
def inBase : Formula → Prop
  | .side _ => False
  | .base _ | .bot => True
  | .imp a b => a.inBase ∧ b.inBase

theorem flip_of_inBase (a : Formula) (h : a.inBase) : a.flip = a := by
  induction a with
  | side _ => exact h.elim
  | base _ => rfl
  | bot => rfl
  | imp a b ia ib => simp [flip, ia h.1, ib h.2]

def eval (v : Nat → Prop) (s : Bool) : Formula → Prop
  | .side i => i = s
  | .base i => v i
  | .bot => False
  | .imp a b => eval v s a → eval v s b

end Formula

/-- Raw natural deduction syntax. The result annotation on elimination
and explosion is verified by the checker. -/
inductive Tree where
  | hyp (claim : Formula)
  | exclusive (i : Bool)
  | exhaustive (i : Bool)
  | intro (premise : Formula) (body : Tree)
  | app (result : Formula) (function argument : Tree)
  | explode (result : Formula) (absurdity : Tree)
  deriving DecidableEq, Repr

namespace Tree

def conclusion : Tree → Formula
  | .hyp a => a
  | .exclusive i => .imp (.side i) (.neg (.side (!i)))
  | .exhaustive i => .imp (.neg (.side i)) (.side (!i))
  | .intro a d => .imp a d.conclusion
  | .app a _ _ | .explode a _ => a

def check (Γ : List Formula) : Tree → Bool
  | .hyp a => decide (a ∈ Γ)
  | .exclusive _ | .exhaustive _ => true
  | .intro a d => d.check (a :: Γ)
  | .app a f x =>
      (f.check Γ && x.check Γ) && decide (f.conclusion = .imp x.conclusion a)
  | .explode _ d => d.check Γ && decide (d.conclusion = .bot)

def flip : Tree → Tree
  | .hyp a => .hyp a.flip
  | .exclusive i => .exclusive (!i)
  | .exhaustive i => .exhaustive (!i)
  | .intro a d => .intro a.flip d.flip
  | .app a f x => .app a.flip f.flip x.flip
  | .explode a d => .explode a.flip d.flip

@[simp] theorem flip_flip (d : Tree) : d.flip.flip = d := by
  induction d <;> simp_all [flip]

def size : Tree → Nat
  | .hyp _ | .exclusive _ | .exhaustive _ => 1
  | .intro _ d | .explode _ d => d.size + 1
  | .app _ f x => f.size + x.size + 1

@[simp] theorem size_flip (d : Tree) : d.flip.size = d.size := by
  induction d <;> simp_all [flip, size]

@[simp] theorem conclusion_flip (d : Tree) : d.flip.conclusion = d.conclusion.flip := by
  induction d <;> simp_all [flip, conclusion, Formula.flip, Formula.neg]

private theorem mem_flip (Γ : List Formula) (a : Formula) :
    a.flip ∈ Γ.map Formula.flip ↔ a ∈ Γ := by
  induction Γ with
  | nil => simp
  | cons b tail ih => simp [ih]

theorem check_flip (d : Tree) (Γ : List Formula) :
    d.flip.check (Γ.map Formula.flip) = d.check Γ := by
  induction d generalizing Γ with
  | hyp a => simp [flip, check, mem_flip]
  | exclusive i => rfl
  | exhaustive i => rfl
  | intro a body ih =>
    simpa only [flip, check, List.map_cons] using ih (a :: Γ)
  | app a f x hf hx =>
    have he : f.conclusion.flip = Formula.imp x.conclusion.flip a.flip ↔
        f.conclusion = Formula.imp x.conclusion a :=
      Formula.flip_inj f.conclusion (.imp x.conclusion a)
    simp [flip, check, hf, hx, he]
  | explode a d ih =>
    have he : d.conclusion.flip = Formula.bot ↔ d.conclusion = Formula.bot :=
      Formula.flip_inj d.conclusion .bot
    simp [flip, check, ih, he]

/-- Independent semantics checks the natural deduction rules and both
complementarity axioms. Either truth value can be chosen for the first atom. -/
theorem sound (d : Tree) (Γ : List Formula) (v : Nat → Prop) (s : Bool)
    (valid : d.check Γ = true) (env : ∀ a ∈ Γ, a.eval v s) :
    d.conclusion.eval v s := by
  induction d generalizing Γ with
  | hyp a =>
    exact env a (of_decide_eq_true valid)
  | exclusive i =>
    cases i <;> cases s <;> simp [conclusion, Formula.neg, Formula.eval]
  | exhaustive i =>
    cases i <;> cases s <;> simp [conclusion, Formula.neg, Formula.eval]
  | intro a d ih =>
    intro ha
    apply ih (a :: Γ) valid
    intro b hb
    rcases List.mem_cons.mp hb with eq | mem
    · simpa [eq] using ha
    · exact env b mem
  | app a f x hf hx =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at valid
    obtain ⟨⟨vf, vx⟩, eq⟩ := valid
    have hfun := hf Γ vf env
    rw [eq] at hfun
    exact hfun (hx Γ vx env)
  | explode a d ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at valid
    obtain ⟨vd, eq⟩ := valid
    have impossible := ih Γ vd env
    rw [eq] at impossible
    exact False.elim impossible

end Tree

def Provable (a : Formula) : Prop :=
  ∃ d : Tree, d.check [] = true ∧ d.conclusion = a

theorem provable_sound {a : Formula} (h : Provable a) (v : Nat → Prop) (s : Bool) :
    a.eval v s := by
  obtain ⟨d, hd, rfl⟩ := h
  exact d.sound [] v s hd (by simp)

theorem consistent {a : Formula} (p : Provable a) (n : Provable a.neg) : False :=
  (provable_sound n (fun _ => False) false) (provable_sound p _ _)

theorem provable_flip {a : Formula} (h : Provable a) : Provable a.flip := by
  obtain ⟨d, hd, rfl⟩ := h
  exact ⟨d.flip, by simpa using (d.check_flip []).trans hd, d.conclusion_flip⟩

theorem modusPonens {a b : Formula} (f : Provable (.imp a b)) (x : Provable a) :
    Provable b := by
  obtain ⟨df, vf, ef⟩ := f
  obtain ⟨dx, vx, ex⟩ := x
  exact ⟨.app b df dx, by simp [Tree.check, vf, vx, ef, ex], rfl⟩

theorem exclusive_provable (i : Bool) :
    Provable (.imp (.side i) (.neg (.side (!i)))) :=
  ⟨.exclusive i, rfl, rfl⟩

theorem exhaustive_provable (i : Bool) :
    Provable (.imp (.neg (.side i)) (.side (!i))) :=
  ⟨.exhaustive i, rfl, rfl⟩

/-- Both proof transformations are obtained from a total renaming operation
on raw trees and a single use of one of the axioms. No independence hypothesis
enters this construction. -/
theorem side_proof_flip (i : Bool) :
    Provable (.side i) ↔ Provable (.neg (.side i)) := by
  constructor
  · intro h
    have h' : Provable (.side (!i)) := provable_flip h
    simpa using modusPonens (exclusive_provable (!i)) h'
  · intro h
    have h' : Provable (.side (!i)) := modusPonens (exhaustive_provable i) h
    simpa [Formula.flip] using provable_flip h'

/-- An external criterion applicable to any two proof-existence predicates. -/
theorem independent_of_flip {positive negative : Prop}
    (incompatible : positive → negative → False)
    (directions : positive ↔ negative) : ¬positive ∧ ¬negative :=
  ⟨fun p => incompatible p (directions.mp p),
   fun n => incompatible (directions.mpr n) n⟩

theorem side_independent (i : Bool) :
    ¬Provable (.side i) ∧ ¬Provable (.neg (.side i)) :=
  independent_of_flip consistent (side_proof_flip i)

/-- A uniform negator for all conclusions is refuted by the identity proof. -/
theorem no_universal_proof_negator :
    ¬ (∀ a, Provable a → Provable a.neg) := by
  intro negator
  let a : Formula := .imp .bot .bot
  have p : Provable a := ⟨.intro .bot (.hyp .bot), by decide, rfl⟩
  exact consistent p (negator a p)

/-- A renaming that fixes the base language cannot produce an object-level
equivalence between a base sentence and its own negation. This applies to
the syntax of this laboratory; the hypothesis is unrelated to how fast an
actual 3-SAT algorithm runs. -/
theorem no_base_negating_equivalence {a : Formula} (ha : a.inBase) :
    ¬ (Provable (.imp a.flip a.neg) ∧ Provable (.imp a.neg a.flip)) := by
  rw [Formula.flip_of_inBase a ha]
  intro ⟨pos, neg⟩
  let v : Nat → Prop := fun _ => False
  let claim := a.eval v false
  have f : claim → ¬ claim := provable_sound pos v false
  have g : ¬ claim → claim := provable_sound neg v false
  have no : ¬ claim := fun p => f p p
  exact no (g no)

-- A closed proof using implication introduction and elimination really changes.
example :
    let d := Tree.intro (.side false)
      (.app (.neg (.side true)) (.exclusive false) (.hyp (.side false)))
    d.check [] = true ∧ d.flip.check [] = true ∧ d.flip ≠ d ∧ d.flip.flip = d := by
  decide

/-- The two subproofs cross under contraposition. Iteration exchanges
their dependencies while the recursion terminates by descent on n. -/
def iterNeg : Nat → Prop → Prop
  | 0, a => a
  | n + 1, a => ¬ iterNeg n a

theorem crossedIff {a b : Prop} (h : a ↔ b) : (n : Nat) → (iterNeg n a ↔ iterNeg n b)
  | 0 => h
  | n + 1 =>
    let prev := crossedIff h n
    ⟨mt prev.mpr, mt prev.mp⟩

/-- Contraposing a closed proof yields a refutation of its negation.
Interchanging the two implications of an equivalence does not yield a negator. -/
theorem contraposition_is_double_negation {a : Prop} (p : a) : ¬ ¬ a :=
  fun opposite => opposite p

end Mobius.Duality
