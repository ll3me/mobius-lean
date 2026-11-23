import Std
import Complexity.Classes
import Complexity.SAT

/-!
# An easy decision problem with no invariant witness selector

A word describes a family of actual width-three formulas. In every yes
instance precisely one of variables 0 and 1 is true. Their exchange, combined
with reversal of literal order in each clause, fixes the entire formula.
It exchanges actual satisfying assignments freely. The parameter language
contains yes and no words and has a one-instruction decider in the upstream
machine model. This distinguishes decision from *equivariant* witness selection.
-/

namespace Mobius.Naturality

open Complexity
open Complexity.SAT (Literal Clause CNF Assignment evalCNF Satisfiable IsThreeCNF)

def renameVar : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

def renameClause (c : Clause) : Clause :=
  (c.map fun l => {l with var := renameVar l.var}).reverse

/-- Four exact-width clauses assert x₀ xor x₁ independently of x₂. -/
def different : CNF :=
  [[⟨0,true⟩, ⟨2,true⟩, ⟨1,true⟩], [⟨0,true⟩, ⟨2,false⟩, ⟨1,true⟩],
   [⟨0,false⟩, ⟨2,true⟩, ⟨1,false⟩], [⟨0,false⟩, ⟨2,false⟩, ⟨1,false⟩]]

private def force (b : Bool) : Clause := List.replicate 3 ⟨2,b⟩

/-- This tautology makes the last variable name vary with the input length. -/
private def padding (n : Nat) : Clause := [⟨n+3,true⟩, ⟨n+3,false⟩, ⟨n+3,true⟩]

def tag : Complexity.Word → Bool
  | [] => false
  | b :: _ => b

def family (w : Complexity.Word) : CNF :=
  different ++ [padding w.length] ++
    (if tag w then [] else [force true, force false])

theorem family_exactWidth (w : Complexity.Word) :
    ∀ c ∈ family w, c.length = 3 := by
  intro c hc
  cases h : tag w
  · simp [family, different, h] at hc
    rcases hc with h | h | h | h | h | h | h <;> subst c <;> rfl
  · simp [family, different, h] at hc
    rcases hc with h | h | h | h | h <;> subst c <;> rfl

/-- The symmetry fixes the raw library formula, including all orderings. -/
theorem family_fixed (w : Complexity.Word) :
    (family w).map renameClause = family w := by
  cases h : tag w <;> simp [family, h, different, padding, force, renameClause, renameVar]

theorem evaluate_family (a : Assignment) (w : Complexity.Word) :
    evalCNF a (family w) = (tag w && (a 0 != a 1)) := by
  cases hw : tag w <;> cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;>
    cases hp : a (w.length+3) <;>
    simp [family, different, force, padding, hw, h0, h1, h2, hp, evalCNF,
      Complexity.SAT.evalClause, Complexity.SAT.evalLiteral]

/-- Even extending witnesses to all variables cannot introduce a fixed point. -/
theorem no_fixed_full_assignment {a : Assignment} {w : Complexity.Word}
    (h : evalCNF a (family w) = true) : (fun i => a (renameVar i)) ≠ a := by
  intro fixed
  have eq : a 1 = a 0 := congrFun fixed 0
  simp [evaluate_family, eq] at h

def ordinaryAssignment : Assignment
  | 1 => true
  | _ => false

def ParameterLanguage (w : Complexity.Word) : Prop := Satisfiable (family w)

theorem language_iff (w : Complexity.Word) : ParameterLanguage w ↔ tag w = true := by
  constructor
  · rintro ⟨a, h⟩
    rw [evaluate_family] at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  · intro hw
    exact ⟨ordinaryAssignment, by simp [evaluate_family, hw, ordinaryAssignment]⟩

def headMachine : Machine where
  states := 0
  start := ⟨0, by decide⟩
  code := fun _ symbol => .halt (decide (symbol = .bit true))

theorem headMachine_run (w : Complexity.Word) (fuel : Nat) :
    runInput headMachine (fuel+1) w = some (tag w, Tape.ofInput w) := by
  cases w with
  | nil => rfl
  | cons b bs => cases b <;> rfl

/-- The coefficient is one and exponent zero, counting the halting instruction. -/
theorem parameter_inP : InP ParameterLanguage := by
  refine ⟨headMachine, ⟨1, 0, fun w => ⟨1, tag w, Tape.ofInput w, ?_, headMachine_run w 0⟩⟩,
    fun w => ?_⟩
  · simp [powerBound_eq]
  · rw [language_iff]
    constructor
    · intro h
      exact ⟨1, Tape.ofInput w, by simpa [h] using headMachine_run w 0⟩
    · rintro ⟨fuel, tape, accepts⟩
      cases fuel with
      | zero => simp [runInput, run] at accepts
      | succ n =>
        rw [headMachine_run] at accepts
        exact (Prod.mk.inj (Option.some.inj accepts)).1

/-- A finite witness records the values on the three constrained variables.
The one extra padding variable is unconstrained. On every satisfying full
assignment the first two values differ, by evaluate_family. -/
structure Witness where
  x : Bool
  y : Bool
  z : Bool
  deriving DecidableEq, Repr

def Witness.assignment (p : Witness) : Assignment
  | 0 => p.x
  | 1 => p.y
  | 2 => p.z
  | _ => false

def Certificate (w : Complexity.Word) :=
  {p : Witness // evalCNF p.assignment (family w) = true}

def Certificate.turn {w : Complexity.Word} (p : Certificate w) : Certificate w :=
  ⟨⟨p.val.y, p.val.x, p.val.z⟩, by
    have h := p.property
    rw [evaluate_family] at h ⊢
    simpa [Witness.assignment, bne_comm] using h⟩

theorem certificate_involution {w : Complexity.Word} (p : Certificate w) :
    p.turn.turn = p := by cases p with | mk a ok => cases a; rfl

theorem certificate_no_fixed {w : Complexity.Word} (p : Certificate w) :
    p.turn ≠ p := by
  intro fixed
  have eq := congrArg (fun t : Certificate w => t.val.x) fixed
  change p.val.y = p.val.x at eq
  have h := p.property
  simp [evaluate_family, Witness.assignment, eq] at h

abbrev Selector := (w : Complexity.Word) → ParameterLanguage w → Certificate w

/-- Normal choices need no side-tag: the witness itself satisfies the CNF. -/
def ordinarySelector : Selector := fun w yes =>
  ⟨⟨false,true,false⟩, by simp [evaluate_family, (language_iff w).mp yes, Witness.assignment]⟩

/-- Input is unchanged by the symmetry. Equivariance would therefore require
the selected proof above each fixed input to be a fixed point of turn. -/
def Equivariant (pick : Selector) : Prop :=
  ∀ w yes, (pick w yes).turn = pick w yes

theorem no_equivariant_selector : ¬∃ pick : Selector, Equivariant pick := by
  rintro ⟨pick, commutes⟩
  have yes : ParameterLanguage [true] := (language_iff _).mpr rfl
  exact certificate_no_fixed (pick [true] yes) (commutes [true] yes)

theorem fast_decision_with_free_certificates :
    InP ParameterLanguage ∧ Nonempty Selector ∧ ¬∃ pick : Selector, Equivariant pick :=
  ⟨parameter_inP, ⟨ordinarySelector⟩, no_equivariant_selector⟩

end Mobius.Naturality
