import Complexity.NPCompleteness
import Mobius.Transport

/-!
A signed graph of certificate-checking obligations on an actual encoded CNF.
The orientation bit belongs to the proof interface. Only re-entry from the
completed checker exchanges the two roles. Edge tests are individual clauses;
no edge calls a SAT decider. The succinct input is the formula, not a list of
all the vertices. The orientation/odd-return classifications below are exact.
-/
namespace Mobius.SATSeam
open Complexity Complexity.SAT Mobius.Transport

abbrev Witness (f : CNF) := Fin (variableBound f) → Bool

def assign {f : CNF} (w : Witness f) (i : Nat) : Bool :=
  if h : i < variableBound f then w ⟨i, h⟩ else false

inductive Position (f : CNF) where
  | root
  | check (w : Witness f) (remaining : Fin (f.length + 1))

/-- A proof branch chooses a finite assignment, discharges the clause
obligations backwards in order, then plugs its output into the opposite port. -/
inductive Step (f : CNF) : SignedEdges (Position f) where
  | enter (w : Witness f) : Step f .root (.check w ⟨f.length, by omega⟩) false
  | discharge (w : Witness f) (i : Fin f.length)
      (ok : evalClause (assign w) f[i] = true) :
      Step f (.check w ⟨i.val + 1, by omega⟩) (.check w ⟨i.val, by omega⟩) false
  | close (w : Witness f) : Step f (.check w ⟨0, by omega⟩) .root true

def PrefixOK {f : CNF} (w : Witness f) (j : Nat) : Prop :=
  ∀ i : Fin f.length, i.val < j → evalClause (assign w) f[i] = true

theorem full_prefix {f : CNF} (w : Witness f) :
    PrefixOK w f.length ↔ evalCNF (assign w) f = true := by
  simp only [evalCNF, List.all_eq_true]
  constructor
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact h ⟨i, hi⟩ hi
  · intro h i _
    exact h _ (List.getElem_mem ..)

theorem prefix_step {f : CNF} {w : Witness f} (i : Fin f.length)
    (ok : evalClause (assign w) f[i] = true) :
    PrefixOK w (i.val + 1) ↔ PrefixOK w i.val := by
  constructor
  · exact fun h j hj => h j (by omega)
  · intro h j hj
    by_cases hij : j = i
    · simpa [hij] using ok
    · exact h j (by have : j.val ≠ i.val := fun e => hij (Fin.ext e); omega)

theorem witness_of_sat {f : CNF} (hs : Satisfiable f) :
    ∃ w : Witness f, PrefixOK w f.length := by
  obtain ⟨a, ha⟩ := hs
  let w : Witness f := fun i => a i
  refine ⟨w, (full_prefix w).2 ?_⟩
  rw [← ha]
  exact Complexity.ThreeSAT.evalCNF_agrees (Complexity.ThreeSAT.input_below_bound f)
    (fun i hi => by simp [assign, hi, w])

theorem discharge_all {f : CNF} (w : Witness f) (j : Nat) (hj : j ≤ f.length)
    (ok : PrefixOK w j) : Walk (Step f) (.check w ⟨j, by omega⟩) (.check w 0) false := by
  induction j with
  | zero => exact .nil _
  | succ j ih =>
    let i : Fin f.length := ⟨j, by omega⟩
    have finished := ih (by omega) (fun t ht => ok t (by omega))
    exact (Walk.single (Step.discharge w i (ok i (by dsimp [i]; omega)))).append finished

def OddReturn (f : CNF) := Walk (Step f) .root .root true

theorem odd_of_sat {f : CNF} (hs : Satisfiable f) : OddReturn f := by
  obtain ⟨w, hw⟩ := witness_of_sat hs
  exact ((Walk.single (Step.enter w)).append (discharge_all w _ (by omega) hw)).snoc
    (Step.close w)

theorem orientation_of_unsat {f : CNF} (hn : ¬ Satisfiable f) : Orientable (Step f) := by
  classical
  let side : Position f → Bool
    | .root => false
    | .check w j => decide (PrefixOK w j)
  refine ⟨side, ?_⟩
  intro v u d edge
  cases edge with
  | enter w =>
    have h : ¬ PrefixOK w f.length := fun q => hn ⟨assign w, (full_prefix w).1 q⟩
    simp [side, h]
  | discharge w i ok => simp [side, (prefix_step i ok)]
  | close w =>
    have hp : PrefixOK w 0 := fun i h => by omega
    simp [side, hp]

theorem odd_iff_sat (f : CNF) : OddReturn f ↔ Satisfiable f := by
  constructor
  · intro odd
    apply Classical.byContradiction
    intro hs
    exact oddLoop_forbids_orientation odd (orientation_of_unsat hs)
  · exact odd_of_sat

theorem orientable_iff_unsat (f : CNF) : Orientable (Step f) ↔ ¬ Satisfiable f :=
  ⟨fun h hs => oddLoop_forbids_orientation (odd_of_sat hs) h, orientation_of_unsat⟩

/-- Encoding is inherited verbatim from the upstream one-tape Cook–Levin
library. The same bytes describe a proof checker; malformed words are rejected. -/
def SeamLanguage (input : Complexity.Word) : Prop :=
  ∃ f, encode f = input ∧ IsThreeCNF f ∧ OddReturn f

theorem seam_eq_threeSAT : SeamLanguage = Complexity.SAT.ThreeSAT := by
  funext input
  apply propext
  simp only [SeamLanguage, Complexity.SAT.ThreeSAT, odd_iff_sat]

theorem seam_np_complete : NPComplete SeamLanguage :=
  seam_eq_threeSAT ▸ threeSAT_np_complete

end Mobius.SATSeam
