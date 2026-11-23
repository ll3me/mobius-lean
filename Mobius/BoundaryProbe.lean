import Mobius.SATSeam

/-! A four-port crossing test in the ordinary serialized 3-SAT language.
The first and fourth ports use variables 0–3, and the two middle ports
use variables 4–7. Each port contributes four ordered unit clauses. -/
namespace Mobius.BoundaryProbe

open Complexity.SAT

abbrev B := BitVec 4

private def unitClause (i : Nat) (value : Bool) : Clause := [⟨i,value⟩]

private def pins (base : Nat) (word : B) : CNF :=
  List.ofFn (fun i : Fin 4 => unitClause (base + i.val) (word.getLsbD i.val))

def probe (x y u v : B) : CNF :=
  pins 0 x ++ (pins 4 y ++ (pins 4 u ++ pins 0 v))

theorem probe_length (x y u v : B) : (probe x y u v).length = 16 := by
  simp [probe, pins]

theorem probe_variableBound (x y u v : B) : variableBound (probe x y u v) = 8 := by
  simp [probe, pins, unitClause, variableBound, clauseBound]

private theorem pins_unit (base : Nat) (word : B) (c : Clause) (mem : c ∈ pins base word) :
    c.length = 1 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
  rfl

theorem probe_unit (x y u v : B) (c : Clause) (mem : c ∈ probe x y u v) : c.length = 1 := by
  simp only [probe, List.mem_append] at mem
  rcases mem with h | h | h | h <;> exact pins_unit _ _ _ h

theorem probe_isThree (x y u v : B) : IsThreeCNF (probe x y u v) := by
  intro c hc
  rw [probe_unit _ _ _ _ _ hc]
  decide

private theorem unit_holds (a : Assignment) (i : Nat) (b : Bool) :
    evalClause a (unitClause i b) = true ↔ a i = b := by
  cases b <;> simp [unitClause, evalLiteral]

private theorem pins_hold (a : Assignment) (base : Nat) (word : B) :
    evalCNF a (pins base word) = true ↔
      ∀ i : Fin 4, a (base + i.val) = word.getLsbD i.val := by
  rw [evalCNF, List.all_eq_true]
  constructor
  · intro h i
    exact (unit_holds ..).mp (h _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · intro h c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact (unit_holds ..).mpr (h i)

private theorem same_bits (x y : B) (h : ∀ i : Fin 4, x.getLsbD i.val = y.getLsbD i.val) : x = y :=
  BitVec.eq_of_getLsbD_eq_iff.mpr (fun i hi => h ⟨i,hi⟩)

theorem probe_sat_iff (x y u v : B) : Satisfiable (probe x y u v) ↔ x = v ∧ y = u := by
  constructor
  · rintro ⟨a,valid⟩
    simp only [probe, evalCNF_append, Bool.and_eq_true, pins_hold] at valid
    obtain ⟨hx,hy,hu,hv⟩ := valid
    exact ⟨same_bits _ _ (fun i => (hx i).symm.trans (hv i)),
      same_bits _ _ (fun i => (hy i).symm.trans (hu i))⟩
  · rintro ⟨rfl,rfl⟩
    let a : Assignment := fun i => if i < 4 then x.getLsbD i else y.getLsbD (i-4)
    have low (i : Fin 4) : a (0+i.val) = x.getLsbD i.val := by simp [a, i.isLt]
    have high (i : Fin 4) : a (4+i.val) = y.getLsbD i.val := by simp [a]
    refine ⟨a, ?_⟩
    simp only [probe, evalCNF_append, Bool.and_eq_true, pins_hold]
    exact ⟨low,high,high,low⟩

theorem probe_threeSAT_iff (x y u v : B) :
    ThreeSAT (encode (probe x y u v)) ↔ x = v ∧ y = u := by
  simp only [ThreeSAT_encode_iff, probe_isThree, true_and, probe_sat_iff]

theorem probe_oddReturn_iff (x y u v : B) :
    SATSeam.OddReturn (probe x y u v) ↔ x = v ∧ y = u :=
  (SATSeam.odd_iff_sat _).trans (probe_sat_iff x y u v)

private theorem pins_injective (base : Nat) {x y : B} (h : pins base x = pins base y) : x = y := by
  apply same_bits
  intro i
  have entry := congrArg (fun f : CNF => f[i.val]?) h
  simp only [pins, List.getElem?_ofFn, dite_eq_left i.isLt, Option.some.injEq] at entry
  exact congrArg (fun c : Clause => (c.headD ⟨0,false⟩).positive) entry

theorem probe_word_injective {x y u v x' y' u' v' : B}
    (h : encode (probe x y u v) = encode (probe x' y' u' v')) :
    x = x' ∧ y = y' ∧ u = u' ∧ v = v' := by
  have syntaxEq := encode_injective _ _ h
  unfold probe at syntaxEq
  obtain ⟨hx,tail₁⟩ := List.append_inj syntaxEq (by simp [pins])
  obtain ⟨hy,tail₂⟩ := List.append_inj tail₁ (by simp [pins])
  obtain ⟨hu,hv⟩ := List.append_inj tail₂ (by simp [pins])
  exact ⟨pins_injective _ hx,pins_injective _ hy,pins_injective _ hu,pins_injective _ hv⟩

end Mobius.BoundaryProbe
