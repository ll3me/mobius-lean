import Complexity.SATBounds

/-! The unary price of introducing variable i is at least i+1 bits.
Every yes-instance has a witness supported on a set of total price at
most the input length. Unused variables are fixed false. -/
namespace Mobius.UnaryWitness
open Complexity.SAT

def identifiers (f : CNF) : List Nat := f.flatMap (fun c => c.map Literal.var)
def price (xs : List Nat) := (xs.map (·+1)).sum

private theorem price_cons (i : Nat) (xs : List Nat) : price (i::xs) = i+1+price xs := rfl

private theorem clause_price (c : Clause) : price (c.map Literal.var) ≤ (encodeClause c).length := by
  induction c with
  | nil => decide
  | cons l c ih =>
    rw [List.map_cons,price_cons,Complexity.SATBounds.encodeClause_cons_length]
    omega

theorem formula_price (f : CNF) : price (identifiers f) ≤ (encode f).length := by
  induction f with
  | nil => decide
  | cons c f ih =>
    have cl := clause_price c
    rw [Complexity.SATBounds.encode_cons_length]
    change price (c.map Literal.var ++ identifiers f) ≤ _
    have sum (xs ys : List Nat) : price (xs++ys) = price xs+price ys := by
      simp [price]
    rw [sum]; omega

private def keep (a : Assignment) : List Nat → List Nat
  | [] => []
  | i::xs =>
    let rest := keep a xs
    if a i && !(rest.contains i) then i::rest else rest

private theorem keep_mem (a : Assignment) (xs : List Nat) (i : Nat) :
    i ∈ keep a xs ↔ i ∈ xs ∧ a i = true := by
  induction xs with
  | nil => simp [keep]
  | cons j xs ih =>
    by_cases ij : i = j
    · subst j
      cases a0 : a i <;> by_cases h : i ∈ keep a xs <;> simp_all [keep]
    · cases a0 : a j <;> by_cases h : j ∈ keep a xs <;> simp_all [keep]

private theorem keep_nodup (a : Assignment) (xs : List Nat) : (keep a xs).Nodup := by
  induction xs with
  | nil => simp [keep]
  | cons i xs ih =>
    by_cases h : i ∈ keep a xs <;> cases ha : a i <;> simp [keep,h,ha,ih]

private theorem keep_price (a : Assignment) (xs : List Nat) : price (keep a xs) ≤ price xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons i xs ih =>
    simp only [keep,price_cons]
    split
    · rw [price_cons]; omega
    · omega

theorem sparse_witness (f : CNF) (sat : Satisfiable f) :
    ∃ ids : List Nat, ids.Nodup ∧ price ids ≤ (encode f).length ∧
      evalCNF (fun i => ids.contains i) f = true := by
  obtain ⟨a,ok⟩ := sat
  let xs := identifiers f
  let ids := keep a xs
  refine ⟨ids,keep_nodup ..,Nat.le_trans (keep_price ..) (formula_price _),?_⟩
  have agrees (i : Nat) (hi : i ∈ xs) : ids.contains i = a i := by
    have h := keep_mem a xs i
    cases ha : a i <;> simp_all [ids]
  apply List.all_eq_true.mpr
  intro c hc
  have existsLit := List.any_eq_true.mp (List.all_eq_true.mp ok c hc)
  obtain ⟨l,hl,works⟩ := existsLit
  refine List.any_eq_true.mpr ⟨l,hl,?_⟩
  have used : l.var ∈ xs := List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨l,hl,rfl⟩⟩
  simpa only [evalLiteral,agrees l.var used] using works

end Mobius.UnaryWitness
