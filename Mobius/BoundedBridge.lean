import Mobius.Bounded
import Mobius.SATSeam
import Complexity.SATBounds

/-!
# The cut examples in the same 3-SAT language used by Cook–Levin

Data variables occupy 0,...,n−1; the two padding variables occupy n and n+1.
The final theorem is a one-pass state bound for the *serialized binary input*,
including the header. Input size in this unary-index encoding is calibrated
below. A streaming lower bound does not constrain unrestricted tape machines.
-/

namespace Mobius.BoundedBridge

open Complexity.SAT
open Mobius.Bounded (Var block)

def index {n : Nat} : Var n → Nat
  | .data i => i.val
  | .auxA => n
  | .auxB => n+1

def lit {n : Nat} (l : Bounded.Literal n) : Literal := ⟨index l.var, l.sign⟩

def clause {n : Nat} (c : Bounded.Clause n) : Clause := [lit c.left, lit c.middle, lit c.right]

def translate {n : Nat} (f : Bounded.Formula n) : CNF := f.map clause

def toWord {n : Nat} (f : Bounded.Formula n) : Word := encode (translate f)

theorem round_trip (f : Bounded.Formula n) : decode (toWord f) = some (translate f) := decode_encode _

theorem three (f : Bounded.Formula n) : IsThreeCNF (translate f) := by
  rintro _ member
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
  exact Nat.le_refl 3

def project (a : Assignment) (v : Var n) : Bool := a (index v)

def extend (a : Bounded.Assignment n) (i : Nat) : Bool :=
  if h : i < n then a (.data ⟨i, h⟩) else if i = n then a .auxA else a .auxB

theorem project_extend (a : Bounded.Assignment n) : project (extend a) = a := by
  funext v
  cases v with
  | data i => simp [project, extend, index, i.isLt]
  | auxA => simp [project, extend, index]
  | auxB => simp [project, extend, index, show ¬ n+1 < n by omega]

theorem eval_lit (a : Assignment) (l : Bounded.Literal n) :
    evalLiteral a (lit l) = true ↔ project a l.var = l.sign := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [lit, project, evalLiteral]

theorem eval_clause (a : Assignment) (c : Bounded.Clause n) :
    evalClause a (clause c) = true ↔ c.Holds (project a) := by
  simp [clause, Bounded.Clause.Holds, Bool.or_eq_true, eval_lit]

theorem eval_translate (a : Assignment) (f : Bounded.Formula n) :
    evalCNF a (translate f) = true ↔ Bounded.Satisfies (project a) f := by
  simp [translate, evalCNF, List.all_eq_true, Bounded.Satisfies, eval_clause]

theorem sat_translate (f : Bounded.Formula n) : Satisfiable (translate f) ↔ Bounded.Satisfiable f := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨project a, (eval_translate a f).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨extend a, (eval_translate _ f).2 (by simpa only [project_extend] using h)⟩

theorem ordinary_threeSAT (f : Bounded.Formula n) :
    ThreeSAT (toWord f) ↔ Bounded.Satisfiable f := by
  simp [toWord, three, sat_translate]

theorem odd_return_iff (f : Bounded.Formula n) :
    SATSeam.OddReturn (translate f) ↔ Bounded.Satisfiable f :=
  (SATSeam.odd_iff_sat _).trans (sat_translate _)

theorem gadget_word_iff (x y : BitVec n) :
    ThreeSAT (toWord (block x ++ block y)) ↔ x = y :=
  (ordinary_threeSAT _).trans (Bounded.sat_append_iff_eq _ _)

theorem gadget_odd_return_iff (x y : BitVec n) :
    SATSeam.OddReturn (translate (block x ++ block y)) ↔ x = y :=
  (odd_return_iff _).trans (Bounded.sat_append_iff_eq _ _)

theorem gadget_clause_count (x y : BitVec n) :
    (translate (block x ++ block y)).length = 8*n := by
  simp [translate, Bounded.block_length]
  omega

private theorem writeValues_append (enc : α → Word) (l r : List α) :
    writeValues enc (l ++ r) = writeValues enc l ++ writeValues enc r := by
  induction l with
  | nil => simp [writeValues]
  | cons a t ih => simp [writeValues, ih, List.append_assoc]

private def body (f : Bounded.Formula n) : Word := writeValues encodeClause (translate f)

private theorem body_append (a b : Bounded.Formula n) : body (a ++ b) = body a ++ body b := by
  simp [body, translate, writeValues_append]

def blockBody (x : BitVec n) : Word := body (block x)

/-- The full serializer writes the fixed clause count, then the independent
bodies, in order. In particular its length header leaks no information about x. -/
theorem gadget_split (x y : BitVec n) :
    toWord (block x ++ block y) = (writeNat (8*n) ++ blockBody x) ++ blockBody y := by
  unfold toWord encode writeList
  rw [gadget_clause_count]
  simp only [translate, List.map_append, writeValues_append, blockBody, body, List.append_assoc]

theorem serialized_one_pass_lower_bound (initial : Fin s) (step : Fin s → Bool → Fin s)
    (accept : Fin s → Bool)
    (correct : ∀ x y : BitVec n,
      accept ((toWord (block x ++ block y)).foldl step initial) = true ↔
        ThreeSAT (toWord (block x ++ block y))) :
    2^n ≤ s := by
  let send (x : BitVec n) := (writeNat (8*n) ++ blockBody x).foldl step initial
  let finish (q : Fin s) (y : BitVec n) := accept ((blockBody y).foldl step q)
  apply Bounded.state_lower_bound send finish
  intro x y
  have h := (correct x y).trans (ordinary_threeSAT _)
  simpa only [gadget_split, List.foldl_append, send, finish] using h

private theorem pin_length (i : Fin n) (bit : Bool) :
    (body (Bounded.pin i bit)).length = 4*i.val + (8*n + 42) + 2 := by
  simp only [body, translate, Bounded.pin, List.map_cons, List.map_nil, writeValues,
    List.length_append, List.length_nil, clause, Bounded.pinClause,
    Complexity.SATBounds.encodeClause_cons_length, Complexity.SATBounds.encodeClause_nil_length,
    lit, index]
  omega

private theorem sum_block_lengths {n : Nat} (k b : Nat) (parts : Fin k → Bounded.Formula n)
    (cost : ∀ i, (body (parts i)).length = 4*i.val + b + 2) :
    (body (List.ofFn parts).flatten).length = 2*k*k + b*k := by
  induction k generalizing b with
  | zero => simp [body, translate, writeValues]
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, body_append, List.length_append, cost]
    have tail := ih (b+4) (fun i => parts i.succ) (fun i => by
      rw [cost, Fin.val_succ]; omega)
    rw [tail]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, Nat.mul_succ, Nat.add_mul]
    omega

theorem block_body_length (x : BitVec n) :
    (blockBody x).length = 10*n*n + 42*n := by
  have cost := sum_block_lengths n (8*n+42)
    (fun i => Bounded.pin i (x.getLsbD i.val)) (fun i => pin_length i _)
  unfold blockBody block
  rw [cost, Nat.add_mul]
  simp only [Nat.mul_assoc]
  omega

/-- Exact number of *bits* under the upstream unary-index representation.
The clause count is linear in n; the input bit length is quadratic. -/
theorem gadget_word_length (x y : BitVec n) :
    (toWord (block x ++ block y)).length = 20*n*n + 92*n + 1 := by
  rw [gadget_split]
  simp only [List.length_append, Complexity.SATBounds.writeNat_length, block_body_length, Nat.mul_assoc]
  omega

end Mobius.BoundedBridge
