import Mobius.BoundedBridge

/-! An unbounded family of ordinary unary-index 3-CNFs and an entire
interval of input-bit boundaries where two diagonal inputs splice exactly. -/
namespace Mobius.CrossingLayout
open Complexity.SAT
open Mobius.Bounded (block pin)
open Mobius.BoundedBridge (toWord blockBody)

def wide (x : BitVec m) : BitVec (m+m) := x.setWidth (m+m)
def word (x y : BitVec m) : Word := toWord (block (wide x) ++ block (wide y))

theorem word_sat (x y : BitVec m) : ThreeSAT (word x y) ↔ x=y := by
  rw [word,BoundedBridge.gadget_word_iff]
  constructor
  · intro h
    have val := congrArg BitVec.toNat h
    apply BitVec.eq_of_toNat_eq
    simpa [wide,BitVec.toNat_setWidth_of_le (show m≤m+m by omega)] using val
  · rintro rfl; rfl

def inputLength (m : Nat) := 80*m*m + 184*m + 1
def firstCut (m : Nat) := 18*m*m + 58*m + 1
def width (m : Nat) := 22*m*m + 42*m

theorem word_length (x y : BitVec m) : (word x y).length = inputLength m := by
  rw [word,BoundedBridge.gadget_word_length]
  simp only [inputLength,Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  omega

private def body (f : Bounded.Formula n) := writeValues encodeClause (BoundedBridge.translate f)

private theorem write_append (enc : α → Word) (a b : List α) :
    writeValues enc (a++b) = writeValues enc a ++ writeValues enc b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [writeValues,ih,List.append_assoc]

private theorem body_append (a b : Bounded.Formula n) : body (a++b) = body a ++ body b := by
  simp [body,BoundedBridge.translate,write_append]

private theorem pin_size (i : Fin n) (bit : Bool) :
    (body (pin i bit)).length = 4*i.val + (8*n+42)+2 := by
  simp only [body,BoundedBridge.translate,pin,List.map_cons,List.map_nil,writeValues,
    List.length_append,List.length_nil,BoundedBridge.clause,Bounded.pinClause,
    Complexity.SATBounds.encodeClause_cons_length,Complexity.SATBounds.encodeClause_nil_length,
    BoundedBridge.lit,BoundedBridge.index]
  omega

private theorem sum_sizes {n : Nat} (k b : Nat) (parts : Fin k → Bounded.Formula n)
    (cost : ∀ i, (body (parts i)).length = 4*i.val + b + 2) :
    (body (List.ofFn parts).flatten).length = 2*k*k + b*k := by
  induction k generalizing b with
  | zero => simp [body,BoundedBridge.translate,writeValues]
  | succ k ih =>
    rw [List.ofFn_succ,List.flatten_cons,body_append,List.length_append,cost]
    have tail := ih (b+4) (fun i => parts i.succ) (fun i => by rw [cost,Fin.val_succ]; omega)
    rw [tail]
    simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_add,Nat.mul_succ,Nat.add_mul]
    omega

def bodyPrefix (x : BitVec m) : Word := body (List.ofFn (fun i : Fin m =>
  pin (i.castLE (Nat.le_add_right m m)) (x.getLsbD i.val))).flatten

def fixed (m : Nat) : Word := body (List.ofFn (fun i : Fin m => pin (i.natAdd m) false)).flatten

def headPart (x : BitVec m) := writeNat (8*(m+m)) ++ bodyPrefix x

theorem split_block (x : BitVec m) : blockBody (wide x) = bodyPrefix x ++ fixed m := by
  change body (List.ofFn (fun i : Fin (m+m) => pin i ((wide x).getLsbD i.val))).flatten = _
  rw [List.ofFn_add,List.flatten_append,body_append]
  simp [bodyPrefix,fixed,wide,BitVec.getLsbD_of_ge,
    show ∀ i : Fin m, i.val < m+m from fun i => by omega]

theorem split_word (x y : BitVec m) :
    word x y = headPart x ++ fixed m ++ blockBody (wide y) := by
  rw [word,BoundedBridge.gadget_split,split_block x]
  simp [headPart,List.append_assoc]

theorem head_length (x : BitVec m) : (headPart x).length = firstCut m := by
  have pref := sum_sizes m (8*(m+m)+42) (fun i : Fin m =>
    pin (i.castLE (Nat.le_add_right m m)) (x.getLsbD i.val)) (fun i => pin_size _ _)
  unfold headPart bodyPrefix
  rw [List.length_append,Complexity.SATBounds.writeNat_length,pref]
  simp only [firstCut,Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  omega

theorem fixed_length (m : Nat) : (fixed m).length = width m := by
  have raw := BoundedBridge.block_body_length (wide (0 : BitVec m))
  rw [split_block,List.length_append] at raw
  have pref := head_length (0 : BitVec m)
  rw [headPart,List.length_append,Complexity.SATBounds.writeNat_length] at pref
  simp only [firstCut,width,Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
  omega

/-- Offsets measure bit boundaries, including both ends of the shared block. -/
def leftPart (x : BitVec m) (j : Nat) := headPart x ++ (fixed m).take j
def rightPart (y : BitVec m) (j : Nat) := (fixed m).drop j ++ blockBody (wide y)

theorem joined (x y : BitVec m) (j : Nat) : leftPart x j ++ rightPart y j = word x y := by
  rw [split_word]
  simp only [leftPart,rightPart,List.append_assoc]
  rw [←List.append_assoc ((fixed m).take j),List.take_append_drop]

theorem cut_position (x : BitVec m) {j : Nat} (hj : j ≤ width m) :
    (leftPart x j).length = firstCut m + j := by
  simp [leftPart,head_length,fixed_length,Nat.min_eq_left hj]

/-- Both halves of the mixed input come from real accepted diagonal words. -/
theorem splice_words (x y : BitVec m) {j : Nat} (hj : j ≤ width m) :
    (word x x).take (firstCut m+j) ++ (word y y).drop (firstCut m+j) = word x y := by
  rw [← joined x x j,← joined y y j]
  have h₁ := cut_position x hj
  have h₂ := cut_position y hj
  conv => lhs; lhs; rw [← h₁,List.take_left]
  conv => lhs; rhs; rw [← h₂,List.drop_left]
  exact joined x y j

end Mobius.CrossingLayout
