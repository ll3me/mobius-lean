import Mobius.EightSquare

/-!
# The saving from grouped three-bit crossings

All rank upper bounds in this module are witnessed by explicit lists of
separated functions, interpreted over the integers. For t blocks and a fixed
number of column choices, the row/column witness lengths have product at most
2048^t. The trivial construction would use 64^t terms on each cut, for
product 4096^t. These counts concern one grouped tensor, not the execution
time of an unrestricted SAT algorithm.
-/

namespace Mobius.EightGroups

open Mobius.EightSquare

abbrev Pair := Block × Block

private def sumOn {α : Type} (xs : List α) (f : α → Int) : Int :=
  (xs.map f).sum

@[simp] private theorem sumOn_nil {α : Type} (f : α → Int) : sumOn [] f = 0 := rfl

@[simp] private theorem sumOn_cons {α : Type} (x : α) (xs : List α) (f : α → Int) :
    sumOn (x :: xs) f = f x + sumOn xs f := rfl

@[simp] private theorem sumOn_map {α β : Type} (xs : List α) (g : α → β) (f : β → Int) :
    sumOn (xs.map g) f = sumOn xs (fun a => f (g a)) := by
  simp [sumOn, List.map_map, Function.comp_def]

@[simp] private theorem sumOn_append {α : Type} (xs ys : List α) (f : α → Int) :
    sumOn (xs ++ ys) f = sumOn xs f + sumOn ys f := by simp [sumOn]

private theorem sumOn_flatMap {α β : Type} (xs : List α) (g : α → List β) (f : β → Int) :
    sumOn (xs.flatMap g) f = sumOn xs (fun x => sumOn (g x) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sumOn_mul {α : Type} (xs : List α) (f : α → Int) (c : Int) :
    sumOn xs (fun x => f x * c) = sumOn xs f * c := by
  induction xs <;> simp_all [Int.add_mul]

private theorem sumOn_mul_left {α : Type} (xs : List α) (f : α → Int) (c : Int) :
    sumOn xs (fun x => c * f x) = c * sumOn xs f := by
  simpa only [Int.mul_comm c] using sumOn_mul xs f c

/-- Each element of this list is one outer product, under the chosen cut. -/
abbrev Terms (α : Type) := List ((α → Int) × (α → Int))

def value {α : Type} (fs : Terms α) (left right : α) : Int :=
  sumOn fs (fun f => f.1 left * f.2 right)

private theorem pick (k : Block) (f : Block → Int) :
    sumOn blocks (fun j => if j = k then f j else 0) = f k := by
  have eq : (fun j => if j = k then f j else 0) =
      (fun j => if j = k then f k else 0) := by
    funext j
    split <;> simp_all
  rw [eq]
  exact sum8_single k (f k)

def small : Terms Pair :=
  blocks.map fun k =>
    let f := fun p : Pair => bond k p.1 p.2
    (f, f)

private theorem small_value (l r : Pair) :
    value small l r = rowPiece l.1 l.2 r.2 r.1 := by
  rw [row_factor_eight]
  simp only [small, value, sumOn_map]
  rfl

/-- Universal 64-row decomposition for an arbitrary kernel on two pairs. -/
def full (F : Pair → Pair → Int) : Terms Pair :=
  blocks.flatMap fun a => blocks.map fun b =>
    (fun l => if a = l.1 ∧ b = l.2 then 1 else 0, F (a,b))

private theorem full_value (F : Pair → Pair → Int) (l r : Pair) :
    value (full F) l r = F l r := by
  unfold value full
  rw [sumOn_flatMap]
  simp only [sumOn_map]
  have eq : (fun a => sumOn blocks (fun b =>
      (if a = l.1 ∧ b = l.2 then (1 : Int) else 0) * F (a,b) r)) =
      (fun a => if a = l.1 then F (a,l.2) r else 0) := by
    funext a
    by_cases ha : a = l.1
    · simp only [ha, true_and, ite_true]
      calc
        _ = sumOn blocks (fun b => if b = l.2 then F (l.1,b) r else 0) := by
          apply congrArg (sumOn blocks)
          funext b
          split <;> simp_all
        _ = _ := pick l.2 (fun b => F (l.1,b) r)
    · simp [ha, sumOn, blocks]
  rw [eq, pick]

/-- The cut is false for (x,y)‖(v,u) and true for (x,u)‖(v,y).
The choice is false for an R block, true for a C block. -/
def localKernel (cut choice : Bool) (l r : Pair) : Int :=
  if choice = cut then rowPiece l.1 l.2 r.2 r.1 else rowPiece l.1 r.2 l.2 r.1

def localFactors (cut choice : Bool) : Terms Pair :=
  if choice = cut then small else full (localKernel cut choice)

theorem local_value (cut choice : Bool) (l r : Pair) :
    value (localFactors cut choice) l r = localKernel cut choice l r := by
  by_cases h : choice = cut
  · simp [localFactors, localKernel, h, small_value]
  · simp [localFactors, h, full_value]

theorem local_count (cut choice : Bool) :
    (localFactors cut choice).length = if choice = cut then 8 else 64 := by
  by_cases h : choice = cut <;> simp [localFactors, h, small, full, blocks]

private def attach (p : (Pair → Int) × (Pair → Int))
    (q : (List Pair → Int) × (List Pair → Int)) :
    (List Pair → Int) × (List Pair → Int) :=
  (fun xs => match xs with | [] => 0 | x :: rest => p.1 x * q.1 rest,
   fun ys => match ys with | [] => 0 | y :: rest => p.2 y * q.2 rest)

def prependFactors (localFs : Terms Pair) (tails : Terms (List Pair)) : Terms (List Pair) :=
  localFs.flatMap fun f => tails.map (attach f)

private theorem prepend_count (fs : Terms Pair) (ts : Terms (List Pair)) :
    (prependFactors fs ts).length = fs.length * ts.length := by
  induction fs with
  | nil => simp [prependFactors]
  | cons f fs ih =>
    change ((ts.map (attach f)) ++ prependFactors fs ts).length = _
    simp [ih, Nat.add_mul, Nat.add_comm]

private theorem prepend_value (fs : Terms Pair) (ts : Terms (List Pair))
    (l r : Pair) (ls rs : List Pair) :
    value (prependFactors fs ts) (l :: ls) (r :: rs) =
    value fs l r * value ts ls rs := by
  unfold prependFactors value
  rw [sumOn_flatMap]
  simp only [sumOn_map, attach]
  have eq (f : (Pair → Int) × (Pair → Int)) :
      sumOn ts (fun g => f.1 l * g.1 ls * (f.2 r * g.2 rs)) =
      (f.1 l * f.2 r) * sumOn ts (fun g => g.1 ls * g.2 rs) := by
    rw [← sumOn_mul_left]
    apply congrArg (sumOn ts)
    funext g
    ac_rfl
  simp only [eq, sumOn_mul]


structure Tile where
  x : Block
  y : Block
  u : Block
  v : Block
  deriving DecidableEq, Repr

def Tile.left (w : Tile) (cut : Bool) : Pair :=
  if cut then (w.x, w.u) else (w.x, w.y)

def Tile.right (w : Tile) (cut : Bool) : Pair :=
  if cut then (w.v, w.y) else (w.v, w.u)

def Tile.piece (w : Tile) (choice : Bool) : Int :=
  if choice then columnPiece w.x w.y w.u w.v else rowPiece w.x w.y w.u w.v

private theorem view_correct (w : Tile) (cut choice : Bool) :
    localKernel cut choice (w.left cut) (w.right cut) = w.piece choice := by
  cases cut <;> cases choice <;> rfl

def maskEntry : List Bool → List Tile → Int
  | [], [] => 1
  | b :: bs, w :: ws => w.piece b * maskEntry bs ws
  | _, _ => 0

def maskFactors (cut : Bool) : List Bool → Terms (List Pair)
  | [] => [(fun _ => 1, fun _ => 1)]
  | b :: bs => prependFactors (localFactors cut b) (maskFactors cut bs)

theorem mask_value (cut : Bool) (m : List Bool) (ws : List Tile) (h : ws.length = m.length) :
    value (maskFactors cut m) (ws.map (·.left cut)) (ws.map (·.right cut)) =
    maskEntry m ws := by
  induction m generalizing ws with
  | nil =>
    cases ws with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [maskFactors, List.map_cons, prepend_value, local_value, view_correct, ih _ h, maskEntry]

theorem mask_count (cut : Bool) (m : List Bool) :
    (maskFactors cut m).length = 8 ^ m.count cut * 64 ^ m.count (!cut) := by
  induction m with
  | nil => simp [maskFactors]
  | cons b bs ih =>
    rw [maskFactors, prepend_count, local_count, ih]
    cases cut <;> cases b <;> simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

private theorem mask_has_length {n : Nat} {bs : List Bool} (h : bs ∈ masks n) :
    bs.length = n := by
  induction n generalizing bs with
  | zero => simpa [masks] using h
  | succ n ih =>
    simp [masks] at h
    rcases h with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ <;> simp [ih hm]

theorem masks_length (n : Nat) : (masks n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [masks, ih, Nat.pow_succ, Nat.mul_two]

private theorem count_both (bs : List Bool) : bs.count false + bs.count true = bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp <;> omega

def bucket (n k : Nat) : List (List Bool) :=
  (masks n).filter (fun bs => bs.count true == k)

def groupFactors (cut : Bool) (n k : Nat) : Terms (List Pair) :=
  (bucket n k).flatMap (maskFactors cut)

/-- Value of the weight-k part. Both cuts below compute this same tensor. -/
def groupEntry (ws : List Tile) (k : Nat) : Int :=
  sumOn (bucket ws.length k) (fun bs => maskEntry bs ws)

theorem group_value (cut : Bool) (ws : List Tile) (k : Nat) :
    value (groupFactors cut ws.length k) (ws.map (·.left cut)) (ws.map (·.right cut)) =
    groupEntry ws k := by
  unfold groupFactors value groupEntry
  rw [sumOn_flatMap]
  unfold sumOn
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  exact mask_value cut m ws (mask_has_length (List.mem_filter.mp hm).1).symm

private theorem flatMap_count {α β : Type} (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ q ∈ xs, (f q).length = n := fun q hq => h q (by simp [hq])
    simp [hx, ih ht, Nat.add_mul, Nat.add_comm]

def maskBudget (cut : Bool) (n k : Nat) : Nat :=
  if cut then 8 ^ k * 64 ^ (n-k) else 8 ^ (n-k) * 64 ^ k

theorem group_count_exact (cut : Bool) (n k : Nat) :
    (groupFactors cut n k).length = (bucket n k).length * maskBudget cut n k := by
  apply flatMap_count
  intro m hm
  obtain ⟨hall, hk⟩ := List.mem_filter.mp hm
  have ht : m.count true = k := beq_iff_eq.mp hk
  have hlen := mask_has_length hall
  have hf : m.count false = n-k := by have := count_both m; omega
  rw [mask_count]
  cases cut <;> simp [maskBudget, hf, ht]

theorem group_count_bound (cut : Bool) (n k : Nat) :
    (groupFactors cut n k).length ≤ 2 ^ n * maskBudget cut n k := by
  rw [group_count_exact]
  apply Nat.mul_le_mul_right
  rw [← masks_length]
  apply List.length_filter_le

/-- Product of the numbers of separated summands in the row and column
witnesses. Each of the n three-bit blocks saves a factor two relative to
the trivial 64-by-64 product. -/
theorem group_rank_product_bound (n k : Nat) (hk : k ≤ n) :
    (groupFactors false n k).length * (groupFactors true n k).length ≤ 2048 ^ n := by
  apply Nat.le_trans (Nat.mul_le_mul (group_count_bound false n k) (group_count_bound true n k))
  apply Nat.le_of_eq
  simp only [maskBudget, Bool.false_eq_true, ite_false, ite_true]
  calc
    _ = (2^n * 2^n) * (8^(n-k) * 8^k) * (64^k * 64^(n-k)) := by ac_rfl
    _ = ((2 * 2) * 8 * 64)^n := by
      rw [← Nat.pow_add (8 : Nat), ← Nat.pow_add (64 : Nat), Nat.sub_add_cancel hk, Nat.add_sub_of_le hk]
      simp only [Nat.mul_pow]
    _ = _ := rfl


private theorem sumOn_zero {α : Type} (xs : List α) :
    sumOn xs (fun _ => 0) = 0 := by induction xs <;> simp_all

private theorem sumOn_add {α : Type} (xs : List α) (f g : α → Int) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [sumOn_cons, ih]; ac_rfl

private theorem sumOn_exchange {α β : Type} (xs : List α) (ys : List β) (f : α → β → Int) :
    sumOn xs (fun x => sumOn ys (f x)) = sumOn ys (fun y => sumOn xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [sumOn_zero]
  | cons x xs ih =>
    simp only [sumOn_cons]
    rw [sumOn_add, ih]

private theorem sumOn_filter {α : Type} (xs : List α) (p : α → Bool) (f : α → Int) :
    sumOn (xs.filter p) f = sumOn xs (fun b => if p b then f b else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x <;> simp [hx, ih]

private theorem delta_sum (xs : List Nat) (k : Nat) (a : Int) (uniq : xs.Nodup) :
    sumOn xs (fun i => if k = i then a else 0) = if k ∈ xs then a else 0 := by
  induction xs with
  | nil => simp
  | cons j js ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp uniq
    simp only [sumOn_cons, ih tail, List.mem_cons]
    by_cases h : k = j <;> simp_all

def crossingProduct : List Tile → Int
  | [] => 1
  | w :: ws => crossing w.x w.y w.u w.v * crossingProduct ws

private theorem all_masks_sum (ws : List Tile) :
    sumOn (masks ws.length) (fun m => maskEntry m ws) =
      (2:Int)^ws.length * crossingProduct ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h : w.piece false + w.piece true = 2 * crossing w.x w.y w.u w.v :=
      row_add_column w.x w.y w.u w.v
    simp only [List.length_cons, masks, sumOn_append, sumOn_map, maskEntry, sumOn_mul_left]
    rw [← Int.add_mul, h, ih, Int.pow_succ, crossingProduct]
    ac_rfl

/-- The n+1 pieces, with their separated decompositions, reconstruct all
crossing equalities on 3n-bit legs, multiplied by the integer factor 2^n. -/
theorem reconstruct_groups (ws : List Tile) :
    ((List.range (ws.length+1)).map (groupEntry ws)).sum =
      (2:Int)^ws.length * crossingProduct ws := by
  change sumOn (List.range (ws.length+1)) (groupEntry ws) = _
  unfold groupEntry bucket
  simp only [sumOn_filter]
  rw [sumOn_exchange, ← all_masks_sum ws]
  unfold sumOn
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  have hlen := mask_has_length hm
  have hle : m.count true ≤ ws.length := by have := count_both m; omega
  have hmem : m.count true ∈ List.range (ws.length+1) := List.mem_range.mpr (by omega)
  simpa [sumOn, beq_iff_eq, hmem] using
    delta_sum (List.range (ws.length+1)) (m.count true) (maskEntry m ws) List.nodup_range

end Mobius.EightGroups
