import Std

/-!
A symplectic three-part crossing on an eight-letter alphabet. The two cut
conventions make SWAP the identity matrix. The signed Pauli matrices give an
integral, orthogonal common eigenbasis. A degree shift by one encodes the
Laurent degrees -1,0,+1 as ordinary polynomial degrees 0,1,2.
-/
namespace Mobius.RankTrade

set_option linter.constructorNameAsVariable false

abbrev B := BitVec 3
abbrev Pair := B × B

def alphabet : List B := [0,1,2,3,4,5,6,7]
def labels : List Pair := alphabet.flatMap fun a => alphabet.map fun b => (a,b)

def bitSign (b : Bool) : Int := if b then -1 else 1
def ch (b x : B) : Int :=
  let w := b &&& x
  bitSign (w.getLsbD 0 ^^ w.getLsbD 1 ^^ w.getLsbD 2)

def basis (col : Bool) (lab w : Pair) : Int :=
  let x := if col then w.1 ^^^ 1 else w.1
  let s := if col then bitSign (w.1.getLsbD 0) else 1
  if x ^^^ w.2 = lab.1 then s * ch lab.2 x else 0

def J (x y : B) : Int := if x ^^^ y = 1 then bitSign (x.getLsbD 0) else 0

structure Tile where
  x : B
  y : B
  u : B
  v : B
  deriving Repr

def Tile.left (w : Tile) (col : Bool) := if col then (w.x,w.u) else (w.x,w.y)
def Tile.right (w : Tile) (col : Bool) := if col then (w.v,w.y) else (w.v,w.u)

def P (w : Tile) := J w.x w.y * J w.v w.u
def Q (w : Tile) : Int := if w.x = w.u ∧ w.v = w.y then 1 else 0
def crossing (w : Tile) : Int := if w.x = w.v ∧ w.y = w.u then 1 else 0
def E (w : Tile) := crossing w - P w - Q w

inductive Piece | q | e | p deriving DecidableEq, Repr, Inhabited

def entry : Piece → Tile → Int
  | .q => Q | .e => E | .p => P

def flip : Piece → Piece | .p => .q | .q => .p | .e => .e

def eigen (col : Bool) (l : Pair) (piece : Piece) : Int :=
  let p := if l = ((1,1) : Pair) then (8:Int) else 0
  let q := ch l.2 l.1
  match if col then flip piece else piece with
  | .p => p | .q => q | .e => 1-p-q

theorem crossing_sum (w : Tile) : Q w + E w + P w = crossing w := by
  unfold E; omega

def key (col : Bool) (w : Pair) : B := (if col then w.1 ^^^ 1 else w.1) ^^^ w.2

def kernelAt (col : Bool) (p : Piece) (w : Tile) (a : B) : Int :=
  (alphabet.map fun b =>
    basis col (a,b) (w.left col) * eigen col (a,b) p * basis col (a,b) (w.right col)).sum

set_option maxRecDepth 16384
set_option maxHeartbeats 0

-- Evaluate a single Fourier sector once: the other seven sectors vanish.
private theorem local_sector (col : Bool) (p : Piece) (x y u v : B) :
    kernelAt col p ⟨x,y,u,v⟩ (key col ((Tile.mk x y u v).left col)) =
      8 * entry p ⟨x,y,u,v⟩ := by
  by_cases h : u = x ^^^ y ^^^ v
  · subst u
    cases p <;> (revert col x y v; decide)
  · let w : Tile := ⟨x,y,u,v⟩
    have off : entry p w = 0 := by
      dsimp [w]; cases p <;> (revert x y u v h; decide)
    have hk : key col (w.right col) ≠ key col (w.left col) := by
      clear off; dsimp [w]; revert col x y u v h; decide
    have zero (b : B) : basis col (key col (w.left col), b) (w.right col) = 0 := by
      change (if key col (w.right col) = key col (w.left col) then _ else _) = 0
      rw [ite_eq_right hk]
    change kernelAt col p w (key col (w.left col)) = 8 * entry p w
    simp [kernelAt, zero, off, alphabet]

private theorem sector_off (col : Bool) (p : Piece) (w : Tile) (a : B)
    (h : a ≠ key col (w.left col)) : kernelAt col p w a = 0 := by
  have hz (b : B) : basis col (a,b) (w.left col) = 0 := by
    change (if key col (w.left col) = a then _ else _) = 0
    rw [ite_eq_right (Ne.symm h)]
  simp [kernelAt, hz, alphabet]

private theorem sector_sum (a : B) (v : Int) :
    (alphabet.map fun k => if k = a then v else 0).sum = v := by
  have hc : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
    revert a; decide
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [alphabet]

/-- Explicit, integral rank-one factorization of each piece on either cut. -/
theorem block_factorization (col : Bool) (p : Piece) (w : Tile) :
    (alphabet.map (kernelAt col p w)).sum = 8 * entry p w := by
  have hs (a : B) : kernelAt col p w a =
      if a = key col (w.left col) then 8 * entry p w else 0 := by
    split
    next h => subst a; obtain ⟨x,y,u,v⟩ := w; exact local_sector col p x y u v
    next h => exact sector_off col p w a h
  rw [show kernelAt col p w = _ from funext hs, sector_sum]

/-- Highest possible degree on a row eigenvector. Reading the column
polynomial backwards gives the same upper degree. -/
def cap (l : Pair) : Nat := if l = (1,1) then 2 else if ch l.2 l.1 = -1 then 1 else 0

def deg : Piece → Nat | .q => 0 | .e => 1 | .p => 2

theorem spectral_support (col : Bool) (l : Pair) (p : Piece) (nz : eigen col l p ≠ 0) :
    (if col then 2 - deg p else deg p) ≤ cap l := by
  obtain ⟨a,b⟩ := l
  cases p <;> (revert col a b nz; decide)

theorem multiplicities :
    (labels.filter (fun l => cap l == 0)).length = 36 ∧
    (labels.filter (fun l => cap l == 1)).length = 27 ∧
    (labels.filter (fun l => cap l == 2)).length = 1 := by decide

end Mobius.RankTrade

namespace Mobius.RankTrade

def sumN {α} (xs : List α) (f : α → Nat) := (xs.map f).sum

private theorem sumN_map {α β} (xs : List α) (g : α → β) (f : β → Nat) :
    sumN (xs.map g) f = sumN xs (fun x => f (g x)) := by
  simp [sumN, List.map_map, Function.comp_def]

private theorem sumN_flat {α β} (xs : List α) (g : α → List β) (f : β → Nat) :
    sumN (xs.flatMap g) f = sumN xs (fun x => sumN (g x) f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [sumN, List.sum_append]

private theorem sumN_mul {α} (xs : List α) (f : α → Nat) (v : Nat) :
    sumN xs (fun x => f x * v) = sumN xs f * v := by
  induction xs with
  | nil => simp [sumN]
  | cons x xs ih => simp_all [sumN, Nat.add_mul]

def words : Nat → List (List Pair)
  | 0 => [[]]
  | n+1 => labels.flatMap fun a => (words n).map (a :: ·)

def capacity : List Pair → Nat
  | [] => 0
  | a::as => cap a + capacity as

theorem block_weight : sumN labels (fun a => 6^cap a) = 234 := by decide

theorem weighted_words (n : Nat) :
    sumN (words n) (fun w => 6^capacity w) = 234^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [words, sumN_flat, sumN_map, capacity, Nat.pow_add]
    have factor (a : Pair) :
        sumN (words n) (fun x => 6^cap a * 6^capacity x) =
          6^cap a * 234^n := by
      rw [Nat.mul_comm]
      simpa only [Nat.mul_comm] using (sumN_mul (words n) (fun x => 6^capacity x) (6^cap a)).trans
        (congrArg (fun v => v * 6^cap a) ih)
    rw [show (fun a => sumN (words n) (fun x => 6^cap a * 6^capacity x)) = _ from funext factor,
        sumN_mul, block_weight, Nat.pow_succ, Nat.mul_comm]

def budget (n k : Nat) : Nat := ((words n).filter fun w => decide (k ≤ capacity w)).length

private theorem weighted_tail (ws : List (List Pair)) (k : Nat) :
    (ws.filter (fun w => decide (k ≤ capacity w))).length * 6^k ≤
      sumN ws (fun w => 6^capacity w) := by
  induction ws with
  | nil => simp [sumN]
  | cons w ws ih =>
    by_cases h : k ≤ capacity w
    · have hc : 6^k ≤ 6^capacity w := Nat.pow_le_pow_right (by decide) h
      simpa [List.filter_cons_of_pos, h, sumN, Nat.succ_mul, Nat.add_mul, Nat.add_comm] using Nat.add_le_add hc ih
    · simpa [h, sumN] using Nat.le_trans ih (Nat.le_add_left (sumN ws (fun w => 6^capacity w)) (6^capacity w))

theorem one_cut_budget (n k : Nat) : budget n k * 6^k ≤ 234^n := by
  rw [← weighted_words]
  exact weighted_tail _ _

/-- Row support requires capacity at least k; column support requires at
least 2n-k. This gives the all-length product of integer factor counts. -/
theorem rank_product_budget (n k : Nat) (h : k ≤ 2*n) :
    budget n k * budget n (2*n-k) ≤ 1521^n := by
  have bound := Nat.mul_le_mul (one_cut_budget n k) (one_cut_budget n (2*n-k))
  have ex : k + (2*n-k) = 2*n := by omega
  have lhs : (budget n k * 6^k) * (budget n (2*n-k) * 6^(2*n-k)) =
      (budget n k * budget n (2*n-k)) * 6^(2*n) := by
    calc
      _ = (budget n k * budget n (2*n-k)) * (6^k * 6^(2*n-k)) := by ac_rfl
      _ = _ := by rw [← Nat.pow_add, ex]
  have rhs : 234^n * 234^n = 1521^n * 6^(2*n) := by
    rw [← Nat.mul_pow, Nat.pow_mul, ← Nat.mul_pow]
  rw [lhs,rhs] at bound
  exact Nat.le_of_mul_le_mul_right bound (Nat.pow_pos (by decide))

end Mobius.RankTrade
