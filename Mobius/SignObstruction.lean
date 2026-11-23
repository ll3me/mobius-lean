import Std
import Mobius.EightSquare

/-!
Trying to extend the two-face eight-square cancellation proof to a larger
alphabet. Each off-diagonal equal-XOR square requires odd sign transport.
The 15 squares below are an independently checkable rejection certificate
for *all* 2^256 sign assignments on a four-bit block. All constraints are
on the local factors of the contraction proof.
-/
namespace Mobius.SignObstruction

abbrev B := BitVec 4
abbrev Cell := B × B
abbrev Rectangle := B × B × B

def corners (r : Rectangle) : List Cell :=
  let (x,y,d) := r
  [(x,y), (x ^^^ d,y), (x,y ^^^ d), (x ^^^ d,y ^^^ d)]

def total {α : Type} (f : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => f x ^^ total f xs

theorem total_append {α : Type} (f : α → Bool) (a b : List α) :
    total f (a ++ b) = (total f a ^^ total f b) := by
  induction a with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih]

theorem total_perm {α : Type} (f : α → Bool) {xs ys : List α} (perm : xs.Perm ys) :
    total f xs = total f ys := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp [total, ih]
  | swap a b xs => exact Bool.xor_left_comm .. 
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem total_paired {α : Type} (f : α → Bool) (xs : List α) :
    total f (xs.flatMap fun x => [x,x]) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [total, ih]

/-- The phase equation equivalent to off-diagonal cancellation in the
signed two-face XOR ansatz, with no algebraicity requirement on phase. -/
def OddSquares {d : Nat} (phase : BitVec d → BitVec d → Bool) : Prop :=
  ∀ x y step, step ≠ 0 →
    (phase x y ^^ (phase (x ^^^ step) y ^^
    (phase x (y ^^^ step) ^^ phase (x ^^^ step) (y ^^^ step)))) = true

theorem eight_exists : ∃ phase : BitVec 3 → BitVec 3 → Bool, OddSquares phase := by
  refine ⟨Mobius.EightSquare.phase, ?_⟩
  unfold OddSquares
  decide

def certificate : List Rectangle :=
  [(0,3,9),(0,3,10),(0,9,5),(0,10,6),(2,3,8),
   (2,3,11),(2,8,4),(2,11,7),(5,6,12),(5,6,15),
   (5,8,2),(5,8,3),(6,10,1),(7,6,13),(7,6,14)]

def usedCells : List Cell := (certificate.flatMap corners).eraseDups

theorem cells_paired : (certificate.flatMap corners).Perm (usedCells.flatMap fun x => [x,x]) := by
  decide

theorem certificate_size : certificate.length = 15 ∧ usedCells.length = 30 := by decide

theorem sum_corners (f : Cell → Bool) (rs : List Rectangle)
    (odd : ∀ r ∈ rs, total f (corners r) = true) :
    total f (rs.flatMap corners) = total (fun _ => true) rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, total_append, odd r (by simp), ih (by
      intro s hs; exact odd s (by simp [hs]))]
    rfl

theorem sixteen_impossible (phase : B → B → Bool) : ¬ OddSquares phase := by
  intro odd
  let f : Cell → Bool := fun (x,y) => phase x y
  have valid : ∀ r ∈ certificate, r.2.2 ≠ 0 := by decide
  have oddTotal := sum_corners f certificate (by
    intro r hr
    obtain ⟨x,y,d⟩ := r
    simpa [corners, total, f] using odd x y d (valid _ hr))
  have evenTotal := (total_perm f cells_paired).trans (total_paired f usedCells)
  have one : total (fun _ => true) certificate = true := by decide
  rw [one, evenTotal] at oddTotal
  contradiction

theorem larger_impossible (n : Nat) (width : 4 ≤ n)
    (phase : BitVec n → BitVec n → Bool) : ¬ OddSquares phase := by
  intro h
  apply sixteen_impossible (fun x y => phase (x.setWidth n) (y.setWidth n))
  intro x y d hd
  have nonzero : d.setWidth n ≠ 0 := by
    intro hz
    have eqn := congrArg (BitVec.setWidth 4) hz
    apply hd
    simpa [BitVec.setWidth_setWidth_of_le _ width] using eqn
  simpa using h (x.setWidth n) (y.setWidth n) (d.setWidth n) nonzero

end Mobius.SignObstruction
