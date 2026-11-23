import Std

/-!
# A tensor crossing, entry by entry

This independent calculation checks the two-wire identity highlighted in
the ETH research artifact at https://github.com/anthropics/formal-math/tree/main/eth .
We use the unnormalized antisymmetric vector (|01⟩ − |10⟩). Its outer product
is twice the normalized singlet projector. The coefficient list expands
arbitrarily many crossings, sorted by the number of chosen antisymmetric
factors. Runtime and tensor-network rank bounds require additional arguments.
-/

namespace Mobius.EthSwap

/-- Four bits index one matrix entry for two incoming and two outgoing wires. -/
structure Crossing where
  leftIn : Bool
  rightIn : Bool
  leftOut : Bool
  rightOut : Bool
  deriving DecidableEq, Repr

def straight (w : Crossing) : Int :=
  if w.leftIn = w.leftOut ∧ w.rightIn = w.rightOut then 1 else 0

def swapped (w : Crossing) : Int :=
  if w.leftIn = w.rightOut ∧ w.rightIn = w.leftOut then 1 else 0

def alternating : Bool → Bool → Int
  | false, true => 1
  | true, false => -1
  | _, _ => 0

@[simp] theorem alternating_flip (a b : Bool) :
    alternating b a = -alternating a b := by
  cases a <;> cases b <;> decide

def singletOuter (w : Crossing) : Int :=
  alternating w.leftIn w.rightIn * alternating w.leftOut w.rightOut

/-- All sixteen integer entries, including the vanishing diagonal cancellation. -/
theorem swap_eq_straight_sub_outer (w : Crossing) :
    swapped w = straight w - singletOuter w := by
  obtain ⟨a, b, c, d⟩ := w
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Multiply a polynomial in ascending coefficient order by a + b·t.
The initial carry is zero. Recursing with b·x shifts that term to the
next degree, counting one additional antisymmetric factor. -/
def insertFactor (a b : Int) : Int → List Int → List Int
  | carry, [] => [carry]
  | carry, x :: xs => (carry + a * x) :: insertFactor a b (b * x) xs

theorem length_insertFactor (a b carry : Int) (xs : List Int) :
    (insertFactor a b carry xs).length = xs.length + 1 := by
  induction xs generalizing carry with
  | nil => rfl
  | cons x xs ih => simp [insertFactor, ih]

def evaluate (t : Int) : List Int → Int
  | [] => 0
  | x :: xs => x + t * evaluate t xs

theorem evaluate_insertFactor (a b t carry : Int) (xs : List Int) :
    evaluate t (insertFactor a b carry xs) = carry + (a + t * b) * evaluate t xs := by
  induction xs generalizing carry with
  | nil => simp [insertFactor, evaluate]
  | cons x xs ih =>
    simp only [insertFactor, evaluate, ih, Int.mul_add, Int.add_mul]
    ac_rfl

/-- Entry of each of the λ+1 grouped operators for the chosen input and
output bit strings. The degree k entry uses exactly k singlet factors,
including their signs from the expansion. -/
def grouped : List Crossing → List Int
  | [] => [1]
  | w :: ws => insertFactor (straight w) (-singletOuter w) 0 (grouped ws)

theorem grouped_length (ws : List Crossing) : (grouped ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [grouped, length_insertFactor, ih]

def tensorEntry (f : Crossing → Int) : List Crossing → Int
  | [] => 1
  | w :: ws => f w * tensorEntry f ws

/-- Generating-function identity for every integer parameter. Taking t=1
contracts all groups into the actual swapped tensor entry. -/
theorem grouped_polynomial (t : Int) (ws : List Crossing) :
    evaluate t (grouped ws) = tensorEntry (fun w => straight w - t * singletOuter w) ws := by
  induction ws with
  | nil => simp [grouped, tensorEntry, evaluate]
  | cons w ws ih =>
    simp only [grouped, tensorEntry, evaluate_insertFactor, Int.zero_add, ih, Int.mul_neg]
    rfl

theorem evaluate_one (xs : List Int) : evaluate 1 xs = xs.sum := by
  induction xs <;> simp_all [evaluate]

theorem grouped_reconstruction (ws : List Crossing) :
    (grouped ws).sum = tensorEntry swapped ws := by
  rw [← evaluate_one, grouped_polynomial]
  congr 1
  funext w
  simpa using (swap_eq_straight_sub_outer w).symm

/-- Two mixed pairs entering and leaving in the same order have zero
swapped entry. Their three nontrivial contributions cancel. -/
example : grouped [⟨false, true, false, true⟩, ⟨false, true, false, true⟩] =
    [1, -2, 1] := by decide

/-- Swapping both mixed pairs gives a unit entry entirely at degree two. -/
example : grouped [⟨false, true, true, false⟩, ⟨false, true, true, false⟩] =
    [0, 0, 1] := by decide

end Mobius.EthSwap
