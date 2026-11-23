import Std

/-!
On a simultaneous eigenvector of Q commuting pair swaps, j minus signs give
eigenvalue (-1)^j for the full flip. This file verifies the integer restriction
of the OpenAI paper's Newton interpolant to consecutive weights. We also prove
a matching necessary difference order for *any* scalar repair on that window.
No vector-space dimension, tail estimate or global runtime is assumed here.
-/
namespace Mobius.ParityWindow

def difference (f : Nat → Int) (x : Nat) := f (x + 1) - f x

def differences : Nat → (Nat → Int) → (Nat → Int)
  | 0, f => f
  | d + 1, f => differences d (difference f)

def parity : Nat → Int
  | 0 => 1
  | n + 1 => -parity n

theorem parity_sq (n : Nat) : parity n * parity n = 1 := by
  induction n with
  | zero => decide
  | succ n ih => simpa only [parity, Int.neg_mul_neg] using ih

theorem parity_add (a b : Nat) : parity (a + b) = parity a * parity b := by
  induction b with
  | zero => simp [parity]
  | succ b ih => simp [parity, ih, Int.mul_neg]

theorem differences_scale (d : Nat) (c : Int) (f : Nat → Int) :
    differences d (fun x => c * f x) = fun x => c * differences d f x := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih =>
    unfold differences
    have h : difference (fun x => c * f x) = fun x => c * difference f x := by
      funext x; simp [difference, Int.mul_sub]
    rw [h, ih]

theorem differences_local (d : Nat) (f g : Nat → Int) (a : Nat)
    (agree : ∀ i, i ≤ d → f (a + i) = g (a + i)) :
    differences d f a = differences d g a := by
  induction d generalizing f g a with
  | zero => simpa [differences] using agree 0 (by omega)
  | succ d ih =>
    apply ih
    intro i hi
    unfold difference
    rw [show a+i+1 = a+(i+1) by omega, agree (i+1) (by omega), agree i (by omega)]

theorem differences_parity (d : Nat) :
    differences d parity = fun x => (-2 : Int)^d * parity x := by
  induction d with
  | zero => funext x; simp [differences]
  | succ d ih =>
    have h : difference parity = fun x => (-2 : Int) * parity x := by
      funext x; unfold difference; rw [parity]; omega
    rw [differences, h, differences_scale, ih]
    funext x
    simp only [Int.pow_succ]
    ac_rfl

/-- Pascal recurrence for sum_{j<width} (-2)^j choose(offset,j).
The input offset starts at the left end of the chosen weight window. -/
def newton : Nat → Nat → Int
  | 0, _ => 0
  | _ + 1, 0 => 1
  | w + 1, n + 1 => newton (w + 1) n - 2 * newton w n
termination_by w n => (n, w)

theorem newton_matches (n w : Nat) (inside : n < w) : newton w n = parity n := by
  induction n generalizing w with
  | zero => cases w <;> simp_all [newton, parity]
  | succ n ih =>
    cases w with
    | zero => omega
    | succ w =>
      rw [newton, ih (w+1) (by omega), ih w (by omega), parity]
      omega

theorem newton_degree (w : Nat) : differences w (newton w) = fun _ => 0 := by
  induction w with
  | zero => funext x; simp [differences, newton]
  | succ w ih =>
    have h : difference (newton (w+1)) = fun x => (-2:Int) * newton w x := by
      funext x; unfold difference; rw [newton]; omega
    rw [differences, h, differences_scale, ih]
    simp

theorem repaired_flip (a j w : Nat) (inside : j < w) :
    parity (a+j) * (parity a * newton w j) = 1 := by
  rw [newton_matches j w inside, ← parity_add, parity_sq]

private theorem negTwo_pow_ne_zero (d : Nat) : ((-2 : Int)^d) ≠ 0 := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [Int.pow_succ]
    exact Int.mul_ne_zero ih (by decide)

/-- The d-th difference reads only d+1 consecutive entries. A zero d-th
difference and a parity match on all d+1 entries contradict each other. -/
theorem window_lower_bound (d a : Nat) (f : Nat → Int)
    (low : differences d f a = 0) :
    ∃ i, i ≤ d ∧ f (a+i) ≠ parity (a+i) := by
  apply Classical.byContradiction
  intro noMismatch
  have h : ∀ i, i ≤ d → f (a+i) = parity (a+i) := by
    intro i hi
    exact Classical.byContradiction (fun bad => noMismatch ⟨i,hi,bad⟩)
  have eqn := differences_local d f parity a h
  rw [low, differences_parity] at eqn
  have hp : parity a ≠ 0 := by
    intro he; have hs := parity_sq a; simp [he] at hs
  exact Int.mul_ne_zero (negTwo_pow_ne_zero d) hp eqn.symm

end Mobius.ParityWindow
