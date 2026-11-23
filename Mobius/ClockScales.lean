import Std

/-!
# Why a subexponential clock leaves the polynomial seam open

The integer inequalities below avoid real logarithms and asymptotic notation.
For positive clocks, the subexponential condition means the exponent divided
by n tends to zero. No lower bound on any 3-SAT machine is assumed here.
-/

namespace Mobius.ClockScales

/-- For each fixed exponential rate 1/k, the clock is eventually at most
2^(n/k), expressed by taking kth powers on the integers. -/
def Subexponential (clock : Nat → Nat) : Prop :=
  ∀ k : Nat, ∃ cutoff : Nat, ∀ n ≥ cutoff, clock n ^ k ≤ 2 ^ n

def PolynomialBound (clock : Nat → Nat) : Prop :=
  ∃ c k cutoff : Nat, ∀ n ≥ cutoff, clock n ≤ c * (n + 1) ^ k

def Superpolynomial (clock : Nat → Nat) : Prop :=
  ∀ c k : Nat, ∃ cutoff : Nat, ∀ n ≥ cutoff, c * (n + 1) ^ k < clock n

def logSquareClock (n : Nat) : Nat := 2 ^ (n.log2 * n.log2)

private theorem shifted_cube_step (x : Nat) : (x + 11)^3 ≤ 2 * (x + 10)^3 := by
  calc
    _ ≤ (x+11)^3 + (x^3 + 27*x^2 + 237*x + 669) := Nat.le_add_right _ _
    _ = _ := by grind

private theorem cube_le_pow2 (s : Nat) (hs : 10 ≤ s) : s^3 ≤ 2^s := by
  have shifted (x : Nat) : (x + 10)^3 ≤ 2^(x+10) := by
    induction x with
    | zero => decide
    | succ x ih =>
      calc
        _ = (x+11)^3 := by congr 1 <;> omega
        _ ≤ 2*(x+10)^3 := shifted_cube_step x
        _ ≤ 2*2^(x+10) := Nat.mul_le_mul_left 2 ih
        _ = 2^(x+1+10) := by
          rw [show x+1+10 = x+10+1 by omega, Nat.pow_succ 2 (x+10), Nat.mul_comm]
  have r := shifted (s-10)
  rwa [Nat.sub_add_cancel hs] at r

private theorem cutoff_log {n d : Nat} (h : 2^d ≤ n) : d ≤ n.log2 := by
  apply (Nat.le_log2 (n := n) (by have := Nat.two_pow_pos d; omega)).mpr h

theorem logSquare_subexponential : Subexponential logSquareClock := by
  intro k
  refine ⟨2^(max 10 k), ?_⟩
  intro n hn
  let s := n.log2
  have h : max 10 k ≤ s := cutoff_log hn
  have ht : 10 ≤ s := Nat.le_trans (Nat.le_max_left _ _) h
  have hk : k ≤ s := Nat.le_trans (Nat.le_max_right _ _) h
  have hn0 : n ≠ 0 := by have := Nat.two_pow_pos (max 10 k); omega
  change (2^(s*s))^k ≤ 2^n
  rw [← Nat.pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  calc
    (s*s)*k ≤ (s*s)*s := Nat.mul_le_mul_left _ hk
    _ = s^3 := by grind
    _ ≤ 2^s := cube_le_pow2 s ht
    _ ≤ n := Nat.log2_self_le hn0

theorem logSquare_superpolynomial : Superpolynomial logSquareClock := by
  intro c k
  refine ⟨2^(c+k+2), ?_⟩
  intro n hn
  let s := n.log2
  have hs : c+k+2 ≤ s := cutoff_log hn
  have input : n+1 ≤ 2^(s+1) := Nat.lt_log2_self
  have const : c ≤ 2^c := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    c*(n+1)^k ≤ 2^c * (2^(s+1))^k := Nat.mul_le_mul const (Nat.pow_le_pow_left input k)
    _ = 2^(c+(s+1)*k) := by rw [Nat.pow_add 2 c ((s+1)*k), Nat.pow_mul 2 (s+1) k]
    _ < 2^(s*s) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < 2)
      calc
        c+(s+1)*k ≤ s*k + s := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ = s*(k+1) := by grind
        _ < s*s := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = logSquareClock n := rfl

theorem no_polynomial_bound {clock : Nat → Nat} (h : Superpolynomial clock) :
    ¬PolynomialBound clock := by
  rintro ⟨c, k, cutoff, upper⟩
  obtain ⟨cutoff', lower⟩ := h c k
  let n := max cutoff cutoff'
  exact Nat.not_lt_of_ge (upper n (Nat.le_max_left _ _)) (lower n (Nat.le_max_right _ _))

theorem subexponential_does_not_imply_polynomial :
    ¬ (∀ clock, Subexponential clock → PolynomialBound clock) := by
  intro claim
  exact no_polynomial_bound logSquare_superpolynomial (claim _ logSquare_subexponential)

/-- Every fixed positive exponential lower rate is eventually ruled out
by a subexponential upper clock. In particular, a seam forcing that rate
on infinitely many sizes cannot hold for this machine. -/
theorem no_fixed_exponential_rate {clock : Nat → Nat} (h : Subexponential clock) (k : Nat) :
    ∃ cutoff : Nat, ∀ n ≥ cutoff, clock n ^ k < 2 ^ n := by
  obtain ⟨cutoff, hcut⟩ := h (k+k)
  refine ⟨cutoff+1, ?_⟩
  intro n hn
  apply Nat.lt_of_not_ge
  intro bad
  have contra : 2^(n+n) ≤ 2^n := calc
    _ = 2^n * 2^n := Nat.pow_add _ _ _
    _ ≤ clock n ^ k * clock n ^ k := Nat.mul_le_mul bad bad
    _ = clock n ^ (k+k) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^n := hcut n (by omega)
  exact Nat.not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : n < n+n)) contra

end Mobius.ClockScales
