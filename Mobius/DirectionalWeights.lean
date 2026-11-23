import Std

/-! Negative directional derivatives of product gates at nonnegative
integer base values introduce nonnegative integer scalar multipliers.
This invariant removes those multipliers on a singleton-bounded output.
It can be attached once to each wire in topological order, with unrestricted
reuse. Naturals suffice for the coefficient argument. -/
namespace Mobius.DirectionalWeights

abbrev Weights (n : Nat) := Fin n → Nat

def singleton (i : Fin n) : Weights n := fun j => if j = i then 1 else 0

structure Wire (n : Nat) where
  original : Weights n → Nat
  normalized : Weights n → Nat
  vanish : (∀ i, original (singleton i) = 0) → ∀ w, original w = 0
  exact : (∀ i, original (singleton i) ≤ 1) → ∀ w, normalized w = original w

def zero : Wire n where
  original := fun _ => 0
  normalized := fun _ => 0
  vanish := by simp
  exact := by simp

def input (j : Fin n) : Wire n where
  original := fun w => w j
  normalized := fun w => w j
  vanish := by intro h; have bad := h j; simp [singleton] at bad
  exact := by simp

def plus (a b : Wire n) : Wire n where
  original := fun w => a.original w + b.original w
  normalized := fun w => a.normalized w + b.normalized w
  vanish := by
    intro h w
    have ha i := h i
    have za := a.vanish (fun i => by have := ha i; omega) w
    have zb := b.vanish (fun i => by have := ha i; omega) w
    omega
  exact := by
    intro h w
    rw [a.exact (fun i => by have := h i; omega) w,
      b.exact (fun i => by have := h i; omega) w]

def maximum (a b : Wire n) : Wire n where
  original := fun w => max (a.original w) (b.original w)
  normalized := fun w => max (a.normalized w) (b.normalized w)
  vanish := by
    intro h w
    have left i := Nat.le_max_left (a.original (singleton i)) (b.original (singleton i))
    have right i := Nat.le_max_right (a.original (singleton i)) (b.original (singleton i))
    have za := a.vanish (fun i => by have := h i; have := left i; omega) w
    have zb := b.vanish (fun i => by have := h i; have := right i; omega) w
    simp [za,zb]
  exact := by
    intro h w
    rw [a.exact (fun i => Nat.le_trans (Nat.le_max_left ..) (h i)) w,
      b.exact (fun i => Nat.le_trans (Nat.le_max_right ..) (h i)) w]

private theorem heavy {k x : Nat} (h : (k+2)*x ≤ 1) : x=0 := by
  cases x with
  | zero => rfl
  | succ x => rw [Nat.mul_succ] at h; omega

/-- Zero multiplication is replaced by zero, every positive multiplication
by a wire. Singleton boundedness is only required at the final output. -/
def scale (k : Nat) (a : Wire n) : Wire n where
  original := fun w => k * a.original w
  normalized := if k = 0 then fun _ => 0 else a.normalized
  vanish := by
    intro h w
    by_cases hk : k = 0
    · simp [hk]
    · have z := a.vanish (fun i => (Nat.mul_eq_zero.mp (h i)).resolve_left hk) w
      simp [z]
  exact := by
    intro h w
    cases k with
    | zero => simp
    | succ k =>
      cases k with
      | zero =>
        have base (i : Fin n) : a.original (singleton i) ≤ 1 := by simpa using h i
        simpa using a.exact base w
      | succ k =>
        have small i : a.original (singleton i) = 0 := heavy (h i)
        have z := a.vanish small w
        have z' := a.exact (fun i => by rw [small i]; decide) w
        simp [z',z]

/-- Product rule at an integer base. After normalization it needs at most
one addition, plus wires and a shared zero. -/
def productGain (leftBase rightBase : Nat) (a b : Wire n) : Wire n :=
  plus (scale rightBase a) (scale leftBase b)

theorem singleton_bounded_output (a : Wire n)
    (h : ∀ i, a.original (singleton i) ≤ 1) :
    ∀ w, a.normalized w = a.original w := a.exact h

end Mobius.DirectionalWeights
