import Std

/-!
A fixed pattern of failed signed-XOR constraints fixes all cut ranks of
the two original terms and their correction. These diagrams are separate
from the symplectic crossing construction. The entrywise certificates give
the left and right diagonal signs explicitly, at every bit width.
-/
namespace Mobius.RankTradeGauge

abbrev Table (n : Nat) := BitVec n → BitVec n → Bool

def sig (b : Bool) : Int := if b then -1 else 1

def kernel {n} (p : Table n) (x y u v : BitVec n) : Int :=
  if x ^^^ y = v ^^^ u then sig (p x y) * sig (p v u) else 0

def physical {n} (r c : Table n) (x y u v : BitVec n) : Int :=
    kernel r x y u v + kernel c x u y v - 2 * (if x = v ∧ y = u then 1 else 0)

def own {n} (col : Bool) (r c : Table n) : Table n := if col then c else r

def cross {n} (col : Bool) (r c : Table n) : Table n := if col then r else c

def diag {n} (col : Bool) (r c : Table n) (k x : BitVec n) :=
    sig (own col r c x (x ^^^ k))

def far {n} (col : Bool) (r c : Table n) (k x v : BitVec n) :=
    sig (cross col r c x (v ^^^ k)) * sig (cross col r c v (x ^^^ k))

/-- The unsigned adjacency matrix of the failed tests in this block. -/
def adjacency {n} (col : Bool) (r c : Table n) (k x v : BitVec n) : Int :=
  if x ≠ v ∧ diag col r c k x * diag col r c k v = far col r c k x v then 1 else 0

/-- In either cut, E = D A D and the opposite main term =
D (2 I - 11ᵀ + 2 A) D, with the convention here using twice E. -/
theorem diagonal_conjugation {n} (col : Bool) (r c : Table n) (k x v : BitVec n) :
    let s := diag col r c k x
    let t := diag col r c k v
    let f := far col r c k x v
    let a := adjacency col r c k x v
    let i : Int := if x = v then 1 else 0
    s*t + f - 2*i = 2*s*a*t ∧ f = s*(2*i-1+2*a)*t := by
  by_cases he : x = v
  · subst v
    cases h : own col r c x (x ^^^ k) <;> cases j : cross col r c x (x ^^^ k) <;>
      simp [diag, far, adjacency, h, j, sig]
  · cases ha : own col r c x (x ^^^ k) <;> cases hb : own col r c v (v ^^^ k) <;>
      cases hc : cross col r c x (v ^^^ k) <;> cases hd : cross col r c v (x ^^^ k) <;>
        simp [diag, far, adjacency, ha, hb, hc, hd, he, sig]

/-- The physical residual, grouped by the equal XOR value of the two
index pairs, is exactly twice the sign-conjugated adjacency matrix. -/
theorem physical_block {n} (col : Bool) (r c : Table n) (k x v : BitVec n) :
    (if col then physical r c x (v ^^^ k) (x ^^^ k) v
     else physical r c x (x ^^^ k) (v ^^^ k) v) =
      2 * diag col r c k x * adjacency col r c k x v * diag col r c k v := by
  have h := (diagonal_conjugation col r c k x v).1
  have bonds : x ^^^ (v ^^^ k) = v ^^^ (x ^^^ k) := by ac_rfl
  have eqv : (x = v ∧ x ^^^ k = v ^^^ k) ↔ x = v := by
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl,rfl⟩
  have eqv' : (x = v ∧ v ^^^ k = x ^^^ k) ↔ x = v := by
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl,rfl⟩
  have base : x ^^^ (x ^^^ k) = v ^^^ (v ^^^ k) := by simp [← BitVec.xor_assoc]
  cases col
  · change physical r c x (x ^^^ k) (v ^^^ k) v = _
    simp only [physical, kernel, base, bonds, ite_true, eqv]
    exact h
  · change physical r c x (v ^^^ k) (x ^^^ k) v = _
    simp only [physical, kernel, base, bonds, ite_true, eqv']
    rw [Int.add_comm]
    exact h

/-- Both pairings and the physical crossing vanish between distinct keys. -/
theorem off_block {n} (r c : Table n) (x y u v : BitVec n) (h : x ^^^ y ≠ v ^^^ u) :
    physical r c x y u v = 0 := by
  have alt : x ^^^ u ≠ v ^^^ y := by
    intro he
    have eq := congrArg (· ^^^ (u ^^^ y)) he
    simp only [BitVec.xor_assoc] at eq
    have ry : y ^^^ (u ^^^ y) = u := by
      calc
        _ = (y ^^^ y) ^^^ u := by ac_rfl
        _ = _ := by simp
    rw [ry] at eq
    apply h
    simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using eq
  have nc : ¬(x = v ∧ y = u) := by rintro ⟨rfl,rfl⟩; exact h rfl
  simp [physical,kernel,h,alt,nc]

end Mobius.RankTradeGauge
