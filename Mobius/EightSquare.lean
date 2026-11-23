import Std

/-!
# Three-bit crossings from the eight-square identity

This independent finite-block proof implements the signed XOR construction
of section 4 of the upstream ETH paper. The phase is the parity of the
three-coordinate polynomial in its Appendix F. Finite kernel reduction
checks its sign rule, then integer algebra shows how a crossing splits into
two tensors. Each tensor has an explicit eight-term separated factorization
in its own pairing of the four legs.
-/

namespace Mobius.EightSquare

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

abbrev Block := BitVec 3

/-- The coefficient of each of the three bits of q is computed in GF(2). -/
def phase (p q : Block) : Bool :=
  let a := p.getLsbD 0
  let b := p.getLsbD 1
  let c := p.getLsbD 2
  let x := q.getLsbD 0
  let y := q.getLsbD 1
  let z := q.getLsbD 2
  (x && (a ^^ (b && c))) ^^
    (y && (a ^^ b ^^ (a && c))) ^^
    (z && (a ^^ b ^^ c ^^ (a && b)))

def sign (p q : Block) : Int := if phase p q then -1 else 1

theorem sign_sq (p q : Block) : sign p q * sign p q = 1 := by
  unfold sign
  cases phase p q <;> decide

/-- The orientation of the phase reverses when the opposite legs are
regrouped off the diagonal. -/
theorem phase_flip (x y u v : Block)
    (overlap : x ^^^ y = v ^^^ u) (offDiagonal : y ≠ u) :
    (phase x y ^^ phase v u) ≠ (phase x u ^^ phase v y) := by
  revert overlap offDiagonal x y u v
  decide

private theorem cancel_signs (a b c d : Bool)
    (h : (a ^^ b) ≠ (c ^^ d)) :
    (if a then (-1 : Int) else 1) * (if b then -1 else 1) +
    (if c then -1 else 1) * (if d then -1 else 1) = 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Row and column pairings of the four legs of the block. -/
def rowPiece (x y u v : Block) : Int :=
  if x ^^^ y = v ^^^ u then sign x y * sign v u else 0

def columnPiece (x y u v : Block) : Int := rowPiece x u y v

def crossing (x y u v : Block) : Int := if x = v ∧ y = u then 1 else 0

/-- Integer form of the paper's three-bit crossing identity; the scale
factor two avoids division. -/
theorem row_add_column (x y u v : Block) :
    rowPiece x y u v + columnPiece x y u v = 2 * crossing x y u v := by
  have parity : (x ^^^ y = v ^^^ u) ↔ (x ^^^ u = v ^^^ y) := by
    revert x y u v
    decide
  by_cases h : x ^^^ y = v ^^^ u
  · by_cases eq : y = u
    · have ex : x = v := by
        subst u
        simpa using congrArg (fun z => z ^^^ y) h
      subst v
      subst u
      simp [rowPiece, columnPiece, crossing, sign_sq]
    · have h' := parity.mp h
      have hc : ¬ (x = v ∧ y = u) := fun e => eq e.2
      simp only [columnPiece, rowPiece, crossing, ite_eq_left h, ite_eq_left h', ite_eq_right hc, Int.mul_zero]
      exact cancel_signs _ _ _ _ (phase_flip x y u v h eq)
  · have h' : ¬(x ^^^ u = v ^^^ y) := fun a => h (parity.mpr a)
    have hc : ¬ (x = v ∧ y = u) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp [rowPiece, columnPiece, crossing, h, h', hc]

/-- An explicit three-bit bond index for either separated factorization. -/
def bond (k p q : Block) : Int := if k = p ^^^ q then sign p q else 0

def blocks : List Block := [0, 1, 2, 3, 4, 5, 6, 7]

def sum8 (f : Block → Int) : Int := (blocks.map f).sum

theorem sum8_single (k : Block) (w : Int) :
    sum8 (fun j => if j = k then w else 0) = w := by
  have casesK : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
    revert k
    decide
  rcases casesK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sum8, blocks]

theorem row_factor_eight (x y u v : Block) :
    rowPiece x y u v = sum8 (fun k => bond k x y * bond k v u) := by
  have single : (fun k => bond k x y * bond k v u) =
      (fun k => if k = x ^^^ y then rowPiece x y u v else 0) := by
    funext k
    by_cases hk : k = x ^^^ y
    · subst k
      by_cases h : x ^^^ y = v ^^^ u <;> simp [bond, rowPiece, h]
    · simp [bond, hk]
  rw [single, sum8_single]

theorem column_factor_eight (x y u v : Block) :
    columnPiece x y u v = sum8 (fun k => bond k x u * bond k v y) :=
  row_factor_eight x u y v

/-- The two low-bond-width decompositions sum to the scaled equalities
connecting opposite legs. -/
theorem crossing_factorizations (x y u v : Block) :
    2 * crossing x y u v =
      sum8 (fun k => bond k x y * bond k v u) +
      sum8 (fun k => bond k x u * bond k v y) := by
  rw [← row_factor_eight, ← column_factor_eight, row_add_column]

end Mobius.EightSquare
