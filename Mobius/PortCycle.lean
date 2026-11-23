import Mobius.OneInThree

/-! In a closed necklace of NOT gadgets, each station supplies the same
    defect bit to the two adjacent edges. Internal phase tables are chosen
    independently for each edge. The closing edge is included in the count. -/
namespace Mobius.PortCycle

/-- A NOT edge fails exactly when its two prescribed bits agree. -/
def equalEdge (a b : Bool) : Nat := if a = b then 1 else 0

/-- Edges on the sequence a, through, z. An empty intermediate list
    leaves the one direct edge from a to z. -/
def pathCost (a z : Bool) : List Bool → Nat
  | [] => equalEdge a z
  | b :: bs => equalEdge a b + pathCost b z bs

def cycleCost : List Bool → Nat
  | [] => 0
  | a :: bs => pathCost a a bs

private theorem path_parity (a z : Bool) (bs : List Bool) :
    (pathCost a z bs + (a ^^ z).toNat) % 2 = (bs.length + 1) % 2 := by
  induction bs generalizing a with
  | nil => cases a <;> cases z <;> decide
  | cons b bs ih =>
    have tail := ih b
    cases a <;> cases b <;> cases z <;>
      simp [pathCost,equalEdge] at tail ⊢ <;> omega

/-- For every labeling, the failure count and the ring length have the same parity. -/
theorem cycle_parity (vertices : List Bool) : cycleCost vertices % 2 = vertices.length % 2 := by
  cases vertices with
  | nil => rfl
  | cons a bs => simpa [cycleCost] using path_parity a a bs

theorem cycle_lower (vertices : List Bool) : vertices.length % 2 ≤ cycleCost vertices := by
  rw [← cycle_parity]
  exact Nat.mod_le _ _

/-- Alternating station labels, starting at a chosen value. -/
def alternating : Nat → Bool → List Bool
  | 0, _ => []
  | n+1, a => a :: alternating n (!a)

theorem alternating_length (n : Nat) (a : Bool) : (alternating n a).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [alternating,ih]

private def finish : Nat → Bool → Bool
  | 0,a => a
  | n+1,a => finish n (!a)

private theorem path_alternating (n : Nat) (a z : Bool) :
    pathCost a z (alternating n (!a)) = equalEdge (finish n a) z := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have no : equalEdge a (!a) = 0 := by cases a <;> decide
    simp only [alternating,pathCost,no,Nat.zero_add,finish,ih]

theorem alternating_attains (k : Nat) (first : Bool) : cycleCost (alternating k first) = k % 2 := by
  have parity := cycle_parity (alternating k first)
  rw [alternating_length] at parity
  have atMost : cycleCost (alternating k first) ≤ 1 := by
    cases k with
    | zero => exact Nat.zero_le 1
    | succ n =>
      change pathCost first first (alternating n (!first)) ≤ 1
      rw [path_alternating]
      unfold equalEdge
      split <;> decide
  omega

/-- In particular for every simple cycle k ≥ 3, the exact optimum is
    zero on an even cycle and one on an odd cycle. -/
theorem cycle_minimum (k : Nat) :
    (∀ vertices : List Bool, vertices.length = k → k % 2 ≤ cycleCost vertices) ∧
    (∃ vertices : List Bool, vertices.length = k ∧ cycleCost vertices = k % 2) :=
  ⟨fun vertices size => size ▸ cycle_lower vertices,
   alternating k false,alternating_length ..,alternating_attains ..⟩

open Mobius.OneInThree

def edgePorts (a b : Bool) : NotBoundary := ⟨literal a,literal b⟩

private theorem literal_defect (a : Bool) : (literal a).defect = a := by cases a <;> rfl

/-- Exact physical edge cost when both endpoint corner quadruples are
    pinned by their positive literals. The exhibited tables preserve every
    corner; different edges may use separate copies of these tables. -/
theorem edge_minimum (a b : Bool) :
    (∀ row col, readNot row col = edgePorts a b → equalEdge a b ≤ notInternalCost row col) ∧
    (readNot (notRow (edgePorts a b)) (notCol (edgePorts a b)) = edgePorts a b ∧
     notInternalCost (notRow (edgePorts a b)) (notCol (edgePorts a b)) = equalEdge a b) := by
  refine ⟨?_,not_extension_boundary _,?_⟩
  · intro row col read
    simpa only [edgePorts,literal_defect,equalEdge] using not_cost_lower (edgePorts a b) row col read
  · simpa only [edgePorts,literal_defect,equalEdge] using not_extension_cost (edgePorts a b)

end Mobius.PortCycle
