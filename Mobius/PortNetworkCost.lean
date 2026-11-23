import Std

/-! Exact three-port clause cost, with positive literals. A one in b means a
failed port square, and a one in z means a true occurrence. Each failed
internal square costs two, each failed port costs one, and disagreement
between the two port vectors costs one per coordinate. -/
namespace Mobius.PortNetworkCost

abbrev Bits := BitVec 3

def weight (b : Bits) : Nat :=
  (b.getLsbD 0).toNat + (b.getLsbD 1).toNat + (b.getLsbD 2).toNat

def hamming (b z : Bits) : Nat := weight (b ^^^ z)

def deviation (k : Nat) : Nat := ((k : Int) - 1).natAbs

def localCost (h : Nat) (b z : Bits) : Nat := weight b + 2*h + hamming b z

private theorem no_internal (b z : Bits) (odd : weight b % 2 = 1) :
    1 + deviation (weight z) ≤ weight b + hamming b z := by
  revert b z odd; decide

private theorem one_internal (b z : Bits) :
    1 + deviation (weight z) ≤ weight b + 2 + hamming b z := by
  revert b z; decide

/-- Holds for every number h of internal failures, including zero. -/
theorem local_lower (h : Nat) (b z : Bits) (odd : (h + weight b) % 2 = 1) :
    1 + deviation (weight z) ≤ localCost h b z := by
  cases h with
  | zero => simpa [localCost] using no_internal b z (by simpa using odd)
  | succ h =>
    have base := one_internal b z
    unfold localCost
    omega

/-- Pick the first true occurrence. The all-false input picks coordinate zero. -/
def nearest (z : Bits) : Bits :=
  if z.getLsbD 0 then 1 else if z.getLsbD 1 then 2 else if z.getLsbD 2 then 4 else 1

theorem nearest_weight (z : Bits) : weight (nearest z) = 1 := by revert z; decide

theorem nearest_distance (z : Bits) : hamming (nearest z) z = deviation (weight z) := by
  revert z; decide

/-- This is a minimum: a lower bound for every one-hot b and an explicit
    one-hot b attaining it. -/
theorem one_hot_minimum (z : Bits) :
    (∀ b : Bits, weight b = 1 → 1 + deviation (weight z) ≤ 1 + hamming b z) ∧
    (∃ b : Bits, weight b = 1 ∧ 1 + hamming b z = 1 + deviation (weight z)) := by
  constructor
  · intro b one
    have low := no_internal b z (by rw [one])
    simpa only [one] using low
  · exact ⟨nearest z,nearest_weight z,congrArg (1 + ·) (nearest_distance z)⟩

/-- Optimizing over all odd local signatures gives the same value:
    h=0 and one failed port already attain the lower bound. -/
theorem sharp_local_cost (z : Bits) :
    (∀ (h : Nat) (b : Bits), (h + weight b) % 2 = 1 →
      1 + deviation (weight z) ≤ localCost h b z) ∧
    ((0 + weight (nearest z)) % 2 = 1 ∧
      localCost 0 (nearest z) z = 1 + deviation (weight z)) := by
  refine ⟨fun h b odd => local_lower h b z odd, ?_, ?_⟩
  · rw [nearest_weight]
  · simp only [localCost, nearest_weight, nearest_distance]

/-- On a cubic input every true variable covers three occurrences.
Charge one error per true variable and one per uncovered clause. -/
private theorem coverage_bound (hits : List Nat) : hits.length ≤ hits.sum + hits.count 0 := by
  induction hits with
  | nil => decide
  | cons k ks ih =>
    cases k with
    | zero => simp; omega
    | succ k => simp; omega

private theorem full_coverage (hits : List Nat) (pos : hits.count 0 = 0)
    (sum : hits.sum = hits.length) : ∀ k ∈ hits, k = 1 := by
  induction hits with
  | nil => simp
  | cons a as ih =>
    have tailBound := coverage_bound as
    cases a with
    | zero => simp at pos
    | succ a =>
      simp at pos
      simp only [List.sum_cons,List.length_cons] at sum
      have zero : a = 0 := by omega
      have tailSum : as.sum = as.length := by omega
      intro k hk
      rcases List.mem_cons.mp hk with rfl | mem
      · omega
      · exact ih pos tailSum k mem

theorem cubic_threshold (hits : List Nat) (trueVariables cost : Nat)
    (regular : hits.sum = 3 * trueVariables)
    (charged : trueVariables + hits.count 0 ≤ cost) (budget : cost ≤ hits.length / 3) :
    3 * trueVariables = hits.length ∧ hits.count 0 = 0 ∧ ∀ k ∈ hits, k = 1 := by
  have bound := coverage_bound hits
  have eq : 3 * trueVariables = hits.length := by omega
  have pos : hits.count 0 = 0 := by omega
  exact ⟨eq,pos,full_coverage hits pos (regular.trans eq)⟩

end Mobius.PortNetworkCost
