/-! Mixed Boolean differences over the integers, together with the enumeration
bound for digraphs with few edges in excess of their vertex count. A mask is
presented as its list of distinct open arcs when applying the lemmas. -/
namespace Mobius.HamiltonianSlice

/-- Include/exclude expansion on the remaining coordinates. At an empty
base, this is the coefficient of their squarefree monomial. -/
def difference (f : List α → Int) : List α → List α → Int
  | [], base => f base
  | e :: es, base => difference f es (base ++ [e]) - difference f es base

theorem difference_congr (f g : List α → Int) (cutoff : Nat)
    (agree : ∀ w, w.length ≤ cutoff → f w = g w) (es base : List α)
    (size : base.length + es.length ≤ cutoff) :
    difference f es base = difference g es base := by
  induction es generalizing base with
  | nil => exact agree base (by simpa using size)
  | cons e es ih =>
    simp only [List.length_cons] at size
    simp only [difference]
    rw [ih (base ++ [e]) (by simp; omega), ih base (by omega)]

private theorem zero_difference (es base : List α) :
    difference (fun _ => 0) es base = 0 := by
  induction es generalizing base with
  | nil => rfl
  | cons e es ih => simp [difference, ih]

/-- If a predicate vanishes on smaller masks, its coefficient at the first
possible weight is precisely its value on the full mask. -/
theorem first_layer (f : List α → Int) (m : Nat)
    (below : ∀ w, w.length < m → f w = 0) (es base : List α)
    (size : base.length + es.length = m) :
    difference f es base = f (base ++ es) := by
  induction es generalizing base with
  | nil => simp [difference]
  | cons e es ih =>
    simp only [List.length_cons] at size
    have smaller : difference f es base = 0 := by
      rw [difference_congr f (fun _ => 0) (base.length + es.length)
        (fun w h => below w (by omega)) es base (by omega), zero_difference]
    rw [difference, smaller, Int.sub_zero]
    simpa [List.append_assoc] using ih (base ++ [e]) (by simp; omega)

private theorem choices_at_vertex (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- Enumerating one outgoing arc at each vertex has at most one factor
of two per edge in excess of one outgoing edge per vertex. -/
theorem successor_count (degrees : List Nat) (positive : ∀ d ∈ degrees, 0 < d) :
    degrees.prod ≤ 2 ^ (degrees.map (fun d => d - 1)).sum := by
  induction degrees with
  | nil => decide
  | cons d ds ih =>
    have hd := positive d (by simp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    simp only [List.prod_cons, List.map_cons, List.sum_cons, Nat.add_one_sub_one, Nat.pow_add]
    exact Nat.mul_le_mul (choices_at_vertex k) (ih (fun a h => positive a (by simp [h])))

end Mobius.HamiltonianSlice
