import Mobius.Bounded

/-! A ceiling on log-cardinality arguments using incompatible positive
examples at one input cut. No upper bound on actual machine steps follows. -/
namespace Mobius.CrossingCeiling

theorem one_cut {l r k : Nat} (p : Fin k → BitVec l) (s : Fin k → BitVec r)
    (yes : BitVec l → BitVec r → Prop) (good : ∀ i, yes (p i) (s i))
    (cross : ∀ i j, i ≠ j → ¬yes (p i) (s j) ∨ ¬yes (p j) (s i)) :
    k ≤ 2 ^ min l r := by
  have left := Mobius.Bounded.fin_size_le (fun i => (p i).toFin) (by
    intro i j eq
    by_cases same : i=j
    · exact same
    · have e : p i=p j := BitVec.eq_of_toFin_eq eq
      rcases cross i j same with h | h
      · exact False.elim (h (e ▸ good j))
      · exact False.elim (h (e ▸ good i)))
  have right := Mobius.Bounded.fin_size_le (fun i => (s i).toFin) (by
    intro i j eq
    by_cases same : i=j
    · exact same
    · have e : s i=s j := BitVec.eq_of_toFin_eq eq
      rcases cross i j same with h | h
      · exact False.elim (h (e ▸ good i))
      · exact False.elim (h (e ▸ good j)))
  by_cases rel : l≤r
  · simpa [Nat.min_eq_left rel] using left
  · simpa [Nat.min_eq_right (by omega : r≤l)] using right

def sumCutBits (n : Nat) := ((List.range (n+1)).map (fun i => min i (n-i))).sum

private theorem sum_inc (f : Nat → Nat) (xs : List Nat) :
    (xs.map (fun i => f i + 1)).sum = (xs.map f).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons a tail ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega

private theorem next_two (n : Nat) : sumCutBits (n+2) = sumCutBits n + n+1 := by
  unfold sumCutBits
  rw [List.range_succ (n := n+2)]
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,Nat.sub_self,Nat.min_zero,Nat.add_zero]
  rw [List.range_succ_eq_map (n := n+1)]
  simp only [List.map_cons, List.map_map,List.sum_cons,Nat.zero_min,Nat.zero_add]
  have eq : ((List.range (n+1)).map ((fun i => min i (n+2-i)) ∘ Nat.succ)) =
      (List.range (n+1)).map (fun i => min i (n-i) + 1) := by
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    simp only [Function.comp_apply]
    omega
  rw [eq,sum_inc,List.length_range]; omega

theorem total_ceiling : ∀ n : Nat, sumCutBits n = n*n/4
  | 0 => rfl
  | 1 => rfl
  | n+2 => by
    rw [next_two,total_ceiling n]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_two,Nat.two_mul]
    omega

end Mobius.CrossingCeiling
