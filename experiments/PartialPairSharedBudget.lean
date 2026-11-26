import Std

/-! Exact arithmetic for the density and simultaneous-selection arguments in
docs/PartialPairSharedGates.md. The circuit and asymptotic arguments are in the note. -/
namespace PartialPairSharedBudget

/-- Number of interleavings of two lists of lengths a,b (Pascal's recurrence). -/
def ways : Nat → Nat → Nat
  | 0, _ => 1
  | _+1, 0 => 1
  | a+1, b+1 => ways a (b+1) + ways (a+1) b

private theorem stepRight (a b : Nat) : ways a b ≤ ways a (b+1) := by
  cases a with
  | zero => simp [ways.eq_1]
  | succ a => rw [ways.eq_3 a b]; omega

private theorem stepLeft (a b : Nat) : ways a b ≤ ways (a+1) b := by
  cases b with
  | zero => cases a <;> simp [ways.eq_1,ways.eq_2]
  | succ b => rw [ways.eq_3 a b]; omega

private theorem monoRight (a : Nat) {b c : Nat} (h : b ≤ c) : ways a b ≤ ways a c := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (stepRight ..)

private theorem diagonal (a : Nat) : 3*ways (a+1) (a+1) ≤ ways (a+2) (a+2) := by
  have outside := Nat.add_le_add (stepRight a (a+1)) (stepLeft (a+1) a)
  rw [← ways.eq_3 a a] at outside
  change ways (a+1) (a+1) ≤ ways a (a+2) + ways (a+2) a at outside
  rw [ways.eq_3 (a+1) (a+1), ways.eq_3 a (a+1), ways.eq_3 (a+1) a]
  change 3*ways (a+1) (a+1) ≤
    (ways a (a+2) + ways (a+1) (a+1)) + (ways (a+1) (a+1) + ways (a+2) a)
  omega

private theorem small11 : ways 1 1 = 2 := by rw [ways.eq_3 0 0, ways.eq_1, ways.eq_2]
private theorem small12 : ways 1 2 = 3 := by rw [ways.eq_3 0 1, ways.eq_1, small11]
private theorem small21 : ways 2 1 = 3 := by rw [ways.eq_3 1 0, small11, ways.eq_2]
private theorem small22 : ways 2 2 = 6 := by rw [ways.eq_3 1 1, small12, small21]

private theorem central (t : Nat) : 9^(t+2) ≤ 4^(t+2)*ways (t+2) (t+2) := by
  induction t with
  | zero => change 9^2 ≤ 4^2*ways 2 2; rw [small22]; decide
  | succ t ih =>
    have diag := Nat.mul_le_mul_left (4^(t+2)*4) (diagonal (t+1))
    calc
      9^(t+3) = 9^(t+2)*9 := Nat.pow_succ ..
      _ ≤ (4^(t+2)*ways (t+2) (t+2))*9 := Nat.mul_le_mul_right 9 ih
      _ ≤ (4^(t+2)*ways (t+2) (t+2))*12 := Nat.mul_le_mul_left _ (by decide)
      _ = (4^(t+2)*4)*(3*ways (t+2) (t+2)) := by
        rw [show 12=4*3 by decide]; ac_rfl
      _ ≤ (4^(t+2)*4)*ways (t+3) (t+3) := diag
      _ = _ := by rw [Nat.pow_succ 4 (t+2)]

/-- All positive ordered splits, clearing denominators of the 9/4 density estimate. -/
theorem density_split (a b : Nat) (ha : 0 < a) (hab : a ≤ b) :
    9^(a+b-1) ≤ ways a b * (9^(a-1)*4^b + 9^(b-1)*4^a) := by
  by_cases small : b = 1
  · have one : a=1 := by omega
    subst b; subst a; rw [small11]; decide
  have factor : 9^a ≤ 4^a * ways a b := by
    by_cases one : a=1
    · subst a
      have := Nat.mul_le_mul_left 4 (monoRight 1 (show 2 ≤ b by omega))
      exact Nat.le_trans (by rw [small12]; decide : 9^1 ≤ 4^1 * ways 1 2) this
    · obtain ⟨t,ht⟩ : ∃ t, a=t+2 := ⟨a-2,by omega⟩
      rw [ht] at hab ⊢
      exact Nat.le_trans (central t) (Nat.mul_le_mul_left _ (monoRight _ hab))
  calc
    9^(a+b-1) = 9^a * 9^(b-1) := by rw [← Nat.pow_add, show a+b-1=a+(b-1) by omega]
    _ ≤ (4^a*ways a b)*9^(b-1) := Nat.mul_le_mul_right _ factor
    _ = ways a b*(9^(b-1)*4^a) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_left ..)

/-- Bad choices cannot absorb more than their number times the size of a pool.
The retained score and the test for a good choice may be arbitrarily correlated. -/
theorem select_avoiding {α : Type} (ls : List α) (good : α → Bool)
    (score : α → Nat) (cap target : Nat) (bounded : ∀ x ∈ ls, score x ≤ cap)
    (mass : target * ls.length + cap * (ls.filter (fun x => !(good x))).length <
      (ls.map score).sum) :
    ∃ x ∈ ls, good x = true ∧ target < score x := by
  apply Classical.byContradiction
  intro absent
  suffices upper : (ls.map score).sum ≤
      target * ls.length + cap * (ls.filter (fun x => !(good x))).length by omega
  clear mass
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y hy => bounded y (List.mem_cons_of_mem _ hy))
      (fun ⟨y,hy,h⟩ => absent ⟨y,List.mem_cons_of_mem _ hy,h⟩)
    have bx := bounded x (List.mem_cons_self ..)
    cases hx : good x with
    | false => simp [hx,Nat.mul_succ] at * <;> omega
    | true =>
      have sx : score x ≤ target := Nat.le_of_not_gt
        (fun h => absent ⟨x,List.mem_cons_self ..,hx,h⟩)
      simp [hx,Nat.mul_succ] at * <;> omega

#print axioms density_split
#print axioms select_avoiding
end PartialPairSharedBudget
