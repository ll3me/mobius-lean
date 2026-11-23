import Mobius.CrossingLayout
import Init.Data.List.Nat.Pairwise
import Init.Data.Nat.Sqrt.Lemmas

/-! Counting variable-length state records and charging arbitrarily many
cuts to one common positive input. All sums and bounds are finite. -/
namespace Mobius.CrossingCharge

def sumOn (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

@[simp] theorem sum_nil (f : α → Nat) : sumOn [] f = 0 := rfl
@[simp] theorem sum_cons (x : α) (xs : List α) (f : α → Nat) :
    sumOn (x::xs) f = f x + sumOn xs f := by simp [sumOn]

theorem sum_const (xs : List α) (k : Nat) : sumOn xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]

theorem sum_add (xs : List α) (f g : α → Nat) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sum_cons,ih]; omega

theorem sum_mul (xs : List α) (c : Nat) (f : α → Nat) :
    sumOn xs (fun x => c*f x) = c*sumOn xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]

theorem sum_mono (xs : List α) (f g : α → Nat) (h : ∀ x∈xs, f x ≤ g x) :
    sumOn xs f ≤ sumOn xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun u hu => h u (by simp [hu])))

theorem sum_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumOn xs (fun x => sumOn ys (f x)) = sumOn ys (fun y => sumOn xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [sum_const]
  | cons x xs ih =>
    simp only [sum_cons,ih]
    rw [sum_add]

private theorem some_at_least (xs : List α) (nonempty : xs ≠ [])
    (f : α → Nat) (c : Nat) (large : xs.length*c ≤ sumOn xs f) : ∃ x∈xs, c ≤ f x := by
  apply Classical.byContradiction; intro none
  have small : ∀ x∈xs, f x + 1 ≤ c := by
    intro x hx
    have hbad : ¬c ≤ f x := fun h => none ⟨x,hx,h⟩
    omega
  have h := sum_mono xs (fun x => f x + 1) (fun _ => c) small
  rw [sum_add,sum_const,sum_const,Nat.mul_one] at h
  have := List.length_pos_iff.mpr nonempty
  omega

/-- All symbol lists of length strictly below k, including the empty list
only if k is positive. -/
def shortWords (s : Nat) : Nat → List (List (Fin s))
  | 0 => []
  | k+1 => [] :: (List.finRange s).flatMap (fun a => (shortWords s k).map (a :: ·))

private theorem short_mem (xs : List (Fin s)) (h : xs.length < k) : xs ∈ shortWords s k := by
  induction k generalizing xs with
  | zero => omega
  | succ k ih =>
    cases xs with
    | nil => simp [shortWords]
    | cons a xs =>
      have hx := ih xs (by simpa using h)
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨a,List.mem_finRange _,List.mem_map.mpr ⟨xs,hx,rfl⟩⟩)

private theorem flat_length (ys : List α) (f : α → List β) (n : Nat)
    (hn : ∀ y∈ys, (f y).length = n) : (ys.flatMap f).length = ys.length*n := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    rw [List.flatMap_cons,List.length_append,hn y (by simp),ih (fun x hx => hn _ (by simp [hx]))]
    simp [Nat.succ_mul,Nat.add_comm]

theorem short_count {s b : Nat} (hs : s ≤ 2^b) (hb : 0 < b) (k : Nat) :
    (shortWords s k).length < 2^(b*k) := by
  induction k with
  | zero => simp [shortWords]
  | succ k ih =>
    have q : 2 ≤ 2^b := Nat.one_lt_two_pow (by omega)
    rw [shortWords,List.length_cons,flat_length _ _ (shortWords s k).length
      (by intro x _; simp),List.length_finRange,Nat.mul_succ,Nat.pow_add]
    have cmp := Nat.mul_le_mul_right (shortWords s k).length hs
    have stronger := Nat.mul_le_mul_left (2^b)
      (show (shortWords s k).length + 1 ≤ 2^(b*k) by omega)
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm (2^b) (2^(b*k))] at stronger
    omega

private theorem sum_long (xs : List α) (v : α → Nat) (k : Nat) :
    (xs.filter (fun x => decide (k≤v x))).length*k ≤ sumOn xs v := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : k≤v x <;> simp [h,Nat.succ_mul] <;> omega

/-- Injective variable-length records force a large total at one cut,
even if every input has its own stopping time. -/
theorem one_cut {m s b k : Nat} (hm : 0<m) (hs : s≤2^b) (hb : 0<b)
    (budget : b*k ≤ m-1) (rec : Fin (2^m) → List (Fin s))
    (inj : ∀ i j, rec i = rec j → i=j) :
    (2^m)*k ≤ 2*sumOn (List.finRange (2^m)) (fun i => (rec i).length) := by
  let ids := List.finRange (2^m)
  let short := ids.filter fun i => decide ((rec i).length<k)
  have nd : (short.map rec).Nodup := List.Pairwise.map rec (fun i j ne h => ne (inj i j h))
    ((List.nodup_finRange _).filter _)
  have sub : short.map rec ⊆ shortWords s k := by
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact short_mem _ (of_decide_eq_true (List.mem_filter.mp hi).2)
  have card := nd.length_le_of_subset sub
  rw [List.length_map] at card
  have limit := Nat.pow_le_pow_right (show 0<2 by decide) budget
  have hsize := short_count hs hb k
  have two : 2^m = 2*2^(m-1) := by
    conv => lhs; rw [show m=m-1+1 by omega,Nat.pow_succ,Nat.mul_comm]
  let long := ids.filter fun i => decide (k≤(rec i).length)
  have partition : short.length + long.length = 2^m := by
    have split := List.length_eq_countP_add_countP (fun i : Fin (2^m) => decide ((rec i).length<k)) (l:=ids)
    simpa [short,long,ids,List.countP_eq_length_filter,Nat.not_lt] using split.symm
  have half : 2^m ≤ 2*long.length := by omega
  have bound := Nat.mul_le_mul_right k half
  have ready := sum_long ids (fun i => (rec i).length) k
  change long.length*k ≤ _ at ready
  rw [Nat.mul_assoc] at bound
  exact Nat.le_trans bound (Nat.mul_le_mul_left 2 ready)

/-- Exchange the two finite sums before extracting the expensive input.
The same input witnesses the combined charge of the whole cut family. -/
theorem same_input {m s b k : Nat} (hm : 0<m) (hs : s≤2^b) (hb : 0<b)
    (budget : b*k ≤ m-1) (cuts : List β)
    (rec : Fin (2^m) → β → List (Fin s)) (time : Fin (2^m) → Nat)
    (inj : ∀ c∈cuts, ∀ i j, rec i c = rec j c → i=j)
    (charge : ∀ i, sumOn cuts (fun c => (rec i c).length) ≤ time i) :
    ∃ i, cuts.length*k ≤ 2*time i := by
  let ids := List.finRange (2^m)
  let measure := fun (c : β) (i : Fin (2^m)) => (rec i c).length
  have single (c) (hc : c∈cuts) := one_cut hm hs hb budget (fun i => rec i c) (inj c hc)
  have add := sum_mono cuts (fun _ => 2^m*k) (fun c => 2*sumOn ids (measure c)) single
  rw [sum_const,sum_mul,sum_swap] at add
  have all := sum_mono ids (fun i => sumOn cuts (fun c => (rec i c).length)) time (fun i _ => charge i)
  have combined := Nat.le_trans add (Nat.mul_le_mul_left 2 all)
  have limit : ids.length*(cuts.length*k) ≤ sumOn ids (fun i => 2*time i) := by
    rw [sum_mul]
    simpa [ids,Nat.mul_left_comm,Nat.mul_assoc] using combined
  have pick := some_at_least ids (by
    intro nil
    have len := congrArg List.length nil
    simp [ids] at len)
    (fun i => 2*time i) (cuts.length*k) limit
  obtain ⟨i,_,hi⟩ := pick
  exact ⟨i,hi⟩


/-- Explicit natural-number form of the subquadratic lower bound. For every
m>b, the finite charge gives N floor(sqrt N) ≤ 884 b T. -/
theorem scale {m b T : Nat} (hb : 0<b) (hm : b<m)
    (charge : CrossingLayout.width m * ((m-1)/b) ≤ 2*T) :
    CrossingLayout.inputLength m * Nat.sqrt (CrossingLayout.inputLength m) ≤ 884*b*T := by
  let N := CrossingLayout.inputLength m
  let L := CrossingLayout.width m
  let k := (m-1)/b
  have hm1 : 1≤m := by omega
  have msq : m ≤ m*m := by simpa using Nat.mul_le_mul_left m hm1
  have bound : N ≤ 265*(m*m) := by
    unfold N CrossingLayout.inputLength; rw [Nat.mul_assoc]; omega
  have nL : N ≤ 13*L := by
    unfold N L CrossingLayout.inputLength CrossingLayout.width
    simp only [Nat.mul_add,Nat.mul_assoc]
    omega
  have root : Nat.sqrt N ≤ 17*m := by
    apply Nat.mul_self_le_mul_self_iff.mp
    apply Nat.le_trans (Nat.sqrt_le N)
    rw [Nat.mul_mul_mul_comm]
    exact Nat.le_trans bound (Nat.mul_le_mul_right _ (by decide : 265≤17*17))
  have kpos : 0<k := Nat.div_pos_iff.mpr ⟨hb,by omega⟩
  have floor := Nat.lt_mul_div_succ (m-1) hb
  change m-1 < b*(k+1) at floor
  have bk := Nat.mul_le_mul_left b (show 1≤k by omega)
  have mk : m ≤ 2*b*k := by
    rw [Nat.mul_add,Nat.mul_one] at floor
    rw [Nat.mul_one] at bk
    rw [Nat.mul_assoc]
    omega
  have step : N * Nat.sqrt N ≤ (13*L)*(17*(2*b*k)) :=
    Nat.mul_le_mul nL (Nat.le_trans root (Nat.mul_le_mul_left 17 mk))
  calc
    N * Nat.sqrt N ≤ (13*L)*(17*(2*b*k)) := step
    _ = (442*b)*(L*k) := by
      change (13*L)*(17*(2*b*k)) = ((13*17*2)*b)*(L*k)
      ac_rfl
    _ ≤ (442*b)*(2*T) := Nat.mul_le_mul_left _ charge
    _ = 884*b*T := by
      change (442*b)*(2*T) = (442*2)*b*T
      ac_rfl

end Mobius.CrossingCharge
