import Std
import Mobius.EightSquare

/-!
# Five-bit square tests with a partially affine phase

Rows and columns are indexed by the 32 vectors over the binary field.
A symmetric binary matrix with diagonal ones is considered. If the XOR
of the four rows indexed by any affine plane is an affine Boolean
function of the column index, every nonzero such XOR has weight at
least 16. Counting the 155 planes through a minimum-weight row proves
a lower bound of 128 ones, including the 32 diagonal entries.
-/
namespace Mobius.FiveRowAffine

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev V := BitVec 5
abbrev Matrix := V → V → Bool

def points : List V := List.ofFn (fun i : Fin 32 => BitVec.ofNat 5 i.val)
def dirs : List V := points.tail

def mass (xs : List α) (w : α → Nat) := (xs.map w).sum
def bit (b : Bool) : Nat := if b then 1 else 0
def rowWeight (b : Matrix) (i : V) := mass points (fun j => bit (b i j))
def weight (b : Matrix) := mass points (rowWeight b)

private theorem mass_add (xs : List α) (f g : α → Nat) :
    mass xs (fun x => f x + g x) = mass xs f + mass xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass, List.map_cons, List.sum_cons] at *
    omega

private theorem mass_scale (xs : List α) (c : Nat) (w : α → Nat) :
    mass xs (fun x => c * w x) = c * mass xs w := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simpa [mass, Nat.mul_add] using congrArg (c * w x + ·) ih

private theorem mass_const (xs : List α) (c : Nat) :
    mass xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    change c + mass xs (fun _ => c) = (xs.length + 1) * c
    rw [ih, Nat.add_mul]; omega

private theorem mass_mono (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : mass xs f ≤ mass xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun a ha => h a (by simp [ha])))

private theorem mass_perm {xs ys : List α} (p : xs.Perm ys) (f : α → Nat) :
    mass xs f = mass ys f := by
  induction p with
  | nil => rfl
  | cons x _ ih => exact congrArg (f x + ·) ih
  | swap x y xs => change f _ + (f _ + _) = f _ + (f _ + _); omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem mass_flat (xs : List α) (f : α → List β) (w : β → Nat) :
    mass (xs.flatMap f) w = mass xs (fun x => mass (f x) w) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [mass, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] using congrArg (mass (f x) w + ·) ih

private theorem points_complete (i : V) : i ∈ points := by revert i; decide
private theorem points_length : points.length = 32 := by decide
private theorem translate_perm (i : V) : (points.map (fun j => i ^^^ j)).Perm points := by
  revert i; decide
private theorem translate_mass (i : V) (w : V → Nat) :
    w i + mass dirs (fun d => w (i ^^^ d)) = mass points w := by
  have h := mass_perm (translate_perm i) w
  rw [show points.map (fun j => i ^^^ j) = i :: dirs.map (fun d => i ^^^ d) by
    have z : i ^^^ (0 : V) = i := BitVec.xor_zero
    conv => lhs; rw [show points = 0 :: dirs by rfl, List.map_cons, z]] at h
  simpa [mass, List.map_map, Function.comp_def] using h

/-- The three nonzero directions in each of the 155 planes through zero. -/
def planes : List (V × V) :=
  (dirs.flatMap (fun a => dirs.map (fun b => (a,b)))).filter
    (fun (a,b) => a < b && b < (a ^^^ b))

def planeDirs (p : V × V) : List V := [p.1,p.2,p.1 ^^^ p.2]
private theorem num_planes : planes.length = 155 := by decide

private theorem design :
    (planes.flatMap planeDirs).Perm (dirs.flatMap (fun d => List.replicate 15 d)) := by
  apply List.perm_iff_count.mpr
  decide

private theorem incidence (w : V → Nat) :
    mass planes (fun p => w p.1 + w p.2 + w (p.1 ^^^ p.2)) = 15 * mass dirs w := by
  have h := mass_perm design w
  rw [mass_flat, mass_flat] at h
  have lh (p : V × V) : mass (planeDirs p) w = w p.1 + w p.2 + w (p.1 ^^^ p.2) := by
    simp [mass, planeDirs, Nat.add_assoc]
  have rh (d : V) : mass (List.replicate 15 d) w = 15*w d := by
    simp only [mass, List.map_replicate, List.sum_replicate_nat]
  simp only [lh, rh] at h
  exact h.trans (mass_scale dirs 15 w)

private theorem rowWeight_pos (b : Matrix) (diag : ∀ i, b i i = true) (i : V) :
    1 ≤ rowWeight b i := by
  have part := translate_mass i (fun j => bit (b i j))
  rw [diag i] at part
  change 1 + _ = rowWeight b i at part
  omega

/-- A plane whose other three rows all vanish at column i has enough
    mass as soon as its four-row XOR is affine and its diagonal is one. -/
def PlaneBound (b : Matrix) : Prop := ∀ (i a e : V),
    b (i ^^^ a) i = false → b (i ^^^ e) i = false → b (i ^^^ (a ^^^ e)) i = false →
    16 ≤ rowWeight b i + rowWeight b (i ^^^ a) + rowWeight b (i ^^^ e) +
      rowWeight b (i ^^^ (a ^^^ e))

private theorem small_row (b : Matrix) (symm : ∀ i j, b i j = b j i)
    (diag : ∀ i, b i i = true) (localBound : PlaneBound b)
    (i : V) (minimal : ∀ j, rowWeight b i ≤ rowWeight b j) (small : rowWeight b i ≤ 3) :
    128 < weight b := by
  let w := rowWeight b
  let k := w i
  let c := 16 - 4*k
  let hit (d : V) := bit (b i (i ^^^ d))
  let neighbor (d : V) := w (i ^^^ d)
  let localMass (p : V × V) := k + (neighbor p.1 + neighbor p.2 + neighbor (p.1 ^^^ p.2))
  let hits (p : V × V) := hit p.1 + hit p.2 + hit (p.1 ^^^ p.2)
  have small' : k ≤ 3 := small
  have positive : 1 ≤ k := rowWeight_pos b diag i
  have each (p : V × V) : 16 ≤ localMass p + c * hits p := by
    by_cases h : hits p = 0
    · have zero := h
      simp only [hits, hit, Nat.add_eq_zero_iff, bit] at zero
      obtain ⟨⟨ha,hb⟩,he⟩ := zero
      have conv (j : V) (v : (if b i j then 1 else 0 : Nat) = 0) : b j i = false := by
        rw [symm]; cases hh : b i j <;> simp_all
      have H := localBound i p.1 p.2 (conv _ ha) (conv _ hb) (conv _ he)
      simpa [h, localMass, neighbor, k, w, Nat.add_assoc] using H
    · have low : 4*k ≤ localMass p := by
        have h₁ := minimal (i ^^^ p.1)
        have h₂ := minimal (i ^^^ p.2)
        have h₃ := minimal (i ^^^ (p.1 ^^^ p.2))
        change _ ≤ k + (rowWeight b _ + rowWeight b _ + rowWeight b _)
        change k ≤ _ at h₁ h₂ h₃
        omega
      have one : 1 ≤ hits p := by omega
      have prod := Nat.mul_le_mul_left c one
      dsimp only [c] at prod ⊢
      omega
  have sum := mass_mono planes (fun _ => 16) (fun p => localMass p + c * hits p) (fun p _ => each p)
  rw [mass_const, num_planes, mass_add, mass_scale] at sum
  have lm : mass planes localMass = 155*k + 15 * mass dirs neighbor := by
    change mass planes (fun p => k + _) = _
    rw [mass_add, mass_const, num_planes, incidence]
  have hs : mass planes hits = 15 * mass dirs hit := incidence hit
  rw [lm, hs] at sum
  have tw : k + mass dirs neighbor = weight b := translate_mass i w
  have th := translate_mass i (fun j => bit (b i j))
  rw [diag i] at th
  change 1 + mass dirs hit = k at th
  change 128 < mass points w
  change k + _ = mass points w at tw
  have opts : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases opts with hk | hk | hk <;> simp [c, hk] at sum <;> omega

private theorem exists_min (xs : List α) (w : α → Nat) (nonempty : xs ≠ []) :
    ∃ x ∈ xs, ∀ y ∈ xs, w x ≤ w y := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    by_cases empty : xs = []
    · subst xs; exact ⟨x,by simp,by simp⟩
    · obtain ⟨y,hy,hm⟩ := ih empty
      by_cases cmp : w x ≤ w y
      · exact ⟨x,by simp,fun z hz => by
          rcases List.mem_cons.mp hz with rfl | ht
          · exact Nat.le_refl _
          · exact Nat.le_trans cmp (hm z ht)⟩
      · exact ⟨y,by simp [hy],fun z hz => by
          rcases List.mem_cons.mp hz with rfl | ht
          · omega
          · exact hm z ht⟩

/-- The abstract design inequality for arbitrary binary matrices. -/
theorem matrix_lower (b : Matrix) (symm : ∀ i j, b i j = b j i)
    (diag : ∀ i, b i i = true) (localBound : PlaneBound b) : 128 ≤ weight b := by
  obtain ⟨i,_,h⟩ := exists_min points (rowWeight b) (by decide)
  have minimal j := h j (points_complete j)
  by_cases small : rowWeight b i ≤ 3
  · exact Nat.le_of_lt (small_row b symm diag localBound i minimal small)
  · have each (j : V) : 4 ≤ rowWeight b j := by have := minimal j; omega
    have all := mass_mono points (fun _ => 4) (rowWeight b) (fun j _ => each j)
    simpa [mass_const, points_length, weight] using all

end Mobius.FiveRowAffine

namespace Mobius.FiveRowAffine
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

local instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩

private theorem cancel_pair {p q : Bool} (u : Bool) (eqn : p = (q ^^ (u ^^ u))) : p = q := by
  simpa using eqn

def dot (a b : V) : Bool :=
  let c := a &&& b
  c.getLsbD 0 ^^ c.getLsbD 1 ^^ c.getLsbD 2 ^^ c.getLsbD 3 ^^ c.getLsbD 4

theorem dot_comm (a b : V) : dot a b = dot b a := by
  simp [dot, BitVec.and_comm]

theorem dot_split (a b c : V) : dot (a ^^^ b) c = (dot a c ^^ dot b c) := by
  simp only [dot, BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_right]
  ac_rfl

private theorem dot_split_right (a b c : V) : dot a (b ^^^ c) = (dot a b ^^ dot a c) := by
  rw [dot_comm a, dot_split, dot_comm b, dot_comm c]

/-- Arbitrary row slopes L and switching functions t. -/
def switched (L : V → V) (t : V → Bool) : Matrix :=
  fun i j => true ^^ (dot (L i) j ^^ (dot (L j) i ^^ (t i ^^ t j)))

private theorem cancel_bool (a b : Bool) : (a ^^ (a ^^ b)) = b := by cases a <;> cases b <;> decide

private theorem switch_sym (L : V → V) (t : V → Bool) (i j : V) :
    switched L t i j = switched L t j i := by unfold switched; simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, cancel_bool, Bool.xor_self, Bool.false_xor, Bool.xor_false]
private theorem switch_diag (L : V → V) (t : V → Bool) (i : V) :
    switched L t i i = true := by simp [switched]

private theorem affine_weight (a : V) (b : Bool) (i : V)
    (atI : (dot a i ^^ b) = true) : 16 ≤ mass points (fun x => bit (dot a x ^^ b)) := by
  have low : ∀ (v : V) (c : Bool), v ≠ 0 → 16 ≤ mass points (fun x => bit (dot v x ^^ c)) := by decide
  by_cases z : a = 0
  · subst a
    have zero (x : V) : dot 0 x = false := by simp [dot]
    rw [zero i] at atI
    have trueB : b = true := by cases b <;> simp_all
    subst b
    rw [show (fun x => bit (dot (0 : V) x ^^ true)) = (fun _ : V => 1) by
      funext x; rw [zero x]; rfl, mass_const, points_length]
    decide
  · exact low _ _ z

private theorem plane_score (L : V → V) (t : V → Bool) (i a e j : V) :
    (switched L t i j ^^ switched L t (i ^^^ a) j ^^ switched L t (i ^^^ e) j ^^
     switched L t (i ^^^ (a ^^^ e)) j) =
    (dot (L i ^^^ L (i ^^^ a) ^^^ L (i ^^^ e) ^^^ L (i ^^^ (a ^^^ e))) j ^^
     (t i ^^ t (i ^^^ a) ^^ t (i ^^^ e) ^^ t (i ^^^ (a ^^^ e)))) := by
  simp only [switched, dot_split, dot_split_right]
  generalize dot (L i) j = p
  generalize dot (L (i ^^^ a)) j = q
  generalize dot (L (i ^^^ e)) j = r
  generalize dot (L (i ^^^ (a ^^^ e))) j = s
  generalize dot (L j) i = x
  generalize dot (L j) a = y
  generalize dot (L j) e = z
  apply cancel_pair x
  apply cancel_pair x
  apply cancel_pair y
  apply cancel_pair z
  apply cancel_pair (t j)
  apply cancel_pair (t j)
  apply cancel_pair true
  apply cancel_pair true
  ac_rfl

private theorem four_xor_le (p q r s : Bool) :
    bit (p ^^ q ^^ r ^^ s) ≤ bit p + bit q + bit r + bit s := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

/-- For each first-coordinate plane, the XOR of its four rows is an
    affine Boolean function of the second-coordinate variable. -/
def AffinePlaneScores (b : Matrix) : Prop := ∀ i a e, ∃ slope value, ∀ j,
    (b i j ^^ b (i ^^^ a) j ^^ b (i ^^^ e) j ^^ b (i ^^^ (a ^^^ e)) j) =
      (dot slope j ^^ value)

theorem planeBound_of_affine (b : Matrix) (diag : ∀ i, b i i = true)
    (affine : AffinePlaneScores b) : PlaneBound b := by
  intro i a e h₁ h₂ h₃
  obtain ⟨slope,value,line⟩ := affine i a e
  have good := line i
  rw [h₁, h₂, h₃, diag] at good
  have bound := affine_weight slope value i good.symm
  have rowSum (j : V) : bit (dot slope j ^^ value) ≤ bit (b i j) + bit (b (i ^^^ a) j) +
      bit (b (i ^^^ e) j) + bit (b (i ^^^ (a ^^^ e)) j) := by
    rw [← line j]
    exact four_xor_le _ _ _ _
  have all := mass_mono points _ _ (fun j _ => rowSum j)
  simp only [mass_add] at all
  exact Nat.le_trans bound all

private theorem switch_bound (L : V → V) (t : V → Bool) : PlaneBound (switched L t) := by
  apply planeBound_of_affine _ (switch_diag L t)
  intro i a e
  exact ⟨_,_,plane_score L t i a e⟩

theorem switched_lower (L : V → V) (t : V → Bool) : 128 ≤ weight (switched L t) :=
  matrix_lower _ (switch_sym L t) (switch_diag L t) (switch_bound L t)

end Mobius.FiveRowAffine

namespace Mobius.FiveRowAffine

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def rectangleBad (f g : Matrix) (i y d : V) : Bool :=
  !(f i y ^^ f (i ^^^ d) (y ^^^ d) ^^ g i (y ^^^ d) ^^ g (i ^^^ d) y)

def anchoredFailures (f g : Matrix) : Nat :=
  mass points (fun i => mass dirs (fun d => mass points (fun y => bit (rectangleBad f g i y d))))

/-- r is the old column anchor plus the second row j. -/
def slice (f g : Matrix) (r : V) : Matrix := fun i j =>
  true ^^ (f i (r ^^^ j) ^^ (f j (r ^^^ i) ^^ (g i (r ^^^ i) ^^ g j (r ^^^ j))))

private theorem bit_cancel (a b : V) : a ^^^ (a ^^^ b) = b := by
  revert a b; decide
private theorem bit_swap_cancel (r i j : V) : r ^^^ j ^^^ (i ^^^ j) = r ^^^ i := by
  calc
    _ = (r ^^^ i) ^^^ (j ^^^ j) := by ac_rfl
    _ = _ := by simp

private theorem slice_diag (f g : Matrix) (r i : V) : slice f g r i i = true := by simp [slice]
theorem anchor_change (f g : Matrix) (r i j : V) :
    rectangleBad f g i (r ^^^ j) (i ^^^ j) = slice f g r i j := by
  have j_eq : (i ^^^ (i ^^^ j)) = j := bit_cancel i j
  have i_eq : (r ^^^ j ^^^ (i ^^^ j)) = r ^^^ i := bit_swap_cancel r i j
  simp only [rectangleBad, slice, j_eq, i_eq, Bool.true_xor, Bool.xor_assoc]

private theorem mass_comm (xs : List α) (ys : List β) (f : α → β → Nat) :
    mass xs (fun x => mass ys (f x)) = mass ys (fun y => mass xs (fun x => f x y)) := by
  induction xs with
  | nil => change 0 = mass ys (fun _ => 0); rw [mass_const, Nat.mul_zero]
  | cons x xs ih =>
    change mass ys (f x) + mass xs (fun z => mass ys (f z)) =
      mass ys (fun y => f x y + mass xs (fun z => f z y))
    rw [mass_add, ih]

private theorem mass_congr (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x = g x) :
    mass xs f = mass xs g := by
  rw [mass, mass, List.map_congr_left h]

private theorem shifted_mass (j : V) (w : V → Nat) :
    mass points (fun r => w (j ^^^ r)) = mass points w := by
  have tr := mass_perm (translate_perm j) w
  simpa only [mass, List.map_map, Function.comp_def] using tr

private theorem sum_slices (f g : Matrix) :
    mass points (fun r => weight (slice f g r)) = 1024 + anchoredFailures f g := by
  unfold weight rowWeight
  rw [mass_comm]
  have perRow (i : V) : mass points (fun r => mass points (fun j => bit (slice f g r i j))) =
      32 + mass dirs (fun d => mass points (fun y => bit (rectangleBad f g i y d))) := by
    rw [mass_comm points points (fun r j => bit (slice f g r i j))]
    let entry (j : V) := mass points (fun r => bit (slice f g r i j))
    have diag : entry i = 32 := by simp [entry, slice_diag, bit, mass_const, points_length]
    have reindex (j : V) :
        entry j = mass points (fun y => bit (rectangleBad f g i y (i ^^^ j))) := by
      let v (y : V) := bit (rectangleBad f g i y (i ^^^ j))
      have each (r : V) : bit (slice f g r i j) = v (j ^^^ r) := by
        unfold v
        rw [BitVec.xor_comm j r, anchor_change]
      exact (mass_congr points _ _ (fun r _ => each r)).trans (shifted_mass j v)
    have rest : mass dirs (fun d => entry (i ^^^ d)) =
        mass dirs (fun d => mass points (fun y => bit (rectangleBad f g i y d))) := by
      apply mass_congr dirs
      intro d _
      have h := reindex (i ^^^ d)
      have cancel : i ^^^ (i ^^^ d) = d := bit_cancel i d
      rw [cancel] at h
      exact h
    exact (translate_mass i entry).symm.trans (by rw [diag, rest])
  let err i := mass dirs (fun d => mass points (fun y => bit (rectangleBad f g i y d)))
  exact (mass_congr points _ _ (fun i _ => perRow i)).trans
    ((mass_add points (fun _ => 32) err).trans (congrArg (· + mass points err)
      ((mass_const points 32).trans (by decide))))

/-- One phase consists of arbitrary row slopes and arbitrary column slopes,
    together with arbitrary functions of x, y, and x XOR y. -/
def separableSlopes (L M : V → V) (h k v : V → Bool) : Matrix := fun x y =>
  dot (L x) y ^^ (dot (M y) x ^^ (h x ^^ (k y ^^ v (x ^^^ y))))

theorem slice_switched (L M : V → V) (h k v : V → Bool) (g : Matrix) (r : V) :
    slice (separableSlopes L M h k v) g r =
      switched (fun i => L i ^^^ M (r ^^^ i))
        (fun i => dot (L i) r ^^ (h i ^^ (k (r ^^^ i) ^^ g i (r ^^^ i)))) := by
  funext i j
  have eqv : i ^^^ (r ^^^ j) = j ^^^ (r ^^^ i) := by ac_rfl
  simp only [slice, separableSlopes, switched, dot_split, dot_split_right, eqv]
  letI : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
  letI : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
  apply cancel_pair (v (j ^^^ (r ^^^ i)))
  ac_rfl

/-- 3072 failures among 32·32·31 anchored tests; the other phase g is unrestricted. -/
theorem five_lower (L M : V → V) (h k v : V → Bool) (g : Matrix) :
    3072 ≤ anchoredFailures (separableSlopes L M h k v) g := by
  have all := mass_mono points (fun _ => 128)
    (fun r => weight (slice (separableSlopes L M h k v) g r))
    (fun r _ => by rw [slice_switched]; exact switched_lower _ _)
  rw [mass_const, points_length, sum_slices] at all
  omega

/-- The complete 404-dimensional slice class is characterized in the
    accompanying argument using the algebraic normal form of f. -/
theorem lower_of_affine_slices (f g : Matrix) (slices : ∀ r, AffinePlaneScores (slice f g r)) :
    3072 ≤ anchoredFailures f g := by
  have symmetric (r i j : V) : slice f g r i j = slice f g r j i := by unfold slice; simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, cancel_bool, Bool.xor_self, Bool.false_xor, Bool.xor_false]
  have all := mass_mono points (fun _ => 128) (fun r => weight (slice f g r))
    (fun r _ => matrix_lower _ (symmetric r) (slice_diag f g r)
      (planeBound_of_affine _ (slice_diag f g r) (slices r)))
  rw [mass_const, points_length, sum_slices] at all
  omega

def projection (x y : V) : Bool :=
  Mobius.EightSquare.phase (x.setWidth 3) (y.setWidth 3)

theorem projection_slice (r i j : V) :
    slice projection projection r i j = (i.setWidth 3 == j.setWidth 3) := by
  have small (s x y : BitVec 3) :
      (true ^^ (Mobius.EightSquare.phase x (s ^^^ y) ^^ (Mobius.EightSquare.phase y (s ^^^ x) ^^
        (Mobius.EightSquare.phase x (s ^^^ x) ^^ Mobius.EightSquare.phase y (s ^^^ y))))) = (x == y) := by
    revert s x y; decide
  simpa only [slice, projection, BitVec.setWidth_xor] using small (r.setWidth 3) (i.setWidth 3) (j.setWidth 3)

theorem projection_attains : anchoredFailures projection projection = 3072 := by
  have chart (r : V) : weight (slice projection projection r) = 128 := by
    have row (i : V) : rowWeight (slice projection projection r) i = 4 := by
      simp only [rowWeight, projection_slice]
      revert i
      decide
    have funEq : rowWeight (slice projection projection r) = (fun _ => 4) := funext row
    rw [weight, funEq, mass_const, points_length]
  have sum := sum_slices projection projection
  simp only [chart, mass_const, points_length] at sum
  omega

end Mobius.FiveRowAffine

namespace Mobius.FiveRowAffine

/-- The eight-square sign is itself an admissible first table. -/
def projectionSlope (i : V) : V :=
  let a := i.getLsbD 0
  let b := i.getLsbD 1
  let c := i.getLsbD 2
  (if a ^^ (b && c) then 1 else 0) ^^^
    (if a ^^ b ^^ (a && c) then 2 else 0) ^^^
    (if a ^^ b ^^ c ^^ (a && b) then 4 else 0)

theorem projection_representation :
    projection = separableSlopes projectionSlope (fun _ => 0)
      (fun _ => false) (fun _ => false) (fun _ => false) := by
  funext x y
  revert x y; decide

/-- Tightness witnessed inside the same class to which the lower bound applies. -/
theorem sharp_example :
    ∃ (L M : V → V) (h k v : V → Bool) (g : Matrix),
      anchoredFailures (separableSlopes L M h k v) g = 3072 := by
  refine ⟨projectionSlope,fun _ => 0,fun _ => false,fun _ => false,fun _ => false,projection,?_⟩
  rw [← projection_representation]
  exact projection_attains

theorem rows_of_equality (b : Matrix) (symm : ∀ i j, b i j = b j i)
    (diag : ∀ i, b i i = true) (localBound : PlaneBound b) (eqn : weight b = 128)
    (i : V) : rowWeight b i = 4 := by
  obtain ⟨u,_,minimal⟩ := exists_min points (rowWeight b) (by decide)
  have ge (j : V) := minimal j (points_complete j)
  have base : 4 ≤ rowWeight b u := by
    by_cases small : rowWeight b u ≤ 3
    · have high := small_row b symm diag localBound u ge small
      omega
    · omega
  have row_ge (j : V) : 4 ≤ rowWeight b j := Nat.le_trans base (ge j)
  have tail := mass_mono dirs (fun _ => 4) (fun d => rowWeight b (i ^^^ d)) (fun d _ => row_ge _)
  rw [mass_const, show dirs.length = 31 by decide] at tail
  have whole := translate_mass i (rowWeight b)
  change _ + _ = weight b at whole
  have low := row_ge i
  omega

end Mobius.FiveRowAffine
