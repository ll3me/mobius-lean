import Mobius.AxisGlue

/-! Remove the two geometric port squares (four directed anchors) of each
designated axis from an ordinary four-bit board. The unweighted version
takes a gap hypothesis explicitly. The integral weighted version is unconditional. -/
namespace Mobius.AxisPortCost

open Mobius.SignObstruction (B Cell Rectangle directions shifts)
open Mobius.AxisGlue (Axis unit bits)
open Mobius.Rigidity (DirectionPattern)
abbrev Phase := B → B → Bool

def ports (p : B) := (List.finRange 4).filter (bits p)
def admissible (p : B) : Prop := 1 ≤ (ports p).length ∧ (ports p).length ≤ 3

def anchors (a : Axis) : List Rectangle :=
  let d := unit a
  [(0,0,d),(0,d,d),(d,0,d),(d,d,d)]

def dropped (p : B) := (ports p).flatMap anchors

def designated (p d : B) : Bool :=
  match d.toNat with
  | 1 => bits p 0 | 2 => bits p 1 | 4 => bits p 2 | 8 => bits p 3 | _ => false

def dropTest (p : B) (t : Rectangle) : Bool :=
  designated p t.2.2 && (t.1 == 0 || t.1 == t.2.2) && (t.2.1 == 0 || t.2.1 == t.2.2)

def tests := directions.flatMap fun d => shifts.map fun s => (s.1,s.2,d)

/-- Exact enumeration in the original directed measure. -/
theorem drop_filter : ∀ p : B, tests.filter (dropTest p) = dropped p := by decide +kernel

theorem dropped_size : ∀ p : B, (dropped p).Nodup ∧ (dropped p).length = 4*(ports p).length := by decide

/-- Companions reverse the two anchors simultaneously and describe the
same geometric square. The two remaining representatives are distinct. -/
def reverseAnchor (t : Rectangle) : Rectangle := (t.1^^^t.2.2,t.2.1^^^t.2.2,t.2.2)
theorem two_geometric : ∀ a : Axis, let d := unit a
    anchors a = [(0,0,d),(0,d,d),reverseAnchor (0,d,d),reverseAnchor (0,0,d)] ∧
    (0,0,d) ≠ (0,d,d) ∧ reverseAnchor (0,0,d) ≠ (0,d,d) := by decide

def retained (p : B) (r c : Phase) := (tests.filter fun t => !(dropTest p t)).countP (Rigidity.twoBad r c)
def removed (p : B) (r c : Phase) := (dropped p).countP (Rigidity.twoBad r c)

/-- Eight untouched copies and one copy with the specified tests removed. -/
def weighted (p : B) (r c : Phase) := 8*TwoPhases.failures r c + retained p r c

private theorem count_nat (xs : List α) (f : α → Bool) :
    xs.countP f = (xs.map (fun x => Rigidity.oneIf (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h,Rigidity.oneIf,ih,Nat.add_comm]

private theorem test_count (r c : Phase) : tests.countP (Rigidity.twoBad r c) = TwoPhases.failures r c := by
  rw [Rigidity.two_count]
  unfold tests
  rw [List.countP_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  simp only [Function.comp_apply,List.countP_map]
  rw [count_nat]
  rfl

theorem partition (p : B) (r c : Phase) :
    removed p r c + retained p r c = TwoPhases.failures r c := by
  rw [←test_count,removed,←drop_filter]
  exact (List.countP_eq_countP_filter_add tests (Rigidity.twoBad r c) (dropTest p)).symm

theorem weighted_sub (p : B) (r c : Phase) :
    weighted p r c = 9*TwoPhases.failures r c - removed p r c := by
  have := partition p r c
  unfold weighted
  omega

theorem removed_le (p : B) (small : admissible p) (r c : Phase) : removed p r c ≤ 12 := by
  have cap := List.countP_le_length (p:=Rigidity.twoBad r c) (l:=dropped p)
  rw [(dropped_size p).2] at cap
  have hs := small.2
  exact Nat.le_trans cap (Nat.mul_le_mul_left 4 hs)

private theorem nz_dropped : ∀ p : B, ∀ t∈dropped p, t.2.2 ≠ 0 := by decide

private theorem dir_count : ∀ p d : B,
    (dropped p).countP (fun t => t.2.2 == d) = if designated p d then 4 else 0 := by decide +kernel

theorem removed_pattern {p d : B} {r c : Phase} (pat : DirectionPattern r c d) :
    removed p r c = if designated p d then 4 else 0 := by
  rw [←dir_count]
  apply List.countP_congr
  intro t ht
  obtain ⟨x,y,e⟩ := t
  change !(TwoPhases.score r c (x,y,e)) = true ↔ (e == d)=true
  rw [pat.2 _ _ _ (nz_dropped p _ ht)]
  by_cases he : e=d <;> simp [he]

theorem retained_pattern {p d : B} {r c : Phase} (pat : DirectionPattern r c d) :
    retained p r c = if designated p d then 252 else 256 := by
  have hp := partition p r c
  rw [removed_pattern pat,Rigidity.optimal_of_direction pat] at hp
  cases h : designated p d <;> simp [h] at hp ⊢ <;> omega

theorem weighted_pattern {p d : B} {r c : Phase} (pat : DirectionPattern r c d) :
    weighted p r c = if designated p d then 2300 else 2304 := by
  rw [weighted,Rigidity.optimal_of_direction pat,retained_pattern pat]
  cases designated p d <;> decide

/-- The external second-weight hypothesis is visible only on unweighted
statements, and is never an axiom of this module. -/
def Gap282 : Prop := ∀ r c : Phase, TwoPhases.failures r c ≠ 256 → 282 ≤ TwoPhases.failures r c

theorem nonoptimal_retained (gap : Gap282) (p : B) (small : admissible p) (r c : Phase)
    (off : TwoPhases.failures r c≠256) : 270 ≤ retained p r c := by
  have hp := partition p r c
  have hr := removed_le p small r c
  have fg := gap r c off
  omega

theorem nonoptimal_weighted (p : B) (small : admissible p) (r c : Phase)
    (off : TwoPhases.failures r c≠256) : 2301 ≤ weighted p r c := by
  have hp := partition p r c
  have hr := removed_le p small r c
  have fg := TwoPhases.failures_lower r c
  unfold weighted
  omega

def Picked (p : B) (r c : Phase) := ∃ a : Axis, bits p a=true ∧ DirectionPattern r c (unit a)

private theorem chosen : ∀ p d : B, designated p d=true ↔ ∃ a : Axis, bits p a=true ∧ d=unit a := by decide
private theorem designated_unit : ∀ p a, designated p (unit a) = bits p a := by decide

theorem retained_local (gap : Gap282) (p : B) (small : admissible p) (r c : Phase) :
    252 ≤ retained p r c ∧ (retained p r c = 252 ↔ Picked p r c) := by
  by_cases opt : TwoPhases.failures r c=256
  · obtain ⟨d,pat,unique⟩ := Rigidity.optimal_direction _ _ opt
    rw [retained_pattern pat]
    constructor
    · cases designated p d <;> decide
    · constructor
      · intro hit
        have hd : designated p d=true := by cases h : designated p d <;> simp_all
        obtain ⟨a,ha,rfl⟩ := (chosen p d).mp hd
        exact ⟨a,ha,pat⟩
      · rintro ⟨a,ha,other⟩
        rw [← unique (unit a) other,designated_unit,ha]; rfl
  · have above := nonoptimal_retained gap p small r c opt
    refine ⟨by omega,⟨fun eq => False.elim (by omega),?_⟩⟩
    rintro ⟨a,_,pat⟩
    exact False.elim (opt (Rigidity.optimal_of_direction pat))

theorem weighted_local (p : B) (small : admissible p) (r c : Phase) :
    2300 ≤ weighted p r c ∧ (weighted p r c = 2300 ↔ Picked p r c) := by
  by_cases opt : TwoPhases.failures r c=256
  · obtain ⟨d,pat,unique⟩ := Rigidity.optimal_direction _ _ opt
    rw [weighted_pattern pat]
    constructor
    · cases designated p d <;> decide
    · constructor
      · intro hit
        have hd : designated p d=true := by cases h : designated p d <;> simp_all
        obtain ⟨a,ha,rfl⟩ := (chosen p d).mp hd
        exact ⟨a,ha,pat⟩
      · rintro ⟨a,ha,other⟩
        rw [← unique (unit a) other,designated_unit,ha]; rfl
  · have above := nonoptimal_weighted p small r c opt
    refine ⟨by omega,⟨fun eq => False.elim (by omega),?_⟩⟩
    rintro ⟨a,_,pat⟩
    exact False.elim (opt (Rigidity.optimal_of_direction pat))


def slice (d : B) := shifts.map fun s => (s.1,s.2,d)
def representatives (d : B) := (slice d).filter fun t => decide (t.1 < t.1 ^^^ d)
def geometric := directions.flatMap representatives

private theorem pair_slices : ∀ d∈directions,
    (slice d).Perm (representatives d ++ (representatives d).map reverseAnchor) := by decide +kernel

private theorem equiv_count (f : Rectangle → Bool) (stable : ∀ t, f (reverseAnchor t)=f t) :
    tests.countP f = 2*geometric.countP f := by
  have one (d : B) (hd : d∈directions) : (slice d).countP f = 2*(representatives d).countP f := by
    rw [(pair_slices d hd).countP_eq f,List.countP_append,List.countP_map]
    have same : (f ∘ reverseAnchor) = f := funext stable
    rw [same]; omega
  have add (ds : List B) (sub : ∀ d∈ds, d∈directions) :
      (ds.flatMap slice).countP f = 2*(ds.flatMap representatives).countP f := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.flatMap_cons,List.countP_append,one d (sub _ (by simp)),ih (fun a ha => sub _ (by simp [ha]))]
      omega
  exact add directions (fun _ h => h)

private theorem stableDrop (p x y d : B) : dropTest p (reverseAnchor (x,y,d)) = dropTest p (x,y,d) := by
  have both : ∀ a b : B, ((a ^^^ b) == 0 || (a ^^^ b) == b) = (a == 0 || a == b) := by decide
  simp only [dropTest,reverseAnchor,both]

def geometricRetained (p : B) (r c : Phase) :=
  (geometric.filter fun t => !(dropTest p t)).countP (Rigidity.twoBad r c)

/-- Count each undirected geometric square once, rather than both anchors.
The exact division by two applies to arbitrary phase tables. -/
theorem retained_twice (p : B) (r c : Phase) : retained p r c = 2*geometricRetained p r c := by
  unfold retained geometricRetained
  rw [List.countP_filter,List.countP_filter]
  apply equiv_count
  rintro ⟨x,y,d⟩
  have same := Rigidity.score_flip r c (x,y,d) true
  change TwoPhases.score r c (reverseAnchor (x,y,d)) = TwoPhases.score r c (x,y,d) at same
  simp only [Rigidity.twoBad,same,stableDrop]

theorem geometric_local (gap : Gap282) (p : B) (small : admissible p) (r c : Phase) :
    126 ≤ geometricRetained p r c ∧ (geometricRetained p r c = 126 ↔ Picked p r c) := by
  obtain ⟨bound,equal⟩ := retained_local gap p small r c
  rw [retained_twice] at bound equal
  exact ⟨by omega, ⟨fun h => equal.mp (by omega),fun h => by have := equal.mpr h; omega⟩⟩

end Mobius.AxisPortCost
