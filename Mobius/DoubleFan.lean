import Mobius.AxisPortCost

/-! Two families of four-dimensional leaves share the two coordinate axes
of one central board. All phases evaluate one pair of physical tables.
The objective counts center tests once and omits the shared axis from
every leaf. -/
namespace Mobius.DoubleFan
open Mobius.SignObstruction (B)
open Mobius.AxisPortCost (Phase removed retained geometricRetained)
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000

abbrev Ambient := B × ((Bool × Nat) → B)
abbrev World := Ambient → Ambient → Bool

def zeroPrivate : (Bool × Nat) → B := fun _ => 0
def pulse (s : Bool) (i : Nat) (u : B) : (Bool × Nat) → B := fun j =>
  if j=(s,i) then u else 0

def center (x : B) : Ambient := (x,zeroPrivate)
def axis (s : Bool) : B := if s then 2 else 1
def axisPoint (s : Bool) (x : B) : B := if x.getLsbD 0 then axis s else 0
def privatePart (x : B) := x &&& 14
def leaf (s : Bool) (i : Nat) (x : B) : Ambient :=
  (axisPoint s x,pulse s i (privatePart x))

def atBoard (g : World) (embed : B → Ambient) : Phase := fun x y => g (embed x) (embed y)

theorem leaf_injective (s : Bool) (i : Nat) {x y : B} (h : leaf s i x=leaf s i y) : x=y := by
  have hi := congrArg (fun z : Ambient => z.2 (s,i)) h
  have low := congrArg Prod.fst h
  have unique : ∀ (s : Bool) (u v : B),
      privatePart u=privatePart v → axisPoint s u=axisPoint s v → u=v := by decide
  exact unique s x y (by simpa [leaf,pulse] using hi) low

@[simp] private theorem pulse_zero (s : Bool) (i : Nat) : pulse s i 0=zeroPrivate := by
  funext j; simp [pulse,zeroPrivate]

/-- A common leaf and center address must lie on the leaf's port. -/
theorem center_leaf_intersection (s : Bool) (i : Nat) (x y : B) :
    center x=leaf s i y ↔ x=axisPoint s y ∧ privatePart y=0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h,by
      have a := congrArg (fun z : Ambient => z.2 (s,i)) h
      simpa [center, leaf, pulse, zeroPrivate, eq_comm] using a⟩
  · rintro ⟨rfl,hy⟩
    simp [center,leaf,hy]
    exact (pulse_zero s i).symm

/-- Distinct leaves have no additional shared addresses outside the center. -/
theorem distinct_leaf_intersection (s t : Bool) (i j : Nat) (ne : (s,i)≠(t,j))
    (x y : B) : leaf s i x=leaf t j y ↔
      privatePart x=0 ∧ privatePart y=0 ∧ axisPoint s x=axisPoint t y := by
  constructor
  · intro h
    have a := congrArg (fun z : Ambient => z.2 (s,i)) h
    have b := congrArg (fun z : Ambient => z.2 (t,j)) h
    exact ⟨by simpa [leaf,pulse,ne] using a,by simpa [leaf,pulse,Ne.symm ne] using b.symm,
      congrArg Prod.fst h⟩
  · rintro ⟨hx,hy,ha⟩
    simp [leaf,hx,hy,ha]
    exact (pulse_zero s i).trans (pulse_zero t j).symm

private theorem port_point (s : Bool) (i : Nat) :
    leaf s i 0 = center 0 ∧ leaf s i 1 = center (axis s) := by
  cases s <;> simp [leaf,center,privatePart,axisPoint,axis] <;> exact pulse_zero _ _

private theorem removed_corners (r c : Phase) : ∀ (s : Bool),
    removed (axis s) r c =
    let d := axis s
    [(0,0,d),(0,d,d),(d,0,d),(d,d,d)].countP (Rigidity.twoBad r c) := by
  intro s; cases s <;> rfl

theorem shared_removed (r c : World) (s : Bool) (i : Nat) :
    removed 1 (atBoard r (leaf s i)) (atBoard c (leaf s i)) =
    removed (axis s) (atBoard r center) (atBoard c center) := by
  rw [←show axis false = (1:B) from rfl,removed_corners,removed_corners]
  have h0 := (port_point s i).1
  have h1 := (port_point s i).2
  cases s <;>
    simp [axis, List.countP_cons,Rigidity.twoBad,TwoPhases.score,TwoPhases.corners,
      SignObstruction.total,atBoard,axis] at h0 h1 ⊢ <;> simp [h0,h1]

private theorem removed_zero (r c : Phase) : removed 0 r c=0 := rfl

def full (r c : Phase) := geometricRetained 0 r c

theorem full_twice (r c : Phase) : 2*full r c=TwoPhases.failures r c := by
  have h := AxisPortCost.partition 0 r c
  simpa only [removed_zero,Nat.zero_add,AxisPortCost.retained_twice,full] using h

theorem full_lower (r c : Phase) : 128≤full r c := by
  have := full_twice r c
  have := TwoPhases.failures_lower r c
  omega

private theorem removed_le_four (r c : Phase) : removed 1 r c≤4 := by
  exact List.countP_le_length (l:=AxisPortCost.dropped 1) (p:=Rigidity.twoBad r c)

/-- A partial axis cannot give the two-test rebate of a completely bad axis. -/
theorem leaf_cost (r c : Phase) : 126≤ geometricRetained 1 r c ∧
    (removed 1 r c≠4 → 128≤geometricRetained 1 r c) := by
  have hp := AxisPortCost.partition 1 r c
  rw [AxisPortCost.retained_twice] at hp
  have lower := TwoPhases.failures_lower r c
  have even := full_twice r c
  have cap := removed_le_four r c
  refine ⟨by omega,?_⟩
  intro partialAxis
  by_cases best : TwoPhases.failures r c=256
  · obtain ⟨d,pat,_⟩ := Rigidity.optimal_direction r c best
    have a := AxisPortCost.removed_pattern (p:=1) pat
    split at a <;> omega
  · omega

def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => total f n + f n

def cost (p : Nat) (r c : World) :=
  full (atBoard r center) (atBoard c center) + total (fun i =>
    geometricRetained 1 (atBoard r (leaf false i)) (atBoard c (leaf false i)) +
    geometricRetained 1 (atBoard r (leaf true i)) (atBoard c (leaf true i))) p

def BothBad (r c : World) : Prop :=
  removed 1 (atBoard r center) (atBoard c center)=4 ∧
  removed 2 (atBoard r center) (atBoard c center)=4

theorem not_both_lower (p : Nat) (r c : World) (h : ¬BothBad r c) : 128+254*p ≤ cost p r c := by
  let f := fun s i => geometricRetained 1 (atBoard r (leaf s i)) (atBoard c (leaf s i))
  have bound (i : Nat) : 254≤f false i+f true i := by
    have e (s : Bool) := leaf_cost (atBoard r (leaf s i)) (atBoard c (leaf s i))
    have strong (s : Bool) (hh : removed (axis s) (atBoard r center) (atBoard c center)≠4) : 128≤f s i :=
      (e s).2 (fun he => hh ((shared_removed r c s i).symm.trans he))
    by_cases h₀ : removed 1 (atBoard r center) (atBoard c center)=4
    · have ha := strong true (fun h₁ => h ⟨h₀,h₁⟩)
      exact Nat.le_trans (by decide : 254≤126+128) (Nat.add_le_add (e false).1 ha)
    · have ha := strong false h₀
      exact Nat.le_trans (by decide : 254≤128+126) (Nat.add_le_add ha (e true).1)
  have sumBound : 254*p≤total (fun i => f false i+f true i) p := by
    induction p with
    | zero => simp [total]
    | succ p ih => rw [Nat.mul_succ, total]; exact Nat.add_le_add ih (bound p)
  exact Nat.add_le_add (full_lower _ _) sumBound

/-- Collapse the private coordinate of each visited leaf to its own upper
three bits; local leaves occupy disjoint private components of the world. -/
def collect (w : (Bool × Nat) → B) : Nat → B
  | 0 => 0
  | n+1 => collect w n ^^^ w (false,n) ^^^ w (true,n)

private theorem collect_zero (p : Nat) : collect zeroPrivate p=0 := by
  induction p <;> simp_all [collect,zeroPrivate]

private theorem collect_pulse (s : Bool) (i : Nat) (v : B) (p : Nat) :
    collect (pulse s i v) p = if i<p then v else 0 := by
  induction p with
  | zero => simp [collect]
  | succ p ih =>
    by_cases eq : i=p
    · subst i; cases s <;> simp [collect,ih,pulse]
    · have unequal := Ne.symm eq
      have order : i<p+1 ↔ i<p := by omega
      cases s <;> simp [collect,ih,pulse,unequal,order]

def candidateCenter (x y : B) :=
  AxisGlue.table 0 x y ^^ ((x==2) && (y==2))

def witness (p : Nat) : World := fun x y =>
  candidateCenter x.1 y.1 ^^ AxisGlue.table 0 (collect x.2 p) (collect y.2 p)

private theorem corner_zero : ∀ (s : Bool) (x y : B),
    candidateCenter (axisPoint s x) (axisPoint s y) = false := by decide +kernel
private theorem ignore_axis : ∀ (x y : B),
    AxisGlue.table 0 (privatePart x) (privatePart y) = AxisGlue.table 0 x y := by decide +kernel

theorem witness_center (p : Nat) : atBoard (witness p) center = candidateCenter := by
  funext x y
  simp [atBoard,witness,center,collect_zero]
  change (candidateCenter x y ^^ AxisGlue.table 0 0 0) = _
  rw [AxisGlue.origin_table, Bool.xor_false]

theorem witness_leaf (p : Nat) (s : Bool) (i : Nat) (hi : i<p) :
    atBoard (witness p) (leaf s i) = AxisGlue.table 0 := by
  funext x y
  simp [atBoard,witness,leaf,collect_pulse,hi,corner_zero,ignore_axis]

theorem candidate_count : full candidateCenter candidateCenter=154 := by decide +kernel
private theorem ground_leaf_cost : geometricRetained 1 (AxisGlue.table 0) (AxisGlue.table 0)=126 := by
  have h := AxisPortCost.retained_pattern (p:=1) (Rigidity.Enumeration.ground_pattern (AxisGlue.direction 0))
  rw [AxisPortCost.retained_twice] at h
  change 2*geometricRetained 1 (AxisGlue.table 0) (AxisGlue.table 0) = 252 at h
  omega

theorem witness_cost (p : Nat) : cost p (witness p) (witness p)=154+252*p := by
  unfold cost
  rw [witness_center,candidate_count]
  congr 1
  have partialSum (k : Nat) (hk : k≤p) : total (fun i =>
      geometricRetained 1 (atBoard (witness p) (leaf false i)) (atBoard (witness p) (leaf false i)) +
      geometricRetained 1 (atBoard (witness p) (leaf true i)) (atBoard (witness p) (leaf true i))) k = 252*k := by
    induction k with
    | zero => simp [total]
    | succ k ih =>
      rw [total,ih (by omega),witness_leaf p false k (by omega),witness_leaf p true k (by omega),
        ground_leaf_cost,Nat.mul_succ]
  exact partialSum p (Nat.le_refl p)

def Minimizes (p : Nat) (r c : World) := ∀ r' c', cost p r c ≤ cost p r' c'

theorem exists_minimizer (p : Nat) : ∃ r c, Minimizes p r c := by
  classical
  have descend (n : Nat) (attained : ∃ r c, cost p r c=n) : ∃ r c, Minimizes p r c := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      obtain ⟨r,c,eqn⟩ := attained
      by_cases best : Minimizes p r c
      · exact ⟨r,c,best⟩
      · unfold Minimizes at best
        obtain ⟨s,hs⟩ := Classical.not_forall.mp best
        obtain ⟨t,ht⟩ := Classical.not_forall.mp hs
        exact ih (cost p s t) (by omega) ⟨s,t,rfl⟩
  exact descend _ ⟨witness p,witness p,rfl⟩

theorem witness_both (p : Nat) : BothBad (witness p) (witness p) := by
  unfold BothBad
  rw [witness_center]
  decide +kernel

/-- The competing construction keeps the central board optimal and
maximally rewards one of the two fans. It is one linear pullback. -/
def baseline (p : Nat) : World := fun x y =>
  AxisGlue.table 0 (x.1 ^^^ collect x.2 p) (y.1 ^^^ collect y.2 p)

def baseLeaf (s : Bool) : Phase := fun x y =>
  AxisGlue.table 0 (axisPoint s x ^^^ privatePart x) (axisPoint s y ^^^ privatePart y)

private theorem baseline_center (p : Nat) : atBoard (baseline p) center=AxisGlue.table 0 := by
  funext x y; simp [atBoard,baseline,center,collect_zero]

private theorem baseline_leaf (p : Nat) (s : Bool) (i : Nat) (hi : i<p) :
    atBoard (baseline p) (leaf s i)=baseLeaf s := by
  funext x y; simp [atBoard,baseline,leaf,collect_pulse,hi,baseLeaf]

private theorem baseline_leaf_pattern : ∀ s : Bool, Rigidity.DirectionPattern (baseLeaf s) (baseLeaf s)
    (if s then 3 else 1) := by unfold Rigidity.DirectionPattern; decide +kernel

private theorem baseline_leaf_cost : ∀ s : Bool, geometricRetained 1 (baseLeaf s) (baseLeaf s) =
    if s then 128 else 126 := by
  intro s
  have h := AxisPortCost.retained_pattern (p:=1) (baseline_leaf_pattern s)
  rw [AxisPortCost.retained_twice] at h
  cases s
  · change 2*geometricRetained 1 (baseLeaf false) (baseLeaf false)=252 at h
    change geometricRetained 1 (baseLeaf false) (baseLeaf false)=126
    omega
  · change 2*geometricRetained 1 (baseLeaf true) (baseLeaf true)=256 at h
    change geometricRetained 1 (baseLeaf true) (baseLeaf true)=128
    omega

theorem baseline_cost (p : Nat) : cost p (baseline p) (baseline p)=128+254*p := by
  have exactCenter : full (AxisGlue.table 0) (AxisGlue.table 0)=128 := by
    have h := full_twice (AxisGlue.table 0) (AxisGlue.table 0)
    have opt := Rigidity.optimal_of_direction (Rigidity.Enumeration.ground_pattern (AxisGlue.direction 0))
    change TwoPhases.failures (AxisGlue.table 0) (AxisGlue.table 0)=256 at opt
    omega
  unfold cost
  rw [baseline_center,exactCenter]
  congr 1
  have partialSum (k : Nat) (hk : k≤p) : total (fun i =>
      geometricRetained 1 (atBoard (baseline p) (leaf false i)) (atBoard (baseline p) (leaf false i)) +
      geometricRetained 1 (atBoard (baseline p) (leaf true i)) (atBoard (baseline p) (leaf true i))) k = 254*k := by
    induction k with
    | zero => simp [total]
    | succ k ih =>
      rw [total,ih (by omega),baseline_leaf p false k (by omega),baseline_leaf p true k (by omega),
        baseline_leaf_cost,baseline_leaf_cost,Nat.mul_succ]
      rfl
  exact partialSum p (Nat.le_refl p)

theorem forced_sacrifice (p : Nat) (hp : 14≤p) (r c : World) (best : Minimizes p r c) :
    BothBad r c ∧ 128<full (atBoard r center) (atBoard c center) := by
  have upper := best (witness p) (witness p)
  rw [witness_cost] at upper
  have both : BothBad r c := by
    apply Classical.byContradiction
    intro notBoth
    have := not_both_lower p r c notBoth
    omega
  refine ⟨both,?_⟩
  have bound := full_lower (atBoard r center) (atBoard c center)
  apply Classical.byContradiction
  intro low
  have twice := full_twice (atBoard r center) (atBoard c center)
  have opt : TwoPhases.failures (atBoard r center) (atBoard c center)=256 := by omega
  obtain ⟨d,pat,_⟩ := Rigidity.optimal_direction _ _ opt
  have left := AxisPortCost.removed_pattern (p:=1) pat
  have right := AxisPortCost.removed_pattern (p:=2) pat
  rw [both.1] at left
  rw [both.2] at right
  have incompatible : ∀ z : B, ¬(AxisPortCost.designated 1 z=true ∧ AxisPortCost.designated 2 z=true) := by decide
  apply incompatible d
  constructor
  · split at left <;> simp_all
  · split at right <;> simp_all


/-- Low-coordinate pullback of the arbitrary eight physical port entries. -/
def portPull (s : Bool) (r : Phase) : Phase := fun x y => r (axisPoint s x) (axisPoint s y)

private theorem pull_good {s : Bool} {r c : Phase} (allBad : removed (axis s) r c=4)
    (x y d : B) : TwoPhases.score (portPull s r) (portPull s c) (x,y,d)=false := by
  have lin : ∀ (s : Bool) (u v : B), axisPoint s (u ^^^ v)=axisPoint s u ^^^ axisPoint s v := by decide
  have eqn : TwoPhases.score (portPull s r) (portPull s c) (x,y,d) =
      TwoPhases.score r c (axisPoint s x,axisPoint s y,axisPoint s d) := by
    simp only [portPull,TwoPhases.score,TwoPhases.corners,SignObstruction.total,lin]
  rw [eqn]
  by_cases hz : axisPoint s d=0
  · simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,hz,Bool.xor_comm]
  · have inside : ∀ (u : Bool) (a b e : B), axisPoint u e≠0 →
        (axisPoint u a,axisPoint u b,axisPoint u e) ∈ AxisPortCost.dropped (axis u) := by decide +kernel
    have len : (AxisPortCost.dropped (axis s)).length=4 := by cases s <;> rfl
    have bad := List.countP_eq_length.mp (allBad.trans len.symm) _ (inside s x y d hz)
    change !(TwoPhases.score r c (axisPoint s x,axisPoint s y,axisPoint s d))=true at bad
    simpa using bad

def extendCenter (p : Nat) (r : Phase) : World := fun x y =>
  r x.1 y.1 ^^ AxisGlue.table 0 (collect x.2 p) (collect y.2 p)

theorem extend_center (p : Nat) (r : Phase) : atBoard (extendCenter p r) center = r := by
  funext x y
  change (r x y ^^ AxisGlue.table 0 (collect zeroPrivate p) (collect zeroPrivate p)) = _
  rw [collect_zero,AxisGlue.origin_table,Bool.xor_false]

private def leafPlus (s : Bool) (r : Phase) : Phase := fun x y =>
  portPull s r x y ^^ AxisGlue.table 0 x y

theorem extend_leaf (p : Nat) (r : Phase) (s : Bool) (i : Nat) (hi : i<p) :
    atBoard (extendCenter p r) (leaf s i) = leafPlus s r := by
  funext x y
  simp [atBoard,extendCenter,leaf,collect_pulse,hi,ignore_axis,portPull,leafPlus]

private theorem extend_leaf_pattern {s : Bool} {r c : Phase} (axisBad : removed (axis s) r c=4) :
    Rigidity.DirectionPattern (leafPlus s r) (leafPlus s c) 1 := by
  refine ⟨by decide,?_⟩
  intro x y e he
  change TwoPhases.score
    (Rigidity.Enumeration.plus (portPull s r,portPull s c) (Rigidity.Enumeration.ground (AxisGlue.direction 0))).1
    (Rigidity.Enumeration.plus (portPull s r,portPull s c) (Rigidity.Enumeration.ground (AxisGlue.direction 0))).2
    (x,y,e) = _
  rw [Rigidity.Enumeration.score_plus, pull_good axisBad, Bool.false_xor]
  exact (Rigidity.Enumeration.ground_pattern (AxisGlue.direction 0)).2 x y e he

def FullAxes (r c : Phase) : Prop := removed 1 r c=4 ∧ removed 2 r c=4

theorem extend_cost (p : Nat) (r c : Phase) (h : FullAxes r c) :
    cost p (extendCenter p r) (extendCenter p c) = full r c+252*p := by
  have paid (s) : geometricRetained 1 (leafPlus s r) (leafPlus s c)=126 := by
    have axisBad : removed (axis s) r c=4 := by cases s; exact h.1; exact h.2
    have e := AxisPortCost.retained_pattern (p:=1) (extend_leaf_pattern axisBad)
    rw [AxisPortCost.retained_twice] at e
    change 2*geometricRetained 1 (leafPlus s r) (leafPlus s c)=252 at e
    omega
  unfold cost
  rw [extend_center,extend_center]
  congr 1
  have partialSum (k : Nat) (hk : k≤p) : total (fun i =>
      geometricRetained 1 (atBoard (extendCenter p r) (leaf false i)) (atBoard (extendCenter p c) (leaf false i)) +
      geometricRetained 1 (atBoard (extendCenter p r) (leaf true i)) (atBoard (extendCenter p c) (leaf true i))) k = 252*k := by
    induction k with
    | zero => simp [total]
    | succ k ih =>
      rw [total,ih (by omega),extend_leaf p r false k (by omega),extend_leaf p c false k (by omega),
        extend_leaf p r true k (by omega),extend_leaf p c true k (by omega),paid,paid,Nat.mul_succ]
  exact partialSum p (Nat.le_refl p)

def CenterMinimum (C : Nat) : Prop :=
    (∃ r c : Phase, FullAxes r c ∧ full r c=C) ∧ (∀ r c, FullAxes r c → C≤full r c)

theorem center_minimum_exists : ∃ C, CenterMinimum C := by
  classical
  have descend (n : Nat) (poss : ∃ r c, FullAxes r c ∧ full r c=n) : ∃ C, CenterMinimum C := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases best : ∀ r c, FullAxes r c → n≤full r c
      · exact ⟨n,poss,best⟩
      · obtain ⟨r,hr⟩ := Classical.not_forall.mp best
        obtain ⟨c,hc⟩ := Classical.not_forall.mp hr
        have axisBad : FullAxes r c := Classical.byContradiction (fun no => hc (fun h => False.elim (no h)))
        exact ih (full r c) (Nat.lt_of_not_ge (fun h => hc (fun _ => h))) ⟨r,c,axisBad,rfl⟩
  refine descend 154 ⟨candidateCenter,candidateCenter,?_,candidate_count⟩
  change removed 1 candidateCenter candidateCenter=4 ∧ removed 2 candidateCenter candidateCenter=4
  decide +kernel

/-- The global optimum over two actual ambient tables is exactly the lower
of two affine functions of the number of leaves per side. -/
theorem exact_cost {C : Nat} (cmin : CenterMinimum C) (p : Nat) (r c : World) (best : Minimizes p r c) :
    cost p r c = min (128+254*p) (C+252*p) := by
  obtain ⟨⟨r₀,c₀,ports,hit⟩,centerBound⟩ := cmin
  have high₁ := best (baseline p) (baseline p)
  rw [baseline_cost] at high₁
  have high₂ := best (extendCenter p r₀) (extendCenter p c₀)
  rw [extend_cost p _ _ ports,hit] at high₂
  by_cases h : BothBad r c
  · have lowCenter := centerBound _ _ h
    let f := fun s i => geometricRetained 1 (atBoard r (leaf s i)) (atBoard c (leaf s i))
    have paid (i : Nat) : 252≤f false i+f true i := Nat.add_le_add (leaf_cost _ _).1 (leaf_cost _ _).1
    have lowLeaves (k : Nat) : 252*k≤total (fun i => f false i+f true i) k := by
      induction k with
      | zero => simp [total]
      | succ p ih => rw [Nat.mul_succ,total]; exact Nat.add_le_add ih (paid p)
    have low : C+252*p ≤ cost p r c := Nat.add_le_add lowCenter (lowLeaves p)
    omega
  · have low := not_both_lower p r c h
    omega

end Mobius.DoubleFan
