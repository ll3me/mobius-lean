import Mobius.AxisNetwork
import Mobius.DoubleFan

/-! In a capped coordinate atlas every port coordinate has one private
four-dimensional cap. Assign both geometric tests on each port to its cap.
This partitions the full-board union using the physical ambient addresses. -/
namespace Mobius.FullCaps

open Mobius.SignObstruction (B Rectangle)
open Mobius.AxisGlue (Axis Atlas World bits unit embed restrict Matching)
open Mobius.AxisPortCost (Phase admissible dropped dropTest geometricRetained Gap282)
open Mobius.AxisNetwork (Feasible actualTest)
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

abbrev ci (n : Nat) (i : Fin k) := i.castAdd n
abbrev vi (k : Nat) (j : Fin n) := j.natAdd k

private theorem ci_inj {i j : Fin k} (h : ci n i=ci n j) : i=j := Fin.ext (congrArg (fun t : Fin (k+n) => t.val) h)
private theorem vi_inj {i j : Fin n} (h : vi k i=vi k j) : i=j := by
  have eqn := congrArg Fin.val h
  change k+i.val=k+j.val at eqn
  exact Fin.ext (by omega)

def cores (T : Atlas (k+n) v) : Atlas k v where
  loc i := T.loc (ci n i)
  inj i := T.inj (ci n i)
  linear _i _j ne := T.linear _ _ (fun eqn => ne (ci_inj eqn))

def caps (T : Atlas (k+n) v) : Atlas n v where
  loc j := T.loc (vi k j)
  inj j := T.inj (vi k j)
  linear _i _j ne := T.linear _ _ (fun eqn => ne (vi_inj eqn))

/-- These are local incidence checks on the input coordinates. Cap zero is
its port, and its other three coordinates are private. Each designated
core coordinate is represented, including ones occurring on just one core. -/
structure Wiring (T : Atlas (k+n) v) (p : Fin k → B) : Prop where
  coreShared : AxisNetwork.AllSharedArePorts (cores T) p
  incident : ∀ i j a b, T.loc (ci n i) a=T.loc (vi k j) b → bits (p i) a=true ∧ b=0
  cover : ∀ i a, bits (p i) a=true → ∃ j, T.loc (ci n i) a=T.loc (vi k j) 0
  separate : ∀ j j' a b, T.loc (vi k j) a=T.loc (vi k j') b → j=j'

/-- Value charged by full caps, in the unoriented measure. -/
def capCost (T : Atlas (k+n) v) (r c : World v) :=
  AxisNetwork.cost (caps T) (fun _ => 1) (fun _ => DoubleFan.full) r c

def cost (T : Atlas (k+n) v) (p : Fin k → B) (r c : World v) :=
  AxisNetwork.cost (cores T) p geometricRetained r c + capCost T r c

theorem cap_lower (T : Atlas (k+n) v) (r c : World v) : n*128≤capCost T r c :=
  AxisNetwork.global_lower (caps T) (fun _ => 1) (fun _ => by unfold admissible; decide) _ 128
    (fun _ _ => DoubleFan.full_lower) r c

theorem lower (gap : Gap282) (T : Atlas (k+n) v) (p : Fin k → B)
    (good : ∀ i, admissible (p i)) (r c : World v) :
    k*126+n*128≤cost T p r c := Nat.add_le_add
  (AxisNetwork.global_lower (cores T) p good _ 126 (fun b h r c => (AxisPortCost.geometric_local gap b h r c).1) r c)
  (cap_lower T r c)

private def capPick (z : Fin v → Bool) (T : Atlas (k+n) v) (j : Fin n) : Axis :=
  if z (T.loc (vi k j) 0) then 0 else 1

private theorem selections (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (feas : Feasible (cores T) p) :
    ∃ f : Fin (k+n) → Axis, Matching T f ∧ ∀ i, bits (p i) (f (ci n i))=true := by
  obtain ⟨z,ok⟩ := (AxisNetwork.feasible_iff_boolean _ _).mp feas
  let pick (i : Fin k) := Classical.choose (ok i)
  have hp (i : Fin k) := Classical.choose_spec (ok i)
  let f : Fin (k+n) → Axis := Fin.addCases pick (capPick z T)
  have onCore (i : Fin k) : f (ci n i)=pick i := Fin.addCases_left i
  have onCap (j : Fin n) : f (vi k j)=capPick z T j := Fin.addCases_right j
  have bitsCore (i : Fin k) (a : Axis) : z (T.loc (ci n i) a)=true ↔ pick i=a := by
    change z ((cores T).loc i a)=true ↔ _
    rw [(hp i).2 a]
    simp only [decide_eq_true_eq]
    exact eq_comm
  have facing (i j a b) (hit : T.loc (ci n i) a=T.loc (vi k j) b) :
      pick i=a ↔ capPick z T j=b := by
    obtain ⟨_,rfl⟩ := w.incident i j a b hit
    rw [←bitsCore i a,hit]
    cases h : z (T.loc (vi k j) 0) <;> simp [capPick,h]
  refine ⟨f,?_,fun i => onCore i ▸ (hp i).1⟩
  intro u t
  induction u using Fin.addCases with
  | left i =>
    induction t using Fin.addCases with
    | left j => intro a b hit; rw [onCore,onCore,←bitsCore,←bitsCore,hit]
    | right j => intro a b hit; rw [onCore,onCap]; exact facing i j a b hit
  | right j =>
    induction t using Fin.addCases with
    | left i => intro b a hit; rw [onCap,onCore]; exact (facing i j a b hit.symm).symm
    | right j' =>
      intro a b hit
      obtain rfl := w.separate j j' a b hit
      obtain rfl := T.inj _ a b hit
      exact Iff.rfl

private theorem sum_exact (f : Fin m → Nat) (t : Nat) (eqn : ∀ i, f i=t) :
    ((List.finRange m).map f).sum=m*t := by
  have ind (xs : List (Fin m)) : (xs.map f).sum=xs.length*t := by
    induction xs with
    | nil => simp
    | cons i xs ih => simp [eqn,ih,Nat.succ_mul,Nat.add_comm]
  simpa using ind (List.finRange m)

theorem attainable (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (feas : Feasible (cores T) p) : ∃ t : World v, cost T p t t=k*126+n*128 := by
  obtain ⟨f,matchAll,allowed⟩ := selections T p w feas
  obtain ⟨t,profiles⟩ := AxisGlue.pasted_optima T f matchAll
  have retained (i : Fin k) :
      geometricRetained (p i) (restrict t (cores T) i) (restrict t (cores T) i)=126 := by
    have e := AxisPortCost.retained_pattern (p:=p i) (profiles (ci n i)).1
    rw [AxisPortCost.retained_twice] at e
    have unitRule : ∀ mask a, AxisPortCost.designated mask (unit a)=bits mask a := by decide
    rw [unitRule,allowed i] at e
    change 2*geometricRetained (p i) (restrict t (cores T) i) (restrict t (cores T) i)=252 at e
    omega
  have whole (j : Fin n) : DoubleFan.full (restrict t (caps T) j) (restrict t (caps T) j)=128 := by
    have e := DoubleFan.full_twice (restrict t (caps T) j) (restrict t (caps T) j)
    have opt := (profiles (vi k j)).2
    change TwoPhases.failures (restrict t (caps T) j) (restrict t (caps T) j)=256 at opt
    omega
  refine ⟨t,?_⟩
  unfold cost capCost AxisNetwork.cost
  rw [sum_exact _ _ retained,sum_exact _ _ whole]

theorem threshold_of_local
    (localCost : ∀ p, admissible p → ∀ r c, 126≤geometricRetained p r c ∧
      (geometricRetained p r c=126 ↔ AxisPortCost.Picked p r c))
    (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p) (good : ∀ i, admissible (p i)) :
    (∃ r c : World v, cost T p r c≤k*126+n*128) ↔ Feasible (cores T) p := by
  constructor
  · rintro ⟨r,c,h⟩
    have capBound := cap_lower T r c
    unfold cost at h
    exact (AxisNetwork.exact_network (cores T) p good geometricRetained 126 localCost).mp ⟨r,c,by omega⟩
  · intro possible
    obtain ⟨t,hit⟩ := attainable T p w possible
    exact ⟨t,t,Nat.le_of_eq hit⟩

theorem threshold_iff (gap : Gap282) (T : Atlas (k+n) v) (p : Fin k → B)
    (w : Wiring T p) (good : ∀ i, admissible (p i)) :
    (∃ r c : World v, cost T p r c≤k*126+n*128) ↔ Feasible (cores T) p :=
  threshold_of_local (AxisPortCost.geometric_local gap) T p w good

/-- The index of a board determines which of its local tests it owns.
Caps keep all tests. Core boards leave the tests of their port lines to caps. -/
def mask (p : Fin k → B) : Fin (k+n) → B := Fin.addCases p (fun _ => 0)

def Owns (p : Fin k → B) (i : Fin (k+n)) (r : Rectangle) : Prop :=
  dropTest (mask p i) r=false

private theorem core_owns (p : Fin k → B) (i : Fin k) (r : Rectangle) :
    Owns (n:=n) p (ci n i) r ↔ dropTest (p i) r=false := by
  simp only [Owns,mask,ci,Fin.addCases_left]

private theorem cap_owns (p : Fin k → B) (j : Fin n) (r : Rectangle) : Owns p (vi k j) r := by
  have zero : ∀ x y d : B, dropTest 0 (x,y,d)=false := by decide +kernel
  rcases r with ⟨x,y,d⟩
  simp only [Owns,mask,vi,Fin.addCases_right,zero]

private theorem other_core_port (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (i : Fin k) (j : Fin (k+n)) (ne : ci n i≠j) (a b : Axis)
    (meet : T.loc (ci n i) a=T.loc j b) : bits (p i) a=true := by
  induction j using Fin.addCases with
  | left u => exact w.coreShared i u (fun h => ne (congrArg (ci n) h)) a b meet
  | right j => exact (w.incident i j a b meet).1

private theorem core_private (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (i : Fin k) (j : Fin (k+n)) (ne : ci n i≠j) (x y d : B) (r : Rectangle)
    (nz : d≠0) (owned : Owns p (ci n i) (x,y,d)) :
    actualTest T (ci n i) (x,y,d) ≠ actualTest T j r := by
  intro equal
  have keep := (core_owns p i _).mp owned
  rcases r with ⟨a,b,e⟩
  simp only [actualTest,Prod.mk.injEq] at equal
  obtain ⟨u,t,hit,dd,hx,hy⟩ := AxisGlue.shared_test_line T ne nz equal.1 equal.2.1 equal.2.2
  have allowed := other_core_port T p w i j ne u t hit
  have chosen : ∀ q u, AxisPortCost.designated q (unit u)=bits q u := by decide
  subst d
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
    simp [dropTest,chosen,allowed] at keep

private theorem cap_disjoint (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (i j : Fin n) (ne : i≠j) (x y d : B) (r : Rectangle) (nz : d≠0) :
    actualTest T (vi k i) (x,y,d)≠actualTest T (vi k j) r := by
  intro equal
  rcases r with ⟨a,b,e⟩
  simp only [actualTest,Prod.mk.injEq] at equal
  obtain ⟨u,t,hit,_⟩ := AxisGlue.shared_test_line T (fun eqn => ne (vi_inj eqn))
    nz equal.1 equal.2.1 equal.2.2
  exact ne (w.separate i j u t hit)

private theorem equal_board (T : Atlas (k+n) v) (i : Fin (k+n)) (r t : Rectangle)
    (equal : actualTest T i r=actualTest T i t) : r=t := by
  rcases r with ⟨x,y,d⟩
  rcases t with ⟨a,b,e⟩
  simp only [actualTest,Prod.mk.injEq] at equal
  exact Prod.ext (AxisGlue.embed_injective T i equal.1)
    (Prod.ext (AxisGlue.embed_injective T i equal.2.1) (AxisGlue.embed_injective T i equal.2.2))

/-- Distinct owners cannot count the same physical test, even when two
caps or two cores are compared. On one board the local address is unique. -/
theorem unique_owner (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (i j : Fin (k+n)) (r t : Rectangle) (nz : r.2.2≠0) (nz' : t.2.2≠0)
    (owns : Owns p i r) (owns' : Owns p j t) (equal : actualTest T i r=actualTest T j t) :
    i=j ∧ r=t := by
  suffices same : i=j by subst j; exact ⟨rfl,equal_board T i r t equal⟩
  apply Classical.byContradiction
  intro ne
  rcases r with ⟨x,y,d⟩
  rcases t with ⟨a,b,e⟩
  induction i using Fin.addCases with
  | left i => exact core_private T p w i j ne x y d _ nz owns equal
  | right i =>
    induction j using Fin.addCases with
    | left j => exact core_private T p w j _ (Ne.symm ne) a b e _ nz' owns' equal.symm
    | right j => exact cap_disjoint T p w i j (fun eqn => ne (congrArg (vi k) eqn)) x y d _ nz equal

private theorem drop_shape (p x y d : B) (dropped : dropTest p (x,y,d)=true) :
    ∃ a : Axis, bits p a=true ∧ d=unit a ∧ (x=0 ∨ x=d) ∧ (y=0 ∨ y=d) := by
  have classify : ∀ q s : B, AxisPortCost.designated q s=true → ∃ a : Axis, bits q a=true ∧ s=unit a := by decide
  simp only [dropTest,Bool.and_eq_true_iff,Bool.or_eq_true_iff,beq_iff_eq] at dropped
  obtain ⟨a,ha,hd⟩ := classify p d dropped.1.1
  exact ⟨a,ha,hd,dropped.1.2,dropped.2⟩

/-- Every directed test of every complete board has an owner at the same
actual embedded coordinates. Dropped core tests become cap tests. -/
theorem owner_exists (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p)
    (i : Fin (k+n)) (r : Rectangle) (nz : r.2.2≠0) :
    ∃ j t, t.2.2≠0 ∧ Owns p j t ∧ actualTest T i r=actualTest T j t := by
  induction i using Fin.addCases with
  | right j => exact ⟨_,r,nz,cap_owns p j r,rfl⟩
  | left i =>
    cases status : dropTest (p i) r with
    | false => exact ⟨_,r,nz,(core_owns p i r).mpr status,rfl⟩
    | true =>
      rcases r with ⟨x,y,d⟩
      obtain ⟨a,ha,hd,hx,hy⟩ := drop_shape _ _ _ _ status
      obtain ⟨j,hit⟩ := w.cover i a ha
      have u : embed T (ci n i) (unit a)=embed T (vi k j) (unit 0) := by
        rw [AxisGlue.embed_unit,AxisGlue.embed_unit,hit]
      have z : embed T (ci n i) 0=embed T (vi k j) 0 :=
        (AxisGlue.embed_zero _ _).trans (AxisGlue.embed_zero _ _).symm
      subst d
      rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
      · exact ⟨_,(0,0,unit 0),by decide,cap_owns p j _,Prod.ext z (Prod.ext z u)⟩
      · exact ⟨_,(0,unit 0,unit 0),by decide,cap_owns p j _,Prod.ext z (Prod.ext u u)⟩
      · exact ⟨_,(unit 0,0,unit 0),by decide,cap_owns p j _,Prod.ext u (Prod.ext z u)⟩
      · exact ⟨_,(unit 0,unit 0,unit 0),by decide,cap_owns p j _,Prod.ext u (Prod.ext u u)⟩

/-- The two opposite anchors of an unoriented test always have the same
owner. Together with each board's paired counting this identifies the
cost with the deduplicated unoriented full-board union. -/
theorem owns_reverse (p : Fin k → B) (i : Fin (k+n)) (r : Rectangle) :
    Owns p i (AxisPortCost.reverseAnchor r) ↔ Owns p i r := by
  have stable : ∀ q x y d : B, dropTest q (AxisPortCost.reverseAnchor (x,y,d))=dropTest q (x,y,d) := by decide +kernel
  rcases r with ⟨x,y,d⟩
  simp only [Owns,stable]

abbrev Address (v : Nat) := AxisGlue.Ambient v × AxisGlue.Ambient v × AxisGlue.Ambient v

/-- One list entry is a root pair and a nonzero direction in the physical
coordinate space. Opposite roots are combined by the final division by two. -/
def physicalBad (r c : World v) (e : Address v) : Bool :=
  let x := e.1
  let y := e.2.1
  let d := e.2.2
  let xd := fun w => x w ^^ d w
  let yd := fun w => y w ^^ d w
  !(r x y ^^ (r xd yd ^^ (c x yd ^^ c xd y)))

private theorem same_score (T : Atlas (k+n) v) (r c : World v) (i : Fin (k+n)) (e : Rectangle) :
    physicalBad r c (actualTest T i e) = Rigidity.twoBad (restrict r T i) (restrict c T i) e := by
  rcases e with ⟨x,y,d⟩
  simp [physicalBad,actualTest,Rigidity.twoBad,TwoPhases.score,TwoPhases.corners,
    SignObstruction.total,restrict,AxisGlue.embed_add]

private def boards (k n : Nat) := (List.finRange k).map (ci n) ++ (List.finRange n).map (vi k)

private theorem board_member (i : Fin (k+n)) : i∈boards k n := by
  induction i using Fin.addCases with
  | left i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
  | right j => exact List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩)

private theorem board_nodup : (boards k n).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_finRange k).map _ (fun _ _ ne eqn => ne (ci_inj eqn)),
    (List.nodup_finRange n).map _ (fun _ _ ne eqn => ne (vi_inj eqn)),?_⟩
  intro a ha b hb eqn
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  have h := congrArg Fin.val eqn
  change i.val=k+j.val at h
  have lt:=i.isLt
  omega

private theorem tests_mem (r : Rectangle) : r∈AxisPortCost.tests ↔ r.2.2≠0 := by
  rcases r with ⟨x,y,d⟩
  have valid : ∀ z : B, z∈SignObstruction.directions ↔ z≠0 := by decide
  constructor
  · intro h
    obtain ⟨e,he,a⟩ := List.mem_flatMap.mp h
    obtain ⟨⟨u,t⟩,_,eqn⟩ := List.mem_map.mp a
    cases eqn
    exact (valid _).mp he
  · intro hn
    exact List.mem_flatMap.mpr ⟨d,(valid _).mpr hn,List.mem_map.mpr
      ⟨(x,y),SignObstruction.shifts_complete _,rfl⟩⟩

private theorem tests_nodup : AxisPortCost.tests.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro d _
    apply SignObstruction.shifts_nodup.map
    intro a b ne e
    exact ne (Prod.ext (congrArg (fun x : Rectangle => x.1) e) (congrArg (fun x : Rectangle => x.2.1) e))
  · have nd : SignObstruction.directions.Nodup := by decide
    apply nd.imp
    intro a b ne x hx y hy eqn
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hy
    exact ne (congrArg (fun e : Rectangle => e.2.2) eqn)

private def ownedAt (T : Atlas (k+n) v) (p : Fin k → B) (i : Fin (k+n)) :=
  (AxisPortCost.tests.filter fun r => !(dropTest (mask p i) r)).map (actualTest T i)

private def owners (T : Atlas (k+n) v) (p : Fin k → B) := (boards k n).flatMap (ownedAt T p)

private theorem in_owned (T : Atlas (k+n) v) (p : Fin k → B) (i : Fin (k+n)) (q : Address v) :
    q∈ownedAt T p i ↔ ∃ r, r.2.2≠0 ∧ Owns p i r ∧ actualTest T i r=q := by
  simp only [ownedAt,List.mem_map,List.mem_filter,tests_mem,Bool.not_eq_true',Owns]
  constructor
  · rintro ⟨r,⟨nz,o⟩,h⟩; exact ⟨r,nz,o,h⟩
  · rintro ⟨r,nz,o,h⟩; exact ⟨r,⟨nz,o⟩,h⟩

private theorem owners_nodup (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p) : (owners T p).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact (tests_nodup.filter _).map _ (fun a b ne eqn => ne (equal_board T i a b eqn))
  · apply board_nodup.imp
    intro i j ne x hx y hy eqn
    obtain ⟨r,nz,ro,er⟩ := (in_owned T p i x).mp hx
    obtain ⟨t,nz',to',et⟩ := (in_owned T p j y).mp hy
    exact ne (unique_owner T p w i j r t nz nz' ro to' (er.trans (eqn.trans et.symm))).1

/-- A literal traversal of the complete boards, before removing overlaps. -/
def fullTraversal (T : Atlas (k+n) v) := (boards k n).flatMap fun i => AxisPortCost.tests.map (actualTest T i)

private theorem same_members (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p) (q : Address v) :
    q∈owners T p ↔ q∈fullTraversal T := by
  constructor
  · intro h
    obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨r,nz,_,eqn⟩ := (in_owned T p i _).mp hr
    exact List.mem_flatMap.mpr ⟨i,hi,List.mem_map.mpr ⟨r,(tests_mem _).mpr nz,eqn⟩⟩
  · intro h
    obtain ⟨i,_,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨r,mem,eqn⟩ := List.mem_map.mp hr
    obtain ⟨j,t,nz,owns,copy⟩ := owner_exists T p w i r ((tests_mem _).mp mem)
    exact List.mem_flatMap.mpr ⟨j,board_member j,(in_owned T p j _).mpr ⟨t,nz,owns,copy.symm.trans eqn⟩⟩

/-- Keep one occurrence per actual address. The reference definition deliberately
favors a small transparent specification over a particular hash-table backend. -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | x::xs => if x∈xs then dedup xs else x::dedup xs

private theorem dedup_mem [DecidableEq α] (x : α) (xs : List α) : x∈dedup xs ↔ x∈xs := by
  induction xs with
  | nil => simp [dedup]
  | cons a xs ih =>
    by_cases h : a∈xs
    · simp [dedup,h,ih]; intro eqn; subst a; exact h
    · simp [dedup,h,ih]

private theorem dedup_nodup [DecidableEq α] (xs : List α) : (dedup xs).Nodup := by
  induction xs with
  | nil => simp [dedup]
  | cons a xs ih =>
    by_cases h : a∈xs <;> simp [dedup,h,ih,dedup_mem]

private instance ambient_eq (v : Nat) : DecidableEq (AxisGlue.Ambient v) := fun x y =>
  if h : ∀ i, x i=y i then isTrue (funext h) else isFalse (fun eqn => h (congrFun eqn))

/-- Score the actual full-board union. Its definition does not read any mask
or ownership metadata. A local geometric square has two directed anchors. -/
def unionCost (T : Atlas (k+n) v) (r c : World v) :=
  ((dedup (fullTraversal T)).countP (physicalBad r c))/2

private theorem count_owned (T : Atlas (k+n) v) (p : Fin k → B) (i : Fin (k+n)) (r c : World v) :
    (ownedAt T p i).countP (physicalBad r c)=2*geometricRetained (mask p i) (restrict r T i) (restrict c T i) := by
  rw [←AxisPortCost.retained_twice]
  unfold ownedAt AxisPortCost.retained
  rw [List.countP_map]
  exact List.countP_congr (fun x _ => by simp [same_score])

private theorem double_sum (xs : List α) (f : α → Nat) :
    (xs.map (fun x => 2*f x)).sum=2*(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]

/-- Exact equality between the billed decomposition and a physical deduplication
of all directed tests of all complete boards, with the geometric factor of two. -/
theorem union_cost_eq (T : Atlas (k+n) v) (p : Fin k → B) (w : Wiring T p) (r c : World v) :
    unionCost T r c=cost T p r c := by
  have perm := (List.perm_ext_iff_of_nodup (dedup_nodup (fullTraversal T)) (owners_nodup T p w)).mpr
    (fun x => (dedup_mem x _).trans (same_members T p w x).symm)
  unfold unionCost
  rw [perm.countP_eq (physicalBad r c)]
  unfold owners boards
  rw [List.flatMap_append,List.countP_append,List.countP_flatMap,List.countP_flatMap]
  simp only [List.map_map,Function.comp_def,count_owned,mask,ci,vi,Fin.addCases_left,Fin.addCases_right]
  rw [double_sum,double_sum]
  change (2*AxisNetwork.cost (cores T) p geometricRetained r c+2*capCost T r c)/2=_
  simp [cost,←Nat.mul_add]

theorem complete_boards_iff (gap : Gap282) (T : Atlas (k+n) v) (p : Fin k → B)
    (w : Wiring T p) (good : ∀ i, admissible (p i)) :
    (∃ r c : World v, unionCost T r c≤k*126+n*128) ↔ Feasible (cores T) p := by
  simpa only [union_cost_eq T p w] using threshold_iff gap T p w good

end Mobius.FullCaps
