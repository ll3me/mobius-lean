import Mobius.RigidityEnumeration

/-! Three central hyperplanes with dependent normals 1, 2, and 3. They
share the same low-two-bits-zero plane and cover the entire four-space.
The eight-cell check is supported on the three boundary squares. -/
namespace Mobius.ThreeFaceParity
open Mobius.SignObstruction (B)
open Mobius.Rigidity (DirectionPattern)
open Mobius.Rigidity.Enumeration (Pair Phase)
open Mobius.TwoPhases (score)

set_option maxRecDepth 16384
set_option maxHeartbeats 15000000

inductive Face where | a | b | c deriving DecidableEq, Repr

def inside (f : Face) (x : B) : Bool :=
  match f with
  | .a => !(x.getLsbD 0)
  | .b => !(x.getLsbD 1)
  | .c => x.getLsbD 0 == x.getLsbD 1

def agree (f : Face) (p q : Pair) : Prop :=
  ∀ x y, inside f x=true → inside f y=true →
    p.1 x y=q.1 x y ∧ p.2 x y=q.2 x y

private theorem closed (f : Face) : ∀ x d : B, inside f x=true → inside f d=true →
    inside f (x ^^^ d)=true := by cases f <;> decide

theorem shared_score (f : Face) {p q : Pair} (same : agree f p q) (x y d : B)
    (hx : inside f x=true) (hy : inside f y=true) (hd : inside f d=true) :
    score p.1 p.2 (x,y,d)=score q.1 q.2 (x,y,d) := by
  have xx := closed f x d hx hd
  have yy := closed f y d hy hd
  simp only [score,TwoPhases.corners,SignObstruction.total,
    (same x y hx hy).1,(same _ _ xx yy).1,(same _ _ hx yy).2,(same _ _ xx hy).2]
  rfl

/-- In each base coordinate the numeral 3 is 1 XOR 2. -/
def parity (p : Pair) : Bool :=
  p.1 0 3 ^^ p.1 1 1 ^^ p.1 3 0 ^^ p.1 3 3 ^^
  p.2 0 2 ^^ p.2 1 1 ^^ p.2 2 0 ^^ p.2 2 2

theorem four_squares (p : Pair) : parity p =
    (score p.1 p.2 (0,3,1) ^^ score p.1 p.2 (2,1,1) ^^
      score p.1 p.2 (1,1,2) ^^ score p.1 p.2 (1,2,3)) := by
  change _ = ((p.1 0 3 ^^ (p.1 1 2 ^^ (p.2 0 2 ^^ (p.2 1 3 ^^ false)))) ^^
    (p.1 2 1 ^^ (p.1 3 0 ^^ (p.2 2 0 ^^ (p.2 3 1 ^^ false)))) ^^
    (p.1 1 1 ^^ (p.1 3 3 ^^ (p.2 1 3 ^^ (p.2 3 1 ^^ false)))) ^^
    (p.1 1 2 ^^ (p.1 2 1 ^^ (p.2 1 1 ^^ (p.2 2 2 ^^ false)))))
  simp [parity,Bool.xor_comm,Bool.xor_left_comm]

theorem pattern_parity (p : Pair) (d : B) (pat : DirectionPattern p.1 p.2 d) :
    parity p = decide (d=2 ∨ d=3) := by
  rw [four_squares,pat.2 0 3 1 (by decide),pat.2 2 1 1 (by decide),
    pat.2 1 1 2 (by decide),pat.2 1 2 3 (by decide)]
  have readout : ∀ e : B, (decide ((1:B)≠e) ^^ decide ((1:B)≠e) ^^ decide ((2:B)≠e) ^^ decide ((3:B)≠e))=decide (e=2 ∨ e=3) := by decide
  exact readout d

theorem boundary_parity {p q : Pair} (ha : agree .a p q) (hb : agree .b p q)
    (hc : agree .c p q) : parity p=parity q := by
  simp only [parity,
    (hc 0 3 (by decide) (by decide)).1, (hb 1 1 (by decide) (by decide)).1,
    (hc 3 0 (by decide) (by decide)).1, (hc 3 3 (by decide) (by decide)).1,
    (ha 0 2 (by decide) (by decide)).2, (hb 1 1 (by decide) (by decide)).2,
    (ha 2 0 (by decide) (by decide)).2, (ha 2 2 (by decide) (by decide)).2]

/-- Zero is the observable 'all successful on this face' marker. -/
def visible (f : Face) (d : B) := if inside f d then d else 0

def pairLabel (f g : Face) (u v : B) : Prop :=
  ∃ d : B, d≠0 ∧ visible f d=u ∧ visible g d=v

def possible (u v w : B) : Prop :=
  pairLabel .a .b u v ∧ pairLabel .a .c u w ∧ pairLabel .b .c v w

private def code (d : B) := (visible .a d,visible .b d,visible .c d)

/-- There are exactly sixteen pair-compatible visible profiles; the
extra all-clear profile is encoded by the zero word here. -/
theorem profile_classification : ∀ u v w : B, possible u v w ↔ ∃ d : B, code d=(u,v,w) := by
  intro u v w
  have seen {f : Face} {e label : B} (h : visible f e=label) (nz : label≠0) : e=label := by
    unfold visible at h
    split at h
    · exact h
    · exact False.elim (nz h.symm)
  constructor
  · rintro ⟨⟨a,_,au,av⟩,⟨b,_,bu,bw⟩,⟨c,_,cv,cw⟩⟩
    by_cases hu : u=0
    · by_cases hv : v=0
      · by_cases hw : w=0
        · exact ⟨0,by rw [hu,hv,hw]; decide⟩
        · obtain rfl := seen bw hw
          obtain rfl := seen cw hw
          exact ⟨_,Prod.ext bu (Prod.ext cv cw)⟩
      · obtain rfl := seen av hv
        obtain rfl := seen cv hv
        exact ⟨_,Prod.ext au (Prod.ext av cw)⟩
    · obtain rfl := seen au hu
      obtain rfl := seen bu hu
      exact ⟨_,Prod.ext au (Prod.ext av bw)⟩
  · rintro ⟨d,h⟩
    have h' : visible .a d=u ∧ visible .b d=v ∧ visible .c d=w := by
      simpa only [code,Prod.mk.injEq] using h
    by_cases z : d=0
    · subst d
      obtain ⟨rfl,rfl,rfl⟩ := h'
      exact ⟨⟨3,by decide,by decide,by decide⟩,⟨1,by decide,by decide,by decide⟩,
        ⟨2,by decide,by decide,by decide⟩⟩
    · exact ⟨⟨d,z,h'.1,h'.2.1⟩,⟨d,z,h'.1,h'.2.2⟩,⟨d,z,h'.2.1,h'.2.2⟩⟩

theorem labels_distinct : ∀ d e : B, code d=code e → d=e := by decide +kernel

/-- Every actual nonzero global direction is visible on at least one face. -/
theorem visible_some (d : B) (nz : d≠0) : inside .a d=true ∨ inside .b d=true ∨ inside .c d=true := by
  revert d; decide

def faceDirection : Face → B | .a => 2 | .b => 1 | .c => 3

/-- Fold the three quotient lines onto one bit while retaining coordinates
two and three. The fold is linear on the union of any chosen two faces
after replacing it by the indicated global linear lift. -/
def foldMap (x : B) : BitVec 3 :=
  (x >>> 2).setWidth 3 ^^^ (if x.toNat%4=0 then 0 else 4)

def liftMap (which : Face) (x : B) : BitVec 3 :=
  (x >>> 2).setWidth 3 ^^^ (if inside which x then 0 else 4)

def pulled (f : B → BitVec 3) : Pair :=
  let t := fun x y => EightSquare.phase (f x) (f y)
  (t,t)

def clear : Pair := pulled foldMap

private theorem lift_agree (which f : Face) (ne : which≠f) :
    agree f clear (pulled (liftMap which)) := by
  have same : ∀ x : B, inside f x=true → foldMap x=liftMap which x := by
    cases which <;> cases f <;> first | contradiction | decide
  intro x y hx hy
  simp only [clear,pulled,same x hx,same y hy,and_self]

private theorem lift_pattern (which : Face) :
    DirectionPattern (pulled (liftMap which)).1 (pulled (liftMap which)).2 (faceDirection which) := by
  cases which <;> unfold DirectionPattern <;> decide +kernel

def PairwiseOpt (p : Pair) : Prop :=
  ∀ i j : Face, i≠j → ∃ d : B, ∃ q : Pair, DirectionPattern q.1 q.2 d ∧ agree i p q ∧ agree j p q

def GloballyOpt (p : Pair) : Prop :=
  ∃ d : B, ∃ q : Pair, DirectionPattern q.1 q.2 d ∧ ∀ f : Face, agree f p q

theorem clear_pairwise : PairwiseOpt clear := by
  intro i j ne
  have third : ∃ k : Face, k≠i ∧ k≠j := by
    cases i <;> cases j <;> first | contradiction | exact ⟨.a,by decide,by decide⟩ |
      exact ⟨.b,by decide,by decide⟩ | exact ⟨.c,by decide,by decide⟩
  obtain ⟨k,ki,kj⟩ := third
  exact ⟨_,_,lift_pattern k,lift_agree k i ki,lift_agree k j kj⟩

private theorem clear_probe (f : Face) (d : B) (nz : d≠0) (within : inside f d=true) :
    score clear.1 clear.2 (0,0,d)=true := by
  cases f <;> revert d <;> decide +kernel

theorem clear_has_no_global_optimum : ¬GloballyOpt clear := by
  rintro ⟨d,q,profile,acts⟩
  have covers := visible_some d profile.1
  have witness (f : Face) (hit : inside f d=true) : False := by
    have origin (s : Face) : inside s 0=true := by cases s <;> decide
    have equal := shared_score f (acts f) 0 0 d (origin _) (origin _) hit
    rw [clear_probe f d profile.1 hit,profile.2 0 0 d profile.1] at equal
    simp at equal
  rcases covers with a|b|c
  · exact witness .a a
  · exact witness .b b
  · exact witness .c c

/-- Single-direction perturbation obtained from the universal homogeneous
one-bit two-table pattern by a linear functional. -/
def oneBit (which : Face) : Pair :=
  let l := fun (x : B) => if which=.b then x.getLsbD 0 else x.getLsbD 1
  if which=.c then (fun _ _ => false,fun _ _ => false)
  else (fun x y => !(l x) && l y,fun x y => l x && l y)

/-- Only the diagonal face receives exceptional values. On the common
plane, its low bit is zero and the formula agrees with both zero faces. -/
def twist : Pair :=
  (fun x y => inside .c x && inside .c y && !x.getLsbD 0 && y.getLsbD 0,
   fun x y => inside .c x && inside .c y && x.getLsbD 0 && y.getLsbD 0)

private theorem twist_agree (which f : Face) (different : which≠f) : agree f twist (oneBit which) := by
  cases which <;> cases f <;> first | contradiction | unfold agree; decide +kernel

private theorem oneBit_homogeneous (which : Face) : ∀ x y e : B,
    score (oneBit which).1 (oneBit which).2 (x,y,e)=false := by
  cases which <;> decide +kernel

private theorem excluded (i j : Face) (ne : i≠j) : ∃ k : Face, k≠i ∧ k≠j := by
  cases i <;> cases j <;> first | contradiction | exact ⟨.a,by decide,by decide⟩ |
    exact ⟨.b,by decide,by decide⟩ | exact ⟨.c,by decide,by decide⟩

def LocalFixed (p : Pair) (d : B) : Prop :=
  ∀ i : Face, ∃ q : Pair, DirectionPattern q.1 q.2 d ∧ agree i p q

def PairFixed (p : Pair) (d : B) : Prop :=
  ∀ i j : Face, i≠j → ∃ q : Pair, DirectionPattern q.1 q.2 d ∧ agree i p q ∧ agree j p q

theorem pairfixed_local {p : Pair} {d : B} (h : PairFixed p d) : LocalFixed p d := by
  intro i
  have another : ∃ j : Face, i≠j := by
    cases i <;> first | exact ⟨.a,by decide⟩ | exact ⟨.b,by decide⟩
  obtain ⟨j,ne⟩ := another
  obtain ⟨q,pat,hq,_⟩ := h i j ne
  exact ⟨q,pat,hq⟩

theorem twist_pair_fixed {p : Pair} {d : B} (h : DirectionPattern p.1 p.2 d) :
    PairFixed (Rigidity.Enumeration.plus p twist) d := by
  intro i j ne
  obtain ⟨k,ki,kj⟩ := excluded i j ne
  let q := Rigidity.Enumeration.plus p (oneBit k)
  have localForm (f : Face) (different : k≠f) :
      agree f (Rigidity.Enumeration.plus p twist) q := by
    intro x y hx hy
    obtain ⟨hr,hc⟩ := twist_agree k f different x y hx hy
    simp [q,Rigidity.Enumeration.plus,hr,hc]
  refine ⟨q,⟨h.1,?_⟩,localForm i ki,localForm j kj⟩
  intro x y e he
  rw [Rigidity.Enumeration.score_plus,oneBit_homogeneous,h.2 _ _ _ he,Bool.xor_false]

theorem identified {p q : Pair} {d e : B} (localDir : LocalFixed p d)
    (candidate : DirectionPattern q.1 q.2 e) (acts : ∀ f, agree f p q) : d=e := by
  obtain ⟨qa,base,_⟩ := localDir .a
  have origin (f : Face) : inside f 0=true := by cases f <;> decide
  have compare (f : Face) (insideD : inside f d=true) : d=e := by
    obtain ⟨q',qpat,hq⟩ := localDir f
    have first := shared_score f hq 0 0 d (origin _) (origin _) insideD
    have second := shared_score f (acts f) 0 0 d (origin _) (origin _) insideD
    have eqn := first.symm.trans second
    rw [qpat.2 0 0 d base.1, candidate.2 0 0 d base.1] at eqn
    by_cases equal : d=e
    · exact equal
    · simp [equal] at eqn
  rcases visible_some d base.1 with ha|hb|hc
  · exact compare .a ha
  · exact compare .b hb
  · exact compare .c hc

theorem parity_plus (p q : Pair) : parity (Rigidity.Enumeration.plus p q)=(parity p ^^ parity q) := by
  simp [parity,Rigidity.Enumeration.plus,Bool.xor_left_comm]

theorem twist_no_global {p : Pair} {d : B} (pat : DirectionPattern p.1 p.2 d) :
    ¬GloballyOpt (Rigidity.Enumeration.plus p twist) := by
  rintro ⟨e,q,candidate,acts⟩
  obtain rfl := identified (pairfixed_local (twist_pair_fixed pat)) candidate acts
  have same := boundary_parity (acts .a) (acts .b) (acts .c)
  have flip : parity twist=true := by decide
  rw [parity_plus,flip,pattern_parity _ _ pat,pattern_parity _ _ candidate] at same
  have no (b : Bool) : (b ^^ true) ≠ b := by cases b <;> decide
  exact no _ same

end Mobius.ThreeFaceParity
