import Mobius.ThreeFaceParity
/-! Linear interpolation of an arbitrary diagonal-face boundary correction
that vanishes on the common core and satisfies its one parity check. All
generated interpolation coefficients are checked against the 62-dimensional
homogeneous decoder and all physical squares by the Lean kernel. -/
namespace Mobius.ThreeFaceCompletion
open Mobius.SignObstruction (B)
open Mobius.Rigidity (DirectionPattern)
open Mobius.Rigidity.Enumeration (Pair Phase ZeroPair plus lookup)
open Mobius.Rigidity.Kernel (key double dot dot_xor)
open Mobius.ThreeFaceParity
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000

private def extData : Array (Array Nat) := #[
  #[0,0,0,0x1,0,0,0,0x2,0,0,0,0x4,0,0,0,0x8],
  #[0,0,0,0x1,0,0,0x30,0x32,0,0,0x50,0x54,0,0,0x90,0x98],
  #[0,0,0,0x1,0,0x30,0,0x32,0,0x50,0,0x54,0,0x90,0,0x98],
  #[0x10,0x10,0x10,0x11,0x20,0x10,0x10,0x22,0x40,0x10,0x10,0x44,0x80,0x10,0x10,0x88],
  #[0,0,0,0x31,0,0,0,0x32,0,0,0,0xc4,0,0,0,0xc8],
  #[0,0,0x30,0x1,0,0,0,0x32,0,0,0x90,0x54,0,0,0x50,0x98],
  #[0,0x30,0,0x1,0,0,0,0x32,0,0x90,0,0x54,0,0x50,0,0x98],
  #[0x100,0x130,0x130,0x131,0x130,0x130,0x130,0x102,0x1a0,0x130,0x130,0x164,0x160,0x130,0x130,0x1a8],
  #[0,0,0,0x51,0,0,0,0xa2,0,0,0,0x54,0,0,0,0xa8],
  #[0,0,0x50,0x1,0,0,0x90,0x32,0,0,0,0x54,0,0,0x30,0x98],
  #[0,0x50,0,0x1,0,0x90,0,0x32,0,0,0,0x54,0,0x30,0,0x98],
  #[0x200,0x250,0x250,0x251,0x2c0,0x250,0x250,0x262,0x250,0x250,0x250,0x204,0x260,0x250,0x250,0x2c8],
  #[0,0,0,0x91,0,0,0,0x62,0,0,0,0x64,0,0,0,0x98],
  #[0,0,0x90,0x1,0,0,0x50,0x32,0,0,0x30,0x54,0,0,0,0x98],
  #[0,0x90,0,0x1,0,0x50,0,0x32,0,0x30,0,0x54,0,0,0,0x98],
  #[0x400,0x490,0x490,0x491,0x4c0,0x490,0x490,0x4a2,0x4a0,0x490,0x490,0x4c4,0x490,0x490,0x490,0x408],
  #[0,0,0,0x800,0,0,0,0x1000,0,0,0,0x2000,0,0,0,0x4000],
  #[0,0,0x801,0x1,0,0,0x1032,0x32,0,0,0x2054,0x54,0,0,0x4098,0x98],
  #[0,0x801,0,0x1,0,0x1032,0,0x32,0,0x2054,0,0x54,0,0x4098,0,0x98],
  #[0x811,0x10,0x10,0x11,0x1022,0x10,0x10,0x22,0x2044,0x10,0x10,0x44,0x4088,0x10,0x10,0x88],
  #[0,0,0,0x1033,0,0,0,0x833,0,0,0,0x40cc,0,0,0,0x20cc],
  #[0,0,0x1032,0x1,0,0,0x801,0x32,0,0,0x4098,0x54,0,0,0x2054,0x98],
  #[0,0x1032,0,0x1,0,0x801,0,0x32,0,0x4098,0,0x54,0,0x2054,0,0x98],
  #[0x1102,0x130,0x130,0x131,0x931,0x130,0x130,0x102,0x41a8,0x130,0x130,0x164,0x2164,0x130,0x130,0x1a8],
  #[0,0,0,0x2055,0,0,0,0x40aa,0,0,0,0x855,0,0,0,0x10aa],
  #[0,0,0x2054,0x1,0,0,0x4098,0x32,0,0,0x801,0x54,0,0,0x1032,0x98],
  #[0,0x2054,0,0x1,0,0x4098,0,0x32,0,0x801,0,0x54,0,0x1032,0,0x98],
  #[0x2204,0x250,0x250,0x251,0x42c8,0x250,0x250,0x262,0xa51,0x250,0x250,0x204,0x1262,0x250,0x250,0x2c8],
  #[0,0,0,0x4099,0,0,0,0x2066,0,0,0,0x1066,0,0,0,0x899],
  #[0,0,0x4098,0x1,0,0,0x2054,0x32,0,0,0x1032,0x54,0,0,0x801,0x98],
  #[0,0x4098,0,0x1,0,0x2054,0,0x32,0,0x1032,0,0x54,0,0x801,0,0x98],
  #[0x4408,0x490,0x490,0x491,0x24c4,0x490,0x490,0x4a2,0x14a2,0x490,0x490,0x4c4,0xc91,0x490,0x490,0x408]
]
private def errData : Array (Array Nat) := #[
  #[0x1,0,0,0,0x2,0,0,0,0x4,0,0,0,0x8,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0x4000,0,0,0,0x4003,0,0,0,0x4005,0,0,0,0x4009],
  #[0x10,0,0,0x12,0x20,0,0,0x21,0x40,0,0,0x48,0x7f,0,0,0x7b],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0x4003,0x33,0,0,0x4033,0x5a,0,0,0x4053,0x69,0,0,0x406c],
  #[0x80,0,0,0x84,0xd6,0,0,0xde,0x100,0,0,0x101,0x159,0,0,0x15b],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0x4005,0x5a,0,0,0x4053,0x185,0,0,0x4185,0x1df,0,0,0x41dc],
  #[0x200,0,0,0x208,0x265,0,0,0x261,0x3d5,0,0,0x3d7,0x3bf,0,0,0x3be],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0x4009,0x69,0,0,0x406c,0x1df,0,0,0x41dc,0x1b6,0,0,0x41b6],
  #[0x400,0,0,0,0x800,0,0,0,0x1000,0,0,0,0x2000,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0x4001,0,0,0x400,0x4001,0,0,0x800,0x4001,0,0,0x1000,0x4001,0,0,0x2000],
  #[0x821,0,0,0x21,0x412,0,0,0x12,0x207b,0,0,0x7b,0x1048,0,0,0x48],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0x4032,0,0,0x833,0x4001,0,0,0x400,0x4068,0,0,0x2069,0x405b,0,0,0x105a],
  #[0x1101,0,0,0x101,0x215b,0,0,0x15b,0x484,0,0,0x84,0x8de,0,0,0xde],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0x4184,0,0,0x1185,0x41de,0,0,0x21df,0x4001,0,0,0x400,0x405b,0,0,0x85a],
  #[0x23be,0,0,0x3be,0x13d7,0,0,0x3d7,0xa61,0,0,0x261,0x608,0,0,0x208],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0x41b7,0,0,0x21b6,0x41de,0,0,0x11df,0x4068,0,0,0x869,0x4001,0,0,0x400]
]
private def freePins : Array Nat := #[3,7,11,15,48,52,56,60,112,176,240,259,263,267,271]
private def corePins : Array Nat := #[0,4,8,12,64,68,72,128,136,192,256,260,264,268]

private def atData (a : Array (Array Nat)) (i : Nat) := (a[i/16]?.getD #[])[i%16]?.getD 0
private def ext (i : Nat) := atData extData i
private def err (i : Nat) := atData errData i
private def freePin (j : Nat) := freePins[j]?.getD 0
private def corePin (j : Nat) := corePins[j]?.getD 0
private def freeAtom (j : Nat) := double.coefficient (freePin j)
private def coreAtom (j : Nat) := if j=14 then
  double.coefficient (key false 0 3) ^^^ double.coefficient (key false 3 0) ^^^
    double.coefficient (key false 3 3) else double.coefficient (corePin j)

private def combo (a : Nat → Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,m => combo a k m ^^^ (if m.testBit k then a k else 0)

private theorem dot0 (w : Nat → Bool) (k : Nat) : dot w k 0=false := by
  induction k <;> simp_all [dot]

private theorem combo_dot (w : Nat → Bool) (k : Nat) (a : Nat → Nat) (n m : Nat) :
    dot w k (combo a n m)=dot (fun j => dot w k (a j)) n m := by
  induction n with
  | zero => exact dot0 _ _
  | succ n ih =>
    rw [combo,dot_xor,ih]
    cases b : m.testBit n <;> simp [b,dot0,dot]

private theorem dot_absent (w : Nat → Bool) (n m : Nat) (none : ∀ j, j<n → w j=false) :
    dot w n m=false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dot,ih (fun j hj => none j (by omega)),none n (by omega)]
    simp

private theorem ext_good : ∀ x y d : B,
    (Rigidity.Kernel.square true x y d).mask ext=0 := by decide +kernel
private theorem ext_zero : ∀ (tag : Bool) (x y : B),
    ((inside .a x=true ∧ inside .a y=true) ∨ (inside .b x=true ∧ inside .b y=true)) →
    ext (key tag x y)=0 := by decide +kernel
private theorem corrected : ∀ (tag : Bool) (x y : B), inside .c x=true → inside .c y=true →
    let i := key tag x y
    double.coefficient i=combo freeAtom 15 (ext i) ^^^ combo coreAtom 15 (err i) := by decide +kernel

def zero : Pair := (fun _ _ => false,fun _ _ => false)
def diagonal (h : Pair) := h.1 0 3 ^^ h.1 3 0 ^^ h.1 3 3

/-- A diagonal patch from any homogeneous full table which is zero on face A
can be realized with zero on A and B precisely when the three remaining
diagonal row entries sum to zero. This direction constructs the repair. -/
theorem repair (h : ZeroPair true) (vanish : agree .a h.val zero)
    (obstruction : diagonal h.val=false) :
    ∃ t : ZeroPair true, agree .a t.val zero ∧ agree .b t.val zero ∧ agree .c t.val h.val := by
  let v := lookup h.val
  let bits := double.read v
  let w := bits.getLsbD
  have good : Rigidity.Kernel.Good true v := by
    intro x y d hd
    rw [Rigidity.Enumeration.eval_lookup true h.val h.property.1]
    exact h.property.2 _ _ _ hd
  have encoded (i : Nat) (hi : i<512) : dot w 62 (double.coefficient i)=v i :=
    Rigidity.Kernel.generate_read double Rigidity.Kernel.double_valid v good i hi
  have keyBound : ∀ (t : Bool) (x y : B), key t x y<512 := by decide
  have real (tag : Bool) (x y : B) : dot w 62 (double.coefficient (key tag x y)) =
      (if tag then h.val.2 else h.val.1) x y :=
    (encoded _ (keyBound tag x y)).trans (Rigidity.Enumeration.lookup_key h.val tag x y)
  have killed (j : Nat) (hj : j<15) : dot w 62 (coreAtom j)=false := by
    by_cases last : j=14
    · subst j
      change dot w 62 (_ ^^^ _ ^^^ _) = _
      rw [dot_xor,dot_xor,real,real,real]
      exact obstruction
    · have bound : j<14 := by omega
      have live : ∀ u : Fin 14, let i := corePin u.val
          i<512 ∧ inside .a (BitVec.ofNat 4 (i/16))=true ∧ inside .a (BitVec.ofNat 4 i)=true := by decide
      obtain ⟨hsize,hx,hy⟩ := live ⟨j,bound⟩
      rw [coreAtom,ite_eq_right last,encoded _ hsize]
      have hz := vanish _ _ hx hy
      change (if corePin j<256 then h.val.1 else h.val.2) _ _=false
      by_cases first : corePin j<256
      · rw [ite_eq_left first]; exact hz.1
      · rw [ite_eq_right first]; exact hz.2
  let read := fun j => dot w 62 (freeAtom j)
  let pay := fun (i : Nat) => dot read 15 (ext i)
  let out := Rigidity.Enumeration.tabulate true pay
  have outGood : ∀ x y d : B, d≠0 → TwoPhases.score out.1 out.2 (x,y,d)=false := by
    intro x y d _
    have chk := congrArg (dot read 15) (ext_good x y d)
    change (pay (key false x y) ^^ (pay (key false (x^^^d) (y^^^d)) ^^
      (pay (key true x (y^^^d)) ^^ (pay (key true (x^^^d) y) ^^ false)))) = false
    simpa only [Rigidity.Kernel.square,Rigidity.Kernel.Quad.mask,dot_xor,dot0,pay,Bool.xor_assoc,
      Bool.xor_false] using chk
  let t : ZeroPair true := ⟨out,fun eqn => by contradiction,outGood⟩
  have freeFalse (tag : Bool) (x y : B) (dom : (inside .a x=true ∧ inside .a y=true) ∨
      (inside .b x=true ∧ inside .b y=true)) : pay (key tag x y)=false := by
    change dot read 15 (ext (key tag x y))=false
    rw [ext_zero tag x y dom,dot0]
  refine ⟨t,fun x y hx hy => ⟨freeFalse _ x y (Or.inl ⟨hx,hy⟩),freeFalse _ x y (Or.inl ⟨hx,hy⟩)⟩,
    fun x y hx hy => ⟨freeFalse _ x y (Or.inr ⟨hx,hy⟩),freeFalse _ x y (Or.inr ⟨hx,hy⟩)⟩,?_⟩
  intro x y hx hy
  have cell (tag : Bool) : pay (key tag x y)=(if tag then h.val.2 else h.val.1) x y := by
    have equality := congrArg (dot w 62) (corrected tag x y hx hy)
    rw [real,dot_xor,combo_dot,combo_dot,dot_absent _ _ _ killed,Bool.xor_false] at equality
    exact equality.symm
  exact ⟨cell false,cell true⟩

private def diff {d : B} (p q : Pair) (hp : DirectionPattern p.1 p.2 d)
    (hq : DirectionPattern q.1 q.2 d) : ZeroPair true :=
  ⟨plus p q,fun h => by contradiction,by
    intro x y e he
    rw [Rigidity.Enumeration.score_plus,hp.2 x y e he,hq.2 x y e he,Bool.xor_self]⟩

private theorem add_preserves {d : B} (p : Pair) (hp : DirectionPattern p.1 p.2 d) (h : ZeroPair true) :
    DirectionPattern (plus p h.val).1 (plus p h.val).2 d := by
  refine ⟨hp.1,?_⟩
  intro x y e he
  rw [Rigidity.Enumeration.score_plus,h.property.2 _ _ _ he,hp.2 _ _ _ he,Bool.xor_false]

private theorem diagonal_read {p base incoming : Pair} (ha : agree .a p base) (hb : agree .b p base)
    (hc : agree .c p incoming) : diagonal (plus base incoming)=(parity p ^^ parity base) := by
  simp only [diagonal,parity,plus,
    ←(hc 0 3 (by decide) (by decide)).1,←(hc 3 0 (by decide) (by decide)).1,←(hc 3 3 (by decide) (by decide)).1,
    ←(hb 1 1 (by decide) (by decide)).1,←(hb 1 1 (by decide) (by decide)).2,
    ←(ha 0 2 (by decide) (by decide)).2,←(ha 2 0 (by decide) (by decide)).2,←(ha 2 2 (by decide) (by decide)).2]
  simp [Bool.xor_comm,Bool.xor_left_comm]

def Extends (p : Pair) (d : B) : Prop := ∃ q : Pair, DirectionPattern q.1 q.2 d ∧ ∀ f : Face, agree f p q

/-- On the three actual hyperplanes with normals 1, 2, and 3, the single
eight-cell check is sufficient for any fixed pairwise-attainable direction. -/
theorem fixed_iff {p : Pair} {d : B} (pairs : PairFixed p d) :
    Extends p d ↔ parity p=decide (d=2 ∨ d=3) := by
  constructor
  · rintro ⟨q,h,faces⟩
    exact (boundary_parity (faces .a) (faces .b) (faces .c)).trans (pattern_parity q d h)
  · intro readout
    obtain ⟨base,basePat,ha,hb⟩ := pairs .a .b (by decide)
    obtain ⟨incoming,inPat,ha',hc⟩ := pairs .a .c (by decide)
    let h := diff base incoming basePat inPat
    have cleared : agree .a h.val zero := by
      intro x y hx hy
      obtain ⟨ar,ac⟩ := ha x y hx hy
      obtain ⟨br,bc⟩ := ha' x y hx hy
      change (base.1 x y ^^ incoming.1 x y)=false ∧ (base.2 x y ^^ incoming.2 x y)=false
      rw [←ar,←ac,←br,←bc,Bool.xor_self,Bool.xor_self]
      exact ⟨rfl,rfl⟩
    have obstruction : diagonal h.val=false := by
      change diagonal (plus base incoming)=false
      rw [diagonal_read ha hb hc,pattern_parity _ _ basePat,readout,Bool.xor_self]
    obtain ⟨t,ta,tb,tc⟩ := repair h cleared obstruction
    refine ⟨plus base t.val,add_preserves base basePat t,?_⟩
    have stay (f : Face) (was : agree f p base) (unmoved : agree f t.val zero) : agree f p (plus base t.val) := by
      intro x y hx hy
      obtain ⟨ar,ac⟩ := was x y hx hy
      obtain ⟨br,bc⟩ := unmoved x y hx hy
      change t.val.1 x y=false at br
      change t.val.2 x y=false at bc
      simp [plus,br,bc,ar,ac]
    intro f; cases f with
    | a => exact stay .a ha ta
    | b => exact stay .b hb tb
    | c =>
      intro x y hx hy
      obtain ⟨ar,ac⟩ := hc x y hx hy
      obtain ⟨br,bc⟩ := tc x y hx hy
      change t.val.1 x y=(base.1 x y ^^ incoming.1 x y) at br
      change t.val.2 x y=(base.2 x y ^^ incoming.2 x y) at bc
      simp [plus,br,bc,ar,ac]

/-- Project to face g along the two-bit line belonging to face f. On f,
the image lies in the common core. -/
private def retract (f g : Face) (x : B) := if inside g x then x else x ^^^faceDirection f

private theorem retract_spec (f g : Face) (distinct : f≠g) :
    (∀ x y, retract f g (x^^^y)=retract f g x ^^^retract f g y) ∧
    (∀ x, inside g (retract f g x)=true) ∧
    (∀ x, inside f x=true → inside f (retract f g x)=true) := by
  cases f <;> cases g <;> first | contradiction | decide +kernel

private def pull (w : B → B) (p : Pair) : Pair :=
  (fun x y => p.1 (w x) (w y),fun x y => p.2 (w x) (w y))

private theorem pull_hom (w : B → B) (linear : ∀ x d, w (x^^^d)=w x^^^w d)
    (h : ZeroPair true) : ∀ x y d : B, TwoPhases.score (pull w h.val).1 (pull w h.val).2 (x,y,d)=false := by
  intro x y d
  have eqn : TwoPhases.score (pull w h.val).1 (pull w h.val).2 (x,y,d)=
      TwoPhases.score h.val.1 h.val.2 (w x,w y,w d) := by
    simp only [pull,TwoPhases.score,TwoPhases.corners,SignObstruction.total,linear]
  rw [eqn]
  by_cases nz : w d=0
  · simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,nz,Bool.xor_comm]
  · exact h.property.2 _ _ _ nz

/-- Consistent raw physical addresses are implicit in p. With fixed
direction, individual extendibility already implies pairwise extendibility. -/
theorem local_pair {p : Pair} {d : B} (localDir : LocalFixed p d) : PairFixed p d := by
  intro f g distinct
  obtain ⟨a,pa,ha⟩ := localDir f
  obtain ⟨b,pb,hb⟩ := localDir g
  let raw := diff a b pa pb
  let w := retract f g
  obtain ⟨linear,into,preserve⟩ := retract_spec f g distinct
  let pulled : ZeroPair true := ⟨pull w raw.val,fun h => by contradiction,
    fun x y e _ => pull_hom w linear raw x y e⟩
  refine ⟨plus a pulled.val,add_preserves a pa pulled,?_,?_⟩
  · intro x y hx hy
    have agree0 := ha x y hx hy
    have s := ha (w x) (w y) (preserve x hx) (preserve y hy)
    have t := hb (w x) (w y) (into x) (into y)
    change p.1 x y=(a.1 x y ^^ (a.1 (w x) (w y) ^^ b.1 (w x) (w y))) ∧
      p.2 x y=(a.2 x y ^^ (a.2 (w x) (w y) ^^ b.2 (w x) (w y)))
    simp [←s.1,←s.2,←t.1,←t.2,agree0]
  · intro x y hx hy
    have e := hb x y hx hy
    have ex : w x=x := by simp [w,retract,hx]
    have ey : w y=y := by simp [w,retract,hy]
    change p.1 x y=(a.1 x y ^^ (a.1 (w x) (w y) ^^ b.1 (w x) (w y))) ∧
      p.2 x y=(a.2 x y ^^ (a.2 (w x) (w y) ^^ b.2 (w x) (w y)))
    simp [ex,ey,e.1,e.2]

/-- The complete fixed-direction test, quantified over arbitrary boundary
pairs and allowing unrelated entries elsewhere on the physical board. -/
theorem fixed_classification (p : Pair) (d : B) : Extends p d ↔
    LocalFixed p d ∧ parity p=decide (d=2 ∨ d=3) := by
  constructor
  · rintro ⟨q,pat,acts⟩
    exact ⟨fun f => ⟨q,pat,acts f⟩,
      (boundary_parity (acts .a) (acts .b) (acts .c)).trans (pattern_parity q d pat)⟩
  · rintro ⟨localDir,par⟩
    exact (fixed_iff (local_pair localDir)).mpr par

/-- A free global direction can be tried among the fifteen nonzero words.
The tests are individual face liftability and one eight-cell parity. -/
theorem free_classification (p : Pair) : GloballyOpt p ↔
    ∃ d : B, LocalFixed p d ∧ parity p=decide (d=2 ∨ d=3) := by
  constructor
  · rintro ⟨d,q,pat,acts⟩
    exact ⟨d,(fixed_classification p d).mp ⟨q,pat,acts⟩⟩
  · rintro ⟨d,h⟩
    exact ⟨d,(fixed_classification p d).mpr h⟩

/-- The completely local, directly evaluable test: every nonzero step of
each face has precisely the failure bit prescribed by the candidate d. -/
def LocalScores (p : Pair) (d : B) : Prop :=
  d≠0 ∧ ∀ (f : Face) (x y e : B), inside f x=true → inside f y=true → inside f e=true →
    e≠0 → TwoPhases.score p.1 p.2 (x,y,e)=decide (e≠d)

theorem local_scores_iff (p : Pair) (d : B) : LocalFixed p d ↔ LocalScores p d := by
  constructor
  · intro l
    obtain ⟨a,pat,_⟩ := l .a
    refine ⟨pat.1,?_⟩
    intro f x y e hx hy he nz
    obtain ⟨b,pb,agreeB⟩ := l f
    exact (shared_score f agreeB x y e hx hy he).trans (pb.2 x y e nz)
  · rintro ⟨nz,localLaw⟩ f
    let h := Rigidity.Enumeration.ground ⟨d,nz⟩
    have hpat : DirectionPattern h.1 h.2 d := Rigidity.Enumeration.ground_pattern ⟨d,nz⟩
    let t := plus p h
    let other := if f=.a then Face.b else Face.a
    have distinct : other≠f := by cases f <;> decide
    let w := retract other f
    obtain ⟨linear,range,_⟩ := retract_spec other f distinct
    have lin : ∀ a b, w (a^^^b)=w a^^^w b := linear
    have sound (x y e : B) : TwoPhases.score (pull w t).1 (pull w t).2 (x,y,e)=false := by
      have eqn : TwoPhases.score (pull w t).1 (pull w t).2 (x,y,e) =
          TwoPhases.score t.1 t.2 (w x,w y,w e) := by
        simp only [pull,TwoPhases.score,TwoPhases.corners,SignObstruction.total,lin]
      rw [eqn]
      by_cases empty : w e=0
      · simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,empty,Bool.xor_comm]
      · rw [Rigidity.Enumeration.score_plus,localLaw f _ _ _ (range x) (range y) (range e) empty,
            hpat.2 (w x) (w y) (w e) empty,Bool.xor_self]
    let patch : ZeroPair true := ⟨pull w t,fun hh => by contradiction,fun x y e _ => sound x y e⟩
    refine ⟨plus h patch.val,add_preserves h hpat patch,?_⟩
    intro x y hx hy
    have ex : w x=x := by simp [w,retract,hx]
    have ey : w y=y := by simp [w,retract,hy]
    change p.1 x y=(h.1 x y ^^ (p.1 (w x) (w y) ^^ h.1 (w x) (w y))) ∧
      p.2 x y=(h.2 x y ^^ (p.2 (w x) (w y) ^^ h.2 (w x) (w y)))
    have cancel (a b : Bool) : (a ^^ (b ^^ a))=b := by cases a <;> cases b <;> decide
    simp only [ex,ey,cancel,and_self]

theorem fixed_observable (p : Pair) (d : B) :
    Extends p d ↔ LocalScores p d ∧ parity p=decide (d=2 ∨ d=3) := by
  rw [fixed_classification,local_scores_iff]

theorem free_observable (p : Pair) : GloballyOpt p ↔
    ∃ d : B, LocalScores p d ∧ parity p=decide (d=2 ∨ d=3) := by
  simp only [free_classification,local_scores_iff]

end Mobius.ThreeFaceCompletion
