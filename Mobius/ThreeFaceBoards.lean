import Mobius.Rigidity
import Mobius.EightSquare

/-! Four-planes with common two-dimensional core. Their other two
coordinates range over a projective line of the binary quotient space.
Every board thus has three genuine three-dimensional station faces. -/
namespace Mobius.ThreeFaceBoards
open Mobius.SignObstruction (B)
open Mobius.Rigidity (DirectionPattern)
abbrev U := BitVec 2
abbrev V (n : Nat) := U × BitVec n
abbrev World (n : Nat) := V n → V n → Bool

structure Line (n : Nat) where
  a : BitVec n
  b : BitVec n
  pos : 0<a.toNat
  ab : a.toNat<b.toNat
  bc : b.toNat<(a^^^b).toNat

def Line.word (L : Line n) (i : U) : BitVec n :=
  if i=0 then 0 else if i=1 then L.a else if i=2 then L.b else L.a^^^L.b

private theorem four : ∀ u : U, u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by decide

theorem order_word (L : Line n) (x y : U) :
    (L.word x).toNat < (L.word y).toNat ↔ x.toNat<y.toNat := by
  have p := L.pos; have ab := L.ab; have bc := L.bc
  have bcn := bc
  simp only [BitVec.toNat_xor] at bcn
  rcases four x with rfl|rfl|rfl|rfl <;> rcases four y with rfl|rfl|rfl|rfl <;>
    simp [Line.word] <;> omega

theorem word_inj (L : Line n) {x y : U} (eq : L.word x=L.word y) : x=y := by
  apply BitVec.eq_of_toNat_eq
  have l : ¬ x.toNat < y.toNat := fun h => Nat.lt_irrefl _ (eq ▸ (order_word L x y).mpr h)
  have r : ¬ y.toNat < x.toNat := fun h => Nat.lt_irrefl _ (eq ▸ (order_word L y x).mpr h)
  omega

theorem word_add (L : Line n) (x y : U) : L.word (x ^^^ y)=L.word x ^^^ L.word y := by
  have eraseL (a b : BitVec n) : a ^^^ (a ^^^ b)=b := by rw [←BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]
  have eraseR (a b : BitVec n) : a ^^^ (b ^^^ a)=b := by rw [BitVec.xor_comm b a,eraseL]
  rcases four x with rfl|rfl|rfl|rfl <;> rcases four y with rfl|rfl|rfl|rfl <;>
    simp [Line.word,eraseL,eraseR,BitVec.xor_comm]

def core (x : B) : U := x.setWidth 2
def plane (x : B) : U := (x >>> 2).setWidth 2
def pack (u j : U) : B := j ++ u
private theorem unpack : ∀ x : B, pack (core x) (plane x)=x := by decide
private theorem core_pack : ∀ u j : U, core (pack u j)=u := by decide
private theorem plane_pack : ∀ u j : U, plane (pack u j)=j := by decide
def embed (L : Line n) (x : B) : V n := (core x,L.word (plane x))
def restrict (g : World n) (L : Line n) := fun x y => g (embed L x) (embed L y)

theorem embed_pack (L : Line n) (u j : U) : embed L (pack u j)=(u,L.word j) := by
  simp [embed,core_pack,plane_pack]

theorem embed_zero (L : Line n) : embed L 0 = (0,0) := rfl

theorem embed_injective (L : Line n) {x y : B} (h : embed L x = embed L y) : x=y := by
  have c : core x=core y := congrArg (fun z : V n => z.1) h
  have p : plane x=plane y := word_inj L (congrArg (fun z : V n => z.2) h)
  rw [←unpack x,←unpack y,c,p]

theorem embed_add (L : Line n) (x y : B) :
    embed L (x^^^y) = ((embed L x).1^^^(embed L y).1,(embed L x).2^^^(embed L y).2) := by
  have add : ∀ a b : B, core (a^^^b)=core a^^^core b ∧ plane (a^^^b)=plane a^^^plane b := by decide
  exact Prod.ext (add x y).1 (by simp only [embed,(add x y).2,word_add])

/-- Independently orient every three-point line cyclically by numeric order.
Zero is the unit, every nonzero basis element squares to minus one. -/
def quat (x y : BitVec n) : Bool :=
  if x=0 ∨ y=0 then false else if x=y then true
  else decide (((x.toNat<y.toNat) && (y.toNat<(x^^^y).toNat)) ||
               ((y.toNat<(x^^^y).toNat) && ((x^^^y).toNat<x.toNat)) ||
               (((x^^^y).toNat<x.toNat) && (x.toNat<y.toNat)))

private theorem q_on_line (L : Line n) (x y : U) : quat (L.word x) (L.word y) = quat x y := by
  have eq (a b : U) : L.word a=L.word b ↔ a=b := ⟨word_inj L,fun h => congrArg _ h⟩
  have zer (a : U) : L.word a=0 ↔ a=0 := eq a 0
  simp only [quat,zer,eq,←word_add,order_word]

/-- Cayley–Dickson multiplication signs on one doubled copy of the
linewise quaternion basis, using a single table for all lines. -/
def twice (x : BitVec n) (t : Bool) (y : BitVec n) (s : Bool) : Bool :=
  (if s then quat y x else quat x y) ^^ (t && decide (y≠0)) ^^ (t && s)

def coreQuot (h u : U) : Bool :=
  if h=1 then u.getLsbD 1 else if h=2 then u.getLsbD 0 else u.getLsbD 0 ^^ u.getLsbD 1

def witness (h : U) : World n := fun x y => twice x.2 (coreQuot h x.1) y.2 (coreQuot h y.1)
def localPhase (h : U) (x y : B) :=
  twice (plane x) (coreQuot h (core x)) (plane y) (coreQuot h (core y))

theorem witness_restrict (L : Line n) (h : U) : restrict (witness h) L = localPhase h := by
  funext x y
  have nz : L.word (plane y) ≠ 0 ↔ plane y≠0 := not_congr
    (show L.word (plane y)=L.word 0 ↔ plane y=0 from ⟨word_inj L,fun e => congrArg _ e⟩)
  change twice (L.word (plane x)) _ (L.word (plane y)) _ = twice (plane x) _ (plane y) _
  simp only [twice,q_on_line,nz]
  rfl

set_option maxRecDepth 16384 in
private theorem checked_local : ∀ h : U, h≠0 → DirectionPattern (localPhase h) (localPhase h) (pack h 0) := by
  unfold DirectionPattern
  decide +kernel

theorem witness_optimal (L : Line n) (h : U) (nz : h≠0) :
    DirectionPattern (restrict (witness h) L) (restrict (witness h) L) (pack h 0) ∧
    TwoPhases.failures (restrict (witness h) L) (restrict (witness h) L) = 256 := by
  rw [witness_restrict]
  have p := checked_local h nz
  exact ⟨p,Rigidity.optimal_of_direction p⟩

/-- If the original core U is installed in the *quotient* low two bits
of the Fano attachment, this is its actual shared two-dimensional plane. -/
def oldCore (z : U) : V 3 := (0,z.setWidth 3)

/-- All sixteen shared cells coincide with the canonical octonion phase
on the original low two bits. The same equality holds for both tags. -/
theorem attachment_on_core : ∀ (h x y : U),
    (witness h : World 3) (oldCore x) (oldCore y) = EightSquare.phase (x.setWidth 3) (y.setWidth 3) := by
  decide +kernel

private def axisA (i : Fin 7) : BitVec 3 := ([1,1,1,2,2,3,3] : List (BitVec 3)).getD i.val 0
private def axisB (i : Fin 7) : BitVec 3 := ([2,4,6,4,5,4,5] : List (BitVec 3)).getD i.val 0
private theorem fano_data : ∀ i, 0<(axisA i).toNat ∧ (axisA i).toNat<(axisB i).toNat ∧
    (axisB i).toNat < (axisA i^^^axisB i).toNat := by decide
def fano (i : Fin 7) : Line 3 := ⟨axisA i,axisB i,(fano_data i).1,(fano_data i).2.1,(fano_data i).2.2⟩

theorem fano_attached (h : U) (hn : h≠0) :
    ∃ p : World 3, (∀ i, DirectionPattern (restrict p (fano i)) (restrict p (fano i)) (pack h 0) ∧
      TwoPhases.failures (restrict p (fano i)) (restrict p (fano i)) = 256) ∧
      ∀ x y, p (oldCore x) (oldCore y) = EightSquare.phase (x.setWidth 3) (y.setWidth 3) :=
  ⟨witness h,fun i => witness_optimal (fano i) h hn,attachment_on_core h⟩


def add (x y : V n) : V n := (x.1^^^y.1,x.2^^^y.2)
def worldScore (r c : World n) (x y d : V n) :=
  r x y ^^ (r (add x d) (add y d) ^^ (c x (add y d) ^^ c (add x d) y))

theorem score_restrict (r c : World n) (L : Line n) (x y d : B) :
    TwoPhases.score (restrict r L) (restrict c L) (x,y,d) =
      worldScore r c (embed L x) (embed L y) (embed L d) := by
  simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,worldScore,restrict,embed_add,add]

def originBad (r c : World n) (w : V n) := !(worldScore r c (0,0) (0,0) w)

private theorem read_direction (r c : World n) (L : Line n) {d : B}
    (pat : DirectionPattern (restrict r L) (restrict c L) d) (s : B) (nz : s≠0) :
    originBad r c (embed L s) = decide (s=d) := by
  have h := pat.2 0 0 s nz
  rw [score_restrict,embed_zero] at h
  unfold originBad
  rw [h]
  by_cases eq : s=d <;> simp [eq]

private def coreWords : List U := [0,1,2,3]
def active (r c : World n) (w : BitVec n) := coreWords.any (fun u => originBad r c (u,w))

private theorem active_face (r c : World n) (L : Line n) {d : B}
    (pat : DirectionPattern (restrict r L) (restrict c L) d) (j : U) (nz : j≠0) :
    active r c (L.word j) = decide (j=plane d) := by
  have nonzero : ∀ u j : U, j≠0 → pack u j≠0 := by decide
  have anyBit : ∀ j : U, ∀ d : B, coreWords.any (fun u => decide (pack u j=d))=decide (j=plane d) := by decide
  have read (u : U) : originBad r c (u,L.word j)=decide (pack u j=d) := by
    rw [←embed_pack L u j]
    exact read_direction r c L pat _ (nonzero u j nz)
  unfold active
  rw [show (fun u => originBad r c (u,L.word j)) = (fun u => decide (pack u j=d)) from funext read]
  exact anyBit _ _

private theorem fano_no_transversal (z : BitVec 3 → Bool)
    (one : ∀ i, (z ((fano i).word 1)).toNat+(z ((fano i).word 2)).toNat+(z ((fano i).word 3)).toNat=1) : False := by
  have a := one 0; have b := one 1; have c := one 2; have d := one 3
  have e := one 4; have f := one 5; have g := one 6
  change (z 1).toNat+(z 2).toNat+(z 3).toNat=1 at a
  change (z 1).toNat+(z 4).toNat+(z 5).toNat=1 at b
  change (z 1).toNat+(z 6).toNat+(z 7).toNat=1 at c
  change (z 2).toNat+(z 4).toNat+(z 6).toNat=1 at d
  change (z 2).toNat+(z 5).toNat+(z 7).toNat=1 at e
  change (z 3).toNat+(z 4).toNat+(z 7).toNat=1 at f
  change (z 3).toNat+(z 5).toNat+(z 6).toNat=1 at g
  omega

/-- With all seven Fano boards individually optimal, even arbitrary
independent global row and column phases force the same nonzero core
direction on all boards. No boundary or direction is prescribed. -/
theorem fano_forces_core (r c : World 3)
    (opt : ∀ i, TwoPhases.failures (restrict r (fano i)) (restrict c (fano i))=256) :
    ∃ h : U, h≠0 ∧ ∀ i, DirectionPattern (restrict r (fano i)) (restrict c (fano i)) (pack h 0) := by
  have choose (i : Fin 7) := Rigidity.optimal_direction _ _ (opt i)
  let ds i := Classical.choose (choose i)
  have pat (i : Fin 7) : DirectionPattern (restrict r (fano i)) (restrict c (fano i)) (ds i) :=
    (Classical.choose_spec (choose i)).1
  have inCore : ∃ i, plane (ds i)=0 := by
    apply Classical.byContradiction
    intro none
    apply fano_no_transversal (active r c)
    intro i
    have single : ∀ w : U, w≠0 → (decide ((1:U)=w)).toNat+(decide ((2:U)=w)).toNat+
        (decide ((3:U)=w)).toNat=1 := by decide
    rw [active_face r c _ (pat i) 1 (by decide),active_face r c _ (pat i) 2 (by decide),
      active_face r c _ (pat i) 3 (by decide)]
    exact single _ (fun eq => none ⟨i,eq⟩)
  obtain ⟨i,hi⟩ := inCore
  let h := core (ds i)
  have back : pack h 0=ds i := by rw [←hi]; exact unpack _
  have nz : pack h 0≠0 := fun eq => (pat i).1 (back.symm.trans eq)
  have hn : h≠0 := fun eq => nz (by rw [eq]; rfl)
  have found : originBad r c (h,0)=true := by
    have obs := read_direction r c (fano i) (pat i) (pack h 0) nz
    rw [embed_pack,decide_eq_true back] at obs
    exact obs
  refine ⟨h,hn,fun j => ?_⟩
  have obs := read_direction r c (fano j) (pat j) (pack h 0) nz
  rw [embed_pack] at obs
  have eq : pack h 0=ds j := of_decide_eq_true (obs.symm.trans found)
  rw [eq]
  exact pat j

private theorem original_embedding : ∀ x : U, embed (fano 0) (pack 0 x)=oldCore x := by decide

/-- The exposed two-plane inside the quotient Fano space is entirely good:
all its shared square scores at all its anchors are true. -/
theorem attachment_forces_good (r c : World 3)
    (opt : ∀ i, TwoPhases.failures (restrict r (fano i)) (restrict c (fano i))=256)
    (x y d : U) (nz : d≠0) :
    worldScore r c (oldCore x) (oldCore y) (oldCore d)=true := by
  obtain ⟨h,_,all⟩ := fano_forces_core r c opt
  have outside : ∀ h d : U, d≠0 → pack 0 d≠0 ∧ pack 0 d≠pack h 0 := by decide
  have p := (all 0).2 (pack 0 x) (pack 0 y) (pack 0 d) (outside h d nz).1
  rw [score_restrict,original_embedding,original_embedding,original_embedding,decide_eq_true (outside h d nz).2] at p
  exact p


/-- The true data on the exposed face: sixteen row entries and sixteen
independent column entries. -/
abbrev Surface := U → U → Bool
def surfaceScore (r c : Surface) (x y d : U) :=
  r x y ^^ (r (x^^^d) (y^^^d) ^^ (c x (y^^^d) ^^ c (x^^^d) y))
def SurfaceGood (r c : Surface) := ∀ x y d, d≠0 → surfaceScore r c x y d=true

def canonical (x y : U) := EightSquare.phase (x.setWidth 3) (y.setWidth 3)
private theorem canonical_good : SurfaceGood canonical canonical := by unfold SurfaceGood; decide +kernel

private theorem xor_shuffle (a b c d x y z w : Bool) :
    ((a^^x) ^^ ((b^^y) ^^ ((c^^z) ^^ (d^^w)))) =
    ((a ^^ (b ^^ (c ^^ d))) ^^ (x ^^ (y ^^ (z ^^ w)))) := by
  revert a b c d x y z w; decide

private theorem surface_sum (r c s t : Surface) (x y d : U) :
    surfaceScore (fun a b => r a b ^^ s a b) (fun a b => c a b ^^ t a b) x y d =
    (surfaceScore r c x y d ^^ surfaceScore s t x y d) := xor_shuffle ..

private theorem zero_step (r c : Surface) (x y : U) : surfaceScore r c x y 0=false := by
  simp [surfaceScore]

def retract (x : V 3) : U := x.2.setWidth 2
def correction (s : Surface) (x y : V 3) := s (retract x) (retract y) ^^ canonical (retract x) (retract y)
def extendSurface (h : U) (s : Surface) : World 3 := fun x y => witness h x y ^^ correction s x y

private theorem correction_zero (r c : Surface) (good : SurfaceGood r c) (x y d : V 3) :
    worldScore (correction r) (correction c) x y d=false := by
  have lin : ∀ u v : BitVec 3, (u^^^v).setWidth 2 = (u.setWidth 2 ^^^ v.setWidth 2) := by decide
  have eqn : worldScore (correction r) (correction c) x y d =
      surfaceScore (fun u v => r u v ^^ canonical u v) (fun u v => c u v ^^ canonical u v)
        (retract x) (retract y) (retract d) := by
    simp only [worldScore,surfaceScore,correction,add,retract,lin]
  rw [eqn,surface_sum]
  by_cases off : retract d=0
  · rw [off,zero_step,zero_step]; rfl
  · rw [good _ _ _ off,canonical_good _ _ _ off]; rfl

theorem extend_scores (h : U) (r c : Surface) (good : SurfaceGood r c) (x y d : V 3) :
    worldScore (extendSurface h r) (extendSurface h c) x y d =
      worldScore (witness h) (witness h) x y d := by
  unfold extendSurface worldScore
  rw [xor_shuffle]
  change (_ ^^ worldScore (correction r) (correction c) x y d) = _
  rw [correction_zero r c good]; exact Bool.xor_false ..

private theorem retract_old : ∀ x : U, retract (oldCore x)=x := by decide

theorem extend_cells (h : U) (s : Surface) (x y : U) : extendSurface h s (oldCore x) (oldCore y)=s x y := by
  simp only [extendSurface,attachment_on_core,correction,retract_old,canonical]
  cases s x y <;> cases EightSquare.phase (x.setWidth 3) (y.setWidth 3) <;> rfl

private theorem old_add : ∀ a b : U, add (oldCore a) (oldCore b)=oldCore (a^^^b) := by decide

/-- Exact boundary projection of this attachment. Every independently
specified pair of boundary tables satisfying the exposed equations extends
cell-for-cell, with any of the three allowable internal bad directions. -/
theorem surface_extension_iff (r c : Surface) (h : U) (hn : h≠0) :
    SurfaceGood r c ↔ ∃ R C : World 3,
      (∀ i, DirectionPattern (restrict R (fano i)) (restrict C (fano i)) (pack h 0)) ∧
      (∀ x y, R (oldCore x) (oldCore y)=r x y) ∧ (∀ x y, C (oldCore x) (oldCore y)=c x y) := by
  constructor
  · intro good
    refine ⟨extendSurface h r,extendSurface h c,fun i => ?_,extend_cells h r,extend_cells h c⟩
    have pat := (witness_optimal (fano i) h hn).1
    refine ⟨pat.1,fun x y d dn => ?_⟩
    rw [score_restrict,extend_scores h r c good,←score_restrict]
    exact pat.2 x y d dn
  · rintro ⟨R,C,all,left,right⟩ x y d dn
    have good := attachment_forces_good R C (fun i => Rigidity.optimal_of_direction (all i)) x y d dn
    simpa only [worldScore,old_add,left,right,surfaceScore] using good

end Mobius.ThreeFaceBoards
