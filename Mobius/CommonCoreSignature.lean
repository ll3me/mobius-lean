import Mobius.CommonCore

/-! A single readout shared by the three nonparallel 3-faces.
    The seven tests in the quotient plane use actual tagged cells.
    A homogeneous binary correction realizes every consistent readout shift. -/
namespace Mobius.CommonCoreSignature
set_option maxHeartbeats 2000000

open SignObstruction (B)
open CommonCore (Addr Table Core)
open Rigidity (DirectionPattern)

def localRead (r : B → B → Bool) (p : B) := r 0 0 ^^ r 0 p ^^ r p 0 ^^ r p p

def signature (o p : Point) (r : Table Point) :=
  r (0,o) (0,o) ^^ r (0,o) (0,p) ^^ r (0,p) (0,o) ^^ r (0,p) (0,p)

theorem seven_scores (r c : B → B → Bool) :
    (localRead r 4 ^^ localRead r 8 ^^ localRead r 12) =
    (TwoPhases.score r c (8,12,4) ^^
      TwoPhases.score r c (0,0,8) ^^
      TwoPhases.score r c (0,8,8) ^^
      TwoPhases.score r c (4,4,8) ^^
      TwoPhases.score r c (0,4,12) ^^
      TwoPhases.score r c (0,12,12) ^^
      TwoPhases.score r c (4,0,12)) := by
  change _=((r 8 12 ^^ (r 12 8 ^^ (c 8 8 ^^ (c 12 12 ^^ false)))) ^^
    (r 0 0 ^^ (r 8 8 ^^ (c 0 8 ^^ (c 8 0 ^^ false)))) ^^
    (r 0 8 ^^ (r 8 0 ^^ (c 0 0 ^^ (c 8 8 ^^ false)))) ^^
    (r 4 4 ^^ (r 12 12 ^^ (c 4 12 ^^ (c 12 4 ^^ false)))) ^^
    (r 0 4 ^^ (r 12 8 ^^ (c 0 8 ^^ (c 12 4 ^^ false)))) ^^
    (r 0 12 ^^ (r 12 0 ^^ (c 0 0 ^^ (c 12 12 ^^ false)))) ^^
    (r 4 0 ^^ (r 8 12 ^^ (c 4 12 ^^ (c 8 0 ^^ false)))))
  unfold localRead
  generalize r 0 0=vr0_0, r 0 4=vr0_4, r 0 8=vr0_8, r 0 12=vr0_12, r 4 0=vr4_0, r 4 4=vr4_4, r 8 0=vr8_0, r 8 8=vr8_8, r 8 12=vr8_12, r 12 0=vr12_0, r 12 8=vr12_8, r 12 12=vr12_12, c 0 0=vc0_0, c 0 8=vc0_8, c 4 12=vc4_12, c 8 0=vc8_0, c 8 8=vc8_8, c 12 4=vc12_4, c 12 12=vc12_12
  simp [Bool.xor_comm,Bool.xor_left_comm]

theorem signature_law (r c : B → B → Bool) (d : B) (pat : DirectionPattern r c d) :
    (localRead r 4 ^^ localRead r 8 ^^ localRead r 12) = decide (d≠4 ∧ d≠8 ∧ d≠12) := by
  rw [seven_scores,pat.2 8 12 4 (by decide),
    pat.2 0 0 8 (by decide),
    pat.2 0 8 8 (by decide),
    pat.2 4 4 8 (by decide),
    pat.2 0 4 12 (by decide),
    pat.2 0 12 12 (by decide),
    pat.2 4 0 12 (by decide)]
  have finite : ∀ e : B, (decide ((4:B)≠e) ^^ decide ((8:B)≠e) ^^ decide ((8:B)≠e) ^^ decide ((8:B)≠e) ^^ decide ((12:B)≠e) ^^ decide ((12:B)≠e) ^^ decide ((12:B)≠e))=decide (e≠4 ∧ e≠8 ∧ e≠12) := by decide
  exact finite d

theorem station_law (o : Point) (line : Fin 3 → Point) (r c : Table Point) (d : B)
    (h : DirectionPattern (CommonCore.restrict r o line) (CommonCore.restrict c o line) d) :
    (signature o (line 0) r ^^ signature o (line 1) r ^^ signature o (line 2) r) =
      decide (d≠4 ∧ d≠8 ∧ d≠12) := signature_law _ _ _ h

/-- A binary local gauge with zero syndrome on every square. -/
def rowBit (x y : Bool) := x && y
def colBit (x y : Bool) := x && !y

private theorem binary_zero (x y e : Bool) :
    (rowBit x y ^^ (rowBit (x^^e) (y^^e) ^^ (colBit x (y^^e) ^^ colBit (x^^e) y)))=false := by
  revert x y e; decide

def toggleRow (r : Table Point) (z : Point → Bool) : Table Point :=
  fun x y => r x y ^^ rowBit (z x.2) (z y.2)
def toggleCol (c : Table Point) (z : Point → Bool) : Table Point :=
  fun x y => c x y ^^ colBit (z x.2) (z y.2)

private def qbit (v : Fin 3 → Bool) (x : B) :=
  if x.toNat<4 then false else v (CommonCore.slot x)

private theorem qlinear (v : Fin 3 → Bool) (even : (v 0 ^^ v 1 ^^ v 2)=false) (x y : B) :
    qbit v (x^^^y) = (qbit v x ^^ qbit v y) := by
  have vtab (j : Fin 3) : v j = (if j=0 then v 0 else if j=1 then v 1 else v 2) := by
    have cases3 : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases cases3 with rfl|rfl|rfl <;> rfl
  have map : v=(fun j => if j=0 then v 0 else if j=1 then v 1 else v 2) := funext vtab
  have test : ∀ a b c : Bool, ∀ x y : B, (a^^b^^c)=false →
      let f := qbit (fun j => if j=0 then a else if j=1 then b else c)
      f (x^^^y)=(f x ^^ f y) := by decide
  conv => lhs; rw [map]
  conv => rhs; rw [map]
  exact test _ _ _ _ _ even

theorem toggle_score (o : Point) (line : Fin 3 → Point) (r c : Table Point)
    (z : Point → Bool) (zero : z o=false) (even : (z (line 0) ^^ z (line 1) ^^ z (line 2))=false)
    (x y e : B) :
    TwoPhases.score (CommonCore.restrict (toggleRow r z) o line) (CommonCore.restrict (toggleCol c z) o line)
      (x,y,e) = TwoPhases.score (CommonCore.restrict r o line) (CommonCore.restrict c o line) (x,y,e) := by
  let f := qbit (fun j => z (line j))
  have view (s : B) : z (CommonCore.embed o line s).2=f s := by
    by_cases core : s.toNat<4 <;> simp [CommonCore.embed,f,qbit,core,zero]
  have linear (s t : B) : f (s^^^t)=(f s ^^ f t) := qlinear _ even s t
  have expand (a a' b b' c c' d d' : Bool) :
      ((a^^a') ^^ ((b^^b') ^^ ((c^^c') ^^ (d^^d')))) =
      ((a ^^ (b ^^ (c ^^ d))) ^^ (a' ^^ (b' ^^ (c' ^^ d')))) := by
    simp [Bool.xor_left_comm,Bool.xor_comm]
  simp only [TwoPhases.score,TwoPhases.corners,SignObstruction.total,CommonCore.restrict,toggleRow,
    toggleCol,view,linear,Bool.xor_false,ite_true,ite_false,Bool.false_eq_true,expand,binary_zero]

theorem toggle_signature (o p : Point) (r : Table Point) (z : Point → Bool) (zero : z o=false) :
    signature o p (toggleRow r z)=(signature o p r ^^ z p) := by
  simp [signature,toggleRow,rowBit,zero,Bool.xor_left_comm,Bool.xor_comm]

end Mobius.CommonCoreSignature
