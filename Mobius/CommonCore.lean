import Mobius.Rigidity
import Mobius.EightSquare

/-! Three nonparallel 3-faces through a common 2-plane.
Coordinates 0..3 are the core in each local 4-board. Its other three
cosets have shared *physical* point names, common between incident boards. -/
namespace Mobius.CommonCore
open SignObstruction (B)
open Rigidity (DirectionPattern)

abbrev Core := BitVec 2
abbrev Addr (Point : Type u) := Core × Point
abbrev Table (Point : Type u) := Addr Point → Addr Point → Bool

def slot (x : B) : Fin 3 := if x.getLsbD 3 then (if x.getLsbD 2 then 2 else 1) else 0

def embed (o : Point) (line : Fin 3 → Point) (x : B) : Addr Point :=
  (x.setWidth 2,if x.toNat<4 then o else line (slot x))

def restrict (t : Table Point) (o : Point) (line : Fin 3 → Point) (x y : B) :=
  t (embed o line x) (embed o line y)

def Profiles (o : Point) (lines : I → Fin 3 → Point) (r c : Table Point) :=
  ∀ i, ∃ d : B, 4≤d.toNat ∧ DirectionPattern (restrict r o (lines i)) (restrict c o (lines i)) d

def OutsideOpt (o : Point) (lines : I → Fin 3 → Point) :=
  ∃ r c : Table Point, Profiles o lines r c

def OneOn (lines : I → Fin 3 → Point) (chosen : Point → Bool) :=
  ∀ i, ∃ a : Fin 3, ∀ s, chosen (lines i s)=decide (s=a)

def lift (s : Fin 3) (u : Core) : B := BitVec.ofNat 4 (4*(s.val+1)+u.toNat)

private theorem lift_properties : ∀ (s : Fin 3) (u : Core), lift s u≠0 ∧ 4≤(lift s u).toNat ∧
    (lift s u).setWidth 2=u ∧ slot (lift s u)=s := by decide

private theorem lift_recover : ∀ d : B, 4≤d.toNat → lift (slot d) (d.setWidth 2)=d := by decide

/-- Read one test in physical coordinates, using the common origin and one
    arbitrary point of the station. Both tables may be independent. -/
def probe (o p : Point) (r c : Table Point) (u : Core) :=
  let origin : Addr Point := (0,o)
  let atPoint : Addr Point := (u,p)
  r origin origin ^^ (r atPoint atPoint ^^ (c origin atPoint ^^ c atPoint origin))

def chosenBy (o : Point) (r c : Table Point) (p : Point) :=
  decide (∃ u : Core, probe o p r c u=false)

theorem read_probe (o : Point) (line : Fin 3 → Point) (r c : Table Point) (s : Fin 3) (u : Core) :
    TwoPhases.score (restrict r o line) (restrict c o line) (0,0,lift s u)=probe o (line s) r c u := by
  have e := lift_properties s u
  have atP : embed o line (lift s u)=(u,line s) := by
    simp [embed,e.2.2.1,e.2.2.2,Nat.not_lt_of_ge e.2.1]
  simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,restrict,atP,probe]
  rfl

theorem choice_of_profiles (o : Point) (lines : I → Fin 3 → Point) (r c : Table Point)
    (h : Profiles o lines r c) : OneOn lines (chosenBy o r c) := by
  intro i
  obtain ⟨d,out,hp⟩ := h i
  refine ⟨slot d,fun s => Bool.eq_iff_iff.mpr ?_⟩
  simp only [chosenBy,decide_eq_true_eq]
  constructor
  · rintro ⟨u,hit⟩
    rw [←read_probe o (lines i) r c s u,hp.2 _ _ _ (lift_properties s u).1] at hit
    have same : lift s u=d := Classical.byContradiction (fun diff => by simp [diff] at hit)
    exact (lift_properties s u).2.2.2.symm.trans (congrArg slot same)
  · rintro rfl
    refine ⟨d.setWidth 2,?_⟩
    rw [←read_probe o (lines i) r c, lift_recover d out,hp.2 _ _ _ hp.1]
    simp

def addBit (u : Core) (t : Bool) : BitVec 3 := BitVec.ofNat 3 (u.toNat+4*t.toNat)

def localImage (a : Fin 3) (x : B) := addBit (x.setWidth 2) (decide (4≤x.toNat ∧ slot x≠a))

def localTable (a : Fin 3) (x y : B) := EightSquare.phase (localImage a x) (localImage a y)

private theorem map_add : ∀ (a : Fin 3) (x y : B),
    localImage a (x^^^y)=(localImage a x ^^^ localImage a y) := by decide

private theorem map_zero : ∀ (a : Fin 3) (x : B), localImage a x=0 ↔ x=0 ∨ x=lift a 0 := by decide

private theorem odd : ∀ (x y s : BitVec 3), s≠0 →
    (EightSquare.phase x y ^^ (EightSquare.phase (x^^^s) (y^^^s) ^^
       (EightSquare.phase x (y^^^s) ^^ EightSquare.phase (x^^^s) y)))=true := by decide +kernel

theorem local_pattern (a : Fin 3) : DirectionPattern (localTable a) (localTable a) (lift a 0) := by
  refine ⟨(lift_properties a 0).1,fun x y e nz => ?_⟩
  simp only [TwoPhases.score,TwoPhases.corners,SignObstruction.total,localTable,map_add,
    Bool.xor_false,ite_self]
  by_cases same : e=lift a 0
  · have z := (map_zero a e).mpr (Or.inr same)
    rw [z]
    simp [same]
  · have nonzero : localImage a e≠0 := fun z => same (((map_zero a e).mp z).resolve_left nz)
    simpa only [decide_eq_true same] using odd (localImage a x) (localImage a y) (localImage a e) nonzero

/-- This is defined on *all* physical points. Its restriction to each
    quotient line is linear when that line contains exactly one chosen point. -/
def image [DecidableEq Point] (o : Point) (chosen : Point → Bool) (v : Addr Point) :=
  addBit v.1 (decide (v.2≠o) && !chosen v.2)

def world [DecidableEq Point] (o : Point) (chosen : Point → Bool) (x y : Addr Point) :=
  EightSquare.phase (image o chosen x) (image o chosen y)

theorem realize_choice [DecidableEq Point] (o : Point) (lines : I → Fin 3 → Point)
    (off : ∀ i j, lines i j≠o) (chosen : Point → Bool) (h : OneOn lines chosen) :
    ∀ i, ∃ a : Fin 3, chosen (lines i a)=true ∧
      DirectionPattern (restrict (world o chosen) o (lines i)) (restrict (world o chosen) o (lines i)) (lift a 0) := by
  intro i
  obtain ⟨a,vals⟩ := h i
  have view (x : B) : image o chosen (embed o (lines i) x)=localImage a x := by
    by_cases inCore : x.toNat<4
    · simp [image,embed,localImage,inCore,Nat.not_le_of_lt inCore]
    · have out := Nat.le_of_not_lt inCore
      simp [image,embed,localImage,inCore,off,vals,out]
  have eq : restrict (world o chosen) o (lines i)=localTable a :=
    funext fun x => funext fun y => by simp only [restrict,world,view,localTable]
  exact ⟨a,by simp [vals],eq ▸ local_pattern a⟩

theorem outside_iff (o : Point) (lines : I → Fin 3 → Point) (off : ∀ i j, lines i j≠o) :
    OutsideOpt o lines ↔ ∃ chosen, OneOn lines chosen := by
  classical
  constructor
  · rintro ⟨r,c,h⟩; exact ⟨_,choice_of_profiles o lines r c h⟩
  · rintro ⟨chosen,h⟩
    refine ⟨world o chosen,world o chosen,fun i => ?_⟩
    obtain ⟨a,_,hp⟩ := realize_choice o lines off chosen h i
    exact ⟨lift a 0,(lift_properties a 0).2.1,hp⟩

end Mobius.CommonCore
