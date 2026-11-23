import Mobius.ThreeFaceColoring
import Mobius.ThreeFaceAttachment

/-! The graph construction uses actual nondegenerate binary two-dimensional
quotient planes. No input boundary phases or exceptional directions are
fixed in the final equivalence. -/
namespace Mobius.ThreeFaceRealization
open Mobius.ThreeFaceColoring (Graph Simple Kind endpoints lines triPoints atom aux Colorable)
open Mobius.SignObstruction (B)

private def vi (i : Fin n) (b : Bool) := 2*i.val+b.toNat
private def ei (n : Nat) (e : Fin m) (b : Bool) := 2*n+2*e.val+b.toNat

private theorem read_atom (i j : Fin n) (a b : Bool) :
    (atom i a).testBit (vi j b)=decide (i=j ∧ a=b) := by
  rw [atom,Nat.testBit_two_pow]; unfold vi
  apply decide_eq_decide.mpr
  cases a <;> cases b <;> simp [Fin.ext_iff] <;> omega

private theorem read_aux (j : Fin n) (e : Fin m) (a b : Bool) :
    (aux n e a).testBit (vi j b)=false := by
  rw [aux,Nat.testBit_two_pow]; unfold vi
  apply decide_eq_false
  cases a <;> cases b <;> simp <;> omega

private theorem read_old (j : Fin n) (e : Fin m) (a b : Bool) :
    (atom j a).testBit (ei n e b)=false := by
  rw [atom,Nat.testBit_two_pow]; unfold ei
  apply decide_eq_false
  cases a <;> cases b <;> simp <;> omega

private theorem read_own (n : Nat) (e : Fin m) (b : Bool) :
    (aux n e b).testBit (ei n e b)=true := by simp [aux,ei]

/-- Private separating coordinates certify independence: the first axis
reads (1,0) and the second reads (0,1) on the pair of generators. -/
def Independent (p q : Nat) :=
  ∃ i j, p.testBit i=true ∧ q.testBit i=false ∧ p.testBit j=false ∧ q.testBit j=true

theorem independent (g : Graph n m) (simple : Simple g) (k : Kind n m) :
    Independent (endpoints g k).1 (endpoints g k).2 := by
  cases k with
  | vertex i =>
    refine ⟨vi i false,vi i true,?_⟩
    simp [endpoints,read_atom]
  | edge e =>
    have ne := simple e
    refine ⟨vi (g e).1 false,vi (g e).1 true,?_⟩
    simp only [endpoints,Nat.testBit_xor,read_atom]
    simp [Ne.symm ne]
  | link e b j =>
    have ne := simple e
    have tags : ∀ s : Fin 3, s=0 ∨ s=1 ∨ s=2 := by decide
    rcases tags j with rfl|rfl|rfl
    · refine ⟨vi (g e).1 b,ei n e b,?_⟩
      simp [endpoints,read_atom,read_aux,read_old,read_own]
    · refine ⟨vi (g e).2 b,ei n e b,?_⟩
      simp only [endpoints,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true,Nat.testBit_xor,read_atom,read_aux,read_old,read_own]
      simp [ne]
    · refine ⟨vi (g e).1 b,ei n e b,?_⟩
      simp only [endpoints,show ¬(2:Fin 3)=0 by decide,show ¬(2:Fin 3)=1 by decide,ite_false,Nat.testBit_xor,read_atom,read_aux,read_old,read_own]
      simp [Ne.symm ne]

private def signature (u : Fin 3) : Bool × Bool := if u=0 then (true,false) else if u=1 then (false,true) else (true,true)

private theorem read_line {p q : Nat} (g : Independent p q) :
    ∃ i j, ∀ a : Fin 3, ((triPoints p q a).testBit i,(triPoints p q a).testBit j)=signature a := by
  obtain ⟨i,j,pi,qi,pj,qj⟩ := g
  refine ⟨i,j,fun a => ?_⟩
  by_cases s : a=0 <;> by_cases t : a=1 <;> simp [triPoints,signature,s,t,pi,pj,qi,qj]

theorem points_nonzero (g : Graph n m) (simple : Simple g) (k : Kind n m) (j : Fin 3) :
    lines g k j ≠ 0 := by
  obtain ⟨i,t,read⟩ := read_line (independent g simple k)
  intro zero
  have h := read j
  change ((lines g k j).testBit i,(lines g k j).testBit t)=signature j at h
  rw [zero] at h
  have valid : ∀ j : Fin 3, signature j ≠ (false,false) := by decide
  exact valid j (by simpa using h.symm)

theorem points_distinct (g : Graph n m) (simple : Simple g) (k : Kind n m) {u v : Fin 3}
    (same : lines g k u=lines g k v) : u=v := by
  obtain ⟨i,j,h⟩ := read_line (independent g simple k)
  have eq := (h u).symm.trans ((congrArg (fun x : Nat => (x.testBit i,x.testBit j)) same).trans (h v))
  have distinct : ∀ a b : Fin 3, signature a=signature b → a=b := by decide
  exact distinct u v eq

theorem points_form_plane (g : Graph n m) (k : Kind n m) :
    lines g k 0 ^^^ lines g k 1=lines g k 2 := rfl

theorem graph_iff (g : Graph n m) (simple : Simple g) :
    ThreeFaceAttachment.Feasible 0 (lines g) ↔ Colorable g :=
  (ThreeFaceAttachment.attached_iff 0 (lines g) (points_nonzero g simple)).trans (ThreeFaceColoring.choices_iff g)


def linearPart (p q : Nat) (x : B) :=
  (if x.getLsbD 2 then p else 0) ^^^ (if x.getLsbD 3 then q else 0)

theorem actual_board (g : Graph n m) (k : Kind n m) (x : B) :
    CommonCore.embed 0 (lines g k) x =
      (x.setWidth 2,linearPart (endpoints g k).1 (endpoints g k).2 x) := by
  have core : ∀ x : B, x.toNat<4 ↔ x.getLsbD 2=false ∧ x.getLsbD 3=false := by decide
  cases a : x.getLsbD 2 <;> cases b : x.getLsbD 3 <;>
    simp only [CommonCore.embed,CommonCore.slot,linearPart,lines,triPoints,core,a,b] <;> simp

private theorem part_read (p q : Nat) (x : B) (i : Nat) :
    (linearPart p q x).testBit i = ((x.getLsbD 2 && p.testBit i) ^^ (x.getLsbD 3 && q.testBit i)) := by
  cases a : x.getLsbD 2 <;> cases b : x.getLsbD 3 <;> simp only [linearPart,a,b] <;> simp

theorem board_injective (g : Graph n m) (simple : Simple g) (k : Kind n m) {x y : B}
    (eq : CommonCore.embed 0 (lines g k) x=CommonCore.embed 0 (lines g k) y) : x=y := by
  rw [actual_board,actual_board] at eq
  obtain ⟨low,high⟩ := Prod.mk.inj eq
  have same : ∀ x y : B, x.setWidth 2=y.setWidth 2 → x.getLsbD 2=y.getLsbD 2 →
      x.getLsbD 3=y.getLsbD 3 → x=y := by decide
  apply same x y low
  all_goals obtain ⟨i,j,pi,qi,pj,qj⟩ := independent g simple k
  · simpa [part_read,pi,qi] using congrArg (fun t => Nat.testBit t i) high
  · simpa [part_read,pj,qj] using congrArg (fun t => Nat.testBit t j) high

theorem board_add (g : Graph n m) (k : Kind n m) (x y : B) :
    let e := CommonCore.embed 0 (lines g k)
    e (x^^^y)=((e x).1^^^(e y).1,(e x).2^^^(e y).2) := by
  dsimp only
  rw [actual_board,actual_board,actual_board]
  apply Prod.ext
  · have lo : ∀ a b : B, (a^^^b).setWidth 2=a.setWidth 2^^^b.setWidth 2 := by decide
    exact lo _ _
  · apply Nat.eq_of_testBit_eq
    intro j
    have dist : ∀ a b c d p q : Bool, (((a^^b) && p) ^^ ((c^^d) && q)) =
      (((a && p) ^^ (c && q)) ^^ ((b && p) ^^ (d && q))) := by decide
    simp only [Nat.testBit_xor,part_read,BitVec.getLsbD_xor]
    exact dist ..

/-- All physical quotient addresses fit exactly in 2n+2m public bits. -/
theorem points_bounded (g : Graph n m) (k : Kind n m) (j : Fin 3) :
    lines g k j < 2^(2*n+2*m) := by
  have coord (u : Fin n) (b : Bool) : atom u b < 2^(2*n+2*m) := by
    unfold atom
    apply Nat.pow_lt_pow_right (by decide)
    cases b <;> simp <;> omega
  have privateCoord (e : Fin m) (b : Bool) : aux n e b < 2^(2*n+2*m) := by
    unfold aux
    apply Nat.pow_lt_pow_right (by decide)
    cases b <;> simp <;> omega
  have both : (endpoints g k).1 < 2^(2*n+2*m) ∧ (endpoints g k).2 < 2^(2*n+2*m) := by
    cases k with
    | vertex i => exact ⟨coord i _,coord i _⟩
    | edge e => exact ⟨Nat.xor_lt_two_pow (coord _ _) (coord _ _),Nat.xor_lt_two_pow (coord _ _) (coord _ _)⟩
    | link e b s =>
      have opts : ∀ z : Fin 3, z=0 ∨ z=1 ∨ z=2 := by decide
      rcases opts s with rfl|rfl|rfl
      · exact ⟨coord _ _,privateCoord _ _⟩
      · exact ⟨coord _ _,Nat.xor_lt_two_pow (coord _ _) (privateCoord _ _)⟩
      · exact ⟨Nat.xor_lt_two_pow (coord _ _) (coord _ _),privateCoord _ _⟩
  unfold lines triPoints
  split
  · exact both.1
  · split
    · exact both.2
    · exact Nat.xor_lt_two_pow both.1 both.2

def finiteLines (g : Graph n m) (k : Kind n m) (j : Fin 3) : BitVec (2*n+2*m) :=
  BitVec.ofNat (2*n+2*m) (lines g k j)

theorem finite_value (g : Graph n m) (k : Kind n m) (j : Fin 3) :
    (finiteLines g k j).toNat=lines g k j := by simp [finiteLines,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (points_bounded g k j)]

/-- A uniformly finite ambient table: the quotient point component is a
bit-vector of width 2n+2m; the common and private coordinates add five bits. -/
theorem finite_graph_iff (g : Graph n m) (simple : Simple g) :
    ThreeFaceAttachment.Feasible (0 : BitVec (2*n+2*m)) (finiteLines g) ↔ Colorable g := by
  have off (k : Kind n m) (j) : finiteLines g k j≠0 := by
    intro eq
    apply points_nonzero g simple k j
    rw [←finite_value,eq]; rfl
  rw [ThreeFaceAttachment.attached_iff _ _ off,←ThreeFaceColoring.choices_iff]
  constructor
  · rintro ⟨chosen,ok⟩
    exact ⟨fun p => chosen (BitVec.ofNat (2*n+2*m) p),ok⟩
  · rintro ⟨chosen,ok⟩
    refine ⟨fun p => chosen p.toNat,fun k => ?_⟩
    obtain ⟨j,bits⟩ := ok k
    exact ⟨j,fun i => (congrArg chosen (finite_value g k i)).trans (bits i)⟩

end Mobius.ThreeFaceRealization
