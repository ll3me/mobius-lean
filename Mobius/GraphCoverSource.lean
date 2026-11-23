import Mobius.FullBoardMerge

/-! Vertex cover as a bitwise monotone projection into positive exact-one
source addresses. The input is the proposed cover; its vertices are labelled,
while the list of graph edges is fixed. Loops and repeated edges are allowed. -/
namespace Mobius.GraphCoverSource
open Mobius.AxisCompiler (Source one Satisfiable)

abbrev Edges (n m : Nat) := Fin m → Fin n × Fin n
def rows (n m : Nat) := (1+m)+n
def vars (n m : Nat) := 2*n+m+2

def zVar (v : Fin n) : Fin (vars n m) := ⟨2*v.val,by unfold vars; omega⟩
def dummyVar (v : Fin n) : Fin (vars n m) := ⟨2*v.val+1,by unfold vars; omega⟩
def slackVar (e : Fin m) : Fin (vars n m) := ⟨2*n+e.val,by unfold vars; omega⟩
def falseVar (n m : Nat) : Fin (vars n m) := ⟨2*n+m,by unfold vars; omega⟩
def trueVar (n m : Nat) : Fin (vars n m) := ⟨2*n+m+1,by unfold vars; omega⟩

def pinRow (n m : Nat) : Fin (rows n m) := (Fin.castAdd m (0 : Fin 1)).castAdd n
def edgeRow (e : Fin m) : Fin (rows n m) := (e.natAdd 1).castAdd n
def inputRow (v : Fin n) : Fin (rows n m) := v.natAdd (1+m)

def triple (a b c : α) (j : Fin 3) := if j=0 then a else if j=1 then b else c
def query (x : Fin n → Bool) (v : Fin n) : Fin (vars n m) :=
  if x v then dummyVar v else zVar v

def source (g : Edges n m) (x : Fin n → Bool) : Source (rows n m) (vars n m) :=
  Fin.addCases (Fin.addCases (fun _ => triple (falseVar n m) (falseVar n m) (trueVar n m))
      (fun e => triple (zVar (g e).1) (zVar (g e).2) (slackVar e)))
    (fun v => triple (query x v) (falseVar n m) (falseVar n m))

@[simp] theorem source_pin (g : Edges n m) (x : Fin n → Bool) (a : Fin 3) :
    source g x (pinRow n m) a=triple (falseVar n m) (falseVar n m) (trueVar n m) a := by
  simp only [source,pinRow,Fin.addCases_left]
@[simp] theorem source_edge (g : Edges n m) (x : Fin n → Bool) (e : Fin m) (a : Fin 3) :
    source g x (edgeRow e) a=triple (zVar (g e).1) (zVar (g e).2) (slackVar e) a := by
  simp only [source,edgeRow,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem source_input (g : Edges n m) (x : Fin n → Bool) (v : Fin n) (a : Fin 3) :
    source g x (inputRow v) a=triple (query x v) (falseVar n m) (falseVar n m) a := by
  simp only [source,inputRow,Fin.addCases_right]

def Covers (g : Edges n m) (x : Fin n → Bool) := ∀ e, x (g e).1=true ∨ x (g e).2=true

/-- Unary pins force the variables of every uncovered vertex to mark an
independent set. For a cover, take that independent set exactly. -/
def assignment (g : Edges n m) (x : Fin n → Bool) (j : Fin (vars n m)) : Bool :=
  if small : j.val<2*n then
    if j.val%2=0 then !(x ⟨j.val/2,by omega⟩) else true
  else if edge : j.val<2*n+m then
    let e : Fin m := ⟨j.val-2*n,by omega⟩
    x (g e).1 && x (g e).2
  else decide (j=trueVar n m)

private theorem assign_z (g : Edges n m) (x : Fin n → Bool) (v : Fin n) :
    assignment g x (zVar v)= !(x v) := by
  have s : 2*v.val<2*n := by omega
  simp [assignment,zVar,s]
private theorem assign_dummy (g : Edges n m) (x : Fin n → Bool) (v : Fin n) :
    assignment g x (dummyVar v)=true := by
  have s : 2*v.val+1<2*n := by omega
  simp [assignment,dummyVar,s]
private theorem assign_slack (g : Edges n m) (x : Fin n → Bool) (e : Fin m) :
    assignment g x (slackVar e)=(x (g e).1 && x (g e).2) := by
  have l : ¬2*n+e.val<2*n := by omega
  have u : 2*n+e.val<2*n+m := by omega
  simp [assignment,slackVar,l,u]
private theorem assign_false (g : Edges n m) (x : Fin n → Bool) :
    assignment g x (falseVar n m)=false := by
  have l : ¬2*n+m<2*n := by omega
  simp [assignment,falseVar,trueVar,l,Fin.ext_iff]
private theorem assign_true (g : Edges n m) (x : Fin n → Bool) :
    assignment g x (trueVar n m)=true := by
  have l : ¬2*n+m+1<2*n := by omega
  have u : ¬2*n+m+1<2*n+m := by omega
  simp [assignment,trueVar,l,u]

theorem source_iff (g : Edges n m) (x : Fin n → Bool) : Satisfiable (source g x) ↔ Covers g x := by
  constructor
  · rintro ⟨z,h⟩
    have pin := h (pinRow n m)
    simp only [one,source_pin,triple] at pin
    have off : z (falseVar n m)=false := by
      cases hf : z (falseVar n m) <;> cases ht : z (trueVar n m) <;> simp_all
    have unset (v : Fin n) (hv : x v=false) : z (zVar v : Fin (vars n m))=true := by
      have p := h (inputRow v)
      simpa [one,triple,query,hv,off] using p
    intro e
    have edge := h (edgeRow e)
    cases a : x (g e).1 <;> cases b : x (g e).2 <;> simp
    have left := unset _ a
    have right := unset _ b
    simp [one,triple,left,right] at edge
    omega
  · intro cover
    refine ⟨assignment g x,?_⟩
    intro row
    change Fin ((1+m)+n) at row
    induction row using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        have e : i=0 := Fin.ext (by omega)
        subst i
        change one (fun a => assignment g x (source g x (pinRow n m) a))
        simp [one,triple,assign_false,assign_true]
      | right e =>
        change one (fun a => assignment g x (source g x (edgeRow e) a))
        simp only [one,source_edge]
        simp [triple,assign_z,assign_slack]
        have he := cover e
        cases h₁ : x (g e).1 <;> cases h₂ : x (g e).2 <;> simp_all
    | right v =>
      change one (fun a => assignment g x (source g x (inputRow v) a))
      cases b : x v <;> simp [one,triple,query,b,assign_z,assign_dummy,assign_false]

/-- Exactly one address position may read an input in an input row.
Its low-order bit reads the cover bit with positive polarity. -/
def driving (row : Fin (rows n m)) (a : Fin 3) : Option (Fin n) :=
  Fin.addCases (m:=1+m) (n:=n) (motive:=fun _ => Option (Fin n))
    (fun _ => none) (fun v => if a=0 then some v else none) row

theorem source_static (g : Edges n m) (x y : Fin n → Bool) (row : Fin (rows n m)) (a : Fin 3)
    (noninput : ∀ u, row≠inputRow u ∨ a≠0) : source g x row a=source g y row a := by
  change Fin ((1+m)+n) at row
  induction row using Fin.addCases with
  | left t => simp only [source,Fin.addCases_left]
  | right v =>
    have slot := (noninput v).resolve_left (fun ne => ne rfl)
    simp only [source,Fin.addCases_right,triple,ite_eq_right slot]

theorem query_bit (x : Fin n → Bool) (v : Fin n) (j : Nat) :
    (query (m:=m) x v).val.testBit j = if j=0 then x v else (2*v.val).testBit j := by
  cases j with
  | zero => cases b : x v <;> simp [query,zVar,dummyVar,b]
  | succ j =>
    have halves : (2*v.val+1)/2=(2*v.val)/2 := by omega
    cases b : x v <;> simp [query,zVar,dummyVar,b,Nat.testBit_succ,halves]

theorem address_bit (g : Edges n m) (x : Fin n → Bool) (row : Fin (rows n m)) (a : Fin 3) (j : Nat) :
    (source g x row a).val.testBit j =
      if j=0 then (driving row a).elim ((source g (fun _ => false) row a).val.testBit j) x
      else (source g (fun _ => false) row a).val.testBit j := by
  change Fin ((1+m)+n) at row
  induction row using Fin.addCases with
  | left i =>
    simp only [driving,source,Fin.addCases_left,Option.elim_none,ite_self]
  | right v =>
    change (source g x (inputRow v) a).val.testBit j=_
    simp only [source_input,driving,Fin.addCases_right]
    by_cases sel : a=0
    · subst a
      simp only [source,Fin.addCases_right,triple,ite_true,Option.elim_some]
      rw [query_bit,query_bit]
      by_cases h : j=0 <;> simp [h]
    · simp [source,triple,sel]

/-- The threshold is the literal deduplicated union of complete four-dimensional
boards; only the reverse implication needs the unweighted local gap. -/
theorem compiled_cover_iff (gap : PortGap.Gap266) (g : Edges n m) (x : Fin n → Bool) :
    let a := rows n m
    let b := vars n m
    (∃ r c : AxisGlue.World ((b+19*a)+3*(b+6*a)),
      FullCaps.unionCost (CapAtlas.compiled (source g x)) r c ≤ (7*a)*126+(b+6*a)*128) ↔ Covers g x :=
  (FullBoardMerge.compiled_iff gap (source g x)).trans (source_iff g x)

end Mobius.GraphCoverSource
