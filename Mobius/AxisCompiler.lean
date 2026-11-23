import Mobius.AxisNetwork

/-! A uniform physical atlas for positive exact-one clauses of arity three.
Each occurrence has its own copy at the center, joined to its original
variable by two exact-one binary boards. Repeated variables are allowed. -/
namespace Mobius.AxisCompiler
open Mobius.AxisGlue (Axis Atlas bits)
open Mobius.SignObstruction (B)
abbrev Source (m v : Nat) := Fin m → Fin 3 → Fin v

def one (z : Fin 3 → Bool) : Prop := (z 0).toNat+(z 1).toNat+(z 2).toNat=1
def Satisfiable (f : Source m v) : Prop := ∃ z : Fin v → Bool, ∀ i, one (fun a => z (f i a))

abbrev Tag := Fin 7
def board (i : Fin m) (s : Tag) : Fin (7*m) := ⟨7*i.val+s.val,by omega⟩
def row (i : Fin (7*m)) : Fin m := ⟨i.val/7,by omega⟩
def tag (i : Fin (7*m)) : Tag := ⟨i.val%7,by omega⟩

@[simp] theorem row_board (i : Fin m) (s : Tag) : row (board i s) = i := by
  apply Fin.ext
  change (7*i.val+s.val)/7=i.val
  omega

@[simp] theorem tag_board (i : Fin m) (s : Tag) : tag (board i s) = s := by
  apply Fin.ext
  change (7*i.val+s.val)%7=s.val
  omega

@[simp] theorem board_row_tag (i : Fin (7*m)) : board (row i) (tag i)=i := by
  apply Fin.ext
  change 7*(i.val/7)+i.val%7=i.val
  omega

/-- Shapes 1..19 are private to a row. Shape zero is the global source
variable of the indicated occurrence. Even identifying all three source
variables of a row leaves a linear seven-board template. -/
def shape (s : Tag) (a : Axis) : Fin 20 :=
  let chart : List (List (Fin 20)) :=
    [[1,2,3,4],[1,5,8,9],[2,6,10,11],[3,7,12,13],
     [5,0,14,15],[6,0,16,17],[7,0,18,19]]
  (chart.getD s.val []).getD a.val 0

def sourceSlot (s : Tag) : Fin 3 := ⟨(s.val+2)%3,by omega⟩
def mask (s : Tag) : B := if s=0 then 7 else 3
def ports (m : Nat) (i : Fin (7*m)) : B := mask (tag i)
def privateIndex (q : Fin 20) : Fin 19 := ⟨q.val-1,by omega⟩

def original (m : Nat) (x : Fin v) : Fin (v+19*m) := ⟨x.val,by omega⟩
def localVertex (v : Nat) (i : Fin m) (j : Fin 19) : Fin (v+19*m) :=
  ⟨v+19*i.val+j.val,by omega⟩

def locate (f : Source m v) (i : Fin m) (s : Tag) (a : Axis) : Fin (v+19*m) :=
  if shape s a = 0 then original m (f i (sourceSlot s))
  else localVertex v i (privateIndex (shape s a))

private theorem shape_inj : ∀ (s : Tag) (a b : Axis), shape s a=shape s b → a=b := by decide
private theorem shape_linear : ∀ (s t : Tag), s≠t → ∀ a b c d,
    shape s a=shape t b → shape s c=shape t d → a=c := by decide +kernel
private theorem shape_port : ∀ (s t : Tag), s≠t → ∀ a b,
    shape s a=shape t b → bits (mask s) a=true := by decide
private theorem source_port : ∀ s a, shape s a=0 → bits (mask s) a=true := by decide

private theorem classify (f : Source m v) {i j : Fin m} {s t : Tag} {a b : Axis}
    (eq : locate f i s a=locate f j t b) : shape s a=shape t b ∧ (i=j ∨ shape s a=0) := by
  have h := congrArg Fin.val eq
  unfold locate at h
  by_cases l : shape s a=0 <;> by_cases r : shape t b=0
  · exact ⟨l.trans r.symm,Or.inr l⟩
  · simp only [ite_eq_left l,ite_eq_right r,original,localVertex,privateIndex] at h
    have := (f i (sourceSlot s)).isLt; omega
  · simp only [ite_eq_right l,ite_eq_left r,original,localVertex,privateIndex] at h
    have := (f j (sourceSlot t)).isLt; omega
  · simp only [ite_eq_right l,ite_eq_right r,localVertex,privateIndex] at h
    have sl : (shape s a).val≠0 := fun u => l (Fin.ext u)
    have sr : (shape t b).val≠0 := fun u => r (Fin.ext u)
    have bl := (shape s a).isLt
    have br := (shape t b).isLt
    exact ⟨Fin.ext (by omega),Or.inl (Fin.ext (by omega))⟩

private theorem tags_differ {i j : Fin (7*m)} (ne : i≠j) (same : tag i=tag j) : row i≠row j := by
  intro h
  apply ne
  calc i = board (row i) (tag i) := (board_row_tag _).symm
       _ = board (row j) (tag j) := by rw [same,h]
       _ = j := board_row_tag _

def atlas (f : Source m v) : Atlas (7*m) (v+19*m) where
  loc i a := locate f (row i) (tag i) a
  inj i a b eq := shape_inj _ _ _ (classify f eq).1
  linear i j ne a b c d first second := by
    obtain ⟨s,h⟩ := classify f first
    obtain ⟨t,u⟩ := classify f second
    by_cases same : tag i=tag j
    · have diff := tags_differ ne same
      exact shape_inj _ _ _ ((h.resolve_left diff).trans (u.resolve_left diff).symm)
    · exact shape_linear _ _ same _ _ _ _ s t

theorem all_shared (f : Source m v) : AxisNetwork.AllSharedArePorts (atlas f) (ports m) := by
  intro i j ne a b same
  obtain ⟨ss,h⟩ := classify f same
  by_cases tags : tag i=tag j
  · exact source_port (tag i) a (h.resolve_left (tags_differ ne tags))
  · exact shape_port _ _ tags _ _ ss

theorem admissible (m : Nat) (i : Fin (7*m)) : AxisPortCost.admissible (ports m i) := by
  have all : ∀ s, AxisPortCost.admissible (mask s) := by unfold AxisPortCost.admissible; decide
  exact all (tag i)

def field (x : Fin 3 → Bool) (j : Fin 19) : Bool :=
  match j.val with
  | 0 => x 0 | 1 => x 1 | 2 => x 2
  | 4 => !(x 0) | 5 => !(x 1) | 6 => !(x 2)
  | _ => false

def extend (f : Source m v) (z : Fin v → Bool) (w : Fin (v+19*m)) : Bool :=
  if h : w.val < v then z ⟨w.val,h⟩
  else
    let i : Fin m := ⟨(w.val-v)/19,by omega⟩
    let j : Fin 19 := ⟨(w.val-v)%19,by omega⟩
    field (fun a => z (f i a)) j

@[simp] theorem extend_original (f : Source m v) (z : Fin v → Bool) (a : Fin v) :
    extend f z (original m a) = z a := by simp [extend,original,a.isLt]

@[simp] theorem extend_local (f : Source m v) (z : Fin v → Bool) (i : Fin m) (j : Fin 19) :
    extend f z (localVertex v i j) = field (fun a => z (f i a)) j := by
  have nlt : ¬ (v+19*i.val+j.val < v) := by omega
  unfold extend localVertex
  simp only [nlt,↓reduceDIte]
  congr 1
  · funext a
    congr 2
    apply Fin.ext
    change ((v+19*i.val+j.val-v)/19)=i.val
    omega
  · apply Fin.ext; change ((v+19*i.val+j.val-v)%19)=j.val; omega

def localBits (x : Fin 3 → Bool) (priv : Fin 19 → Bool) (s : Tag) (a : Axis) : Bool :=
  if shape s a=0 then x (sourceSlot s) else priv (privateIndex (shape s a))

def boardOK (s : Tag) (y : Axis → Bool) : Prop :=
  ∃ a : Axis, bits (mask s) a=true ∧ ∀ b, y b=decide (b=a)

private theorem extend_locate (f : Source m v) (z : Fin v → Bool) (i : Fin m) (s : Tag) (a : Axis) :
    extend f z (locate f i s a) =
      localBits (fun j => z (f i j)) (field (fun j => z (f i j))) s a := by
  by_cases h : shape s a=0 <;> simp [locate,localBits,h]

private theorem local_yes (x : Fin 3 → Bool) (s : Tag) (ok : one x) :
    boardOK s (localBits x (field x) s) := by
  let tuple (a b c : Bool) : Fin 3 → Bool := Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0))
  have eta : tuple (x 0) (x 1) (x 2) = x := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      induction i using Fin.cases with
      | zero => rfl
      | succ i =>
        induction i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i
  have all : ∀ (t : Tag) (a b c : Bool), let z := tuple a b c
      one z → boardOK t (localBits z (field z) t) := by
    dsimp only; unfold one boardOK tuple; decide +kernel
  have h := all s (x 0) (x 1) (x 2)
  rw [eta] at h
  exact h ok

theorem extend_solution (f : Source m v) (z : Fin v → Bool) (ok : ∀ i, one (fun a => z (f i a))) :
    ∀ i, ∃ a, bits (ports m i) a=true ∧
      ∀ b, extend f z ((atlas f).loc i b)=decide (b=a) := by
  intro i
  have solved := local_yes (fun a => z (f (row i) a)) (tag i) (ok (row i))
  obtain ⟨a,ha,bitsOK⟩ := solved
  exact ⟨a,ha,fun b => (extend_locate f z _ _ b).trans (bitsOK b)⟩


private theorem binary_forces {s : Tag} (wire : s≠0) {y : Axis → Bool} (h : boardOK s y) :
    y 0≠y 1 := by
  obtain ⟨a,ha,values⟩ := h
  have allowed : ∀ a : Axis, bits 3 a=true → decide ((0:Axis)=a) ≠ decide ((1:Axis)=a) := by decide
  rw [values 0,values 1]
  exact allowed a (by simpa [mask,wire] using ha)

private theorem center_forces {y : Axis → Bool} (h : boardOK 0 y) :
    (y 0).toNat + (y 1).toNat + (y 2).toNat =1 := by
  obtain ⟨a,ha,values⟩ := h
  rw [values 0,values 1,values 2]
  have allowed : ∀ a : Axis, bits 7 a=true →
      (decide ((0:Axis)=a)).toNat + (decide ((1:Axis)=a)).toNat + (decide ((2:Axis)=a)).toNat=1 := by decide
  exact allowed a ha

private theorem twice_not {a b c : Bool} (ab : a≠b) (bc : b≠c) : a=c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem local_only (x : Fin 3 → Bool) (priv : Fin 19 → Bool)
    (ok : ∀ s : Tag, boardOK s (localBits x priv s)) : one x := by
  have center := center_forces (ok 0)
  change (priv 0).toNat+(priv 1).toNat+(priv 2).toNat=1 at center
  have h₀ : priv 0=x 0 := twice_not
    (binary_forces (s:=1) (by decide) (ok 1)) (binary_forces (s:=4) (by decide) (ok 4))
  have h₁ : priv 1=x 1 := twice_not
    (binary_forces (s:=2) (by decide) (ok 2)) (binary_forces (s:=5) (by decide) (ok 5))
  have h₂ : priv 2=x 2 := twice_not
    (binary_forces (s:=3) (by decide) (ok 3)) (binary_forces (s:=6) (by decide) (ok 6))
  rw [h₀,h₁,h₂] at center
  exact center

theorem boolean_iff (f : Source m v) :
    AxisNetwork.BooleanSolution (atlas f) (ports m) ↔ Satisfiable f := by
  constructor
  · rintro ⟨z,boards⟩
    refine ⟨fun a => z (original m a),fun i => ?_⟩
    apply local_only (priv:=fun j => z (localVertex v i j))
    intro s
    obtain ⟨a,ha,matchBits⟩ := boards (board i s)
    refine ⟨a,?_,fun b => ?_⟩
    · simpa [ports] using ha
    · have view : localBits (fun t => z (original m (f i t))) (fun j => z (localVertex v i j)) s b =
          z (locate f i s b) := by by_cases on : shape s b=0 <;> simp [localBits,locate,on]
      exact view.trans (by simpa only [atlas,row_board,tag_board] using matchBits b)
  · rintro ⟨z,ok⟩
    exact ⟨extend f z,extend_solution f z ok⟩

theorem weighted_iff (f : Source m v) :
    (∃ r c : AxisGlue.World (v+19*m),
      AxisNetwork.cost (atlas f) (ports m) AxisPortCost.weighted r c ≤ (7*m)*2300) ↔ Satisfiable f :=
  ((AxisNetwork.weighted_iff _ _ (admissible m)).trans (AxisNetwork.feasible_iff_boolean _ _)).trans
    (boolean_iff f)

theorem geometric_iff (gap : AxisPortCost.Gap282) (f : Source m v) :
    (∃ r c : AxisGlue.World (v+19*m),
      AxisNetwork.cost (atlas f) (ports m) AxisPortCost.geometricRetained r c ≤ (7*m)*126) ↔ Satisfiable f :=
  ((AxisNetwork.geometric_iff gap _ _ (admissible m)).trans (AxisNetwork.feasible_iff_boolean _ _)).trans
    (boolean_iff f)

end Mobius.AxisCompiler
