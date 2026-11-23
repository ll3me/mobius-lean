import Mobius.RigidityEnumeration

/-! Ground phases on coordinate four-planes in a common Boolean space.
The input hypergraph is linear: two distinct four-sets share at most one
actual coordinate. An executable paste evaluates a single global table. -/
namespace Mobius.AxisGlue
open Mobius.SignObstruction (B alphabet)
open Mobius.Rigidity (DirectionPattern)
open Mobius.Rigidity.Enumeration (Direction ground ground_pattern)

abbrev Axis := Fin 4
abbrev Ambient (v : Nat) := Fin v → Bool
abbrev World (v : Nat) := Ambient v → Ambient v → Bool

structure Atlas (k v : Nat) where
  loc : Fin k → Axis → Fin v
  inj : ∀ i a b, loc i a = loc i b → a=b
  linear : ∀ i j, i≠j → ∀ a b c d, loc i a=loc j b → loc i c=loc j d → a=c

def bits (p : B) (a : Axis) := p.getLsbD a.val
def unit (a : Axis) : B := BitVec.ofNat 4 (2^a.val)
private theorem unit_ne : ∀ a : Axis, unit a≠0 := by decide
def direction (a : Axis) : Direction := ⟨unit a,unit_ne a⟩
def table (a : Axis) := (ground (direction a)).1

def embed (T : Atlas k v) (i : Fin k) (p : B) : Ambient v := fun w =>
  (List.finRange 4).any (fun a => (T.loc i a == w) && bits p a)

def restrict (t : World v) (T : Atlas k v) (i : Fin k) := fun x y => t (embed T i x) (embed T i y)

private theorem present (T : Atlas k v) (i : Fin k) (p : B) (w : Fin v) :
    embed T i p w = true ↔ ∃ a, T.loc i a=w ∧ bits p a=true := by
  simp [embed,List.any_eq_true]

theorem at_axis (T : Atlas k v) (i : Fin k) (p : B) (a : Axis) :
    embed T i p (T.loc i a) = bits p a := by
  apply Bool.eq_iff_iff.mpr
  rw [present]
  constructor
  · rintro ⟨b,e,hb⟩; exact T.inj i b a e ▸ hb
  · intro ha; exact ⟨a,rfl,ha⟩

private theorem bits_inj : ∀ x y : B, (∀ a, bits x a=bits y a) → x=y := by decide

theorem embed_injective (T : Atlas k v) (i : Fin k) {x y : B} (h : embed T i x=embed T i y) :
    x=y := bits_inj x y (fun a => by simpa only [at_axis] using congrFun h (T.loc i a))

def onAxis (a : Axis) (b : Bool) : B := if b then unit a else 0

private theorem supported : ∀ (x : B) (a : Axis), (∀ t, t≠a → bits x t=false) →
    x=onAxis a (bits x a) := by decide
private theorem zero_of_empty : ∀ x : B, (∀ t, bits x t=false) → x=0 := by decide

/-- These four corner values are simultaneous with the entire board's
direction pattern. Only the diagonal (unit,unit) records a nonselected axis. -/
theorem axis_table : ∀ (chosen a : Axis) (x y : Bool),
    table chosen (onAxis a x) (onAxis a y) = (x && y && decide (chosen≠a)) := by
  decide +kernel

theorem origin_table : ∀ a : Axis, table a 0 0 = false := by decide +kernel

private theorem axis_bits (T : Atlas k v) {i j : Fin k} {a b : Axis}
    {x y : B} (axis : T.loc i a=T.loc j b) (eq : embed T i x=embed T j y) :
    bits x a=bits y b := by
  rw [←at_axis T i x a,←at_axis T j y b,eq,axis]

private theorem unsupported (T : Atlas k v) {i j : Fin k} {x y : B}
    (eq : embed T i x = embed T j y) (a : Axis) (missing : ∀ b, T.loc i a≠T.loc j b) :
    bits x a = false := by
  cases h : bits x a with
  | false => rfl
  | true =>
    have yes := (at_axis T i x a).trans h
    rw [eq] at yes
    obtain ⟨b,hit,_⟩ := (present T j y (T.loc i a)).mp yes
    exact False.elim (missing b hit.symm)

private theorem along_shared (T : Atlas k v) {i j : Fin k} (ne : i≠j)
    {a b : Axis} (hit : T.loc i a=T.loc j b) {x y : B} (eq : embed T i x=embed T j y) :
    x=onAxis a (bits x a) := by
  apply supported
  intro t diff
  exact unsupported T eq t (fun w other => diff (T.linear i j ne t w a b other hit))

def Matching (T : Atlas k v) (pick : Fin k → Axis) : Prop :=
  ∀ i j a b, T.loc i a=T.loc j b → (pick i=a ↔ pick j=b)

/-- Physical table cells from different boards have the same actual value
whenever both local copies refer to these two ambient coordinates. -/
theorem overlap_agrees (T : Atlas k v) (pick : Fin k → Axis) (ok : Matching T pick)
    (i j : Fin k) (x y x' y' : B) (hx : embed T i x=embed T j x') (hy : embed T i y=embed T j y') :
    table (pick i) x y = table (pick j) x' y' := by
  by_cases same : i=j
  · subst j
    rw [embed_injective T i hx,embed_injective T i hy]
  by_cases common : ∃ a b, T.loc i a = T.loc j b
  · obtain ⟨a,b,hit⟩ := common
    have lx := along_shared T same hit hx
    have ly := along_shared T same hit hy
    have rx := along_shared T (Ne.symm same) hit.symm hx.symm
    have ry := along_shared T (Ne.symm same) hit.symm hy.symm
    have bx := axis_bits T hit hx
    have byv := axis_bits T hit hy
    have kind := ok i j a b hit
    calc
      table (pick i) x y = table (pick i) (onAxis a (bits x a)) (onAxis a (bits y a)) :=
        (congrArg (fun p => table (pick i) p y) lx).trans (congrArg (table (pick i) _) ly)
      _ = (bits x a && bits y a && decide (pick i≠a)) := axis_table _ _ _ _
      _ = (bits x' b && bits y' b && decide (pick j≠b)) := by
        rw [bx,byv]
        by_cases ci : pick i=a
        · have cj := kind.mp ci; simp [ci,cj]
        · have cj : pick j≠b := fun e => ci (kind.mpr e)
          rw [decide_eq_true ci,decide_eq_true cj]
      _ = table (pick j) (onAxis b (bits x' b)) (onAxis b (bits y' b)) := (axis_table _ _ _ _).symm
      _ = table (pick j) x' y' := (congrArg (fun p => table (pick j) p _) rx.symm).trans (congrArg (table (pick j) _) ry.symm)
  · have left0 {s t : B} (h : embed T i s=embed T j t) : s=0 :=
      zero_of_empty s (fun a => unsupported T h a (fun b e => common ⟨a,b,e⟩))
    have right0 {s t : B} (h : embed T i s=embed T j t) : t=0 :=
      zero_of_empty t (fun b => unsupported T h.symm b (fun a e => common ⟨a,b,e.symm⟩))
    rw [left0 hx,left0 hy,right0 hx,right0 hy,origin_table,origin_table]

def vecEq (x y : Ambient v) : Bool := (List.finRange v).all fun w => x w == y w

private theorem vecEq_true (x y : Ambient v) : vecEq x y=true ↔ x=y := by
  simp only [vecEq,List.all_eq_true,List.mem_finRange,true_implies,beq_iff_eq]
  exact ⟨fun h => funext h,fun h w => congrFun h w⟩

/-- OR together the contributions of actual local matrix cells whose
ambient arguments match. A nonincident cell receives false. -/
def paste (T : Atlas k v) (pick : Fin k → Axis) : World v := fun x y =>
  (List.finRange k).any fun i => alphabet.any fun a => alphabet.any fun b =>
    vecEq (embed T i a) x && vecEq (embed T i b) y && table (pick i) a b

private theorem all_words : ∀ a : B, a∈alphabet := by decide

private theorem paste_true (T : Atlas k v) (pick : Fin k → Axis) (x y : Ambient v) :
    paste T pick x y = true ↔
      ∃ i a b, embed T i a=x ∧ embed T i b=y ∧ table (pick i) a b=true := by
  simp [paste,List.any_eq_true,vecEq_true,all_words,and_assoc]

theorem paste_restrict (T : Atlas k v) (pick : Fin k → Axis) (ok : Matching T pick) (i : Fin k) :
    restrict (paste T pick) T i = (ground (direction (pick i))).1 := by
  funext x y
  change paste T pick (embed T i x) (embed T i y) = table (pick i) x y
  apply Bool.eq_iff_iff.mpr
  rw [paste_true]
  constructor
  · rintro ⟨j,a,b,ha,hb,hv⟩
    exact (overlap_agrees T pick ok j i a b x y ha hb).symm.trans hv
  · intro hv
    exact ⟨i,x,y,rfl,rfl,hv⟩

theorem pasted_optima (T : Atlas k v) (pick : Fin k → Axis) (ok : Matching T pick) :
    ∃ p : World v, ∀ i, let t := restrict p T i
      DirectionPattern t t (unit (pick i)) ∧ TwoPhases.failures t t = 256 := by
  refine ⟨paste T pick,fun i => ?_⟩
  dsimp only
  rw [paste_restrict _ _ ok]
  have p := ground_pattern (direction (pick i))
  exact ⟨p,Rigidity.optimal_of_direction p⟩


private theorem bits_add : ∀ (a b : B) k, bits (a ^^^ b) k = (bits a k ^^ bits b k) := by decide

private theorem off_chart (T : Atlas k v) (i : Fin k) (w : Fin v) (off : ∀ a, T.loc i a ≠ w)
    (p : B) : embed T i p w=false := by
  cases e : embed T i p w with
  | false => rfl
  | true =>
    obtain ⟨a,h,_⟩ := (present _ _ _ _).mp e
    exact False.elim (off a h)

theorem embed_add (T : Atlas k v) (i : Fin k) (x y : B) :
    embed T i (x ^^^ y) = fun w => embed T i x w ^^ embed T i y w := by
  funext w
  by_cases inside : ∃ a, T.loc i a=w
  · obtain ⟨a,rfl⟩ := inside
    simp only [at_axis,bits_add]
  · have off := fun a h => inside ⟨a,h⟩
    simp only [off_chart _ _ _ off,Bool.false_xor]

theorem embed_zero (T : Atlas k v) (i : Fin k) : embed T i 0 = fun _ => false := by
  funext w
  by_cases inside : ∃ a, T.loc i a=w
  · obtain ⟨a,rfl⟩ := inside
    simp [at_axis,bits]
  · exact off_chart T i w (fun a e => inside ⟨a,e⟩) 0

private theorem unit_bit : ∀ a b, bits (unit a) b = decide (a=b) := by decide

theorem embed_unit (T : Atlas k v) (i : Fin k) (a : Axis) :
    embed T i (unit a) = fun w => decide (T.loc i a=w) := by
  funext w
  apply Bool.eq_iff_iff.mpr
  simp only [present,unit_bit,decide_eq_true_eq]
  constructor
  · rintro ⟨b,h,rfl⟩; exact h
  · intro h; exact ⟨a,h,rfl⟩

theorem shared_axis_score (T : Atlas k v) (r c : World v) (i j : Fin k) (a b : Axis)
    (hit : T.loc i a=T.loc j b) :
    TwoPhases.score (restrict r T i) (restrict c T i) (0,0,unit a) =
    TwoPhases.score (restrict r T j) (restrict c T j) (0,0,unit b) := by
  simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,restrict,embed_unit,hit]
  have h : embed T i 0#4 = embed T j 0#4 := (embed_zero T i).trans (embed_zero T j).symm
  rw [h]

theorem matching_necessary (T : Atlas k v) (pick : Fin k → Axis) (r c : World v)
    (pat : ∀ i, DirectionPattern (restrict r T i) (restrict c T i) (unit (pick i))) : Matching T pick := by
  intro i j a b hit
  have same := shared_axis_score T r c i j a b hit
  rw [(pat i).2 _ _ _ (unit_ne a),(pat j).2 _ _ _ (unit_ne b)] at same
  have finite : ∀ s a t b, decide (unit a≠unit s) = decide (unit b≠unit t) → (s=a ↔ t=b) := by decide
  exact finite _ _ _ _ same

theorem matching_iff (T : Atlas k v) (pick : Fin k → Axis) :
    (∃ r c : World v, ∀ i, DirectionPattern (restrict r T i) (restrict c T i) (unit (pick i)))
    ↔ Matching T pick := by
  constructor
  · rintro ⟨r,c,pat⟩; exact matching_necessary T pick r c pat
  · intro ok
    obtain ⟨p,h⟩ := pasted_optima T pick ok
    exact ⟨p,p,fun i => (h i).1⟩


/-- A shared nonzero step of two distinct boards pins down their single
common axis. Both anchors of any shared directed test lie on that line. -/
theorem shared_test_line (T : Atlas k v) {i j : Fin k} (ne : i≠j)
    {x y d x' y' e : B} (nz : d≠0)
    (hx : embed T i x=embed T j x') (hy : embed T i y=embed T j y') (hd : embed T i d=embed T j e) :
    ∃ a b, T.loc i a=T.loc j b ∧ d=unit a ∧ (x=0 ∨ x=d) ∧ (y=0 ∨ y=d) := by
  have anyBit : ∀ f : B, f≠0 → ∃ a, bits f a=true := by decide
  obtain ⟨a,ha⟩ := anyBit d nz
  have same := (at_axis T i d a).trans ha
  rw [hd] at same
  obtain ⟨b,back,_⟩ := (present T j e (T.loc i a)).mp same
  have dir : d=unit a := by simpa only [ha,onAxis,ite_true] using along_shared T ne back.symm hd
  have ends {s t : B} (eq : embed T i s=embed T j t) : s=0 ∨ s=d := by
    have on := along_shared T ne back.symm eq
    cases bb : bits s a
    · left; simpa only [bb,onAxis,Bool.false_eq_true,ite_false] using on
    · right; rw [dir]; simpa only [bb,onAxis,ite_true] using on
  exact ⟨a,b,back.symm,dir,ends hx,ends hy⟩

end Mobius.AxisGlue
