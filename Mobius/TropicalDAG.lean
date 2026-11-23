import Std

/-!
A gate-by-gate directional restriction of a shared min-plus DAG. The source
may have rational constants. The target has only input variables, zero,
binary max, and binary addition. A strict comparison at the fixed base
point emits no gate: all later uses of the result are redirected.
-/
namespace Mobius.TropicalDAG

inductive Op (I K : Type) (n : Nat) where
  | input (i : I)
  | literal (c : K)
  | add (l r : Fin n)
  | choose (l r : Fin n)

/-- Gate 0 denotes the most recently emitted gate. References may be reused
any number of times, including by several different later gates. -/
inductive Program (I K : Type) : Nat → Type where
  | empty : Program I K 0
  | push {n} (prev : Program I K n) (op : Op I K n) : Program I K (n+1)

def extend (v : A) (prev : Fin n → A) : Fin (n+1) → A := Fin.cases v prev
@[simp] theorem extend_zero (v : A) (h : Fin n → A) : extend v h 0 = v := rfl
@[simp] theorem extend_succ (v : A) (h : Fin n → A) (i : Fin n) :
    extend v h i.succ = h i := rfl

def Op.eval (x : I → A) (lit : K → A) (plus choose : A → A → A)
    (prev : Fin n → A) : Op I K n → A
  | .input i => x i
  | .literal c => lit c
  | .add l r => plus (prev l) (prev r)
  | .choose l r => choose (prev l) (prev r)

def Program.run (x : I → A) (lit : K → A) (plus choose : A → A → A) :
    {n : Nat} → Program I K n → (Fin n → A)
  | _, .empty => Fin.elim0
  | _, .push p op =>
    let prev := p.run x lit plus choose
    extend (op.eval x lit plus choose prev) prev

abbrev MinDAG (I : Type) := Program I Rat
abbrev MaxDAG (J : Type) := Program J Unit

def primal (p : MinDAG I n) (x : I → Rat) : Fin n → Rat :=
    p.run x id (·+·) min

def value (p : MaxDAG J n) (w : J → Rat) : Fin n → Rat :=
    p.run w (fun _ => 0) (·+·) max

/-- A source input has either zero gain or the indicated target variable. -/
def slopeInput (labels : I → Option J) (w : J → Rat) (i : I) : Rat :=
    ((labels i).map w).getD 0

structure Jet where
  base : Rat
  gain : Rat

def Jet.plus (a b : Jet) : Jet := ⟨a.base+b.base,a.gain+b.gain⟩

def Jet.choose (a b : Jet) : Jet :=
    if a.base < b.base then a
    else if b.base < a.base then b
    else ⟨a.base,max a.gain b.gain⟩

def jets (p : MinDAG I n) (b d : I → Rat) : Fin n → Jet :=
    p.run (fun i => ⟨b i,d i⟩) (fun c => ⟨c,0⟩) Jet.plus Jet.choose

private theorem base_min (a b : Jet) : (a.choose b).base = min a.base b.base := by
  by_cases h : a.base < b.base <;> by_cases j : b.base < a.base <;> simp [Jet.choose,h,j,Rat.min_def] <;> grind

theorem base_is_primal (p : MinDAG I n) (b d : I → Rat) (i : Fin n) :
    (jets p b d i).base = primal p b i := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p op ih =>
    induction i using Fin.cases with
    | zero =>
      cases op <;> simp [jets,primal,Program.run,Op.eval,Jet.plus,base_min] at *
      all_goals grind
    | succ i => exact ih i

structure Pass (J : Type) (n : Nat) where
  size : Nat
  program : MaxDAG J size
  addr : Fin n → Fin size

def Pass.emit (p : Pass J n) (gate : Op J Unit p.size) : Pass J (n+1) :=
    ⟨p.size+1,.push p.program gate,extend 0 (fun i => (p.addr i).succ)⟩

def Pass.alias (p : Pass J n) (i : Fin n) : Pass J (n+1) :=
    ⟨p.size,p.program,extend (p.addr i) p.addr⟩

def step (prev : Pass J n) (base : Fin n → Rat) (labels : I → Option J) :
    Op I Rat n → Pass J (n+1)
  | .input i => match labels i with
    | some j => prev.emit (.input j)
    | none => prev.emit (.literal ())
  | .literal _ => prev.emit (.literal ())
  | .add l r => prev.emit (.add (prev.addr l) (prev.addr r))
  | .choose l r =>
    if base l < base r then prev.alias l
    else if base r < base l then prev.alias r
    else prev.emit (.choose (prev.addr l) (prev.addr r))

/-- Compilation depends on the fixed b and on the variable substitution,
independently of the weights supplied later. -/
def compile (b : I → Rat) (labels : I → Option J) : {n : Nat} → MinDAG I n → Pass J n
  | _, .empty => ⟨0,.empty,Fin.elim0⟩
  | _, .push p g => step (compile b labels p) (primal p b) labels g

private theorem step_size (v : Pass J n) (b : Fin n → Rat) (labels : I → Option J) (g : Op I Rat n) :
    (step v b labels g).size ≤ v.size+1 := by
  cases g with
  | input i => cases e : labels i <;> simp [step,e,Pass.emit]
  | literal c => exact Nat.le_refl _
  | add i j => exact Nat.le_refl _
  | choose i j =>
    by_cases h : b i < b j <;> by_cases g : b j < b i <;> simp [step,h,g,Pass.alias,Pass.emit]

theorem size_le (p : MinDAG I n) (b : I → Rat) (labels : I → Option J) :
    (compile b labels p).size ≤ n := by
  induction p with
  | empty => exact Nat.le_refl _
  | push p g ih => exact Nat.le_trans (step_size _ _ _ _) (Nat.succ_le_succ ih)

def Pass.read (p : Pass J n) (w : J → Rat) (i : Fin n) : Rat :=
    value p.program w (p.addr i)

@[simp] private theorem emit_old (p : Pass J n) (g : Op J Unit p.size) (w : J → Rat) (i : Fin n) :
    (p.emit g).read w i.succ = p.read w i := rfl
@[simp] private theorem emit_new (p : Pass J n) (g : Op J Unit p.size) (w : J → Rat) :
    (p.emit g).read w 0 = g.eval w (fun _ => 0) (·+·) max (value p.program w) := rfl
@[simp] private theorem alias_old (p : Pass J n) (i j : Fin n) (w : J → Rat) :
    (p.alias i).read w j.succ = p.read w j := rfl
@[simp] private theorem alias_new (p : Pass J n) (i : Fin n) (w : J → Rat) :
    (p.alias i).read w 0 = p.read w i := rfl

private theorem step_old (p : Pass J n) (b : Fin n → Rat) (labels : I → Option J) (g : Op I Rat n)
    (w : J → Rat) (i : Fin n) : (step p b labels g).read w i.succ = p.read w i := by
  cases g with
  | input j => cases e : labels j <;> simp [step,e]
  | literal _ => rfl
  | add _ _ => rfl
  | choose l r => by_cases h : b l < b r <;> by_cases g : b r < b l <;> simp [step,h,g]

theorem compiled_gain (p : MinDAG I n) (b : I → Rat) (labels : I → Option J)
    (w : J → Rat) (i : Fin n) :
    (compile b labels p).read w i = (jets p b (slopeInput labels w) i).gain := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p g ih =>
    induction i using Fin.cases with
    | succ i =>
      change (step (compile b labels p) _ _ _).read w i.succ = _
      rw [step_old]; exact ih i
    | zero =>
      let old := jets p b (slopeInput labels w)
      let prev := compile b labels p
      change (step prev (primal p b) labels g).read w 0 =
        (g.eval (fun i => ⟨b i,slopeInput labels w i⟩) (fun c => ⟨c,0⟩) Jet.plus Jet.choose old).gain
      cases g with
      | input i => cases e : labels i <;> simp [step,e,Op.eval,slopeInput]
      | literal c => rfl
      | add l r =>
        change prev.read w l + prev.read w r = (old l).gain+(old r).gain
        rw [show prev.read w l = _ from ih l, show prev.read w r = _ from ih r]
      | choose l r =>
        have bl : (old l).base = primal p b l := base_is_primal p b _ l
        have br : (old r).base = primal p b r := base_is_primal p b _ r
        simp only [Op.eval,Jet.choose,bl,br,step]
        by_cases lt : primal p b l < primal p b r
        · simpa [lt] using ih l
        · by_cases gt : primal p b r < primal p b l
          · simpa [lt,gt] using ih r
          · simp only [lt,gt,ite_false,emit_new,Op.eval]
            change max (prev.read w l) (prev.read w r) = _
            rw [show prev.read w l = _ from ih l, show prev.read w r = _ from ih r]

end Mobius.TropicalDAG

namespace Mobius.TropicalDAG

def Jet.along (a : Jet) (t : Rat) := a.base - t*a.gain

private theorem smaller_stays (a b : Jet) (h : a.base < b.base) :
    ∃ δ : Rat, 0 < δ ∧ ∀ t : Rat, 0 < t → t < δ → a.along t ≤ b.along t := by
  by_cases hg : a.gain < b.gain
  · have pos : 0 < b.gain-a.gain := (Rat.lt_iff_sub_pos ..).mp hg
    have gap : 0 < b.base-a.base := (Rat.lt_iff_sub_pos ..).mp h
    refine ⟨(b.base-a.base)/(b.gain-a.gain), (Rat.lt_div_iff pos).2 (by simpa using gap), ?_⟩
    intro t _ ht
    have step := (Rat.lt_div_iff pos).mp ht
    unfold Jet.along
    grind
  · refine ⟨1,by decide,?_⟩
    intro t ht _
    have hm : t*b.gain ≤ t*a.gain := Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
    unfold Jet.along; grind

private theorem choice_window (a b : Jet) :
    ∃ δ : Rat, 0 < δ ∧ ∀ t : Rat, 0 < t → t < δ →
      min (a.along t) (b.along t) = (a.choose b).along t := by
  by_cases hab : a.base < b.base
  · obtain ⟨δ,hd,h⟩ := smaller_stays a b hab
    exact ⟨δ,hd,fun t ht he => by simp [Jet.choose,hab,Rat.min_def,h t ht he]⟩
  · by_cases hba : b.base < a.base
    · obtain ⟨δ,hd,h⟩ := smaller_stays b a hba
      refine ⟨δ,hd,?_⟩
      intro t ht he
      have hh := h t ht he
      simp [Jet.choose,hab,hba,Rat.min_def]; grind
    · have eq : a.base = b.base := by grind
      refine ⟨1,by decide,?_⟩
      intro t ht _
      have ht0 : 0 ≤ t := by grind
      by_cases gains : a.gain ≤ b.gain
      · have h := Rat.mul_le_mul_of_nonneg_left gains ht0
        simp [Jet.choose,Jet.along,eq,Rat.max_def,Rat.min_def,gains] at *
        grind
      · have rev : b.gain ≤ a.gain := by grind
        have h := Rat.mul_le_mul_of_nonneg_left rev ht0
        simp [Jet.choose,Jet.along,eq,Rat.max_def,Rat.min_def,gains] at *
        grind

/-- For each fixed direction there is one strictly positive rational window
valid at every gate. It may vary with direction; compilation never uses it. -/
theorem exact_window (p : MinDAG I n) (b d : I → Rat) :
    ∃ δ : Rat, 0 < δ ∧ ∀ (t : Rat), 0 < t → t < δ → ∀ i,
      primal p (fun x => b x - t*d x) i = (jets p b d i).along t := by
  induction p with
  | empty => exact ⟨1,by decide,fun _ _ _ i => Fin.elim0 i⟩
  | push p op ih =>
    obtain ⟨δ,hδ,window⟩ := ih
    let tmp := jets p b d
    have single : ∃ η : Rat, 0 < η ∧ ∀ t : Rat, 0 < t → t < η →
        op.eval (fun i => b i-t*d i) id (·+·) min (fun i => (tmp i).along t) =
        (op.eval (fun i => ⟨b i,d i⟩) (fun c => ⟨c,0⟩) Jet.plus Jet.choose tmp).along t := by
      cases op with
      | input i => exact ⟨1,by decide,fun _ _ _ => rfl⟩
      | literal c => exact ⟨1,by decide,fun _ _ _ => by simp [Op.eval,Jet.along]; grind⟩
      | add l r => exact ⟨1,by decide,fun _ _ _ => by simp [Op.eval,Jet.along,Jet.plus]; grind⟩
      | choose l r => exact choice_window _ _
    obtain ⟨η,hη,loc⟩ := single
    refine ⟨min δ η,by simp [Rat.min_def]; grind,?_⟩
    intro t ht he i
    have hd : t < δ := by simp [Rat.min_def] at he; grind
    have hn : t < η := by simp [Rat.min_def] at he; grind
    induction i using Fin.cases with
    | succ j => exact window t ht hd j
    | zero =>
      change op.eval _ id _ _ (primal p (fun x => b x-t*d x)) = _
      rw [show primal p (fun x => b x-t*d x) = _ from funext (window t ht hd)]
      exact loc t ht hn

theorem directional_restriction (p : MinDAG I n) (b : I → Rat) (labels : I → Option J)
    (w : J → Rat) :
    ∃ δ : Rat, 0 < δ ∧ ∀ (t : Rat), 0 < t → t < δ → ∀ i,
      primal p (fun x => b x-t*slopeInput labels w x) i =
        primal p b i - t*(compile b labels p).read w i := by
  obtain ⟨δ,hδ,hw⟩ := exact_window p b (slopeInput labels w)
  refine ⟨δ,hδ,?_⟩
  intro t ht he i
  rw [hw t ht he i,compiled_gain,Jet.along,base_is_primal]

/-- If the output of the original DAG has a known local affine expansion,
the compiled max-plus output is its exact gain. -/
theorem known_gain (p : MinDAG I n) (b : I → Rat) (labels : I → Option J)
    (i : Fin n) (w : J → Rat) (target : Rat)
    (h : ∃ η : Rat, 0 < η ∧ ∀ t : Rat, 0 < t → t < η →
      primal p (fun x => b x-t*slopeInput labels w x) i = primal p b i - t*target) :
    (compile b labels p).read w i = target := by
  obtain ⟨δ,hδ,hp⟩ := directional_restriction p b labels w
  obtain ⟨η,hη,hw⟩ := h
  let t := (min δ η)/2
  have pos : 0 < t := by
    apply (Rat.lt_div_iff (by decide : (0:Rat)<2)).mpr
    simp [Rat.min_def]; grind
  have lim : t < min δ η := by
    apply (Rat.div_lt_iff (by decide : (0:Rat)<2)).mpr
    simp [Rat.min_def]; grind
  have ld : t < δ := by simp [Rat.min_def] at lim; grind
  have le : t < η := by simp [Rat.min_def] at lim; grind
  have eq := (hp t pos ld i).symm.trans (hw t pos le)
  have mult : t*(compile b labels p).read w i = t*target := by grind
  by_cases lt : (compile b labels p).read w i < target
  · exact False.elim ((Rat.ne_of_lt ((Rat.mul_lt_mul_left pos).2 lt)) mult)
  · by_cases gt : target < (compile b labels p).read w i
    · exact False.elim ((Rat.ne_of_lt ((Rat.mul_lt_mul_left pos).2 gt)) mult.symm)
    · grind

end Mobius.TropicalDAG

namespace Mobius.TropicalDAG

/-- Pure max-plus outputs with zero as the only constant are subadditive,
including when intermediate gates have arbitrary fan-out. -/
theorem value_subadditive (p : MaxDAG J n) (u v : J → Rat) (i : Fin n) :
    value p (fun x => u x + v x) i ≤ value p u i + value p v i := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p g ih =>
    induction i using Fin.cases with
    | succ i => exact ih i
    | zero =>
      cases g with
      | input j => exact Rat.le_refl
      | literal c => change (0:Rat) ≤ 0+0; grind
      | add j k =>
        change value p _ j + value p _ k ≤
          (value p u j + value p u k) + (value p v j + value p v k)
        have := ih j; have := ih k; grind
      | choose j k =>
        change max (value p _ j) (value p _ k) ≤
          max (value p u j) (value p u k) + max (value p v j) (value p v k)
        have := ih j; have := ih k; grind

/-- An active maximum in a source minimization circuit would differentiate
to minimum. No pure target computes this function even on the three
displayed binary weight assignments. -/
theorem cannot_extract_binary_min (p : MaxDAG Bool n) (i : Fin n) :
    ¬ (∀ w : Bool → Rat, value p w i = min (w false) (w true)) := by
  intro h
  let u : Bool → Rat := fun b => if b then 0 else 1
  let v : Bool → Rat := fun b => if b then 1 else 0
  have bad := value_subadditive p u v i
  rw [h,h,h] at bad
  have impossible : ¬min (u false+v false) (u true+v true) ≤
      min (u false) (u true)+min (v false) (v true) := by dsimp [u,v]; grind
  exact impossible bad

/-- Agreement on the nonnegative integer grid alone need not determine a
one-sided slope at a positive integer base point. Both formulas use
nonnegative integer constants, minimum, and addition. -/
theorem lattice_agreement (x : Nat) :
    min (x+x) 3 = min (min (x+x) (x+1)) 3 := by omega

theorem different_left_slopes (t : Rat) (lo : 0<t) (hi : t<1/2) :
    let x := 2-t
    min (x+x) 3 = 3 ∧ min (min (x+x) (x+1)) 3 = 3-t := by
  dsimp; grind

end Mobius.TropicalDAG
