import Mobius.TropicalPort
import Mobius.DirectionalWeights

/-! True multiplication is allowed at source gates. At a fixed base, the
right-sided gain is a weighted sum of the two child gains. A quadratic
remainder bound makes the claim about actual values on rational rays.
All reference indices in the program are real prior gates of a shared DAG.
-/
namespace Mobius.TropicalProduct

open Mobius.TropicalDAG (Jet extend MinDAG)

inductive Op (I K : Type) (n : Nat) where
  | input (i : I)
  | literal (c : K)
  | add (l r : Fin n)
  | product (l r : Fin n)
  | minimum (l r : Fin n)

inductive Program (I K : Type) : Nat → Type where
  | empty : Program I K 0
  | push {n} (p : Program I K n) (op : Op I K n) : Program I K (n+1)

def Op.eval (x : I → A) (c : K → A) (plus mul meet : A → A → A) (prev : Fin n → A) :
    Op I K n → A
  | .input i => x i
  | .literal k => c k
  | .add i j => plus (prev i) (prev j)
  | .product i j => mul (prev i) (prev j)
  | .minimum i j => meet (prev i) (prev j)

def Program.run (x : I → A) (c : K → A) (plus mul meet : A → A → A) :
    {n : Nat} → Program I K n → (Fin n → A)
  | _, .empty => Fin.elim0
  | _, .push p g =>
    let prev := p.run x c plus mul meet
    extend (g.eval x c plus mul meet prev) prev

def value (p : Program I K n) (c : K → Rat) (b : I → Rat) :=
    p.run b c (·+·) (·*·) min

def times (a b : Jet) : Jet := ⟨a.base*b.base,b.base*a.gain+a.base*b.gain⟩

def jets (p : Program I K n) (c : K → Rat) (b d : I → Rat) :=
    p.run (fun i => ⟨b i,d i⟩) (fun k => ⟨c k,0⟩) Jet.plus times Jet.choose

theorem base_is_value (p : Program I K n) (c : K → Rat) (b d : I → Rat) (i : Fin n) :
    (jets p c b d i).base = value p c b i := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p g ih =>
    induction i using Fin.cases with
    | succ i => exact ih i
    | zero =>
      cases g with
      | input j => rfl
      | literal k => rfl
      | add i j => change (jets p c b d i).base + (jets p c b d j).base = value p c b i + value p c b j; rw [ih i,ih j]
      | product i j => change (jets p c b d i).base * (jets p c b d j).base = value p c b i * value p c b j; rw [ih i,ih j]
      | minimum i j =>
        change ((jets p c b d i).choose (jets p c b d j)).base = min (value p c b i) (value p c b j)
        rw [← ih i,← ih j]
        unfold Jet.choose
        by_cases l : (jets p c b d i).base < (jets p c b d j).base <;>
          by_cases r : (jets p c b d j).base < (jets p c b d i).base <;>
            simp [l,r,Rat.min_def] <;> grind

/-- On a positive neighborhood, f(t)=base-t*gain+t²*r(t), with uniformly
bounded r(t). This implies the usual rational one-sided derivative. -/
def Approx (f : Rat → Rat) (a : Jet) : Prop :=
    ∃ M δ : Rat, 0 ≤ M ∧ 0 < δ ∧ ∀ t : Rat, 0 < t → t < δ →
       ∃ r : Rat, r.abs ≤ M ∧ f t = a.along t + t*t*r

private theorem abs_bounds (x : Rat) : -x.abs ≤ x ∧ x ≤ x.abs := by
  unfold Rat.abs; split <;> grind

private theorem abs_le {x M : Rat} (lo : -M ≤ x) (hi : x ≤ M) : x.abs ≤ M := by
  unfold Rat.abs; split <;> grind

private theorem add_bound {x y X Y : Rat} (hx : x.abs ≤ X) (hy : y.abs ≤ Y) :
    (x+y).abs ≤ X+Y := by
  obtain ⟨a,b⟩ := abs_bounds x
  obtain ⟨c,d⟩ := abs_bounds y
  apply abs_le <;> grind only

private theorem abs_product (x y : Rat) : (x*y).abs = x.abs*y.abs := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [Rat.abs_of_nonneg hx,Rat.abs_of_nonneg hy,Rat.abs_of_nonneg (Rat.mul_nonneg hx hy)]
  · have hy' : y ≤ 0 := by grind
    have hp := Rat.mul_le_mul_of_nonneg_left hy' hx
    rw [Rat.abs_of_nonneg hx,Rat.abs_of_nonpos hy',Rat.abs_of_nonpos (by grind)]
    grind
  · have hx' : x ≤ 0 := by grind
    have hp := Rat.mul_le_mul_of_nonneg_right hx' hy
    rw [Rat.abs_of_nonpos hx',Rat.abs_of_nonneg hy,Rat.abs_of_nonpos (by grind)]
    grind
  · have hx' : x ≤ 0 := by grind
    have hy' : y ≤ 0 := by grind
    have hp := Rat.mul_nonneg (by grind : 0 ≤ -x) (by grind : 0 ≤ -y)
    rw [Rat.abs_of_nonpos hx',Rat.abs_of_nonpos hy',Rat.abs_of_nonneg (by grind)]
    grind

private theorem mul_bound {x y X Y : Rat} (hx : x.abs ≤ X) (hy : y.abs ≤ Y) :
    (x*y).abs ≤ X*Y := by
  rw [abs_product]
  have hn := @Rat.abs_nonneg x
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hx Rat.abs_nonneg)
    (Rat.mul_le_mul_of_nonneg_left hy (by grind only))

private theorem linear (a : Jet) : Approx a.along a :=
    ⟨0,1,by decide,by decide,fun t _ _ => ⟨0,by simp,by grind⟩⟩

private theorem plus_approx {f g : Rat → Rat} {a b : Jet} (hf : Approx f a) (hg : Approx g b) :
    Approx (fun t => f t+g t) (a.plus b) := by
  obtain ⟨A,δ,A0,d0,hf⟩ := hf
  obtain ⟨B,η,B0,e0,hg⟩ := hg
  refine ⟨A+B,min δ η,by grind only,by grind,?_⟩
  intro t ht he
  obtain ⟨r,hr,fr⟩ := hf t ht (by grind)
  obtain ⟨s,hs,gs⟩ := hg t ht (by grind)
  refine ⟨r+s,add_bound hr hs,?_⟩
  change f t+g t = _
  rw [fr,gs]; unfold Jet.along Jet.plus; grind only

private theorem times_approx {f g : Rat → Rat} {a b : Jet} (hf : Approx f a) (hg : Approx g b) :
    Approx (fun t => f t*g t) (times a b) := by
  obtain ⟨A,δ,A0,d0,hf⟩ := hf
  obtain ⟨B,η,B0,e0,hg⟩ := hg
  let X := a.gain.abs+A
  let Y := b.gain.abs+B
  let M := a.base.abs*B+b.base.abs*A+X*Y
  have An := @Rat.abs_nonneg a.base
  have Bn := @Rat.abs_nonneg b.base
  have Xn : 0≤X := by dsimp [X]; have := @Rat.abs_nonneg a.gain; grind only
  have Yn : 0≤Y := by dsimp [Y]; have := @Rat.abs_nonneg b.gain; grind only
  have N : 0 ≤ M := by
    have := Rat.mul_nonneg An B0; have := Rat.mul_nonneg Bn A0; have := Rat.mul_nonneg Xn Yn
    dsimp [M]; grind only
  refine ⟨M,min 1 (min δ η),N,by grind,?_⟩
  intro t ht he
  obtain ⟨r,hr,fr⟩ := hf t ht (by grind)
  obtain ⟨s,hs,gs⟩ := hg t ht (by grind)
  let u := -a.gain+t*r
  let v := -b.gain+t*s
  have tb : t.abs ≤ 1 := by rw [Rat.abs_of_nonneg (by grind)]; grind
  have ra : (t*r).abs ≤ A := by simpa using (mul_bound tb hr)
  have sb : (t*s).abs ≤ B := by simpa using (mul_bound tb hs)
  have ub : u.abs ≤ X := add_bound (by simp [Rat.abs_neg]) ra
  have vb : v.abs ≤ Y := add_bound (by simp [Rat.abs_neg]) sb
  have aB := mul_bound (Rat.le_refl (a := a.base.abs)) hs
  have bA := mul_bound (Rat.le_refl (a := b.base.abs)) hr
  refine ⟨a.base*s+b.base*r+u*v,add_bound (add_bound aB bA) (mul_bound ub vb),?_⟩
  change f t*g t = _
  rw [fr,gs]; dsimp [u,v,Jet.along,times]; grind only

/-- Reuse the exact linear min-window on a three-gate pure DAG. -/
private theorem linear_choice (a b : Jet) : ∃ δ : Rat, 0 < δ ∧ ∀ t : Rat, 0<t → t<δ →
    min (a.along t) (b.along t) = (a.choose b).along t := by
  let p : MinDAG Bool 3 := .push (.push (.push .empty (.input false)) (.input true)) (.choose 1 0)
  let bs := fun k : Bool => if k then b.base else a.base
  let ds := fun k : Bool => if k then b.gain else a.gain
  obtain ⟨δ,hδ,hw⟩ := Mobius.TropicalDAG.exact_window p bs ds
  refine ⟨δ,hδ,?_⟩
  intro t ht he
  exact hw t ht he 0

private theorem choose_approx {f g : Rat → Rat} {a b : Jet} (hf : Approx f a) (hg : Approx g b) :
    Approx (fun t => min (f t) (g t)) (a.choose b) := by
  obtain ⟨A,δ,A0,d0,hf⟩ := hf
  obtain ⟨B,η,B0,e0,hg⟩ := hg
  obtain ⟨ζ,z0,hl⟩ := linear_choice a b
  let M := max A B
  refine ⟨M,min δ (min η ζ),by dsimp [M]; grind,by grind,?_⟩
  intro t ht he
  obtain ⟨r,hr,fr⟩ := hf t ht (by grind)
  obtain ⟨s,hs,gs⟩ := hg t ht (by grind)
  have lin := hl t ht (by grind)
  let v := min (f t) (g t) - (a.choose b).along t
  have pos := Rat.mul_pos ht ht
  have rm : -M ≤ r ∧ r ≤ M := by have := abs_bounds r; dsimp [M]; grind
  have sm : -M ≤ s ∧ s ≤ M := by have := abs_bounds s; dsimp [M]; grind
  have h1 := Rat.mul_le_mul_of_nonneg_left rm.1 (Rat.le_of_lt pos)
  have h2 := Rat.mul_le_mul_of_nonneg_left rm.2 (Rat.le_of_lt pos)
  have h3 := Rat.mul_le_mul_of_nonneg_left sm.1 (Rat.le_of_lt pos)
  have h4 := Rat.mul_le_mul_of_nonneg_left sm.2 (Rat.le_of_lt pos)
  have lo : -(t*t*M) ≤ v := by dsimp [v]; rw [←lin,fr,gs]; grind
  have hi : v ≤ t*t*M := by dsimp [v]; rw [←lin,fr,gs]; grind
  let e := v/(t*t)
  have eq : e*(t*t) = v := Rat.div_mul_cancel (Rat.ne_of_gt pos)
  refine ⟨e,abs_le (Rat.le_of_mul_le_mul_right (by grind only) pos)
      (Rat.le_of_mul_le_mul_right (by grind only) pos),?_⟩
  dsimp [v] at eq; grind only

/-- For the actual source arithmetic, at every gate and in every rational
direction the computed jet bounds a quadratic remainder. -/
theorem directional (p : Program I K n) (c : K → Rat) (b d : I → Rat) (i : Fin n) :
    Approx (fun t => value p c (fun x => b x-t*d x) i) (jets p c b d i) := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p g ih =>
    induction i using Fin.cases with
    | succ i => exact ih i
    | zero =>
      cases g with
      | input j => exact linear ⟨b j,d j⟩
      | literal k =>
        refine ⟨0,1,by decide,by decide,fun t _ _ => ⟨0,by simp,?_⟩⟩
        change c k = c k-t*0+t*t*0; grind only
      | add i j => exact plus_approx (ih i) (ih j)
      | product i j => exact times_approx (ih i) (ih j)
      | minimum i j => exact choose_approx (ih i) (ih j)

end Mobius.TropicalProduct

namespace Mobius.TropicalProduct

open Mobius.TropicalDAG (Jet)

/-- Identify a first-order gain from an exact affine expression for the
same physical value. A possibly nonzero bounded quadratic term disappears. -/
theorem gain_unique {f : Rat → Rat} {a : Jet} (h : Approx f a) (v : Rat)
    (aff : ∃ η : Rat, 0<η ∧ ∀ t : Rat, 0<t → t<η → f t=a.base-t*v) : a.gain=v := by
  obtain ⟨M,δ,hM,hδ,near⟩ := h
  obtain ⟨η,hη,window⟩ := aff
  by_cases eq : a.gain=v
  · exact eq
  · have pos : 0 < (a.gain-v).abs := Rat.abs_pos_iff.mpr (by grind)
    have den : 0 < M+1 := by grind only
    let hstar := (a.gain-v).abs/(M+1)
    have hs : 0<hstar := (Rat.lt_div_iff den).2 (by simpa using pos)
    let t := (min δ (min η hstar))/2
    have tpos : 0<t := (Rat.lt_div_iff (by decide : (0:Rat)<2)).2 (by grind)
    have tu : t < min δ (min η hstar) := (Rat.div_lt_iff (by decide : (0:Rat)<2)).2 (by grind)
    obtain ⟨r,hr,formula⟩ := near t tpos (by grind)
    have afft := window t tpos (by grind)
    rw [afft] at formula
    unfold Jet.along at formula
    have productEq : t*(a.gain-v) = t*(t*r) := by grind only
    have ordinary : a.gain-v = t*r := by
      by_cases l : a.gain-v < t*r
      · exact False.elim ((Rat.ne_of_lt ((Rat.mul_lt_mul_left tpos).2 l)) productEq)
      · by_cases r' : t*r < a.gain-v
        · exact False.elim ((Rat.ne_of_lt ((Rat.mul_lt_mul_left tpos).2 r')) productEq.symm)
        · grind only
    have less : t*(M+1) < (a.gain-v).abs := (Rat.lt_div_iff den).1 (by
      change t<hstar; grind)
    have bound := Rat.mul_le_mul_of_nonneg_left hr (Rat.le_of_lt tpos)
    rw [ordinary,abs_product,Rat.abs_of_nonneg (Rat.le_of_lt tpos)] at less
    grind only

namespace NatBase

open Mobius.DirectionalWeights (Wire Weights)
open Mobius.TropicalDAG (MaxDAG)

structure State (m : Nat) where
  base : Nat
  wire : Wire m

def inputWire : Option (Fin m) → Wire m
  | none => Mobius.DirectionalWeights.zero
  | some j => Mobius.DirectionalWeights.input j

def plus (a b : State m) : State m := ⟨a.base+b.base,Mobius.DirectionalWeights.plus a.wire b.wire⟩
def mul (a b : State m) : State m :=
  ⟨a.base*b.base,Mobius.DirectionalWeights.productGain a.base b.base a.wire b.wire⟩
def meet (a b : State m) : State m :=
  if a.base < b.base then a
  else if b.base < a.base then b
  else ⟨a.base,Mobius.DirectionalWeights.maximum a.wire b.wire⟩

def states (p : Program I Nat s) (b : I → Nat) (labels : I → Option (Fin m)) :=
    p.run (fun i => ⟨b i,inputWire (labels i)⟩) (fun k => ⟨k,Mobius.DirectionalWeights.zero⟩)
      plus mul meet

def liftState (a : State m) (w : Weights m) : Jet := ⟨a.base,a.wire.original w⟩

private theorem lift_plus (a b : State m) (w : Weights m) :
    liftState (plus a b) w = (liftState a w).plus (liftState b w) := by
  simp [liftState,plus,Jet.plus,Mobius.DirectionalWeights.plus]

private theorem lift_mul (a b : State m) (w : Weights m) :
    liftState (mul a b) w = times (liftState a w) (liftState b w) := by
  simp [liftState,mul,times,Mobius.DirectionalWeights.productGain,Mobius.DirectionalWeights.plus,
    Mobius.DirectionalWeights.scale]

private theorem lift_meet (a b : State m) (w : Weights m) :
    liftState (meet a b) w = (liftState a w).choose (liftState b w) := by
  by_cases hab : a.base < b.base <;> by_cases hba : b.base < a.base <;>
    simp [liftState,meet,Jet.choose,hab,hba,Mobius.DirectionalWeights.maximum,
      Rat.natCast_lt_natCast,Nat.max_def,Rat.max_def,Rat.natCast_le_natCast] <;> grind

/-- The natural-number wire semantics is precisely the rational forward
derivative of true source products evaluated on natural directions. -/
theorem lift_states (p : Program I Nat s) (b : I → Nat) (labels : I → Option (Fin m))
    (w : Weights m) (i : Fin s) :
    liftState (states p b labels i) w = jets p (fun k => k) (fun x => b x)
      (Mobius.TropicalDAG.slopeInput labels (fun j => w j)) i := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p g ih =>
    induction i using Fin.cases with
    | succ i => exact ih i
    | zero =>
      cases g with
      | input x =>
        change liftState ⟨b x,inputWire (labels x)⟩ w =
            ⟨b x,Mobius.TropicalDAG.slopeInput labels (fun j => w j) x⟩
        cases eq : labels x <;> simp [inputWire,liftState,Mobius.TropicalDAG.slopeInput,eq,
          Mobius.DirectionalWeights.zero,Mobius.DirectionalWeights.input]
      | literal k => rfl
      | add l r =>
        change liftState (plus (states p b labels l) (states p b labels r)) w = _
        rw [lift_plus,ih l,ih r]; rfl
      | product l r =>
        change liftState (mul (states p b labels l) (states p b labels r)) w = _
        rw [lift_mul,ih l,ih r]; rfl
      | minimum l r =>
        change liftState (meet (states p b labels l) (states p b labels r)) w = _
        rw [lift_meet,ih l,ih r]; rfl

/-- One new max-plus gate per source gate, with one shared global zero.
Strict minima become additions to zero. A nonzero multiplier is wired
through; a zero multiplier takes its reference from that shared zero. -/
def normalizedOp (src : Fin s → State m) (labels : I → Option (Fin m)) :
    Op I Nat s → Mobius.TropicalDAG.Op (Fin m) Unit (s+1)
  | .input i => match labels i with
      | some j => .input j
      | none => .literal ()
  | .literal _ => .literal ()
  | .add i j => .add i.castSucc j.castSucc
  | .product i j => .add (if (src j).base=0 then Fin.last s else i.castSucc)
                         (if (src i).base=0 then Fin.last s else j.castSucc)
  | .minimum i j => if (src i).base < (src j).base then .add i.castSucc (Fin.last s)
      else if (src j).base < (src i).base then .add j.castSucc (Fin.last s)
      else .choose i.castSucc j.castSucc

def normalize (b : I → Nat) (labels : I → Option (Fin m)) :
    {s : Nat} → Program I Nat s → MaxDAG (Fin m) (s+1)
  | _, .empty => .push .empty (.literal ())
  | _, .push p g => .push (normalize b labels p) (normalizedOp (states p b labels) labels g)

private theorem last_zero (p : Program I Nat s) (b : I → Nat) (labels : I → Option (Fin m))
    (w : Fin m → Rat) : Mobius.TropicalDAG.value (normalize b labels p) w (Fin.last s) = 0 := by
  induction p with
  | empty => rfl
  | push p g ih => exact ih

theorem normalized_value (p : Program I Nat s) (b : I → Nat) (labels : I → Option (Fin m))
    (w : Weights m) (i : Fin s) :
    Mobius.TropicalDAG.value (normalize b labels p) (fun j => w j) i.castSucc =
       ((states p b labels i).wire.normalized w : Rat) := by
  induction p with
  | empty => exact Fin.elim0 i
  | push p g ih =>
    induction i using Fin.cases with
    | succ i => exact ih i
    | zero =>
      let src := states p b labels
      let tgt := Mobius.TropicalDAG.value (normalize b labels p) (fun j => (w j : Rat))
      have z : tgt (Fin.last _) = 0 := last_zero _ _ _ _
      have agree (i) : tgt i.castSucc = ((src i).wire.normalized w : Rat) := ih i
      change (normalizedOp src labels g).eval (fun j => (w j : Rat)) (fun _ => 0)
          (·+·) max tgt = ((g.eval (fun j => ⟨b j,inputWire (labels j)⟩)
            (fun k => ⟨k,Mobius.DirectionalWeights.zero⟩) plus mul meet src).wire.normalized w : Rat)
      cases g with
      | input j =>
        cases e : labels j <;> simp [e,normalizedOp,Mobius.TropicalDAG.Op.eval,Op.eval,inputWire,
          Mobius.DirectionalWeights.zero,Mobius.DirectionalWeights.input]
      | literal _ => rfl
      | add i j => simp [normalizedOp,Op.eval,Mobius.TropicalDAG.Op.eval,plus,
          Mobius.DirectionalWeights.plus,agree]
      | product i j =>
        by_cases l : (src i).base=0 <;> by_cases r : (src j).base=0 <;>
          simp [normalizedOp,Op.eval,Mobius.TropicalDAG.Op.eval,mul,Mobius.DirectionalWeights.productGain,
             Mobius.DirectionalWeights.scale,Mobius.DirectionalWeights.plus,l,r,agree,z] <;> grind
      | minimum i j =>
        by_cases l : (src i).base < (src j).base <;> by_cases r : (src j).base < (src i).base <;>
          simp [normalizedOp,Op.eval,Mobius.TropicalDAG.Op.eval,meet,Mobius.DirectionalWeights.maximum,
            l,r,agree,z,Nat.max_def,Rat.max_def,Rat.natCast_le_natCast] <;> grind

theorem singleton_normalization (p : Program I Nat s) (b : I → Nat) (labels : I → Option (Fin m))
    (out : Fin s) (bound : ∀ j, (states p b labels out).wire.original
      (Mobius.DirectionalWeights.singleton j) ≤ 1) (w : Weights m) :
    Mobius.TropicalDAG.value (normalize b labels p) (fun j => w j) out.castSucc =
    (jets p (fun k => (k:Rat)) (fun i => (b i:Rat))
      (Mobius.TropicalDAG.slopeInput labels (fun i => w i)) out).gain := by
  rw [normalized_value, Mobius.DirectionalWeights.singleton_bounded_output _ bound w]
  exact congrArg Jet.gain (lift_states p b labels w out)

end NatBase
end Mobius.TropicalProduct

namespace Mobius.TropicalProduct

open Mobius.PortGraphGeometry (Edge)
open Mobius.TropicalMWIS (Graph Prices Coloring gain mwis energy optimum)
open Mobius.DirectionalWeights (Weights singleton)
open Mobius.TropicalDAG (Jet slopeInput)
open Mobius.TropicalPort (geometricMinimum graph)

def natDegree (g : Graph n) (v : Fin n) :=
    (g.map (fun e => (if v=e.1 then 1 else 0 : Nat)+(if v=e.2 then 1 else 0))).sum

def natBase (g : Graph n) (slot : Fin n × Bool) : Nat :=
    1+if slot.2 then natDegree g slot.1 else 0

private theorem degree_cast (g : Graph n) (v : Fin n) :
    (natDegree g v : Rat) = Mobius.TropicalMWIS.degree g v := by
  induction g with
  | nil => rfl
  | cons e es ih =>
    by_cases l : v=e.1 <;> by_cases r : v=e.2 <;>
      simp_all [natDegree,Mobius.TropicalMWIS.degree,Mobius.TropicalMWIS.sumQ] <;> grind only

theorem base_cast (g : Graph n) : (fun i => (natBase g i : Rat)) = Mobius.TropicalMWIS.base g := by
  funext i; obtain ⟨v,b⟩ := i
  cases b <;> simp [natBase,Mobius.TropicalMWIS.base,Mobius.TropicalMWIS.bit,degree_cast] <;> grind only

private theorem base_nonnegative (g : Graph n) (i : Fin n × Bool) :
    0 ≤ Mobius.TropicalMWIS.base g i := by rw [←base_cast]; grind

/-- Correctness on the nonnegative rational neighborhood implies that the
actual product-rule jet computes the MWIS gain at every rational direction. -/
theorem geometric_gain (es : List (Edge n)) (p : Program (Fin n × Bool) Nat s) (out : Fin s)
    (correct : ∀ h : Prices n, (∀ i,0≤h i) →
      value p (fun k => (k:Rat)) h out = geometricMinimum es h) (w : Fin n → Rat) :
    (jets p (fun k => (k:Rat)) (Mobius.TropicalMWIS.base (graph es))
      (slopeInput Mobius.TropicalMWIS.labels w) out).gain = mwis (graph es) w := by
  let g := graph es
  let b := Mobius.TropicalMWIS.base g
  let d := slopeInput Mobius.TropicalMWIS.labels w
  let j := jets p (fun k => (k:Rat)) b d out
  apply gain_unique (directional p (fun k => (k:Rat)) b d out)
  obtain ⟨δ,hδ,win⟩ := Mobius.TropicalMWIS.mwis_window g w
  refine ⟨δ,hδ,?_⟩
  intro t ht he
  obtain ⟨pos,eq⟩ := win t ht he
  have hb : j.base = (n:Rat)+g.length := by
    rw [show j.base = _ from base_is_value p (fun k => (k:Rat)) b d out,
      correct b (base_nonnegative g),Mobius.TropicalPort.geometric_eq_graph]
    exact Mobius.TropicalMWIS.at_base g
  change value p _ (Mobius.TropicalMWIS.perturbed g w t) out = j.base-t*mwis g w
  rw [correct _ pos,Mobius.TropicalPort.geometric_eq_graph,hb]
  exact eq

private theorem single_sum {α} [DecidableEq α] (xs : List α) (v : α) (a : Rat) (h : xs.Nodup) :
    Mobius.TropicalMWIS.sumQ xs (fun x => if x=v then a else 0) =
      if v∈xs then a else 0 := by
  induction xs with
  | nil => simp [Mobius.TropicalMWIS.sumQ]
  | cons x xs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp h
    change (if x=v then a else 0) + Mobius.TropicalMWIS.sumQ xs (fun y => if y=v then a else 0) = _
    rw [ih tail]
    by_cases eq : x=v
    · subst v; simp [fresh,Rat.add_zero]
    · simp [eq,Ne.symm eq,Rat.zero_add]

theorem singleton_mwis_le (g : Graph n) (v : Fin n) :
    mwis g (fun j => (singleton v j : Rat)) ≤ 1 := by
  let z := (Mobius.TropicalMWIS.independent g).maxOn
    (gain (fun j => (singleton v j : Rat))) (by
      apply List.ne_nil_of_mem (a := fun _ => false)
      simp [Mobius.TropicalMWIS.independent,Mobius.TropicalMWIS.colors,
        Mobius.TourCount.assignments_complete,Mobius.TropicalMWIS.conflicts,Mobius.TropicalMWIS.hit])
  change gain (fun j => (singleton v j : Rat)) z ≤ 1
  have cell (j : Fin n) : (if z j then ((singleton v j : Nat):Rat) else 0) =
      if j=v then (if z v then (1:Rat) else 0) else 0 := by
    by_cases eq : j=v
    · subst j; cases _h : z v <;> simp [Mobius.DirectionalWeights.singleton]
    · simp [Mobius.DirectionalWeights.singleton,eq]
  unfold gain
  rw [show (fun j => _) = _ from funext cell,single_sum _ _ _ (List.nodup_finRange n)]
  simp; split <;> grind

/-- The normalized circuit is independent of w. All input constants of
the original product program are natural. Every accepting program for
the real square-table objective has a pure max-plus simulation on
nonnegative integer weights, in particular on all binary weights. -/
theorem compiled_geometric_product_for_mwis (es : List (Edge n))
    (p : Program (Fin n × Bool) Nat s) (out : Fin s)
    (correct : ∀ h : Prices n, (∀ i,0≤h i) →
      value p (fun k => (k:Rat)) h out = geometricMinimum es h) :
    ∀ w : Weights n,
      Mobius.TropicalDAG.value
        (NatBase.normalize (natBase (graph es)) Mobius.TropicalMWIS.labels p)
        (fun j => w j) out.castSucc = mwis (graph es) (fun j => w j) := by
  let g := graph es
  let b := natBase g
  let label := @Mobius.TropicalMWIS.labels n
  have realGain (w : Weights n) :
      (jets p (fun k => (k:Rat)) (fun i => (b i:Rat))
        (slopeInput label (fun j => w j)) out).gain = mwis g (fun j => w j) := by
    change (jets p (fun k => (k:Rat)) (fun i => (natBase g i:Rat)) _ out).gain = _
    rw [base_cast]
    exact geometric_gain es p out correct _
  have bounded (j : Fin n) : (NatBase.states p b label out).wire.original (singleton j) ≤ 1 := by
    have lift := congrArg Jet.gain (NatBase.lift_states p b label (singleton j) out)
    change (((NatBase.states p b label out).wire.original (singleton j) : Nat):Rat) = _ at lift
    rw [realGain] at lift
    apply Rat.natCast_le_natCast.mp
    change _ ≤ (1:Rat)
    rw [lift]
    exact singleton_mwis_le g j
  intro w
  exact (NatBase.singleton_normalization p b label out bounded w).trans (realGain w)

end Mobius.TropicalProduct
