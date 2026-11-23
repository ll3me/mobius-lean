import Mobius.RigidityEnumeration
import Mobius.RigidityResidualData
import Mobius.RankTradeGauge
import Mobius.Residual

/-! A minimum-error residual has a separable sign pattern on its unique
translated crossing. The result concerns independent arbitrary row/column
phase tables and keeps track of individual tensor legs. -/
namespace Mobius.Rigidity.Residual
open Mobius.SignObstruction (B)
open Mobius.Rigidity.Enumeration (Phase Pair Direction ground plus ZeroPair OptPairs)
open Mobius.Rigidity.Kernel (key double dot dot_xor)
open Mobius.TwoPhases (score)
open Mobius.RankTradeGauge (physical sig)

set_option maxRecDepth 16384
set_option maxHeartbeats 50000000

def delta (p : Phase) (d x y : B) := p x y ^^ p (x ^^^ d) (y ^^^ d)

private theorem kernel_delta (p : ZeroPair true) (d x y : B) :
    delta p.val.1 d x y = (delta p.val.1 d x 0 ^^ delta p.val.1 d 0 y ^^ delta p.val.1 d 0 0) := by
  let v := Enumeration.lookup p.val
  let bits := double.read v
  have valid : Kernel.Good true v := by
    intro a b e he
    rw [Enumeration.eval_lookup true p.val p.property.1]
    exact p.property.2 _ _ _ he
  have cell (a b : B) : p.val.1 a b = double.generate bits (key false a b) := by
    have bound : ∀ a b : B, key false a b < 512 := by decide
    exact ((Kernel.generate_read double Kernel.double_valid v valid _ (bound a b)).trans
      (Enumeration.lookup_key p.val false a b)).symm
  have packed (u v : B) : delta p.val.1 d u v = dot bits.getLsbD double.k (mask d u v) := by
    unfold delta
    rw [cell u v,cell (u ^^^ d) (v ^^^ d)]
    exact (dot_xor _ _ _ _).symm
  rw [packed, packed, packed, packed,checked_mask d x y, dot_xor,dot_xor]

private theorem ground_delta (d : Direction) (x y : B) : delta (ground d).1 d.val x y = false := by
  have zero : ∀ a : B, Mobius.SignObstruction.quotient a a = 0 := by decide
  have clean : ∀ a : BitVec 3, a ^^^ (0 : BitVec 3) = a := by decide
  simp only [delta,ground,Mobius.SignObstruction.quotient_linear,zero,clean,Bool.xor_self]

private theorem delta_plus (p q : Pair) (d x y : B) :
    delta (plus p q).1 d x y = (delta p.1 d x y ^^ delta q.1 d x y) := by
  simp [delta,plus,Bool.xor_left_comm]

private theorem same_direction {r c : Phase} {a b : Direction}
    (ha : DirectionPattern r c a.val) (hb : DirectionPattern r c b.val) : a=b := by
  apply Subtype.ext
  have h := ha.2 0 0 a.val a.property
  have j := hb.2 0 0 a.val a.property
  rw [h] at j
  by_cases eqn : a.val=b.val
  · exact eqn
  · simp [eqn] at j

/-- The sign of the failed row product splits into two one-leg signs. -/
theorem separable_row_sign {r c : Phase} (d : Direction) (pat : DirectionPattern r c d.val) :
    ∃ a b : B → Bool, ∀ x y, delta r d.val x y = (a x ^^ b y) := by
  let p : Pair := (r,c)
  let z : ZeroPair true := ⟨plus p (ground d),fun ht => by contradiction,by
    intro x y e he
    rw [Enumeration.score_plus,pat.2 x y e he,(Enumeration.ground_pattern d).2 x y e he]
    simp⟩
  have phases (x y : B) : delta z.val.1 d.val x y = delta r d.val x y := by
    change delta (plus p (ground d)).1 d.val x y = _
    rw [delta_plus,ground_delta,Bool.xor_false]
  refine ⟨fun x => delta r d.val x 0, fun y => delta r d.val 0 y ^^ delta r d.val 0 0,?_⟩
  intro x y
  have equality := kernel_delta z d.val x y
  rw [phases,phases,phases,phases] at equality
  simpa only [Bool.xor_assoc] using equality

private theorem four_signs (a b c e : Bool) :
    sig a * sig b + sig c * sig e =
      (if a ^^ (b ^^ (c ^^ (e ^^ false))) then 0 else 2 * sig (a ^^ b)) := by
  cases a <;> cases b <;> cases c <;> cases e <;> decide

private theorem sign_xor (a b : Bool) : sig (a ^^ b) = sig a * sig b := by cases a <;> cases b <;> decide

private theorem even_pair (x y d : B) : x ^^^ y = (x ^^^ d) ^^^ (y ^^^ d) := by
  calc
    _ = (x ^^^ y) ^^^ (d ^^^ d) := by simp
    _ = _ := by ac_rfl

private theorem physical_step (r c : Phase) (x y e : B) (nz : e ≠ 0) :
    physical r c x y (y ^^^ e) (x ^^^ e) =
      if score r c (x,y,e) then 0 else 2 * sig (delta r e x y) := by
  have second : x ^^^ (y ^^^ e) = (x ^^^ e) ^^^ y := by ac_rfl
  have neq : ¬(x = x ^^^ e ∧ y = y ^^^ e) := by
    rintro ⟨h,_⟩
    apply nz
    apply (BitVec.xor_right_inj x).1
    simpa using h.symm
  have first := even_pair x y e
  simp only [physical,Mobius.RankTradeGauge.kernel,first,second,ite_true,neq,ite_false,
    Int.mul_zero,Int.sub_zero,score,Mobius.TwoPhases.corners,Mobius.SignObstruction.total,delta]
  exact four_signs (r x y) (r (x ^^^ e) (y ^^^ e)) (c x (y ^^^ e)) (c (x ^^^ e) y)

/-- At every optimum, the complete physical correction is a translated
crossing times two independent one-leg signs and the normalization factor 2. -/
theorem local_crossing (r c : Phase) (opt : Mobius.TwoPhases.failures r c = 256) :
    ∃ (d : Direction) (a b : B → Bool), ∀ x y u v : B,
      physical r c x y u v = if u = y ^^^ d.val ∧ v = x ^^^ d.val then
          2 * sig (a x) * sig (b y) else 0 := by
  obtain ⟨h,pattern,_⟩ := optimal_direction r c opt
  let d : Direction := ⟨h,pattern.1⟩
  obtain ⟨a,b,split⟩ := separable_row_sign d pattern
  refine ⟨d,a,b,?_⟩
  intro x y u v
  by_cases bal : x ^^^ y = v ^^^ u
  · obtain ⟨e,rfl,rfl⟩ := Mobius.SignObstruction.fiber_parameter x y u v bal
    have recognize : (y ^^^ e = y ^^^ d.val ∧ x ^^^ e = x ^^^ d.val) ↔ e = d.val := by
      simp only [BitVec.xor_right_inj, and_self]
    by_cases ez : e = 0
    · subst e
      have no := Ne.symm d.property
      rw [ite_eq_right (fun hb => no (recognize.1 hb))]
      cases hr : r x y <;> cases hc : c x y <;>
        simp [physical,Mobius.RankTradeGauge.kernel,sig,hr,hc]
    · rw [physical_step r c x y e ez, pattern.2 x y e ez]
      by_cases same : e = d.val
      · rw [ite_eq_left (recognize.2 same)]
        change (if decide (e ≠ d.val) then 0 else 2 * sig (delta r e x y)) = _
        rw [same,split,sign_xor]
        simp [Int.mul_assoc]
      · rw [ite_eq_right (fun hb => same (recognize.1 hb))]
        change (if decide (e ≠ d.val) then 0 else _) = 0
        simp [same]
  · rw [Mobius.RankTradeGauge.off_block r c x y u v bal]
    rw [ite_eq_right]
    rintro ⟨rfl,rfl⟩
    exact bal (even_pair x y d.val)

/-- Dividing the integer correction by its exact factor 2 gives a tensor
obtained from the crossing using only invertible signed permutations. -/
theorem normalized_local_crossing (r c : Phase) (opt : Mobius.TwoPhases.failures r c = 256) :
    ∃ (d : Direction) (a b : B → Bool), ∀ x y u v : B,
      physical r c x y u v / 2 = if u = y ^^^ d.val ∧ v = x ^^^ d.val then
          sig (a x) * sig (b y) else 0 := by
  obtain ⟨d,a,b,formula⟩ := local_crossing r c opt
  refine ⟨d,a,b,?_⟩
  intro x y u v
  rw [formula]
  split
  · rw [Int.mul_assoc]
    omega
  · decide

end Mobius.Rigidity.Residual
