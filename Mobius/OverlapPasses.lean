import Mobius.MatrixMerge

/-! Multi-pass evaluation of a split instance. Arbitrary computation,
    shared subroutines and read-only advice may be included in either
    update. All mutable information retained between halves fits the
    transmitted state. -/
namespace Mobius.OverlapPasses

open Mobius.OverlapProtocols (intersects)
open Mobius.Bounded (Protocol)

private theorem disjoint_self (x : BitVec n) : ¬intersects x (~~~x) := by
  rintro ⟨i,h,t⟩
  simp only [BitVec.getLsbD_not,decide_eq_true i.isLt,Bool.true_and,h] at t
  contradiction

private theorem cross_equal {x y : BitVec n}
    (xy : ¬intersects x (~~~y)) (yx : ¬intersects y (~~~x)) : x=y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  cases l : x.getLsbD i <;> cases r : y.getLsbD i
  · rfl
  · exact False.elim (yx ⟨⟨i,hi⟩,r,by simp only [BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and,l]; rfl⟩)
  · exact False.elim (xy ⟨⟨i,hi⟩,l,by simp only [BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and,r]; rfl⟩)
  · rfl

/-- Each of the fixed number of messages may carry a whole state.
    Either party may send the next message according to the transcript. -/
theorem messages_lower (P : Protocol n s m) (correct : ∀ x y, P.run x y=true ↔ intersects x y) :
    n ≤ m*s := by
  have inj (x y : BitVec n) (eq : P.transcript x (~~~x)=P.transcript y (~~~y)) : x=y := by
    have l := Bounded.transcript_mix P x (~~~x) y (~~~y) eq
    have r := Bounded.transcript_mix P y (~~~y) x (~~~x) eq.symm
    exact cross_equal (fun h => disjoint_self y ((correct ..).mp (l ▸ (correct ..).mpr h)))
      (fun h => disjoint_self x ((correct ..).mp (r ▸ (correct ..).mpr h)))
  have cap : 2^n ≤ 2^(s*m) := by
    apply Bounded.fin_size_le (fun i : Fin (2^n) => (P.transcript (.ofFin i) (~~~(BitVec.ofFin i))).toFin)
    intro i j eq
    exact congrArg BitVec.toFin (inj (.ofFin i) (.ofFin j) (congrArg BitVec.ofFin eq))
  rw [Nat.mul_comm]
  exact Nat.le_of_not_lt (fun h => Nat.not_lt_of_ge cap (Nat.pow_lt_pow_right (by decide : 1<2) h))

/-- On each public pass, read the whole left block and then the whole right
    block. The same fixed program and parameters may be reused on all passes.
    The last right half may compute its answer locally. -/
structure Scanner (L R : Type) (s : Nat) where
  initial : BitVec s
  left : Nat → L → BitVec s → BitVec s
  right : Nat → R → BitVec s → BitVec s
  answer : R → BitVec s → Bool

def Scanner.from (P : Scanner L R s) (l : L) (r : R) :
    (extra pass : Nat) → BitVec s → Bool
  | 0, pass, state => P.answer r (P.right pass r (P.left pass l state))
  | extra+1, pass, state => P.from l r extra (pass+1) (P.right pass r (P.left pass l state))

def Scanner.run (P : Scanner L R s) (passes : Nat) (l : L) (r : R) : Bool :=
  match passes with
  | 0 => false
  | e+1 => P.from l r e 0 P.initial

private def simulate (P : Scanner L R s) (leftInput : BitVec n → L) (rightInput : BitVec n → R) :
    (extra pass : Nat) → BitVec s → Protocol n s (2*extra+1)
  | 0, pass, state =>
    .left (fun x => P.left pass (leftInput x) state) (fun mid =>
      .done fun y => P.answer (rightInput y) (P.right pass (rightInput y) mid))
  | extra+1, pass, state =>
    .left (fun x => P.left pass (leftInput x) state) (fun mid =>
      .right (fun y => P.right pass (rightInput y) mid) (simulate P leftInput rightInput extra (pass+1)))

private theorem simulate_run (P : Scanner L R s) (l : BitVec n → L) (r : BitVec n → R)
    (x y : BitVec n) (extra pass : Nat) (v : BitVec s) :
    (simulate P l r extra pass v).run x y = P.from (l x) (r y) extra pass v := by
  induction extra generalizing pass v with
  | zero => rfl
  | succ e ih => exact ih (pass+1) _

/-- One left-to-right handoff per pass and one return for each further pass. -/
def protocol (P : Scanner L R s) (l : BitVec n → L) (r : BitVec n → R)
    (p : Nat) (pos : 0<p) : Protocol n s (2*p-1) := by
  cases p with
  | zero => exact False.elim (Nat.lt_irrefl _ pos)
  | succ e =>
    have count : 2*(e+1)-1 = 2*e+1 := by omega
    exact count ▸ simulate P l r e 0 P.initial

theorem protocol_run (P : Scanner L R s) (l : BitVec n → L) (r : BitVec n → R)
    (p : Nat) (pos : 0<p) (x y : BitVec n) :
    (protocol P l r p pos).run x y = P.run p (l x) (r y) := by
  cases p with
  | zero => exact False.elim (Nat.lt_irrefl _ pos)
  | succ e =>
    exact simulate_run P l r x y e 0 _

theorem passes_lower (P : Scanner L R s) (l : BitVec n → L) (r : BitVec n → R) (p : Nat) (pos : 0<p)
    (correct : ∀ a b, P.run p (l a) (r b)=true ↔ intersects a b) : n ≤ (2*p-1)*s := by
  apply messages_lower (protocol P l r p pos)
  intro a b
  rw [protocol_run]
  exact correct a b

open Mobius.MatrixMerge (Mask Gate WeightedMerge UnweightedMerge leftRows rightRows)

/-- The local inputs are the concrete positive three-literal rows of the
    two separately computable halves of the geometric construction. -/
theorem weighted_passes (P : Scanner (List (Gate k)) (List (Gate k)) s) (p : Nat) (pos : 0<p)
    (correct : ∀ a b : Mask k, P.run p (leftRows a) (rightRows b)=true ↔ WeightedMerge a b) :
    k*k ≤ (2*p-1)*s := by
  apply passes_lower P leftRows rightRows p pos
  intro a b
  exact ((correct a b).trans (MatrixMerge.weighted_merge_iff a b)).trans (MatrixMerge.merge_iff a b)

theorem unweighted_passes (gap : AxisPortCost.Gap282)
    (P : Scanner (List (Gate k)) (List (Gate k)) s) (p : Nat) (pos : 0<p)
    (correct : ∀ a b : Mask k, P.run p (leftRows a) (rightRows b)=true ↔ UnweightedMerge a b) :
    k*k ≤ (2*p-1)*s := by
  apply passes_lower P leftRows rightRows p pos
  intro a b
  exact ((correct a b).trans (MatrixMerge.unweighted_merge_iff gap a b)).trans (MatrixMerge.merge_iff a b)

end Mobius.OverlapPasses
