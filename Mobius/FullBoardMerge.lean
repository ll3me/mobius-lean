import Mobius.CapAtlas
import Mobius.PortGap
import Mobius.MatrixPromise
import Mobius.OverlapPasses

/-! Merging complete, equally weighted four-dimensional boards. The
ownership partition in FullCaps assigns each geometric square one count. -/
namespace Mobius.FullBoardMerge
open Mobius.MatrixMerge (Mask rowCount varCount src)
open Mobius.MatrixPromise (Live allMask)
open Mobius.OverlapProtocols (Tree)
open Mobius.PortGap (Gap266)

/-- The complete-board construction needs to exclude only geometric
weights 129 through 132. Its actual input contains no port masks. -/
theorem compiled_iff (gap : Gap266) (f : AxisCompiler.Source m v) :
    (∃ r c : AxisGlue.World ((v+19*m)+3*(v+6*m)),
      FullCaps.unionCost (CapAtlas.compiled f) r c ≤ (7*m)*126+(v+6*m)*128) ↔
        AxisCompiler.Satisfiable f := by
  have w := CapAtlas.compiled_wiring f
  simp only [FullCaps.union_cost_eq _ _ w]
  rw [FullCaps.threshold_of_local (PortGap.geometric_local gap) _ _ w (AxisCompiler.admissible m)]
  exact ((CapAtlas.feasible_cores _ _ _ _).trans (AxisNetwork.feasible_iff_boolean _ _)).trans
    (AxisCompiler.boolean_iff f)

def AtThreshold (a b : Mask k) : Prop :=
  let m := rowCount k
  let v := varCount k
  ∃ r c : AxisGlue.World ((v+19*m)+3*(v+6*m)),
    FullCaps.unionCost (CapAtlas.compiled (src a b)) r c ≤
      (7*m)*126+(v+6*m)*128

theorem merge_iff (gap : Gap266) (a b : Mask k) :
    AtThreshold a b ↔ MatrixMerge.Merge a b :=
  (compiled_iff gap (src a b)).trans (MatrixMerge.src_iff a b)

theorem exact_protocol (gap : Gap266) (a b : Mask k) :
    ((MatrixMerge.thresholdProtocol k).run a b = true ↔ AtThreshold a b) ∧
      (MatrixMerge.thresholdProtocol k).cost a b = k*k := by
  obtain ⟨ok,cost⟩ := MatrixMerge.weighted_protocol a b
  exact ⟨(ok.trans (MatrixMerge.weighted_merge_iff a b)).trans (merge_iff gap a b).symm,cost⟩

/-- On this costly rejecting run, each party extends separately against an
all-allowing opposite input. Local work and rounds are unrestricted. -/
theorem hard_pair (gap : Gap266) (hk : 2≤k) (t : Tree (k*k))
    (correct : ∀ a b : Mask k, Live a → Live b → (t.run a b = true ↔ AtThreshold a b)) :
    ∃ a : Mask k, Live a ∧ Live (~~~a) ∧ AtThreshold a (allMask (k*k)) ∧
      AtThreshold (allMask (k*k)) (~~~a) ∧ ¬AtThreshold a (~~~a) ∧ k*k≤t.cost a (~~~a) := by
  have same (x y : Mask k) := (merge_iff gap x y).trans (MatrixMerge.weighted_merge_iff x y).symm
  obtain ⟨a,ha,hb,l,r,no,time⟩ := MatrixPromise.exact_weighted_live hk t
    fun x y hx hy => (correct x y hx hy).trans (same x y)
  exact ⟨a,ha,hb,(same ..).mpr l,(same ..).mpr r,fun e => no ((same ..).mp e),time⟩

theorem passes (gap : Gap266)
    (P : OverlapPasses.Scanner (List (MatrixMerge.Gate k)) (List (MatrixMerge.Gate k)) s)
    (p : Nat) (pos : 0<p)
    (correct : ∀ a b : Mask k,
      P.run p (MatrixMerge.leftRows a) (MatrixMerge.rightRows b) = true ↔ AtThreshold a b) :
    k*k ≤ (2*p-1)*s := by
  apply OverlapPasses.weighted_passes P p pos
  intro a b
  exact ((correct a b).trans (merge_iff gap a b)).trans (MatrixMerge.weighted_merge_iff a b).symm

end Mobius.FullBoardMerge
