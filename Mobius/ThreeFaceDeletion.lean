import Mobius.ThreeFaceSoft

/-! Every one of the seven Fano attachment pages is essential. For each
omitted page one actual global signing makes every remaining page optimal,
even when the graph does not admit a three-coloring. -/
namespace Mobius.ThreeFaceDeletion
open Mobius.SignObstruction (B)
open Mobius.ThreeFaceColoring (Graph Simple Kind lines)
open Mobius.ThreeFaceBoards (U V fano embed restrict oldCore coreQuot)
open Mobius.ThreeFaceAttachment (World paste mainPull capPull)
open Mobius.ThreeFaceSoft (mainAlong)

private def normal (i : Fin 7) := ([4,2,6,1,5,3,7] : List (BitVec 3)).getD i.val 0
def kernelOnOldCore (i : Fin 7) := ([1,1,1,2,2,3,3] : List U).getD i.val 0
private def dot (a b : BitVec 3) := (a.getLsbD 0 && b.getLsbD 0) ^^
  (a.getLsbD 1 && b.getLsbD 1) ^^ (a.getLsbD 2 && b.getLsbD 2)

def image (i : Fin 7) (x : V 3) :=
  let offset : U := if i=0 ∧ x.2.getLsbD 1 then 1 else 0
  CommonCore.addBit (x.1^^^offset) (dot (normal i) x.2)

def table (i : Fin 7) : ThreeFaceBoards.World 3 := fun x y => EightSquare.phase (image i x) (image i y)

theorem boundary_match : ∀ (i : Fin 7) (u v : U),
    table i (oldCore u) (oldCore v) = mainAlong (kernelOnOldCore i) (u,0) (v,0) := by decide +kernel

private def project (i j : Fin 7) (x : B) := image i (embed (fano j) x)
private def kernel (i j : Fin 7) : B :=
  (SignObstruction.directions.find? fun d => project i j d == 0).getD 0

private theorem linear : ∀ (i j : Fin 7) (x y : B),
    project i j (x^^^y)=project i j x^^^project i j y := by decide +kernel
private theorem kernel_check : ∀ i j : Fin 7, j≠i → kernel i j≠0 ∧
    ∀ d : B, d≠0 → (project i j d=0 ↔ d=kernel i j) := by decide +kernel

private theorem octonion_score : ∀ a b h : BitVec 3,
    (EightSquare.phase a b ^^ (EightSquare.phase (a^^^h) (b^^^h) ^^
      (EightSquare.phase a (b^^^h) ^^ (EightSquare.phase (a^^^h) b ^^ false)))) = decide (h≠0) := by
  decide +kernel

theorem all_other_pages (i j : Fin 7) (different : j≠i) :
    let p := restrict (table i) (fano j)
    Rigidity.DirectionPattern p p (kernel i j) ∧ TwoPhases.failures p p=256 := by
  let p := restrict (table i) (fano j)
  have facts := kernel_check i j different
  have pattern : Rigidity.DirectionPattern p p (kernel i j) := by
    refine ⟨facts.1,fun x y d nz => ?_⟩
    have eq : TwoPhases.score p p (x,y,d) = decide (project i j d≠0) := by
      unfold TwoPhases.score TwoPhases.corners SignObstruction.total
      change (EightSquare.phase (project i j x) (project i j y) ^^
        (EightSquare.phase (project i j (x^^^d)) (project i j (y^^^d)) ^^
         (EightSquare.phase (project i j x) (project i j (y^^^d)) ^^
         (EightSquare.phase (project i j (x^^^d)) (project i j y) ^^ false)))) = _
      simp only [linear]
      exact octonion_score ..
    rw [eq]
    exact decide_eq_decide.mpr (not_congr (facts.2 d nz))
  exact ⟨pattern,Rigidity.optimal_of_direction pattern⟩

/-- The omitted board's identity is quantified after the graph. The resulting
phase is still shared by both roles and by all main and attachment boards. -/
theorem delete_any (g : Graph n m) (simple : Simple g) (i : Fin 7) :
    ∃ w : World Nat,
      (∀ k : Kind n m, let t := CommonCore.restrict (mainPull w) 0 (lines g k)
        TwoPhases.failures t t=256) ∧
      (∀ j : Fin 7, j≠i → let t := restrict (capPull w 0) (fano j)
        TwoPhases.failures t t=256) := by
  let h := kernelOnOldCore i
  let w := paste 0 (mainAlong h) (table i)
  have hn : ∀ i, kernelOnOldCore i≠0 := by decide
  have main : mainPull w=mainAlong h := ThreeFaceAttachment.paste_main _ _ _ (boundary_match i)
  have caps : capPull w 0=table i := ThreeFaceAttachment.paste_cap ..
  refine ⟨w,fun k => ?_,fun j diff => ?_⟩
  · dsimp only; rw [main]; exact (ThreeFaceSoft.main_along_optimal g simple k h (hn i)).2
  · dsimp only; rw [caps]; exact (all_other_pages i j diff).2


/-- Restrict the quotient label to its actual public number of bits. -/
def numeric (x : ThreeFaceAttachment.Addr (BitVec q)) : ThreeFaceAttachment.Addr Nat :=
  (x.1,x.2.1.toNat,x.2.2.1,x.2.2.2)
def finiteWorld (q : Nat) (w : World Nat) : World (BitVec q) := fun x y => w (numeric x) (numeric y)

private theorem finite_cap (q : Nat) (w : World Nat) :
    capPull (finiteWorld q w) 0=capPull w 0 := by
  funext x y; rfl

private theorem finite_main (g : Graph n m) (w : World Nat) (k : Kind n m) :
    CommonCore.restrict (mainPull (finiteWorld (2*n+2*m) w)) 0 (ThreeFaceRealization.finiteLines g k) =
      CommonCore.restrict (mainPull w) 0 (lines g k) := by
  have addr (x : B) :
      numeric (ThreeFaceAttachment.mainAt (CommonCore.embed 0 (ThreeFaceRealization.finiteLines g k) x)) =
      ThreeFaceAttachment.mainAt (CommonCore.embed 0 (lines g k) x) := by
    by_cases c : x.toNat<4 <;>
      simp [numeric,ThreeFaceAttachment.mainAt,CommonCore.embed,c,ThreeFaceRealization.finite_value]
  funext x y
  exact (congrArg (fun a => w a _) (addr x)).trans (congrArg (w _) (addr y))

theorem delete_any_finite (g : Graph n m) (simple : Simple g) (i : Fin 7) :
    ∃ w : World (BitVec (2*n+2*m)),
      (∀ k : Kind n m, let t := CommonCore.restrict (mainPull w) 0 (ThreeFaceRealization.finiteLines g k)
        TwoPhases.failures t t=256) ∧
      (∀ j : Fin 7, j≠i → let t := restrict (capPull w 0) (fano j)
        TwoPhases.failures t t=256) := by
  obtain ⟨w,main,cap⟩ := delete_any g simple i
  exact ⟨finiteWorld _ w,fun k => by dsimp only; rw [finite_main]; exact main k,
    fun j diff => by dsimp only; rw [finite_cap]; exact cap j diff⟩

theorem soft_finite (g : Graph n m) (simple : Simple g) :
    ∃ A B : World (BitVec (2*n+2*m)),
      (∀ k : Kind n m, let t := CommonCore.restrict (mainPull A) 0 (ThreeFaceRealization.finiteLines g k)
                       let u := CommonCore.restrict (mainPull B) 0 (ThreeFaceRealization.finiteLines g k)
                       TwoPhases.failures t t=256 ∧ TwoPhases.failures u u=256) ∧
      (∀ j, ThreeFaceSoft.directed (capPull A 0) j=2*ThreeFaceSoft.oneCost j ∧
        ThreeFaceSoft.directed (capPull B 0) j=2*ThreeFaceSoft.patchCost j) := by
  obtain ⟨A,B,ma,ca⟩ := ThreeFaceSoft.soft_network g simple
  refine ⟨finiteWorld _ A,finiteWorld _ B,fun k => ?_,fun j => ?_⟩
  · dsimp only; rw [finite_main,finite_main]; exact ma k
  · rw [finite_cap,finite_cap]; exact ca j

end Mobius.ThreeFaceDeletion
