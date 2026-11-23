import Mobius.ThreeFaceRealization

/-! Two distinct soft witnesses. One sacrifices only one Fano board, the
other changes only the common face of the optimum Fano attachment. Costs
are per-board geometric counts with multiplicity across boards. -/
namespace Mobius.ThreeFaceSoft

set_option Elab.async false
open Mobius.ThreeFaceBoards (U fano oldCore)
open Mobius.ThreeFaceColoring (Graph Simple Kind endpoints lines)
open Mobius.ThreeFaceRealization (linearPart)
open Mobius.ThreeFaceAttachment (paste mainPull capPull)
open Mobius.SignObstruction (B)

def boundary (x y : U) := x.getLsbD 1 && y.getLsbD 1

def image (x : ThreeFaceBoards.V 3) : BitVec 3 :=
  CommonCore.addBit (x.1 ^^^ (if x.2.getLsbD 1 then 1 else 0)) (x.2.getLsbD 2)

def oneCap (x y : ThreeFaceBoards.V 3) := EightSquare.phase (image x) (image y)

def onIntersection (x : ThreeFaceBoards.V 3) := x.1==0 && !(x.2.getLsbD 2)
def patchedCap (x y : ThreeFaceBoards.V 3) :=
  if onIntersection x && onIntersection y then boundary (x.2.setWidth 2) (y.2.setWidth 2)
  else ThreeFaceBoards.witness 1 x y

theorem overlap_values : ∀ x y : U,
    oneCap (oldCore x) (oldCore y)=boundary x y ∧ patchedCap (oldCore x) (oldCore y)=boundary x y := by decide

def directed (p : ThreeFaceBoards.World 3) (i : Fin 7) :=
  let t := ThreeFaceBoards.restrict p (fano i)
  TwoPhases.failures t t

def oneCost (i : Fin 7) : Nat := if i=0 then 384 else 128
def patchCost (i : Fin 7) : Nat := if i=0 then 216 else if i.val<3 then 154 else 128

private def wordTable (w : Nat) (x y : B) := w.testBit (16*x.toNat+y.toNat)
private def oneMask (i : Fin 7) : Nat :=
  [92632849143831790751730603865807407466083778010238162267569347542862126252032,
   92632964658216499619828500884351701257603407413882567957586170546039049027584,
   69385497716785790032563782662495998420430962986713013426521748125881140117504,
   68113367830145360849046156662737914504568770202869333992008385006280298070016,
   68113367830145360849046156662737914504568770202869333992008385006280298070016,
   68113367830145360849046156662737914504568770202869333992008385006280298070016,
   68113367830145360849046156662737914504568770202869333992008385006280298070016].getD i.val 0
private def patchMask (i : Fin 7) : Nat :=
  [93651390833085478969419876644150309180668016395276858810075639271037299851264,
   93651390833085477462915460151346925860078554825436918950232699082538661969920,
   93651390833085477462915460151346925860078554825436918950232699082538661969920,
   93651390833085477462915460151346925860078554825436918950527846987718014795776,
   93651390833085477462915460151346925860078554825436918950527846987718014795776,
   93651390833085477462915460151346925860078554825436918950527846987718014795776,
   93651390833085477462915460151346925860078554825436918950527846987718014795776].getD i.val 0

set_option maxRecDepth 32768 in
private theorem countMask0 :
    TwoPhases.failures (wordTable 92632849143831790751730603865807407466083778010238162267569347542862126252032) (wordTable 92632849143831790751730603865807407466083778010238162267569347542862126252032) = 768 := by decide +kernel

set_option maxRecDepth 32768 in
private theorem countMask1 :
    TwoPhases.failures (wordTable 92632964658216499619828500884351701257603407413882567957586170546039049027584) (wordTable 92632964658216499619828500884351701257603407413882567957586170546039049027584) = 256 := by decide +kernel

set_option maxRecDepth 32768 in
private theorem countMask2 :
    TwoPhases.failures (wordTable 69385497716785790032563782662495998420430962986713013426521748125881140117504) (wordTable 69385497716785790032563782662495998420430962986713013426521748125881140117504) = 256 := by decide +kernel

set_option maxRecDepth 32768 in
private theorem countMask3 :
    TwoPhases.failures (wordTable 68113367830145360849046156662737914504568770202869333992008385006280298070016) (wordTable 68113367830145360849046156662737914504568770202869333992008385006280298070016) = 256 := by decide +kernel

set_option maxRecDepth 32768 in
private theorem countMask4 :
    TwoPhases.failures (wordTable 93651390833085478969419876644150309180668016395276858810075639271037299851264) (wordTable 93651390833085478969419876644150309180668016395276858810075639271037299851264) = 432 := by decide +kernel

set_option maxRecDepth 32768 in
private theorem countMask5 :
    TwoPhases.failures (wordTable 93651390833085477462915460151346925860078554825436918950232699082538661969920) (wordTable 93651390833085477462915460151346925860078554825436918950232699082538661969920) = 308 := by decide +kernel

set_option maxRecDepth 32768 in
private theorem countMask6 :
    TwoPhases.failures (wordTable 93651390833085477462915460151346925860078554825436918950527846987718014795776) (wordTable 93651390833085477462915460151346925860078554825436918950527846987718014795776) = 256 := by decide +kernel

set_option maxRecDepth 32768 in
theorem cap_scores (i : Fin 7) :
    directed oneCap i=2*oneCost i ∧ directed patchedCap i=2*patchCost i := by
  have masks : ∀ (j : Fin 7) (x y : B),
      ThreeFaceBoards.restrict oneCap (fano j) x y=wordTable (oneMask j) x y ∧
      ThreeFaceBoards.restrict patchedCap (fano j) x y=wordTable (patchMask j) x y := by decide +kernel
  have cost (j : Fin 7) :
      TwoPhases.failures (wordTable (oneMask j)) (wordTable (oneMask j))=2*oneCost j ∧
      TwoPhases.failures (wordTable (patchMask j)) (wordTable (patchMask j))=2*patchCost j := by
    have cases7 : ∀ v : Fin 7, v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 ∨ v=5 ∨ v=6 := by decide
    rcases cases7 j with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨countMask0,countMask4⟩
    · exact ⟨countMask1,countMask5⟩
    · exact ⟨countMask2,countMask5⟩
    · exact ⟨countMask3,countMask6⟩
    · exact ⟨countMask3,countMask6⟩
    · exact ⟨countMask3,countMask6⟩
    · exact ⟨countMask3,countMask6⟩
  unfold directed
  rw [show ThreeFaceBoards.restrict oneCap (fano i) = wordTable (oneMask i) from
    funext fun x => funext fun y => (masks i x y).1,
    show ThreeFaceBoards.restrict patchedCap (fano i) = wordTable (patchMask i) from
    funext fun x => funext fun y => (masks i x y).2]
  exact cost i

theorem cap_penalties :
    ((List.finRange 7).map oneCost).sum=7*128+256 ∧
    ((List.finRange 7).map patchCost).sum=7*128+140 := by decide

end Mobius.ThreeFaceSoft
