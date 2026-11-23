import Mobius.ThreeFaceSoftCounts

namespace Mobius.ThreeFaceSoft
open Mobius.ThreeFaceBoards (U fano oldCore)
open Mobius.ThreeFaceColoring (Graph Simple Kind endpoints lines)
open Mobius.ThreeFaceRealization (linearPart)
open Mobius.ThreeFaceAttachment (paste mainPull capPull)
open Mobius.SignObstruction (B)

private def cyc (a b c : Nat) := decide ((a<b ∧ b<c) ∨ (b<c ∧ c<a) ∨ (c<a ∧ a<b))
private theorem rotate (a b c : Nat) : cyc b c a=cyc a b c := by
  unfold cyc; apply decide_eq_decide.mpr; grind
private theorem reverseCyc (a b c : Nat) (ab : a≠b) (bc : b≠c) (ca : c≠a) :
    cyc b a c= !cyc a b c := by
  apply Bool.eq_iff_iff.mpr
  simp only [cyc,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
  omega

private def quat (x y : Nat) := if x=0 ∨ y=0 then false else if x=y then true else cyc x y (x^^^y)
private def word (p q : Nat) (s : U) := if s=0 then 0 else if s=1 then p else if s=2 then q else p^^^q
private def localQuat (orientation : Bool) (a b : U) :=
  if a=0 ∨ b=0 then false else if a=b then true else
  if (a=1 ∧ b=2) ∨ (a=2 ∧ b=3) ∨ (a=3 ∧ b=1) then orientation else !orientation

private theorem local_quat (p q : Nat) (p0 : p≠0) (q0 : q≠0) (r0 : p^^^q≠0)
    (pq : p≠q) (pr : p≠p^^^q) (qr : q≠p^^^q) (a b : U) :
    quat (word p q a) (word p q b)=localQuat (cyc p q (p^^^q)) a b := by
  let r := p^^^q
  have pq' : q^^^p=r := Nat.xor_comm ..
  have pr' : p^^^r=q := by simp [r,←Nat.xor_assoc]
  have qr' : q^^^r=p := by rw [←pq']; simp [←Nat.xor_assoc]
  have rp' : r^^^p=q := (Nat.xor_comm ..).trans pr'
  have rq' : r^^^q=p := (Nat.xor_comm ..).trans qr'
  let o := cyc p q r
  have forward (x y z : Nat) (hx : x≠0) (hy : y≠0) (ne : x≠y) (mix : x^^^y=z) :
      quat x y=cyc x y z := by simp [quat,hx,hy,ne,mix]
  have h₁₂ : quat p q=o := forward p q r p0 q0 pq rfl
  have h₂₃ : quat q r=o := (forward q r p q0 r0 qr qr').trans (rotate p q r)
  have h₃₁ : quat r p=o := (forward r p q r0 p0 (Ne.symm pr) rp').trans ((rotate q r p).trans (rotate p q r))
  have neg := reverseCyc p q r pq qr (Ne.symm pr)
  have h₂₁ : quat q p= !o := (forward q p r q0 p0 (Ne.symm pq) pq').trans neg
  have h₁₃ : quat p r= !o := (forward p r q p0 r0 pr pr').trans ((rotate q p r).trans neg)
  have h₃₂ : quat r q= !o := (forward r q p r0 q0 (Ne.symm qr) rq').trans ((rotate p r q).trans ((rotate q p r).trans neg))
  have zL (x : Nat) : quat 0 x=false := by simp [quat]
  have zR (x : Nat) : quat x 0=false := by simp [quat]
  have diag (x : Nat) (nz : x≠0) : quat x x=true := by simp [quat,nz]
  have four : ∀ t : U, t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by decide
  rcases four a with rfl|rfl|rfl|rfl <;> rcases four b with rfl|rfl|rfl|rfl <;>
    simp [word,localQuat,←show r=p^^^q from rfl,zL,zR,diag p p0,diag q q0,diag r r0,
      h₁₂,h₂₃,h₃₁,h₂₁,h₁₃,h₃₂,o]

/-- Nonlinear in the quotient labels: orient each binary projective line
independently by its actual point order, ensuring quaternion signs on that line. -/
def mainAlong (h : U) (x y : CommonCore.Addr Nat) : Bool :=
  let t := ThreeFaceBoards.coreQuot h x.1
  let s := ThreeFaceBoards.coreQuot h y.1
  (if s then quat y.2 x.2 else quat x.2 y.2) ^^ (t && decide (y.2≠0)) ^^ (t && s)

abbrev mainTable := mainAlong 1

theorem main_boundary : ∀ h u v : U, mainAlong h (u,0) (v,0) =
    (ThreeFaceBoards.coreQuot h u && ThreeFaceBoards.coreQuot h v) := by decide

theorem main_on_core (u v : U) : mainTable (u,0) (v,0)=boundary u v := main_boundary 1 u v

private def board (h : U) (o : Bool) (x y : B) : Bool :=
  let a := ThreeFaceBoards.plane x
  let b := ThreeFaceBoards.plane y
  let t := ThreeFaceBoards.coreQuot h (x.setWidth 2)
  let s := ThreeFaceBoards.coreQuot h (y.setWidth 2)
  (if s then localQuat o b a else localQuat o a b) ^^ (t && decide (b≠0)) ^^ (t && s)

private theorem verified : ∀ (h : U), h≠0 → ∀ o : Bool, Rigidity.DirectionPattern (board h o) (board h o) (ThreeFaceBoards.pack h 0) := by
  unfold Rigidity.DirectionPattern
  decide +kernel

private theorem linearWord (p q : Nat) (x : B) : linearPart p q x=word p q (ThreeFaceBoards.plane x) := by
  have codes : ∀ x : B, ThreeFaceBoards.plane x =
      if x.getLsbD 3 then (if x.getLsbD 2 then 3 else 2) else (if x.getLsbD 2 then 1 else 0) := by decide
  cases a : x.getLsbD 2 <;> cases b : x.getLsbD 3 <;> simp only [linearPart,codes,a,b] <;> simp [word]

theorem main_along_optimal (g : Graph n m) (simple : Simple g) (k : Kind n m) (h : U) (hn : h≠0) :
    let r := CommonCore.restrict (mainAlong h) 0 (lines g k)
    Rigidity.DirectionPattern r r (ThreeFaceBoards.pack h 0) ∧ TwoPhases.failures r r=256 := by
  let p := (endpoints g k).1
  let q := (endpoints g k).2
  have p0 : p≠0 := ThreeFaceRealization.points_nonzero g simple k 0
  have q0 : q≠0 := ThreeFaceRealization.points_nonzero g simple k 1
  have r0 : p^^^q≠0 := ThreeFaceRealization.points_nonzero g simple k 2
  have pq : p≠q := fun e => (by decide : (0:Fin 3)≠1) (ThreeFaceRealization.points_distinct g simple k (u:=0) (v:=1) e)
  have pr : p≠p^^^q := fun e => (by decide : (0:Fin 3)≠2) (ThreeFaceRealization.points_distinct g simple k (u:=0) (v:=2) e)
  have qr : q≠p^^^q := fun e => (by decide : (1:Fin 3)≠2) (ThreeFaceRealization.points_distinct g simple k (u:=1) (v:=2) e)
  let o := cyc p q (p^^^q)
  have nz (s : U) : word p q s≠0 ↔ s≠0 := by
    have four : ∀ t : U, t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by decide
    rcases four s with rfl|rfl|rfl|rfl <;> simp [word,p0,q0,r0]
  have same : CommonCore.restrict (mainAlong h) 0 (lines g k)=board h o := by
    funext x y
    unfold CommonCore.restrict mainAlong board
    rw [ThreeFaceRealization.actual_board,ThreeFaceRealization.actual_board]
    simp only [←show p=(endpoints g k).1 from rfl,←show q=(endpoints g k).2 from rfl,
      linearWord,local_quat p q p0 q0 r0 pq pr qr,nz,o]
  dsimp only
  rw [same]
  exact ⟨verified h hn o,Rigidity.optimal_of_direction (verified h hn o)⟩

theorem main_optimal (g : Graph n m) (simple : Simple g) (k : Kind n m) :
    let t := CommonCore.restrict mainTable 0 (lines g k)
    Rigidity.DirectionPattern t t 1 ∧ TwoPhases.failures t t=256 := main_along_optimal g simple k 1 (by decide)

/-- Two separate global witnesses with different local profiles. -/
theorem soft_network (g : Graph n m) (simple : Simple g) :
    ∃ A B : ThreeFaceAttachment.World Nat,
      (∀ k, let t := CommonCore.restrict (mainPull A) 0 (lines g k)
            let u := CommonCore.restrict (mainPull B) 0 (lines g k)
            TwoPhases.failures t t=256 ∧ TwoPhases.failures u u=256) ∧
      (∀ j, directed (capPull A 0) j=2*oneCost j ∧ directed (capPull B 0) j=2*patchCost j) := by
  let A := paste 0 mainTable oneCap
  let B := paste 0 mainTable patchedCap
  have ha : mainPull A=mainTable := ThreeFaceAttachment.paste_main 0 mainTable oneCap (fun u v => ((overlap_values u v).1).trans (main_on_core u v).symm)
  have hb : mainPull B=mainTable := ThreeFaceAttachment.paste_main 0 mainTable patchedCap (fun u v => ((overlap_values u v).2).trans (main_on_core u v).symm)
  refine ⟨A,B,fun k => ?_,fun j => ?_⟩
  · dsimp only; rw [ha,hb]; exact ⟨(main_optimal g simple k).2,(main_optimal g simple k).2⟩
  · rw [show capPull A 0=oneCap from ThreeFaceAttachment.paste_cap ..,
      show capPull B 0=patchedCap from ThreeFaceAttachment.paste_cap ..]
    exact cap_scores j

end Mobius.ThreeFaceSoft
