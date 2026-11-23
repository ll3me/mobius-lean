import Mobius.CommonCore
import Mobius.ThreeFaceBoards

/-! Eliminate direction pinning using seven genuine Fano boards in private
coordinates. The main core and the attachment share exactly one two-plane. -/
namespace Mobius.ThreeFaceAttachment
open Mobius.CommonCore (Core OneOn)
open Mobius.SignObstruction (B)
open Mobius.ThreeFaceBoards (U fano oldCore)

abbrev Addr (Point : Type u) := Core × Point × Core × Bool
abbrev World (Point : Type u) := Addr Point → Addr Point → Bool

def mainAt (x : CommonCore.Addr Point) : Addr Point := (x.1,x.2,0,false)
def capAt (o : Point) (x : ThreeFaceBoards.V 3) : Addr Point :=
  (x.2.setWidth 2,o,x.1,x.2.getLsbD 2)
def mainPull (r : World Point) : CommonCore.Table Point := fun x y => r (mainAt x) (mainAt y)
def capPull (r : World Point) (o : Point) : ThreeFaceBoards.World 3 := fun x y => r (capAt o x) (capAt o y)

private theorem old_coordinates : ∀ u : U, ((u.setWidth 3).setWidth 2)=u ∧ (u.setWidth 3).getLsbD 2=false := by decide

theorem contact (o : Point) (u : Core) : capAt o (oldCore u) = mainAt (u,o) := by
  simp only [capAt,oldCore,mainAt,(old_coordinates u).1,(old_coordinates u).2]

private theorem three_bits : ∀ w : BitVec 3, CommonCore.addBit (w.setWidth 2) (w.getLsbD 2)=w := by decide
private theorem low_only : ∀ w : BitVec 3, w.getLsbD 2=false → (w.setWidth 2).setWidth 3=w := by decide

theorem actual_intersection (o : Point) (x : CommonCore.Addr Point) (y : ThreeFaceBoards.V 3) :
    mainAt x=capAt o y ↔ ∃ u : Core, x=(u,o) ∧ y=oldCore u := by
  constructor
  · rcases x with ⟨u,p⟩
    rcases y with ⟨h,w⟩
    intro eq
    simp only [mainAt,capAt,Prod.mk.injEq] at eq
    refine ⟨u,Prod.ext rfl eq.2.1,Prod.ext eq.2.2.1.symm ?_⟩
    change w=u.setWidth 3
    rw [eq.1]; exact (low_only w eq.2.2.2.symm).symm
  · rintro ⟨u,rfl,rfl⟩; exact (contact o u).symm

def capProject (x : Addr Point) : ThreeFaceBoards.V 3 := (x.2.2.1,CommonCore.addBit x.1 x.2.2.2)
def mainProject (x : Addr Point) : CommonCore.Addr Point := (x.1,x.2.1)

theorem project_cap (o : Point) (x : ThreeFaceBoards.V 3) : capProject (capAt o x)=x :=
  Prod.ext rfl (three_bits x.2)

private theorem add_false : ∀ x : Core, CommonCore.addBit x false=x.setWidth 3 := by decide

/-- Shared entries are read from the attachment if both Point coordinates are
the common origin. Other main-chart entries retain their original values. -/
def paste [DecidableEq Point] (o : Point) (main : CommonCore.Table Point) (cap : ThreeFaceBoards.World 3)
    (x y : Addr Point) :=
  if x.2.1=o ∧ y.2.1=o then cap (capProject x) (capProject y) else main (mainProject x) (mainProject y)

theorem paste_cap [DecidableEq Point] (o : Point) (main : CommonCore.Table Point) (cap : ThreeFaceBoards.World 3) :
    capPull (paste o main cap) o=cap := by
  funext x y; simp [capPull,paste,show ∀ x, (capAt o x).2.1=o from fun _ => rfl,project_cap]

theorem paste_main [DecidableEq Point] (o : Point) (main : CommonCore.Table Point) (cap : ThreeFaceBoards.World 3)
    (agree : ∀ u v, cap (oldCore u) (oldCore v) = main (u,o) (v,o)) :
    mainPull (paste o main cap)=main := by
  funext x y
  obtain ⟨u,p⟩ := x; obtain ⟨v,q⟩ := y
  by_cases hp : p=o <;> by_cases hq : q=o
  · subst p; subst q
    simpa [mainPull,paste,mainAt,capProject,oldCore,add_false] using agree u v
  all_goals simp [mainPull,paste,mainAt,mainProject,hp,hq]

/-- Both families count the original full four-bit directed failure measure. -/
def Feasible (o : Point) (lines : I → Fin 3 → Point) : Prop :=
  ∃ r c : World Point,
    (∀ i, TwoPhases.failures (CommonCore.restrict (mainPull r) o (lines i))
      (CommonCore.restrict (mainPull c) o (lines i))=256) ∧
    (∀ j, TwoPhases.failures (ThreeFaceBoards.restrict (capPull r o) (fano j))
      (ThreeFaceBoards.restrict (capPull c o) (fano j))=256)

private theorem main_core_read (o : Point) (line : Fin 3 → Point) (r c : World Point)
    (d : B) (small : d.toNat<4) :
    TwoPhases.score (CommonCore.restrict (mainPull r) o line) (CommonCore.restrict (mainPull c) o line) (0,0,d) =
      ThreeFaceBoards.worldScore (capPull r o) (capPull c o) (oldCore 0) (oldCore 0) (oldCore (d.setWidth 2)) := by
  have emb : CommonCore.embed o line d=(d.setWidth 2,o) := by simp [CommonCore.embed,small]
  have z : CommonCore.embed o line 0#4=(0,o) := rfl
  have add (u : U) : ThreeFaceBoards.add (oldCore 0#2) (oldCore u)=oldCore u := by
    unfold ThreeFaceBoards.add oldCore; simp
  simp [TwoPhases.score,TwoPhases.corners,SignObstruction.total,CommonCore.restrict,emb,
    ThreeFaceBoards.worldScore,add,capPull,contact,mainPull,z]

/-- Unrestricted simultaneous full-board optimality encodes the one-on-each-
line condition with no prescribed boundary data or exceptional direction. -/
theorem attached_iff (o : Point) (lines : I → Fin 3 → Point) (off : ∀ i j, lines i j≠o) :
    Feasible o lines ↔ ∃ chosen : Point → Bool, OneOn lines chosen := by
  classical
  constructor
  · rintro ⟨r,c,mainOpt,capOpt⟩
    have profiles : CommonCore.Profiles o lines (mainPull r) (mainPull c) := by
      intro i
      obtain ⟨d,pat,_⟩ := Rigidity.optimal_direction _ _ (mainOpt i)
      refine ⟨d,?_,pat⟩
      apply Nat.le_of_not_lt; intro small
      have lowNZ : ∀ d : B, d≠0 → d.toNat<4 → d.setWidth 2≠0 := by decide
      have capGood := ThreeFaceBoards.attachment_forces_good _ _ capOpt 0 0 _ (lowNZ d pat.1 small)
      have mainBad := pat.2 0 0 d pat.1
      rw [main_core_read o (lines i) r c d small,capGood] at mainBad
      simp at mainBad
    exact ⟨_,CommonCore.choice_of_profiles o lines (mainPull r) (mainPull c) profiles⟩
  · rintro ⟨chosen,yes⟩
    let t := CommonCore.world o chosen
    obtain ⟨p,cap,agrees⟩ := ThreeFaceBoards.fano_attached 1 (by decide)
    have matchCore (u v : Core) : p (oldCore u) (oldCore v)=t (u,o) (v,o) := by
      simpa [t,CommonCore.world,CommonCore.image,add_false] using agrees u v
    let W := paste o t p
    have hm : mainPull W=t := paste_main o t p matchCore
    have hc : capPull W o=p := paste_cap o t p
    refine ⟨W,W,fun i => ?_,fun j => ?_⟩
    · rw [hm]
      obtain ⟨_,_,pat⟩ := CommonCore.realize_choice o lines off chosen yes i
      exact Rigidity.optimal_of_direction pat
    · rw [hc]; exact (cap j).2

end Mobius.ThreeFaceAttachment
