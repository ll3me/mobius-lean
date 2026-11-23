import Mobius.RigidityGeometry

/-! Double-counting anchored defects. Every template with exactly one square
per nonzero direction gives the same count when both anchors are translated. -/
namespace Mobius.Rigidity
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Mobius.SignObstruction (B Cell Rectangle translate directions shifts)

private def sumOver (xs : List α) (f : α → Nat) := (xs.map f).sum

private theorem sum_congr {xs : List α} {f g : α → Nat} (h : ∀ a ∈ xs, f a = g a) :
    sumOver xs f = sumOver xs g := congrArg List.sum (List.map_congr_left h)

private theorem sum_add (xs : List α) (f g : α → Nat) :
    sumOver xs (fun x => f x + g x) = sumOver xs f + sumOver xs g := by
  induction xs with
  | nil => simp [sumOver]
  | cons x xs ih => simp only [sumOver,List.map_cons,List.sum_cons] at ih ⊢; omega

private theorem sum_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumOver xs (fun x => sumOver ys (f x)) = sumOver ys (fun y => sumOver xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = (ys.map (fun _ => (0 : Nat))).sum
    induction ys with
    | nil => rfl
    | cons y ys ih => calc
        0 = (ys.map (fun _ => (0 : Nat))).sum := ih
        _ = _ := by simp only [List.map_cons, List.sum_cons, Nat.zero_add]
  | cons x xs ih =>
    change sumOver ys (f x) + sumOver xs _ = sumOver ys (fun y => f x y + sumOver xs (fun z => f z y))
    rw [sum_add, ih]

def oneIf (b : Bool) : Nat := if b then 1 else 0

private theorem length_filter (xs : List α) (f : α → Bool) :
    (xs.filter f).length = sumOver xs (fun x => oneIf (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [sumOver,oneIf,h,ih,Nat.add_comm]

private def shiftBy (t s : Cell) : Cell := (s.1 ^^^ t.1,s.2 ^^^ t.2)
private theorem shift_invol (t s : Cell) : shiftBy t (shiftBy t s) = s := by
  obtain ⟨u,v⟩ := s; simp [shiftBy, BitVec.xor_assoc]

private theorem shifted_perm (t : Cell) : (shifts.map (shiftBy t)).Perm shifts := by
  have nodup := Mobius.SignObstruction.shifts_nodup
  apply (List.perm_ext_iff_of_nodup (nodup.map _ (fun a b h e => h (by
    simpa only [shift_invol] using congrArg (shiftBy t) e))) nodup).2
  intro s
  exact ⟨fun _ => Mobius.SignObstruction.shifts_complete s, fun _ => List.mem_map.mpr
    ⟨shiftBy t s,Mobius.SignObstruction.shifts_complete _,shift_invol _ _⟩⟩

def dir (r : Rectangle) : B := r.2.2

def IsTemplate (rs : List Rectangle) : Prop := (rs.map dir).Perm directions

def hits (bad : Rectangle → Bool) (rs : List Rectangle) (s : Cell) :=
  (rs.filter fun r => bad (translate s r)).length

def totalDefects (bad : Rectangle → Bool) : Nat :=
  sumOver directions fun d => sumOver shifts fun s => oneIf (bad (s.1,s.2,d))

theorem total_of_template (bad : Rectangle → Bool) (rs : List Rectangle) (good : IsTemplate rs) :
    (shifts.map (hits bad rs)).sum = totalDefects bad := by
  change sumOver shifts (hits bad rs) = _
  let column := fun d : B => sumOver shifts fun s => oneIf (bad (s.1,s.2,d))
  calc
    _ = sumOver shifts (fun s => sumOver rs fun r => oneIf (bad (translate s r))) :=
      sum_congr fun s _ => length_filter rs _
    _ = sumOver rs (fun r => sumOver shifts fun s => oneIf (bad (translate s r))) := sum_swap _ _ _
    _ = sumOver rs (fun r => column (dir r)) := by
      apply sum_congr
      intro r _
      let f := fun s : Cell => oneIf (bad (s.1,s.2,dir r))
      have k := ((shifted_perm (r.1,r.2.1)).map f).sum_nat
      simpa only [List.map_map, Function.comp_def, shiftBy, sumOver, column, f, translate, dir] using k
    _ = totalDefects bad := by
      have k := (good.map column).sum_nat
      simpa only [List.map_map, Function.comp_def, sumOver, totalDefects, column] using k

def twoBad (row col : B → B → Bool) (r : Rectangle) := !Mobius.TwoPhases.score row col r

def oneBad (phase : B → B → Bool) (r : Rectangle) :=
  !(Mobius.SignObstruction.total (fun z : Cell => phase z.1 z.2) (Mobius.SignObstruction.corners r))

theorem two_count (row col : B → B → Bool) :
    Mobius.TwoPhases.failures row col = totalDefects (twoBad row col) :=
by
  have good : (Mobius.TwoPhases.certificate.map dir).Perm directions := by decide
  calc
    _ = (shifts.map (hits (twoBad row col) Mobius.TwoPhases.certificate)).sum := by
      unfold Mobius.TwoPhases.failures
      apply congrArg List.sum
      apply List.map_congr_left
      intro s _
      rfl
    _ = _ := total_of_template (twoBad row col) Mobius.TwoPhases.certificate good

theorem one_count (p : B → B → Bool) : Mobius.SignObstruction.failures p = totalDefects (oneBad p) :=
by
  have good : (Mobius.SignObstruction.certificate.map dir).Perm directions := by decide
  calc
    _ = (shifts.map (hits (oneBad p) Mobius.SignObstruction.certificate)).sum := by
      unfold Mobius.SignObstruction.failures
      apply congrArg List.sum
      apply List.map_congr_left
      intro s _
      rfl
    _ = _ := total_of_template (oneBad p) Mobius.SignObstruction.certificate good

theorem twoBad_same (p : B → B → Bool) : twoBad p p = oneBad p := by
  funext r
  obtain ⟨x,y,d⟩ := r
  simp [twoBad,oneBad,Mobius.TwoPhases.score,Mobius.TwoPhases.corners,
    Mobius.SignObstruction.corners,Mobius.SignObstruction.total,Bool.xor_comm,Bool.xor_left_comm]

theorem same_count (p : B → B → Bool) : Mobius.TwoPhases.failures p p = Mobius.SignObstruction.failures p := by
  rw [two_count,one_count,twoBad_same]

end Mobius.Rigidity
