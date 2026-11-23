import Mobius.TwoPhases

/-! Two distinct directions can always occur together in an affine copy of
the 15-square tagged parity certificate. Opposite anchors describe the same
directed square, even when the row and column phase tables are independent. -/
namespace Mobius.Rigidity
open Mobius.SignObstruction (B Cell Rectangle alphabet translate)

structure Frame where
  a : B
  b : B
  c : B
  d : B
  deriving DecidableEq, Repr, Inhabited

def frame (mask : Nat) : Frame :=
  ⟨BitVec.ofNat 4 mask, BitVec.ofNat 4 (mask / 16),
    BitVec.ofNat 4 (mask / 256), BitVec.ofNat 4 (mask / 4096)⟩

def coeff (b : Bool) (x : B) : B := if b then x else 0

def Frame.eval (F : Frame) (x : B) : B :=
  coeff (x.getLsbD 0) F.a ^^^ coeff (x.getLsbD 1) F.b ^^^
    coeff (x.getLsbD 2) F.c ^^^ coeff (x.getLsbD 3) F.d

private theorem coeff_xor (b c : Bool) (x : B) :
    coeff (b ^^ c) x = coeff b x ^^^ coeff c x := by cases b <;> cases c <;> simp [coeff]

theorem Frame.eval_xor (F : Frame) (x y : B) : F.eval (x ^^^ y) = F.eval x ^^^ F.eval y := by
  simp only [Frame.eval, BitVec.getLsbD_xor, coeff_xor]
  ac_rfl

/-- A linear change of coordinates together with its concrete inverse. -/
structure Chart where
  act : B → B
  inv : B → B
  linear : ∀ x y, act (x ^^^ y) = act x ^^^ act y
  left : ∀ x, inv (act x) = x
  right : ∀ x, act (inv x) = x

theorem Chart.zero (g : Chart) : g.act 0 = 0 := by simpa using g.linear 0 0

theorem Chart.inj (g : Chart) {u v : B} (h : g.act u = g.act v) : u = v := by
  simpa only [g.left] using congrArg g.inv h

def Chart.comp (g h : Chart) : Chart where
  act x := g.act (h.act x)
  inv x := h.inv (g.inv x)
  linear x y := by rw [h.linear, g.linear]
  left x := by rw [g.left, h.left]
  right x := by rw [h.right, g.right]

def mapRect (f : B → B) (r : Rectangle) : Rectangle := (f r.1, f r.2.1, f r.2.2)

def flip (r : Rectangle) (swap : Bool) : Rectangle :=
  if swap then (r.1 ^^^ r.2.2, r.2.1 ^^^ r.2.2, r.2.2) else r

theorem score_flip (row col : B → B → Bool) (r : Rectangle) (swap : Bool) :
    Mobius.TwoPhases.score row col (flip r swap) = Mobius.TwoPhases.score row col r := by
  obtain ⟨x,y,d⟩ := r
  cases swap <;> simp [flip, Mobius.TwoPhases.score, Mobius.TwoPhases.corners,
    Mobius.SignObstruction.total, BitVec.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem map_flip (g : Chart) (r : Rectangle) (swap : Bool) :
    mapRect g.act (flip r swap) = flip (mapRect g.act r) swap := by
  obtain ⟨x,y,d⟩ := r
  cases swap <;> simp [flip, mapRect, g.linear]

theorem flip_translate (s : Cell) (r : Rectangle) (swap : Bool) :
    translate s (flip r swap) = flip (translate s r) swap := by
  obtain ⟨x,y,d⟩ := r
  cases swap <;> simp [translate, flip, BitVec.xor_assoc]

private theorem finite_all {P : B → Prop} [DecidablePred P] (h : alphabet.all (fun x => decide (P x)) = true) :
    ∀ x, P x := by
  intro x
  have hx : x ∈ alphabet := by revert x; decide
  exact of_decide_eq_true (List.all_eq_true.mp h x hx)

def inverseTest (f h : Frame) := alphabet.all (fun x => h.eval (f.eval x) == x && f.eval (h.eval x) == x)

def chart (f h : Frame) (cert : inverseTest f h = true) : Chart where
  act := f.eval
  inv := h.eval
  linear := f.eval_xor
  left x := by
    have hx : x ∈ alphabet := by revert x; decide
    exact eq_of_beq (Bool.and_eq_true_iff.mp (List.all_eq_true.mp cert x hx)).1
  right x := by
    have hx : x ∈ alphabet := by revert x; decide
    exact eq_of_beq (Bool.and_eq_true_iff.mp (List.all_eq_true.mp cert x hx)).2

end Mobius.Rigidity
