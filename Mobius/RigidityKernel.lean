import Mobius.Rigidity

/-! A decoder for a homogeneous binary four-term equation system. Each
instruction recovers one cell from the three other entries in a tested square.
The generator gives every cell as a parity of independent information bits. -/
namespace Mobius.Rigidity.Kernel
open Mobius.SignObstruction (B)

def key (tag : Bool) (x y : B) := (if tag then 256 else 0) + 16*x.toNat + y.toNat

structure Quad where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving Inhabited

def square (two : Bool) (x y d : B) : Quad :=
  ⟨key false x y, key false (x ^^^ d) (y ^^^ d), key two x (y ^^^ d), key two (x ^^^ d) y⟩

def Quad.val (q : Quad) (v : Nat → Bool) := v q.a ^^ v q.b ^^ v q.c ^^ v q.d

def Quad.mask (q : Quad) (v : Nat → Nat) := v q.a ^^^ v q.b ^^^ v q.c ^^^ v q.d

def Quad.turn (q : Quad) (k : Nat) : Quad := match k with
  | 0 => q
  | 1 => ⟨q.b,q.c,q.d,q.a⟩
  | 2 => ⟨q.c,q.d,q.a,q.b⟩
  | _ => ⟨q.d,q.a,q.b,q.c⟩

theorem Quad.turn_val (q : Quad) (v : Nat → Bool) (k : Nat) : (q.turn k).val v = q.val v := by
  cases k with
  | zero => rfl
  | succ k => cases k with
    | zero => simp [Quad.turn, Quad.val,Bool.xor_comm,Bool.xor_left_comm]
    | succ k => cases k <;> simp [Quad.turn, Quad.val,Bool.xor_comm,Bool.xor_left_comm]

def Good (two : Bool) (v : Nat → Bool) := ∀ x y d : B, d ≠ 0 → (square two x y d).val v = false

structure Step where
  x : B
  y : B
  d : B
  turn : Nat
  deriving Inhabited

def mark (s i : Nat) := s ||| 2^i

def Step.run (two : Bool) (s : Nat) (p : Step) : Nat :=
  let q := (square two p.x p.y p.d).turn p.turn
  if p.d != 0 && s.testBit q.b && s.testBit q.c && s.testBit q.d then mark s q.a else s

private theorem quad_recover (a b c d a' b' c' d' : Bool)
    (h : (a ^^ b ^^ c ^^ d) = false) (h' : (a' ^^ b' ^^ c' ^^ d') = false)
    (hb : b=b') (hc : c=c') (hd : d=d') : a=a' := by
  subst b'; subst c'; subst d'; cases a <;> cases a' <;> cases b <;> cases c <;> cases d <;> simp_all

def Agree (s : Nat) (v w : Nat → Bool) : Prop := ∀ i, s.testBit i = true → v i = w i

private theorem agree_mark {s i : Nat} {v w : Nat → Bool} (old : Agree s v w) (atNew : v i = w i) :
    Agree (mark s i) v w := by
  intro j h
  simp only [mark,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true_iff,decide_eq_true_eq] at h
  rcases h with h | rfl
  · exact old j h
  · exact atNew

private theorem agree_step (two : Bool) (v w : Nat → Bool) (hv : Good two v) (hw : Good two w)
    (p : Step) (s : Nat) (old : Agree s v w) : Agree (p.run two s) v w := by
  let q := (square two p.x p.y p.d).turn p.turn
  unfold Step.run
  change Agree (if p.d != 0 && s.testBit q.b && s.testBit q.c && s.testBit q.d then _ else _) v w
  split
  · rename_i h
    simp only [Bool.and_eq_true_iff,bne_iff_ne] at h
    have hh (f : Nat → Bool) (good : Good two f) : q.val f = false :=
      ((square two p.x p.y p.d).turn_val f _).trans (good _ _ _ h.1.1.1)
    apply agree_mark old
    exact quad_recover _ _ _ _ _ _ _ _ (hh v hv) (hh w hw) (old _ h.1.1.2) (old _ h.1.2) (old _ h.2)
  · exact old

def dot (w : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => false
  | k+1,m => dot w k m ^^ (m.testBit k && w k)

theorem dot_xor (w : Nat → Bool) (k a b : Nat) :
    dot w k (a ^^^ b) = (dot w k a ^^ dot w k b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dot,Nat.testBit_xor,ih]
    cases a.testBit k <;> cases b.testBit k <;> cases w k <;>
      simp [Bool.xor_comm]

private theorem dot_zero (w : Nat → Bool) (k : Nat) : dot w k 0 = false := by induction k <;> simp_all [dot]

private theorem dot_unit (w : Nat → Bool) (k i : Nat) :
    dot w k (2^i) = if i < k then w i else false := by
  induction k with
  | zero => simp [dot]
  | succ k ih =>
    simp only [dot, Nat.testBit_two_pow, ih]
    by_cases lt : i < k
    · simp [lt, Nat.ne_of_lt lt, Nat.lt_succ_of_lt lt]
    · by_cases eqn : i = k
      · subst k; simp
      · have h : ¬i < k+1 := by omega
        simp [lt,eqn,h]

structure Model where
  two : Bool
  k : Nat
  pins : Array Nat
  coeff : Array (Array Nat)
  instructions : List Step

def Model.pin (m : Model) (i : Nat) := m.pins[i]?.getD 0
def Model.coefficient (m : Model) (i : Nat) := ((m.coeff[i / 16]?).getD #[])[i % 16]?.getD 0

def Model.finished (m : Model) := m.instructions.foldl (Step.run m.two)
  (((List.range m.k).map m.pin).foldl mark 0)

def Model.size (m : Model) := if m.two then 512 else 256

structure Valid (m : Model) : Prop where
  units : ∀ i : Fin m.k, m.coefficient (m.pin i) = 2^i.val
  rows : ∀ x y d : B, d ≠ 0 → (square m.two x y d).mask m.coefficient = 0
  complete : m.finished = 2^m.size-1

def Model.generate (m : Model) (bits : BitVec m.k) (i : Nat) :=
  dot bits.getLsbD m.k (m.coefficient i)

def Model.read (m : Model) (v : Nat → Bool) : BitVec m.k :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin m.k => v (m.pin i))).setWidth m.k

theorem read_bit (m : Model) (v : Nat → Bool) {i : Nat} (hi : i < m.k) :
    (m.read v).getLsbD i = v (m.pin i) := by
  simp only [Model.read, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, hi,
    decide_true, Bool.true_and,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem read_generate (m : Model) (valid : Valid m) (bits : BitVec m.k) :
    m.read (m.generate bits) = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [read_bit _ _ hi]
  change dot _ _ (m.coefficient (m.pin i)) = _
  rw [valid.units ⟨i,hi⟩, dot_unit]
  simp [hi]

theorem generate_good (m : Model) (valid : Valid m) (bits : BitVec m.k) : Good m.two (m.generate bits) := by
  intro x y d hd
  let q := square m.two x y d
  have h := congrArg (dot bits.getLsbD m.k) (valid.rows x y d hd)
  simpa only [Quad.mask, Quad.val, Model.generate, dot_xor, dot_zero] using h

private theorem agreement_of_pins (m : Model) (v w : Nat → Bool) (hv : Good m.two v) (hw : Good m.two w)
    (pinned : ∀ i : Fin m.k, v (m.pin i) = w (m.pin i)) : Agree m.finished v w := by
  let pins := (List.range m.k).map m.pin
  have hp (a : Nat) (ha : a ∈ pins) : v a = w a := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact pinned ⟨i,List.mem_range.mp hi⟩
  have start (xs : List Nat) (hh : ∀ a ∈ xs, v a = w a) (s : Nat) (old : Agree s v w) :
      Agree (xs.foldl mark s) v w := by
    induction xs generalizing s with
    | nil => exact old
    | cons x xs ih => exact ih (fun a h => hh a (by simp [h])) _ (agree_mark old (hh x (by simp)))
  have rest (ps : List Step) (s : Nat) (old : Agree s v w) : Agree (ps.foldl (Step.run m.two) s) v w := by
    induction ps generalizing s with
    | nil => exact old
    | cons p ps ih => exact ih _ (agree_step _ _ _ hv hw p _ old)
  apply rest _ _ (start pins hp 0 ?_)
  intro i h
  simp at h

theorem generate_read (m : Model) (valid : Valid m) (v : Nat → Bool) (hv : Good m.two v)
    (i : Nat) (hi : i < m.size) : m.generate (m.read v) i = v i := by
  have agree := agreement_of_pins m (m.generate (m.read v)) v (generate_good m valid _) hv (by
    intro j
    change dot _ _ (m.coefficient (m.pin j)) = _
    rw [valid.units j,dot_unit,ite_eq_left j.isLt,read_bit _ _ j.isLt])
  apply agree i
  rw [valid.complete,Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hi

end Mobius.Rigidity.Kernel
