import Mobius.RigidityEnumeration

/-! Three rectangular row parities read the low bits of the unique bad
direction of every optimal four-dimensional board. Any cycle of actual
station restrictions therefore has zero total tangential direction. -/
namespace Mobius.ParallelSignature
open Mobius.SignObstruction (B)
open Mobius.Rigidity (DirectionPattern)
open Mobius.Rigidity.Enumeration (Phase Pair Direction ground plus ZeroPair)
open Mobius.Rigidity.Kernel (key double dot dot_xor)

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

/-- The three low-coordinate rectangles use (a,b) = (2,4),(1,4),(1,2). -/
def a (j : Fin 3) : B := if j.val=0 then 2 else 1
def b (j : Fin 3) : B := if j.val=2 then 2 else 4

def cornerParity (r : Phase) (t : B) (j : Fin 3) : Bool :=
  r t t ^^ r (t ^^^ a j) t ^^ r t (t ^^^ b j) ^^ r (t ^^^ a j) (t ^^^ b j)

private def mask (t : B) (j : Fin 3) : Nat :=
  let m := fun x y => double.coefficient (key false x y)
  m t t ^^^ m (t ^^^ a j) t ^^^ m t (t ^^^ b j) ^^^ m (t ^^^ a j) (t ^^^ b j)

private theorem equal_masks : ∀ j : Fin 3, mask 0 j = mask 8 j := by decide +kernel

private theorem equal_kernel_readings (p : ZeroPair true) (j : Fin 3) :
    cornerParity p.val.1 0 j = cornerParity p.val.1 8 j := by
  let v := Rigidity.Enumeration.lookup p.val
  let bits := double.read v
  have good : Rigidity.Kernel.Good true v := by
    intro x y d hd
    rw [Rigidity.Enumeration.eval_lookup true p.val p.property.1]
    exact p.property.2 _ _ _ hd
  have row (x y : B) : p.val.1 x y = double.generate bits (key false x y) := by
    have bd : ∀ x y : B, key false x y < 512 := by decide
    exact ((Rigidity.Kernel.generate_read double Rigidity.Kernel.double_valid v good _ (bd x y)).trans
      (Rigidity.Enumeration.lookup_key p.val false x y)).symm
  have packed (t : B) : cornerParity p.val.1 t j = dot bits.getLsbD double.k (mask t j) := by
    simp only [cornerParity, mask, row, Rigidity.Kernel.Model.generate, dot_xor]
  rw [packed,packed,equal_masks]

private theorem ground_signature : ∀ (d : Direction) (j : Fin 3),
    (cornerParity (ground d).1 0 j ^^ cornerParity (ground d).1 8 j) =
      d.val.getLsbD j.val := by
  let raw (d : B) : Phase := fun x y =>
    EightSquare.phase (SignObstruction.quotient d x) (SignObstruction.quotient d y)
  have checked : ∀ (d : B) (j : Fin 3), d≠0 →
      (cornerParity (raw d) 0 j ^^ cornerParity (raw d) 8 j) = d.getLsbD j.val := by
    decide +kernel
  exact fun d j => checked d.val j d.property

private theorem corner_plus (p q : Pair) (t : B) (j : Fin 3) :
    cornerParity (plus p q).1 t j = (cornerParity p.1 t j ^^ cornerParity q.1 t j) := by
  simp [cornerParity,plus,Bool.xor_comm,Bool.xor_left_comm]

/-- Applies to both tangential and transverse exceptional directions. -/
theorem board_signature {r c : Phase} {d : B} (profile : DirectionPattern r c d)
    (j : Fin 3) : (cornerParity r 0 j ^^ cornerParity r 8 j) = d.getLsbD j.val := by
  let label : Direction := ⟨d,profile.1⟩
  let p : Pair := (r,c)
  let z : ZeroPair true := ⟨plus p (ground label), fun ht => by contradiction, by
    intro x y e he
    rw [Rigidity.Enumeration.score_plus,profile.2 _ _ _ he,
      (Rigidity.Enumeration.ground_pattern label).2 _ _ _ he]
    simp [label]⟩
  have eqn := equal_kernel_readings z j
  change cornerParity (plus p (ground label)).1 0 j = cornerParity (plus p (ground label)).1 8 j at eqn
  rw [corner_plus,corner_plus] at eqn
  have cancel (u v s t : Bool) (h : (u ^^ s) = (v ^^ t)) : (u ^^ v) = (s ^^ t) := by
    revert h; cases u <;> cases v <;> cases s <;> cases t <;> decide
  exact (cancel _ _ _ _ eqn).trans (ground_signature label j)

abbrev Station (α : Type) := BitVec 3 → α

def chart (stations : Nat → Station α) (i : Nat) (x : B) : α :=
  if x.getLsbD 3 then stations (i+1) (x.setWidth 3) else stations i (x.setWidth 3)

def localPhase (world : α → α → Bool) (stations : Nat → Station α) (i : Nat) : Phase :=
  fun x y => world (chart stations i x) (chart stations i y)

def stationBit (world : α → α → Bool) (st : Station α) (j : Fin 3) : Bool :=
  let p := fun (x y : BitVec 3) => world (st x) (st y)
  p 0 0 ^^ p ((a j).setWidth 3) 0 ^^ p 0 ((b j).setWidth 3) ^^
    p ((a j).setWidth 3) ((b j).setWidth 3)

private theorem local_readings (world : α → α → Bool) (st : Nat → Station α)
    (i : Nat) (j : Fin 3) :
    cornerParity (localPhase world st i) 0 j = stationBit world (st i) j ∧
    cornerParity (localPhase world st i) 8 j = stationBit world (st (i+1)) j := by
  have cases3 (j : Fin 3) : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases cases3 j with rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

def parity (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n+1 => parity f n ^^ f n

/-- The whole row and column tables live on one common address space.
Stations may be embedded in any ambient geometry. No periodicity of
unvisited pages or private cells is required. -/
theorem cycle_xor (row col : α → α → Bool) (st : Nat → Station α) (ds : Nat → B)
    (n : Nat) (closed : st n = st 0)
    (profiles : ∀ i, i<n → DirectionPattern (localPhase row st i) (localPhase col st i) (ds i))
    (j : Fin 3) : parity (fun i => (ds i).getLsbD j.val) n = false := by
  have step (i : Nat) (hi : i<n) :
      (ds i).getLsbD j.val = (stationBit row (st i) j ^^ stationBit row (st (i+1)) j) := by
    rw [←board_signature (profiles i hi) j,(local_readings row st i j).1,(local_readings row st i j).2]
  have telescope (k : Nat) (hk : k≤n) : parity (fun i => (ds i).getLsbD j.val) k =
      (stationBit row (st 0) j ^^ stationBit row (st k) j) := by
    induction k with
    | zero => simp [parity]
    | succ k ih => rw [parity,ih (by omega),step k (by omega)]; simp
  simpa [closed] using telescope n (Nat.le_refl n)

end Mobius.ParallelSignature
