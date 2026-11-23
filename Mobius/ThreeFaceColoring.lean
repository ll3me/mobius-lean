import Mobius.CommonCore
import Mobius.RigidityKernel

/-! A graph encoded by projective lines in an actual binary quotient.
The two nonzero bits at a vertex are its three possible colors. Three
projective lines impose pure parity on each edge-coordinate difference. -/
namespace Mobius.ThreeFaceColoring
open Mobius.Rigidity.Kernel (dot dot_xor)

abbrev Graph (n m : Nat) := Fin m → Fin n × Fin n
def Simple (g : Graph n m) := ∀ e, (g e).1≠(g e).2
abbrev Color := Bool × Bool
def Colorable (g : Graph n m) := ∃ z : Fin n → Color, (∀ i, z i≠(false,false)) ∧
  ∀ e, z (g e).1 ≠ z (g e).2

abbrev triangle (a b c : Bool) : Prop := a.toNat+b.toNat+c.toNat=2
private theorem tri_iff (a b c : Bool) : triangle a b c ↔ c=(a ^^ b) ∧ (a,b)≠(false,false) := by
  cases a <;> cases b <;> cases c <;> decide

def helper (a b : Bool) := !(a && !b)

theorem xor_bridge (a b c : Bool) :
    (∃ t p q, triangle a t p ∧ triangle b p q ∧ triangle c t q) ↔ c=(a ^^ b) := by
  revert a b c; decide

private theorem bridge_witness (a b : Bool) :
    let t := helper a b
    triangle a t (a ^^ t) ∧ triangle b (a ^^ t) ((a ^^ b) ^^ t) ∧
      triangle (a ^^ b) t ((a ^^ b) ^^ t) := by
  cases a <;> cases b <;> decide

def pick (p : Color) (i : Bool) := if i then p.2 else p.1
def atom (i : Fin n) (b : Bool) := 2^(2*i.val+b.toNat)
def aux (n : Nat) (e : Fin m) (b : Bool) := 2^(2*n+2*e.val+b.toNat)

inductive Kind (n m : Nat) where
  | vertex (i : Fin n)
  | link (e : Fin m) (b : Bool) (j : Fin 3)
  | edge (e : Fin m)

def triPoints (p q : Nat) (i : Fin 3) : Nat := if i=0 then p else if i=1 then q else p^^^q

def endpoints (g : Graph n m) : Kind n m → Nat × Nat
  | .vertex v => (atom v false,atom v true)
  | .edge e => (atom (g e).1 false^^^atom (g e).2 false,atom (g e).1 true^^^atom (g e).2 true)
  | .link e b j =>
    let a := atom (g e).1 b
    let d := atom (g e).2 b
    let t := aux n e b
    if j=0 then (a,t) else if j=1 then (d,a^^^t) else (a^^^d,t)

def lines (g : Graph n m) (k : Kind n m) := triPoints (endpoints g k).1 (endpoints g k).2

private theorem one_triangle (a b c : Bool) :
    (∃ j : Fin 3, ∀ i : Fin 3, (if i=0 then !a else if i=1 then !b else !c)=decide (i=j))
      ↔ triangle a b c := by revert a b c; decide

def Good (g : Graph n m) (s : Nat → Bool) := ∀ k, let p := endpoints g k
  triangle (s p.1) (s p.2) (s (p.1^^^p.2))

theorem one_iff (g : Graph n m) (s : Nat → Bool) :
    CommonCore.OneOn (lines g) (fun p => !(s p)) ↔ Good g s := by
  have localEq (k : Kind n m) :
      (∃ j : Fin 3, ∀ i, (!(s (lines g k i)))=decide (i=j)) ↔
      triangle (s (endpoints g k).1) (s (endpoints g k).2)
        (s ((endpoints g k).1^^^(endpoints g k).2)) := by
    apply Iff.trans _ (one_triangle ..)
    have h (i : Fin 3) : (!(s (lines g k i))) =
      (if i=0 then !(s (endpoints g k).1) else if i=1 then !(s (endpoints g k).2)
       else !(s ((endpoints g k).1^^^(endpoints g k).2))) := by
      by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> simp [lines,triPoints,h0,h1]
    simp only [h]
  exact ⟨fun h k => (localEq k).mp (h k),fun h k => (localEq k).mpr (h k)⟩

private theorem diff_read (g : Graph n m) (s : Nat → Bool) (ok : Good g s) (e : Fin m) (b : Bool) :
    s (atom (g e).1 b^^^atom (g e).2 b)=(s (atom (g e).1 b) ^^ s (atom (g e).2 b)) := by
  let a := atom (g e).1 b
  let d := atom (g e).2 b
  let t := aux n e b
  apply (xor_bridge ..).mp
  refine ⟨s t,s (a^^^t),s ((a^^^d)^^^t),ok (.link e b 0),?_,ok (.link e b 2)⟩
  have h := ok (.link e b 1)
  change triangle (s d) (s (a^^^t)) (s (d^^^(a^^^t))) at h
  change triangle (s d) (s (a^^^t)) (s ((a^^^d)^^^t))
  rwa [←Nat.xor_assoc,Nat.xor_comm d a] at h

theorem extract (g : Graph n m) (s : Nat → Bool) (ok : Good g s) : Colorable g := by
  refine ⟨fun i => (s (atom i false),s (atom i true)),fun i => (tri_iff ..).mp (ok (.vertex i)) |>.2,?_⟩
  intro e eq
  have bad := ((tri_iff ..).mp (ok (.edge e))).2
  change (s (atom (g e).1 false^^^atom (g e).2 false),
    s (atom (g e).1 true^^^atom (g e).2 true))≠(false,false) at bad
  rw [diff_read g s ok e false,diff_read g s ok e true] at bad
  have left := congrArg Prod.fst eq
  have right := congrArg Prod.snd eq
  change s (atom (g e).1 false)=s (atom (g e).2 false) at left
  change s (atom (g e).1 true)=s (atom (g e).2 true) at right
  simp [left,right] at bad

private theorem dot_atom (w : Nat → Bool) (k j : Nat) :
    dot w k (2^j) = if j<k then w j else false := by
  induction k with
  | zero => simp [dot]
  | succ k ih =>
    rw [dot,ih,Nat.testBit_two_pow]
    by_cases eq : j=k
    · subst j; simp
    · by_cases lt : j<k <;> simp [eq,lt,show (j<k+1)=(j<k) by apply propext; omega]

def values (g : Graph n m) (z : Fin n → Color) (i : Nat) : Bool :=
  if h : i/2<n then pick (z ⟨i/2,h⟩) (decide (i%2=1)) else
  if h : (i/2-n)<m then
    let e : Fin m := ⟨i/2-n,h⟩
    let b := decide (i%2=1)
    helper (pick (z (g e).1) b) (pick (z (g e).2) b)
  else false

private theorem val_atom (g : Graph n m) (z : Fin n → Color) (i : Fin n) (b : Bool) :
    dot (values g z) (2*n+2*m) (atom i b)=pick (z i) b := by
  have hi := i.isLt
  let k := 2*i.val+b.toNat
  have small : k<2*n+2*m := by cases b <;> unfold k <;> simp <;> omega
  have idx : k/2=i.val := by cases b <;> unfold k <;> simp <;> omega
  have which : decide (k%2=1)=b := by cases b <;> simp [k] <;> omega
  change dot _ _ (2^k)=_
  rw [dot_atom,ite_eq_left small]
  simp [values,idx,which,hi]

private theorem val_aux (g : Graph n m) (z : Fin n → Color) (e : Fin m) (b : Bool) :
    dot (values g z) (2*n+2*m) (aux n e b)=helper (pick (z (g e).1) b) (pick (z (g e).2) b) := by
  have he := e.isLt
  let k := 2*n+2*e.val+b.toNat
  have small : k<2*n+2*m := by cases b <;> unfold k <;> simp <;> omega
  have idx : k/2=n+e.val := by cases b <;> unfold k <;> simp <;> omega
  have which : decide (k%2=1)=b := by cases b <;> simp [k] <;> omega
  change dot _ _ (2^k)=_
  rw [dot_atom,ite_eq_left small]
  simp [values,idx,which,he,show ¬n+e.val<n by omega]

private theorem color_diff (a b : Color) (hne : a≠b) : (a.1 ^^ b.1,a.2 ^^ b.2)≠(false,false) := by
  rcases a with ⟨a₀,a₁⟩; rcases b with ⟨b₀,b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> simp_all

theorem build (g : Graph n m) (col : Colorable g) : ∃ s, Good g s := by
  obtain ⟨z,nonzero,differ⟩ := col
  let s := dot (values g z) (2*n+2*m)
  refine ⟨s,?_⟩
  intro k
  cases k with
  | vertex i =>
    change triangle _ _ (s (atom i false^^^atom i true))
    simp only [endpoints,s,dot_xor,val_atom]
    exact (tri_iff ..).mpr ⟨rfl,nonzero i⟩
  | edge e =>
    change triangle _ _ (s ((atom (g e).1 false^^^atom (g e).2 false)^^^(atom (g e).1 true^^^atom (g e).2 true)))
    simp only [endpoints,s,dot_xor,val_atom]
    exact (tri_iff ..).mpr ⟨rfl,color_diff _ _ (differ e)⟩
  | link e b j =>
    have h := bridge_witness (pick (z (g e).1) b) (pick (z (g e).2) b)
    have opts : ∀ u : Fin 3, u=0 ∨ u=1 ∨ u=2 := by decide
    rcases opts j with rfl|rfl|rfl
    · simpa [endpoints,s,dot_xor,val_atom,val_aux] using h.1
    · simpa [endpoints,s,dot_xor,val_atom,val_aux,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
        using h.2.1
    · simpa [endpoints,s,dot_xor,val_atom,val_aux] using h.2.2

theorem choices_iff (g : Graph n m) : (∃ c, CommonCore.OneOn (lines g) c) ↔ Colorable g := by
  constructor
  · rintro ⟨c,ok⟩
    exact extract g (fun p => !(c p)) ((one_iff ..).mp (by simpa using ok))
  · intro col
    obtain ⟨s,ok⟩ := build g col
    exact ⟨_,(one_iff ..).mpr ok⟩

end Mobius.ThreeFaceColoring
