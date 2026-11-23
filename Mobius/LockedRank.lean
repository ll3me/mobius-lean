import Mobius.LockedGap

/-! The kernel of the switched matching in one physical XOR block. Integer
vectors suffice to test rational nonsingularity of an integer matrix. -/
namespace Mobius.LockedRank
open Mobius.SignObstruction (B alphabet)
open Mobius.LockedGap (mass matchCut sumN one)

def zsum (xs : List α) (f : α → Int) := (xs.map f).sum
def sg (p : Bool) : Int := if p then -1 else 1

private theorem add (xs : List α) (f g : α → Int) :
    zsum xs (fun x => f x + g x) = zsum xs f + zsum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [zsum,List.map_cons,List.sum_cons] at *; omega

private theorem mult (xs : List α) (k : Int) (f : α → Int) :
    zsum xs (fun x => k*f x) = k*zsum xs f := by
  induction xs with
  | nil => simp [zsum]
  | cons x xs ih => simp only [zsum,List.map_cons,List.sum_cons] at *; rw [ih,Int.mul_add]

private theorem cong (xs : List α) {f g : α → Int} (he : ∀ x, f x=g x) :
    zsum xs f = zsum xs g := congrArg List.sum (List.map_congr_left fun x _ => he x)

private theorem shift (f : B → Int) (h : B) :
    zsum alphabet (fun x => f (x ^^^ h)) = zsum alphabet f := by
  have perm : (alphabet.map (fun x => x ^^^ h)).Perm alphabet := by revert h; decide
  have keep {a b : List Int} (p : a.Perm b) : a.sum=b.sum := by
    induction p with
    | nil => rfl
    | cons _ _ ih => simp only [List.sum_cons]; omega
    | swap => simp only [List.sum_cons]; omega
    | trans _ _ ih jh => exact ih.trans jh
  have k := keep (perm.map f)
  simpa [zsum, List.map_map, Function.comp_def] using k

private theorem signsum (xs : List α) (p : α → Bool) :
    zsum xs (fun x => sg (p x)) = (xs.length : Int)-2*(sumN xs fun x => one (p x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sg (p x) + zsum xs _ = ((xs.length+1 : Nat) : Int) -
      2*((one (p x) + sumN xs (fun x => one (p x)) : Nat) : Int)
    rw [ih]
    cases p x <;> simp [sg,one] <;> omega

private theorem commute (p q : Bool) : sg p * sg q = sg (p ^^ q) := by cases p <;> cases q <;> decide
private theorem sq (p : Bool) : sg p * sg p = 1 := by cases p <;> decide

/-- The doubled, unsigned adjacency matrix acting on z; its entries are
twice those of the matching toggled across the cut p. -/
def kernelEq (p : B → Bool) (h : B) (z : B → Int) : Prop :=
  ∀ x, 2*sg (p x)*sg (p (x ^^^ h))*z (x ^^^ h) +
    zsum alphabet z - sg (p x)*zsum alphabet (fun v => sg (p v)*z v) = 0

theorem adjacency_entry (p : B → Bool) (h x v : B) :
    2 * (one (Mobius.LockedGap.matched h x v ^^ Mobius.LockedGap.crossed p x v) : Int) =
    2 * sg (p x) * sg (p v) * (one (Mobius.LockedGap.matched h x v) : Int) +
      1 - sg (p x) * sg (p v) := by
  unfold Mobius.LockedGap.crossed
  cases p x <;> cases p v <;> cases Mobius.LockedGap.matched h x v <;> decide

private theorem classify (k m : Fin 17) (P Q : Int) (k1 : k.val ≠ 1) (k15 : k.val ≠ 15)
    (a : (18-4*(m.val:Int))*P = (16-2*(k.val:Int))*Q)
    (b : (16-2*(k.val:Int))*P = 14*Q) : P=0 ∧ Q=0 := by
  have nums : ∀ i j : Fin 17, i.val ≠ 1 → i.val ≠ 15 →
      14*(18-4*(j.val:Int)) - (16-2*(i.val:Int))*(16-2*(i.val:Int)) ≠ 0 := by decide
  have ha := congrArg (fun w : Int => 14*w) a
  have hb := congrArg (fun w : Int => (16-2*(k.val:Int))*w) b
  have he : (14*(18-4*(m.val:Int)) - (16-2*(k.val:Int))*(16-2*(k.val:Int)))*P=0 := by
    grind only
  have hp := (Int.mul_eq_zero.mp he).resolve_left (nums k m k1 k15)
  exact ⟨hp,by rw [hp] at b; omega⟩

theorem nonsingular_away_from_singleton (p : B → Bool) (h : B) (z : B → Int)
    (ker : kernelEq p h z) (k1 : mass p ≠ 1) (k15 : mass p ≠ 15) :
    ∀ x, z x=0 := by
  let P := zsum alphabet z
  let Q := zsum alphabet (fun x => sg (p x)*z x)
  let s := fun x => sg (p x)
  let v := fun x => s x * s (x ^^^ h)
  have sum_s : zsum alphabet s = 16-2*(mass p : Int) := signsum _ _
  have sum_v : zsum alphabet v = 16-2*(matchCut p h : Int) := by
    rw [cong alphabet (fun x => commute (p x) (p (x ^^^ h)))]
    exact signsum _ _
  have line (x : B) : 2*z x = (-P)*v x + Q*s x := by
    have hx := ker (x ^^^ h)
    simp only [BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero] at hx
    change 2*s (x ^^^ h)*s x*z x + P-s (x ^^^ h)*Q=0 at hx
    have hprod := congrArg (fun w : Int => s x*s (x ^^^ h)*w) hx
    have hs := sq (p x); have ht := sq (p (x ^^^ h))
    change s x*s x = 1 at hs; change s (x ^^^ h)*s (x ^^^ h)=1 at ht
    dsimp only [v]; grind only
  have sum1 := cong alphabet line
  rw [mult,add,mult,mult,sum_v,sum_s] at sum1
  have a : (18-2*(matchCut p h : Int))*P = (16-2*(mass p : Int))*Q := by
    change 2*P = _ at sum1
    grind only
  have weighted (x : B) : 2*(s x*z x) = (-P)*s (x ^^^ h) + Q*1 := by
    have eq' := congrArg (fun w : Int => s x*w) (line x)
    have hs := sq (p x); change s x*s x=1 at hs
    dsimp only [v] at eq'; grind only
  have sum2 := cong alphabet weighted
  rw [mult,add,mult,mult,shift,sum_s] at sum2
  have b : (16-2*(mass p : Int))*P = 14*Q := by
    change 2*Q = -P*(16-2*(mass p : Int))+Q*16 at sum2
    grind only
  have mt : matchCut p h ≤ 16 := by
    calc
      _ ≤ sumN alphabet (fun _ => 1) := Mobius.LockedGap.sum_le _ _ _ fun x _ => by
        cases Mobius.LockedGap.crossed p x (x ^^^ h) <;> decide
      _ = _ := Mobius.LockedGap.total_ones
  have even : matchCut p h % 2 = 0 := by
    -- A cut meets an involutive matching twice per separated pair.
    have plus := Mobius.LockedGap.sum_flip (fun x => one ((p x) && !(p (x ^^^ h)))) h
    have split : matchCut p h =
        sumN alphabet (fun x => one ((p x) && !(p (x ^^^ h)))) +
        sumN alphabet (fun x => one ((p (x ^^^ h)) && !(p x))) := by
      rw [← Mobius.LockedGap.sum_add]
      apply Mobius.LockedGap.sum_congr; intro x _
      simp only [Mobius.LockedGap.crossed]; cases p x <;> cases p (x ^^^ h) <;> rfl
    simp only [BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero] at plus
    omega
  have kt := Mobius.LockedGap.mass_complement p
  let k : Fin 17 := ⟨mass p,by omega⟩
  let m : Fin 17 := ⟨matchCut p h / 2,by omega⟩
  have step : (matchCut p h : Int) = 2*(m.val:Int) := by dsimp [m]; omega
  rw [step] at a
  have ac : (18-4*(m.val:Int))*P=(16-2*(k.val:Int))*Q := by
    change (18-4*(m.val:Int))*P=(16-2*(mass p:Int))*Q; grind only
  obtain ⟨hp,hq⟩ := classify k m P Q k1 k15 ac b
  intro x; have eq := line x; rw [hp,hq] at eq; omega

end Mobius.LockedRank
