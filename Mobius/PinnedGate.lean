import Mobius.MatrixMerge
import Mobius.BoardInputProjection

/-! Exact local gates of the BRS circuit compiler. The pin has one
    input-dependent literal address, in slot zero of its designated row. -/
namespace Mobius.PinnedGate
open MatrixMerge (One)

theorem constants (f t : Bool) : One f f t ↔ f=false ∧ t=true := by
  cases f <;> cases t <;> simp [MatrixMerge.One]

theorem not_gate (a na : Bool) : One a na false ↔ na=(!a) := by
  cases a <;> cases na <;> simp [MatrixMerge.One]

def AndRows (a b z l q t : Bool) : Prop :=
  One z l (!a) ∧ One z q (!b) ∧ One l q t

/-- All four computed wires, including every private slack, are forced. -/
theorem and_assignment (a b z l q t : Bool) : AndRows a b z l q t ↔
    z=(a && b) ∧ l=(a && !b) ∧ q=(!a && b) ∧ t=(a == b) := by
  unfold AndRows MatrixMerge.One
  revert a b z l q t
  decide

/-- Complements in the actual positive rows can also be existentially quantified. -/
theorem and_extension (a b z : Bool) :
    (∃ na nb l q t : Bool, One a na false ∧ One b nb false ∧
      One z l na ∧ One z q nb ∧ One l q t) ↔ z=(a && b) := by
  constructor
  · rintro ⟨na,nb,l,q,t,ca,cb,h⟩
    rw [(not_gate ..).mp ca,(not_gate ..).mp cb] at h
    exact ((and_assignment a b z l q t).mp h).1
  · rintro rfl
    exact ⟨!a,!b,a && !b,!a && b,a == b,(not_gate ..).mpr rfl,(not_gate ..).mpr rfl,
      (and_assignment ..).mpr ⟨rfl,rfl,rfl,rfl⟩⟩

theorem pin_assignment (input positive negative : Bool) :
    (One positive negative false ∧ One (if input then positive else negative) false false) ↔
      positive=input ∧ negative=(!input) := by
  cases input <;> cases positive <;> cases negative <;> simp [MatrixMerge.One]

theorem pin_extension (input positive : Bool) :
    (∃ negative, One positive negative false ∧ One (if input then positive else negative) false false) ↔
      positive=input := by
  constructor
  · rintro ⟨v,h⟩; exact ((pin_assignment ..).mp h).1
  · intro eq; subst positive; exact ⟨!input,(pin_assignment ..).mpr ⟨rfl,rfl⟩⟩

/-- Variable identifiers in the compiler are 2+2i and 3+2i. -/
def selector (i : Nat) (b : Bool) := 2*(i+1)+b.toNat

theorem literal_pin (values : Nat → Bool) (i : Nat) (input : Bool) :
    (One (values (3+2*i)) (values (2+2*i)) false ∧ One (values (selector i input)) false false) ↔
      values (3+2*i)=input ∧ values (2+2*i)=(!input) := by
  have lo : selector i false=2+2*i := by simp [selector]; omega
  have hi : selector i true=3+2*i := by simp [selector]; omega
  cases input with
  | false => rw [lo]; exact pin_assignment false _ _
  | true => rw [hi]; exact pin_assignment true _ _

theorem selector_bit (i j : Nat) (b : Bool) :
    (selector i b).testBit j = if j=0 then b else (selector i false).testBit j := by
  cases j with
  | zero => cases b <;> simp [selector]
  | succ j =>
    have eq : (2*(i+1)+1)/2 = (2*(i+1))/2 := by omega
    cases b <;> simp [selector,Nat.testBit_succ,eq]

open AxisCompiler (Source)
open BoardInputProjection (Location occurrence address index bitCount encodedBit whereBit)

/-- At this position the false and true source matrices differ only in
    the first literal of the one pin row. The constant rows are arbitrary. -/
def withPin (base : Source m v) (row : Fin m) (i : Nat) (bound : 3+2*i<v)
    (b : Bool) : Source m v := fun j a =>
  if j=row ∧ a=0 then ⟨selector i b,by cases b <;> simp [selector] <;> omega⟩ else base j a

def offset (v : Nat) (row : Fin m) : Fin (bitCount m v) :=
  index (occurrence v row 0) ⟨0,Nat.zero_lt_succ _⟩

theorem offset_value (v : Nat) (row : Fin m) :
    (offset v row).val=(4*(7*row.val+4)+1)*BoardInputProjection.width m v := by
  change ((7*row.val+(4+0))*4+1)*_+0=_
  rw [Nat.add_zero,Nat.add_zero,Nat.mul_comm _ 4]

private theorem at_field (f : Source m v) (g : Fin m) (i : Nat) (h : 3+2*i<v) (b : Bool) :
    address (withPin f g i h b) (occurrence v g 0)=selector i b := by
  rw [BoardInputProjection.occurrence_address]
  simp [withPin]

theorem encoded_single_slot (f : Source m v) (g : Fin m) (i : Nat) (h : 3+2*i<v) (b : Bool)
    (k : Fin (bitCount m v)) :
    encodedBit (withPin f g i h b) k =
      if k=offset v g then b else encodedBit (withPin f g i h false) k := by
  by_cases active : k=offset v g
  · rw [ite_eq_left active,active,offset,BoardInputProjection.read_index,at_field,selector_bit]
    rfl
  · rw [ite_eq_right active]
    let p := (whereBit k).1
    let j := (whereBit k).2
    have split : index p j=k := BoardInputProjection.index_where k
    rw [←split,BoardInputProjection.read_index,BoardInputProjection.read_index]
    by_cases same : p=occurrence v g 0
    · have nonzero : j.val≠0 := by
        intro zero
        have fj : j=⟨0,Nat.zero_lt_succ _⟩ := Fin.ext zero
        exact active (by rw [←split,same,fj]; rfl)
      simp only [same,at_field,selector_bit i j.val b,ite_eq_right nonzero]
    · have unchanged : address (withPin f g i h b) p=address (withPin f g i h false) p := by
        apply Classical.byContradiction
        intro changed
        obtain ⟨t,a,where_,diff⟩ := BoardInputProjection.changed_location _ _ _ changed
        have miss : ¬ (t=g ∧ a=0) := by rintro ⟨rfl,rfl⟩; exact same where_
        simp [withPin,miss] at diff
      rw [unchanged]

end Mobius.PinnedGate
