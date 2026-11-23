import Mobius.Bounded

/-! Exact one-way memory for two-station queries to a graph on k shared
stations. The left side asks that true stations be independent; the right
side requests two distinct true stations. This module concerns the
boundary relation itself and does not assume any graph coloring gadget. -/
namespace Mobius.ThreeFaceMemory

def slots : Nat → Nat
  | 0 => 0
  | k+1 => slots k+k

private theorem slots_mono {a b : Nat} (h : a≤b) : slots a≤slots b := by
  induction b with
  | zero =>
    have e : a=0 := by omega
    rw [e]; exact Nat.le_refl _
  | succ b ih =>
    by_cases e : a=b+1
    · rw [e]; exact Nat.le_refl _
    · have ih' := ih (by omega)
      simp only [slots]; omega

theorem slot_count (k : Nat) : 2*slots k=k*(k-1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => decide
    | succ k =>
      simp only [slots,Nat.mul_add] at ih ⊢
      simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero] at ih ⊢
      simp only [Nat.succ_mul,Nat.mul_succ] at ih ⊢
      omega

structure Query (k : Nat) where
  lo : Fin k
  hi : Fin k
  ordered : lo.val<hi.val
  deriving DecidableEq

def number (q : Query k) : Fin (slots k) :=
  ⟨slots q.hi.val + q.lo.val,by
    have upper := slots_mono (a:=q.hi.val+1) (b:=k) q.hi.isLt
    have lt := q.ordered
    simp only [slots] at upper
    omega⟩

private theorem query_recover {q t : Query k}
    (a : t.lo=q.lo ∨ t.lo=q.hi) (b : t.hi=q.lo ∨ t.hi=q.hi) : t=q := by
  obtain ⟨i,j,ij⟩:=q
  obtain ⟨s,u,su⟩:=t
  change s=i ∨ s=j at a
  change u=i ∨ u=j at b
  rcases a with rfl|rfl <;> rcases b with rfl|rfl <;> first | rfl | omega

theorem number_surjective (k : Nat) : ∀ i : Fin (slots k), ∃ q : Query k, number q=i := by
  induction k with
  | zero => exact fun i => Fin.elim0 i
  | succ k ih =>
    intro i
    by_cases before : i.val<slots k
    · obtain ⟨q,h⟩ := ih ⟨i.val,before⟩
      exact ⟨⟨q.lo.castSucc,q.hi.castSucc,q.ordered⟩,Fin.ext (congrArg (fun j : Fin (slots k) => j.val) h)⟩
    · have hi := i.isLt
      change i.val<slots k+k at hi
      let lo : Fin (k+1) := ⟨i.val-slots k,by omega⟩
      refine ⟨⟨lo,Fin.last k,by change i.val-slots k<k; omega⟩,?_⟩
      apply Fin.ext
      change slots k + (i.val-slots k)=i.val
      omega

theorem number_injective {q t : Query k} (h : number q=number t) : q=t := by
  have eqn := congrArg Fin.val h
  change slots q.hi.val+q.lo.val=slots t.hi.val+t.lo.val at eqn
  have compare {p r : Query k} (lt : p.hi.val<r.hi.val) :
      slots p.hi.val+p.lo.val<slots r.hi.val+r.lo.val := by
    have h₁ := slots_mono (a:=p.hi.val+1) (b:=r.hi.val) lt
    have h₂ := p.ordered
    simp only [slots] at h₁
    omega
  have same : q.hi.val=t.hi.val := by
    by_cases left : q.hi.val<t.hi.val
    · have := compare (p:=q) (r:=t) left; omega
    by_cases right : t.hi.val<q.hi.val
    · have := compare (p:=t) (r:=q) right; omega
    omega
  have sameLo : q.lo=t.lo := Fin.ext (by rw [same] at eqn; omega)
  have sameHi : q.hi=t.hi := Fin.ext same
  exact query_recover (q:=t) (t:=q) (Or.inl sameLo) (Or.inr sameHi)

abbrev Graph (k : Nat) := BitVec (slots k)

def adjacent (g : Graph k) (q : Query k) := g.getLsbD (number q).val

def Left (g : Graph k) (s : Fin k → Bool) : Prop :=
  ∀ e : Query k, adjacent g e=true → ¬(s e.lo=true ∧ s e.hi=true)

def Right (q : Query k) (s : Fin k → Bool) : Prop := s q.lo=true ∧ s q.hi=true

def Join (g : Graph k) (q : Query k) : Prop := ∃ s, Left g s ∧ Right q s

theorem join_iff (g : Graph k) (q : Query k) : Join g q ↔ adjacent g q=false := by
  constructor
  · rintro ⟨s,left,right⟩
    cases h : adjacent g q
    · rfl
    · exact False.elim (left q h right)
  · intro absent
    let s := fun i : Fin k => decide (i=q.lo ∨ i=q.hi)
    refine ⟨s,?_,by simp [Right,s]⟩
    intro e edge selected
    have eqn := query_recover (q:=q) (t:=e) (of_decide_eq_true selected.1) (of_decide_eq_true selected.2)
    rw [eqn,absent] at edge
    contradiction

/-- No upper bound is imposed on the deterministic local computation on
either side. Only the left summary is counted. -/
theorem distinguish {s : Type} (send : Graph k → s) (answer : s → Query k → Bool)
    (correct : ∀ g q, answer (send g) q=true ↔ Join g q) {a b : Graph k}
    (same : send a=send b) : a=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨q,slot⟩ := number_surjective k ⟨j,hj⟩
  have va := correct a q
  have vb := correct b q
  rw [same,join_iff] at va
  rw [join_iff] at vb
  have eqn := va.symm.trans vb
  change a.getLsbD (number q).val=false ↔ b.getLsbD (number q).val=false at eqn
  rw [slot] at eqn
  cases ha : a.getLsbD j <;> cases hb : b.getLsbD j <;> simp_all

theorem state_lower (send : Graph k → Fin s) (answer : Fin s → Query k → Bool)
    (correct : ∀ g q, answer (send g) q=true ↔ Join g q) : 2^(slots k)≤s := by
  apply Bounded.fin_size_le (fun i => send (BitVec.ofFin i))
  intro i j h
  exact congrArg BitVec.toFin (distinguish send answer correct h)

def answerFull (g : Graph k) (q : Query k) : Bool := !(adjacent g q)

theorem exact_states (k s : Nat) :
    (∃ (send : Graph k → Fin s) (answer : Fin s → Query k → Bool),
      ∀ g q, answer (send g) q=true ↔ Join g q) ↔ 2^(slots k)≤s := by
  constructor
  · rintro ⟨send,answer,spec⟩; exact state_lower send answer spec
  · intro enough
    let send := fun g : Graph k => (g.toFin).castLE enough
    let read := fun a : Fin s => BitVec.ofNat (slots k) a.val
    refine ⟨send,fun a q => answerFull (read a) q,?_⟩
    intro g q
    have restore : read (send g)=g := by apply BitVec.eq_of_toNat_eq; simp [read,send]
    change answerFull (read (send g)) q=true ↔ Join g q
    rw [restore,join_iff]
    simp [answerFull]

end Mobius.ThreeFaceMemory
