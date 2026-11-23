import Mobius.Bounded

/-! Deterministic communication for an arbitrary allowed-matrix
intersection query. A finite binary tree has unrestricted local computation
and adaptive speakers. Its worst root-to-leaf length counts transmitted
bits, not local calls, storage cells, or the size of an unrolled program. -/
namespace Mobius.OverlapProtocols

def intersects (x y : BitVec n) : Prop :=
  ∃ i : Fin n, x.getLsbD i.val = true ∧ y.getLsbD i.val = true

private theorem self_no (x : BitVec n) : ¬intersects x (~~~x) := by
  rintro ⟨i,h,k⟩
  simp only [BitVec.getLsbD_not,decide_eq_true i.isLt,Bool.true_and,h] at k
  contradiction

private theorem cross_eq {x y : BitVec n} (xy : ¬intersects x (~~~y)) (yx : ¬intersects y (~~~x)) :
    x=y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  cases ex : x.getLsbD i <;> cases ey : y.getLsbD i
  · rfl
  · exact False.elim (yx ⟨⟨i,hi⟩,ey,by simp only [BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and,ex]; rfl⟩)
  · exact False.elim (xy ⟨⟨i,hi⟩,ex,by simp only [BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and,ey]; rfl⟩)
  · rfl

/-- The complement diagonal gives 2^n mutually distinguishable
    rejecting transcripts. At least one mixed pair accepts. -/
theorem fixed_lower (p : Bounded.Protocol n 1 k)
    (correct : ∀ x y, p.run x y = true ↔ intersects x y) : n ≤ k := by
  have inj (x y : BitVec n) (same : p.transcript x (~~~x) = p.transcript y (~~~y)) : x=y := by
    have mix₁ := Bounded.transcript_mix p x (~~~x) y (~~~y) same
    have mix₂ := Bounded.transcript_mix p y (~~~y) x (~~~x) same.symm
    exact cross_eq (fun h => self_no y ((correct ..).mp (mix₁ ▸ (correct ..).mpr h)))
      (fun h => self_no x ((correct ..).mp (mix₂ ▸ (correct ..).mpr h)))
  have count := Bounded.fin_size_le
    (fun i : Fin (2^n) => (p.transcript (.ofFin i) (~~~(BitVec.ofFin i))).toFin)
    (fun i j e => congrArg BitVec.toFin (inj (.ofFin i) (.ofFin j) (congrArg BitVec.ofFin e)))
  change 2^n ≤ 2^(1*k) at count
  rw [Nat.one_mul] at count
  exact Nat.le_of_not_lt (fun h => Nat.not_lt_of_ge count (Nat.pow_lt_pow_right (by decide : 1<2) h))

inductive Tree (n : Nat) where
  | halt (answer : BitVec n → Bool)
  | left (write : BitVec n → Bool) (zero one : Tree n)
  | right (write : BitVec n → Bool) (zero one : Tree n)

def Tree.run : Tree n → BitVec n → BitVec n → Bool
  | .halt h, _, y => h y
  | .left w a b, x, y => if w x then b.run x y else a.run x y
  | .right w a b, x, y => if w y then b.run x y else a.run x y

def Tree.depth : Tree n → Nat
  | .halt _ => 0
  | .left _ a b | .right _ a b => max a.depth b.depth + 1

private def idle (n : Nat) (answer : BitVec n → Bool) : (k : Nat) → Bounded.Protocol n 1 k
  | 0 => .done answer
  | k+1 => .left (fun _ => 0) (fun _ => idle n answer k)

private theorem idle_run (answer : BitVec n → Bool) (k : Nat) (x y : BitVec n) :
    (idle n answer k).run x y = answer y := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

private theorem child_bounds {a b k : Nat} (h : max a b + 1 ≤ k+1) : a≤k ∧ b≤k :=
  ⟨Nat.le_trans (Nat.le_max_left ..) (Nat.le_of_succ_le_succ h),
   Nat.le_trans (Nat.le_max_right ..) (Nat.le_of_succ_le_succ h)⟩

private def padded (k : Nat) (t : Tree n) (enough : t.depth ≤ k) : Bounded.Protocol n 1 k :=
  match k,t with
  | 0,.halt h => .done h
  | 0,.left _ _ _ => False.elim (Nat.not_succ_le_zero _ enough)
  | 0,.right _ _ _ => False.elim (Nat.not_succ_le_zero _ enough)
  | k+1,.halt h => idle n h (k+1)
  | k+1,.left w a b => .left (fun x => BitVec.ofBool (w x)) (fun bit =>
      if bit.getLsbD 0 then padded k b (child_bounds enough).2 else padded k a (child_bounds enough).1)
  | k+1,.right w a b => .right (fun y => BitVec.ofBool (w y)) (fun bit =>
      if bit.getLsbD 0 then padded k b (child_bounds enough).2 else padded k a (child_bounds enough).1)

private theorem padded_correct (k : Nat) (t : Tree n) (enough : t.depth ≤ k) (x y : BitVec n) :
    (padded k t enough).run x y = t.run x y := by
  induction k generalizing t with
  | zero =>
    cases t with
    | halt h => rfl
    | left => exact False.elim (Nat.not_succ_le_zero _ enough)
    | right => exact False.elim (Nat.not_succ_le_zero _ enough)
  | succ k ih =>
    cases t with
    | halt h => exact idle_run h (k+1) x y
    | left w a b =>
      cases e : w x
      · simpa [padded,Bounded.Protocol.run,Tree.run,e] using ih a (child_bounds enough).1
      · simpa [padded,Bounded.Protocol.run,Tree.run,e] using ih b (child_bounds enough).2
    | right w a b =>
      cases e : w y
      · simpa [padded,Bounded.Protocol.run,Tree.run,e] using ih a (child_bounds enough).1
      · simpa [padded,Bounded.Protocol.run,Tree.run,e] using ih b (child_bounds enough).2

theorem interactive_lower (t : Tree n) (correct : ∀ x y, t.run x y = true ↔ intersects x y) :
    n ≤ t.depth := by
  apply fixed_lower (padded t.depth t (Nat.le_refl _))
  intro x y
  rw [padded_correct]
  exact correct x y

/-- The k×k matrix is serialized as its k² independent allowed bits. -/
theorem matrix_lower (k : Nat) (t : Tree (k*k))
    (correct : ∀ x y, t.run x y = true ↔ intersects x y) : k*k ≤ t.depth :=
  interactive_lower t correct

/-- Number of bits actually transmitted on this input pair. -/
def Tree.cost : Tree n → BitVec n → BitVec n → Nat
  | .halt _, _, _ => 0
  | .left w a b, x, y => (if w x then b.cost x y else a.cost x y) + 1
  | .right w a b, x, y => (if w y then b.cost x y else a.cost x y) + 1

private def truncate (k : Nat) (t : Tree n) : Tree n :=
  match k,t with
  | _,.halt a => .halt a
  | 0,.left _ _ _ | 0,.right _ _ _ => .halt (fun _ => false)
  | k+1,.left w a b => .left w (truncate k a) (truncate k b)
  | k+1,.right w a b => .right w (truncate k a) (truncate k b)

private theorem truncate_depth (k : Nat) (t : Tree n) : (truncate k t).depth ≤ k := by
  induction k generalizing t with
  | zero => cases t <;> exact Nat.zero_le _
  | succ k ih =>
    cases t with
    | halt => exact Nat.zero_le _
    | left w a b | right w a b => exact Nat.succ_le_succ (Nat.max_le.mpr ⟨ih a,ih b⟩)

private theorem truncate_run (k : Nat) (t : Tree n) (x y : BitVec n) (h : t.cost x y ≤ k) :
    (truncate k t).run x y = t.run x y := by
  induction k generalizing t with
  | zero =>
    cases t with
    | halt => rfl
    | left | right => exact False.elim (Nat.not_succ_le_zero _ h)
  | succ k ih =>
    cases t with
    | halt => rfl
    | left w a b =>
      cases e : w x <;> simp [Tree.cost,e] at h <;> simp [truncate,Tree.run,e,ih _ h]
    | right w a b =>
      cases e : w y <;> simp [Tree.cost,e] at h <;> simp [truncate,Tree.run,e,ih _ h]

/-- The lower bound is witnessed by an actual run, even if a deeper branch
    of the protocol has no inputs leading to it. -/
theorem interactive_cost_lower (t : Tree n) (correct : ∀ x y, t.run x y = true ↔ intersects x y) :
    ∃ x y, n ≤ t.cost x y := by
  cases n with
  | zero => exact ⟨0,0,Nat.zero_le _⟩
  | succ k =>
    apply Classical.byContradiction
    intro no
    have cap (x y : BitVec (k+1)) : t.cost x y ≤ k := by
      exact Nat.le_of_not_lt (fun h => no ⟨x,y,h⟩)
    have yes (x y : BitVec (k+1)) : (truncate k t).run x y = true ↔ intersects x y := by
      rw [truncate_run k t x y (cap x y)]
      exact correct x y
    exact Nat.not_succ_le_self k (Nat.le_trans (interactive_lower (truncate k t) yes) (truncate_depth k t))

theorem matrix_cost_lower (k : Nat) (t : Tree (k*k))
    (correct : ∀ x y, t.run x y = true ↔ intersects x y) :
    ∃ x y, k*k ≤ t.cost x y := interactive_cost_lower t correct

end Mobius.OverlapProtocols
