import Std

/-! Invariant colourings of the product of two ordered rooted cycles.
Adding the new largest vertex either inserts it in an old orbit or
leaves it as a separate fixed point. -/
namespace Mobius.OrderedMatching

def Stable (step : α → α) (colour : α → Bool) := ∀ x, colour (step x) = colour x

def OneOrbit (step : α → α) :=
  ∀ c : α → Bool, Stable step c → ∀ x y, c x = c y

def swapRoot [DecidableEq α] (o : α) : Option α → Option α
  | none => some o
  | some x => if x = o then none else some x

theorem swap_twice [DecidableEq α] (o : α) (x : Option α) :
    swapRoot o (swapRoot o x) = x := by
  cases x with
  | none => simp [swapRoot]
  | some x => by_cases h : x = o <;> simp [swapRoot, h]

def forward [DecidableEq α] (o : α) (d : α → α) (active : Bool) (x : Option α) :=
  if active then swapRoot o (x.map d) else x.map d

def backward [DecidableEq α] (o : α) (q : α → α) (singled : Bool) (x : Option α) :=
  (if singled then x else swapRoot o x).map q

theorem colouring_step [DecidableEq α] (o : α) (d q : α → α) (s t : Bool)
    (c : Option α → Bool) :
    Stable (fun x => backward o q t (forward o d s x)) c ↔
      Stable (fun x => q (d x)) (fun x => c (some x)) ∧
      (s = t → c none = c (some (q o))) := by
  have same :
      Stable (fun x : Option α => (swapRoot o (x.map d)).map q) c ↔
        Stable (fun x => q (d x)) (fun x => c (some x)) ∧ c none = c (some (q o)) := by
    constructor
    · intro h
      have fresh := (h none).symm
      change c none = c (some (q o)) at fresh
      refine ⟨?_, fresh⟩
      intro x
      have old := h (some x)
      by_cases hx : d x = o
      · simpa [hx] using fresh.symm.trans (by simpa [swapRoot, hx] using old)
      · simpa [swapRoot, hx] using old
    · rintro ⟨h, fresh⟩ x
      cases x with
      | none => exact fresh.symm
      | some x =>
        by_cases hx : d x = o
        · simpa [swapRoot, hx] using fresh.trans (by simpa [hx] using h x)
        · simpa [swapRoot, hx] using h x
  have different :
      Stable (fun x : Option α => (x.map d).map q) c ↔
        Stable (fun x => q (d x)) (fun x => c (some x)) := by
    constructor
    · intro h x
      exact h (some x)
    · intro h x
      cases x with
      | none => rfl
      | some x => exact h x
  cases s <;> cases t <;> simp [forward, backward, swap_twice, same] <;> simpa using different

theorem orbit_step [DecidableEq α] (o : α) (d q : α → α) (s t : Bool) :
    OneOrbit (fun x => backward o q t (forward o d s x)) ↔
      s=t ∧ OneOrbit (fun x => q (d x)) := by
  constructor
  · intro h
    have equal : s = t := by
      apply Classical.byContradiction
      intro diff
      let c : Option α → Bool := fun x => x.isSome
      have stable := (colouring_step o d q s t c).mpr
        ⟨fun _ => rfl, fun yes => False.elim (diff yes)⟩
      have impossible := h c stable none (some o)
      contradiction
    refine ⟨equal, ?_⟩
    intro c stable x y
    let ext : Option α → Bool := fun z => z.elim (c (q o)) c
    have ok := (colouring_step o d q s t ext).mpr ⟨stable, fun _ => rfl⟩
    exact h ext ok (some x) (some y)
  · rintro ⟨equal, h⟩ c stable
    have ⟨old, fresh⟩ := (colouring_step o d q s t c).mp stable
    have same := h (fun x => c (some x)) old
    intro x y
    cases x <;> cases y
    · rfl
    · exact (fresh equal).trans (same _ _)
    · exact (same _ _).trans (fresh equal).symm
    · exact same _ _

def Vertices : Nat → Type
  | 0 => Unit
  | n+1 => Option (Vertices n)

structure Maps (α : Type) where
  root : α
  d : α → α
  q : α → α

noncomputable def Maps.grow (p : Maps α) (s t : Bool) : Maps (Option α) := by
  classical
  exact ⟨some p.root, forward p.root p.d s, backward p.root p.q t⟩

noncomputable def cycles : (bits : List (Bool × Bool)) → Maps (Vertices bits.length)
  | [] => ⟨(), id, id⟩
  | st :: tail => (cycles tail).grow st.1 st.2

theorem one_cycle_iff_equal (bits : List (Bool × Bool)) :
    OneOrbit (fun x => (cycles bits).q ((cycles bits).d x)) ↔
      ∀ st ∈ bits, st.1 = st.2 := by
  classical
  induction bits with
  | nil =>
    simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
    intro c h x y
    cases x
    cases y
    rfl
  | cons st tail ih =>
    let p := cycles tail
    rw [List.forall_mem_cons, ← ih]
    exact orbit_step p.root p.d p.q st.1 st.2

end Mobius.OrderedMatching
