import Mobius.BoardInputProjection

/-! A finite-alphabet symbol selects the first variable ID in one exact-one
    row. The trace bound below applies to an individual accepting computation.
    It assumes no read bound on other paths through the same nodes. -/
namespace Mobius.SemanticBoardQuery
open BoardInputProjection (occurrence address boards)
open AxisCompiler (Source)

def selectSource (base : Source m v) (owner : Fin m → Option (Fin n))
    (wire : Fin n → D → Fin v) (x : Fin n → D) : Source m v := fun row slot =>
  if slot = 0 then
    match owner row with
    | some i => wire i (x i)
    | none => base row slot
  else base row slot

theorem selected_address (base : Source m v) (owner : Fin m → Option (Fin n))
    (wire : Fin n → D → Fin v) (x : Fin n → D) (h : owner row = some i) :
    address (selectSource base owner wire x) (occurrence v row 0) = (wire i (x i)).val := by
  rw [BoardInputProjection.occurrence_address]
  simp [selectSource, h]

theorem pin_boards_distinct {row other : Fin m}
    (h : (occurrence v row 0).1 = (occurrence v other 0).1) : row = other := by
  have e := congrArg Fin.val h
  change 7 * row.val + (4 + 0) = 7 * other.val + (4 + 0) at e
  exact Fin.ext (by omega)

/-- Matching the symbol owned by this board suffices for all four axes.
    On a fixed board the agreement hypothesis is vacuous. -/
theorem board_agrees (base : Source m v) (owner : Fin m → Option (Fin n))
    (wire : Fin n → D → Fin v) (x y : Fin n → D) (b : Fin (boards m v))
    (agree : ∀ row i, owner row = some i → (occurrence v row 0).1 = b → x i = y i)
    (a : AxisGlue.Axis) :
    address (selectSource base owner wire x) (b,a) =
      address (selectSource base owner wire y) (b,a) := by
  apply Classical.byContradiction
  intro different
  obtain ⟨row, slot, loc, changes⟩ := BoardInputProjection.changed_location _ _ _ different
  apply changes
  by_cases pin : slot = 0
  · subst slot
    cases h : owner row with
    | none => simp [selectSource, h]
    | some i => simp [selectSource, h, agree row i h (congrArg Prod.fst loc).symm]
  · simp [selectSource, pin]

/-- First read the chosen symbols once, then run the original trace using
    its cached answers whenever one of those symbols is tested. -/
def cachedTrace (chosen : Fin n → Bool) (trace : List (Fin n)) :=
  (List.finRange n).filter chosen ++ trace.filter (fun i => !(chosen i))

private theorem length_le_quota [DecidableEq I] (ids trace : List I) (r : Nat)
    (covers : ∀ i ∈ trace, i ∈ ids) (quota : ∀ i, trace.count i ≤ r) :
    trace.length ≤ r * ids.length := by
  induction ids generalizing trace with
  | nil => cases trace with
    | nil => simp
    | cons i rest => exact False.elim (List.not_mem_nil (covers i (by simp)))
  | cons i ids ih =>
    let rest := trace.filter (fun j => decide (j ≠ i))
    have sub : rest.Sublist trace := List.filter_sublist
    have restBound := ih rest (by
      intro j hj
      obtain ⟨mem, ne⟩ := List.mem_filter.mp hj
      exact (List.mem_cons.mp (covers j mem)).resolve_left (of_decide_eq_true ne))
      (fun j => Nat.le_trans (sub.count_le j) (quota j))
    have split : trace.length = trace.count i + rest.length := by
      simpa [rest, List.count_eq_countP, List.countP_eq_length_filter] using
        (List.length_eq_countP_add_countP (fun j => j == i) (l := trace))
    rw [List.length_cons, Nat.mul_succ]
    have := quota i
    omega

private theorem cached_count (chosen : Fin n → Bool) (trace : List (Fin n)) (hr : 1 ≤ r)
    (quota : ∀ i, chosen i = false → trace.count i ≤ r) (i : Fin n) :
    (cachedTrace chosen trace).count i ≤ r := by
  rw [cachedTrace, List.count_append]
  cases h : chosen i with
  | true =>
    have miss : i ∉ trace.filter (fun j => !(chosen j)) := by simp [h]
    rw [List.count_eq_zero_of_not_mem miss, Nat.add_zero, List.count_filter h,
      (List.nodup_finRange n).count_of_mem (List.mem_finRange i)]
    exact hr
  | false =>
    have miss : i ∉ (List.finRange n).filter chosen := by simp [h]
    rw [List.count_eq_zero_of_not_mem miss, Nat.zero_add, List.count_filter (by simp [h])]
    exact quota i h

theorem cached_length (chosen : Fin n → Bool) (trace : List (Fin n)) (hr : 1 ≤ r)
    (quota : ∀ i, chosen i = false → trace.count i ≤ r) :
    (cachedTrace chosen trace).length ≤ r * n := by
  have length := length_le_quota (List.finRange n) (cachedTrace chosen trace) r
    (fun i _ => List.mem_finRange i) (cached_count chosen trace hr quota)
  simpa using length

private theorem phase_count [DecidableEq I] (phases : List (List I)) (i : I)
    (distinct : ∀ u ∈ phases, u.Nodup) :
    phases.flatten.count i = phases.countP (fun u => u.contains i) := by
  induction phases with
  | nil => rfl
  | cons u rest ih =>
    have head := distinct u (by simp)
    have tail := ih (fun v hv => distinct v (List.mem_cons_of_mem _ hv))
    by_cases mem : i ∈ u <;> simp [head.count, mem, tail, Nat.add_comm]

/-- Reading each phase's allowed variables once restores a syntactic read
    bound. A chosen exception is queried up front and omitted from all phases. -/
theorem phase_read_bound (chosen : Fin n → Bool) (phases : List (List (Fin n))) (hr : 1 ≤ r)
    (distinct : ∀ u ∈ phases, u.Nodup) (quota : ∀ i, phases.countP (fun u => u.contains i) ≤ r)
    (i : Fin n) : (cachedTrace chosen phases.flatten).count i ≤ r :=
  cached_count chosen phases.flatten hr (fun j _ => phase_count phases j distinct ▸ quota j) i

inductive Test (n : Nat) (D : Type) where
  | constant (enabled : Bool)
  | query (index : Fin n) (accepts : D → Bool)

def Test.eval (t : Test n D) (x : Fin n → D) : Bool :=
  match t with
  | .constant b => b
  | .query i check => check (x i)

def indices (label : E → Test n D) (path : List E) : List (Fin n) :=
  path.filterMap fun e => match label e with
    | .constant _ => none
    | .query i _ => some i

def acceptsOn (g : ReadRestriction.Graph V E) (label : E → Test n D)
    (x : Fin n → D) (path : List E) : Prop :=
  g.walk g.initial path ∧ ∀ e ∈ path, (label e).eval x = true

/-- If another input differs only at i and is rejected, every witness for
    x actually tests i, even if the rest of the graph has arbitrary reads. -/
theorem must_query (g : ReadRestriction.Graph V E) (label : E → Test n D)
    (x y : Fin n → D) (i : Fin n) (same : ∀ j, j ≠ i → x j = y j)
    (path : List E) (accepted : acceptsOn g label x path)
    (rejected : ¬ ∃ route, acceptsOn g label y route) : i ∈ indices label path := by
  apply Classical.byContradiction
  intro missing
  apply rejected
  refine ⟨path, accepted.1, ?_⟩
  intro e he
  have pass := accepted.2 e he
  cases h : label e with
  | constant b => simpa [h, Test.eval] using pass
  | query j check =>
    have ne : j ≠ i := by
      rintro rfl
      apply missing
      exact List.mem_filterMap.mpr ⟨e, he, by simp [h]⟩
    simpa [h, Test.eval, same j ne] using pass

def withCache (chosen : Fin n → Bool) (values : {i // chosen i = true} → D)
    (x : Fin n → D) (i : Fin n) : D :=
  if h : chosen i = true then values ⟨i,h⟩ else x i

private theorem checked_cache (chosen : Fin n → Bool) (values : {i // chosen i = true} → D)
    (x : Fin n → D) (checked : ∀ i, values i = x i.val) : withCache chosen values x = x := by
  funext i
  unfold withCache
  split
  · exact checked _
  · rfl

/-- Guess a set and its values, check the values, then cap the number of
    actual probes. Completeness needs just one affordable witness per yes
    input. Soundness applies even to a wrong guess of the exceptional set. -/
theorem cached_accept_iff (g : ReadRestriction.Graph V E) (label : E → Test n D)
    (x : Fin n → D) (hr : 1 ≤ r)
    (witness : (∃ path, acceptsOn g label x path) →
      ∃ path chosen, acceptsOn g label x path ∧ (List.finRange n).countP chosen ≤ k ∧
        ∀ i, chosen i = false → (indices label path).count i ≤ r) :
    (∃ path, acceptsOn g label x path) ↔
      ∃ (chosen : Fin n → Bool) (values : {i // chosen i = true} → D),
        (List.finRange n).countP chosen ≤ k ∧ (∀ i, values i = x i.val) ∧
        ∃ path, acceptsOn g label (withCache chosen values x) path ∧
          (cachedTrace chosen (indices label path)).length ≤ r * n := by
  constructor
  · intro accepted
    obtain ⟨path, chosen, original, few, quota⟩ := witness accepted
    refine ⟨chosen, fun i => x i.val, few, fun _ => rfl, path, ?_, cached_length _ _ hr quota⟩
    rw [checked_cache chosen _ x (fun _ => rfl)]
    exact original
  · rintro ⟨chosen, values, _, checked, path, accepts, _⟩
    exact ⟨path, checked_cache chosen values x checked ▸ accepts⟩

end Mobius.SemanticBoardQuery
