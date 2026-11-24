import Mobius.MatrixMerge

/-! Local facts for paired restrictions. Gate elimination counts distinct
gate names, even if many wires reuse a gate. The Boolean guard dispatch
uses just AND and OR. -/
namespace Mobius.PairContraction

open Mobius.MatrixMerge (One)

theorem tied_faces (p q r s : Bool) :
    (∃ a b : Bool, a = b ∧ One a p q ∧ One b r s) ↔
      p.toNat + q.toNat = r.toNat + s.toNat ∧ p.toNat + q.toNat ≤ 1 := by
  unfold MatrixMerge.One
  revert p q r s
  decide

theorem duplicated_control (selected x y : Bool) :
    (∃ copy : Bool, copy = selected ∧ (copy = true → x = true) ∧ (copy = true → y = true)) ↔
      (selected = true → (x && y) = true) := by
  revert selected x y
  decide

def dispatch (allPairs small anyForeign big : Bool) :=
  (allPairs && small) || (anyForeign && big)

theorem dispatch_correct (y h z big : Bool)
    (sufficient : (y && h) = true → big = true)
    (onFace : z = false → big = (y && h)) :
    dispatch y h z big = big := by
  revert y h z big
  decide

theorem dispatch_on_pair (small big : Bool) : dispatch true small false big = small := by
  simp [dispatch]

/-- A sufficient positive condition can be ORed into every source wire. -/
theorem sufficient_mask (f : (ι → Bool) → Bool) (all : f (fun _ => true) = true)
    (x : ι → Bool) (b : Bool) (suff : b = true → f x = true) :
    f (fun i => x i || b) = f x := by
  cases b with
  | false => simp
  | true => simpa using all.trans (suff rfl).symm

/-- A short list cannot cover distinct boards when each label hits few of them. -/
theorem path_list_misses (boards : List α) (labels : List β) (hits : β → List α) (cap : Nat)
    (distinct : boards.Nodup) (bound : ∀ l ∈ labels, (hits l).length ≤ cap)
    (short : cap * labels.length < boards.length) :
    ∃ x ∈ boards, ∀ l ∈ labels, x ∉ hits l := by
  classical
  have limit (ls : List β) (h : ∀ l ∈ ls, (hits l).length ≤ cap) :
      (ls.flatMap hits).length ≤ cap * ls.length := by
    induction ls with
    | nil => simp
    | cons l ls ih =>
      have head := h l (by simp)
      have tail := ih (fun a ha => h a (by simp [ha]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
      omega
  apply Classical.byContradiction
  intro noMiss
  have sub : boards ⊆ labels.flatMap hits := by
    intro x hx
    apply Classical.byContradiction
    intro missing
    exact noMiss ⟨x, hx, fun l hl hit => missing (List.mem_flatMap.mpr ⟨l, hl, hit⟩)⟩
  have lower := distinct.length_le_of_subset sub
  have upper := limit labels bound
  omega

/-- Three successive raw operands can be collected around the single incoming wire. -/
private def rawStep (takeAnd left raw : Bool) :=
  if takeAnd then left && raw else left || raw

private def extendCoeff (takeAnd : Bool) (ab : Bool × Bool) (raw : Bool) : Bool × Bool :=
  if takeAnd then (ab.1 && raw, ab.2 && raw) else (ab.1 || raw, ab.2)

theorem chain_coeff_step (op u a b x : Bool) :
    rawStep op (a || (u && b)) x =
      (extendCoeff op (a,b) x).1 || (u && (extendCoeff op (a,b) x).2) := by
  revert op u a b x
  decide

/-- The internal wire surplus left after globally caching the three-step coefficients. -/
theorem internal_branch_budget (s g₀ g₁ g₂ surplus blocks chains preprocessing slack : Nat)
    (size : s = g₀ + g₁ + g₂) (wires : g₂ + 1 = g₀ + surplus)
    (starts : chains ≤ g₀ + g₂ + 2*surplus) (partition : g₁ ≤ 3*blocks + 2*chains)
    (optimal : blocks ≤ preprocessing + slack) :
    s ≤ 7*surplus + 6*g₀ + 3*(preprocessing + slack) := by omega

/-- The two cyclic shifts force all tail bits to agree when written periodically. -/
theorem shift_pool_constant (x y : Nat → Bool) (one : ∀ i, x i = y (i+1))
    (two : ∀ i, x i = y (i+2)) : ∀ i, x i = x 0 := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => exact ((one (i+1)).trans (two i).symm).trans ih

/-- Only the prescribed tails, heads and real open edges are needed for this
necessary condition. An additional single-cycle condition may also be imposed. -/
theorem pair_forces_type (openEdge selected : V → V → Prop) (tails heads : V → Prop)
    (a b : V) (allowed : ∀ u v, selected u v → openEdge u v)
    (outgoing : ∀ v, openEdge a v → v = b)
    (incoming : ∀ u, openEdge u b → u = a)
    (rows : ∀ u, tails u ↔ ∃ v, selected u v)
    (cols : ∀ v, heads v ↔ ∃ u, selected u v) :
    tails a ↔ heads b := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (rows a).mp h
    obtain rfl := outgoing v (allowed a v hv)
    exact (cols v).mpr ⟨a, hv⟩
  · intro h
    obtain ⟨u, hu⟩ := (cols b).mp h
    obtain rfl := incoming u (allowed u b hu)
    exact (rows u).mpr ⟨b, hu⟩

/-- A globally sufficient gate may be split off the output, independently
of the logic downstream of the gate. -/
theorem sufficient_gate_split (value : Bool) (down : Bool → Bool)
    (suff : value = true → down value = true) :
    (value || down false) = down value := by
  cases value <;> simp_all

/-- Regroup boundary signals by the set of continuations available to them. -/
theorem regroup_contexts (signal : ι → α → Prop) (key : ι → κ) (context : κ → β → Prop)
    (join : α → β → γ) (w : γ) :
    (∃ i p q, signal i p ∧ context (key i) q ∧ join p q = w) ↔
    ∃ k p q, (∃ i, key i = k ∧ signal i p) ∧ context k q ∧ join p q = w := by
  constructor
  · rintro ⟨i, p, q, hp, hq, hw⟩
    exact ⟨key i, p, q, ⟨i, rfl, hp⟩, hq, hw⟩
  · rintro ⟨k, p, q, ⟨i, rfl, hp⟩, hq, hw⟩
    exact ⟨i, p, q, hp, hq, hw⟩

theorem high_band_budget (entries sums products excess overhead : Nat)
    (flow : sums + 1 = entries + excess)
    (optimal : sums + products + 1 ≤ entries + overhead) :
    products + excess ≤ overhead := by omega

/-- Only operands in the upper band are listed. The other operand of an
extension is a lower-degree factor. -/
inductive HighGate (V : Type) where
  | entry
  | extend (child : V)
  | merge (left right : V)

private def highLiveInputs (g : HighGate V) (on : V → Bool) (value : Bool) : Nat :=
  if value then match g with
    | .entry => 0
    | .extend x => (on x).toNat
    | .merge x y => (on x).toNat + (on y).toNat
  else 0

private def liveEntry (g : HighGate V) (value : Bool) : Bool :=
  match g with
  | .entry => value
  | _ => false

private def liveBoth (g : HighGate V) (on : V → Bool) : Bool :=
  match g with
  | .merge x y => on x && on y
  | _ => false

private def highConsistent (g : HighGate V) (on : V → Bool) (value : Bool) : Prop :=
  match g with
  | .entry => True
  | .extend x => value = true → on x = true
  | .merge x y => value = (on x || on y)

/-- Counting the high wires inside nonzero gates before hash-consing or pruning. -/
theorem live_high_wires (gs : List V) (kind : V → HighGate V) (on : V → Bool)
    (correct : ∀ g ∈ gs, highConsistent (kind g) on (on g)) :
    (gs.map (fun g => highLiveInputs (kind g) on (on g))).sum +
      gs.countP (fun g => liveEntry (kind g) (on g)) =
      gs.countP on + gs.countP (fun g => liveBoth (kind g) on) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun x hx => correct x (by simp [hx]))
    have head := correct g (by simp)
    have contribution :
        highLiveInputs (kind g) on (on g) + (if liveEntry (kind g) (on g) then 1 else 0) =
        (if on g then 1 else 0) + (if liveBoth (kind g) on then 1 else 0) := by
      cases t : kind g with
      | entry => cases h : on g <;> simp [highLiveInputs, liveEntry, liveBoth]
      | extend x =>
        cases h : on g <;> cases a : on x <;>
          simp [highConsistent, highLiveInputs, liveEntry, liveBoth, t, h, a] at head ⊢
      | merge x y =>
        cases h : on g <;> cases a : on x <;> cases b : on y <;>
          simp [highConsistent, highLiveInputs, liveEntry, liveBoth, t, h, a, b] at head ⊢
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    omega

/-- Count live two-input unions using the outgoing wire capacities of live high nodes. -/
theorem live_high_unions (entries products one two excess : Nat)
    (capacity : products + one + 2*two + 1 ≤ entries + products + one + two + excess) :
    two + 1 ≤ entries + excess := by omega

private def operands (gates : List V) (child : V → Bool → V) :=
  gates.flatMap (fun g => [child g false, child g true])

def lost (constant : V → Bool) (child : V → Bool → V) (g : V) :=
  constant g || constant (child g false) || constant (child g true)

private theorem operand_capacity (gs : List V) (c : V → Bool) (ch : V → Bool → V)
    (both : ∀ g ∈ gs, c (ch g false) = true → c (ch g true) = true → c g = true) :
    ((operands gs ch).filter c).length ≤ (gs.filter c).length + gs.countP (lost c ch) := by
  induction gs with
  | nil => simp [operands]
  | cons g gs ih =>
    have upper := ih (fun v hv => both v (by simp [hv]))
    have head := both g (by simp)
    change (([ch g false, ch g true] ++ operands gs ch).filter c).length ≤ _
    cases a : c (ch g false) <;> cases b : c (ch g true) <;> cases k : c g <;>
      simp [lost, a, b, k] at head ⊢ <;> omega

/-- Every fixed input and every constant gate feeds at least one operand
in a pruned circuit with nonconstant output. Such an operand enters a gate
removed by monotone constant propagation. -/
theorem fixed_inputs_le_lost [DecidableEq V] (inputs gates : List V) (c : V → Bool)
    (ch : V → Bool → V) (ids : (inputs ++ gates.filter c).Nodup)
    (fixed : ∀ v ∈ inputs, c v = true)
    (used : ∀ v ∈ inputs ++ gates.filter c, ∃ g ∈ gates, ∃ side : Bool, ch g side = v)
    (both : ∀ g ∈ gates, c (ch g false) = true → c (ch g true) = true → c g = true) :
    inputs.length ≤ gates.countP (lost c ch) := by
  have sub : inputs ++ gates.filter c ⊆ (operands gates ch).filter c := by
    intro v hv
    obtain ⟨g, hg, side, eq⟩ := used v hv
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨g, hg, ?_⟩, ?_⟩
    · cases side <;> simp [eq]
    · rcases List.mem_append.mp hv with hi | hc
      · exact fixed v hi
      · exact (List.mem_filter.mp hc).2
  have lower := ids.length_le_of_subset sub
  have upper := operand_capacity gates c ch both
  simp only [List.length_append] at lower
  omega

/-- A constant gate with exactly one constant operand discards the other operand. -/
def absorbing (c : V → Bool) (ch : V → Bool → V) (g : V) :=
  c g && (c (ch g false) != c (ch g true))

private theorem constant_operand_count (gs : List V) (c : V → Bool) (ch : V → Bool → V)
    (both : ∀ g ∈ gs, c (ch g false) = true → c (ch g true) = true → c g = true)
    (fromChild : ∀ g ∈ gs, c g = true → c (ch g false) = true ∨ c (ch g true) = true) :
    ((operands gs ch).filter c).length + gs.countP (absorbing c ch) =
      (gs.filter c).length + gs.countP (lost c ch) := by
  induction gs with
  | nil => simp [operands]
  | cons g gs ih =>
    have tail := ih (fun v hv => both v (by simp [hv])) (fun v hv => fromChild v (by simp [hv]))
    have headBoth := both g (by simp)
    have headFrom := fromChild g (by simp)
    change (([ch g false, ch g true] ++ operands gs ch).filter c).length + _ = _
    cases a : c (ch g false) <;> cases b : c (ch g true) <;> cases h : c g <;>
      simp [lost, absorbing, a, b, h] at headBoth headFrom ⊢ <;> omega

/-- If all fixed sources and constant gates are used, the surplus counts their
outgoing wires beyond the first. The identity counts distinct gates removed
before deleting any further unreachable or structurally identical gates. -/
theorem constant_wire_balance (gs : List V) (c : V → Bool) (ch : V → Bool → V)
    (fixed surplus : Nat)
    (wireCount : ((operands gs ch).filter c).length = fixed + (gs.filter c).length + surplus)
    (both : ∀ g ∈ gs, c (ch g false) = true → c (ch g true) = true → c g = true)
    (fromChild : ∀ g ∈ gs, c g = true → c (ch g false) = true ∨ c (ch g true) = true) :
    gs.countP (lost c ch) = fixed + surplus + gs.countP (absorbing c ch) := by
  have balance := constant_operand_count gs c ch both fromChild
  omega

/-- A gate is removed by constant propagation as soon as it has a constant operand
in the paid AND/OR/NOT basis. Count each gate once, including a consumer of two pins. -/
def touchesConstant (args : V → List V) (c : V → Bool) (g : V) :=
  decide (0 < (args g).countP c)

private theorem signed_slot_capacity (gs : List V) (args : V → List V) (c : V → Bool)
    (arity : ∀ g ∈ gs, (args g).length ≤ 2)
    (both : ∀ g ∈ gs, (args g).countP c = 2 → c g = true) :
    (gs.flatMap args).countP c ≤ gs.countP c + gs.countP (touchesConstant args c) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun v hv => arity v (by simp [hv])) (fun v hv => both v (by simp [hv]))
    have cap := Nat.le_trans (List.countP_le_length (p := c) (l := args g)) (arity g (by simp))
    have forced := both g (by simp)
    have head : (args g).countP c ≤ (if c g then 1 else 0) +
        (if touchesConstant args c g then 1 else 0) := by
      by_cases zero : (args g).countP c = 0
      · simp [zero]
      · have hit : touchesConstant args c g = true := by
          simp only [touchesConstant, decide_eq_true_eq]
          omega
        by_cases two : (args g).countP c = 2
        · simp [two, forced two, hit]
        · cases val : c g <;> simp [hit] <;> omega
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons]
    omega

private theorem split_constant_slots (slots : List V) (pin c : V → Bool)
    (fixed : ∀ v, pin v = true → c v = true) :
    slots.countP pin + slots.countP (fun v => c v && !pin v) = slots.countP c := by
  induction slots with
  | nil => simp
  | cons v slots ih =>
    have head := fixed v
    cases hp : pin v <;> cases hc : c v <;>
      simp [hp, hc] at head ⊢ <;> omega

/-- In the strict descendants of a cut, each use of a pinned cut signal costs a
different removed gate, up to the one output that might itself become constant. -/
theorem cut_fanout_le_removed [DecidableEq V] (gs : List V) (args : V → List V)
    (pin c : V → Bool) (out : V) (ids : gs.Nodup)
    (apart : ∀ g ∈ gs, pin g = false) (fixed : ∀ v, pin v = true → c v = true)
    (used : ∀ g ∈ gs, g ≠ out → g ∈ gs.flatMap args)
    (arity : ∀ g ∈ gs, (args g).length ≤ 2)
    (both : ∀ g ∈ gs, (args g).countP c = 2 → c g = true) :
    (gs.flatMap args).countP pin ≤ gs.countP (touchesConstant args c) + (c out).toNat := by
  have nd : (gs.filter c).Nodup := ids.filter c
  have sub : (gs.filter c).erase out ⊆ (gs.flatMap args).filter (fun v => c v && !pin v) := by
    intro v hv
    obtain ⟨mem, cv⟩ := List.mem_filter.mp (List.mem_of_mem_erase hv)
    have ne : v ≠ out := by
      intro eq
      subst v
      exact nd.not_mem_erase hv
    exact List.mem_filter.mpr ⟨used v mem ne, by simp [cv, apart v mem]⟩
  have fit := List.Nodup.length_le_of_subset (List.Nodup.erase out nd) sub
  have sink : (gs.filter c).length ≤ ((gs.filter c).erase out).length + (c out).toNat := by
    by_cases h : out ∈ gs.filter c
    · simp [List.length_erase_of_mem h, (List.mem_filter.mp h).2]
      omega
    · rw [List.erase_of_not_mem h]
      omega
  have total := split_constant_slots (gs.flatMap args) pin c fixed
  have cap := signed_slot_capacity gs args c arity both
  simp only [List.countP_eq_length_filter] at total cap
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  omega

/-- Telescoping the paid-NOT loss for one oriented pair at a time. The
sequence may count the successive residual DAGs of a single circuit. -/
theorem oriented_pair_budget (s : Nat → Nat) (m : Nat)
    (step : ∀ k, m ≤ k → k < 2*m → s k + (2*k+1) ≤ s (k+1)) :
    s m + 3*(m*m) ≤ s (2*m) := by
  have interval (t : Nat) (ht : t ≤ m) :
      s m + (m+t)*(m+t) ≤ s (m+t) + m*m := by
    induction t with
    | zero => simp
    | succ t ih =>
      have prior := ih (by omega)
      have next := step (m+t) (by omega) (by omega)
      change s m + (m+t+1)*(m+t+1) ≤ s (m+t+1) + m*m
      rw [Nat.succ_mul, Nat.mul_succ]
      omega
  have doubled := interval m (Nat.le_refl _)
  simp only [Nat.add_mul, Nat.mul_add] at doubled
  rw [show 2*m = m+m by omega]
  omega

/-- Little-o as an integer ratio, for eventually positive size functions. -/
def Negligible (s b : Nat → Nat) := ∀ k : Nat, ∃ n₀, ∀ n ≥ n₀, k * s n ≤ b n

theorem near_forces_ratio (s b residual size : Nat → Nat) (a : Nat) (pos : 0 < a)
    (lower : ∀ n, s n ≤ residual n) (near : ∀ n, size n ≤ a * b n)
    (shrinks : Negligible residual size) : Negligible s b := by
  intro k
  obtain ⟨n₀, bound⟩ := shrinks (a*k)
  refine ⟨n₀, fun n hn => ?_⟩
  have h := Nat.le_trans (Nat.mul_le_mul_left (a*k) (lower n)) (Nat.le_trans (bound n hn) (near n))
  rw [Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h pos

theorem dispatch_is_near (s b size : Nat → Nat) (a : Nat)
    (upper : ∀ n, size n ≤ b n + a * s n) (ratio : Negligible s b) :
    ∀ k : Nat, ∃ n₀, ∀ n ≥ n₀, k * size n ≤ (k+1) * b n := by
  intro k
  obtain ⟨n₀, h⟩ := ratio (k*a)
  refine ⟨n₀, fun n hn => ?_⟩
  have cost := Nat.mul_le_mul_left k (upper n)
  have extra := h n hn
  rw [Nat.mul_add, ← Nat.mul_assoc] at cost
  rw [Nat.succ_mul]
  omega

/-- A subdivision keeps the edge excess fixed. An exactly invariant
predicate agreeing in a sparse window cannot first disagree outside
that window if successive subdivisions make the window grow unboundedly. -/
theorem growing_window (f h : X → Bool) (next : X → X) (excess room : X → Nat)
    (fSame : ∀ x, f (next x) = f x) (hSame : ∀ x, h (next x) = h x)
    (exSame : ∀ x, excess (next x) = excess x) (grows : ∀ x, room x < room (next x))
    (low : ∀ x, excess x ≤ room x → f x = h x) : ∀ x, f x = h x := by
  intro x
  generalize start : excess x - room x = n
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    by_cases inRange : excess x ≤ room x
    · exact low x inRange
    · have step := grows x
      have smaller : excess (next x) - room (next x) < n := by rw [exSame]; omega
      exact (fSame x).symm.trans ((ih _ smaller (next x) rfl).trans (hSame x))

/-- Check original gate values while feeding prescribed bits to all their consumers.
The monitored gates can depend on one another. The first mismatch is observed
on the same input in both computations. A gate law may use any earlier wire. -/
theorem monitored_replay_iff (n : Nat) (law : (i : Nat) → (Fin i → Bool) → Bool)
    (selected prescribed original replay : Nat → Bool)
    (orig : ∀ i < n, original i = law i (fun j => original j.val))
    (rewired : ∀ i < n, replay i = law i (fun j =>
      if selected j.val then prescribed j.val else replay j.val)) :
    (∀ i < n, selected i = true → original i = prescribed i) ↔
      (∀ i < n, selected i = true → replay i = prescribed i) := by
  have agree (consistent : ∀ i < n, selected i = true →
      original i = prescribed i ∨ replay i = prescribed i) :
      ∀ i < n, replay i = original i := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i earlier =>
      intro hi
      rw [rewired i hi, orig i hi]
      apply congrArg (law i)
      funext j
      have hj := Nat.lt_trans j.isLt hi
      have prev := earlier j.val j.isLt hj
      cases sel : selected j.val with
      | false => simpa [sel] using prev
      | true =>
        obtain ok | ok := consistent j.val hj sel
        · simpa [sel] using ok.symm
        · simpa [sel] using ok.symm.trans prev
  constructor
  · intro consistent i hi sel
    exact (agree (fun j hj hsel => Or.inl (consistent j hj hsel)) i hi).trans (consistent i hi sel)
  · intro consistent i hi sel
    exact (agree (fun j hj hsel => Or.inr (consistent j hj hsel)) i hi).symm.trans (consistent i hi sel)

end Mobius.PairContraction
