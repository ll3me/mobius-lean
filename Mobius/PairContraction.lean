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

/-- A directed path, including its endpoints, which avoids every cut wire. -/
inductive UncutPath (edge : V → V → Prop) (cut : V → Prop) (start : V) : V → Prop where
  | here (available : ¬cut start) : UncutPath edge cut start start
  | step {u v} (prefixPath : UncutPath edge cut start u) (arc : edge u v)
      (available : ¬cut v) : UncutPath edge cut start v

theorem UncutPath.weaken {edge : V → V → Prop} {first second : V → Prop} {u v : V}
    (path : UncutPath edge first u v) (subset : ∀ w, second w → first w) :
    UncutPath edge second u v := by
  induction path with
  | here ok => exact .here (fun h => ok (subset _ h))
  | step _ arc ok ih => exact .step ih arc (fun h => ok (subset _ h))

theorem UncutPath.append {edge : V → V → Prop} {cut : V → Prop} {u v w : V}
    (pre : UncutPath edge cut u v) (post : UncutPath edge cut v w) :
    UncutPath edge cut u w := by
  induction post with
  | here => exact pre
  | step _ arc ok ih => exact .step ih arc ok

/-- A difference between two evaluations traces back to the varied source
along an uncut path when the selected wires agree in both evaluations. -/
theorem uncut_path_of_difference (edge : Nat → Nat → Prop) (cut : Nat → Prop)
    (source : Nat) (left right : Nat → Bool)
    (agree : ∀ g, cut g → left g = right g)
    (reader : ∀ g, g ≠ source → left g ≠ right g →
      ∃ p, p < g ∧ edge p g ∧ left p ≠ right p)
    (out : Nat) : left out ≠ right out → UncutPath edge cut source out := by
  induction out using Nat.strongRecOn with
  | ind g ih =>
    intro different
    have ok : ¬cut g := fun h => different (agree g h)
    by_cases sourceHere : g = source
    · subst g
      exact .here ok
    · obtain ⟨p, hp, arc, prev⟩ := reader g sourceHere different
      exact .step (ih p hp prev) arc ok

/-- On a preselected path to the first eligible reader, only that reader
can be cut. If it still reaches the output, the original use does too. -/
theorem first_reader_preserves_use {edge : V → V → Prop} {heads cut : V → Prop}
    {use reader out : V} (onlyHeads : ∀ v, cut v → heads v)
    (first : UncutPath edge (fun v => heads v ∧ v ≠ reader) use reader)
    (kept : ¬cut reader) (suffixPath : UncutPath edge cut reader out) :
    UncutPath edge cut use out := by
  apply UncutPath.append (first.weaken ?_) suffixPath
  intro v hv
  exact ⟨onlyHeads v hv, fun eq => kept (eq ▸ hv)⟩

/-- The other pruned gates pay for at least half of the lost literal
positions. All quantities on both sides refer to one restriction. -/
theorem absorbing_reader_budget (loss fixed raw selected pruned lostUses : Nat)
    (ledger : fixed + raw + selected + pruned ≤ loss + lostUses)
    (capacity : lostUses ≤ 2 * pruned) :
    2 * (fixed + raw + selected) ≤ 2 * loss + lostUses := by omega

/-- A raw variable read in exactly one counted region must also have a
reader outside that region when the region can be pinned without it. -/
theorem bypass_reader_count (regions reads : Nat)
    (distinctReads : regions ≤ reads) (bypass : regions = 1 → 2 ≤ reads) :
    regions ≤ 2 * (reads - 1) := by omega

/-- Below the raw-literal threshold the internal budget must exceed
197/150 of the gap. All the following tests use the old baseline. -/
theorem residual_internal_weight (gap delta internal : Nat)
    (total : 4 * gap ≤ 3 * (delta + internal)) (below : 50 * delta < gap) :
    197 * gap < 150 * internal := by omega

/-- For a prescribed cut at m >= 40, each certified position contributes
at least 39/40 in expectation after retaining both of its readers. -/
theorem monochrome_one_percent (gap internal covered extra : Nat)
    (weight : 197 * gap < 150 * internal) (coverage : internal ≤ 128 * covered)
    (earned : 39 * covered ≤ 40 * extra) : gap ≤ 100 * extra := by omega

/-- For m >= 158, a trigger probability of 1/4 less the two-reader
allowance 1/m is at least 77/316. -/
theorem quarter_trigger_one_percent (gap internal covered extra : Nat)
    (weight : 197 * gap < 150 * internal) (coverage : internal ≤ 32 * covered)
    (earned : 77 * covered ≤ 316 * extra) : gap ≤ 100 * extra := by omega

/-- Enough distinct exposed raw reads exhaust the small-delta case,
regardless of the geometric compatibility of their certificates. -/
theorem private_region_one_percent (gap base delta internal exposed : Nat)
    (total : 4 * gap ≤ 3 * (delta + internal))
    (coverage : internal ≤ 32 * exposed) (raw : exposed ≤ 2 * (base + delta))
    (scale : 1920 * base ≤ gap) : gap ≤ 50 * delta := by omega

/-- Cut all uses of one wire, holding the rest of the primary input fixed. -/
theorem observable_substitution (context : Bool → Bool) (old new : Bool) :
    context old ≠ context new ↔ old ≠ new ∧ context false ≠ context true := by
  cases old <;> cases new <;> cases h₀ : context false <;> cases h₁ : context true <;> simp_all

/-- A window consumes at most three marked regions; a normalization deletion
can touch the region of the deleted gate and the region of its new driver. -/
theorem window_step_budget (removed inserted normalized spoiled : Nat)
    (width : removed ≤ 3) (cheaper : inserted < removed)
    (touch : spoiled ≤ removed + 2 * normalized) :
    spoiled + 3 * inserted ≤ 3 * (removed + normalized) := by omega

/-- Telescope the packing budget through the actual sequence of rewrites. -/
theorem window_packing_budget (size marks : Nat → Nat) (rounds : Nat)
    (step : ∀ i < rounds, marks i + 3 * size (i+1) ≤ marks (i+1) + 3 * size i)
    (finished : marks rounds = 0) : marks 0 + 3 * size rounds ≤ 3 * size 0 := by
  have telescope (j : Nat) (hj : j ≤ rounds) :
      marks 0 + 3 * size j ≤ marks j + 3 * size 0 := by
    induction j with
    | zero => omega
    | succ j ih =>
      have prev := ih (by omega)
      have thisStep := step j (by omega)
      omega
  have last := telescope rounds (by omega)
  omega

/-- The same binary signal cannot be decoded as AND in one context and OR in another. -/
theorem and_or_distinct_partitions (p : Bool → Bool → Bool) (a o : Bool → Bool)
    (ha : ∀ x y, a (p x y) = (x && y)) (ho : ∀ x y, o (p x y) = (x || y)) : False := by
  have a₀ := ha false false
  have a₁ := ha false true
  have a₂ := ha true true
  have o₀ := ho false false
  have o₁ := ho false true
  have o₂ := ho true true
  cases h₀ : p false false <;> cases h₁ : p false true <;> cases h₂ : p true true <;>
    simp_all

/-- No allocated side can consist of just one use of an exposed root.
Unused leaves and surplus leaves in allocated sides pay for these uses. -/
theorem private_or_single_leaf (singles pos exempt leaves slack uses : Nat)
    (allocation : leaves + exempt = singles + pos + slack)
    (exports : 2 * exempt ≤ uses + 2) (capacity : uses ≤ 2 * slack) :
    singles + pos ≤ leaves + 1 := by omega

/-- An eight-arc OR cofactor bounds all-positive sides. A second side with
one leaf also needs a source of the right sign. Both counts use the same forest. -/
theorem private_or_leaf_budget (singles pos exempt leaves slack cheap stemNeg sideNeg
    neg fees excess forks : Nat)
    (allocation : leaves + exempt = singles + pos + slack)
    (exports : 2 * exempt ≤ cheap + 2 * stemNeg + 2)
    (shortSides : 7 * cheap ≤ 8 * (slack + sideNeg))
    (nots : stemNeg + sideNeg ≤ neg)
    (secondSides : pos + forks ≤ exempt + 2 * slack + 3 * neg + 2 * fees + excess) :
    6 * singles + 7 * pos + forks ≤ 6 * leaves + 10 * neg + 2 * fees + excess + 7 := by omega

/-- Translate the leaf positions back to physical gates, with direct literals
charged in F and all other negations charged in the shared circuit budget. -/
theorem private_or_size_budget (N V F W J singles pos leaves a forks : Nat)
    (weights : V = F + W + J) (leafBound : leaves ≤ W + forks + 2 * F) (fanout : forks ≤ W)
    (oneRead : N ≤ singles + F) (firstOr : N ≤ pos + a + F)
    (forest : 6 * singles + 7 * pos + forks ≤ 6 * leaves + 10 * J + 2 * F + W + 7) :
    13 * N ≤ 12 * V + 15 * F + 7 * a + 7 := by omega

/-- At n >= 64 and s <= 2N the OR forest and the same-pair first-reader
bound together cover at least one thirtieth of the gap to a quarter. -/
theorem private_or_small_size_fraction (N n s V F delta a gap extra : Nat)
    (gateCount : V + N = s + 1) (literalCount : F + 2 = n + delta)
    (forest : 13 * N ≤ 12 * V + 15 * F + 7 * a + 7)
    (small : s ≤ 2 * N) (scale : 63 * n ≤ N)
    (quarter : 4 * gap ≤ 3 * N) (actual : 15 * delta + 7 * a ≤ 30 * extra) :
    gap ≤ 30 * extra := by omega

/-- A width of q+2 in the multi-arc OR test bounds the cheap leaf positions. -/
theorem variable_or_leaf_budget (q L P E M U stemNeg sideNeg J leaves F W forks : Nat)
    (allocation : leaves + E = L + P + M) (exports : 2*E ≤ U+2*stemNeg+2)
    (shortSides : (q+1)*U ≤ (q+2)*(M+sideNeg)) (nots : stemNeg+sideNeg ≤ J)
    (secondSides : P+forks ≤ E+2*M+3*J+2*F+W) :
    (5*q+6)*L + (6*q+6)*P + q*forks ≤
      (5*q+6)*leaves + (9*q+6)*J + 2*q*F + q*W + 6*q+6 := by
  have hAlloc := congrArg (q * ·) allocation
  have hExports := Nat.mul_le_mul_left q exports
  have hNots := Nat.mul_le_mul_left q nots
  have hSecond := Nat.mul_le_mul_left q secondSides
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_assoc] at *
  simp only [Nat.mul_left_comm q 2, Nat.mul_left_comm q 3] at *
  omega

/-- Convert the variable-width leaf bound to reader fees in the physical circuit. -/
theorem variable_or_size_budget (q N V F W J L P leaves a forks : Nat)
    (weights : V = F+W+J) (capacity : leaves ≤ W+forks+2*F) (fanout : forks ≤ W)
    (oneRead : N ≤ L+F) (firstOr : N ≤ P+a+F)
    (forest : (5*q+6)*L + (6*q+6)*P + q*forks ≤
      (5*q+6)*leaves + (9*q+6)*J + 2*q*F + q*W + 6*q+6) :
    (11*q+12)*N ≤ (10*q+12)*V + (13*q+12)*F + (6*q+6)*a + 6*q+6 := by
  have hV := congrArg (q * ·) weights
  have hCapacity := Nat.mul_le_mul_left q capacity
  have hFanout := Nat.mul_le_mul_left q fanout
  have hOne := Nat.mul_le_mul_left q oneRead
  have hOr := Nat.mul_le_mul_left q firstOr
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
  simp only [Nat.mul_left_comm q 2] at *
  omega

/-- A single expectation exceeding x and (x+y)/2 pays any combination with
at least as much weight on x as on y. All terms can be scaled to integers. -/
theorem blend_reader_estimates (w b x y z : Nat) (first : x ≤ z) (both : x+y ≤ 2*z) :
    (w+b)*x + b*y ≤ (w+2*b)*z := by
  have hFirst := Nat.mul_le_mul_left w first
  have hBoth := Nat.mul_le_mul_left b both
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm b 2] at *
  omega

/-- For m >= 242 the finite integer loss pays one twentieth of the old gap.
Here extra is the actual loss above 3m², and the old baseline is 3m²+m-2. -/
theorem variable_or_twentieth (m extra gap : Nat) (scale : 242 ≤ m)
    (target : gap+4*m ≤ 3*(m*m)+2) (actual : 3*(m*m) ≤ 19*extra+21*m) :
    gap+20*m ≤ 20*extra+40 := by
  have hm : 724 ≤ 3*m := by omega
  have h := Nat.mul_le_mul_left m hm
  rw [Nat.mul_left_comm m 3] at h
  omega

/-- Comparing actual deletions with the smaller decision circuit gives a
recurrence in the two optimum sizes. -/
theorem paired_zero_size_step (N n s small a loss : Nat)
    (heads : 10 * N ≤ a + 6 * s + 4 * n + 13)
    (readers : 3 * N + 3 * a ≤ 4 * loss + 4 * n + 8)
    (correct : small + loss ≤ s) :
    33 * N + 4 * small ≤ 22 * s + 16 * n + 47 := by omega

/-- A size certificate for the finite quarter, with the very same gate loss. -/
theorem paired_zero_quarter (N n s a loss : Nat)
    (heads : 10 * N ≤ a + 6 * s + 4 * n + 13)
    (readers : 3 * N + 3 * a ≤ 4 * loss + 4 * n + 8)
    (size : 21 * s + 16 * n + 47 ≤ 33 * N) : 3 * s ≤ 4 * loss := by omega

/-- The induction hypothesis at m implies the sharper even-size estimate at 2m. -/
theorem paired_zero_even_density (N n smallN m s small : Nat)
    (double : n = 2 * m) (arcs : N = 4 * smallN + n)
    (step : 33 * N + 4 * small ≤ 22 * s + 16 * n + 47)
    (ih : 11 * smallN ≤ 7 * small + 21 * m + 28) :
    22 * N ≤ 14 * s + 21 * n + 42 := by omega

/-- Splitting one vertex gives the required odd-size induction step. -/
theorem paired_zero_odd_density (N n s nextSize : Nat)
    (evenBound : 22 * N ≤ 14 * s + 21 * n + 42)
    (split : s + 2 * n ≤ nextSize) :
    11 * (N + 2 * n) ≤ 7 * nextSize + 21 * (n+1) + 28 := by omega

/-- Induct all the way down to the small orders. N denotes the number of
loopless input arcs. The structural circuit results supply the two size steps. -/
theorem paired_zero_density (N s : Nat → Nat)
    (base : ∀ n, 2 ≤ n → n ≤ 7 → 11 * N n ≤ 7 * s n + 21 * n + 28)
    (doubleArcs : ∀ m, 4 ≤ m → N (2*m) = 4 * N m + 2*m)
    (nextArcs : ∀ k, 8 ≤ k → N (k+1) = N k + 2*k)
    (evenStep : ∀ m, 4 ≤ m → 33 * N (2*m) + 4 * s m ≤ 22 * s (2*m) + 16 * (2*m) + 47)
    (split : ∀ k, 8 ≤ k → s k + 2*k ≤ s (k+1)) :
    ∀ n, 2 ≤ n → 11 * N n ≤ 7 * s n + 21 * n + 28 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases small : n ≤ 7
    · exact base n hn small
    · let m := n / 2
      have hm : 4 ≤ m := by dsimp [m]; omega
      have prev := ih m (by dsimp [m]; omega) (by omega)
      have evenBound := paired_zero_even_density _ _ _ _ _ _ rfl (doubleArcs m hm) (evenStep m hm) prev
      have parity : n = 2*m ∨ n = 2*m+1 := by dsimp [m]; omega
      rcases parity with h | h
      · rw [h]
        omega
      · rw [h, nextArcs _ (by omega)]
        exact paired_zero_odd_density _ _ _ _ evenBound (split _ (by omega))

/-- In a permutation of equally many entries and exits, the two kinds of
same-side arc have the same count. True denotes an entry. -/
theorem same_side_balance (arcs : List (Bool × Bool))
    (balanced : arcs.countP (fun e => e.1) = arcs.countP (fun e => !e.2)) :
    arcs.countP (fun e => e.1 && e.2) = arcs.countP (fun e => !e.1 && !e.2) := by
  have ledger (a : List (Bool × Bool)) :
      a.countP (fun e => e.1 && e.2) + a.countP (fun e => !e.2) =
      a.countP (fun e => !e.1 && !e.2) + a.countP (fun e => e.1) := by
    induction a with
    | nil => rfl
    | cons edge tail ih =>
      obtain ⟨u,v⟩ := edge
      cases u <;> cases v <;> simp at * <;> omega
  have h := ledger arcs
  omega

/-- Clear the denominators in the flexible-pin expectation. The two coefficient
comparisons account for the signed fee term and the missing entry-side heads. -/
theorem flexible_reader_comparison (N n loss t u flex F a : Nat) (pos : 0 < N)
    (cost : N*N+u*F+flex*a ≤ N*loss+t*F+N)
    (fee : 4*t ≤ 4*u+N) (heads : N=2*flex+2*(n+1)) (count : a ≤ N) :
    4*N+2*a ≤ 4*loss+F+4*n+8 := by
  have hFee := Nat.mul_le_mul_right F fee
  have hHeads := congrArg (· * a) heads
  have hCount := Nat.mul_le_mul_left (4*(n+1)) count
  have priced : N*(4*N+2*a) ≤ N*(4*loss+F+4*n+8) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one] at *
    simp only [Nat.mul_left_comm N 4, Nat.mul_left_comm N 2, Nat.mul_comm n N] at *
    omega
  exact Nat.le_of_mul_le_mul_left priced pos

theorem flexible_fee_capacity (n : Nat) (scale : 8 ≤ n) :
    2*(n*(n-1)+1) ≤ (n-2)*(2*n+3) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le scale
  have left : 8+k-1 = 7+k := by omega
  have right : 8+k-2 = 6+k := by omega
  rw [left, right]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_left_comm k 2]
  omega

/-- Remove the denominator n-2 from the first forest inequality. The
capacity hypothesis is 2(N+1) <= (n-2)(2n+3), valid from n=8. -/
theorem flexible_fee_bound (d N n s F : Nat) (pos : 0 < d)
    (weight : F+N ≤ s+1) (forest : d*(F+3*N) ≤ d*(2*s+2)+2*F)
    (capacity : 2*(N+1) ≤ d*(2*n+3)) : F+3*N ≤ 2*s+2*n+5 := by
  by_cases h : s ≤ 2*N
  · have hF : 2*F ≤ d*(2*n+3) := by omega
    have hsum : d*(F+3*N) ≤ d*(2*s+2)+d*(2*n+3) := by omega
    rw [← Nat.mul_add] at hsum
    have h' := Nat.le_of_mul_le_mul_left hsum pos
    omega
  · omega

/-- The first-reader loss here is for an alternative restriction representing
the same smaller function. It need not be the zero-filled pairing. -/
theorem flexible_size_step (N n s small F a loss : Nat)
    (fees : F+3*N ≤ 2*s+2*n+5) (forest : 4*N ≤ 2*s+2*F+a+3)
    (readers : 4*N+2*a ≤ 4*loss+F+4*n+8) (correct : small+loss ≤ s) :
    27*N+4*small ≤ 18*s+14*n+39 := by omega

/-- A finite budget for the excess of a physical residual over the small optimum. -/
theorem flexible_quarter_room (N smallN n m s small room : Nat) (double : n=2*m)
    (arcs : N=4*smallN+n) (step : 27*N+4*small ≤ 18*s+14*n+39)
    (price : 68*small+72*room+39 ≤ 108*smallN+26*m) : 4*(small+room) ≤ s := by omega

/-- The sharper even estimate supplies the following odd size via one split. -/
theorem flexible_even_density (N smallN n m s small : Nat)
    (double : n=2*m) (arcs : N=4*smallN+n)
    (step : 27*N+4*small ≤ 18*s+14*n+39)
    (ih : 27*smallN ≤ 17*small+51*m+85) : 54*N ≤ 34*s+51*n+136 := by omega

theorem flexible_odd_density (N nextN n s next : Nat) (arcs : nextN=N+2*n)
    (even : 54*N ≤ 34*s+51*n+136) (split : s+2*n ≤ next) :
    27*nextN ≤ 17*next+51*(n+1)+85 := by omega

/-- Strong induction needs only the even-size comparison, the single-vertex
split and the base cases. The bound is in raw directed arc bits. -/
theorem flexible_density (N s : Nat → Nat)
    (base : ∀ n, 2 ≤ n → n ≤ 7 → 27*N n ≤ 17*s n+51*n+85)
    (doubleArcs : ∀ m, 4 ≤ m → N (2*m)=4*N m+2*m)
    (nextArcs : ∀ k, 8 ≤ k → N (k+1)=N k+2*k)
    (evenStep : ∀ m, 4 ≤ m → 27*N (2*m)+4*s m ≤ 18*s (2*m)+14*(2*m)+39)
    (split : ∀ k, 8 ≤ k → s k+2*k ≤ s (k+1)) :
    ∀ n, 2 ≤ n → 27*N n ≤ 17*s n+51*n+85 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases small : n ≤ 7
    · exact base n hn small
    · let m := n/2
      have hm : 4 ≤ m := by dsimp [m]; omega
      have prev := ih m (by dsimp [m]; omega) (by omega)
      have even := flexible_even_density _ _ _ _ _ _ rfl (doubleArcs m hm) (evenStep m hm) prev
      have parity : n=2*m ∨ n=2*m+1 := by dsimp [m]; omega
      rcases parity with h | h
      · rw [h]
        omega
      · rw [h]
        exact flexible_odd_density _ _ _ _ _ (nextArcs _ (by omega)) even (split _ (by omega))

/-- Marking just the flexible side gives a scale difference independent of the
small optimum. Strictness of m*N < 2*w*F accounts for the integer rounding. -/
theorem flexible_absolute_gap (N m loss w F : Nat)
    (ledger : N*N+w*F ≤ N*(loss+1)) (strictFee : m*N < 2*(w*F)) :
    N+m/2 ≤ loss := by
  have clear : N*(2*N+m) < N*(2*loss+2) := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm N 2, Nat.mul_comm N m] at *
    omega
  have step := Nat.lt_of_mul_lt_mul_left clear
  omega

/-- Specialize the density induction to the actual loopless arc count and
discharge the small orders using only essentiality of the raw inputs. -/
theorem flexible_arc_density (s : Nat → Nat)
    (raw : ∀ n, 2 ≤ n → n*(n-1) ≤ s n+1)
    (evenStep : ∀ m, 4 ≤ m →
      27*((2*m)*(2*m-1))+4*s m ≤ 18*s (2*m)+14*(2*m)+39)
    (split : ∀ k, 8 ≤ k → s k+2*k ≤ s (k+1)) :
    ∀ n, 2 ≤ n → 27*(n*(n-1)) ≤ 17*s n+51*n+85 := by
  apply flexible_density (fun n => n*(n-1)) s
  · intro n hn h7
    have essential := raw n hn
    have cases : n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 := by omega
    rcases cases with h | h | h | h | h | h <;> subst n <;> omega
  · intro m hm
    have h : 2*m-1 = 2*(m-1)+1 := by omega
    simp only [h, Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm m 2]
    omega
  · intro k hk
    have h : k+1-1 = k := by omega
    have hk' : k = (k-1)+1 := by omega
    change (k+1)*(k+1-1) = k*(k-1)+2*k
    rw [h, Nat.add_mul, Nat.one_mul]
    have expansion := congrArg (k * ·) hk'
    simp only [Nat.mul_add, Nat.mul_one] at expansion
    omega
  · exact evenStep
  · exact split

/-- With the fixed-partner promise priced at small + 3*arcs, characterize
the cost of full-graph correctness needed to pay for a given residue. -/
theorem fixed_partner_quarter (full small arcs outside residualExtra : Nat)
    (price : full = small + 3*arcs + outside) :
    4*(small + residualExtra) ≤ full ↔
      3*small + 4*residualExtra ≤ outside + 3*arcs := by omega

/-- Cutting a shared computation of the grouped adjacencies and a small
optimal core suffices under the stated full-graph gate budget. -/
theorem quotient_core_quarter (full small bigArcs smallArcs cut dead ports : Nat)
    (ledger : cut + dead + ports + bigArcs + small ≤ full + smallArcs)
    (core : smallArcs + small ≤ cut) (cost : 2*small ≤ bigArcs) :
    4*small ≤ full := by omega

/-- Count an original representative once across four runs, then add its
repeated uses. The three-unit allowance accounts for rounding each quarter. -/
theorem four_residues_quarter (full unused repeated extra a b c d : Nat)
    (ledger : a+b+c+d+unused+extra = full+repeated)
    (budget : repeated + full%4 ≤ unused+extra+3) :
    a ≤ full/4 ∨ b ≤ full/4 ∨ c ≤ full/4 ∨ d ≤ full/4 := by omega

/-- Count the boundary once even when a removed signal has many outside readers. -/
theorem constant_cut_third (g ports hidden incoming unary rawRepeat gateRepeat singles credit : Nat)
    (cut : g + ports = hidden + credit)
    (wires : credit = incoming + unary + rawRepeat + gateRepeat)
    (first : hidden ≤ singles + rawRepeat + unary)
    (sides : singles ≤ incoming + 2*gateRepeat + rawRepeat) :
    g + ports + incoming + unary ≤ 3*credit := by omega

/-- When inputs on either side can be recovered with the other side fixed,
the same port count bounds both sets of hidden raw inputs. -/
theorem internal_cut_half (g ports left right credit : Nat)
    (cut : g + ports = left + right + credit)
    (readers : left + right ≤ g) (recoverLeft : left ≤ ports) (recoverRight : right ≤ ports) :
    g ≤ 2*credit := by omega

/-- Each boundary bit has at most k+1 views across the two directions in
total. Combine recoverability with the shared forest bound. -/
theorem constant_cut_views (k g ports hidden credit : Nat)
    (cut : g + ports = hidden + credit) (recover : hidden ≤ (k+1)*ports)
    (forest : g+ports ≤ 3*credit) : (k+1)*g ≤ (3*k+1)*credit := by
  have scaled := Nat.mul_le_mul_left k forest
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm k 3] at *
  omega

/-- Recovering every addressed bit from the same word bounds the width of
that word, even when different addresses use different decoding functions. -/
theorem probe_word_width {n w : Nat} (encode : BitVec n → BitVec w)
    (decode : BitVec w → Fin n → Bool)
    (reads : ∀ x i, decode (encode x) i = x.getLsbD i.val) : n ≤ w := by
  have cap : 2^n ≤ 2^w := by
    apply Bounded.fin_size_le (fun v : Fin (2^n) => (encode (.ofFin v)).toFin)
    intro a b eq
    have same : encode (.ofFin a) = encode (.ofFin b) := by
      simpa using congrArg BitVec.ofFin eq
    apply congrArg BitVec.toFin
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    exact (reads (.ofFin a) ⟨i,hi⟩).symm.trans
      ((congrArg (fun z => decode z ⟨i,hi⟩) same).trans (reads (.ofFin b) ⟨i,hi⟩))
  exact Nat.le_of_not_lt fun h => Nat.not_lt_of_ge cap (Nat.pow_lt_pow_right (by decide : 1<2) h)

/-- If a quarter is reached, what the second stage pays beyond its raw
fixed inputs follows from the alternating circuit lower bound. -/
theorem alternating_stage_gap (s rows square interim residue extra : Nat)
    (forest : 6*square + rows ≤ 2*interim + 5)
    (second : interim = residue + square + rows + extra)
    (quarter : residue ≤ s/4) :
    4*square ≤ 2*(s/4) + 2*extra + rows + 5 := by omega

/-- Opposite-matrix raw inputs lost at the cut are charged separately.
Only the return entries can be lost under the standard matching. -/
theorem alternating_mixed_cut (area rest g ports forward backward credit : Nat)
    (cut : g+ports = forward+backward+credit)
    (capacity : area*forward ≤ (area+rest)*ports)
    (forest : g+ports ≤ 3*credit) :
    (area+rest)*g ≤ (area+3*rest)*credit + area*backward := by
  have scaledCut := congrArg (area * ·) cut
  have scaledForest := Nat.mul_le_mul_left rest forest
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm rest 3] at *
  omega

/-- A relabelled address rectangle sees area out of area+rest entries.
A cut depending only on the forward matrix loses no backward raw inputs. -/
theorem alternating_matrix_cut (area rest g ports hidden credit : Nat)
    (cut : g+ports = hidden+credit) (capacity : area*hidden ≤ (area+rest)*ports)
    (forest : g+ports ≤ 3*credit) : (area+rest)*g ≤ (area+3*rest)*credit := by
  simpa using alternating_mixed_cut area rest g ports hidden 0 credit (by simpa using cut) capacity forest

/-- An exceptional connected component can discard one ticket beyond its
gate count only if it contains at least k tickets. Sum over the actual DAG. -/
theorem pruned_component_tickets (k : Nat) (blocks : List (Nat × Nat))
    (bounds : ∀ p ∈ blocks, p.2 ≤ p.1+1 ∧ (p.1 < p.2 → k ≤ p.2)) :
    k * (blocks.map Prod.snd).sum ≤ k * (blocks.map Prod.fst).sum + (blocks.map Prod.snd).sum := by
  induction blocks with
  | nil => simp
  | cons p ps ih =>
    have h := bounds p (by simp)
    have part : k*p.2 ≤ k*p.1 + p.2 := by
      by_cases same : p.2 ≤ p.1
      · have h' := Nat.mul_le_mul_left k same
        omega
      · have h' : p.2 = p.1+1 := by omega
        have deep := h.2 (by omega)
        rw [h', Nat.mul_add, Nat.mul_one]
        omega
    have tail := ih (fun x hx => bounds x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- The common finite recurrence for the full-to-alternating stage and
the alternating-to-small stage; square is the number of matrix cells. -/
theorem two_stage_size_recurrence (full alt small N square m : Nat)
    (raw : N+2*m = 4*square)
    (first : 5*N+2*alt ≤ 4*full+12*m+22)
    (second : 10*square+2*small ≤ 4*alt+12*m+22) :
    25*N+4*small ≤ 16*full+62*m+132 := by omega

theorem matrix_stage_size (M s next a fees m : Nat)
    (sparse : 3*M+a+fees ≤ 4*(s-next)+20*m+32)
    (forest : 7*M ≤ 4*s+a+fees+4*m+11) (mono : next ≤ s) :
    5*M+2*next ≤ 4*s+12*m+22 := by omega

theorem ordered_arc_density (s : Nat → Nat)
    (raw : ∀ n, 2 ≤ n → n*(n-1) ≤ s n+1)
    (halve : ∀ m, 4 ≤ m →
      25*((2*m)*(2*m-1))+4*s m ≤ 16*s (2*m)+62*m+132)
    (split : ∀ n, 8 ≤ n → s n+2*n ≤ s (n+1)) :
    ∀ n, 2 ≤ n → 5*(n*(n-1)) ≤ 3*s n+12*n+36 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hsmall : n ≤ 7
    · have h := raw n hn
      have cases : n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 := by omega
      rcases cases with h | h | h | h | h | h <;> subst n <;> omega
    · let m := n/2
      have hm : 4 ≤ m := by dsimp [m]; omega
      have prev := ih m (by dsimp [m]; omega) (by omega)
      have stepEven := halve m hm
      have arms : 2*m-1 = 2*(m-1)+1 := by omega
      have doubleArcs : (2*m)*(2*m-1) = 4*(m*(m-1))+2*m := by
        rw [arms]
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm m 2]
        omega

      have even : 5*((2*m)*(2*m-1)) ≤ 3*s (2*m)+8*(2*m)+36 := by omega
      have cases : n=2*m ∨ n=2*m+1 := by dsimp [m]; omega
      rcases cases with h | h
      · rw [h]
        omega
      · rw [h]
        have step := split (2*m) (by omega)
        have succArcs : (2*m+1)*(2*m+1-1) = (2*m)*(2*m-1)+2*(2*m) := by
          have sub : 2*m+1-1 = 2*m := by omega
          have add : 2*m = (2*m-1)+1 := by omega
          rw [sub, Nat.add_mul, Nat.one_mul]
          have expand := congrArg ((2*m) * ·) add
          simp only [Nat.mul_add, Nat.mul_one] at expand
          omega
        omega

/-- A period of a monotone decision makes every bit in its support
irrelevant. The low and high corners of each fibre have the same answer. -/
theorem monotone_period_fibre (f : (ι → Bool) → Bool) (mask : ι → Bool)
    (mono : ∀ a b : ι → Bool, (∀ i, a i=true → b i=true) → f a=true → f b=true)
    (period : ∀ a, f (fun i => a i ^^ mask i) = f a)
    (x y : ι → Bool) (agree : ∀ i, mask i=false → x i=y i) : f x = f y := by
  let lo := fun i => x i && !mask i
  let hi := fun i => x i || mask i
  have toggled : (fun i => lo i ^^ mask i) = hi := by
    funext i
    cases hx : x i <;> cases hm : mask i <;> simp [lo, hi, hx, hm]
  have eq := period lo
  rw [toggled] at eq
  have middle (z : ι → Bool) (hz : ∀ i, mask i=false → x i=z i) : f lo = f z := by
    have low : ∀ i, lo i=true → z i=true := by
      intro i h
      cases hm : mask i with
      | false => simpa [lo, hm, hz i hm] using h
      | true => simp [lo, hm] at h
    have high : ∀ i, z i=true → hi i=true := by
      intro i h
      cases hm : mask i with
      | false => simp [hi, hm, hz i hm, h]
      | true => simp [hi, hm]
    apply Bool.eq_iff_iff.mpr
    exact ⟨mono lo z low, fun h => eq ▸ mono z hi high h⟩
  exact (middle x (fun _ _ => rfl)).symm.trans (middle y agree)

/-- A two-way protocol across the physical cut includes its incoming
positions. Keep both directions when combining communication and forest size. -/
theorem separated_port_credit (mass hit g ports hidden incoming credit : Nat)
    (cut : g+ports = hidden+credit)
    (communication : hit*hidden ≤ mass*(ports+incoming))
    (forest : g+ports+incoming ≤ 3*credit) :
    (mass+hit)*g+hit*ports ≤ (3*mass+hit)*credit := by
  have scaled := Nat.mul_le_mul_left mass forest
  have same := congrArg (hit * ·) cut
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm mass 3] at *
  omega

/-- Integer endpoint of the uniform one-fourteenth bound. -/
theorem component_fourteenth (m extra gap : Nat) (scale : 123 ≤ m)
    (need : gap+4*m ≤ 3*(m*m)+2)
    (credit : 3*(m*m)+24 ≤ 13*extra+30*m) : gap ≤ 14*extra := by
  have scale' : 368 ≤ 3*m := by omega
  have quad := Nat.mul_le_mul_left m scale'
  rw [Nat.mul_left_comm m 3] at quad
  omega

/-- Two ways to complete a prescribed forward arc. The return arcs either
avoid both endpoints at once or reach the two endpoints separately. -/
theorem return_arc_witness (X : β → α → Prop) (j : β) (i : α) :
    ((∃ l k, X l k ∧ l ≠ j ∧ k ≠ i) ∨
      ((∃ l, X l i ∧ l ≠ j) ∧ (∃ k, X j k ∧ k ≠ i))) ↔
      ((∃ l k, X l k ∧ l ≠ j) ∧ (∃ l k, X l k ∧ k ≠ i)) := by
  constructor
  · rintro (⟨l,k,h,hl,hk⟩ | ⟨⟨l,h,hl⟩,⟨k,h',hk⟩⟩)
    · exact ⟨⟨l,k,h,hl⟩, ⟨l,k,h,hk⟩⟩
    · exact ⟨⟨l,i,h,hl⟩, ⟨j,k,h',hk⟩⟩
  · rintro ⟨⟨l,k,h,hl⟩,⟨l',k',h',hk'⟩⟩
    by_cases hk : k = i
    · by_cases hl' : l' = j
      · exact Or.inr ⟨⟨l,hk ▸ h,hl⟩, ⟨k',hl' ▸ h',hk'⟩⟩
      · exact Or.inl ⟨l',k',h',hl',hk'⟩
    · exact Or.inl ⟨l,k,h,hl,hk⟩

/-- Every off-row, off-column cell is simultaneously sensitive at an
absorbing assignment for a guard satisfying the tour witness condition. -/
theorem opposite_guard_sensitive [DecidableEq α] [DecidableEq β]
    (guard : (β → α → Bool) → Bool) (neutral : Bool) (j : β) (i : α)
    (witness : ∀ X l k, l ≠ j → k ≠ i → X l k = true → guard X = neutral)
    (X : β → α → Bool) (absorbs : guard X ≠ neutral)
    (l : β) (k : α) (hl : l ≠ j) (hk : k ≠ i) :
    X l k = false ∧
    guard (fun u v => if u = l ∧ v = k then true else X u v) = neutral := by
  constructor
  · cases hv : X l k with
    | false => rfl
    | true => exact False.elim (absorbs (witness X l k hl hk hv))
  · exact witness _ l k hl hk (by simp)

/-- All nonzero patterns of the pool give the same port value. They can
be replaced by a single designated bit, at either output polarity. -/
theorem pool_at_representative [DecidableEq ι] (f : (ι → Bool) → β → γ)
    (rep : ι) (on : β → γ)
    (forced : ∀ x z i, x i = true → f x z = on z) (x : ι → Bool) (z : β)
    (anyBit : Bool) (correct : anyBit = true ↔ ∃ i, x i = true) :
    f x z = f (fun i => if i = rep then anyBit else false) z := by
  cases ha : anyBit with
  | false =>
    have off (i : ι) : x i = false := by
      cases hx : x i with
      | false => rfl
      | true => have := correct.mpr ⟨i,hx⟩; simp_all
    have eq : x = fun i => if i = rep then false else false := by
      funext i
      simp [off]
    exact congrArg (fun v => f v z) eq
  | true =>
    obtain ⟨i,hi⟩ := correct.mp ha
    exact (forced x z i hi).trans
      (forced (fun j => if j = rep then true else false) z rep (by simp)).symm

/-- The whole-graph INDEX probes pay for the hidden reverse inputs.
Every hidden item outside that matrix, and each missed address, is debited once. -/
theorem full_index_cut_credit (pins gates ports reverse other missed loss : Nat)
    (replay : pins+gates+ports ≤ loss+reverse+other)
    (address : reverse ≤ ports+missed) : pins+gates ≤ loss+other+missed := by omega

/-- Removing a private OR tree at the same time as first readers loses
at most one unit relative to the number of its free inputs. -/
theorem pruned_pool_credit (q fixed free tree reads : Nat)
    (partition : q = fixed+free) (size : q=tree+1) (paid : reads ≤ fixed) :
    free+reads ≤ tree+1 := by omega

/-- A connected component with p vertices and k signed pins uses at
most k contractions, including one auxiliary vertex per forbidden adjacency. -/
theorem pin_block_budget (p k detours : Nat) (vertices : 2 ≤ p)
    (connected : p ≤ k+1) (average : p*detours ≤ k) : p-1+detours ≤ k := by
  cases detours with
  | zero => omega
  | succ d =>
    have h := Nat.mul_le_mul_right d (show 1 ≤ p by omega)
    simp only [Nat.one_mul] at h
    rw [Nat.mul_succ] at average
    omega

/-- Each successful one-pair quarter step multiplies the size by four.
Steps on which the condition is unavailable still preserve monotonicity. -/
theorem quarter_jump_product (s : Nat → Nat) (jump : Nat → Bool)
    (mono : ∀ i, s i ≤ s (i+1)) (step : ∀ i, jump i = true → 4*s i ≤ s (i+1)) :
    ∀ m, 4^((List.range m).filter jump).length * s 0 ≤ s m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append]
    cases h : jump m with
    | false => simpa [h] using Nat.le_trans ih (mono m)
    | true =>
      have t := Nat.le_trans (Nat.mul_le_mul_left 4 ih) (step m h)
      simpa [h, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using t

end Mobius.PairContraction
