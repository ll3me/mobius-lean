/-! The residual Hall bound with universal hubs, and the cost of expanding
    an adaptive transcript of individual bit and positive conjunction tests. -/
namespace Mobius.CycleCoverQueries

def neighbors (vs : List V) (edge : V → V → Bool) (side : V → Bool) (v : V) :=
  vs.any fun u => side u && edge u v

private theorem count_add_le (vs : List V) (a b c d : V → Bool)
    (h : ∀ v ∈ vs, (a v).toNat + (b v).toNat ≤ (c v).toNat + (d v).toNat) :
    vs.countP a + vs.countP b ≤ vs.countP c + vs.countP d := by
  induction vs with
  | nil => simp
  | cons v rest ih =>
    have head := h v (by simp)
    have tail := ih (fun u hu => h u (by simp [hu]))
    simp only [List.countP_cons]
    cases ha : a v <;> cases hb : b v <;> cases hc : c v <;> cases hd : d v <;>
      simp [ha, hb, hc, hd] at head ⊢ <;> omega

/-- With a loop at every vertex and all arcs to/from each hub, every set
of remaining rows has enough neighbors after deleting the occupied heads.
The remaining parts have equal size after prescribing a partial matching. -/
theorem residual_hall (vs : List V) (edge : V → V → Bool) (hub side removed : V → Bool)
    (loops : ∀ u ∈ vs, edge u u = true)
    (outgoing : ∀ u ∈ vs, hub u = true → ∀ v ∈ vs, edge u v = true)
    (incoming : ∀ v ∈ vs, hub v = true → ∀ u ∈ vs, edge u v = true)
    (quota : vs.countP removed ≤ vs.countP hub)
    (fits : vs.countP side ≤ vs.countP (fun v => !removed v)) :
    vs.countP side ≤ vs.countP (fun v => neighbors vs edge side v && !removed v) := by
  by_cases hit : ∃ h ∈ vs, side h = true ∧ hub h = true
  · obtain ⟨h, hh, hs, hu⟩ := hit
    apply Nat.le_trans fits
    apply List.countP_mono_left
    intro v hv free
    have vn : neighbors vs edge side v = true :=
      List.any_eq_true.mpr ⟨h, hh, by simp [hs, outgoing h hh hu v hv]⟩
    simp [vn, free]
  by_cases nonempty : ∃ u ∈ vs, side u = true
  · obtain ⟨w, hw, sw⟩ := nonempty
    have bound := count_add_le vs side hub
      (fun v => neighbors vs edge side v && !removed v) removed (by
        intro v hv
        by_cases sv : side v = true
        · have nh : hub v = false := Bool.eq_false_iff.mpr fun yes => hit ⟨v, hv, sv, yes⟩
          have vn : neighbors vs edge side v = true :=
            List.any_eq_true.mpr ⟨v, hv, by simp [sv, loops v hv]⟩
          cases removed v <;> simp [sv, nh, vn]
        · by_cases hu : hub v = true
          · have vn : neighbors vs edge side v = true :=
              List.any_eq_true.mpr ⟨w, hw, by simp [sw, incoming v hv hu w hw]⟩
            cases removed v <;> simp [sv, hu, vn]
          · simp_all)
    omega
  · have z : vs.countP side = 0 := by
      apply Nat.eq_zero_of_not_pos
      exact fun h => nonempty (List.countP_pos_iff.mp h)
    simp [z]

def pinOnes [DecidableEq V] (test : List V) (x : V → Bool) (v : V) : Bool :=
  if v ∈ test then true else x v

private theorem pin_agrees [DecidableEq V] {test : List V} {x : V → Bool}
    (h : test.all x = true) : pinOnes test x = x := by
  funext v
  by_cases hv : v ∈ test
  · simp [pinOnes, hv, List.all_eq_true.mp h v hv]
  · simp [pinOnes, hv]

/-- A negative conjunction has two terms, irrespective of its arity. -/
def expand [DecidableEq V] (p : (V → Bool) → Int) : List (List V) → (V → Bool) → Int
  | [], x => p x
  | test :: ts, x => expand p ts x - (test.all x).toNat * expand p ts (pinOnes test x)

theorem expand_correct [DecidableEq V] (p : (V → Bool) → Int) (ts : List (List V)) (x : V → Bool) :
    expand p ts x = if ts.all (fun test => !(test.all x)) then p x else 0 := by
  induction ts with
  | nil => simp [expand]
  | cons test ts ih =>
    cases h : test.all x with
    | false => simp [expand, h, ih]
    | true => simp [expand, h, pin_agrees h]

inductive Transcript where
  | leaf (cost : Nat)
  | bit (no yes : Transcript)
  | joint (no yes : Transcript)

def expanded : Transcript → Nat
  | .leaf w => w
  | .bit a b => expanded a + expanded b
  | .joint a b => 2 * expanded a + expanded b

def peak : Transcript → Nat
  | .leaf w => w
  | .bit a b => 2 * max (peak a) (peak b)
  | .joint a b => 3 * max (peak a) (peak b)

/-- The peak is the maximum of 2^q 3^s times the leaf cost on one path.
Impossible transcripts may be supplied with leaf cost zero. -/
theorem expanded_le_peak (t : Transcript) : expanded t ≤ peak t := by
  induction t with
  | leaf w => exact Nat.le_refl _
  | bit a b ha hb =>
    simp only [expanded, peak]
    have := Nat.le_max_left (peak a) (peak b)
    have := Nat.le_max_right (peak a) (peak b)
    omega
  | joint a b ha hb =>
    simp only [expanded, peak]
    have := Nat.le_max_left (peak a) (peak b)
    have := Nat.le_max_right (peak a) (peak b)
    omega

end Mobius.CycleCoverQueries
