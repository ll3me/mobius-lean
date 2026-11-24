/-! Local steps used in the matching boundary lower bound. An accepting
    trace retains one input of an OR and both inputs of an AND. Node IDs
    may be reused. The ambient finite DAG is counted in the written proof. -/
namespace Mobius.HybridMatching

def one (a b c : Bool) := a.toNat + b.toNat + c.toNat = 1

theorem six_pin_cancels (a b c : Bool) (h : one a b c) :
    ((!a) ^^ (!b) ^^ (!c)) = false := by
  unfold one at h
  revert a b c; decide

theorem vertex_ports (a b c : Bool) :
    (∃ d p q : Bool, one a b p ∧ one c d q ∧ one p q false) ↔
      a.toNat + b.toNat + c.toNat ≤ 1 := by
  unfold one; revert a b c; decide

/-- An affine projection onto conflicting bits misses one legal local
    pattern: the xor of the three legal patterns is the forbidden one. -/
theorem affine_pair (holds : Bool → Bool → Prop)
    (closed : ∀ a b c d e f, holds a b → holds c d → holds e f →
      holds (a ^^ c ^^ e) (b ^^ d ^^ f))
    (legal : ¬ holds true true) :
    ¬ (holds false false ∧ holds true false ∧ holds false true) := by
  rintro ⟨zero, left, right⟩
  exact legal (closed _ _ _ _ _ _ zero left right)

inductive Trace (I : Type) where
  | leaf (gate : I)
  | pick (gate : I) (chosen : Trace I)
  | join (gate : I) (left right : Trace I)

def Trace.root : Trace I → I
  | .leaf g | .pick g _ | .join g _ _ => g

/-- Sibling obligations on a route to a selected occurrence. -/
inductive Route : Trace I → Trace I → List I → Prop where
  | here (t) : Route t t []
  | pick (g) : Route t v hs → Route (.pick g t) v hs
  | left (g r) : Route l v hs → Route (.join g l r) v (r.root :: hs)
  | right (g l) : Route r v hs → Route (.join g l r) v (l.root :: hs)

def Trace.rules (value : I → X → Prop) : Trace I → Prop
  | .leaf _ => True
  | .pick g t => (∀ x, value t.root x → value g x) ∧ t.rules value
  | .join g l r => (∀ x, value l.root x → value r.root x → value g x) ∧
      l.rules value ∧ r.rules value

theorem route_sound (value : I → X → Prop) (path : Route t v hs) (rules : t.rules value)
    (inside : value v.root x) (outside : ∀ h ∈ hs, value h x) : value t.root x := by
  induction path with
  | here => exact inside
  | pick g _ ih => exact rules.1 x (ih rules.2 inside outside)
  | left g r _ ih =>
    exact rules.1 x (ih rules.2.1 inside (fun h m => outside h (by simp [m])))
      (outside r.root (by simp))
  | right g l _ ih =>
    exact rules.1 x (outside l.root (by simp))
      (ih rules.2.2 inside (fun h m => outside h (by simp [m])))

/-- For one gate and interface value, union all qualifying outside
    witnesses. The route and its sibling certificates may depend on b.
    The inside assignment a can then be replaced throughout its leg. -/
theorem grouped_rectangle (value : I → A × B → Prop) (output gate : I)
    (inside agrees : A → Prop) (outside : B → Prop)
    (atGate : ∀ a b, inside a → value gate (a,b))
    (witness : ∀ b, outside b → ∃ t v hs, t.root = output ∧ v.root = gate ∧
      Route t v hs ∧ t.rules value ∧ ∀ a, agrees a → ∀ h ∈ hs, value h (a,b))
    (hi : inside a) (ha : agrees a) (hb : outside b) : value output (a,b) := by
  obtain ⟨t, v, hs, hout, hg, path, rules, accepted⟩ := witness b hb
  rw [← hout]
  apply route_sound value path rules _ (accepted a ha)
  simpa only [hg] using atGate a b hi

def Trace.regular (scope : I → Nat) : Trace I → Prop
  | .leaf _ => True
  | .pick g t => scope g = scope t.root ∧ t.regular scope
  | .join g l r => scope g ≤ scope l.root + scope r.root ∧ l.regular scope ∧ r.regular scope

def Trace.isLeaf : Trace I → Prop
  | .leaf _ => True
  | _ => False

/-- Applies to every trace, independently of the sequence of OR choices.
    Stop at a balanced occurrence or at a leaf too large to be balanced. -/
theorem frontier (scope : I → Nat) (n : Nat) (t : Trace I) (regular : t.regular scope)
    (big : n ≤ 3 * scope t.root) :
    ∃ v hs, Route t v hs ∧ n ≤ 3 * scope v.root ∧
      (3 * scope v.root ≤ 2*n ∨ v.isLeaf) := by
  induction t with
  | leaf g => exact ⟨_, _, .here _, big, Or.inr trivial⟩
  | pick g t ih =>
    obtain ⟨same, good⟩ := regular
    change n ≤ 3 * scope g at big
    obtain ⟨v, hs, path, lo, hi⟩ := ih good (same ▸ big)
    exact ⟨v, hs, .pick g path, lo, hi⟩
  | join g l r ihl ihr =>
    change n ≤ 3 * scope g at big
    by_cases mid : 3 * scope g ≤ 2*n
    · exact ⟨_, _, .here _, big, Or.inl mid⟩
    obtain ⟨bound, gl, gr⟩ := regular
    by_cases large : n ≤ 3 * scope l.root
    · obtain ⟨v, hs, path, lo, hi⟩ := ihl gl large
      exact ⟨v, r.root :: hs, .left g r path, lo, hi⟩
    · obtain ⟨v, hs, path, lo, hi⟩ := ihr gr (by omega)
      exact ⟨v, l.root :: hs, .right g l path, lo, hi⟩

end Mobius.HybridMatching
