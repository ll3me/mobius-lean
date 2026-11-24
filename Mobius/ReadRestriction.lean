/-! Restrictions of edge-labeled nondeterministic branching programs.
    Paths and nodes are shared. The bound on reads holds on every syntactic
    path, including paths whose literals cannot all be true. -/
namespace Mobius.ReadRestriction

inductive Guard (I : Type) where
  | constant (value : Bool)
  | literal (input : I) (polarity : Bool)

def Guard.eval (x : I → Bool) : Guard I → Bool
  | .constant b => b
  | .literal i b => x i == b

def Guard.mentions [DecidableEq I] (i : I) : Guard I → Bool
  | .constant _ => false
  | .literal j _ => decide (j=i)

/-- A physical bit is a fixed constant or one source input. -/
inductive Field (I : Type) where
  | fixed (value : Bool)
  | input (index : I)
  deriving DecidableEq

def Field.read (x : I → Bool) : Field I → Bool
  | .fixed b => b
  | .input i => x i

def Guard.specialize (f : O → Field I) : Guard O → Guard I
  | .constant b => .constant b
  | .literal j b => match f j with
    | .fixed c => .constant (c == b)
    | .input i => .literal i b

theorem eval_specialize (f : O → Field I) (x : I → Bool) (g : Guard O) :
    (g.specialize f).eval x = g.eval (fun j => (f j).read x) := by
  cases g with
  | constant => rfl
  | literal j b => cases h : f j <;> simp [Guard.specialize,Guard.eval,Field.read,h]

/-- Node and edge types do not change under a restriction. -/
structure Graph (V E : Type) where
  initial : V
  finalNode : V → Prop
  src : E → V
  dst : E → V

def Graph.walk (g : Graph V E) (v : V) : List E → Prop
  | [] => g.finalNode v
  | e::es => g.src e = v ∧ g.walk (g.dst e) es

def Accept (g : Graph V E) (label : E → Guard I) (x : I → Bool) : Prop :=
  ∃ path, g.walk g.initial path ∧ ∀ e ∈ path, (label e).eval x = true

theorem accept_iff (g : Graph V E) (label : E → Guard O) (f : O → Field I) (x : I → Bool) :
    Accept g (fun e => (label e).specialize f) x ↔ Accept g label (fun j => (f j).read x) := by
  simp only [Accept,eval_specialize]

def ReadBound [DecidableEq I] (g : Graph V E) (label : E → Guard I) (r : Nat) : Prop :=
  ∀ path, g.walk g.initial path → ∀ i, path.countP (fun e => (label e).mentions i) ≤ r

/-- Each source input has a unique physical coordinate. Without this
    condition a restriction could duplicate reads of the same source bit. -/
theorem syntactic_count [DecidableEq I] [DecidableEq O] (label : E → Guard O)
    (f : O → Field I) (location : I → O) (unique : ∀ i j, f j = .input i ↔ j=location i)
    (path : List E) (i : I) :
    path.countP (fun e => ((label e).specialize f).mentions i) =
      path.countP (fun e => (label e).mentions (location i)) := by
  have same (a : Guard O) : (a.specialize f).mentions i = a.mentions (location i) := by
    cases a with
    | constant => rfl
    | literal j b =>
      cases h : f j with
      | fixed c =>
        have ne : j ≠ location i := fun eq => by
          have hl := (unique i j).mpr eq
          simp [h] at hl
        simp [Guard.specialize,Guard.mentions,h,ne]
      | input k =>
        have eqs : k=i ↔ j=location i := by simpa [h] using unique i j
        simp [Guard.specialize,Guard.mentions,h,eqs]
  simp only [same]

theorem read_bound [DecidableEq I] [DecidableEq O] (g : Graph V E) (label : E → Guard O)
    (f : O → Field I) (location : I → O) (unique : ∀ i j, f j = .input i ↔ j=location i)
    (old : ReadBound g label r) : ReadBound g (fun e => (label e).specialize f) r := by
  intro path route i
  rw [syntactic_count label f location unique]
  exact old path route (location i)



/-- A prefix to a node can be followed by every accepting suffix there.
    The prefix need not be consistent with any input. -/
def Graph.prefixTo (g : Graph V E) (v : V) (pre : List E) (w : V) : Prop :=
  ∀ tail, g.walk w tail → g.walk v (pre ++ tail)

def OneException [DecidableEq I] (g : Graph V E) (label : E → Guard I) (r : Nat) : Prop :=
  ∀ path, g.walk g.initial path → ∀ i j,
    r < path.countP (fun e => (label e).mentions i) →
    r < path.countP (fun e => (label e).mentions j) → i = j

/-- A single over-budget prefix bounds *every* suffix at the same node,
    including suffixes used by computations with a different prefix. -/
theorem suffix_bound_of_overread [DecidableEq I] (g : Graph V E) (label : E → Guard I)
    (budget : OneException g label r) (pre tail : List E)
    (join : g.prefixTo g.initial pre v) (suffix : g.walk v tail)
    (heavy : r < pre.countP (fun e => (label e).mentions i)) (other : i ≠ j) :
    tail.countP (fun e => (label e).mentions j) ≤ r := by
  apply Nat.le_of_not_gt
  intro excessive
  apply other
  apply budget (pre ++ tail) (join tail suffix)
  · rw [List.countP_append]
    omega
  · rw [List.countP_append]
    omega

end Mobius.ReadRestriction
