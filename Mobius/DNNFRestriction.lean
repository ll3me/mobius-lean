import Mobius.ReadRestriction

/-! A topologically numbered negation-normal-form DAG. Restrictions change
only the leaf labels. The evaluator stores each visited node's value once,
with arbitrary fan-in and fan-out over the same finite list of node IDs. -/
namespace Mobius.DNNFRestriction
open Mobius.ReadRestriction (Guard Field)

inductive Gate (n : Nat) where
  | leaf
  | conj (inputs : List (Fin n))
  | disj (inputs : List (Fin n))

def Gate.inputs : Gate n → List (Fin n)
  | .leaf => []
  | .conj xs | .disj xs => xs

structure DAG (n : Nat) where
  gate : Fin n → Gate n
  output : Fin n
  earlier : ∀ v u, u∈(gate v).inputs → u.val<v.val

structure Circuit (n : Nat) (I : Type) where
  graph : DAG n
  label : Fin n → Guard I

def specialize (c : Circuit n O) (f : O → Field I) : Circuit n I :=
  ⟨c.graph, fun v => (c.label v).specialize f⟩

def nodeCount (_ : Circuit n I) := n
def edgeCount (c : Circuit n I) := ((List.finRange n).map fun v => (c.graph.gate v).inputs.length).sum

theorem same_shape (c : Circuit n O) (f : O → Field I) :
    (specialize c f).graph=c.graph ∧ nodeCount (specialize c f)=nodeCount c ∧
    edgeCount (specialize c f)=edgeCount c := ⟨rfl,rfl,rfl⟩

/-- The temporary array is in topological order, so every child index
exists before its parent executes. Empty conjunction/disjunction use
the ordinary Boolean identities. -/
def evalGate (g : Gate n) (b : Bool) (read : Fin n → Bool) : Bool :=
  match g with
  | .leaf => b
  | .conj xs => xs.all read
  | .disj xs => xs.any read

def lookup (a : Array Bool) (u : Fin n) : Bool := a[u.val]?.getD false

def table (c : Circuit n I) (x : I → Bool) : Nat → Array Bool
  | 0 => #[]
  | k+1 =>
    let prev := table c x k
    if h : k<n then
      let v : Fin n := ⟨k,h⟩
      prev.push (evalGate (c.graph.gate v) ((c.label v).eval x) (lookup prev))
    else prev

theorem table_size (c : Circuit n I) (x : I → Bool) (k : Nat) (cap : k≤n) :
    (table c x k).size=k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k<n := by omega
    simp [table,hk,ih (by omega)]

theorem child_available (c : Circuit n I) (x : I → Bool) (v u : Fin n) (edge : u ∈ (c.graph.gate v).inputs) :
    u.val < (table c x v.val).size := by
  rw [table_size _ _ _ (Nat.le_of_lt v.isLt)]
  exact c.graph.earlier v u edge

def value (c : Circuit n I) (x : I → Bool) (v : Fin n) : Bool := lookup (table c x n) v

def run (c : Circuit n I) (x : I → Bool) : Bool := value c x c.graph.output

private theorem stable_lookup (c : Circuit n I) (x : I → Bool) (u : Fin n) (k t : Nat)
    (hu : u.val<k) (hk : k≤t) (ht : t≤n) : lookup (table c x t) u=lookup (table c x k) u := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases equal : k=t+1
    · subst k; rfl
    · have next : t<n := by omega
      have earlier : u.val<(table c x t).size := by rw [table_size _ _ _ (by omega)]; omega
      simp only [table,next,↓reduceDIte,lookup,Array.getElem?_push,
        Nat.ne_of_lt earlier,ite_false]
      exact ih (by omega) (by omega)

private theorem evalGate_congr (g : Gate n) (b : Bool) (p q : Fin n → Bool)
    (agree : ∀ u∈g.inputs, p u=q u) : evalGate g b p=evalGate g b q := by
  cases g with
  | leaf => rfl
  | conj xs =>
    apply Bool.eq_iff_iff.mpr
    simp only [evalGate,List.all_eq_true]
    exact ⟨fun h u hu => (agree u hu) ▸ h u hu,fun h u hu => (agree u hu).symm ▸ h u hu⟩
  | disj xs =>
    apply Bool.eq_iff_iff.mpr
    simp only [evalGate,List.any_eq_true]
    constructor <;> rintro ⟨u,hu,h⟩
    · exact ⟨u,hu,(agree u hu) ▸ h⟩
    · exact ⟨u,hu,(agree u hu).symm ▸ h⟩

/-- The shared single-pass evaluator satisfies the usual local circuit
equation at every gate using its children's final values. -/
theorem value_gate (c : Circuit n I) (x : I → Bool) (v : Fin n) :
    value c x v=evalGate (c.graph.gate v) ((c.label v).eval x) (value c x) := by
  change lookup (table c x n) v=_
  rw [stable_lookup c x v (v.val+1) n (by omega) v.isLt (Nat.le_refl n)]
  simp only [table,v.isLt,↓reduceDIte,lookup,Array.getElem?_push,
    table_size _ _ _ (Nat.le_of_lt v.isLt),ite_true,Option.getD_some]
  apply evalGate_congr
  intro u edge
  exact (stable_lookup c x u v.val n (c.graph.earlier v u edge) (Nat.le_of_lt v.isLt) (Nat.le_refl n)).symm

theorem table_specialize (c : Circuit n O) (f : O → Field I) (x : I → Bool) (k : Nat) :
    table (specialize c f) x k=table c (fun j => (f j).read x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [table]
    rw [ih]
    simp only [specialize,ReadRestriction.eval_specialize]

theorem value_specialize (c : Circuit n O) (f : O → Field I) (x : I → Bool) (v : Fin n) :
    value (specialize c f) x v=value c (fun j => (f j).read x) v := by
  simp only [value,table_specialize]

theorem run_specialize (c : Circuit n O) (f : O → Field I) (x : I → Bool) :
    run (specialize c f) x=run c (fun j => (f j).read x) :=
  value_specialize c f x c.graph.output

/-- Reachability is a property of the stored node indices, including zero
steps at a leaf. Syntactic support counts both positive and negative uses. -/
inductive Descendant (g : DAG n) (root : Fin n) : Fin n → Prop where
  | here : Descendant g root root
  | child {v u} : Descendant g root v → u∈(g.gate v).inputs → Descendant g root u

def Support (c : Circuit n I) (v : Fin n) (i : I) : Prop :=
  ∃ w, Descendant c.graph v w ∧ c.graph.gate w=.leaf ∧ ∃ sign, c.label w=.literal i sign

/-- Pairwise runs over child occurrences, so two copies of a child with
nonempty support do not qualify as disjoint inputs. -/
def Decomposable (c : Circuit n I) : Prop :=
  ∀ v xs, c.graph.gate v=.conj xs →
    xs.Pairwise (fun a b => ∀ i, Support c a i → ¬Support c b i)

private theorem literal_image (g : Guard O) (f : O → Field I) (i : I) :
    (∃ pol, g.specialize f=.literal i pol) ↔
    ∃ j, f j=.input i ∧ ∃ pol, g=.literal j pol := by
  cases g with
  | constant b => simp [Guard.specialize]
  | literal j b =>
    cases h : f j with
    | fixed a => simp [Guard.specialize,h]
    | input k => simp [Guard.specialize,h]

/-- A specialized syntactic support is exactly the image of the original
reachable literal leaves after constant coordinates have been discarded. -/
theorem support_image (c : Circuit n O) (f : O → Field I) (v : Fin n) (i : I) :
    Support (specialize c f) v i ↔ ∃ j, f j=.input i ∧ Support c v j := by
  constructor
  · rintro ⟨w,reachable,leaf,pol,lit⟩
    obtain ⟨j,copy,pol',old⟩ := (literal_image (c.label w) f i).mp ⟨pol,lit⟩
    exact ⟨j,copy,w,reachable,leaf,pol',old⟩
  · rintro ⟨j,copy,w,reachable,leaf,pol,lit⟩
    obtain ⟨newSign,hit⟩ := (literal_image (c.label w) f i).mpr ⟨j,copy,pol,lit⟩
    exact ⟨w,reachable,leaf,newSign,hit⟩

theorem support_location (c : Circuit n O) (f : O → Field I) (location : I → O)
    (unique : ∀ i j, f j=.input i ↔ j=location i) (v : Fin n) (i : I) :
    Support (specialize c f) v i ↔ Support c v (location i) := by
  rw [support_image]
  constructor
  · rintro ⟨j,copy,s⟩
    exact (unique i j).mp copy ▸ s
  · intro s
    exact ⟨_,(unique i _).mpr rfl,s⟩

/-- A partial injective renaming is enough. Some surviving input names
may have no corresponding physical coordinate. -/
theorem decomposable_of_partial_injection (c : Circuit n O) (f : O → Field I)
    (inj : ∀ a b i, f a=.input i → f b=.input i → a=b)
    (old : Decomposable c) : Decomposable (specialize c f) := by
  intro v xs gate
  apply (old v xs gate).imp
  intro a b disjoint i ha hb
  obtain ⟨u,fu,sa⟩ := (support_image c f a i).mp ha
  obtain ⟨w,fw,sb⟩ := (support_image c f b i).mp hb
  obtain rfl := inj u w i fu fw
  exact disjoint u sa sb

/-- Ready for a raw-bit projection with one physical position per source
bit. Both semantics and sizes refer to the original shared circuit. -/
theorem restrict_dnnf (c : Circuit n O) (f : O → Field I) (location : I → O)
    (unique : ∀ i j, f j=.input i ↔ j=location i) (old : Decomposable c) :
    Decomposable (specialize c f) ∧
    (∀ x, run (specialize c f) x=run c (fun j => (f j).read x)) ∧
    nodeCount (specialize c f)=nodeCount c ∧ edgeCount (specialize c f)=edgeCount c := by
  have inj (a b : O) (i : I) (fa : f a=.input i) (fb : f b=.input i) : a=b :=
    ((unique i a).mp fa).trans ((unique i b).mp fb).symm
  exact ⟨decomposable_of_partial_injection c f inj old,run_specialize c f,(same_shape c f).2⟩

end Mobius.DNNFRestriction
