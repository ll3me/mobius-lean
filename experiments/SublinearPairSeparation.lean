import Mobius.Clock
import Complexity.PolynomialBound

/-!
# Conditional separation from sublinear pair contraction

The premise `EarlyQuarter R` is the criterion in `docs/MixedGuardPooling.md`.
The same implication holds for every fixed survival fraction below one and for
varying savings that dominate the fraction of vertices removed. Each criterion
counts gates after a fixed simplifier acts on an explicit partial pairing and
requires its output to decide every smaller graph.

The proof constructs circuits for clocked machines, projects Hamiltonian
cycle to the pinned project's SAT language and proves the growth recurrence
for the true minimum gate count. The separation theorems take their contraction
assumptions as arguments. Their transitive axioms are printed at the end.

Run from the repository root:
`.toolchain/bin/lake env .toolchain/bin/lean -DwarningAsError=true experiments/SublinearPairSeparation.lean`
-/
namespace SublinearPairSeparation
open Complexity

/-- A free constant or an actual input wire. -/
inductive Source (I : Type) where
  | fixed (b : Bool)
  | input (i : I)

def Source.read (x : I → Bool) : Source I → Bool
  | .fixed b => b
  | .input i => x i

inductive Formula (I : Type) where
  | leaf (v : Source I)
  | neg (p : Formula I)
  | conj (p q : Formula I)
  | disj (p q : Formula I)

def Formula.run (x : I → Bool) : Formula I → Bool
  | .leaf s => s.read x
  | .neg a => !(a.run x)
  | .conj a b => a.run x && b.run x
  | .disj a b => a.run x || b.run x

def Formula.cost : Formula I → Nat
  | .leaf _ => 0
  | .neg a => a.cost+1
  | .conj a b | .disj a b => a.cost+b.cost+1

/-- Wires in a layer may be used arbitrarily often by the next layer. An
unchanged wire costs zero to carry forward. A usual straight-line DAG can
thus be scheduled one gate per layer, carrying forward all earlier wires. -/
inductive Net (I : Type) : Type → Nat → Type 1 where
  | inputs {K : Type} (wires : K → Source I) : Net I K 0
  | layer {J K : Type} {s : Nat} (prev : Net I J s)
      (names : List K) (allNames : ∀ i, i ∈ names) (fs : K → Formula J) :
      Net I K (s + (names.map (fun i => (fs i).cost)).sum)

def Net.run {s : Nat} (c : Net I K s) (x : I → Bool) : K → Bool :=
  match c with
  | .inputs wires => fun i => (wires i).read x
  | .layer prev _ _ fs => fun i => (fs i).run (prev.run x)

def Gates (p : (I → Bool) → Prop) (s : Nat) : Prop :=
  ∃ c : Net I Unit s, ∀ x, (c.run x () = true ↔ p x)

/-- Nonuniform polynomial-size circuits on all binary words of each length. -/
def InPpoly (L : Language) : Prop :=
  ∃ B : Nat → Nat, PolynomialBound B ∧
    ∀ n, ∃ s ≤ B n, Gates (fun x : Fin n → Bool => L ((List.finRange n).map x)) s

private theorem sum_member {l : List α} {a : α} (f : α → Nat) (h : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hh
    · simp
    · have := ih hh; simp only [List.map_cons,List.sum_cons]; omega

private theorem zero_formula (f : Formula I) (h : f.cost = 0) :
    ∃ v : Source I, ∀ x, f.run x = v.read x := by
  cases f with
  | leaf v => exact ⟨v,fun _ => rfl⟩
  | neg p => simp [Formula.cost] at h
  | conj p q => simp [Formula.cost] at h
  | disj p q => simp [Formula.cost] at h

private theorem zero_net {s : Nat} (c : Net I K s) (h : s = 0) (i : K) :
    ∃ v : Source I, ∀ x, c.run x i = v.read x := by
  induction c with
  | inputs wires => exact ⟨wires i, fun _ => rfl⟩
  | layer prev names covers fs ih =>
    have hc := sum_member (fun j => (fs j).cost) (covers i)
    obtain ⟨w,hw⟩ := zero_formula (fs i) (by omega)
    cases w with
    | fixed b => exact ⟨.fixed b, fun x => hw (prev.run x)⟩
    | input j =>
      obtain ⟨v,hv⟩ := ih (by omega) j
      exact ⟨v,fun x => (hw (prev.run x)).trans (hv x)⟩

def Source.subst (p : J → Source I) : Source J → Source I
  | .fixed b => .fixed b
  | .input j => p j

def Net.prepend (p : J → Source I) : {K : Type} → {s : Nat} → Net J K s → Net I K s
  | _, _, .inputs w => .inputs (fun i => (w i).subst p)
  | _, _, .layer prev ls h fs => .layer (prev.prepend p) ls h fs

theorem Net.prepend_run {s : Nat} (c : Net J K s) (p : J → Source I) (x : I → Bool) :
    (c.prepend p).run x = c.run (fun j => (p j).read x) := by
  induction c with
  | inputs w => funext i; change ((w i).subst p).read x = (w i).read _; cases w i <;> rfl
  | layer prev ls h fs ih => funext i; exact congrArg (fun y => (fs i).run y) ih

private def grid (a b : Nat) : List (Fin a × Fin b) :=
  (List.finRange a).flatMap (fun i => (List.finRange b).map (fun j => (i,j)))

@[simp] private theorem mem_grid (v : Fin a × Fin b) : v ∈ grid a b := by
  rcases v with ⟨i,j⟩; simp [grid]

@[simp] private theorem length_grid (a b : Nat) : (grid a b).length = a*b := by
  simp [grid,List.length_flatMap,List.map_const',List.sum_replicate_nat]

private def anyF (ls : List α) (f : α → Formula I) : Formula I :=
  ls.foldr (fun a rest => .disj (f a) rest) (.leaf (.fixed false))

private theorem anyF_run (ls : List α) (f : α → Formula I) (x : I → Bool) :
    (anyF ls f).run x = ls.any (fun a => (f a).run x) := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp [anyF,Formula.run] at ih ⊢; rw [ih]

private theorem anyF_cost (ls : List α) (f : α → Formula I) (b : Nat)
    (h : ∀ j∈ls, (f j).cost ≤ b) : (anyF ls f).cost ≤ ls.length*(b+1) := by
  induction ls with
  | nil => simp [anyF,Formula.cost]
  | cons i ls ih =>
    have head := h i (by simp)
    have tail := ih (fun j hj => h j (by simp [hj]))
    change (f i).cost + (anyF ls f).cost + 1 ≤ (ls.length+1)*(b+1)
    rw [Nat.succ_mul]; omega

open LocalConstraint

/-- Compute one output bit of the one-hot encoding of a local transition tree. -/
private def treeBit {m d : Nat} (z : Fin (d+1)) :
    Tree m d → Formula (Fin m × Fin (d+1))
  | .value v => .leaf (.fixed (decide (v=z)))
  | .query i branches => anyF (List.finRange (d+1)) fun a =>
      .conj (.leaf (.input (i,a))) (treeBit z (branches a))

private theorem treeBit_run {m d : Nat} (t : Tree m d) (v : CSPSAT.Valuation m d)
    (z : Fin (d+1)) :
    (treeBit z t).run (fun j => decide (v j.1 = j.2)) = decide (t.eval v=z) := by
  induction t with
  | value a => rfl
  | query i bs ih =>
    apply Bool.eq_iff_iff.mpr
    simp [treeBit,anyF_run,Formula.run,Source.read,ih,Tree.eval] <;> exact ⟨decide_eq_true, of_decide_eq_true⟩

private def lookupCost (choices : Nat) : Nat → Nat
  | 0 => 0
  | t+1 => choices * (lookupCost choices t + 2)

private theorem treeBit_cost {m d : Nat} (depth : Nat) (t : Tree m d)
    (h : FiniteRows.QueriesAtMost depth t) (z : Fin (d+1)) :
    (treeBit z t).cost ≤ lookupCost (d+1) depth := by
  induction depth generalizing t with
  | zero => cases t with
    | value _ => exact Nat.le_refl _
    | query _ _ => exact False.elim h
  | succ depth ih =>
    cases t with
    | value _ => exact Nat.zero_le _
    | query i bs =>
      apply Nat.le_trans (anyF_cost _ _ (lookupCost (d+1) depth+1) (fun a _ => ?_))
      · simp [lookupCost,Nat.add_assoc]
      · change 0 + (treeBit z (bs a)).cost + 1 ≤ _
        have := ih (bs a) (h a); omega

private def unary (f : Bool → Bool) (s : Source I) : Formula I :=
  if f true then (if f false then .leaf (.fixed true) else .leaf s)
  else (if f false then .neg (.leaf s) else .leaf (.fixed false))

private theorem unary_run (f : Bool → Bool) (s : Source I) (x : I → Bool) :
    (unary f s).run x = f (s.read x) := by
  cases ht : f true <;> cases hf : f false <;> cases hs : s.read x <;>
    simp [unary,ht,hf,Formula.run,Source.read] at hs ⊢ <;> simp_all

private theorem unary_cost (f : Bool → Bool) (s : Source I) : (unary f s).cost ≤ 1 := by
  cases h : f true <;> cases j : f false <;> simp [unary,h,j,Formula.cost]

private abbrev RowBit (M : Machine) (w : Nat) := FiniteRows.Slot w × FiniteRows.Value M

private def initialBit (M : Machine) (w : Nat) (word : List (Source I)) (v : RowBit M w) : Formula I :=
  match FiniteRows.coordinate w v.1 with
  | .state => .leaf (.fixed (decide (FiniteRows.stateValue M M.start=v.2)))
  | .left _ => .leaf (.fixed (decide (FiniteRows.symbolValue M .blank=v.2)))
  | .right i =>
    match word[i.val]? with
    | none => .leaf (.fixed (decide (FiniteRows.symbolValue M .blank=v.2)))
    | some s => unary (fun b => decide (FiniteRows.symbolValue M (.bit b)=v.2)) s

private theorem initialBit_cost (M : Machine) (w : Nat) (word : List (Source I)) (v : RowBit M w) :
    (initialBit M w word v).cost ≤ 1 := by
  unfold initialBit
  split
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · apply unary_cost

private theorem initialBit_run (M : Machine) (w : Nat) (word : List (Source I)) (x : I → Bool)
    (v : RowBit M w) :
    (initialBit M w word v).run x =
      decide (CookLevin.initialRow M w (word.map (Source.read x)) v.1=v.2) := by
  unfold CookLevin.initialRow FiniteRows.encode initialBit
  cases hc : FiniteRows.coordinate w v.1 with
  | state => rfl
  | left i =>
    change _ = decide (FiniteRows.symbolValue M ((Tape.ofInput _).window w |>.left |>.getD i.val .blank) = _)
    rw [Tape.window_left_getD_lt _ _ _ i.isLt]
    simp [Tape.ofInput,List.getD,Formula.run,Source.read]
  | right i =>
    change _ = decide (FiniteRows.symbolValue M ((Tape.ofInput _).window w |>.right |>.getD i.val .blank) = _)
    rw [Tape.window_right_getD_lt _ _ _ i.isLt]
    cases hd : word[i.val]? <;>
      simp [hd,Tape.ofInput,List.getD,List.getElem?_map,unary_run,Formula.run,Source.read] <;>
      apply Bool.eq_iff_iff.mpr <;> simp only [decide_eq_true_eq] <;> exact ⟨of_decide_eq_true,decide_eq_true⟩

private def rowCount (M : Machine) (w : Nat) := (2*w+1)*(M.states+4)

private theorem simulateRows (M : Machine) (w : Nat) (hw : 0<w) (word : List (Source I)) (t : Nat) :
    ∃ s, ∃ c : Net I (RowBit M w) s,
      s ≤ rowCount M w + t*(rowCount M w * lookupCost (M.states+4) 3) ∧
      ∀ x j, c.run x j = decide (Tableau.iterate (CookLevin.transitionSystem M w hw) t
        (CookLevin.initialRow M w (word.map (Source.read x))) j.1=j.2) := by
  let ls := grid (2*w+1) (M.states+4)
  induction t with
  | zero =>
    refine ⟨_, Net.layer (.inputs Source.input) ls mem_grid (initialBit M w word), ?_, ?_⟩
    · have h := FiniteRows.sum_map_le_constant ls _ 1 (fun i _ => initialBit_cost M w word i)
      simpa [ls,rowCount] using h
    · intro x j; exact initialBit_run M w word x j
  | succ t ih =>
    obtain ⟨s,c,hs,valid⟩ := ih
    let fs (j : RowBit M w) := treeBit j.2 (FiniteRows.transitionTree M w hw j.1)
    refine ⟨_, Net.layer c ls mem_grid fs, ?_, ?_⟩
    · have bound := FiniteRows.sum_map_le_constant ls (fun j => (fs j).cost)
        (lookupCost (M.states+4) 3) (fun j _ => treeBit_cost 3 _ (FiniteRows.transitionTree_queries M w hw j.1) _)
      have b : (ls.map (fun j => (fs j).cost)).sum ≤ rowCount M w * lookupCost (M.states+4) 3 := by
        simpa only [ls,length_grid,rowCount] using bound
      simpa only [Nat.succ_mul t, Nat.add_assoc] using Nat.add_le_add hs b
    · intro x j
      change (fs j).run (c.run x) = _
      rw [funext (valid x)]
      apply treeBit_run

private def simulationBound (M : Machine) (length steps : Nat) :=
  let width := length + 2*steps + 1
  rowCount M width + steps*(rowCount M width * lookupCost (M.states+4) 3)

private theorem simulateDecision (M : Machine) (word : List (Source I)) (steps : Nat) :
    ∃ s ≤ simulationBound M word.length steps,
      Gates (fun x => ∃ tape, runInput M steps (word.map (Source.read x)) = some (true,tape)) s := by
  let w := word.length + 2*steps+1
  have hw : 0 < w := by dsimp [w]; omega
  obtain ⟨s,c,hs,valid⟩ := simulateRows M w hw word steps
  let q : RowBit M w := (FiniteRows.stateSlot w,FiniteRows.decisionValue M true)
  let last : Unit → Formula (RowBit M w) := fun _ => .leaf (.input q)
  refine ⟨_, ?_, Net.layer c [()] (by intro i; simp) last, ?_⟩
  · simpa [last,Formula.cost,simulationBound,w] using hs
  · intro x
    change c.run x q = true ↔ _
    rw [valid,decide_eq_true_eq]
    exact (InitialWord.pin_correct _ _ _).symm.trans
      (CookLevin.iterate_initialRow_accepted_iff M w hw steps _ (by simp [w]))

/-- Only off-diagonal, in-range arcs are input bits. -/
abbrev Arc (n : Nat) := {e : Nat × Nat // e.1<n ∧ e.2<n ∧ e.1≠e.2}
abbrev Graph (n : Nat) := Arc n → Bool

def arc (n u v : Nat) : Source (Arc n) :=
  if h : u<n ∧ v<n ∧ u≠v then .input ⟨(u,v),h⟩ else .fixed false

def edge (g : Graph n) (u v : Nat) : Bool := (arc n u v).read g

/-- A directed spanning tour written from vertex zero back to vertex zero. -/
def Hamilton (n : Nat) (g : Graph n) : Prop :=
  ∃ p : Nat → Nat, p 0 = 0 ∧ p n = 0 ∧
    (∀ t, t ≤ n → p t < n) ∧
    (∀ t, t<n → ∀ s, s<n → p t = p s → t=s) ∧
    (∀ v, v<n → ∃ t, t<n ∧ p t=v) ∧
    ∀ t, t<n → edge g (p t) (p (t+1)) = true

abbrev TLit (I : Type) := Nat × Source I
abbrev Template (I : Type) := List (List (TLit I))

private def instLit (x : I → Bool) (l : TLit I) : SAT.Literal := ⟨l.1,l.2.read x⟩
private def instantiate (x : I → Bool) (f : Template I) : SAT.CNF :=
  f.map (List.map (instLit x))

private def fixedWord (w : Word) : List (Source I) := w.map Source.fixed

private def litWord (l : TLit I) : List (Source I) := l.2 :: fixedWord (SAT.writeNat l.1)
private def clauseWord (ls : List (TLit I)) : List (Source I) :=
  fixedWord (SAT.writeNat ls.length) ++ ls.flatMap litWord
private def formulaWord (f : Template I) : List (Source I) :=
  fixedWord (SAT.writeNat f.length) ++ f.flatMap clauseWord

private theorem writeValues_flat (enc : α → Word) (ls : List α) :
    SAT.writeValues enc ls = ls.flatMap enc := by
  induction ls with
  | nil => rfl
  | cons x xs ih => simp [SAT.writeValues,ih]

@[simp] private theorem fixedWord_read (x : I → Bool) (w : Word) :
    (fixedWord w).map (Source.read x) = w := by simp [fixedWord,List.map_map,Function.comp_def,Source.read]

private theorem formulaWord_correct (x : I → Bool) (f : Template I) :
    (formulaWord f).map (Source.read x) = SAT.encode (instantiate x f) := by
  simp [formulaWord,clauseWord,litWord,instantiate,instLit,SAT.encode,SAT.encodeClause,
    SAT.encodeLiteral,SAT.writeList,writeValues_flat,List.map_flatMap,List.flatMap_map]

private def each (n : Nat) (f : Nat → List α) : List α := (List.range n).flatMap f

private def Holds (g : I → Bool) (a : SAT.Assignment) (f : Template I) : Prop :=
  ∀ c∈f, ∃ l∈c, a l.1 = l.2.read g

private theorem holds_sat (g : I → Bool) (a : SAT.Assignment) (f : Template I) :
    Holds g a f ↔ SAT.evalCNF a (instantiate g f) = true := by
  have lit (l : TLit I) : SAT.evalLiteral a (instLit g l) = true ↔ a l.1 = l.2.read g := by
    cases h : l.2.read g <;> simp [SAT.evalLiteral,instLit,h]
  simp [Holds,SAT.evalCNF,SAT.evalClause,instantiate,lit]

@[simp] private theorem holds_append (g : I → Bool) (a : SAT.Assignment) (f h : Template I) :
    Holds g a (f++h) ↔ Holds g a f ∧ Holds g a h := by
  simp [Holds,List.mem_append,or_imp,forall_and]

@[simp] private theorem holds_each (g : I → Bool) (a : SAT.Assignment) (n : Nat) (f : Nat → Template I) :
    Holds g a (each n f) ↔ ∀ t, t<n → Holds g a (f t) := by
  constructor
  · intro h t ht c hc
    exact h c (List.mem_flatMap.mpr ⟨t,List.mem_range.mpr ht,hc⟩)
  · intro h c hc
    obtain ⟨t,ht,hc⟩ := List.mem_flatMap.mp hc
    exact h t (List.mem_range.mp ht) c hc

private def posLit (v : Nat) : TLit I := (v,.fixed true)
private def negLit (v : Nat) : TLit I := (v,.fixed false)
private def unit (v : Nat) : Template I := [[posLit v]]
private def someVar (n : Nat) (v : Nat → Nat) : Template I := [(List.range n).map (fun t => posLit (v t))]
private def exclude (i j u v : Nat) : Template I := if i=j then [] else [[negLit u,negLit v]]
private def enabled (u v : Nat) (e : Source I) : Template I := [[negLit u,negLit v,(0,e)]]

@[simp] private theorem holds_unit (g : I → Bool) (a : SAT.Assignment) (v : Nat) :
    Holds g a (unit v) ↔ a v=true := by simp [holds_sat,unit,posLit,instantiate,instLit,SAT.evalLiteral,Source.read]

@[simp] private theorem holds_someVar (g : I → Bool) (a : SAT.Assignment) (n : Nat) (v : Nat → Nat) :
    Holds g a (someVar n v) ↔ ∃ t, t<n ∧ a (v t)=true := by
  simp [holds_sat,someVar,posLit,instantiate,instLit,SAT.evalClause,SAT.evalLiteral,Source.read]

@[simp] private theorem holds_exclude (g : I → Bool) (a : SAT.Assignment) (i j u v : Nat) :
    Holds g a (exclude i j u v) ↔ (a u=true → a v=true → i=j) := by
  by_cases h : i=j <;> cases hu : a u <;> cases hv : a v <;>
    simp [holds_sat,instantiate,instLit,exclude,h,negLit,SAT.evalLiteral,Source.read,hu,hv]

@[simp] private theorem holds_enabled (g : I → Bool) (a : SAT.Assignment) (h : a 0=true)
    (u v : Nat) (e : Source I) :
    Holds g a (enabled u v e) ↔ (a u=true → a v=true → e.read g=true) := by
  cases hu : a u <;> cases hv : a v <;> cases he : e.read g <;>
    simp [holds_sat,instantiate,instLit,enabled,negLit,SAT.evalLiteral,h,hu,hv,Source.read] at * <;> exact he

private def ix (n t v : Nat) := 1+(t*n+v)

/-- Times 0 through n have exactly one vertex. The final occurrence of
zero closes the tour and is excluded from the permutation constraints. -/
private def instanceOf (n : Nat) : Template (Arc n) :=
  unit 0 ++ unit (ix n 0 0) ++ unit (ix n n 0) ++
  each (n+1) (fun t => someVar n (ix n t)) ++
  each n (fun v => someVar n (fun t => ix n t v)) ++
  each (n+1) (fun t => each n (fun u => each n (fun v => exclude u v (ix n t u) (ix n t v)))) ++
  each n (fun v => each n (fun t => each n (fun s => exclude s t (ix n s v) (ix n t v)))) ++
  each n (fun t => each n (fun u => each n (fun v => enabled (ix n t u) (ix n (t+1) v) (arc n u v))))

private def ValidTable (n : Nat) (g : Graph n) (sel : Nat → Nat → Bool) : Prop :=
  sel 0 0=true ∧ sel n 0=true ∧
  (∀ t, t<n+1 → ∃ v, v<n ∧ sel t v=true) ∧
  (∀ v, v<n → ∃ t, t<n ∧ sel t v=true) ∧
  (∀ t, t<n+1 → ∀ u, u<n → ∀ v, v<n → sel t u=true → sel t v=true → u=v) ∧
  (∀ v, v<n → ∀ t, t<n → ∀ s, s<n → sel s v=true → sel t v=true → s=t) ∧
  ∀ t, t<n → ∀ u, u<n → ∀ v, v<n → sel t u=true → sel (t+1) v=true → edge g u v=true

private theorem instance_spec (g : Graph n) (a : SAT.Assignment) :
    Holds g a (instanceOf n) ↔ a 0=true ∧ ValidTable n g (fun t v => a (ix n t v)) := by
  by_cases h : a 0=true
  · simp only [instanceOf,holds_append,holds_unit,holds_each,holds_someVar,holds_exclude,
      holds_enabled _ _ h,ValidTable,edge,h,true_and,and_assoc]
  · simp [instanceOf,h]

private theorem table_tour (g : Graph n) :
    (∃ sel, ValidTable n g sel) ↔ Hamilton n g := by
  constructor
  · rintro ⟨sel,root,close,rows,cols,uniqueRow,uniqueCol,openArc⟩
    let p (t : Nat) := if ht : t<n+1 then Classical.choose (rows t ht) else 0
    have chosen (t : Nat) (ht : t≤n) : p t<n ∧ sel t (p t)=true := by
      have h : t<n+1 := by omega
      simpa [p,h] using Classical.choose_spec (rows t h)
    have hn := (chosen 0 (by omega)).1
    have zero : 0<n := by omega
    refine ⟨p,uniqueRow 0 (by omega) _ (chosen 0 (by omega)).1 _ zero (chosen 0 (by omega)).2 root,
      uniqueRow n (by omega) _ (chosen n (by omega)).1 _ zero (chosen n (by omega)).2 close,
      fun t ht => (chosen t ht).1, ?_, ?_, ?_⟩
    · intro t ht s hs eq
      exact uniqueCol (p t) (chosen t (by omega)).1 s hs t ht (chosen t (by omega)).2
        (eq ▸ (chosen s (by omega)).2)
    · intro v hv
      obtain ⟨t, ht, h⟩ := cols v hv
      exact ⟨t,ht,uniqueRow t (by omega) _ (chosen t (by omega)).1 v hv (chosen t (by omega)).2 h⟩
    · intro t ht
      exact openArc t ht _ (chosen t (by omega)).1 _ (chosen (t+1) (by omega)).1
        (chosen t (by omega)).2 (chosen (t+1) (by omega)).2
  · rintro ⟨p,h0,hn,bound,inj,onto,ok⟩
    refine ⟨fun t v => decide (p t=v), ?_⟩
    simp only [ValidTable,decide_eq_true_eq]
    exact ⟨h0,hn,fun t ht => ⟨p t,bound t (by omega),rfl⟩,onto,
      fun _ _ _ _ _ _ h j => h.symm.trans j,
      fun _ _ t ht s hs a b => inj s hs t ht (a.trans b.symm),
      fun t ht u _ v _ eu ev => eu ▸ ev ▸ ok t ht⟩

private theorem hamilton_sat (g : Graph n) :
    SAT.SAT ((formulaWord (instanceOf n)).map (Source.read g)) ↔ Hamilton n g := by
  rw [formulaWord_correct,SAT.SAT_encode_iff,← table_tour]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨_,((instance_spec g a).mp ((holds_sat ..).mpr ha)).2⟩
  · rintro ⟨sel,hs⟩
    have row := hs.2.2.1 0 (by omega)
    obtain ⟨v,hv,_⟩ := row
    have hn : 0<n := by omega
    let a (j : Nat) := if j=0 then true else sel ((j-1)/n) ((j-1)%n)
    have data (t v : Nat) (h : v<n) : a (ix n t v) = sel t v := by
      have hd : (t*n+v)/n=t := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt h, Nat.zero_add]
      simp [a,ix,Nat.add_comm 1,hd,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt h]
    refine ⟨a,(holds_sat ..).mp ((instance_spec g a).mpr ⟨by simp [a],?_⟩)⟩
    obtain ⟨z,last,rows,cols,ur,uc,edges⟩ := hs
    refine ⟨(data _ _ hn).trans z,(data _ _ hn).trans last,?_,?_,?_,?_,?_⟩
    · intro t ht; obtain ⟨v,hv,h⟩ := rows t ht; exact ⟨v,hv,(data _ _ hv).trans h⟩
    · intro v hv; obtain ⟨t,ht,h⟩ := cols v hv; exact ⟨t,ht,(data _ _ hv).trans h⟩
    · intro t ht u hu v hv h1 h2; exact ur t ht u hu v hv ((data t u hu).symm.trans h1) ((data t v hv).symm.trans h2)
    · intro v hv t ht s hh h1 h2; exact uc v hv t ht s hh ((data s v hv).symm.trans h1) ((data t v hv).symm.trans h2)
    · intro t ht u hu v hv h1 h2; exact edges t ht u hu v hv ((data t u hu).symm.trans h1) ((data (t+1) v hv).symm.trans h2)

/-- Count the actual serialized bit length, including the unary variable indices. -/
private def weight (f : Template I) :=
  (f.map (fun c => 2+(c.map (fun l => l.1+3)).sum)).sum

private theorem word_length (f : Template I) : (formulaWord f).length = weight f+1 := by
  have clause (ls : List (TLit I)) : (clauseWord ls).length = 1+(ls.map (fun l => l.1+3)).sum := by
    induction ls with
    | nil => rfl
    | cons a ls ih =>
      simp [clauseWord,fixedWord,litWord,SATBounds.writeNat_length] at ih ⊢
      omega
  induction f with
  | nil => rfl
  | cons c f ih =>
    simp [formulaWord,fixedWord,weight,SATBounds.writeNat_length] at ih ⊢
    have h := clause c
    omega

private def varCap (n : Nat) := 1+n*n+n
private def clauseCap (n : Nat) := 2+(n+3)*(varCap n+3)
private def groups (n : Nat) := 3+(n+1)+n+(n+1)*(n*(n*1))+n*(n*(n*1))+n*(n*(n*1))

private theorem ix_bound (n t v : Nat) (ht : t≤n) (hv : v≤n) : ix n t v ≤ varCap n := by
  have := Nat.mul_le_mul_right n ht
  unfold ix varCap; omega

private theorem single_weight {c : List (TLit I)} (n : Nat) (hc : c.length≤n+3)
    (hl : ∀ l∈c, l.1≤varCap n) : weight [c] ≤ clauseCap n := by
  have h := FiniteRows.sum_map_le_constant c (fun l => l.1+3) (varCap n+3) (fun l hh => by
    have := hl l hh; omega)
  have j := Nat.mul_le_mul_right (varCap n+3) hc
  simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,clauseCap]
  omega

private theorem each_weight (n b : Nat) (f : Nat → Template I)
    (h : ∀ t, t<n → weight (f t)≤b) : weight (each n f) ≤ n*b := by
  have hs := FiniteRows.sum_map_le_constant (List.range n) (fun t => weight (f t)) b
    (fun t ht => h t (List.mem_range.mp ht))
  have flat (ls : List Nat) : weight (ls.flatMap f) = (ls.map (fun t => weight (f t))).sum := by
    induction ls with
    | nil => rfl
    | cons a ls ih => simp [weight] at ih ⊢; exact ih
  simpa only [each,flat,List.length_range] using hs

private theorem append_weight (f g : Template I) : weight (f++g) = weight f + weight g := by
  simp [weight]

private theorem template_size (n : Nat) : weight (instanceOf n) ≤ groups n * clauseCap n := by
  let B := clauseCap n
  have un (u : Nat) (h : u≤varCap n) : weight (unit (I:=Arc n) u)≤B := by
    apply single_weight <;> simp [posLit,h]
  have ex (i j u v : Nat) (hu : u≤varCap n) (hv : v≤varCap n) :
      weight (exclude (I:=Arc n) i j u v)≤B := by
    unfold exclude; split
    · exact Nat.zero_le _
    · apply single_weight
      · simp
      · intro l hl; rcases List.mem_cons.mp hl with rfl | h
        · exact hu
        · obtain rfl := List.mem_singleton.mp h; exact hv
  have en (u v : Nat) (e : Source (Arc n)) (hu : u≤varCap n) (hv : v≤varCap n) :
      weight (enabled u v e)≤B := by
    apply single_weight
    · simp
    · intro l hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact hu
      · exact hv
      · exact Nat.zero_le _
  have someW (f : Nat → Nat) (h : ∀ t, t<n → f t≤varCap n) :
      weight (someVar (I:=Arc n) n f)≤B := by
    apply single_weight
    · simp
    · intro l hl; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hl
      exact h t (List.mem_range.mp ht)
  have b0 : weight (unit (I:=Arc n) 0) + weight (unit (I:=Arc n) (ix n 0 0)) + weight (unit (I:=Arc n) (ix n n 0)) ≤ 3*B := by
    have h1 := un 0 (Nat.zero_le _)
    have h2 := un _ (ix_bound n 0 0 (by omega) (by omega))
    have h3 := un _ (ix_bound n n 0 (by omega) (by omega))
    omega
  have b1 := each_weight (n+1) B (fun t => someVar (I:=Arc n) n (ix n t))
    (fun t ht => someW _ (fun v hv => ix_bound n t v (by omega) (by omega)))
  have b2 := each_weight n B (fun v => someVar (I:=Arc n) n (fun t => ix n t v))
    (fun v hv => someW _ (fun t ht => ix_bound n t v (by omega) (by omega)))
  have b3 := each_weight (n+1) _ _ (fun t ht => each_weight n _ _ (fun u hu =>
    each_weight n B _ (fun v hv => ex u v _ _ (ix_bound n t u (by omega) (by omega))
      (ix_bound n t v (by omega) (by omega)))))
  have b4 := each_weight n _ _ (fun v hv => each_weight n _ _ (fun t ht =>
    each_weight n B _ (fun s hs => ex s t _ _ (ix_bound n s v (by omega) (by omega))
      (ix_bound n t v (by omega) (by omega)))))
  have b5 := each_weight n _ _ (fun t ht => each_weight n _ _ (fun u hu =>
    each_weight n B _ (fun v hv => en _ _ (arc n u v) (ix_bound n t u (by omega) (by omega))
      (ix_bound n (t+1) v (by omega) (by omega)))))
  have h := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    b0 b1) b2) b3) b4) b5
  simpa only [instanceOf,append_weight,groups,B,Nat.add_mul,Nat.mul_assoc,Nat.one_mul] using h

private theorem poly_word : PolynomialBound (fun n => (formulaWord (instanceOf n)).length) := by
  apply PolynomialBound.weaken (g:=fun n => groups n * clauseCap n + 1)
  · unfold groups clauseCap varCap
    repeat' first | exact PolynomialBound.identity | apply PolynomialBound.constant |
      apply PolynomialBound.add | apply PolynomialBound.mul
  · intro n; rw [word_length]; exact Nat.add_le_add_right (template_size n) 1

private theorem poly_sim (M : Machine) (c d : Nat) :
    PolynomialBound (fun n => simulationBound M n (powerBound c d n)) := by
  have ht := PolynomialBound.power c d
  have hw := (PolynomialBound.identity.add ((PolynomialBound.constant 2).mul ht)).add
    (PolynomialBound.constant 1)
  have cells := (((PolynomialBound.constant 2).mul hw).add (PolynomialBound.constant 1)).mul
    (PolynomialBound.constant (M.states+4))
  exact cells.add (ht.mul (cells.mul (PolynomialBound.constant (lookupCost (M.states+4) 3))))

/-- P ⊆ P/poly for the pinned project's one-tape machines and this circuit basis. -/
theorem inP_to_p_poly {L : Language} (hp : InP L) : InPpoly L := by
  obtain ⟨M,c,d,clock⟩ := (Mobius.Clock.inP_iff_clock L).mp hp
  refine ⟨_,poly_sim M c d,?_⟩
  intro n
  let word := (List.finRange n).map (fun i => Source.input i)
  have len : word.length = n := by simp [word]
  obtain ⟨s,hs,net,correct⟩ := simulateDecision M word (powerBound c d word.length)
  refine ⟨s,by simpa only [len] using hs,net,?_⟩
  intro x
  have same : word.map (Source.read x) = (List.finRange n).map x := by
    simp [word,List.map_map,Function.comp_def,Source.read]
  obtain ⟨b,t,run,answer⟩ := clock (word.map (Source.read x))
  simp only [List.length_map] at run
  rw [correct]
  change (∃ tape, runInput M (powerBound c d word.length) (word.map (Source.read x)) =
    some (true,tape)) ↔ L ((List.finRange n).map x)
  rw [← same,answer]
  constructor
  · rintro ⟨t',hr⟩
    have hh := run.symm.trans hr
    exact congrArg Prod.fst (Option.some.inj hh)
  · rintro rfl; exact ⟨_,run⟩


/- A single-vertex split. Insert a new vertex zero in front of the old
root, shift every old label by one, and route old returns to the new root. -/
private def splitWire (n : Nat) (e : Arc (n+1)) : Source (Arc n) :=
  let u := e.val.1
  let v := e.val.2
  if u=0 then .fixed (decide (v=1))
  else if v=0 then arc n (u-1) 0
  else if v=1 then .fixed false
  else arc n (u-1) (v-1)

private def splitGraph (g : Graph n) : Graph (n+1) := fun e => (splitWire n e).read g

private theorem split_root (g : Graph n) (v : Nat) (hv : v<n+1) :
    edge (splitGraph g) 0 v = decide (v=1) := by
  by_cases h : v=0
  · subst v; simp [edge,arc,Source.read]
  · have ne : 0≠v := Ne.symm h
    simp [edge,arc,ne,hv,splitGraph,splitWire,Source.read]

private theorem split_return (g : Graph n) (v : Nat) (hv : v<n) :
    edge (splitGraph g) (v+1) 0 = edge g v 0 := by
  have h : v+1<n+1 := by omega
  simp [edge,arc,h,splitGraph,splitWire,Source.read]

private theorem split_inner (g : Graph n) (u v : Nat) (hu : u<n) (hv : v<n) :
    edge (splitGraph g) (u+1) (v+1) = if v=0 then false else edge g u v := by
  by_cases huv : u=v
  · subst v; simp [edge,arc,Source.read]
  · have h : (u+1)≠v+1 := by omega
    have hu' : u+1<n+1 := by omega
    have hv' : v+1<n+1 := by omega
    by_cases hz : v=0
    · subst v
      have hn : 0<n := by omega
      simp [edge,arc,hu,huv,hn,splitGraph,splitWire,Source.read]
    · simp [edge,arc,hu',hv',hu,hv,huv,splitGraph,splitWire,hz,Source.read]

private theorem tour_split (g : Graph n) (hn : 2≤n) :
    Hamilton n g ↔ Hamilton (n+1) (splitGraph g) := by
  constructor
  · rintro ⟨p,p0,pn,bd,inj,onto,ok⟩
    let q (t : Nat) := if t=0 ∨ t=n+1 then 0 else p (t-1)+1
    have q0 : q 0=0 := by simp [q]
    have qn : q (n+1)=0 := by simp [q]
    have atOld (t : Nat) (h : t<n) : q (t+1)=p t+1 := by simp [q,show t≠n by omega]
    refine ⟨q,q0,qn,?_,?_,?_,?_⟩
    · intro t ht
      dsimp [q]; split
      · omega
      · have := bd (t-1) (by omega); omega
    · intro t ht s hs h
      cases t with
      | zero =>
        cases s with
        | zero => rfl
        | succ l => rw [q0,atOld l (by omega)] at h; omega
      | succ j =>
        cases s with
        | zero => rw [q0,atOld j (by omega)] at h; omega
        | succ l =>
          rw [atOld j (by omega),atOld l (by omega)] at h
          exact congrArg Nat.succ (inj j (by omega) l (by omega) (Nat.succ.inj h))
    · intro v hv
      cases v with
      | zero => exact ⟨0,by omega,q0⟩
      | succ u =>
        obtain ⟨t,ht,h⟩ := onto u (by omega)
        exact ⟨t+1,by omega,(atOld t ht).trans (congrArg Nat.succ h)⟩
    · intro t ht
      cases t with
      | zero =>
        rw [q0,atOld 0 (by omega),p0,split_root _ _ (by omega)]
        decide
      | succ t =>
        have ht' : t<n := by omega
        rw [atOld t ht']
        by_cases last : t+1=n
        · rw [last,qn,split_return _ _ (bd _ (by omega))]
          simpa [last,pn] using ok t ht'
        · have next : t+1<n := by omega
          have nz : p (t+1)≠0 := by
            intro h; have := inj (t+1) next 0 (by omega) (h.trans p0.symm); omega
          rw [atOld _ next,split_inner _ _ _ (bd _ (by omega)) (bd _ (by omega)),ite_eq_right nz]
          exact ok t ht'
  · rintro ⟨q,q0,qn,bd,inj,onto,ok⟩
    have q1 : q 1=1 := by
      have h := ok 0 (by omega)
      rw [q0,split_root _ _ (bd _ (by omega))] at h
      exact of_decide_eq_true h
    let p (t : Nat) := if t=n then 0 else q (t+1)-1
    have pn : p n=0 := by simp [p]
    have p0 : p 0=0 := by simp [p,show 0≠n by omega,q1]
    have qt (t : Nat) (ht : t<n) : q (t+1)=p t+1 := by
      have nz : q (t+1)≠0 := by
        intro h; have := inj (t+1) (by omega) 0 (by omega) (h.trans q0.symm); omega
      simp only [p,ite_eq_right (show t≠n by omega)]; omega
    have pb (t : Nat) (ht : t≤n) : p t<n := by
      by_cases last : t=n
      · subst t; omega
      · have := qt t (by omega); have := bd (t+1) (by omega); omega
    refine ⟨p,p0,pn,pb,?_,?_,?_⟩
    · intro t ht s hs h
      have hh := inj (t+1) (by omega) (s+1) (by omega)
        ((qt t ht).trans ((congrArg Nat.succ h).trans (qt s hs).symm))
      omega
    · intro v hv
      obtain ⟨t,ht,h⟩ := onto (v+1) (by omega)
      cases t with
      | zero => omega
      | succ t =>
        have := qt t (by omega)
        exact ⟨t,by omega,by omega⟩
    · intro t ht
      have h := ok (t+1) (by omega)
      rw [qt t ht] at h
      by_cases last : t+1=n
      · rw [last,qn,split_return _ _ (pb _ (by omega))] at h
        simpa [last,pn] using h
      · rw [qt (t+1) (by omega), split_inner _ _ _ (pb _ (by omega)) (pb _ (by omega))] at h
        split at h
        · contradiction
        · exact h

/-- Minimum gate count over explicit shared circuits; the finite truth-table
construction below supplies a circuit at every size. -/
private theorem leastWitness (P : Nat → Prop) {a : Nat} (ha : P a) :
    ∃ m, P m ∧ ∀ t, P t → m≤t := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases h : ∃ t, t<a ∧ P t
    · obtain ⟨t,lt,ht⟩ := h
      exact ih t lt ht
    · exact ⟨a,ha,fun t ht => Nat.le_of_not_gt (fun lt => h ⟨t,lt,ht⟩)⟩

private def arcNames (n : Nat) : List (Arc n) :=
  (grid n n).flatMap fun e =>
    if h : e.1.val ≠ e.2.val then [⟨(e.1,e.2),e.1.isLt,e.2.isLt,h⟩] else []

private theorem mem_arcNames (e : Arc n) : e ∈ arcNames n := by
  rcases e with ⟨⟨u,v⟩,hu,hv,h⟩
  apply List.mem_flatMap.mpr
  refine ⟨(⟨u,hu⟩,⟨v,hv⟩),mem_grid _,?_⟩
  simp [h]

private theorem truth_formula (ls : List I) (p : (I → Bool) → Prop)
    (support : ∀ x y, (∀ i∈ls, x i=y i) → (p x ↔ p y)) :
    ∃ f : Formula I, ∀ x, f.run x=true ↔ p x := by
  classical
  induction ls generalizing p with
  | nil =>
    refine ⟨.leaf (.fixed (decide (p (fun _ => false)))), fun x => ?_⟩
    exact (show decide (p (fun _ => false)) = true ↔ p (fun _ => false) from
      ⟨of_decide_eq_true,decide_eq_true⟩).trans (support _ x (by simp))
  | cons i ls ih =>
    let pin (b : Bool) (x : I → Bool) (j : I) := if j=i then b else x j
    have hp (b : Bool) : ∃ f : Formula I, ∀ x, f.run x=true ↔ p (pin b x) := by
      apply ih
      intro x y h
      apply support
      intro j hj
      by_cases eq : j=i
      · simp [pin,eq]
      · have hh := h j ((List.mem_cons.mp hj).resolve_left eq)
        simp [pin,eq,hh]
    obtain ⟨f0,h0⟩ := hp false
    obtain ⟨f1,h1⟩ := hp true
    refine ⟨.disj (.conj (.leaf (.input i)) f1) (.conj (.neg (.leaf (.input i))) f0), fun x => ?_⟩
    have H (b : Bool) (hx : x i=b) : pin b x=x := by
      funext j; by_cases eq : j=i <;> simp [pin,eq,hx]
    cases hx : x i with
    | false => simpa [Formula.run,Source.read,hx,H false hx] using h0 x
    | true => simpa [Formula.run,Source.read,hx,H true hx] using h1 x

private theorem gates_exist (n : Nat) : ∃ s, Gates (Hamilton n) s := by
  obtain ⟨f,h⟩ := truth_formula (arcNames n) (Hamilton n) (fun x y hh => by
    have eq : x=y := funext (fun i => hh i (mem_arcNames i))
    rw [eq])
  refine ⟨_, Net.layer (Net.inputs (fun i : Arc n => Source.input i)) [()] (by simp) (fun _ => f), ?_⟩
  intro x; exact h x

private theorem minimum_exists (n : Nat) : ∃ s, Gates (Hamilton n) s ∧ ∀ r, Gates (Hamilton n) r → s≤r := by
  obtain ⟨s,h⟩ := gates_exist n
  exact leastWitness _ h

noncomputable def S (n : Nat) := Classical.choose (minimum_exists n)

theorem size_spec (n : Nat) : Gates (Hamilton n) (S n) ∧ ∀ r, Gates (Hamilton n) r → S n≤r :=
  Classical.choose_spec (minimum_exists n)

private theorem size_step (n : Nat) (hn : 2≤n) : S n ≤ S (n+1) := by
  obtain ⟨c,correct⟩ := (size_spec (n+1)).1
  apply (size_spec n).2
  refine ⟨c.prepend (splitWire n),fun g => ?_⟩
  rw [Net.prepend_run]
  exact (correct (splitGraph g)).trans (tour_split g hn).symm

private theorem size_mono {n m : Nat} (hn : 2≤n) (hm : n≤m) : S n ≤ S m := by
  induction hm with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (size_step _ (Nat.le_trans hn h))

private theorem dead_vertex {g : Graph n} (v : Nat) (hv : v<n) (dead : ∀ w, edge g v w=false) :
    ¬Hamilton n g := by
  rintro ⟨p,_,_,_,_,onto,openArc⟩
  obtain ⟨t,ht,e⟩ := onto v hv
  have h := openArc t ht
  rw [e,dead] at h
  contradiction

private theorem two_complete : Hamilton 2 (fun _ => true) := by
  let p (t : Nat) := if t=1 then 1 else 0
  refine ⟨p, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro t _; dsimp [p]; split <;> omega
  · intro s hs t ht; dsimp [p]; split <;> split <;> omega
  · intro v hv
    rcases (show v=0 ∨ v=1 by omega) with rfl | rfl
    · exact ⟨0,by decide,rfl⟩
    · exact ⟨1,by decide,rfl⟩
  · intro t ht
    rcases (show t=0 ∨ t=1 by omega) with rfl | rfl <;> rfl

private theorem size_positive (n : Nat) (hn : 2≤n) : 0<S n := by
  suffices h : 0 < S 2 from Nat.lt_of_lt_of_le h (size_mono (by decide) hn)
  apply Nat.lt_of_not_ge
  intro bound
  obtain ⟨c,correct⟩ := (size_spec 2).1
  obtain ⟨src,h⟩ := zero_net c (by omega) ()
  cases src with
  | fixed b =>
    have yes := (correct _).mpr two_complete
    rw [h] at yes
    have empty : ¬Hamilton 2 (fun _ => false) := dead_vertex 0 (by decide) (fun w => by
      unfold edge arc; split <;> rfl)
    apply empty
    apply (correct _).mp
    rw [h]; exact yes
  | input e =>
    let one : Graph 2 := fun v => decide (v=e)
    have yes : Hamilton 2 one := (correct one).mp (by rw [h]; simp [Source.read,one])
    apply dead_vertex e.val.2 e.property.2.1 _ yes
    intro w; unfold edge arc
    split
    · change decide (_=e) = false
      apply decide_eq_false
      intro eq
      exact e.property.2.2 (congrArg (fun j : Arc 2 => j.val.1) eq).symm
    · rfl

/-- The integer definition of k(n)=o(n), with a common k for every size. -/
def Sublinear (k : Nat → Nat) : Prop :=
  ∀ A : Nat, ∃ n₀, ∀ n ≥ n₀, A*k n ≤ n

/-- At most p/q of the original minimum suffices after removing k(n)=o(n) vertices. -/
def FractionRecurrence (p q : Nat) : Prop :=
  ∃ k : Nat → Nat, Sublinear k ∧ ∃ n₀, ∀ m, n₀≤2*m → q*S (2*m-k (2*m)) ≤ p*S (2*m)

abbrev QuarterRecurrence := FractionRecurrence 1 4

/-- For each factor A, eventually at every even n there is a step whose
relative saving is at least A*(k+1)/(n+1). The extra vertex pays for rounding
the smaller size down to an even number for the next induction step. -/
def RelativeRecurrence : Prop :=
  ∀ A : Nat, ∃ n₀, ∀ m, n₀ ≤ 2*m → ∃ k, 0 < k ∧ k ≤ m ∧
    (2*m+1)*S (2*m-k) + (A*(k+1))*S (2*m) ≤ (2*m+1)*S (2*m)

private theorem fraction_budget {p q n w kept total : Nat} (lt : p < q)
    (room : q*w ≤ n) (retention : q*kept ≤ p*total) :
    n*kept + w*total ≤ n*total := by
  apply Nat.le_of_mul_le_mul_left _ (show 0 < q by omega)
  calc
    q*(n*kept + w*total) = n*(q*kept) + (q*w)*total := by rw [Nat.mul_add]; ac_rfl
    _ ≤ n*(p*total) + n*total :=
      Nat.add_le_add (Nat.mul_le_mul_left n retention) (Nat.mul_le_mul_right total room)
    _ = (p+1)*(n*total) := by rw [Nat.succ_mul]; ac_rfl
    _ ≤ q*(n*total) := Nat.mul_le_mul_right _ lt

theorem relative_of_fraction {p q : Nat} (lt : p < q) (h : FractionRecurrence p q) :
    RelativeRecurrence := by
  obtain ⟨k,sub,cut,step⟩ := h
  intro A
  let b := q*A
  obtain ⟨nf,fit⟩ := sub 2
  obtain ⟨ns,slow⟩ := sub (2*b)
  refine ⟨cut+nf+ns+2*b+8,?_⟩
  intro m big
  have hk := fit (2*m) (by omega)
  have hb := slow (2*m) (by omega)
  have keep := step m (by omega)
  have pos : 0 < k (2*m) := by
    by_cases hz : k (2*m) = 0
    · simp only [hz,Nat.sub_zero] at keep
      have := Nat.le_of_mul_le_mul_right keep (size_positive _ (by omega))
      omega
    · omega
  have room : q*(A*(k (2*m)+1)) ≤ 2*m+1 := by
    rw [← Nat.mul_assoc, Nat.mul_succ]
    change b*k (2*m)+b ≤ 2*m+1
    rw [Nat.mul_assoc 2 b] at hb
    omega
  exact ⟨_,pos,by omega,fraction_budget lt room keep⟩

private theorem power_loss (a h t : Nat) :
    (a+h)^(t+1) ≤ a^(t+1) + ((t+1)*h)*(a+h)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have tail := Nat.mul_le_mul_right h (Nat.pow_le_pow_left (Nat.le_add_right a h) (t+1))
    calc
      (a+h)^(t+2) = (a+h)^(t+1)*(a+h) := Nat.pow_succ ..
      _ ≤ (a^(t+1) + ((t+1)*h)*(a+h)^t)*(a+h) := Nat.mul_le_mul_right _ ih
      _ = a^(t+2) + a^(t+1)*h + ((t+1)*h)*(a+h)^(t+1) := by
        rw [Nat.add_mul, Nat.mul_add (a^(t+1)), Nat.pow_succ a (t+1), Nat.pow_succ (a+h) t]
        ac_rfl
      _ ≤ a^(t+2) + (a+h)^(t+1)*h + ((t+1)*h)*(a+h)^(t+1) :=
        Nat.add_le_add_right (Nat.add_le_add_left tail _) _
      _ = a^(t+2) + ((t+2)*h)*(a+h)^(t+1) := by
        rw [Nat.succ_mul (t+1) h,Nat.add_mul ((t+1)*h) h ((a+h)^(t+1))]
        ac_rfl

private theorem compare_powers (a h d kept total : Nat)
    (step : (a+h)*kept + ((d+1)*h)*total ≤ (a+h)*total) :
    (a+h)^(d+1)*kept ≤ a^(d+1)*total := by
  have scaled :
      (a+h)^(d+1)*kept + (((d+1)*h)*(a+h)^d)*total ≤ (a+h)^(d+1)*total := by
    calc
      _ = ((a+h)*kept + ((d+1)*h)*total)*(a+h)^d := by
        rw [Nat.pow_succ, Nat.add_mul ((a+h)*kept) _ _]; ac_rfl
      _ ≤ ((a+h)*total)*(a+h)^d := Nat.mul_le_mul_right _ step
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have loss := Nat.mul_le_mul_right total (power_loss a h d)
  rw [Nat.add_mul (a^(d+1)) _ total] at loss
  exact Nat.le_of_add_le_add_right (Nat.le_trans scaled loss)

private theorem even_growth (rec : RelativeRecurrence) (d : Nat) :
    ∃ K : Nat, ∀ m, 1≤m → (2*m+1)^(d+1) ≤ K*S (2*m) := by
  obtain ⟨cut,step⟩ := rec (d+1)
  let threshold := cut+8
  let K := (threshold+1)^(d+1)
  refine ⟨K,?_⟩
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    have positive := size_positive (2*m) (by omega)
    by_cases small : 2*m<threshold
    · have h : (2*m+1)^(d+1)≤K := Nat.pow_le_pow_left (by omega) _
      exact Nat.le_trans h (by simpa using Nat.mul_le_mul_left K positive)
    · have big : cut+8 ≤ 2*m := by change ¬ 2*m < cut+8 at small; omega
      obtain ⟨k,hpos,hfit,shrink⟩ := step m (by omega)
      let j := (2*m-k)/2
      have jpos : 1≤j := by dsimp [j]; omega
      have jlt : j<m := by dsimp [j]; omega
      have delta : 2*m-2*j ≤ k+1 := by dsimp [j]; omega
      have add : (2*j+1)+(2*m-2*j)=2*m+1 := by omega
      have smaller := size_mono (n:=2*j) (m:=2*m-k) (by omega) (by dsimp [j]; omega)
      have power := compare_powers (2*j+1) (2*m-2*j) d (S (2*j)) (S (2*m)) (by
        rw [add]
        apply Nat.le_trans _ shrink
        exact Nat.add_le_add (Nat.mul_le_mul_left _ smaller)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ delta)))
      rw [add] at power
      have lower := ih j jlt jpos
      apply Nat.le_of_mul_le_mul_right _ (size_positive (2*j) (by omega))
      calc
        (2*m+1)^(d+1)*S (2*j) ≤ (2*j+1)^(d+1)*S (2*m) := power
        _ ≤ (K*S (2*j))*S (2*m) := Nat.mul_le_mul_right _ lower
        _ = (K*S (2*m))*S (2*j) := by ac_rfl

/-- At *every* sufficiently large size, including odd sizes, S beats each
prescribed coefficient and exponent. This is the eventual-growth reading of
the README's superpolynomial gate lower bound. -/
theorem eventual_growth_of_relative (h : RelativeRecurrence) (c d : Nat) :
    ∃ n₀, ∀ n ≥ n₀, powerBound c d n ≤ S n := by
  obtain ⟨K,growth⟩ := even_growth h d
  have kpos : 0 < K := by
    have lower := growth 1 (by decide)
    have pos : 0 < (2*1+1)^(d+1) := Nat.pow_pos (by decide)
    by_cases hz : K=0
    · simp only [hz,Nat.zero_mul] at lower; omega
    · omega
  let coeff := K*(c*2^d)
  refine ⟨coeff+4,?_⟩
  intro n big
  let m := n/2
  have parity : 2*m ≤ n ∧ n ≤ 2*m+1 := by dsimp [m]; omega
  have scale := Nat.pow_le_pow_left (show n+1 ≤ 2*(2*m+1) by omega) d
  rw [Nat.mul_pow] at scale
  calc
    powerBound c d n = c*(n+1)^d := powerBound_eq ..
    _ ≤ S (2*m) := by
      apply Nat.le_of_mul_le_mul_left _ kpos
      calc
        K*(c*(n+1)^d) ≤ K*(c*(2^d*(2*m+1)^d)) :=
          Nat.mul_le_mul_left K (Nat.mul_le_mul_left c scale)
        _ = coeff*(2*m+1)^d := by dsimp [coeff]; ac_rfl
        _ ≤ (2*m+1)*(2*m+1)^d := Nat.mul_le_mul_right _ (by omega)
        _ = (2*m+1)^(d+1) := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ K*S (2*m) := growth m (by omega)
    _ ≤ S n := size_mono (by omega) parity.1

theorem no_polynomial_size_of_relative (h : RelativeRecurrence) : ¬PolynomialBound S := by
  rintro ⟨c,d,poly⟩
  obtain ⟨n₀,lower⟩ := eventual_growth_of_relative h (c+1) d
  have impossible := Nat.le_trans (lower n₀ (Nat.le_refl _)) (poly n₀)
  simp only [powerBound_eq] at impossible
  have small := Nat.le_of_mul_le_mul_right impossible (Nat.pow_pos (by omega))
  omega

theorem eventual_growth (h : QuarterRecurrence) (c d : Nat) :
    ∃ n₀, ∀ n ≥ n₀, powerBound c d n ≤ S n :=
  eventual_growth_of_relative (relative_of_fraction (by decide : 1 < 4) h) c d

theorem no_polynomial_size (h : QuarterRecurrence) : ¬PolynomialBound S :=
  no_polynomial_size_of_relative (relative_of_fraction (by decide : 1 < 4) h)

private theorem read_word (w : List (Source I)) (x : I → Bool) :
    (List.finRange w.length).map (fun i => (w.get i).read x) = w.map (Source.read x) := by
  apply List.ext_getElem <;> simp [List.get_eq_getElem]

private theorem small_hamilton_of_sat_circuits (h : InPpoly SAT.SAT) : PolynomialBound S := by
  obtain ⟨B,poly,family⟩ := h
  apply (poly.comp poly_word).weaken
  intro n
  let w := formulaWord (instanceOf n)
  obtain ⟨s,bound,c,wins⟩ := family w.length
  apply Nat.le_trans ((size_spec n).2 s ?_) bound
  refine ⟨c.prepend w.get, fun g => ?_⟩
  rw [Net.prepend_run, wins]
  change SAT.SAT ((List.finRange w.length).map (fun i => (w.get i).read g)) ↔ Hamilton n g
  rw [read_word]
  exact hamilton_sat g

private theorem separation_of_relative_recurrence (h : RelativeRecurrence) :
    (¬ (∀ L : Language, InNP L → InPpoly L)) ∧ Complexity.InP ≠ Complexity.InNP := by
  have sat : ¬ InPpoly SAT.SAT := fun family =>
    no_polynomial_size_of_relative h (small_hamilton_of_sat_circuits family)
  exact ⟨fun inclusion => sat (inclusion SAT.SAT sat_inNP),
    fun eq => sat (inP_to_p_poly (eq ▸ sat_inNP))⟩

/-- SAT itself witnesses failure of the nonuniform inclusion under the recurrence. -/
theorem sat_not_inPpoly_of_recurrence (h : QuarterRecurrence) : ¬InPpoly SAT.SAT :=
  fun family => no_polynomial_size h (small_hamilton_of_sat_circuits family)

/-- The conclusion refers to the pinned project's predicates on binary languages. -/
theorem p_ne_np_of_recurrence (h : QuarterRecurrence) : Complexity.InP ≠ Complexity.InNP := by
  intro eq
  exact sat_not_inPpoly_of_recurrence h (inP_to_p_poly (eq ▸ sat_inNP))

/-- A labelled, ordered layout. Positions 0,1 then 2,3 and so on are paired.
The remaining positions stand for singleton vertices. Every choice of disjoint
oriented pairs has such an ordering. The order maps an original vertex to its position. -/
structure PartialPairing (n : Nat) where
  count : Nat
  fits : 2*count ≤ n
  order : Fin n → Fin n
  inverse : Fin n → Fin n
  leftInv : ∀ v, inverse (order v) = v
  rightInv : ∀ v, order (inverse v) = v

private def city (k t : Nat) : Nat := if t < 2*k then t/2 else t-k

/-- A paired entry may go only to its own exit. A paired exit may be entered
only from its own entry. Each arc from one block's last vertex to a different
block's first vertex reads the corresponding raw arc of the smaller graph. -/
def PartialPairing.wire (ρ : PartialPairing n) (e : Arc n) : Source (Arc (n-ρ.count)) :=
  let a := (ρ.order ⟨e.val.1,e.property.1⟩).val
  let b := (ρ.order ⟨e.val.2,e.property.2.1⟩).val
  if a < 2*ρ.count ∧ a%2 = 0 then .fixed (decide (b=a+1))
  else if b < 2*ρ.count ∧ b%2 = 1 then .fixed false
  else arc (n-ρ.count) (city ρ.count a) (city ρ.count b)

/-- Two oriented pairs and a singleton test both forbidden directions and
the free arcs entering and leaving the singleton. -/
example :
    let ρ : PartialPairing 5 := ⟨2, by decide, id, id, fun _ => rfl, fun _ => rfl⟩
    ρ.wire ⟨(0,1),by decide⟩ = .fixed true ∧
    ρ.wire ⟨(1,0),by decide⟩ = .fixed false ∧
    ρ.wire ⟨(4,3),by decide⟩ = .fixed false ∧
    ρ.wire ⟨(1,2),by decide⟩ = arc 3 0 1 ∧
    ρ.wire ⟨(1,4),by decide⟩ = arc 3 0 2 ∧
    ρ.wire ⟨(4,2),by decide⟩ = arc 3 2 1 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

structure GraphCircuit (n : Nat) where
  gates : Nat
  circuit : Net (Arc n) Unit gates

def GraphCircuit.Correct (C : GraphCircuit n) : Prop :=
  ∀ g, C.circuit.run g () = true ↔ Hamilton n g

def GraphCircuit.restrict (C : GraphCircuit n) (ρ : PartialPairing n) :
    GraphCircuit (n-ρ.count) :=
  ⟨C.gates, C.circuit.prepend ρ.wire⟩

abbrev Simplifier := (n : Nat) → GraphCircuit n → GraphCircuit n

/-- The budget reads the pair count, the exact original gate count and the
gate count that the specified simplifier actually leaves on this restriction. -/
def ContractionAt (R : Simplifier) (n : Nat) (budget : Nat → Nat → Nat → Prop) : Prop :=
  ∃ (C : GraphCircuit n) (ρ : PartialPairing n),
    C.Correct ∧ C.gates = S n ∧ (R _ (C.restrict ρ)).Correct ∧
    budget ρ.count C.gates (R _ (C.restrict ρ)).gates

/-- A fixed retained fraction, with sublinearly many pairs. -/
def EarlyFraction (R : Simplifier) (p q : Nat) : Prop :=
  ∃ k : Nat → Nat, Sublinear k ∧ ∃ n₀, ∀ m, n₀ ≤ 2*m →
    ContractionAt R (2*m) (fun pairs original remaining =>
      pairs = k (2*m) ∧ q*remaining ≤ p*original)

/-- The README's early-quarter premise. -/
abbrev EarlyQuarter (R : Simplifier) := EarlyFraction R 1 4

/-- The normalized saving (1 - remaining/original)*(n+1)/(pairs+1) must
eventually exceed each fixed factor at every even size. -/
def RelativeSaving (R : Simplifier) : Prop :=
  ∀ A : Nat, ∃ n₀, ∀ m, n₀ ≤ 2*m →
    ContractionAt R (2*m) (fun k original remaining => 0 < k ∧
      (2*m+1)*remaining + (A*(k+1))*original ≤ (2*m+1)*original)

theorem recurrence_of_early_fraction (R : Simplifier) {p q : Nat} (h : EarlyFraction R p q) :
    FractionRecurrence p q := by
  obtain ⟨k,sub,n₀,step⟩ := h
  refine ⟨k,sub,n₀,?_⟩
  intro m hm
  obtain ⟨C,ρ,_,optimal,correct,count,budget⟩ := step m hm
  let D := R _ (C.restrict ρ)
  have lower : S (2*m-ρ.count) ≤ D.gates := (size_spec _).2 _ ⟨D.circuit, correct⟩
  rw [← count, ← optimal]
  exact Nat.le_trans (Nat.mul_le_mul_left q lower) budget

theorem recurrence_of_early_quarter (R : Simplifier) (h : EarlyQuarter R) : QuarterRecurrence :=
  recurrence_of_early_fraction R h

theorem recurrence_of_relative_saving (R : Simplifier) (h : RelativeSaving R) :
    RelativeRecurrence := by
  intro A
  obtain ⟨cut,step⟩ := h A
  refine ⟨cut,?_⟩
  intro m hm
  obtain ⟨C,ρ,_,optimal,correct,positive,budget⟩ := step m hm
  let D := R _ (C.restrict ρ)
  have low : S (2*m-ρ.count) ≤ D.gates := (size_spec _).2 _ ⟨D.circuit,correct⟩
  have fits := ρ.fits
  refine ⟨ρ.count,positive,by omega,?_⟩
  rw [← optimal]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left (2*m+1) low) _) budget

theorem separation_of_relative_saving (R : Simplifier) (h : RelativeSaving R) :
    (¬ (∀ L : Language, InNP L → InPpoly L)) ∧ Complexity.InP ≠ Complexity.InNP :=
  separation_of_relative_recurrence (recurrence_of_relative_saving R h)

theorem separation_of_early_fraction (R : Simplifier) {p q : Nat} (lt : p < q)
    (h : EarlyFraction R p q) :
    (¬ (∀ L : Language, InNP L → InPpoly L)) ∧ Complexity.InP ≠ Complexity.InNP :=
  separation_of_relative_recurrence (relative_of_fraction lt (recurrence_of_early_fraction R h))

example (R : Simplifier) (h : EarlyFraction R 99 100) : Complexity.InP ≠ Complexity.InNP :=
  (separation_of_early_fraction R (by decide) h).2

/-- The numerical deletion from a quadratic budget when k vertices are lost. -/
theorem quadratic_saving (a k : Nat) : (a+k)^2 = a^2 + k*(2*a+k) := by
  simp only [Nat.pow_two, Nat.two_mul, Nat.mul_add, Nat.add_mul]
  ac_rfl

example (m : Nat) : (2*m)^2 = 4*m^2 := by rw [Nat.mul_pow]

/-- A polynomial numerical model for any prescribed *bounded* relative saving.
For n ≥ d this is n(n-1)⋯(n-d+1) and deleting one vertex saves exactly d/n. -/
private def falling : Nat → Nat → Nat
  | 0, _ => 1
  | d+1, n => falling d n * (n-d)

private theorem falling_step (d a : Nat) :
    (a+1)*falling d a = (a+1-d)*falling d (a+1) := by
  induction d with
  | zero => simp [falling]
  | succ d ih =>
    change (a+1)*(falling d a*(a-d)) =
      (a+1-(d+1))*(falling d (a+1)*(a+1-d))
    rw [← Nat.mul_assoc, ih, show a+1-(d+1) = a-d by omega]
    ac_rfl

private theorem falling_polynomial (d : Nat) : PolynomialBound (falling d) := by
  refine ⟨1,d,fun n => ?_⟩
  simp only [powerBound_eq,Nat.one_mul]
  induction d with
  | zero => simp [falling]
  | succ d ih =>
    exact Nat.mul_le_mul ih (show n-d ≤ n+1 by omega)

private theorem falling_positive (d n : Nat) (h : d ≤ n) : 0 < falling d n := by
  induction d with
  | zero => simp [falling]
  | succ d ih => exact Nat.mul_pos (ih (by omega)) (show 0 < n-d by omega)

/-- With *one* pair and any single fixed factor A, the numerical inequality
in RelativeRecurrence is compatible with an eventually positive polynomial. -/
theorem fixed_factor_allows_polynomial (A : Nat) :
    ∃ T : Nat → Nat, PolynomialBound T ∧ ∃ n₀, ∀ n ≥ n₀,
      0 < T n ∧ (n+1)*T (n-1) + (A*2)*T n ≤ (n+1)*T n := by
  let d := A*2
  refine ⟨falling d,falling_polynomial d,d+2,?_⟩
  intro n hn
  have hd : d ≤ n := by omega
  have cross := falling_step d (n-1)
  rw [show n-1+1 = n by omega] at cross
  have basic : n*falling d (n-1) + d*falling d n = n*falling d n := by
    rw [cross, ← Nat.add_mul, Nat.sub_add_cancel hd]
  have mono : falling d (n-1) ≤ falling d n :=
    Nat.le_of_mul_le_mul_left (c:=n) (by omega) (by omega)
  refine ⟨falling_positive d n hd,?_⟩
  change (n+1)*falling d (n-1) + d*falling d n ≤ (n+1)*falling d n
  rw [Nat.succ_mul n (falling d (n-1)), Nat.succ_mul n (falling d n)]
  omega

theorem np_not_subset_p_poly_of_early_quarter (R : Simplifier) (h : EarlyQuarter R) :
    ¬ (∀ L : Language, Complexity.InNP L → InPpoly L) :=
  fun inclusion =>
    sat_not_inPpoly_of_recurrence (recurrence_of_early_quarter R h) (inclusion SAT.SAT sat_inNP)

theorem p_ne_np_of_early_quarter (R : Simplifier) (h : EarlyQuarter R) :
    Complexity.InP ≠ Complexity.InNP :=
  p_ne_np_of_recurrence (recurrence_of_early_quarter R h)

#check np_not_subset_p_poly_of_early_quarter
#check p_ne_np_of_early_quarter
#print axioms np_not_subset_p_poly_of_early_quarter
#print axioms p_ne_np_of_early_quarter
#check separation_of_early_fraction
#check separation_of_relative_saving
#print axioms separation_of_early_fraction
#print axioms separation_of_relative_saving
#print axioms fixed_factor_allows_polynomial

end SublinearPairSeparation
