import Mobius.TourCount
import Mobius.RigidityResidual

/-!
The four tensor legs select actual variables of ordinary CNF formulas.
Two binary clauses implement each wire, and no auxiliary assignment is
introduced. The boundary histogram counts satisfying assignments before
closing the eight equalities. An integer tensor may be substituted into
that histogram without assuming independence of the four legs.
-/
namespace Mobius.BoundarySemantics

open Complexity.SAT
abbrev B := BitVec 4

structure Port where
  b₀ : Nat
  b₁ : Nat
  b₂ : Nat
  b₃ : Nat
  deriving Repr

structure Ports where
  x : Port
  y : Port
  u : Port
  v : Port
  deriving Repr

structure Key where
  x : B
  y : B
  u : B
  v : B
  deriving DecidableEq, Repr

private def pack (a b c d : Bool) : B := BitVec.ofBoolListLE [a,b,c,d]

def Port.read (p : Port) (a : Assignment) : B := pack (a p.b₀) (a p.b₁) (a p.b₂) (a p.b₃)

def Ports.read (p : Ports) (a : Assignment) : Key :=
  ⟨p.x.read a, p.y.read a, p.u.read a, p.v.read a⟩

/-- The two clauses express logical equivalence of the named variables. -/
def equalBits (i j : Nat) : CNF :=
  [[⟨i,false⟩,⟨j,true⟩], [⟨i,true⟩,⟨j,false⟩]]

def equalPorts (p q : Port) : CNF :=
  equalBits p.b₀ q.b₀ ++ equalBits p.b₁ q.b₁ ++
  equalBits p.b₂ q.b₂ ++ equalBits p.b₃ q.b₃

def glue (f : CNF) (p : Ports) : CNF :=
  f ++ equalPorts p.x p.v ++ equalPorts p.y p.u

@[simp] theorem equal_bits_eval (a : Assignment) (i j : Nat) :
    evalCNF a (equalBits i j) = (a i == a j) := by
  cases h : a i <;> cases g : a j <;>
    simp [equalBits,evalCNF,evalClause,evalLiteral,h,g]

private theorem four_eq (a b c d e f g h : Bool) :
    ((((a == e) && (b == f)) && (c == g)) && (d == h)) =
      (pack a b c d == pack e f g h) := by
  revert a b c d e f g h; decide

@[simp] theorem eval_append (a : Assignment) (f g : CNF) :
    evalCNF a (f++g) = (evalCNF a f && evalCNF a g) := List.all_append

@[simp] theorem equal_ports_eval (a : Assignment) (p q : Port) :
    evalCNF a (equalPorts p q) = (p.read a == q.read a) := by
  simp only [equalPorts,eval_append,equal_bits_eval,Port.read,four_eq]

def closes (q : Key) : Bool := (q.x == q.v) && (q.y == q.u)

theorem glue_eval (a : Assignment) (f : CNF) (p : Ports) :
    evalCNF a (glue f p) = (evalCNF a f && closes (p.read a)) := by
  simp [glue, closes,Ports.read]

theorem glue_length (f : CNF) (p : Ports) : (glue f p).length = f.length+16 := by
  simp [glue,equalPorts,equalBits]

private theorem three_append {f g : CNF} (h : IsThreeCNF f) (j : IsThreeCNF g) :
    IsThreeCNF (f++g) := fun c hc => (List.mem_append.mp hc).elim (h c) (j c)

private theorem bit_three (i j : Nat) : IsThreeCNF (equalBits i j) := by
  intro c hc
  simp [equalBits] at hc
  rcases hc with rfl | rfl <;> simp

private theorem ports_three (p q : Port) : IsThreeCNF (equalPorts p q) :=
    three_append (three_append (three_append (bit_three _ _) (bit_three _ _))
      (bit_three _ _)) (bit_three _ _)

theorem glue_threeCNF (f : CNF) (p : Ports) (h : IsThreeCNF f) :
    IsThreeCNF (glue f p) := three_append (three_append h (ports_three _ _)) (ports_three _ _)

abbrev Finite (n : Nat) := Fin n → Bool

/-- Same finite witness convention as TourCount.countWith. -/
def assignment (w : Finite n) (i : Nat) : Bool := if h : i<n then w ⟨i,h⟩ else false

def models (n : Nat) (f : CNF) :=
  (Mobius.TourCount.assignments n).filter (fun w => evalCNF (assignment w) f)

theorem models_count (n : Nat) (f : CNF) :
    (models n f).length = Mobius.TourCount.countWith n f := by
  change ((Mobius.TourCount.assignments n).filter (fun w => evalCNF (assignment w) f)).length =
    (Mobius.TourCount.assignments n).countP (fun w => evalCNF (assignment w) f)
  rw [List.countP_eq_length_filter]

/-- Every element is one satisfying assignment's four boundary values.
Repeated boundary values represent different satisfying assignments. -/
def sample (n : Nat) (f : CNF) (p : Ports) :=
  (models n f).map (fun w => p.read (assignment w))

def fiber (n : Nat) (f : CNF) (p : Ports) (q : Key) : Nat :=
    (sample n f p).count q

private def distinct : List Key → List Key
  | [] => []
  | q::qs => if q ∈ qs then distinct qs else q::distinct qs

private theorem mem_distinct (k : Key) (qs : List Key) : k ∈ distinct qs ↔ k ∈ qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases h : q ∈ qs <;> simp_all [distinct] <;> grind

private theorem distinct_nodup (qs : List Key) : (distinct qs).Nodup := by
  induction qs with
  | nil => simp [distinct]
  | cons q qs ih => by_cases h : q ∈ qs <;> simp [distinct,h,ih,mem_distinct]

def keys (n : Nat) (f : CNF) (p : Ports) := distinct (sample n f p)

def sumI {α} (xs : List α) (f : α → Int) := (xs.map f).sum

/-- Cache assignment counts once per distinct observed boundary. -/
def contract (n : Nat) (f : CNF) (p : Ports) (w : Key → Int) :=
    sumI (keys n f p) (fun q => (fiber n f p q : Int)*w q)

private theorem sum_add {α} (xs : List α) (f g : α → Int) :
    sumI xs (fun x => f x+g x) = sumI xs f+sumI xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [sumI]; omega

private theorem sum_zero {α} (xs : List α) : sumI xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [sumI]

private theorem sum_delta {α : Type} [DecidableEq α] (qs : List α) (q : α) (v : Int) (h : qs.Nodup) :
    sumI qs (fun k => if k=q then v else 0) = if q ∈ qs then v else 0 := by
  induction qs with
  | nil => simp [sumI]
  | cons a qs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp h
    change (if a=q then v else 0) + sumI qs (fun k => if k=q then v else 0) = _
    rw [ih tail]
    by_cases eq : a=q <;> simp_all [eq_comm]

private theorem fiber_partition {α : Type} [DecidableEq α] (xs qs : List α) (w : α → Int)
    (h : qs.Nodup) (cover : ∀ q ∈ xs, q ∈ qs) :
    sumI qs (fun q => (xs.count q : Int) * w q) = sumI xs w := by
  induction xs with
  | nil => simp [sumI,show (qs.map (fun _ => (0:Int))).sum=0 from sum_zero qs]
  | cons a xs ih =>
    have mem := cover a (by simp)
    have re (q : α) : (((a::xs).count q : Nat):Int)*w q =
        (if q=a then w a else 0) + (xs.count q : Int)*w q := by
      by_cases eq : q=a
      · subst q; simp [Int.add_mul,Int.add_comm]
      · simp [eq, Ne.symm eq]
    rw [show (fun q => _) = _ from funext re,sum_add,sum_delta _ _ _ h,ite_eq_left mem,
      ih (fun q hq => cover q (by simp [hq]))]
    rfl

theorem contract_unfold (n : Nat) (f : CNF) (p : Ports) (w : Key → Int) :
    contract n f p w = sumI (sample n f p) w := by
  apply fiber_partition
  · exact distinct_nodup _
  · intro q h; exact (mem_distinct _ _).mpr h

def W (q : Key) : Int := if closes q then 1 else 0

private theorem indicator_count {α} (xs : List α) (g : α → Bool) :
    sumI xs (fun x => if g x then 1 else 0) = (xs.countP g : Int) := by
  induction xs with
  | nil => simp [sumI]
  | cons x xs ih => cases h : g x <;> simp_all [sumI,Int.add_comm]

/-- Ordinary #SAT of the formula with eight equalities, with any declared
variable count, equals the boundary histogram contracted against SWAP. -/
theorem countWith_crossing (n : Nat) (f : CNF) (p : Ports) :
    contract n f p W = (Mobius.TourCount.countWith n (glue f p) : Int) := by
  rw [contract_unfold]
  unfold sample sumI W
  simp only [List.map_map,Function.comp_def]
  rw [show ((models n f).map (fun w => if closes (p.read (assignment w)) then (1:Int) else 0)).sum =
    _ from indicator_count (models n f) (fun w => closes (p.read (assignment w)))]
  rw [← models_count,List.countP_eq_length_filter]
  unfold models
  rw [List.filter_filter]
  simp only [glue_eval,Bool.and_comm]

abbrev Phase := B → B → Bool

def R (r : Phase) (q : Key) := Mobius.RankTradeGauge.kernel r q.x q.y q.u q.v
def C (c : Phase) (q : Key) := Mobius.RankTradeGauge.kernel c q.x q.u q.y q.v

/-- The correction is an outer product across (x,v) | (y,u). -/
def correctionLeg (d : B) (s : B → Bool) (x v : B) : Int :=
    if v = x ^^^ d then Mobius.RankTradeGauge.sig (s x) else 0

def correction (d : B) (s t : B → Bool) (q : Key) :=
    correctionLeg d s q.x q.v * correctionLeg d t q.y q.u

private theorem subsumes (r c : Phase) (d : B) (s t : B → Bool)
    (h : ∀ x y u v : B, Mobius.RankTradeGauge.physical r c x y u v =
      if u = y ^^^ d ∧ v = x ^^^ d then
         2 * Mobius.RankTradeGauge.sig (s x) * Mobius.RankTradeGauge.sig (t y) else 0)
    (q : Key) : R r q + C c q - 2*correction d s t q = 2*W q := by
  have hp := h q.x q.y q.u q.v
  change R r q + C c q - 2*(if q.x=q.v ∧ q.y=q.u then 1 else 0) = _ at hp
  by_cases he : q.u=q.y ^^^ d <;> by_cases hv : q.v=q.x ^^^ d <;>
    simp [he,hv,correction,correctionLeg,W,closes,Int.mul_assoc] at hp ⊢ <;> omega

private theorem distribute {α} (xs : List α) (f g h k : α → Int)
    (rel : ∀ x, f x + g x - 2*h x = 2*k x) :
    sumI xs f + sumI xs g - 2*sumI xs h = 2*sumI xs k := by
  induction xs with
  | nil => simp [sumI]
  | cons x xs ih =>
    have hx := rel x
    change (f x+sumI xs f)+(g x+sumI xs g)-2*(h x+sumI xs h) = 2*(k x+sumI xs k)
    omega

/-- A single set of correction parameters works for every ordinary input
formula and every choice of boundary variables. -/
theorem optimal_count_reconstruction (r c : Phase) (opt : Mobius.TwoPhases.failures r c = 256) :
    ∃ (d : B) (s t : B → Bool), d ≠ 0 ∧ ∀ (n : Nat) (f : CNF) (p : Ports),
      contract n f p (R r) + contract n f p (C c) - 2*contract n f p (correction d s t) =
        2*(Mobius.TourCount.countWith n (glue f p) : Int) := by
  obtain ⟨d,s,t,h⟩ := Mobius.Rigidity.Residual.local_crossing r c opt
  refine ⟨d.val,s,t,d.property,?_⟩
  intro n f p
  rw [← countWith_crossing]
  simp only [contract_unfold]
  exact distribute _ _ _ _ _ (subsumes r c d.val s t h)

theorem canonical_tours (f : CNF) (p : Ports) (source : Bool) :
    (Mobius.TourCount.tours (glue f p) source (!source) : Int) =
      contract (variableBound (glue f p)) f p W := by
  rw [countWith_crossing,Mobius.TourCount.transfer_entry,ite_eq_left rfl]
  rfl

end Mobius.BoundarySemantics

namespace Mobius.BoundarySemantics

open Complexity.SAT

/-- Shift a private CNF block into a disjoint interval of variable names. -/
def rename (n : Nat) (f : CNF) : CNF :=
    f.map (List.map fun l => { l with var := n+l.var })

def Port.shift (n : Nat) (p : Port) : Port := ⟨n+p.b₀,n+p.b₁,n+p.b₂,n+p.b₃⟩
def Port.Below (p : Port) (n : Nat) : Prop := p.b₀<n ∧ p.b₁<n ∧ p.b₂<n ∧ p.b₃<n

def joined (n : Nat) (f g : CNF) (x y v u : Port) : CNF :=
    glue (f ++ rename n g) ⟨x,y,u.shift n,v.shift n⟩

theorem joined_threeCNF (n : Nat) (f g : CNF) (x y v u : Port)
    (hf : IsThreeCNF f) (hg : IsThreeCNF g) : IsThreeCNF (joined n f g x y v u) := by
  apply glue_threeCNF
  apply three_append hf
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  simpa using hg d hd

private theorem rename_eval (n : Nat) (g : CNF) (a : Assignment) :
    evalCNF a (rename n g) = evalCNF (fun i => a (n+i)) g := by
  simp [rename,evalCNF,evalClause,evalLiteral,List.all_map,Function.comp_def]
  rfl

private def joinAssignment (l : Finite n) (r : Finite m) : Finite (n+m) := Fin.addCases l r

private theorem read_left (l : Finite n) (r : Finite m) (i : Nat) (hi : i<n) :
    assignment (joinAssignment l r) i = assignment l i := by
  simp only [assignment,hi,show i<n+m by omega,dite_true]
  exact Fin.addCases_left (motive := fun _ => Bool) (left := l) (right := r) ⟨i,hi⟩

private theorem read_right (l : Finite n) (r : Finite m) (i : Nat) :
    assignment (joinAssignment l r) (n+i) = assignment r i := by
  by_cases hi : i<m
  · simp only [assignment,hi,show n+i<n+m by omega,dite_true]
    exact Fin.addCases_right (motive := fun _ => Bool) (left := l) (right := r) ⟨i,hi⟩
  · simp [assignment,hi,show ¬ n+i<n+m by omega]

private theorem port_left (l : Finite n) (r : Finite m) (p : Port) (h : p.Below n) :
    p.read (assignment (joinAssignment l r)) = p.read (assignment l) := by
  obtain ⟨a,b,c,d⟩ := h
  simp only [Port.read, read_left l r _ a,read_left l r _ b,read_left l r _ c,read_left l r _ d]

private theorem port_right (l : Finite n) (r : Finite m) (p : Port) :
    (p.shift n).read (assignment (joinAssignment l r)) = p.read (assignment r) := by
  simp only [Port.shift,Port.read,read_right]

private def iface (x y : Port) (a : Assignment) := (x.read a, y.read a)

private theorem joined_eval (f g : CNF) (x y v u : Port) (l : Finite n) (r : Finite m)
    (hf : Complexity.ThreeSAT.CNFBelow n f) (hx : x.Below n) (hy : y.Below n) :
    evalCNF (assignment (joinAssignment l r)) (joined n f g x y v u) =
      ((evalCNF (assignment l) f && evalCNF (assignment r) g) &&
        (iface x y (assignment l) == iface v u (assignment r))) := by
  have left := Complexity.ThreeSAT.evalCNF_agrees hf (read_left l r)
  have right := rename_eval n g (assignment (joinAssignment l r))
  rw [show (fun i => assignment (joinAssignment l r) (n+i)) = assignment r from funext (read_right l r)] at right
  simp only [joined,glue_eval,eval_append,left,right,closes,Ports.read,port_left l r x hx,
    port_left l r y hy,port_right,iface]
  rfl

private theorem join_injective (l x : Finite n) (r y : Finite m)
    (h : joinAssignment l r = joinAssignment x y) : l=x ∧ r=y := by
  constructor
  · funext i
    simpa [joinAssignment] using congrFun h (Fin.castAdd m i)
  · funext i
    simpa [joinAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd n i)

/-- Keys for two independent assignment lists enumerate exactly the same
declared witnesses as the encoded formula with the second block renamed. -/
private theorem assignment_product (n m : Nat) :
    (Mobius.TourCount.assignments (n+m)).Perm
      ((Mobius.TourCount.assignments n).flatMap fun l =>
        (Mobius.TourCount.assignments m).map (joinAssignment l)) := by
  apply (List.perm_ext_iff_of_nodup (Mobius.TourCount.assignments_nodup _) ?_).mpr
  · intro w
    constructor
    · intro _
      let l := fun i : Fin n => w (Fin.castAdd m i)
      let r := fun i : Fin m => w (Fin.natAdd n i)
      have eq : joinAssignment l r = w := by
        funext i
        induction i using Fin.addCases with
        | left i => simp [joinAssignment,l]
        | right i => simp [joinAssignment,r,Fin.addCases_right]
      exact List.mem_flatMap.mpr ⟨l,Mobius.TourCount.assignments_complete l,
        List.mem_map.mpr ⟨r,Mobius.TourCount.assignments_complete r,eq⟩⟩
    · intro _; exact Mobius.TourCount.assignments_complete w
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro l _
      apply (Mobius.TourCount.assignments_nodup m).map
      intro a b neq eq; exact neq (join_injective _ _ _ _ eq).2
    · apply (Mobius.TourCount.assignments_nodup n).imp
      intro l r neq w hw z hz eq
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
      exact neq (join_injective _ _ _ _ eq).1

/-- List of the eight visible boundary bits, one entry per satisfying
assignment of a single block. Private assignments with the same interface
contribute separately. -/
def interfaces (n : Nat) (f : CNF) (x y : Port) :=
    (models n f).map (fun w => iface x y (assignment w))

/-- Dot product of the two interface multiplicities, with the left side
represented by a list containing one item per private assignment. -/
def joinCount (n m : Nat) (f g : CNF) (x y v u : Port) : Nat :=
    ((interfaces n f x y).map (fun q => (interfaces m g v u).count q)).sum

private theorem count_matches (rs : List (Finite m)) (g : CNF) (v u : Port) (k : B × B) :
    rs.countP (fun r => evalCNF (assignment r) g && (k == iface v u (assignment r))) =
      (((rs.filter (fun r => evalCNF (assignment r) g)).map
        (fun r => iface v u (assignment r))).count k) := by
  rw [List.count_eq_countP,List.countP_map,List.countP_filter]
  apply List.countP_congr
  intro r _
  by_cases eq : k=iface v u (assignment r)
  · simp [eq]
  · simp [eq,Ne.symm eq]

private theorem left_filter_sum {α} (xs : List α) (g : α → Bool) (a : α → Nat) :
    (xs.map (fun x => if g x then a x else 0)).sum = ((xs.filter g).map a).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : g x <;> simp_all

/-- The count of the actual joined 3-CNF is the product-sum of the two
independently computed boundary histograms. Closing the eight wires has
a unique expansion of every compatible pair of private assignments. -/
theorem joined_count (n m : Nat) (f g : CNF) (x y v u : Port)
    (hf : Complexity.ThreeSAT.CNFBelow n f) (hx : x.Below n) (hy : y.Below n) :
    Mobius.TourCount.countWith (n+m) (joined n f g x y v u) =
      joinCount n m f g x y v u := by
  let ls := Mobius.TourCount.assignments n
  let rs := Mobius.TourCount.assignments m
  let ok := fun w : Finite (n+m) => evalCNF (assignment w) (joined n f g x y v u)
  change (Mobius.TourCount.assignments (n+m)).countP ok = _
  rw [(assignment_product n m).countP_eq ok, List.countP_flatMap]
  have one (l : Finite n) : (rs.map (joinAssignment l)).countP ok =
      if evalCNF (assignment l) f then (interfaces m g v u).count (iface x y (assignment l)) else 0 := by
    rw [List.countP_map]
    have eval (r : Finite m) := joined_eval f g x y v u l r hf hx hy
    by_cases yes : evalCNF (assignment l) f
    · rw [ite_eq_left yes]
      have he : ok ∘ joinAssignment l = fun r => evalCNF (assignment r) g &&
          (iface x y (assignment l) == iface v u (assignment r)) := by
        funext r
        simpa only [ok,Function.comp_apply,yes,Bool.true_and] using eval r
      rw [he]
      exact count_matches rs g v u _
    · rw [ite_eq_right yes]
      apply List.countP_eq_zero.mpr
      intro r _ h
      have no := eval r
      simp [Bool.eq_false_iff.mpr yes] at no
      exact Bool.false_ne_true (no.symm.trans h)
  change (ls.map (fun l => (rs.map (joinAssignment l)).countP ok)).sum = _
  rw [show (fun l => _) = _ from funext one,left_filter_sum]
  simp [joinCount,interfaces,models,ls,List.map_map,Function.comp_def]

end Mobius.BoundarySemantics

namespace Mobius.BoundarySemantics

open Complexity.SAT

def Port.bound (p : Port) :=
    max (max (p.b₀+1) (p.b₁+1)) (max (p.b₂+1) (p.b₃+1))

/-- The canonical declaration also includes unused interface variables. -/
def width (f : CNF) (p q : Port) := max (variableBound f) (max p.bound q.bound)

private theorem bound_append (f g : CNF) :
    variableBound (f++g) = max (variableBound f) (variableBound g) := by
  induction f with
  | nil => simp [variableBound]
  | cons c f ih => simp [variableBound,ih,Nat.max_assoc]

private theorem eqbit_bound (i j : Nat) :
    variableBound (equalBits i j) = max (i+1) (j+1) := by
  simp [equalBits,variableBound,clauseBound]

private theorem port_bound (p q : Port) :
    variableBound (equalPorts p q) = max p.bound q.bound := by
  simp only [equalPorts,bound_append,eqbit_bound,Port.bound]
  ac_rfl

private theorem shift_bound (n : Nat) (p : Port) : (p.shift n).bound = n+p.bound := by
  simp only [Port.bound,Port.shift]; omega

private theorem shifted_clause (n : Nat) (c : Clause) :
    max n (clauseBound (c.map (fun l => {l with var := n+l.var}))) = n+clauseBound c := by
  induction c with
  | nil => simp [clauseBound]
  | cons l cs ih => simp only [List.map_cons,clauseBound]; omega

private theorem shifted_formula (n : Nat) (g : CNF) :
    max n (variableBound (rename n g)) = n+variableBound g := by
  induction g with
  | nil => simp [rename,variableBound]
  | cons c g ih =>
    have h := shifted_clause n c
    change max n (max (clauseBound (c.map (fun l => {l with var := n+l.var})))
      (variableBound (rename n g))) = n+max (clauseBound c) (variableBound g)
    omega

private theorem scope (f : CNF) (p q : Port) :
    Complexity.ThreeSAT.CNFBelow (width f p q) f ∧ p.Below (width f p q) ∧
      q.Below (width f p q) := by
  constructor
  · intro c hc l hl
    have := literal_lt_variableBound hc hl
    unfold width; omega
  · unfold Port.Below width Port.bound; omega

theorem joined_variableBound (f g : CNF) (x y v u : Port) :
    variableBound (joined (width f x y) f g x y v u) = width f x y + width g v u := by
  let n := width f x y
  have hf : variableBound f ≤ n := Nat.le_max_left ..
  have hx : x.bound ≤ n := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have hy : y.bound ≤ n := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
  have sr := shifted_formula n g
  change variableBound (joined n f g x y v u) = n+width g v u
  simp only [joined,glue,bound_append,port_bound,shift_bound]
  unfold width
  omega

/-- Without bound hypotheses or extra declared variables, the ordinary
#SAT count is the contraction of the independent eight-bit interfaces. -/
theorem joined_sharp (f g : CNF) (x y v u : Port) :
    Mobius.TourCount.sharp (joined (width f x y) f g x y v u) =
      joinCount (width f x y) (width g v u) f g x y v u := by
  rw [Mobius.TourCount.sharp,joined_variableBound]
  obtain ⟨hf,hx,hy⟩ := scope f x y
  exact joined_count _ _ f g x y v u hf hx hy

end Mobius.BoundarySemantics

namespace Mobius.BoundarySemantics

open Complexity.SAT

/-- One entry of a private block's 16 by 16 boundary histogram. -/
def interfaceCount (n : Nat) (f : CNF) (x y : Port) (q : B × B) :=
    (interfaces n f x y).count q

private theorem cast_sum {α} (xs : List α) (g : α → Nat) :
    (((xs.map g).sum : Nat) : Int) = sumI xs (fun x => (g x : Int)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [sumI]

/-- A fixed 256-entry dot product gives ordinary #SAT of the joined formula.
Each operand depends only on its own formula and its own ports. -/
theorem joined_sharp_dot (f g : CNF) (x y v u : Port) :
    (Mobius.TourCount.sharp (joined (width f x y) f g x y v u) : Int) =
      sumI Mobius.SignObstruction.shifts (fun q =>
        (interfaceCount (width f x y) f x y q : Int) *
        (interfaceCount (width g v u) g v u q : Int)) := by
  rw [joined_sharp,joinCount,cast_sum]
  symm
  apply fiber_partition
  · exact Mobius.SignObstruction.shifts_nodup
  · intro q _; exact Mobius.SignObstruction.shifts_complete q

end Mobius.BoundarySemantics
