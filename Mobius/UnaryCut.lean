import Mobius.TropicalMWIS

/-! A vertex gauge turns the uncut-edge penalty on a bipartite graph into
an ordinary directed s–t cut. Both unary prices are retained at every vertex.
The graph and its objective are the same objects as in TropicalMWIS. -/
namespace Mobius.UnaryCut
open Mobius.TropicalMWIS (Graph Coloring Prices bit sumQ energy optimum)
open Mobius.TourCount (assignments assignments_complete assignments_length)

inductive Node (n : Nat)
  | source | vertex (v : Fin n) | sink
  deriving DecidableEq

structure Arc (n : Nat) where
  tail : Node n
  head : Node n
  cap : Rat

abbrev Network (n : Nat) := List (Arc n)
def nonnegative (a : Network n) : Prop := ∀ e ∈ a, 0 ≤ e.cap

/-- True denotes the source side of an s–t cut. -/
def side (y : Coloring n) : Node n → Bool
  | .source => true
  | .sink => false
  | .vertex v => y v

theorem every_cut (u : Node n → Bool) (hs : u .source=true) (ht : u .sink=false) :
    side (fun v => u (.vertex v)) = u := by
  funext v; cases v <;> simp [side,hs,ht]

def arcPrice (y : Coloring n) (e : Arc n) : Rat :=
  if side y e.tail && !(side y e.head) then e.cap else 0

def cutPrice (a : Network n) (y : Coloring n) : Rat := sumQ a (arcPrice y)

def minimizing (f : Coloring n → Rat) : Coloring n :=
  (assignments n).minOn f (List.ne_nil_of_mem (assignments_complete (fun _ => false)))

def minimumCut (a : Network n) : Rat := cutPrice a (minimizing (cutPrice a))

theorem minimizing_le (f : Coloring n → Rat) (z : Coloring n) : f (minimizing f) ≤ f z :=
  List.apply_minOn_le_of_mem (assignments_complete z)

theorem optimum_spec (g : Graph n) (h : Prices n) :
    optimum g h = energy g h (minimizing (energy g h)) := rfl

def gauge (χ y : Coloring n) : Coloring n := fun v => y v ^^ χ v

theorem gauge_inverse (χ y : Coloring n) : gauge χ (gauge χ y) = y := by
  funext v
  cases hx : χ v <;> cases hy : y v <;> simp [gauge,hx,hy]

def Proper (g : Graph n) (χ : Coloring n) := ∀ e∈g, χ e.1 ≠ χ e.2

def terminals (v : Fin n) (zero one : Rat) : Network n :=
  [⟨.source,.vertex v,zero⟩, ⟨.vertex v,.sink,one⟩]

def pairArcs (e : Fin n × Fin n) : Network n :=
  [⟨.vertex e.1,.vertex e.2,1⟩, ⟨.vertex e.2,.vertex e.1,1⟩]

def network (g : Graph n) (h : Prices n) (χ : Coloring n) : Network n :=
  g.flatMap pairArcs ++ (List.finRange n).flatMap
    (fun v => terminals v (h (v,χ v)) (h (v,!χ v)))

private theorem cut_append (a b : Network n) (y : Coloring n) :
    cutPrice (a++b) y = cutPrice a y+cutPrice b y := by
  simp [cutPrice,sumQ,List.sum_append]

private theorem flat_cost (xs : List α) (net : α → Network n) (v : α → Rat) (y : Coloring n)
    (each : ∀ x∈xs, cutPrice (net x) y = v x) : cutPrice (xs.flatMap net) y = sumQ xs v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,cut_append,each x (by simp),ih (fun a ha => each a (by simp [ha]))]
    rfl

private theorem terminals_cost (v : Fin n) (a b : Rat) (y : Coloring n) :
    cutPrice (terminals v a b) y = if y v then b else a := by
  cases hv : y v <;> simp [cutPrice,sumQ,terminals,arcPrice,side,hv] <;> grind

private theorem pair_cost (e : Fin n × Fin n) (y : Coloring n) :
    cutPrice (pairArcs e) y = bit (y e.1 != y e.2) := by
  cases h : y e.1 <;> cases k : y e.2 <;> simp [pairArcs,cutPrice,sumQ,arcPrice,bit,side,h,k] <;> grind

private theorem gauge_edge (e : Fin n × Fin n) (χ y : Coloring n) (op : χ e.1 ≠ χ e.2) :
    bit (y e.1 != y e.2) = bit (gauge χ y e.1 == gauge χ y e.2) := by
  cases h : χ e.1 <;> cases k : χ e.2 <;> cases p : y e.1 <;> cases q : y e.2 <;>
    simp_all [gauge,bit]

theorem cut_eq_energy (g : Graph n) (h : Prices n) (χ : Coloring n) (proper : Proper g χ)
    (y : Coloring n) : cutPrice (network g h χ) y = energy g h (gauge χ y) := by
  unfold network energy TropicalMWIS.cutCost
  rw [cut_append]
  congr 1
  · apply flat_cost; intro e he
    exact (pair_cost e y).trans (gauge_edge e χ y (proper e he))
  · apply flat_cost; intro v _
    rw [terminals_cost]
    cases h₁ : χ v <;> cases h₂ : y v <;> simp [gauge,h₁,h₂]

theorem energy_eq_cut (g : Graph n) (h : Prices n) (χ : Coloring n) (proper : Proper g χ)
    (z : Coloring n) : energy g h z = cutPrice (network g h χ) (gauge χ z) := by
  rw [cut_eq_energy _ _ _ proper,gauge_inverse]

/-- The minimum over all vertex labels equals the actual capacity of a
minimum s–t cut of the constructed network. -/
theorem mincut_exact (g : Graph n) (h : Prices n) (χ : Coloring n) (proper : Proper g χ) :
    optimum g h = minimumCut (network g h χ) := by
  rw [optimum_spec]
  apply Rat.le_antisymm
  · unfold minimumCut
    rw [cut_eq_energy _ _ _ proper]
    exact minimizing_le _ _
  · unfold minimumCut
    rw [energy_eq_cut _ _ _ proper]
    exact minimizing_le _ _

theorem network_nonnegative (g : Graph n) (h : Prices n) (χ : Coloring n)
    (hp : ∀ p, 0≤h p) : nonnegative (network g h χ) := by
  intro a ha
  rcases List.mem_append.mp ha with edge|vertex
  · obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp edge
    simp [pairArcs] at mem
    rcases mem with rfl|rfl <;> exact (by decide : (0:Rat) ≤ 1)
  · obtain ⟨v,_,mem⟩ := List.mem_flatMap.mp vertex
    simp [terminals] at mem
    rcases mem with rfl|rfl <;> exact hp _

theorem network_arcs (g : Graph n) (h : Prices n) (χ : Coloring n) :
    (network g h χ).length = 2*g.length + 2*n := by
  have two {α} (xs : List α) (f : α → Network n) (len : ∀ x,(f x).length=2) :
      (xs.flatMap f).length = 2*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [len,ih,Nat.mul_succ]; omega
  rw [network,List.length_append,two _ _ (fun _ => rfl),two _ _ (fun _ => rfl),List.length_finRange]

def triangle : Graph 3 := [(0,1),(1,2),(2,0)]

theorem triangle_no_gauge : ¬∃ χ, Proper triangle χ := by
  rintro ⟨χ,p⟩
  have a := p (0,1) (by decide)
  have b := p (1,2) (by decide)
  have c := p (2,0) (by decide)
  change χ 0 ≠ χ 1 at a
  change χ 1 ≠ χ 2 at b
  change χ 2 ≠ χ 0 at c
  cases h : χ 0 <;> cases k : χ 1 <;> cases l : χ 2 <;> simp_all


/-- An explicit index for the vertices whose assignments are enumerated.
The partial inverse permits arbitrary placements of the r deleted vertices. -/
structure Deletion (n r : Nat) where
  vertex : Fin r → Fin n
  index : Fin n → Option (Fin r)
  atVertex : ∀ i, index (vertex i) = some i
  inverse : ∀ v i, index v = some i → vertex i=v

def FreeProper (g : Graph n) (D : Deletion n r) (χ : Coloring n) : Prop :=
  ∀ e∈g, D.index e.1=none → D.index e.2=none → χ e.1 ≠ χ e.2

def lift (D : Deletion n r) (z : Coloring r) (χ y : Coloring n) : Coloring n :=
  fun v => match D.index v with
    | some i => z i
    | none => gauge χ y v

def constantArc (k : Rat) : Network n := [⟨.source,.sink,k⟩]

def priceFixed (v : Fin n) (b : Bool) (χ : Coloring n) : Network n :=
  terminals v (bit (χ v == b)) (bit ((!χ v) == b))

def branchEdge (D : Deletion n r) (z : Coloring r) (χ : Coloring n)
    (e : Fin n × Fin n) : Network n :=
  match D.index e.1, D.index e.2 with
  | none, none => pairArcs e
  | some i, some j => constantArc (bit (z i == z j))
  | none, some i => priceFixed e.1 (z i) χ
  | some i, none => priceFixed e.2 (z i) χ

def branchVertex (h : Prices n) (D : Deletion n r) (z : Coloring r)
    (χ : Coloring n) (v : Fin n) : Network n :=
  match D.index v with
  | some i => constantArc (h (v,z i))
  | none => terminals v (h (v,χ v)) (h (v,!χ v))

def branchNetwork (g : Graph n) (h : Prices n) (D : Deletion n r) (z : Coloring r)
    (χ : Coloring n) : Network n :=
  g.flatMap (branchEdge D z χ) ++ (List.finRange n).flatMap (branchVertex h D z χ)

private theorem constant_cost (k : Rat) (y : Coloring n) :
    cutPrice (constantArc k) y = k := by simp [constantArc,cutPrice,sumQ,arcPrice,side]; grind

private theorem priceFixed_cost (v : Fin n) (b : Bool) (χ y : Coloring n) :
    cutPrice (priceFixed v b χ) y = bit (gauge χ y v == b) := by
  rw [priceFixed,terminals_cost]
  cases h : χ v <;> cases q : y v <;> cases b <;> simp [gauge,h,q]

private theorem branchEdge_cost (D : Deletion n r) (z : Coloring r) (χ y : Coloring n)
    (e : Fin n × Fin n)
    (proper : D.index e.1=none → D.index e.2=none → χ e.1 ≠ χ e.2) :
    cutPrice (branchEdge D z χ e) y = bit (lift D z χ y e.1 == lift D z χ y e.2) := by
  cases h : D.index e.1 with
  | none =>
    cases k : D.index e.2 with
    | none => simpa only [branchEdge,h,k,lift] using (pair_cost e y).trans (gauge_edge e χ y (proper h k))
    | some i => simpa only [branchEdge,h,k,lift] using priceFixed_cost e.1 (z i) χ y
  | some i =>
    cases k : D.index e.2 with
    | none =>
      simp only [branchEdge,h,k,lift,priceFixed_cost]
      rw [BEq.comm]
    | some j => simp only [branchEdge,h,k,lift,constant_cost]

theorem branch_exact (g : Graph n) (h : Prices n) (D : Deletion n r) (χ : Coloring n)
    (proper : FreeProper g D χ) (z : Coloring r) (y : Coloring n) :
    cutPrice (branchNetwork g h D z χ) y = energy g h (lift D z χ y) := by
  unfold branchNetwork energy TropicalMWIS.cutCost
  rw [cut_append]
  congr 1
  · apply flat_cost; intro e he; exact branchEdge_cost D z χ y e (proper e he)
  · apply flat_cost; intro v _
    cases hv : D.index v with
    | some i => simp only [branchVertex,hv,constant_cost,lift]
    | none =>
      simp only [branchVertex,hv,terminals_cost,lift]
      cases hv : y v <;> cases hc : χ v <;> simp [gauge,hv,hc]

theorem lift_original (D : Deletion n r) (χ z : Coloring n) :
    lift D (fun i => z (D.vertex i)) χ (gauge χ z) = z := by
  funext v
  cases h : D.index v with
  | none => simp [lift,h,gauge_inverse]
  | some i => simp [lift,h,D.inverse v i h]

private theorem nonneg_terminal (v : Fin n) {a b : Rat} (ha : 0≤a) (hb : 0≤b) :
    nonnegative (terminals v a b) := by
  intro e he
  simp [terminals] at he
  rcases he with rfl|rfl <;> assumption

private theorem nonneg_constant {q : Rat} (h : 0≤q) : nonnegative (constantArc (n:=n) q) := by
  intro e he
  simp [constantArc] at he
  subst e; exact h

private theorem bit_nonnegative (b : Bool) : (0:Rat) ≤ bit b := by cases b <;> decide

theorem branch_nonnegative (g : Graph n) (h : Prices n) (D : Deletion n r)
    (χ : Coloring n) (z : Coloring r) (hp : ∀ p, 0≤h p) :
    nonnegative (branchNetwork g h D z χ) := by
  intro a ha
  rcases List.mem_append.mp ha with fromEdge|fromVertex
  · obtain ⟨e,_,he⟩ := List.mem_flatMap.mp fromEdge
    have nn : nonnegative (branchEdge D z χ e) := by
      cases h₁ : D.index e.1 <;> cases h₂ : D.index e.2 <;>
        simp only [branchEdge,h₁,h₂]
      · intro a mem
        simp [pairArcs] at mem
        rcases mem with rfl|rfl <;> exact (by decide : (0:Rat)≤1)
      · exact nonneg_terminal _ (bit_nonnegative _) (bit_nonnegative _)
      · exact nonneg_terminal _ (bit_nonnegative _) (bit_nonnegative _)
      · exact nonneg_constant (bit_nonnegative _)
    exact nn _ he
  · obtain ⟨v,_,he⟩ := List.mem_flatMap.mp fromVertex
    have nn : nonnegative (branchVertex h D z χ v) := by
      cases hv : D.index v <;> simp only [branchVertex,hv]
      · exact nonneg_terminal _ (hp _) (hp _)
      · exact nonneg_constant (hp _)
    exact nn _ he

def branches (g : Graph n) (h : Prices n) (D : Deletion n r) (χ : Coloring n) : List (Network n) :=
  (assignments r).map (fun z => branchNetwork g h D z χ)

theorem branch_count (g : Graph n) (h : Prices n) (D : Deletion n r) (χ : Coloring n) :
    (branches g h D χ).length = 2^r := by simp [branches,assignments_length]

def bestBranch (g : Graph n) (h : Prices n) (D : Deletion n r) (χ : Coloring n) : Coloring r :=
  minimizing fun z => minimumCut (branchNetwork g h D z χ)

/-- Minimize the actual network cut separately at each of the 2^r frozen
assignments. A fixed/free edge contributes ordinary unary terminal arcs. -/
theorem deletion_mincut (g : Graph n) (h : Prices n) (D : Deletion n r) (χ : Coloring n)
    (proper : FreeProper g D χ) :
    optimum g h = minimumCut (branchNetwork g h D (bestBranch g h D χ) χ) := by
  rw [optimum_spec]
  apply Rat.le_antisymm
  · unfold minimumCut
    rw [branch_exact _ _ _ _ proper]
    exact minimizing_le _ _
  · let z := minimizing (energy g h)
    let f := fun i => z (D.vertex i)
    let N := branchNetwork g h D f χ
    have first := minimizing_le (fun x => minimumCut (branchNetwork g h D x χ)) f
    have second := minimizing_le (cutPrice N) (gauge χ z)
    have last : cutPrice N (gauge χ z) = energy g h z := by
      rw [show N = branchNetwork g h D f χ from rfl,branch_exact _ _ _ _ proper,lift_original]
    rw [last] at second
    exact Rat.le_trans first second


theorem branch_arcs (g : Graph n) (h : Prices n) (D : Deletion n r) (χ : Coloring n)
    (z : Coloring r) : (branchNetwork g h D z χ).length ≤ 2*g.length+2*n := by
  have bound {α} (xs : List α) (f : α → Network n) (size : ∀ x,(f x).length≤2) :
      (xs.flatMap f).length ≤ 2*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
      have := size x
      omega
  have edges := bound g (branchEdge D z χ) (fun e => by
    cases i : D.index e.1 <;> cases j : D.index e.2 <;> simp [branchEdge,i,j,constantArc,priceFixed,pairArcs,terminals])
  have vertices := bound (List.finRange n) (branchVertex h D z χ) (fun v => by
    cases i : D.index v <;> simp [branchVertex,i,constantArc,terminals])
  rw [List.length_finRange] at vertices
  simpa only [branchNetwork,List.length_append] using Nat.add_le_add edges vertices

/-- Even with both unary prices zero, no vertexwise gauge transforms the
whole triangle objective into the directed cut of this construction. -/
theorem triangle_energy_obstruction :
    ¬∃ χ : Coloring 3, ∀ y, cutPrice (network triangle (fun _ => 0) χ) y =
      energy triangle (fun _ => 0) (gauge χ y) := by
  rintro ⟨χ,all⟩
  let zero : Coloring 3 := fun _ => false
  have cut0 : cutPrice (network triangle (fun _ => 0) χ) zero = 0 := by
    change cutPrice (network triangle (fun _ => 0) (fun _ => false)) (fun _ => false) = 0
    decide +kernel
  have impossible (z : Coloring 3) : energy triangle (fun _ => 0) z ≠ 0 := by
    have unary : sumQ (List.finRange 3) (fun _ => (0:Rat)) = 0 := by decide +kernel
    unfold energy
    rw [unary]
    cases a : z 0 <;> cases b : z 1 <;> cases c : z 2 <;>
      simp [TropicalMWIS.cutCost,triangle,sumQ,bit,a,b,c] <;> grind
  exact impossible _ ((all zero).symm.trans cut0)

end Mobius.UnaryCut
