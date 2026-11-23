import Mobius.PortGraphGeometry
import Mobius.TourCount

/-! A finite graph of NOT wires in one common direct-sum address space.
Each vertex owns a three-dimensional station. An edge reads the actual
tagged addresses of its thirteen internal tests. For every choice of all
four station bits, a single pair of global tables attains every edge
minimum. The resulting unrestricted optimum is the complement of Max-Cut. -/
namespace Mobius.PortGraph

open Mobius.PortGeometry (Station)
open Mobius.PortGraphGeometry (Edge Addr endpoint endCell address vertexAddress)
open Mobius.OneInThree (Quad NotBoundary Phase readNot notRow notCol notInternalCost internalNot)
open Mobius.TwoPhases (TaggedCell corners halfCells)
open Mobius.SignObstruction (B Rectangle total)

abbrev Coordinate (n : Nat) := Fin n → Station

structure Tables (n : Nat) where
  row : Coordinate n → Coordinate n → Bool
  col : Coordinate n → Coordinate n → Bool

def Tables.value (t : Tables n) (a : Addr n) : Bool :=
  if a.1 then t.col a.2.1 a.2.2 else t.row a.2.1 a.2.2

def Tables.local (t : Tables n) (e : Edge n) (tag : Bool) : Phase :=
  fun x y => t.value (address e (tag,x,y))

def stationQuad (t : Tables n) (v : Fin n) : Quad :=
  ⟨t.value (vertexAddress v 0), t.value (vertexAddress v 1),
   t.value (vertexAddress v 2), t.value (vertexAddress v 3)⟩

def edgeCost (t : Tables n) (e : Edge n) : Nat := notInternalCost (t.local e false) (t.local e true)

def graphCost (edges : List (Edge n)) (t : Tables n) : Nat := (edges.map (edgeCost t)).sum

/-- The concrete list of four-corner XOR tests in the common address space. -/
def placedSquare (e : Edge n) (r : Rectangle) : List (Addr n) :=
  Mobius.PortGraphGeometry.coordCorners (Mobius.PortGraphGeometry.xCoord e r.1)
    (Mobius.PortGraphGeometry.yCoord e r.2.1) (Mobius.PortGraphGeometry.stepCoord e r.2.2)

def selectedSquares (es : List (Edge n)) : List (List (Addr n)) :=
  es.flatMap fun e => internalNot.map (placedSquare e)

theorem selected_length (es : List (Edge n)) : (selectedSquares es).length = 13*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change ((internalNot.map (placedSquare e)) ++ selectedSquares es).length = _
    rw [List.length_append,List.length_map,show internalNot.length = 13 by decide,ih,List.length_cons]
    omega

def failuresOn (t : Tables n) (squares : List (List (Addr n))) : Nat :=
  squares.countP (fun cs => !total t.value cs)

private def cornerBit (q : Quad) (i : Fin 4) : Bool := match i.val with
  | 0 => q.a
  | 1 => q.b
  | 2 => q.c
  | _ => q.d

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide

private theorem eq_quad {p q : Quad} (h : ∀ j, cornerBit p j = cornerBit q j) : p = q := by
  obtain ⟨a,b,c,d⟩ := p
  obtain ⟨w,x,y,z⟩ := q
  have ha : a=w := h 0
  have hb : b=x := h 1
  have hc : c=y := h 2
  have hd : d=z := h 3
  cases ha; cases hb; cases hc; cases hd; rfl

private theorem station_bit (t : Tables n) (v : Fin n) (i : Fin 4) :
    cornerBit (stationQuad t v) i = t.value (vertexAddress v i) := by
  rcases four i with rfl | rfl | rfl | rfl <;> rfl

private def tagged (r c : Phase) (p : TaggedCell) : Bool :=
  if p.1 then c p.2.1 p.2.2 else r p.2.1 p.2.2

private def portAt (p : NotBoundary) (side : Bool) : Quad := if side then p.twelfth else p.first

private theorem tagged_end (r c : Phase) (side : Bool) (j : Fin 4) :
    tagged r c (endCell side j) = cornerBit (portAt (readNot r c) side) j := by
  rcases four j with rfl | rfl | rfl | rfl <;> cases side <;> rfl

private theorem tagged_pull (t : Tables n) (e : Edge n) (p : TaggedCell) :
    tagged (t.local e false) (t.local e true) p = t.value (address e p) := by
  obtain ⟨b,x,y⟩ := p
  cases b <;> rfl

private def ports (Q : Fin n → Quad) (e : Edge n) : NotBoundary := ⟨Q e.lo,Q e.hi⟩

private theorem port_endpoint (Q : Fin n → Quad) (e : Edge n) (side : Bool) :
    portAt (ports Q e) side = Q (endpoint e side) := by cases side <;> rfl

/-- The same four station values are seen at every incidence, including
    when the same vertex is a left endpoint in one wire and a right in another. -/
theorem edge_reads (t : Tables n) (e : Edge n) :
    readNot (t.local e false) (t.local e true) = ports (stationQuad t) e := by
  have side (s : Bool) : portAt (readNot (t.local e false) (t.local e true)) s =
      stationQuad t (endpoint e s) := by
    apply eq_quad
    intro j
    rw [← tagged_end,tagged_pull,Mobius.PortGraphGeometry.address_endCell,station_bit]
  have left := side false
  have right := side true
  cases h : readNot (t.local e false) (t.local e true) with
  | mk first last =>
    rw [h] at left right
    change first = stationQuad t e.lo at left
    change last = stationQuad t e.hi at right
    cases left; cases right; rfl

private def wireValue (Q : Fin n → Quad) (e : Edge n) : TaggedCell → Bool :=
  tagged (notRow (ports Q e)) (notCol (ports Q e))

private theorem wire_end (Q : Fin n → Quad) (e : Edge n) (s : Bool) (j : Fin 4) :
    wireValue Q e (endCell s j) = cornerBit (Q (endpoint e s)) j := by
  unfold wireValue
  rw [tagged_end,Mobius.OneInThree.not_extension_boundary,port_endpoint]

/-- A finite address registry. Vertex entries are included even when
    no edge is incident. Duplicate edges need no extra assumption. -/
private inductive Source (n : Nat)
  | vertex (v : Fin n) (j : Fin 4)
  | wire (e : Edge n) (p : TaggedCell)

private def Source.addr : Source n → Addr n
  | .vertex v j => vertexAddress v j
  | .wire e p => address e p

private def Source.bit (Q : Fin n → Quad) : Source n → Bool
  | .vertex v j => cornerBit (Q v) j
  | .wire e p => wireValue Q e p

private def Source.valid : Source n → Prop
  | .vertex _ _ => True
  | .wire _ p => p ∈ halfCells

private theorem vertex_wire (Q : Fin n → Quad) (e : Edge n) (p : TaggedCell)
    (v : Fin n) (j : Fin 4) (hp : p ∈ halfCells) (h : address e p = vertexAddress v j) :
    wireValue Q e p = cornerBit (Q v) j := by
  obtain ⟨s,vEq,rfl⟩ := Mobius.PortGraphGeometry.station_overlap hp h
  rw [wire_end,vEq]

private theorem source_compatible (Q : Fin n → Quad) {a b : Source n} (ha : a.valid) (hb : b.valid)
    (h : a.addr = b.addr) : a.bit Q = b.bit Q := by
  cases a with
  | vertex v i =>
    cases b with
    | vertex w j =>
      obtain ⟨rfl,rfl⟩ := Mobius.PortGraphGeometry.vertexAddress_injective h
      rfl
    | wire e p => exact (vertex_wire Q e p v i hb h.symm).symm
  | wire e p =>
    cases b with
    | vertex w j => exact vertex_wire Q e p w j ha h
    | wire f q =>
      rcases Mobius.PortGraphGeometry.overlap ha hb h with ⟨rfl,rfl⟩ | ⟨s,t,j,vertex,rfl,rfl⟩
      · rfl
      · change wireValue Q e _ = wireValue Q f _
        rw [wire_end,wire_end,vertex]

private def sources (es : List (Edge n)) : List (Source n) :=
  ((List.finRange n).flatMap fun v => (List.finRange 4).map (Source.vertex v)) ++
   (es.flatMap fun e => halfCells.map (Source.wire e))

private theorem vertex_mem (es : List (Edge n)) (v : Fin n) (j : Fin 4) :
    Source.vertex v j ∈ sources es := by
  simp [sources, List.mem_flatMap]

private theorem wire_mem (es : List (Edge n)) {e : Edge n} {p : TaggedCell}
    (he : e ∈ es) (hp : p ∈ halfCells) : Source.wire e p ∈ sources es := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨e,he,List.mem_map.mpr ⟨p,hp,rfl⟩⟩

private theorem source_valid (es : List (Edge n)) (s : Source n) (hs : s ∈ sources es) : s.valid := by
  rcases List.mem_append.mp hs with stations | wires
  · obtain ⟨v,_,members⟩ := List.mem_flatMap.mp stations
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp members
    trivial
  · obtain ⟨e,_,members⟩ := List.mem_flatMap.mp wires
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp members
    exact hp

private def coordDecEq (n : Nat) : DecidableEq (Coordinate n) := fun x y =>
  decidable_of_iff (∀ i, x i = y i) ⟨funext, fun h i => congrFun h i⟩

private def lookup (es : List (Edge n)) (Q : Fin n → Quad) (a : Addr n) : Bool :=
  letI : DecidableEq (Coordinate n) := coordDecEq n
  (sources es).any fun s => decide (s.addr = a) && s.bit Q

private theorem lookup_source (es : List (Edge n)) (Q : Fin n → Quad) (s : Source n)
    (hs : s ∈ sources es) : lookup es Q s.addr = s.bit Q := by
  letI : DecidableEq (Coordinate n) := coordDecEq n
  have iff : lookup es Q s.addr = true ↔ s.bit Q = true := by
    simp only [lookup,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨other,member,addr,one⟩
      have both := source_compatible Q (source_valid _ _ member) (source_valid _ _ hs) addr
      exact both ▸ one
    · exact fun one => ⟨s,hs,rfl,one⟩
  cases left : lookup es Q s.addr <;> cases right : s.bit Q <;> simp_all

/-- Executable row/column tables: the lookup defaults to false at any
    address outside the station and edge registry. -/
def realize (es : List (Edge n)) (Q : Fin n → Quad) : Tables n :=
  ⟨fun x y => lookup es Q (false,x,y), fun x y => lookup es Q (true,x,y)⟩

private theorem realize_reads (es : List (Edge n)) (Q : Fin n → Quad) (s : Source n)
    (hs : s ∈ sources es) : (realize es Q).value s.addr = s.bit Q := by
  have id (a : Addr n) : (realize es Q).value a = lookup es Q a := by
    obtain ⟨b,x,y⟩ := a
    cases b <;> rfl
  rw [id,lookup_source es Q _ hs]

theorem realizes_stations (es : List (Edge n)) (Q : Fin n → Quad) (v : Fin n) :
    stationQuad (realize es Q) v = Q v := by
  apply eq_quad
  intro j
  rw [station_bit]
  exact realize_reads es Q _ (vertex_mem es v j)

private theorem value_on_wire (es : List (Edge n)) (Q : Fin n → Quad) {e : Edge n}
    (he : e ∈ es) {p : TaggedCell} (hp : p ∈ halfCells) :
    (realize es Q).value (address e p) = wireValue Q e p :=
  realize_reads es Q _ (wire_mem es he hp)

private theorem active_cells : ∀ r ∈ internalNot, ∀ p ∈ corners r, p ∈ halfCells := by decide

private theorem total_congr (f g : TaggedCell → Bool) (cs : List TaggedCell)
    (h : ∀ p ∈ cs, f p = g p) : total f cs = total g cs := by
  induction cs with
  | nil => rfl
  | cons p cs ih =>
    rw [show total f (p::cs) = (f p ^^ total f cs) by rfl,
        show total g (p::cs) = (g p ^^ total g cs) by rfl,
        h p (by simp),ih (fun q hq => h q (by simp [hq]))]

private theorem total_mapped (f : β → Bool) (g : α → β) (xs : List α) :
    total f (xs.map g) = total (fun a => f (g a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,total,ih]

private theorem private_corner : ∀ r ∈ internalNot, ∃ p ∈ corners r,
    ∀ (s : Bool) (j : Fin 4), p ≠ endCell s j := by decide

private theorem local_identifies : ∀ r ∈ internalNot, ∀ s ∈ internalNot,
    (∀ p ∈ corners r, p ∈ corners s) → r = s := by decide

/-- Even forgetting the order of the four tagged corners, different
    (edge,internal face) pairs yield different tests. -/
theorem placed_identifies {e f : Edge n} {r s : Rectangle} (hr : r ∈ internalNot)
    (hs : s ∈ internalNot) (sub : ∀ a ∈ placedSquare e r, a ∈ placedSquare f s) :
    e=f ∧ r=s := by
  have lift (p : TaggedCell) (hp : p ∈ corners r) :
      ∃ q ∈ corners s, address e p = address f q := by
    have src : address e p ∈ placedSquare e r := by
      rw [placedSquare,← Mobius.PortGraphGeometry.placed_corners]
      exact List.mem_map.mpr ⟨_,hp,rfl⟩
    have target := sub _ src
    rw [placedSquare,← Mobius.PortGraphGeometry.placed_corners] at target
    obtain ⟨q,hq,eqn⟩ := List.mem_map.mp target
    exact ⟨q,hq,eqn.symm⟩
  obtain ⟨p,hp,privateAt⟩ := private_corner r hr
  obtain ⟨q,hq,hit⟩ := lift p hp
  have same : e = f := by
    rcases Mobius.PortGraphGeometry.overlap (active_cells r hr p hp) (active_cells s hs q hq) hit with
      ⟨eqn,_⟩ | ⟨a,b,j,_,hp',_⟩
    · exact eqn
    · exact False.elim (privateAt a j hp')
  subst f
  refine ⟨rfl,local_identifies r hr s hs ?_⟩
  intro p hp
  obtain ⟨q,hq,hit⟩ := lift p hp
  exact (Mobius.PortGraphGeometry.address_injective e hit) ▸ hq

theorem selected_distinct (es : List (Edge n)) (simple : es.Nodup) :
    (selectedSquares es).Pairwise (fun a b => ¬a.Perm b) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro e _
    apply List.pairwise_map.mpr
    have nd : internalNot.Nodup := by decide
    apply nd.imp_of_mem
    intro r s hr hs ne perm
    exact ne (placed_identifies hr hs (fun a ha => perm.mem_iff.mp ha)).2
  · apply simple.imp
    intro e f ne a ha b hb perm
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hb
    exact ne (placed_identifies hr hs (fun a ma => perm.mem_iff.mp ma)).1

theorem selected_nodup (es : List (Edge n)) (simple : es.Nodup) : (selectedSquares es).Nodup := by
  apply (selected_distinct es simple).imp
  intro a b distinct same
  exact distinct (same ▸ List.Perm.refl _)

/-- Reading the pullback tables on a local face has exactly the parity
    obtained by reading its genuine global XOR square. -/
theorem score_placed (t : Tables n) (e : Edge n) (r : Rectangle) :
    Mobius.TwoPhases.score (t.local e false) (t.local e true) r =
      total t.value (Mobius.PortGraphGeometry.coordCorners (Mobius.PortGraphGeometry.xCoord e r.1)
        (Mobius.PortGraphGeometry.yCoord e r.2.1) (Mobius.PortGraphGeometry.stepCoord e r.2.2)) := by
  rw [← Mobius.PortGraphGeometry.placed_corners, total_mapped]
  apply total_congr
  intro p _
  exact tagged_pull t e p

theorem actual_failures (es : List (Edge n)) (t : Tables n) :
    failuresOn t (selectedSquares es) = graphCost es t := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have one : (internalNot.map (placedSquare e)).countP (fun cs => !total t.value cs) = edgeCost t e := by
      rw [List.countP_map]
      unfold edgeCost notInternalCost
      apply List.countP_congr
      intro r _
      simp only [Function.comp_apply,score_placed,placedSquare]
    change List.countP _ (_ ++ selectedSquares es) = edgeCost t e + graphCost es t
    rw [List.countP_append, one]
    exact congrArg (edgeCost t e + ·) ih

theorem realizes_edge (es : List (Edge n)) (Q : Fin n → Quad) {e : Edge n} (he : e ∈ es) :
    edgeCost (realize es Q) e = if (Q e.lo).defect = (Q e.hi).defect then 1 else 0 := by
  have scores (r : Rectangle) (hr : r ∈ internalNot) :
      Mobius.TwoPhases.score ((realize es Q).local e false) ((realize es Q).local e true) r =
      Mobius.TwoPhases.score (notRow (ports Q e)) (notCol (ports Q e)) r := by
    apply total_congr
    intro p hp
    exact (tagged_pull _ _ p).trans (value_on_wire es Q he (active_cells r hr p hp))
  have costs : edgeCost (realize es Q) e =
      notInternalCost (notRow (ports Q e)) (notCol (ports Q e)) := by
    apply List.countP_congr
    intro r hr
    rw [scores r hr]
  exact costs.trans (Mobius.OneInThree.not_extension_cost (ports Q e))

theorem edge_lower (t : Tables n) (e : Edge n) :
    (if (stationQuad t e.lo).defect = (stationQuad t e.hi).defect then 1 else 0) ≤ edgeCost t e :=
  Mobius.OneInThree.not_cost_lower (ports (stationQuad t) e) _ _ (edge_reads t e)

theorem edgewise_extension (es : List (Edge n)) (Q : Fin n → Quad) :
    ∃ t : Tables n, (∀ v, stationQuad t v = Q v) ∧
      ∀ e ∈ es, edgeCost t e = if (Q e.lo).defect = (Q e.hi).defect then 1 else 0 :=
  ⟨realize es Q,realizes_stations es Q,fun _ he => realizes_edge es Q he⟩

def cutSize (es : List (Edge n)) (color : Fin n → Bool) : Nat :=
  es.countP fun e => color e.lo != color e.hi

private theorem count_cut {es : List (Edge n)} {z : Fin n → Bool} {cost : Edge n → Nat}
    (h : ∀ e ∈ es, (if z e.lo = z e.hi then 1 else 0) ≤ cost e) :
    es.length ≤ (es.map cost).sum + cutSize es z := by
  induction es with
  | nil => exact Nat.le_refl 0
  | cons e es ih =>
    have atEdge := h e (by simp)
    have tail := ih (fun f hf => h f (by simp [hf]))
    change es.length + 1 ≤ cost e + (es.map cost).sum + _
    simp only [cutSize,List.countP_cons] at tail ⊢
    cases h₀ : z e.lo <;> cases h₁ : z e.hi <;> simp [h₀,h₁] at atEdge ⊢ <;> omega

private theorem complement {es : List (Edge n)} {z : Fin n → Bool} {cost : Edge n → Nat}
    (h : ∀ e ∈ es, cost e = if z e.lo = z e.hi then 1 else 0) :
    (es.map cost).sum + cutSize es z = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have atEdge := h e (by simp)
    have tail := ih (fun f hf => h f (by simp [hf]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,cutSize,List.countP_cons] at tail ⊢
    cases h₀ : z e.lo <;> cases h₁ : z e.hi <;> simp [h₀,h₁] at atEdge ⊢ <;> omega

def bestColor (es : List (Edge n)) : Fin n → Bool :=
  let candidates := Mobius.TourCount.assignments n
  let nonempty := List.ne_nil_of_mem (Mobius.TourCount.assignments_complete (fun _ : Fin n => false))
  candidates.maxOn (cutSize es) nonempty

def maxCut (es : List (Edge n)) : Nat := cutSize es (bestColor es)

theorem cut_le_maxCut (es : List (Edge n)) (color : Fin n → Bool) : cutSize es color ≤ maxCut es :=
  List.le_apply_maxOn_of_mem (Mobius.TourCount.assignments_complete color)

/-- The extremizer is an actual pair of tables in the common address
    space, including for an empty graph. Repetitions in an edge list
    count with multiplicity; a nodup list is the ordinary simple graph. -/
theorem exact_maxCut (es : List (Edge n)) :
    (∀ t : Tables n, es.length - maxCut es ≤ graphCost es t) ∧
      ∃ t : Tables n, graphCost es t = es.length - maxCut es := by
  constructor
  · intro t
    let z := fun v => (stationQuad t v).defect
    have lo := count_cut (es := es) (z := z) (cost := edgeCost t) (fun e _ => edge_lower t e)
    have hi := cut_le_maxCut es z
    change es.length - maxCut es ≤ (es.map (edgeCost t)).sum
    omega
  · let z := bestColor es
    let Q := fun v => Mobius.OneInThree.literal (z v)
    have lit (b : Bool) : (Mobius.OneInThree.literal b).defect = b := by cases b <;> rfl
    have values (e : Edge n) (he : e ∈ es) :
        edgeCost (realize es Q) e = if z e.lo = z e.hi then 1 else 0 := by
      simpa only [Q,lit] using realizes_edge es Q he
    have eqn := complement values
    refine ⟨realize es Q,?_⟩
    change (es.map (edgeCost (realize es Q))).sum = es.length - cutSize es z
    omega

theorem actual_maxCut (es : List (Edge n)) :
    (∀ t : Tables n, es.length - maxCut es ≤ failuresOn t (selectedSquares es)) ∧
      ∃ t : Tables n, failuresOn t (selectedSquares es) = es.length - maxCut es := by
  simpa only [actual_failures] using exact_maxCut es

end Mobius.PortGraph
