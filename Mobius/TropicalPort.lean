import Mobius.TropicalMWIS
import Mobius.PortGraph

/-! Unary prices are charged on the four actual global station cells.
The edge term is the failure count of the 13 placed squares per edge.
The result quantifies over complete, shared geometric tables. -/
namespace Mobius.TropicalPort

open Mobius.PortGraphGeometry (Edge)
open Mobius.PortGraph (Tables stationQuad failuresOn selectedSquares)
open Mobius.TropicalMWIS (Graph Coloring Prices sumQ energy optimum)
open Mobius.TropicalDAG

def graph (es : List (Edge n)) : Graph n := es.map (fun e => (e.lo,e.hi))

def colorOf (t : Tables n) : Coloring n := fun v => (stationQuad t v).defect

def tableCost (es : List (Edge n)) (h : Prices n) (t : Tables n) : Rat :=
    (failuresOn t (selectedSquares es) : Rat) +
      sumQ (List.finRange n) (fun v => h (v,(stationQuad t v).defect))

def encode (es : List (Edge n)) (z : Coloring n) : Tables n :=
    Mobius.PortGraph.realize es (fun v => Mobius.OneInThree.literal (z v))

private theorem literal_bit (b : Bool) : (Mobius.OneInThree.literal b).defect = b := by
  cases b <;> rfl

theorem station_color (es : List (Edge n)) (z : Coloring n) (v : Fin n) :
    colorOf (encode es z) v = z v := by
  unfold colorOf encode
  rw [Mobius.PortGraph.realizes_stations,literal_bit]

private def uncutCount (es : List (Edge n)) (z : Coloring n) : Nat :=
    (es.map fun e => if z e.lo=z e.hi then 1 else 0).sum

private theorem graph_uncutCount (es : List (Edge n)) (z : Coloring n) :
    Mobius.TropicalMWIS.cutCost (graph es) z = (uncutCount es z : Rat) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change Mobius.TropicalMWIS.bit (z e.lo == z e.hi) + Mobius.TropicalMWIS.cutCost (graph es) z =
      ((if z e.lo=z e.hi then 1 else 0 : Nat) + uncutCount es z : Nat)
    by_cases eq : z e.lo=z e.hi <;> simp [eq,Mobius.TropicalMWIS.bit,ih] <;> grind

private theorem table_lower_raw (es : List (Edge n)) (t : Tables n) :
    uncutCount es (colorOf t) ≤ Mobius.PortGraph.graphCost es t := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.add_le_add (Mobius.PortGraph.edge_lower t e) ih

private theorem table_attains_raw (es : List (Edge n)) (z : Coloring n) :
    Mobius.PortGraph.graphCost es (encode es z) = uncutCount es z := by
  unfold Mobius.PortGraph.graphCost uncutCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  simpa only [encode,literal_bit] using
    (Mobius.PortGraph.realizes_edge es (fun v => Mobius.OneInThree.literal (z v)) he)

/-- Pointwise domination: the actual table pays at least the objective of
its own decoded station coloring, even for signed prices. -/
theorem lower_for_every_table (es : List (Edge n)) (h : Prices n) (t : Tables n) :
    energy (graph es) h (colorOf t) ≤ tableCost es h t := by
  have lo := Rat.natCast_le_natCast.mpr (table_lower_raw es t)
  unfold energy tableCost
  rw [graph_uncutCount,Mobius.PortGraph.actual_failures]
  exact (Rat.add_le_add_right).mpr lo

/-- A single pair of global tables realizes the prescribed coloring,
including isolated vertices, and attains its complete unary-plus-square cost. -/
theorem attain_every_coloring (es : List (Edge n)) (h : Prices n) (z : Coloring n) :
    tableCost es h (encode es z) = energy (graph es) h z := by
  unfold energy tableCost
  rw [graph_uncutCount,Mobius.PortGraph.actual_failures,table_attains_raw]
  change _+sumQ (List.finRange n) (fun v => h (v,colorOf (encode es z) v)) = _
  simp only [station_color]

def witness (es : List (Edge n)) (h : Prices n) : Tables n :=
  let choices := Mobius.TourCount.assignments n
  let nonempty := List.ne_nil_of_mem (Mobius.TourCount.assignments_complete (fun _ : Fin n => false))
  encode es (choices.minOn (fun z => tableCost es h (encode es z)) nonempty)

def geometricMinimum (es : List (Edge n)) (h : Prices n) := tableCost es h (witness es h)

private theorem graph_le (g : Graph n) (h : Prices n) (z : Coloring n) :
    optimum g h ≤ energy g h z :=
  List.apply_minOn_le_of_mem (f := energy g h) (xs := Mobius.TropicalMWIS.colors n)
    (Mobius.TourCount.assignments_complete z)

private theorem physical_le_encode (es : List (Edge n)) (h : Prices n) (z : Coloring n) :
    geometricMinimum es h ≤ tableCost es h (encode es z) :=
  List.apply_minOn_le_of_mem (f := fun w => tableCost es h (encode es w))
    (xs := Mobius.TourCount.assignments n) (Mobius.TourCount.assignments_complete z)

theorem geometric_eq_graph (es : List (Edge n)) (h : Prices n) :
    geometricMinimum es h = optimum (graph es) h := by
  apply Rat.le_antisymm
  · let best := (Mobius.TropicalMWIS.colors n).minOn (energy (graph es) h)
      (List.ne_nil_of_mem (Mobius.TourCount.assignments_complete (fun _ : Fin n => false)))
    have bound := physical_le_encode es h best
    rw [attain_every_coloring] at bound
    exact bound
  · exact Rat.le_trans (graph_le _ _ _) (lower_for_every_table es h (witness es h))

/-- This is an attained minimum over all tables, with no consistency
promise on a competitor. -/
theorem exact_physical_minimum (es : List (Edge n)) (h : Prices n) :
    (∀ t : Tables n, optimum (graph es) h ≤ tableCost es h t) ∧
    ∃ t : Tables n, tableCost es h t = optimum (graph es) h := by
  exact ⟨fun t => Rat.le_trans (graph_le _ _ _) (lower_for_every_table es h t),
    ⟨witness es h,geometric_eq_graph es h⟩⟩

/-- A circuit solving the actual geometric problem for all nonnegative
unary prices yields one shared zero-constant max-plus DAG for MWIS on this
fixed graph, with no increase in the number of gates. -/
theorem compiled_geometric_for_mwis (es : List (Edge n)) (p : MinDAG (Fin n × Bool) s) (out : Fin s)
    (correct : ∀ h : Prices n, (∀ i,0≤h i) → primal p h out = geometricMinimum es h) :
    (compile (Mobius.TropicalMWIS.base (graph es)) Mobius.TropicalMWIS.labels p).size ≤ s ∧
    ∀ w : Fin n → Rat,
      (compile (Mobius.TropicalMWIS.base (graph es)) Mobius.TropicalMWIS.labels p).read w out =
        Mobius.TropicalMWIS.mwis (graph es) w := by
  apply Mobius.TropicalMWIS.compile_for_mwis
  intro h nonneg
  exact (correct h nonneg).trans (geometric_eq_graph es h)

end Mobius.TropicalPort
