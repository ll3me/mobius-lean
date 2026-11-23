import Mobius.PortGeometry

/-! An ordered edge is an actual affine copy of the wire in the direct sum
of its endpoint spaces. The four corner slots at a vertex agree under either
endpoint embedding. Distinct edges can meet only at those slots. -/
namespace Mobius.PortGraphGeometry
open Mobius.SignObstruction (B Rectangle)
open Mobius.TwoPhases (TaggedCell corners halfCells)
open Mobius.OneInThree (port₁ port₁₂)
open Mobius.PortGeometry (Station inLeft inRight left right)

set_option maxRecDepth 8192

@[ext] structure Edge (n : Nat) where
  lo : Fin n
  hi : Fin n
  lt : lo < hi
  deriving DecidableEq

abbrev Coord (n : Nat) := Fin n → Station
abbrev Addr (n : Nat) := Bool × Coord n × Coord n

def endpoint (e : Edge n) (b : Bool) := if b then e.hi else e.lo

def endCell (b : Bool) (j : Fin 4) : TaggedCell :=
  (corners (if b then port₁₂ else port₁)).getD j.val (false,0,0)

def slot (j : Fin 4) : Bool × Station × Station :=
  [(false,1,2),(false,5,6),(true,1,6),(true,5,2)].getD j.val (false,0,0)

def vertexCoord (v : Fin n) (s : Station) : Coord n := fun i => if i = v then s else 0

def vertexAddress (v : Fin n) (j : Fin 4) : Addr n :=
  ((slot j).1, vertexCoord v (slot j).2.1, vertexCoord v (slot j).2.2)

def plant (e : Edge n) (p q : Station) : Coord n := fun i =>
  if i = e.lo then p else if i = e.hi then q else 0

private theorem ne_ends (e : Edge n) : e.lo ≠ e.hi := Fin.ne_of_lt e.lt

@[simp] theorem plant_lo (e : Edge n) (p q : Station) : plant e p q e.lo = p := by
  simp [plant]

@[simp] theorem plant_hi (e : Edge n) (p q : Station) : plant e p q e.hi = q := by
  simp [plant, (ne_ends e).symm]

def address (e : Edge n) (c : TaggedCell) : Addr n :=
  (c.1, plant e (inLeft c).1 (inRight c).1, plant e (inLeft c).2 (inRight c).2)

def atStation (z : Addr n) (i : Fin n) : Station × Station := (z.2.1 i,z.2.2 i)

@[simp] theorem at_lo (e : Edge n) (c : TaggedCell) :
    atStation (address e c) e.lo = inLeft c := by simp [atStation,address]

@[simp] theorem at_hi (e : Edge n) (c : TaggedCell) :
    atStation (address e c) e.hi = inRight c := by simp [atStation,address]

theorem endCell_mem_half : ∀ (a : Bool) (j : Fin 4), endCell a j ∈ halfCells := by decide

private theorem end_coordinates : ∀ (a : Bool) (j : Fin 4),
    (endCell a j).1 = (slot j).1 ∧
    inLeft (endCell a j) = (if a then (0,0) else (slot j).2) ∧
    inRight (endCell a j) = (if a then (slot j).2 else (0,0)) := by decide

theorem address_endCell (e : Edge n) (b : Bool) (j : Fin 4) :
    address e (endCell b j) = vertexAddress (endpoint e b) j := by
  obtain ⟨h,l,r⟩ := end_coordinates b j
  cases b <;> apply Prod.ext h <;> apply Prod.ext <;> funext i <;>
    by_cases hl : i=e.lo <;> by_cases hr : i=e.hi <;>
    simp_all [address,plant,vertexAddress,vertexCoord,endpoint,ne_ends e,(ne_ends e).symm]

private theorem slot_live : ∀ j : Fin 4, (slot j).2.1 ≠ 0 := by decide
private theorem slots_inj : ∀ i j : Fin 4, slot i = slot j → i=j := by decide

theorem vertexAddress_injective {v w : Fin n} {i j : Fin 4}
    (h : vertexAddress v i = vertexAddress w j) : v=w ∧ i=j := by
  have hx := congrArg (fun z : Addr n => z.2.1 v) h
  have hv : v=w := by
    by_cases hv : v=w
    · exact hv
    · exact False.elim (slot_live i (by simpa [vertexAddress,vertexCoord,hv] using hx))
  subst w
  have hs := congrArg (fun z : Addr n => (z.1,atStation z v)) h
  simp [atStation,vertexAddress,vertexCoord] at hs
  exact ⟨rfl, slots_inj i j (Prod.ext hs.1 (Prod.ext hs.2.1 hs.2.2))⟩

private theorem x_inj : ∀ x y : B, (1 ^^^ left x) = (1 ^^^ left y) →
    right x = right y → x=y := by decide

private theorem y_inj : ∀ x y : B, (2 ^^^ left (x ^^^ 5)) = (2 ^^^ left (y ^^^ 5)) →
    right (x ^^^ 5) = right (y ^^^ 5) → x=y := by decide

theorem address_injective (e : Edge n) {c d : TaggedCell}
    (h : address e c = address e d) : c=d := by
  have hl := congrArg (fun z : Addr n => atStation z e.lo) h
  have hr := congrArg (fun z : Addr n => atStation z e.hi) h
  simp only [at_lo,at_hi] at hl hr
  exact Prod.ext (congrArg (fun z : Addr n => z.1) h) (Prod.ext
    (x_inj _ _ (congrArg Prod.fst hl) (congrArg Prod.fst hr))
    (y_inj _ _ (congrArg Prod.snd hl) (congrArg Prod.snd hr)))

private theorem in_ports : ∀ (a : Bool) (c : TaggedCell),
    c ∈ corners (if a then port₁₂ else port₁) → ∃ j : Fin 4, c=endCell a j := by decide

private theorem edge_end_or {e : Edge n} {c : TaggedCell} {v : Fin n}
    (h : atStation (address e c) v ≠ (0,0)) : v=e.lo ∨ v=e.hi := by
  by_cases hl : v=e.lo
  · exact Or.inl hl
  by_cases hr : v=e.hi
  · exact Or.inr hr
  exact False.elim (h (by simp [atStation,address,plant,hl,hr]))

private theorem edge_eq_of_endpoints {e f : Edge n}
    (l : e.lo=f.lo ∨ e.lo=f.hi) (r : e.hi=f.lo ∨ e.hi=f.hi) : e=f := by
  have he := e.lt
  have hf := f.lt
  rcases l with l|l <;> rcases r with r|r
  · exact False.elim (ne_ends e (l.trans r.symm))
  · exact Edge.ext l r
  · omega
  · exact False.elim (ne_ends e (l.trans r.symm))

private theorem end_of_overlap {e f : Edge n} {c d : TaggedCell}
    (hc : c∈halfCells) (hne : e≠f) (h : address e c = address f d) :
    ∃ a j, c = endCell a j := by
  by_cases hr : inRight c = (0,0)
  · obtain ⟨j,hj⟩ := in_ports false c ((PortGeometry.station_contact c hc).1.mp hr)
    exact ⟨false,j,hj⟩
  by_cases hl : inLeft c = (0,0)
  · obtain ⟨j,hj⟩ := in_ports true c ((PortGeometry.station_contact c hc).2.mp hl)
    exact ⟨true,j,hj⟩
  exact False.elim (hne (edge_eq_of_endpoints
    (edge_end_or (c:=d) (by simpa only [← h,at_lo] using hl))
    (edge_end_or (c:=d) (by simpa only [← h,at_hi] using hr))))

/-- Complete collision classification for all cells used by the two wires. -/
theorem overlap {e f : Edge n} {c d : TaggedCell} (hc : c∈halfCells) (hd : d∈halfCells)
    (h : address e c = address f d) :
    (e=f ∧ c=d) ∨ ∃ a b j, endpoint e a = endpoint f b ∧ c=endCell a j ∧ d=endCell b j := by
  by_cases he : e=f
  · subst f
    exact Or.inl ⟨rfl,address_injective e h⟩
  obtain ⟨a,j,rfl⟩ := end_of_overlap hc he h
  obtain ⟨b,k,rfl⟩ := end_of_overlap hd (Ne.symm he) h.symm
  rw [address_endCell,address_endCell] at h
  obtain ⟨hv,rfl⟩ := vertexAddress_injective h
  exact Or.inr ⟨a,b,j,hv,rfl,rfl⟩

theorem station_overlap {e : Edge n} {c : TaggedCell} {v : Fin n} {j : Fin 4}
    (hc : c∈halfCells) (h : address e c = vertexAddress v j) :
    ∃ a, endpoint e a=v ∧ c=endCell a j := by
  have l_or_r : inLeft c = (0,0) ∨ inRight c = (0,0) := by
    by_cases hl : e.lo=v
    · right
      have hr : e.hi ≠ v := fun eq => ne_ends e (hl.trans eq.symm)
      have hx := congrArg (fun z : Addr n => atStation z e.hi) h
      rw [at_hi] at hx
      simpa only [atStation,vertexAddress,vertexCoord,ite_eq_right hr] using hx
    · left
      have hx := congrArg (fun z : Addr n => atStation z e.lo) h
      rw [at_lo] at hx
      simpa only [atStation,vertexAddress,vertexCoord,ite_eq_right hl] using hx
  obtain ⟨a,k,hk⟩ : ∃ a k, c=endCell a k := by
    rcases l_or_r with hl|hr
    · obtain ⟨k,hk⟩ := in_ports true c ((PortGeometry.station_contact c hc).2.mp hl)
      exact ⟨true,k,hk⟩
    · obtain ⟨k,hk⟩ := in_ports false c ((PortGeometry.station_contact c hc).1.mp hr)
      exact ⟨false,k,hk⟩
  rw [hk,address_endCell] at h
  obtain ⟨hv,rfl⟩ := vertexAddress_injective h
  exact ⟨a,hv,hk⟩


/-- Pointwise addition in the direct sum of the three-bit station spaces. -/
def coordXor (a b : Coord n) : Coord n := fun i => a i ^^^ b i

def xCoord (e : Edge n) (x : B) : Coord n := plant e (1 ^^^ left x) (right x)
def yCoord (e : Edge n) (y : B) : Coord n :=
  plant e (2 ^^^ left (y ^^^ 5)) (right (y ^^^ 5))
def stepCoord (e : Edge n) (d : B) : Coord n := plant e (left d) (right d)

private theorem x_translate : ∀ (x d : B),
    (1 ^^^ left (x ^^^ d)) = ((1 ^^^ left x) ^^^ left d) := by decide

private theorem y_translate : ∀ (y d : B),
    (2 ^^^ left ((y ^^^ d) ^^^ 5)) = ((2 ^^^ left (y ^^^ 5)) ^^^ left d) ∧
    right ((y ^^^ d) ^^^ 5) = (right (y ^^^ 5) ^^^ right d) := by decide

private theorem plant_xor (e : Edge n) (a b c d : Station) :
    plant e (a ^^^ c) (b ^^^ d) = coordXor (plant e a b) (plant e c d) := by
  funext i
  by_cases hl : i=e.lo <;> by_cases hr : i=e.hi <;> simp [plant,coordXor,hl,hr,(ne_ends e).symm]

theorem xCoord_xor (e : Edge n) (x d : B) :
    xCoord e (x ^^^ d) = coordXor (xCoord e x) (stepCoord e d) := by
  unfold xCoord stepCoord
  rw [x_translate, (PortGeometry.chart_linear x d).2, plant_xor]

theorem yCoord_xor (e : Edge n) (y d : B) :
    yCoord e (y ^^^ d) = coordXor (yCoord e y) (stepCoord e d) := by
  unfold yCoord stepCoord
  rw [(y_translate y d).1,(y_translate y d).2,plant_xor]

theorem stepCoord_ne_zero (e : Edge n) {d : B} (hd : d≠0) :
    stepCoord e d ≠ fun _ => 0 := by
  intro h
  have l := congrFun h e.lo
  have r := congrFun h e.hi
  apply hd
  apply PortGeometry.chart_injective
  · rw [show left 0 = 0 from by decide]
    simpa only [stepCoord,plant_lo] using l
  · rw [show right 0 = 0 from by decide]
    simpa only [stepCoord,plant_hi] using r

def coordCorners (x y d : Coord n) : List (Addr n) :=
  [(false,x,y),(false,coordXor x d,coordXor y d),(true,x,coordXor y d),
   (true,coordXor x d,y)]

/-- For every local rectangle, its actual tagged images are the four corners
of a single XOR rectangle in the global ambient coordinate space. -/
theorem placed_corners (e : Edge n) (r : Rectangle) :
    (corners r).map (address e) =
    coordCorners (xCoord e r.1) (yCoord e r.2.1) (stepCoord e r.2.2) := by
  rcases r with ⟨x,y,d⟩
  change [(false,xCoord e x,yCoord e y),(false,xCoord e (x ^^^ d),yCoord e (y ^^^ d)),
          (true,xCoord e x,yCoord e (y ^^^ d)),(true,xCoord e (x ^^^ d),yCoord e y)] = _
  rw [xCoord_xor,yCoord_xor]
  rfl

end Mobius.PortGraphGeometry
