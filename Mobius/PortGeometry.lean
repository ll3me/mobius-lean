import Mobius.OneInThree

/-! A wire in two independent station spaces. Coordinates in each station
are the coefficients of its independent X, Y and D. This universal chart
allows arbitrary injective linear placements of the two station triples. -/
namespace Mobius.PortGeometry
open Mobius.SignObstruction (B)
open Mobius.TwoPhases (TaggedCell corners halfCells)
open Mobius.OneInThree (port₁ port₁₂)

abbrev Station := BitVec 3

private def linear (w : B) (a b c d : Station) : Station :=
  (if w.getLsbD 0 then a else 0) ^^^ (if w.getLsbD 1 then b else 0) ^^^
  (if w.getLsbD 2 then c else 0) ^^^ (if w.getLsbD 3 then d else 0)

def left (w : B) := linear w 2 4 1 1
def right (w : B) := linear w 6 0 1 5

theorem chart_linear : ∀ u v : B,
    left (u ^^^ v) = left u ^^^ left v ∧ right (u ^^^ v) = right u ^^^ right v := by decide

theorem chart_injective : ∀ u v : B, left u = left v → right u = right v → u = v := by decide

theorem basis_images :
    (left 2,right 2) = (4,0) ∧ (left 12,right 12) = (0,4) ∧
    (left 4,right 4) = (1,1) ∧ (left 13,right 13) = (2,2) := by decide

/-- The first x anchor is zero and its y anchor is five in the local chart. -/
def inLeft (p : TaggedCell) : Station × Station := (1 ^^^ left p.2.1, 2 ^^^ left (p.2.2 ^^^ 5))
def inRight (p : TaggedCell) : Station × Station := (right p.2.1, right (p.2.2 ^^^ 5))

/-- A cell of the wire is supported wholly in one station exactly when
it is one of that endpoint's four *tagged* corners. -/
theorem station_contact : ∀ p ∈ halfCells,
    (inRight p = (0,0) ↔ p ∈ corners port₁) ∧
    (inLeft p = (0,0) ↔ p ∈ corners port₁₂) := by decide

/-- Both endpoint faces have the same ordered tagged corners in their
own station. This retains arbitrary four-bit encodings across a connection. -/
theorem endpoint_cells :
    ((corners port₁).map fun p => (p.1,inLeft p)) =
       [(false,1,2),(false,5,6),(true,1,6),(true,5,2)] ∧
    ((corners port₁₂).map fun p => (p.1,inRight p)) =
       [(false,1,2),(false,5,6),(true,1,6),(true,5,2)] := by decide

theorem no_origin : ∀ p ∈ halfCells, ¬(inLeft p = (0,0) ∧ inRight p = (0,0)) := by decide

/-- Injective placement of a station's coefficient triples into a larger
vector space preserves the contact test. The image of zero is the origin. -/
theorem contact_after_embedding {α β : Type} (f : Station → α) (g : Station → β)
    (hf : ∀ {u v}, f u = f v → u = v) (hg : ∀ {u v}, g u = g v → u = v)
    (p : TaggedCell) (hp : p ∈ halfCells) :
    ((g (inRight p).1 = g 0 ∧ g (inRight p).2 = g 0) ↔ p ∈ corners port₁) ∧
    ((f (inLeft p).1 = f 0 ∧ f (inLeft p).2 = f 0) ↔ p ∈ corners port₁₂) := by
  have coords {γ : Type} (map : Station → γ) (inj : ∀ {u v}, map u = map v → u = v)
      (c : Station × Station) : (map c.1 = map 0 ∧ map c.2 = map 0) ↔ c = (0,0) := by
    constructor
    · intro h
      exact Prod.ext (inj h.1) (inj h.2)
    · rintro rfl
      exact ⟨rfl,rfl⟩
  exact ⟨(coords g hg _).trans (station_contact p hp).1,
    (coords f hf _).trans (station_contact p hp).2⟩

end Mobius.PortGeometry
