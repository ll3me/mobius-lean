import Mobius.BoardInputProjection
import Mobius.DNNFRestriction

/-! Connect the fixed-width input positions to the acceptance function of
the concrete complete-board list and specialize programs without unrolling
their graphs. Public shape parameters fix the threshold and word length. -/
namespace Mobius.BoardProgramRestriction
open Mobius.BoardInputProjection
open Mobius.GraphCoverSource (Edges Covers rows vars source)
open Mobius.AxisGlue (Atlas)

/-- Valid complete-board words name four physical axes per board. A program
may do anything on words outside the promised family in the theorems below. -/
def Describes (word : Fin (bitCount r v) → Bool) (T : Atlas (boards r v) (dimension r v)) :=
  List.ofFn word=rawWord r v T

theorem describes_iff (f : AxisCompiler.Source r v) (T : Atlas (boards r v) (dimension r v)) :
    Describes (encodedBit f) T ↔ T=CapAtlas.compiled f := by
  constructor
  · intro same
    exact raw_word_injective r v (same.symm.trans (compiled_raw f).symm)
  · rintro rfl
    rfl

def AcceptsWord (word : Fin (bitCount r v) → Bool) : Prop :=
  ∃ T : Atlas (boards r v) (dimension r v), Describes word T ∧
    ∃ R C : AxisGlue.World (dimension r v),
      FullCaps.unionCost T R C ≤ (7*r)*126+(v+6*r)*128

theorem formula_word_iff (gap : PortGap.Gap266) (f : AxisCompiler.Source r v) :
    AcceptsWord (encodedBit f) ↔ AxisCompiler.Satisfiable f := by
  constructor
  · rintro ⟨T,description,phases⟩
    rw [(describes_iff f T).mp description] at phases
    exact (FullBoardMerge.compiled_iff gap f).mp phases
  · intro sat
    exact ⟨_,(describes_iff f _).mpr rfl,(FullBoardMerge.compiled_iff gap f).mpr sat⟩

theorem cover_word_iff (gap : PortGap.Gap266) (g : Edges n m) (x : Fin n → Bool) :
    AcceptsWord (encodedBit (source g x)) ↔ Covers g x :=
  (formula_word_iff gap _).trans (GraphCoverSource.source_iff g x)

/-- The specializing branching program uses the very same nodes and edges. -/
theorem restrict_program (gap : PortGap.Gap266) (g : Edges n m)
    (graph : ReadRestriction.Graph V E) (label : E → ReadRestriction.Guard (Flat n m))
    (bound : ReadRestriction.ReadBound graph label s)
    (correct : ∀ x, ReadRestriction.Accept graph label (encodedBit (source g x)) ↔
      AcceptsWord (encodedBit (source g x))) :
    ∃ labels : E → ReadRestriction.Guard (Fin n), ReadRestriction.ReadBound graph labels s ∧
      ∀ x, ReadRestriction.Accept graph labels x ↔ Covers g x := by
  refine ⟨fun e => (label e).specialize (field g),ReadRestriction.read_bound graph label
    (field g) (offset m) (field_input_iff g) bound,?_⟩
  intro x
  rw [ReadRestriction.accept_iff]
  simpa only [field_read] using (correct x).trans (cover_word_iff gap g x)

theorem restrict_dnnf (gap : PortGap.Gap266) (g : Edges n m)
    (c : DNNFRestriction.Circuit N (Flat n m)) (dec : DNNFRestriction.Decomposable c)
    (correct : ∀ x, DNNFRestriction.run c (encodedBit (source g x))=true ↔
      AcceptsWord (encodedBit (source g x))) :
    ∃ d : DNNFRestriction.Circuit N (Fin n), d.graph=c.graph ∧
      DNNFRestriction.Decomposable d ∧ DNNFRestriction.edgeCount d=DNNFRestriction.edgeCount c ∧
      ∀ x, DNNFRestriction.run d x=true ↔ Covers g x := by
  obtain ⟨ok,sem,_,count⟩ := DNNFRestriction.restrict_dnnf c (field g) (offset m) (field_input_iff g) dec
  refine ⟨_,rfl,ok,count,?_⟩
  intro x
  rw [sem]
  simpa only [field_read] using (correct x).trans (cover_word_iff gap g x)

end Mobius.BoardProgramRestriction
