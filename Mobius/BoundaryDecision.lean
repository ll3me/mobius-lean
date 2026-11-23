import Mobius.BoundaryChoice
import Mobius.BoundaryProbe
import Mobius.BoundaryThreshold
import Mobius.Clock

/-! Compare exact signed contraction, Boolean SAT and actual machine
answers on ordinary encoded CNFs with four observable boundary words. -/
namespace Mobius.BoundaryDecision
open Mobius.BoundarySemantics (B Key Phase R C closes)
open Mobius.BoundaryChoice (Context)
open Complexity.SAT

/-- Both fixed contraction terms are used before any scalar decoding. -/
def raw (r c : Phase) (q : Key) : Int := R r q + C c q

def diagonal : Key := ⟨0,0,0,0⟩

def off (x y d : B) : Key := ⟨x,y,y ^^^ d,x ^^^ d⟩

theorem closes_off (x y d : B) (hd : d ≠ 0) : closes (off x y d) = false := by
  have ne : x ≠ x ^^^ d := by
    intro he; apply hd; simpa [← BitVec.xor_assoc] using (congrArg (fun z => x ^^^ z) he).symm
  simp [off,closes,ne]

theorem raw_off (r c : Phase) (x y d : B) :
    raw r c (off x y d) =
      Mobius.RankTradeGauge.sig (r x y) * Mobius.RankTradeGauge.sig (r (x ^^^ d) (y ^^^ d)) +
      Mobius.RankTradeGauge.sig (c x (y ^^^ d)) * Mobius.RankTradeGauge.sig (c (x ^^^ d) y) := by
  have a : x ^^^ y = (x ^^^ d) ^^^ (y ^^^ d) := by
    calc x ^^^ y = (x ^^^ y) ^^^ (d ^^^ d) := by simp
         _ = _ := by ac_rfl
  have b : x ^^^ (y ^^^ d) = (x ^^^ d) ^^^ y := by ac_rfl
  simp [raw,R,C,off,Mobius.RankTradeGauge.kernel,a,b]

theorem unit_signs : ∀ a b u v : Bool,
    let sum := Mobius.RankTradeGauge.sig a * Mobius.RankTradeGauge.sig b +
      Mobius.RankTradeGauge.sig u * Mobius.RankTradeGauge.sig v
    (decide (sum ≠ 0) = !(a ^^ (b ^^ (u ^^ (v ^^ false))))) ∧
    (sum ≠ 0 → sum=2 ∨ sum= -2) := by decide

theorem mismatch (r c : Phase) (x y d : B) :
    decide (raw r c (off x y d) ≠ 0) = !Mobius.TwoPhases.score r c (x,y,d) := by
  rw [raw_off]
  exact (unit_signs _ _ _ _).1

theorem raw_diagonal (r c : Phase) : raw r c diagonal = 2 := by
  unfold raw R C diagonal Mobius.RankTradeGauge.kernel
  cases hr : r 0 0 <;> cases hc : c 0 0 <;> rfl

/-- When the four ports are identified, even one raw measurement contains
the full model count of the base formula. This measures the cost hidden
in treating contraction as one operation. -/
theorem coincident_ports_count (n : Nat) (f : CNF) (p : Mobius.BoundarySemantics.Port) (r c : Phase) :
    Mobius.BoundarySemantics.contract n f ⟨p,p,p,p⟩ (raw r c) =
      2 * (Mobius.TourCount.countWith n f : Int) := by
  open Mobius.BoundarySemantics in
    have same (z : B) : raw r c ⟨z,z,z,z⟩ = 2 := by
      unfold raw R C Mobius.RankTradeGauge.kernel
      simp only [ite_true]
      cases r z z <;> cases c z z <;> rfl
    rw [contract_unfold, ←models_count]
    unfold sumI sample
    simp only [List.map_map]
    generalize models n f = ws
    induction ws with
    | nil => simp
    | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, Ports.read, same,
        List.length_cons, Int.natCast_succ] at *
      omega

/-- These are numerical errors against actual satisfying-assignment counts
of 3-CNFs. The total uses all nonzero directions and all ordered anchors.
BoundaryProbe.probe_word_injective and SignObstruction.entry_injective
give distinct binary formula inputs for the distinct triples. -/
def probeErrors (r c : Phase) : Nat :=
  Mobius.Rigidity.totalDefects (fun (x,y,d) => decide (raw r c (off x y d) ≠
    2*(Mobius.TourCount.sharp (Mobius.BoundaryProbe.probe x y (y ^^^ d) (x ^^^ d)) : Int)))

theorem probeErrors_eq_failures (r c : Phase) :
    probeErrors r c = Mobius.TwoPhases.failures r c := by
  rw [Mobius.Rigidity.two_count]
  unfold probeErrors Mobius.Rigidity.totalDefects
  apply congrArg List.sum; apply List.map_congr_left; intro d hd
  have valid : ∀ d ∈ Mobius.SignObstruction.directions, d ≠ 0 := by decide
  apply congrArg List.sum; apply List.map_congr_left; intro xy _
  obtain ⟨x,y⟩ := xy
  have no : ¬Satisfiable (Mobius.BoundaryProbe.probe x y (y ^^^ d) (x ^^^ d)) := by
    rw [Mobius.BoundaryProbe.probe_sat_iff]
    have h := closes_off x y d (valid d hd)
    simp [off,closes] at h
    exact fun ⟨a,b⟩ => h a b
  have h0 := mt (Mobius.TourCount.sharp_pos_iff _).mp no
  have zero : Mobius.TourCount.sharp (Mobius.BoundaryProbe.probe x y (y ^^^ d) (x ^^^ d)) = 0 := by omega
  change Mobius.Rigidity.oneIf (decide (raw r c (off x y d) ≠
    2*(Mobius.TourCount.sharp (Mobius.BoundaryProbe.probe x y (y ^^^ d) (x ^^^ d)) : Int))) = _
  rw [zero]
  change Mobius.Rigidity.oneIf (decide (raw r c (off x y d) ≠ 0)) = _
  exact congrArg Mobius.Rigidity.oneIf (mismatch r c x y d)

theorem probe_lower (r c : Phase) : 256 ≤ probeErrors r c := by
  rw [probeErrors_eq_failures]; exact Mobius.TwoPhases.failures_lower r c

theorem probe_optimum : probeErrors Mobius.BoundaryThreshold.thresholdPhase
    Mobius.BoundaryThreshold.thresholdPhase = 256 :=
  (probeErrors_eq_failures ..).trans Mobius.BoundaryThreshold.thresholdPhase_optimal

/-- The same table can have a nonzero numerical error and still answer ALL
single-boundary Boolean probes using a positive threshold. -/
theorem pointwise_threshold (x y u v : B) :
    (0 < Mobius.BoundaryThreshold.S x y u v) ↔
      ThreeSAT (encode (Mobius.BoundaryProbe.probe x y u v)) :=
  (Mobius.BoundaryThreshold.positive_iff ..).trans
    (Mobius.BoundaryProbe.probe_threeSAT_iff ..).symm

theorem bad_value (r c : Phase) : ∃ q : Key,
    closes q = false ∧ (raw r c q = 2 ∨ raw r c q = -2) := by
  have nonzero : ∃ x y d : B, d ≠ 0 ∧ raw r c (off x y d) ≠ 0 := by
    apply Classical.byContradiction
    intro none
    apply Mobius.TwoPhases.no_integer_cancellation 4 (by decide) r c
    intro x y d hd
    have z : raw r c (off x y d) = 0 := Classical.byContradiction
      (fun nz => none ⟨x,y,d,hd,nz⟩)
    rw [raw_off] at z
    exact z
  obtain ⟨x,y,d,hd,nz⟩ := nonzero
  refine ⟨off x y d,closes_off _ _ _ hd,?_⟩
  rw [raw_off] at nz ⊢
  exact (unit_signs _ _ _ _).2 nz

/-- Score an encoded formula using its actual finite range of named variables. -/
def measure (ctx : Context) (t : Key → Int) :=
  Mobius.BoundarySemantics.contract
    (variableBound (Mobius.BoundarySemantics.glue ctx.base ctx.ports)) ctx.base ctx.ports t

theorem measure_at_four (ctx : Context) (t : Key → Int)
    (h : variableBound (Mobius.BoundarySemantics.glue ctx.base ctx.ports) = 4) :
    measure ctx t = ctx.score t := by
  unfold measure
  rw [h]; rfl

/-- Rescoring the single uncorrected integer cannot decide SAT in every
CNF environment. Both members of the collision are real encoded instances. -/
theorem opposite_answers_same_measure (r c : Phase) :
    ∃ yes no : Context, ThreeSAT yes.word ∧ ¬ThreeSAT no.word ∧
      measure yes (raw r c) = measure no (raw r c) := by
  open Mobius.BoundaryChoice in
    obtain ⟨q,hq,h⟩ := bad_value r c
    rcases h with hp | hn
    · refine ⟨point diagonal,point q,(threeSAT_point _).2 (by rfl),
         (fun sat => Bool.noConfusion (hq.symm.trans ((threeSAT_point q).1 sat))),?_⟩
      rw [measure_at_four _ _ (point_bound _), measure_at_four _ _ (point_bound _),
        score_point,score_point,raw_diagonal,hp]
    · refine ⟨pair diagonal q,empty,(threeSAT_pair ..).2 (Or.inl (by rfl)),not_threeSAT_empty,?_⟩
      rw [measure_at_four _ _ (pair_bound ..), measure_at_four _ _ empty_bound,
        score_pair,score_empty,raw_diagonal,hn]; decide

theorem no_uniform_scalar_decoder (r c : Phase) :
    ¬∃ readout : Int → Bool, ∀ g : Context,
        (ThreeSAT g.word ↔ readout (measure g (raw r c)) = true) := by
  rintro ⟨readout,correct⟩
  obtain ⟨yes,no,hy,hn,eq⟩ := opposite_answers_same_measure r c
  exact hn ((correct no).2 (eq ▸ (correct yes).1 hy))

/-- A machine with ANY sufficient running-time budget must distinguish
two words whose scalar scores coincide. No hypothesis on its internal form. -/
theorem correct_machine_distinguishes (r c : Phase) (M : Complexity.Machine)
    (fuel : Complexity.Word → Nat)
    (correct : ∀ w, Mobius.Clock.CorrectBy ThreeSAT M (fuel w) w) :
    ∃ yes no : Context, measure yes (raw r c) = measure no (raw r c) ∧
      (∃ out, Complexity.runInput M (fuel yes.word) yes.word = some (true,out)) ∧
      (∃ out, Complexity.runInput M (fuel no.word) no.word = some (false,out)) := by
  obtain ⟨yes,no,hy,hn,eq⟩ := opposite_answers_same_measure r c
  obtain ⟨a,t,ra,ha⟩ := correct yes.word
  obtain ⟨b,u,rb,hb⟩ := correct no.word
  have atYes := ha.mp hy
  have atNo : b = false := by cases b <;> simp_all
  exact ⟨yes,no,eq,⟨t,atYes ▸ ra⟩,⟨u,atNo ▸ rb⟩⟩

/-- With variable 1 fixed false, the upper bit of both outgoing ports
is the free variable 0. The two actual boundary keys are (0,0,0,0)
and (0,0,8,8), and just the first one closes. -/
def twoKeysBase : CNF := [[⟨1,false⟩]]

def twoKeysPorts : Mobius.BoundarySemantics.Ports :=
  let zero : Mobius.BoundarySemantics.Port := ⟨1,1,1,1⟩
  let switch : Mobius.BoundarySemantics.Port := ⟨1,1,1,0⟩
  ⟨zero,zero,switch,switch⟩

theorem cancellation_example :
    let f := Mobius.BoundarySemantics.glue twoKeysBase twoKeysPorts
    let p := Mobius.BoundaryThreshold.thresholdPhase
    IsThreeCNF f ∧ Mobius.TourCount.sharp f = 1 ∧
      Mobius.BoundarySemantics.contract (variableBound f) twoKeysBase twoKeysPorts (raw p p) = 0 := by
  dsimp only
  refine ⟨Mobius.BoundarySemantics.glue_threeCNF _ _ ?_, ?_, ?_⟩
  · intro clause hc
    simp [twoKeysBase] at hc
    subst clause; decide
  · decide
  · decide

end Mobius.BoundaryDecision
