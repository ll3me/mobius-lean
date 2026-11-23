import Mobius
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Follows the upstream audit idiom. The scanned environment imports the
solution modules only; benchmark challenge stubs are never imported. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut localDecls : Nat := 0
  let mut upstreamDecls : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Mobius).isPrefixOf name || (`Complexity).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
      if (`Mobius).isPrefixOf name then
        localDecls := localDecls + 1
      else
        upstreamDecls := upstreamDecls + 1
  logInfo m!"Checked transitive axioms of {localDecls} Mobius and {upstreamDecls} Complexity declarations."

#print axioms Mobius.SATSeam.seam_np_complete
#print axioms Mobius.Clock.separation_iff_clock_failure
#print axioms Mobius.FixedCutRank.short_eight_requires_turn_and_cancellation
#print axioms Mobius.SignObstruction.fifteen_inconsistent
#print axioms Mobius.SignObstruction.any_fourteen_consistent
#print axioms Mobius.SignObstruction.repair_optimal
#print axioms Mobius.TwoPhases.no_integer_cancellation
#print axioms Mobius.SwapSupport.support_and_window


#print axioms Mobius.Inclusion.collapse_iff_eq
#print axioms Mobius.TourCount.transfer_entry
#print axioms Mobius.SignObstruction.valid_rectangle_iff_zero

#print axioms Mobius.TwoPhases.optimum_failure_fraction
#print axioms Mobius.Endpoint.extraction_iff_separation
#print axioms Mobius.FixedGraphConjecture.iff_separation

#print axioms Mobius.DirectionLaws.minimum_weight
#print axioms Mobius.DirectionLaws.failures_attained
#print axioms Mobius.Rigidity.optimal_direction
#print axioms Mobius.Rigidity.Enumeration.count_double
#print axioms Mobius.Rigidity.Enumeration.count_single
#print axioms Mobius.Rigidity.Residual.normalized_local_crossing
#print axioms Mobius.LockedGap.locked_row_gap
#print axioms Mobius.LockedGap.witness_weight
#print axioms Mobius.LockedGap.witness_zero_rows
#print axioms Mobius.LockedRank.nonsingular_away_from_singleton
#print axioms Mobius.FiveRowAffine.five_lower
#print axioms Mobius.FiveRowAffine.projection_attains
#print axioms Mobius.RankTrade.integer_factorization
#print axioms Mobius.RankTrade.integer_rank_product
#print axioms Mobius.RankTrade.recover_crossing
#print axioms Mobius.RankTrade.center_spectrum_product
#print axioms Mobius.RankTrade.arbitrary_center_product
#print axioms Mobius.Rigidity.Backtracks.optimal_law
#print axioms Mobius.NaslundRestriction.witness_strip
