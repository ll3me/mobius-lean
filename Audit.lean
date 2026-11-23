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

#print axioms Mobius.BoundaryProbe.probe_threeSAT_iff
#print axioms Mobius.BoundaryProbe.probe_word_injective
#print axioms Mobius.BoundaryDecision.probeErrors_eq_failures
#print axioms Mobius.BoundaryDecision.coincident_ports_count
#print axioms Mobius.BoundaryDecision.probe_optimum
#print axioms Mobius.BoundaryDecision.pointwise_threshold
#print axioms Mobius.BoundaryDecision.opposite_answers_same_measure
#print axioms Mobius.BoundaryDecision.no_uniform_scalar_decoder
#print axioms Mobius.BoundaryDecision.correct_machine_distinguishes
#print axioms Mobius.BoundaryDecision.cancellation_example
#print axioms Mobius.BoundarySemantics.joined_sharp_dot
#print axioms Mobius.BoundarySemantics.optimal_count_reconstruction
#print axioms Mobius.BoundaryTwoSums.tours_from_two
#print axioms Mobius.BoundaryTwoSums.clipping_order_example
#print axioms Mobius.BoundaryTwoSums.exact_measurement_number
#print axioms Mobius.BoundaryScan.seam_injective
#print axioms Mobius.BoundaryScan.one_pass_lower_bound
#print axioms Mobius.BoundaryScan.buffered_at_cut
#print axioms Mobius.BoundaryScan.buffered_correct

#print axioms Mobius.BoundaryBooleanRate.threshold_errors_eq_failures
#print axioms Mobius.BoundaryBooleanRate.optimal_error_direction
#print axioms Mobius.BoundaryBooleanRate.sharp_threshold
#print axioms Mobius.BoundaryBooleanRate.sharp_all_decoders

#print axioms Mobius.OneInThree.defect_gauge
#print axioms Mobius.OneInThree.extends_iff_odd
#print axioms Mobius.OneInThree.minimum_one_iff_exactlyOne
#print axioms Mobius.OneInThree.extends_not_iff
#print axioms Mobius.OneInThree.not_minimum_cost
#print axioms Mobius.OneInThree.extends_pin_iff
#print axioms Mobius.OneInThree.not_tiles_clean
#print axioms Mobius.PortGeometry.chart_injective
#print axioms Mobius.PortGeometry.station_contact
#print axioms Mobius.PortGeometry.contact_after_embedding
#print axioms Mobius.PortNetworkCost.sharp_local_cost
#print axioms Mobius.PortNetworkCost.cubic_threshold

#print axioms Mobius.PortCycle.edge_minimum
#print axioms Mobius.PortCycle.cycle_parity
#print axioms Mobius.PortCycle.cycle_minimum

#print axioms Mobius.FourBitPortCut.sparse_minimum
#print axioms Mobius.FourBitPortCut.board_optimum_profile
#print axioms Mobius.FourBitPortCut.best_among_board_optima
#print axioms Mobius.FourBitPortCut.near_witness
#print axioms Mobius.PortGraphGeometry.overlap
#print axioms Mobius.PortGraphGeometry.placed_corners
#print axioms Mobius.PortGraph.edgewise_extension
#print axioms Mobius.PortGraph.actual_maxCut

#print axioms Mobius.PortGraph.selected_distinct
#print axioms Mobius.PortGraph.selected_length
#print axioms Mobius.PortCutEdits.minimum_hamming

#print axioms Mobius.TropicalDAG.directional_restriction
#print axioms Mobius.TropicalMWIS.compile_for_mwis
#print axioms Mobius.TropicalPort.compiled_geometric_for_mwis
#print axioms Mobius.DirectionalWeights.singleton_bounded_output
#print axioms Mobius.UnaryCut.mincut_exact
#print axioms Mobius.UnaryCut.deletion_mincut
#print axioms Mobius.UnaryCut.triangle_energy_obstruction
#print axioms Mobius.CrossingRun.advance_embed
#print axioms Mobius.CrossingRun.trace_of_runInput
#print axioms Mobius.CrossingRun.splice_accept
#print axioms Mobius.CrossingMachine.ordinary_threeSAT_time
#print axioms Mobius.CrossingCeiling.total_ceiling
#print axioms Mobius.UnaryWitness.sparse_witness
#print axioms Mobius.WitnessStream.accept_iff_encoded
#print axioms Mobius.WitnessPacking.sqrt_bound

#print axioms Mobius.TropicalProduct.directional
#print axioms Mobius.TropicalProduct.compiled_geometric_product_for_mwis
