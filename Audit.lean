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
#print axioms Mobius.OverlapBoards.profile_iff
#print axioms Mobius.OverlapBoards.union_exact
#print axioms Mobius.ParallelSignature.board_signature
#print axioms Mobius.ParallelSignature.cycle_xor
#print axioms Mobius.DoubleFan.exists_minimizer
#print axioms Mobius.DoubleFan.baseline_cost
#print axioms Mobius.DoubleFan.witness_cost
#print axioms Mobius.DoubleFan.extend_cost
#print axioms Mobius.DoubleFan.center_minimum_exists
#print axioms Mobius.DoubleFan.exact_cost
#print axioms Mobius.DoubleFan.forced_sacrifice
#print axioms Mobius.AxisPortCost.weighted_local
#print axioms Mobius.AxisPortCost.geometric_local
#print axioms Mobius.AxisGlue.paste_restrict
#print axioms Mobius.AxisNetwork.feasible_iff_boolean
#print axioms Mobius.AxisNetwork.retained_private
#print axioms Mobius.AxisCompiler.weighted_iff
#print axioms Mobius.AxisCompiler.geometric_iff
#print axioms Mobius.OverlapMessages.memo_bits_iff
#print axioms Mobius.OverlapProtocols.matrix_cost_lower
#print axioms Mobius.MatrixMerge.source_split
#print axioms Mobius.MatrixMerge.public_separator
#print axioms Mobius.MatrixMerge.weighted_protocol
#print axioms Mobius.MatrixMerge.unweighted_protocol
#print axioms Mobius.MatrixMerge.weighted_cost_lower
#print axioms Mobius.MatrixMerge.unweighted_cost_lower
#print axioms Mobius.OverlapPasses.weighted_passes
#print axioms Mobius.OverlapPasses.unweighted_passes
#print axioms Mobius.MatrixPromise.exact_weighted_live
#print axioms Mobius.MatrixPromise.unweighted_live_lower
#print axioms Mobius.MatrixPromise.unweighted_individually_extend
#print axioms Mobius.MatrixPromise.exact_unweighted_live
#print axioms Mobius.FullCaps.unique_owner
#print axioms Mobius.FullCaps.owner_exists
#print axioms Mobius.FullCaps.owns_reverse
#print axioms Mobius.FullCaps.threshold_iff
#print axioms Mobius.CapAtlas.compiled_wiring
#print axioms Mobius.CapAtlas.compiled_threshold
#print axioms Mobius.FullBoardMerge.merge_iff
#print axioms Mobius.FullBoardMerge.exact_protocol
#print axioms Mobius.FullBoardMerge.hard_pair
#print axioms Mobius.FullBoardMerge.passes
#print axioms Mobius.FullCaps.union_cost_eq
#print axioms Mobius.FullCaps.complete_boards_iff
#print axioms Mobius.CapAtlas.compiled_union_iff
#print axioms Mobius.PortGap.code_distance
#print axioms Mobius.PortGap.no_small_excess
#print axioms Mobius.PortGap.geometric_local
#print axioms Mobius.FullBoardMerge.compiled_iff
#print axioms Mobius.PortGap.compressed_counts
#print axioms Mobius.GraphCoverSource.source_iff
#print axioms Mobius.GraphCoverSource.compiled_cover_iff
#print axioms Mobius.BoardInputProjection.raw_word_injective
#print axioms Mobius.BoardInputProjection.field_input_iff
#print axioms Mobius.BoardInputProjection.field_word
#print axioms Mobius.BoardInputProjection.graph_length
#print axioms Mobius.BoardInputProjection.Switches.field_read
#print axioms Mobius.ReadRestriction.syntactic_count
#print axioms Mobius.DNNFRestriction.restrict_dnnf
#print axioms Mobius.BoardProgramRestriction.formula_word_iff
#print axioms Mobius.BoardProgramRestriction.restrict_program
#print axioms Mobius.BoardProgramRestriction.restrict_dnnf
#print axioms Mobius.PinnedGate.and_assignment
#print axioms Mobius.PinnedGate.and_extension
#print axioms Mobius.PinnedGate.pin_extension
#print axioms Mobius.PinnedGate.selector_bit
#print axioms Mobius.SemanticBoardQuery.selected_address
#print axioms Mobius.SemanticBoardQuery.pin_boards_distinct
#print axioms Mobius.SemanticBoardQuery.board_agrees
#print axioms Mobius.SemanticBoardQuery.must_query
#print axioms Mobius.SemanticBoardQuery.cached_length
#print axioms Mobius.SemanticBoardQuery.phase_read_bound
#print axioms Mobius.SemanticBoardQuery.cached_accept_iff
#print axioms Mobius.ThreeFaceParity.twist_no_global
#print axioms Mobius.ThreeFaceCompletion.fixed_observable
#print axioms Mobius.ThreeFaceCompletion.free_observable
#print axioms Mobius.CommonCore.outside_iff
#print axioms Mobius.CommonCore.choice_of_profiles
#print axioms Mobius.ThreeFaceBoards.witness_optimal
#print axioms Mobius.ThreeFaceBoards.surface_extension_iff
#print axioms Mobius.ThreeFaceBoards.fano_forces_core
#print axioms Mobius.ThreeFaceAttachment.attached_iff
#print axioms Mobius.ThreeFaceColoring.xor_bridge
#print axioms Mobius.ThreeFaceColoring.nineFaces_equal
#print axioms Mobius.HybridMatching.six_pin_cancels
#print axioms Mobius.HybridMatching.vertex_ports
#print axioms Mobius.HybridMatching.affine_pair
#print axioms Mobius.HybridMatching.route_sound
#print axioms Mobius.HybridMatching.grouped_rectangle
#print axioms Mobius.HybridMatching.frontier
#print axioms Mobius.SignReadout.uniform_mass
#print axioms Mobius.BoardSearchStage.stage_iff
#print axioms Mobius.BoardSearchStage.captures
#print axioms Mobius.BoardSearchStage.cutoff_correct
#print axioms Mobius.HamiltonianSlice.difference_congr
#print axioms Mobius.HamiltonianSlice.first_layer
#print axioms Mobius.HamiltonianSlice.successor_count
#print axioms Mobius.CycleCoverQueries.residual_hall
#print axioms Mobius.CycleCoverQueries.expand_correct
#print axioms Mobius.CycleCoverQueries.expanded_le_peak
#print axioms Mobius.PostRead.leave_unary
#print axioms Mobius.PostRead.three_track_time
#print axioms Mobius.PairContraction.tied_faces
#print axioms Mobius.PairContraction.duplicated_control
#print axioms Mobius.PairContraction.dispatch_correct
#print axioms Mobius.PairContraction.sufficient_mask
#print axioms Mobius.PairContraction.path_list_misses
#print axioms Mobius.PairContraction.chain_coeff_step
#print axioms Mobius.PairContraction.internal_branch_budget
#print axioms Mobius.PairContraction.shift_pool_constant
#print axioms Mobius.PairContraction.pair_forces_type
#print axioms Mobius.PairContraction.sufficient_gate_split
#print axioms Mobius.PairContraction.regroup_contexts
#print axioms Mobius.PairContraction.high_band_budget
#print axioms Mobius.PairContraction.live_high_wires
#print axioms Mobius.PairContraction.live_high_unions
#print axioms Mobius.PairContraction.fixed_inputs_le_lost
#print axioms Mobius.PairContraction.constant_wire_balance
#print axioms Mobius.PairContraction.cut_fanout_le_removed
#print axioms Mobius.PairContraction.monitored_replay_iff
#print axioms Mobius.PairContraction.uncut_path_of_difference
#print axioms Mobius.PairContraction.first_reader_preserves_use
#print axioms Mobius.PairContraction.absorbing_reader_budget
#print axioms Mobius.PairContraction.bypass_reader_count
#print axioms Mobius.PairContraction.residual_internal_weight
#print axioms Mobius.PairContraction.monochrome_one_percent
#print axioms Mobius.PairContraction.quarter_trigger_one_percent
#print axioms Mobius.PairContraction.private_region_one_percent
#print axioms Mobius.PairContraction.and_or_distinct_partitions
#print axioms Mobius.PairContraction.private_or_single_leaf
#print axioms Mobius.PairContraction.private_or_leaf_budget
#print axioms Mobius.PairContraction.private_or_size_budget
#print axioms Mobius.PairContraction.private_or_small_size_fraction
#print axioms Mobius.PairContraction.paired_zero_size_step
#print axioms Mobius.PairContraction.paired_zero_quarter
#print axioms Mobius.PairContraction.paired_zero_even_density
#print axioms Mobius.PairContraction.paired_zero_odd_density
#print axioms Mobius.PairContraction.paired_zero_density
#print axioms Mobius.PairContraction.observable_substitution
#print axioms Mobius.PairContraction.window_step_budget
#print axioms Mobius.PairContraction.window_packing_budget
#print axioms Mobius.PairContraction.oriented_pair_budget
#print axioms Mobius.PairContraction.near_forces_ratio
#print axioms Mobius.PairContraction.dispatch_is_near
#print axioms Mobius.PairContraction.growing_window
#print axioms Mobius.ThreeFaceColoring.choices_iff
#print axioms Mobius.ThreeFaceRealization.finite_graph_iff
#print axioms Mobius.ThreeFaceRealization.board_injective
#print axioms Mobius.ThreeFaceMemory.exact_states
#print axioms Mobius.CommonCoreSignature.station_law
#print axioms Mobius.CommonCoreQuery.physical_query_iff
#print axioms Mobius.CommonCoreQuery.physical_bits_exact
#print axioms Mobius.ThreeFaceProbeJoin.boards_iff
#print axioms Mobius.ThreeFaceProbeJoin.memo_exact
#print axioms Mobius.ThreeFaceProbeJoin.left_query_independent
#print axioms Mobius.ThreeFaceProbeJoin.right_graph_independent
#print axioms Mobius.ThreeFaceSoft.cap_penalties
#print axioms Mobius.ThreeFaceSoft.soft_network
#print axioms Mobius.ThreeFaceDeletion.delete_any
#print axioms Mobius.ThreeFaceDeletion.soft_finite
#print axioms Mobius.ThreeFaceDeletion.delete_any_finite
