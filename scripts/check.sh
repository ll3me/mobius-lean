#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
python3 scripts/bootstrap.py
if [ -x .toolchain/bin/lake ]; then
  PATH="$PWD/.toolchain/bin:$PATH"
  export PATH
fi
lean --version
lake build
lake env lean Audit.lean
lake env lean experiments/EncodedCuts.lean
lake env lean experiments/HamiltonianAffineCut.lean
lake env lean -DwarningAsError=true experiments/SublinearPairSeparation.lean
python3 experiments/sign_obstruction.py
python3 experiments/two_phases.py
python3 experiments/contractions.py
python3 experiments/direction_laws.py 6
python3 experiments/optimal_support.py
python3 experiments/optimal_residual.py
python3 experiments/second_weight.py
python3 experiments/locked_rank_curve.py
python3 experiments/five_slices.py
python3 experiments/five_collisions.py
python3 experiments/five_margins.py
python3 experiments/rank_symplectic.py
python3 experiments/naslund_slices.py
python3 experiments/port_geometry.py
python3 experiments/one_in_three_geometry.py
python3 experiments/cubic_ports.py
python3 experiments/port_cut.py
python3 experiments/port_k4.py
python3 experiments/tropical_controls.py
python3 experiments/crossing_controls.py
python3 experiments/unary_sat.py --self-test
python3 experiments/recognized_gadgets.py
python3 experiments/overlap_fibers.py
python3 experiments/double_fan.py
python3 experiments/whole_board_matching.py
python3 experiments/axis_relations.py
python3 experiments/full_board_caps.py
python3 experiments/port_gap.py
python3 experiments/board_input_bits.py
python3 experiments/read_bounded_boards.py
python3 experiments/semantic_board_queries.py
python3 experiments/three_face_profiles.py
python3 experiments/common_core_signatures.py
python3 experiments/free_direction_coloring.py
python3 experiments/face_multiplicity.py
python3 experiments/color_deletion.py
python3 experiments/hybrid_matching_boards.py
python3 experiments/determinant_matching.py
python3 experiments/hamiltonian_boards.py
python3 experiments/cycle_cover_queries.py
python3 experiments/postread_switches.py
python3 experiments/paired_contraction.py
python3 experiments/signed_tour_sweep.py
python3 experiments/paired_fanout.py
python3 experiments/oriented_contraction.py
python3 experiments/staged_contraction.py
python3 experiments/joint_pair_support.py
python3 experiments/negative_gate_loss.py
python3 experiments/paired_cover_witnesses.py
python3 experiments/observable_rewrites.py
python3 experiments/pair_trigger_matching.py
python3 experiments/single_cycle_controls.py
python3 experiments/absorbing_readers.py
python3 experiments/private_reader_forest.py
python3 experiments/simultaneous_zero_pins.py
python3 experiments/paired_tag_ports.py
python3 experiments/paired_matrix_tests.py
python3 experiments/flexible_pair_budget.py
python3 experiments/four_pair_budget.py
python3 experiments/alternating_cut.py
python3 experiments/matched_matrix_budget.py
python3 experiments/paired_guard_pooling.py
python3 experiments/sunflower_charges.py
python3 experiments/sunflower_core_control.py
python3 experiments/pair_certificate.py
python3 experiments/path_list_masking.py
python3 experiments/read_one_contraction.py
python3 experiments/shared_chains.py
python3 experiments/defect_paths.py
python3 experiments/direction_polarity.py
python3 experiments/paired_ports.py
python3 experiments/three_face_queries.py
