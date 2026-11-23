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
