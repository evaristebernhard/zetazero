from argparse import Namespace

import numpy as np

from scripts.compute_original_contour import compute


def test_original_closed_contour_and_self_block_sign():
    args = Namespace(
        height=80.0, packet_reserve=0.1, a0=0.1, smooth_cap=0.1,
        columns=12, height_step=0.08, horizontal_nodes=256,
        derivative_step=0.002,
    )
    result, matrices = compute(args)
    assert result["closed_f_self_relative_error"] < 1e-4
    assert result["left_f_self_vs_negative_adjoint_relative_error"] < 1e-5
    assert result["left_vs_right_H_adjoint_relative_error"] < 1e-5
    assert result["exact_split_relative_error"] < 1e-5
    assert result["zero_direct_vs_H_relative_error"] < 1e-3
    assert result["norm_A_f_self_right"] > result["norm_A_true_core"]
    assert result["A_F_spectrum"]["negative_count"] == 0
    assert result["A_true_core_spectrum"]["negative_count"] > 0
    omitted = (
        matrices["A_true_core"] + matrices["A_geom_exact"]
        + matrices["A_fprime_right"] + matrices["horizontal_H"]
    )
    self_block = matrices["A_f_self_right"]
    assert np.linalg.norm(matrices["A_F_H"] - omitted - self_block) < 1e-4
