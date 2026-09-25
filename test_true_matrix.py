from argparse import Namespace

import numpy as np

from scripts.compute_true_matrix import compute, right_edge_source


def test_fft_true_matrix_matches_direct_packet_integrals():
    args = Namespace(
        height=80.0, packet_reserve=1.0, core_fraction=0.95, a0=None,
        height_oversample=12, u_step=0.003, max_fft=1 << 18,
        derivative_step=0.002, source="ar", columns=12,
        direct_check=True, matrix_output=None,
    )
    result = compute(args)
    assert result["matrix_fft_vs_analytic_relative_frobenius_error"] < 2e-4
    assert result["hermitian_residual"] == 0


def test_exact_source_is_log_plus_residual_and_derivative_step_converges():
    t = np.array([80.0, 100.0, 140.0])
    L = np.log(80 / (2 * np.pi))
    ar = right_edge_source(t, L, 0.002, "ar")
    log = right_edge_source(t, L, 0.002, "log")
    residual = right_edge_source(t, L, 0.002, "residual")
    refined = right_edge_source(t, L, 0.001, "ar")
    assert np.max(np.abs(ar - log - residual)) < 1e-10
    assert np.max(np.abs(ar - refined)) / np.max(np.abs(refined)) < 2e-5
