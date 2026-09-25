"""Finite-scale right-edge matrix from sections 03 and 08 of the manuscript.

This is a numerical experiment, not an asymptotic certificate.  The packet
centres are an exact lattice, the core multiplier is a sharp restriction inside
the flat packet plateau, and the horizontal edges are not included.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy import linalg, special


def zeta_with_derivatives(s: np.ndarray, h: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Fourth-order central differences, using SciPy's complex zeta evaluator."""
    z = special.zeta(s)
    zm2 = special.zeta(s - 2 * h)
    zm1 = special.zeta(s - h)
    zp1 = special.zeta(s + h)
    zp2 = special.zeta(s + 2 * h)
    dz = (zm2 - 8 * zm1 + 8 * zp1 - zp2) / (12 * h)
    ddz = (-zm2 + 16 * zm1 - 30 * z + 16 * zp1 - zp2) / (12 * h * h)
    return z, dz, ddz


def right_edge_source(t: np.ndarray, log_scale: float, derivative_step: float, source_part: str = "ar") -> np.ndarray:
    """chi(1-s) * zeta(s)^2 * Q(s) * H(s) / L^2 at s=2+it."""
    s = 2.0 + 1j * t
    z, dz, ddz = zeta_with_derivatives(s, derivative_step)
    p = -dz / z
    q = ddz / z - (dz / z) ** 2
    f = -0.5 * np.log(np.pi) + 0.25 * (
        special.digamma((1 - s) / 2) + special.digamma(s / 2)
    )
    chi_recip = np.exp(
        (0.5 - s) * np.log(np.pi)
        + special.loggamma(s / 2)
        - special.loggamma((1 - s) / 2)
    )
    h_ar = -p + q / (f - p)
    if source_part == "ar":
        source = h_ar
    else:
        shifted = s - 2 / log_scale
        shifted_z, shifted_dz, _ = zeta_with_derivatives(shifted, derivative_step)
        shifted_p = -shifted_dz / shifted_z
        h_log = -2 * p + shifted_p
        source = h_log if source_part == "log" else h_ar - h_log
    return chi_recip * z * z * q * source / (log_scale * log_scale)


def analytic_packet(offset: np.ndarray, sigma: float, left: float, width: float, packet_width: float) -> np.ndarray:
    """Closed-form integral of a flat core packet (used for FFT validation)."""
    a = sigma + 1j * offset
    return np.exp(a * (left + width / 2)) * width * np.sinh(a * width / 2) / (a * width / 2) / np.sqrt(packet_width)


def packet_table_fft(
    offsets: np.ndarray, sigma: float, left: float, width: float,
    packet_width: float, height_step: float, nfft: int,
) -> np.ndarray:
    """Midpoint quadrature in u, transformed at all required frequencies by FFT."""
    du = 2 * np.pi / (nfft * height_step)
    # Cell centres follow left + (j+1/2)du.  The last cell is clipped to
    # the exact core endpoint, avoiding a first-order support error.
    count = int(np.ceil(width / du))
    lengths = np.minimum(du, width - np.arange(count) * du)
    centres = left + np.arange(count) * du + lengths / 2
    samples = np.zeros(nfft, dtype=complex)
    samples[:count] = lengths * np.exp(sigma * centres) / np.sqrt(packet_width)
    transformed = nfft * np.fft.ifft(samples)
    frequency_indices = np.rint(offsets / height_step).astype(int)
    if not np.allclose(frequency_indices * height_step, offsets, atol=1e-9):
        raise ValueError("packet offsets must lie on the FFT frequency grid")
    return transformed[frequency_indices % nfft] * np.exp(1j * offsets * (left + du / 2))


def voronoi_weights(t: np.ndarray, lower: float, upper: float, step: float) -> np.ndarray:
    return np.maximum(0, np.minimum(upper, t + step / 2) - np.maximum(lower, t - step / 2))


def reference_gram(centres: np.ndarray, left: float, width: float, packet_width: float, L: float) -> tuple[np.ndarray, np.ndarray]:
    """The paper's triangular primitive Gram and its mean constraint."""
    nodes = max(128, int(np.ceil(4 * np.max(centres) * width / np.pi)))
    x0, w0 = special.roots_legendre(nodes)
    x = (x0 + 1) * width / 2
    weights = w0 * width / 2
    primitive = (
        np.exp(1j * centres[None, :] * left)
        * np.expm1(1j * x[:, None] * centres[None, :])
        / (1j * centres[None, :] * np.sqrt(packet_width))
    )
    mean = (
        np.exp(1j * centres * left)
        * np.expm1(1j * width * centres)
        / (1j * centres * np.sqrt(packet_width))
    )
    gram = (2 / L**2) * (primitive.conj().T @ (weights[:, None] * primitive))
    return (gram + gram.conj().T) / 2, mean


def compute(args: argparse.Namespace) -> dict:
    t0 = args.height
    L = np.log(t0 / (2 * np.pi))
    if L <= 1:
        raise ValueError("height must exceed 2*pi*e")
    if not (0 < args.packet_reserve < 2):
        raise ValueError("packet_reserve must lie in (0,2), as in the manuscript")
    if args.a0 is not None and args.a0 < 0:
        raise ValueError("a0 must be nonnegative")
    if args.height_oversample <= 0 or args.u_step <= 0 or args.derivative_step <= 0:
        raise ValueError("sampling steps and oversampling must be positive")
    packet_width = L + args.packet_reserve * np.log(L)
    core_width = L - args.a0 * np.log(L) if args.a0 is not None else args.core_fraction * L
    core_left = -L / 2
    if not (0 < core_width <= L):
        raise ValueError("core width must lie in (0,L]; reduce a0 or adjust core_fraction")
    spacing = 2 * np.pi / packet_width
    centres = np.arange(np.ceil(t0 / spacing), np.floor(2 * t0 / spacing) + 1) * spacing
    if args.columns:
        mid = len(centres) // 2
        half = args.columns // 2
        centres = centres[max(0, mid - half):max(0, mid - half) + args.columns]
    height_step = spacing / args.height_oversample
    indices = np.arange(
        int(np.floor(t0 / height_step - 0.5)),
        int(np.ceil(2 * t0 / height_step + 0.5)) + 1,
    )
    t = indices * height_step
    weights = voronoi_weights(t, t0, 2 * t0, height_step)
    keep = weights > 0
    t, weights = t[keep], weights[keep]
    offsets = t[:, None] - centres[None, :]
    max_frequency = np.max(np.abs(offsets))
    minimum_fft = int(np.ceil(2 * max_frequency / height_step)) + 2
    minimum_resolution = int(np.ceil(2 * np.pi / (height_step * args.u_step)))
    nfft = 1 << (max(minimum_fft, minimum_resolution) - 1).bit_length()
    if nfft > args.max_fft:
        raise ValueError(f"required FFT length {nfft} exceeds max_fft={args.max_fft}")
    sigma = 1.5  # c - 1/2, for the manuscript's fixed c=2
    plus = packet_table_fft(offsets, sigma, core_left, core_width, packet_width, height_step, nfft)
    minus = packet_table_fft(offsets, -sigma, core_left, core_width, packet_width, height_step, nfft)
    source = right_edge_source(t, L, args.derivative_step, args.source)
    weighted = (weights * source) / (2 * np.pi)
    right = minus.conj().T @ (weighted[:, None] * plus)
    hermitian = right + right.conj().T
    gram, mean = reference_gram(centres, core_left, core_width, packet_width, L)
    if args.matrix_output:
        args.matrix_output.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(args.matrix_output, A_true=hermitian, G_reference=gram, mean=mean, centres=centres, height_nodes=t, height_weights=weights)
    eigenvalues = np.linalg.eigvalsh(hermitian)
    mean_zero_basis = linalg.null_space(mean[None, :])
    mean_zero_eigenvalues = np.linalg.eigvalsh(mean_zero_basis.conj().T @ hermitian @ mean_zero_basis)
    gram_eigenvalues = np.linalg.eigvalsh(gram)
    scale = np.linalg.norm(hermitian, ord="fro")
    negative = eigenvalues[eigenvalues < 0]
    # Direct packet integration checks the FFT discretization alone.
    check_rows = np.linspace(0, len(t) - 1, min(11, len(t)), dtype=int)
    check_cols = np.linspace(0, len(centres) - 1, min(7, len(centres)), dtype=int)
    test_offset = offsets[np.ix_(check_rows, check_cols)]
    fft_error = max(
        np.max(np.abs(plus[np.ix_(check_rows, check_cols)] - analytic_packet(test_offset, sigma, core_left, core_width, packet_width))),
        np.max(np.abs(minus[np.ix_(check_rows, check_cols)] - analytic_packet(test_offset, -sigma, core_left, core_width, packet_width))),
    )
    matrix_check = None
    if args.direct_check:
        direct_plus = analytic_packet(offsets, sigma, core_left, core_width, packet_width)
        direct_minus = analytic_packet(offsets, -sigma, core_left, core_width, packet_width)
        direct_right = direct_minus.conj().T @ (weighted[:, None] * direct_plus)
        direct_matrix = direct_right + direct_right.conj().T
        matrix_check = float(np.linalg.norm(hermitian - direct_matrix, ord="fro") / np.linalg.norm(direct_matrix, ord="fro"))
    max_abs = float(np.max(np.abs(eigenvalues)))
    return {
        "definition": "section 08 right-edge form, sharp flat-core lattice specialization",
        "source_part": args.source,
        "height_interval": [t0, 2 * t0],
        "L": float(L), "packet_width": float(packet_width),
        "core_interval": [float(core_left), float(core_left + core_width)],
        "effective_a0": float((L - core_width) / np.log(L)),
        "columns": len(centres), "height_nodes": len(t), "fft_length": nfft,
        "height_step": float(height_step), "u_step": float(2 * np.pi / (nfft * height_step)),
        "derivative_step": args.derivative_step,
        "fft_packet_max_abs_error": float(fft_error),
        "matrix_fft_vs_analytic_relative_frobenius_error": matrix_check,
        "hermitian_residual": float(np.max(np.abs(hermitian - hermitian.conj().T))),
        "frobenius_norm": float(scale),
        "reference_gram_max_eigenvalue": float(gram_eigenvalues[-1]),
        "reference_gram_min_eigenvalue": float(gram_eigenvalues[0]),
        "negative_count": len(negative),
        "negative_fraction": float(len(negative) / len(eigenvalues)),
        "negative_squared_mass_fraction": float(np.sum(negative ** 2) / np.sum(eigenvalues ** 2)),
        "negative_max_abs_over_frobenius": float(-negative[0] / scale) if len(negative) else 0.0,
        "negative_median_abs": float(np.median(np.abs(negative))) if len(negative) else 0.0,
        "max_abs_eigenvalue": max_abs,
        "near_zero_count_at_1e-8_max_abs": int(np.sum(np.abs(eigenvalues) < 1e-8 * max_abs)),
        "mean_zero_negative_count": int(np.sum(mean_zero_eigenvalues < 0)),
        "mean_zero_negative_squared_mass_fraction": float(
            np.sum(mean_zero_eigenvalues[mean_zero_eigenvalues < 0] ** 2)
            / np.sum(mean_zero_eigenvalues ** 2)
        ),
        "eigenvalues": eigenvalues.tolist(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=float, default=80)
    parser.add_argument("--packet-reserve", type=float, default=1)
    parser.add_argument("--core-fraction", type=float, default=0.75)
    parser.add_argument("--a0", type=float, help="use the manuscript W=L-a0*log(L) core instead of core-fraction")
    parser.add_argument("--height-oversample", type=int, default=12)
    parser.add_argument("--u-step", type=float, default=0.003)
    parser.add_argument("--max-fft", type=int, default=1 << 18)
    parser.add_argument("--derivative-step", type=float, default=0.002)
    parser.add_argument("--source", choices=["ar", "log", "residual"], default="ar")
    parser.add_argument("--columns", type=int, default=0)
    parser.add_argument("--direct-check", action="store_true", help="compare the full FFT matrix with analytic packet integrals")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--matrix-output", type=Path, help="save A_true, reference Gram, mean row, centres, and height quadrature as NPZ")
    args = parser.parse_args()
    result = compute(args)
    payload = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n")
    else:
        print(payload)


if __name__ == "__main__":
    main()
