"""Directly integrate the original closed-contour A_F and audit its split.

Uses the flat packet plateau (a compactly supported L1 window, hence entire
packet functions) and a sharp stable core. This is a finite numerical audit;
it is independent of the stationary/HLZ reductions.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy import special

try:
    from scripts.compute_true_matrix import analytic_packet, zeta_with_derivatives
except ModuleNotFoundError as exc:
    if exc.name != "scripts":
        raise
    from compute_true_matrix import analytic_packet, zeta_with_derivatives


def fields(s: np.ndarray, L: float, h: float) -> dict[str, np.ndarray]:
    z, dz, ddz = zeta_with_derivatives(s, h)
    p = -dz / z
    q = ddz / z - (dz / z) ** 2
    def f_at(x: np.ndarray) -> np.ndarray:
        return -.5 * np.log(np.pi) + .25 * (
            special.digamma((1 - x) / 2) + special.digamma(x / 2)
        )
    f = f_at(s)
    fp = (f_at(s - 2*h) - 8*f_at(s - h) + 8*f_at(s + h) - f_at(s + 2*h)) / (12*h)
    chi_recip = np.exp(
        (.5 - s) * np.log(np.pi)
        + special.loggamma(s / 2)
        - special.loggamma((1 - s) / 2)
    )
    curvature = chi_recip * (z * ddz - dz * dz + fp * z * z) / L**2
    z1 = dz + f * z
    z2 = ddz + 2 * f * dz + (fp + f * f) * z
    l1 = (ddz + fp * z + f * dz) / z1
    h_ar = -p + q / (f - p)
    ar = chi_recip * (z * ddz - dz * dz) * h_ar / L**2
    return {
        "z1": z1, "l1": l1, "f": f, "H": f + l1,
        "curvature": curvature, "ar": ar,
        "f_self": f * curvature,
        "fprime_rest": l1 * curvature - ar,
        "zero_direct": chi_recip * z * z2 * z2 / (z1 * L**2),
    }


def packet_legs(
    t: np.ndarray, sigma: np.ndarray, centres: np.ndarray,
    left: float, width: float, packet_width: float, cap_delta: float,
) -> tuple[np.ndarray, np.ndarray]:
    offsets = t[:, None] - centres[None, :]
    displacement = sigma[:, None] - .5
    plus = analytic_packet(offsets, displacement, left, width, packet_width)
    minus = analytic_packet(offsets, -displacement, left, width, packet_width)
    if cap_delta > 0:
        x0, w0 = special.roots_legendre(64)
        cap_x = (x0 + 1) / 2
        cap_w = cap_delta * w0 / 2
        ramp_up = np.exp(-1 / cap_x)
        ramp_down = np.exp(-1 / (1 - cap_x))
        taper = ramp_up / (ramp_up + ramp_down)
        for u, taper_here in (
            (left - cap_delta + cap_delta * cap_x, taper),
            (left + width + cap_delta * cap_x, 1 - taper),
        ):
            amplitude = cap_w * taper_here / np.sqrt(packet_width)
            exponent = (displacement[:, :, None] + 1j * offsets[:, :, None]) * u[None, None, :]
            plus = plus + np.sum(amplitude[None, None, :] * np.exp(exponent), axis=2)
            exponent = (-displacement[:, :, None] + 1j * offsets[:, :, None]) * u[None, None, :]
            minus = minus + np.sum(amplitude[None, None, :] * np.exp(exponent), axis=2)
    return plus, minus


def packet_matrix(
    weights: np.ndarray, t: np.ndarray, sigma: np.ndarray,
    centres: np.ndarray, left: float, width: float, packet_width: float,
    cap_delta: float = 0,
) -> np.ndarray:
    plus, minus = packet_legs(t, sigma, centres, left, width, packet_width, cap_delta)
    return minus.conj().T @ (weights[:, None] * plus)


def matrices_at_nodes(
    s: np.ndarray, ds_weight: np.ndarray, centres: np.ndarray,
    left: float, width: float, packet_width: float, L: float, h: float,
    cap_delta: float,
) -> dict[str, np.ndarray]:
    f = fields(s, L, h)
    t = s.imag
    sigma = s.real
    plus, minus = packet_legs(t, sigma, centres, left, width, packet_width, cap_delta)
    out = {}
    for name in ("l1", "H", "ar", "f_self", "fprime_rest", "zero_direct"):
        scalar = f[name] * f["curvature"] if name in ("l1", "H") else f[name]
        out[name] = minus.conj().T @ ((ds_weight * scalar / (2j * np.pi))[:, None] * plus)
    return out


def choose_good_height(base: float, L: float, h: float) -> tuple[float, float]:
    candidates = base + np.linspace(.05, .95, 19)
    sigma = np.linspace(-1, 2, 301)
    scores = []
    for height in candidates:
        z1 = fields(sigma + 1j * height, L, h)["z1"]
        scores.append(float(np.min(np.abs(z1))))
    best = int(np.argmax(scores))
    return float(candidates[best]), scores[best]


def hermitian_spectrum(a: np.ndarray) -> dict:
    eig = np.linalg.eigvalsh((a + a.conj().T) / 2)
    neg = eig[eig < 0]
    return {
        "dimension": len(eig), "negative_count": len(neg),
        "negative_squared_mass_fraction": float(np.sum(neg**2) / np.sum(eig**2)),
        "min_eigenvalue": float(eig[0]), "max_eigenvalue": float(eig[-1]),
        "eigenvalues": eig.tolist(),
    }


def compute(args: argparse.Namespace) -> tuple[dict, dict[str, np.ndarray]]:
    T = args.height
    L = np.log(T / (2 * np.pi))
    packet_width = L + args.packet_reserve * np.log(L)
    core_width = L - args.a0 * np.log(L)
    if L <= 1 or core_width <= 0 or core_width > L:
        raise ValueError("invalid finite packet/core parameters")
    centres = np.arange(
        np.ceil(T * packet_width / (2 * np.pi)),
        np.floor(2 * T * packet_width / (2 * np.pi)) + 1,
    ) * 2 * np.pi / packet_width
    if args.columns:
        mid = len(centres) // 2
        centres = centres[max(0, mid - args.columns // 2):][:args.columns]
    lower, lower_score = choose_good_height(T, L, args.derivative_step)
    upper, upper_score = choose_good_height(2*T, L, args.derivative_step)
    n_height = int(np.ceil((upper - lower) / args.height_step)) + 1
    t = np.linspace(lower, upper, n_height)
    dt = t[1] - t[0]
    w = np.full(n_height, dt)
    w[0] /= 2
    w[-1] /= 2
    right_s = 2 + 1j*t
    left_s = -1 + 1j*t
    right = matrices_at_nodes(right_s, 1j*w, centres, -packet_width/2, packet_width, packet_width, L, args.derivative_step, args.smooth_cap)
    left = matrices_at_nodes(left_s, -1j*w, centres, -packet_width/2, packet_width, packet_width, L, args.derivative_step, args.smooth_cap)
    x, wx = special.roots_legendre(args.horizontal_nodes)
    sigma = .5 + 1.5*x
    wx = 1.5*wx
    bottom = matrices_at_nodes(sigma + 1j*lower, wx, centres, -packet_width/2, packet_width, packet_width, L, args.derivative_step, args.smooth_cap)
    top = matrices_at_nodes(sigma + 1j*upper, -wx, centres, -packet_width/2, packet_width, packet_width, L, args.derivative_step, args.smooth_cap)
    full_l1 = right["l1"] + left["l1"] + bottom["l1"] + top["l1"]
    full_h = right["H"] + left["H"] + bottom["H"] + top["H"]
    full_zero = right["zero_direct"] + left["zero_direct"] + bottom["zero_direct"] + top["zero_direct"]
    right_ar = right["ar"] + right["ar"].conj().T
    right_self = right["f_self"] + right["f_self"].conj().T
    right_fp = right["fprime_rest"] + right["fprime_rest"].conj().T
    core_s = 2 + 1j*t
    core_fields = fields(core_s, L, args.derivative_step)
    core_ar = packet_matrix(
        w * core_fields["ar"] / (2 * np.pi), t, np.full_like(t, 2), centres,
        -L/2, core_width, packet_width,
    )
    true_core = core_ar + core_ar.conj().T
    horizontal_h = bottom["H"] + top["H"]
    horizontal_f = bottom["f_self"] + top["f_self"]
    closed_f = right["f_self"] + left["f_self"] + horizontal_f
    matrices = {
        "A_F_L1": full_l1, "A_F_H": full_h, "A_F_zero_direct": full_zero,
        "right_H": right["H"], "left_H": left["H"],
        "horizontal_H": horizontal_h,
        "A_ar_full": right_ar, "A_true_core": true_core,
        "A_geom_exact": right_ar - true_core,
        "A_f_self_right": right_self,
        "right_f_self_raw": right["f_self"],
        "left_f_self_raw": left["f_self"],
        "horizontal_f_self": horizontal_f,
        "A_fprime_right": right_fp,
        "centres": centres,
    }
    norm = np.linalg.norm(full_h, ord="fro")
    split = true_core + (right_ar - true_core) + right_self + right_fp + horizontal_h
    result = {
        "height_interval": [lower, upper],
        "boundary_min_abs_z1_sample": [lower_score, upper_score],
        "dimension": len(centres),
        "smooth_cap": args.smooth_cap,
        "height_nodes": n_height,
        "horizontal_nodes": args.horizontal_nodes,
        "norm_A_F": float(norm),
        "A_F_L1_hermitian_relative_residual": float(np.linalg.norm(full_l1-full_l1.conj().T, ord="fro") / norm),
        "A_F_H_hermitian_relative_residual": float(np.linalg.norm(full_h-full_h.conj().T, ord="fro") / norm),
        "closed_L1_vs_H_relative_error": float(np.linalg.norm(full_l1-full_h, ord="fro") / norm),
        "zero_direct_vs_H_relative_error": float(np.linalg.norm(full_zero-full_h, ord="fro") / norm),
        "closed_f_self_relative_error": float(np.linalg.norm(closed_f, ord="fro") / norm),
        "left_vs_right_H_adjoint_relative_error": float(np.linalg.norm(left["H"]-right["H"].conj().T, ord="fro") / norm),
        "left_f_self_vs_negative_adjoint_relative_error": float(np.linalg.norm(left["f_self"]+right["f_self"].conj().T, ord="fro") / norm),
        "exact_split_relative_error": float(np.linalg.norm(full_h-split, ord="fro") / norm),
        "norm_A_true_core": float(np.linalg.norm(true_core, ord="fro")),
        "norm_A_geom_exact": float(np.linalg.norm(right_ar-true_core, ord="fro")),
        "norm_A_f_self_right": float(np.linalg.norm(right_self, ord="fro")),
        "norm_A_fprime_right": float(np.linalg.norm(right_fp, ord="fro")),
        "norm_horizontal_H": float(np.linalg.norm(horizontal_h, ord="fro")),
        "A_F_spectrum": hermitian_spectrum(full_l1),
        "A_true_core_spectrum": hermitian_spectrum(true_core),
    }
    return result, matrices


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=float, default=80)
    parser.add_argument("--packet-reserve", type=float, default=.1)
    parser.add_argument("--a0", type=float, default=.1)
    parser.add_argument("--smooth-cap", type=float, default=0., help="C-infinity transition width beyond the flat packet interval")
    parser.add_argument("--columns", type=int, default=0)
    parser.add_argument("--height-step", type=float, default=.08)
    parser.add_argument("--horizontal-nodes", type=int, default=256)
    parser.add_argument("--derivative-step", type=float, default=.002)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--matrix-output", type=Path)
    args = parser.parse_args()
    result, matrices = compute(args)
    if args.matrix_output:
        args.matrix_output.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(args.matrix_output, **matrices)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
