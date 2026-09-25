"""Finite mean-zero comparison of the true matrix with the manuscript model.

This diagnoses an explicitly chosen finite packet lattice.  It is not the
paper's unspecified retained-space beta-minus certificate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy import linalg, special


def g_log(rho: np.ndarray) -> np.ndarray:
    return (
        -7 * rho**4 / 6 + 2 * rho**3 - rho**2
        + np.e**2 / 8 * (
            (2 * rho**2 - 4 * rho + 3) * np.cosh(2 * rho)
            - 4 * rho**2 + 4 * rho - 3
        )
    )


def comparison_matrix(
    centres: np.ndarray, core_left: float, core_right: float,
    L: float, packet_width: float, nodes: int,
) -> np.ndarray:
    """Gauss quadrature of K(r,s)=G_log(1-|r-s|) on the flat core."""
    x0, w0 = special.roots_legendre(nodes)
    length_r = (core_right - core_left) / L
    r = (x0 + 1) * length_r / 2
    weights = w0 * length_r / 2
    kernel = g_log(1 - np.abs(r[:, None] - r[None, :]))
    analysis = np.sqrt(L / packet_width) * np.exp(
        1j * (core_left + L * r[:, None]) * centres[None, :]
    )
    p = analysis.conj().T @ (
        (weights[:, None] * kernel * weights[None, :]) @ analysis
    )
    return (p + p.conj().T) / 2


def compare(matrix_path: Path, metadata_path: Path, nodes: int, max_condition: float) -> tuple[dict, np.ndarray]:
    data = np.load(matrix_path)
    meta = json.loads(metadata_path.read_text())
    a = data["A_true"]
    g = data["G_reference"]
    mean = data["mean"]
    p = comparison_matrix(
        data["centres"], *meta["core_interval"], meta["L"],
        meta["packet_width"], nodes,
    )
    basis = linalg.null_space(mean[None, :])
    aa = basis.conj().T @ a @ basis
    gg = basis.conj().T @ g @ basis
    pp = basis.conj().T @ p @ basis
    gram_eigenvalues = np.linalg.eigvalsh(gg)
    condition = float(gram_eigenvalues[-1] / gram_eigenvalues[0])
    result = {
        "matrix": str(matrix_path), "quadrature_nodes": nodes,
        "mean_zero_dimension": aa.shape[0],
        "reference_gram_condition": condition,
        "comparison_frobenius_norm": float(np.linalg.norm(pp, ord="fro")),
    }
    if not np.isfinite(condition) or condition > max_condition:
        result["generalized_spectrum"] = "skipped: reference Gram ill-conditioned at this precision"
        return result, p
    floor = linalg.eigh(pp, gg, eigvals_only=True)
    defect = linalg.eigh(aa - pp, gg, eigvals_only=True)
    neg = defect[defect < 0]
    result.update({
        "comparison_over_gram_min": float(floor[0]),
        "comparison_over_gram_max": float(floor[-1]),
        "defect_negative_count": len(neg),
        "defect_negative_squared_mass": float(np.sum(neg**2)),
        "defect_min_eigenvalue": float(defect[0]),
        "defect_max_eigenvalue": float(defect[-1]),
    })
    return result, p


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--nodes", type=int, default=512)
    parser.add_argument("--max-condition", type=float, default=1e10)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--model-output", type=Path)
    args = parser.parse_args()
    result, model = compare(args.matrix, args.metadata, args.nodes, args.max_condition)
    if args.model_output:
        args.model_output.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(args.model_output, P_comparison=model)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
