import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Algebraic stationary residue blocks

The analytic residue theorem will later produce scalar weights at real
stationary points and `2 × 2` conjugate-pair blocks at nonreal stationary
points.  This file isolates the finite-dimensional algebra of those blocks from
all contour and zeta-function arguments.
-/

open Complex
open scoped Matrix ComplexConjugate

noncomputable section

namespace ZetaZero
namespace ZeroSideStationaryGeometry

/-- Real stationary residue weight after the positive `L⁻²` normalization. -/
def realStationaryWeight (L H H₂ : ℝ) : ℝ :=
  -(H * H₂) / L ^ 2

/-- A real stationary point with `H(c) H''(c) > 0` contributes a strictly
negative scalar residue weight. -/
theorem realStationaryWeight_neg
    {L H H₂ : ℝ} (hL : 0 < L) (hgood : 0 < H * H₂) :
    realStationaryWeight L H H₂ < 0 := by
  unfold realStationaryWeight
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hgood) (sq_pos_of_pos hL)

/-- Hermitian residue block attached to a nonreal conjugate pair. -/
def conjugatePairBlock (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, star w], ![w, 0]]

/-- The conjugate-pair residue block is Hermitian. -/
theorem conjugatePairBlock_isHermitian (w : ℂ) :
    (conjugatePairBlock w).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjugatePairBlock]

/-- Its determinant is `-|w|²`, the algebraic signature test behind the fact
that a nonzero conjugate pair contributes one positive and one negative
direction. -/
theorem det_conjugatePairBlock (w : ℂ) :
    Matrix.det (conjugatePairBlock w) = -(star w * w) := by
  rw [Matrix.det_fin_two]
  simp [conjugatePairBlock]

/-- In particular, a nonzero conjugate-pair block is nonsingular. -/
theorem det_conjugatePairBlock_ne_zero {w : ℂ} (hw : w ≠ 0) :
    Matrix.det (conjugatePairBlock w) ≠ 0 := by
  rw [det_conjugatePairBlock]
  simp [hw]

/-- Real quadratic form represented by the conjugate-pair block. -/
def conjugatePairQuadratic (w : ℂ) (x : Fin 2 → ℂ) : ℝ :=
  (conj (x 0) * conj w * x 1 + conj (x 1) * w * x 0).re

/-- An explicit vector on which a nonzero conjugate-pair block is negative. -/
def conjugatePairNegativeVector (w : ℂ) : Fin 2 → ℂ :=
  ![(1 : ℂ), -w]

/-- Evaluation on the explicit negative vector is `-2 |w|²`. -/
theorem conjugatePairQuadratic_negativeVector (w : ℂ) :
    conjugatePairQuadratic w (conjugatePairNegativeVector w) =
      -2 * Complex.normSq w := by
  simp [conjugatePairQuadratic, conjugatePairNegativeVector,
    ← Complex.normSq_eq_conj_mul_self]
  ring

/-- Hence a nonzero conjugate pair really contributes a negative direction. -/
theorem conjugatePairQuadratic_negativeVector_neg {w : ℂ} (hw : w ≠ 0) :
    conjugatePairQuadratic w (conjugatePairNegativeVector w) < 0 := by
  rw [conjugatePairQuadratic_negativeVector, Complex.normSq_eq_norm_sq]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  nlinarith

end ZeroSideStationaryGeometry
end ZetaZero
