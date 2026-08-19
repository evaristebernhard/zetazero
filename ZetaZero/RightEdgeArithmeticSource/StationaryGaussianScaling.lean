import ZetaZero.RightEdgeArithmeticSource.StationaryLocalGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Gaussian scaling at the one-chi saddle

This module introduces the canonical local coordinate

`v = 1 + y / sqrt(t_*)`

and records the exact scale identities that convert the normalized cubic
Taylor estimate into a Gaussian phase with an `O(|y|^3 / sqrt(t_*))` error.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Canonical stationary-phase coordinate around the normalized saddle. -/
def stationaryGaussianCoordinate (eta y : ℝ) : ℝ :=
  1 + y / Real.sqrt (stationaryScale eta)

/-- The Gaussian coordinate is centered exactly at `v=1`. -/
theorem stationaryGaussianCoordinate_sub_one
    (eta y : ℝ) :
    stationaryGaussianCoordinate eta y - 1 =
      y / Real.sqrt (stationaryScale eta) := by
  simp [stationaryGaussianCoordinate]

/-- The quadratic phase rescales exactly to `y^2`. -/
theorem stationaryGaussianCoordinate_quadratic_scale
    {eta y : ℝ} (heta : 0 < eta) :
    stationaryScale eta * (stationaryGaussianCoordinate eta y - 1) ^ 2 = y ^ 2 := by
  have hspos := stationaryScale_pos heta
  have hrpos : 0 < Real.sqrt (stationaryScale eta) := Real.sqrt_pos.2 hspos
  have hrne := hrpos.ne'
  rw [stationaryGaussianCoordinate_sub_one]
  rw [div_pow]
  rw [Real.sq_sqrt hspos.le]
  field_simp [hrne]

/-- The cubic Taylor scale becomes precisely `|y|^3 / sqrt(t_*)`. -/
theorem stationaryGaussianCoordinate_cubic_scale
    {eta y : ℝ} (heta : 0 < eta) :
    stationaryScale eta * |stationaryGaussianCoordinate eta y - 1| ^ 3 =
      |y| ^ 3 / Real.sqrt (stationaryScale eta) := by
  have hspos := stationaryScale_pos heta
  have hrpos : 0 < Real.sqrt (stationaryScale eta) := Real.sqrt_pos.2 hspos
  have hrne := hrpos.ne'
  rw [stationaryGaussianCoordinate_sub_one, abs_div, abs_of_pos hrpos, div_pow]
  field_simp [hrne]
  rw [Real.sq_sqrt hspos.le]
  ring

/-- A `sqrt(t_*)/2` window in Gaussian coordinates lies inside the standard
normalized saddle window `[1/2, 3/2]`. -/
theorem stationaryGaussianCoordinate_mem_standard_window
    {eta y : ℝ} (heta : 0 < eta)
    (hy : |y| ≤ Real.sqrt (stationaryScale eta) / 2) :
    (1 / 2 : ℝ) ≤ stationaryGaussianCoordinate eta y ∧
      stationaryGaussianCoordinate eta y ≤ 3 / 2 := by
  have hspos := stationaryScale_pos heta
  have hrpos : 0 < Real.sqrt (stationaryScale eta) := Real.sqrt_pos.2 hspos
  have habs := abs_le.mp hy
  have hylo : -(1 / 2 : ℝ) ≤ y / Real.sqrt (stationaryScale eta) := by
    rw [le_div_iff₀ hrpos]
    nlinarith [habs.1]
  have hyhi : y / Real.sqrt (stationaryScale eta) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hrpos]
    nlinarith [habs.2]
  unfold stationaryGaussianCoordinate
  constructor <;> linarith

/-- Quantitative Gaussian normal form for the centered normalized phase. -/
theorem stationaryGaussianCoordinate_phase_remainder
    {eta y : ℝ} (heta : 0 < eta)
    (hy : |y| ≤ Real.sqrt (stationaryScale eta) / 2) :
    |stationaryScale eta *
          (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) -
        y ^ 2 / 2| ≤
      (2 / 3 : ℝ) * |y| ^ 3 / Real.sqrt (stationaryScale eta) := by
  have hspos := stationaryScale_pos heta
  have hwindow := stationaryGaussianCoordinate_mem_standard_window heta hy
  have hrem := normalizedOneChiPhase_quadratic_remainder_abs_le hwindow.1 hwindow.2
  have hscaled := mul_le_mul_of_nonneg_left hrem hspos.le
  have hscaled' :
      |stationaryScale eta *
          (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) -
            (-1 + (stationaryGaussianCoordinate eta y - 1) ^ 2 / 2))| ≤
        stationaryScale eta *
          ((2 / 3 : ℝ) * |stationaryGaussianCoordinate eta y - 1| ^ 3) := by
    rw [abs_mul, abs_of_pos hspos]
    exact hscaled
  have hquad := stationaryGaussianCoordinate_quadratic_scale (eta := eta) (y := y) heta
  have hcubic := stationaryGaussianCoordinate_cubic_scale (eta := eta) (y := y) heta
  have hremainderRewrite :
      stationaryScale eta *
          (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) -
            (-1 + (stationaryGaussianCoordinate eta y - 1) ^ 2 / 2)) =
        stationaryScale eta *
            (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) -
          y ^ 2 / 2 := by
    rw [← hquad]
    ring
  rw [hremainderRewrite] at hscaled'
  calc
    |stationaryScale eta *
          (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) -
        y ^ 2 / 2| ≤
        stationaryScale eta *
          ((2 / 3 : ℝ) * |stationaryGaussianCoordinate eta y - 1| ^ 3) := hscaled'
    _ = (2 / 3 : ℝ) *
        (stationaryScale eta * |stationaryGaussianCoordinate eta y - 1| ^ 3) := by ring
    _ = (2 / 3 : ℝ) * |y| ^ 3 / Real.sqrt (stationaryScale eta) := by
      rw [hcubic]
      ring

end RightEdgeArithmeticSource
end ZetaZero
