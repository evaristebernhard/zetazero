import ZetaZero.RightEdgeArithmeticSource.StationaryPhaseGeometry
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Exact normalization of the one-chi stationary main term

The stationary-phase theorem itself contributes the Gaussian Hessian factor.
This file proves the exact algebraic normalization used by the manuscript once
that theorem is applied: the Stirling amplitude at the saddle is `eta^(-1/2)`,
the Gaussian factor is `2*pi*sqrt eta`, and the external `1/(2*pi)` makes the
net scalar prefactor exactly `1`.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The saddle scale divided by `2*pi` is exactly the carrier ratio. -/
@[simp] theorem stationaryScale_div_two_pi (eta : ℝ) :
    stationaryScale eta / (2 * Real.pi) = eta := by
  unfold stationaryScale
  field_simp [Real.pi_ne_zero]

/-- Stirling amplitude evaluated at the exact saddle. -/
def saddleStirlingAmplitude (eta c : ℝ) : ℝ :=
  (stationaryScale eta / (2 * Real.pi)) ^ (c - (1 / 2 : ℝ)) * eta ^ (-c)

/-- The powers of the carrier in the Stirling amplitude combine to
`eta^(-1/2)`, independently of the right-edge real part `c`. -/
theorem saddleStirlingAmplitude_eq
    {eta c : ℝ} (heta : 0 < eta) :
    saddleStirlingAmplitude eta c = eta ^ (-(1 / 2 : ℝ)) := by
  unfold saddleStirlingAmplitude
  rw [stationaryScale_div_two_pi]
  rw [← Real.rpow_add heta]
  congr 1
  ring

/-- Gaussian Hessian factor after inserting `Phi''(t_*)=1/t_*`. -/
def gaussianSaddleFactor (eta : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * stationaryScale eta)

/-- The Gaussian factor is exactly `2*pi*sqrt eta`. -/
theorem gaussianSaddleFactor_eq
    (eta : ℝ) :
    gaussianSaddleFactor eta = 2 * Real.pi * Real.sqrt eta := by
  unfold gaussianSaddleFactor stationaryScale
  calc
    Real.sqrt (2 * Real.pi * (2 * Real.pi * eta)) =
        Real.sqrt ((2 * Real.pi * (2 * Real.pi)) * eta) := by
      congr 1
      ring
    _ = Real.sqrt (2 * Real.pi * (2 * Real.pi)) * Real.sqrt eta := by
      rw [Real.sqrt_mul (mul_self_nonneg (2 * Real.pi)) eta]
    _ = 2 * Real.pi * Real.sqrt eta := by
      rw [Real.sqrt_mul_self]
      positivity

/-- Reciprocal half-power times the positive square root cancels exactly. -/
theorem rpow_neg_half_mul_sqrt
    {eta : ℝ} (heta : 0 < eta) :
    eta ^ (-(1 / 2 : ℝ)) * Real.sqrt eta = 1 := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_add heta]
  norm_num

/-- The complete scalar main-term normalization is exactly one. -/
theorem stationaryMainPrefactor_eq_one
    {eta c : ℝ} (heta : 0 < eta) :
    (1 / (2 * Real.pi)) * saddleStirlingAmplitude eta c * gaussianSaddleFactor eta = 1 := by
  rw [saddleStirlingAmplitude_eq heta, gaussianSaddleFactor_eq eta]
  have hpow := rpow_neg_half_mul_sqrt heta
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc
    (1 / (2 * Real.pi)) * eta ^ (-(1 / 2 : ℝ)) *
        (2 * Real.pi * Real.sqrt eta) =
        eta ^ (-(1 / 2 : ℝ)) * Real.sqrt eta := by
      field_simp [hpi]
    _ = 1 := hpow

end RightEdgeArithmeticSource
end ZetaZero
