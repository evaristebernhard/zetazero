import ZetaZero.HardyGaugeInvariantContourForm.SameFormLogDerivative
import ZetaZero.HardyGaugeInvariantContourForm.SameFormContour

/-!
# From `Z₁` zeros to stationary zeros of the analytic Hardy gauge

This file closes the local algebraic part of the M02→M03 seam.  Since
`𝒵' = q Z₁` and the branch `q` never vanishes on the high rectangle, zeros and
simple zeros of `Z₁` are exactly stationary and simple-stationary zeros of the
analytic Hardy gauge.  At such a point the curvature source collapses to the
expected `𝒵 𝒵''` coefficient.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace ZeroSideStationaryGeometry

open HardyGaugeInvariantContourForm

/-- A `Z₁` zero is a stationary point of the analytic Hardy gauge. -/
theorem deriv_hardyGauge_eq_zero_of_zetaOne_eq_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s = 0) :
    deriv (hardyGauge q) s = 0 := by
  rw [deriv_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow s hs, hz1, mul_zero]

/-- At a `Z₁` zero the second Hardy-gauge derivative is simply `q Z₁'`. -/
theorem deriv2_hardyGauge_eq_branch_mul_deriv_zetaOne_of_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s = 0) :
    deriv (deriv (hardyGauge q)) s = q s * deriv zetaOne s := by
  rw [deriv2_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow hs, hz1]
  ring

/-- At a stationary `Z₁` zero the invariant curvature source is exactly
`𝒵(s) 𝒵''(s)`. -/
theorem hardyCurvature_eq_hardyGauge_mul_deriv2_of_zetaOne_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s = 0) :
    hardyCurvature q s =
      hardyGauge q s * deriv (deriv (hardyGauge q)) s := by
  have hcrit := deriv_hardyGauge_eq_zero_of_zetaOne_eq_zero
    hεT hqa hqpow hs hz1
  simp [hardyCurvature, curvatureJet, hcrit]

/-- Simple `Z₁` zeros and simple stationary points of the analytic Hardy gauge
are equivalent on the high rectangle. -/
theorem hardyGauge_simpleStationary_iff_zetaOne_simpleZero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    (deriv (hardyGauge q) s = 0 ∧
      deriv (deriv (hardyGauge q)) s ≠ 0) ↔
      (zetaOne s = 0 ∧ deriv zetaOne s ≠ 0) := by
  have hqne := branch_ne_zero_on_highRectangle hqpow hεT s hs
  constructor
  · rintro ⟨hcrit, hsimple⟩
    have hz1 : zetaOne s = 0 := by
      have hprod : q s * zetaOne s = 0 := by
        rw [← deriv_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow s hs]
        exact hcrit
      exact (mul_eq_zero.mp hprod).resolve_left hqne
    refine ⟨hz1, ?_⟩
    intro hz1'
    apply hsimple
    rw [deriv2_hardyGauge_eq_branch_mul_deriv_zetaOne_of_zero
      hεT hqa hqpow hs hz1, hz1', mul_zero]
  · rintro ⟨hz1, hz1'⟩
    refine ⟨deriv_hardyGauge_eq_zero_of_zetaOne_eq_zero
      hεT hqa hqpow hs hz1, ?_⟩
    rw [deriv2_hardyGauge_eq_branch_mul_deriv_zetaOne_of_zero
      hεT hqa hqpow hs hz1]
    exact mul_ne_zero hqne hz1'

end ZeroSideStationaryGeometry
end ZetaZero
