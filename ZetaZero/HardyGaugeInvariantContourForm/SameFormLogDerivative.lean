import ZetaZero.HardyGaugeInvariantContourForm.ZetaOneAnalytic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.Ring

/-!
# Logarithmic-derivative bridge for the same contour form

The Hardy-gauge derivative identity `𝒵' = q Z₁` is already available in
`GaugeDerivative`.  This module differentiates that identity once more and
puts it in the exact logarithmic-derivative form used by the manuscript's
same-form contour identity:

`𝒵'' / 𝒵' = f + Z₁' / Z₁`.

The statement is pointwise on the high rectangle and only excludes zeros of
`Z₁`, exactly where the logarithmic derivative has a pole.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Differentiating `𝒵' = q Z₁` on the open high rectangle gives the exact
second-derivative factorization used before taking logarithmic derivatives. -/
theorem deriv2_hardyGauge_eq_branch_mul_zetaOne
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    deriv (deriv (hardyGauge q)) s =
      q s * (hardyF s * zetaOne s + deriv zetaOne s) := by
  have hqdiff : DifferentiableAt ℂ q s := (hqa s hs).differentiableAt
  have him := highRectangleNhd_im_ne_zero hεT s hs
  have hz1diff : DifferentiableAt ℂ zetaOne s :=
    (analyticAt_zetaOne_of_im_ne_zero him).differentiableAt
  have hrect : highRectangleNhd T₁ T₂ ε ∈ 𝓝 s :=
    (isOpen_highRectangleNhd T₁ T₂ ε).mem_nhds hs
  have hev : deriv (hardyGauge q) =ᶠ[𝓝 s] q * zetaOne := by
    filter_upwards [hrect] with z hz
    exact deriv_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow z hz
  have hderivEq :
      deriv (deriv (hardyGauge q)) s = deriv (q * zetaOne) s :=
    hev.deriv_eq
  rw [deriv_mul hqdiff hz1diff,
    deriv_branch_eq_hardyF_mul hεT hqa hqpow s hs] at hderivEq
  calc
    deriv (deriv (hardyGauge q)) s =
        hardyF s * q s * zetaOne s + q s * deriv zetaOne s := hderivEq
    _ = q s * (hardyF s * zetaOne s + deriv zetaOne s) := by ring

/-- Pointwise form of the manuscript identity
`𝒵'' / 𝒵' = f + Z₁' / Z₁` away from the poles of `Z₁'/Z₁`. -/
theorem hardyGauge_second_over_first_eq
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s ≠ 0) :
    deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s =
      hardyF s + deriv zetaOne s / zetaOne s := by
  have hqne := branch_ne_zero_on_highRectangle hqpow hεT s hs
  rw [deriv_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow s hs,
    deriv2_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow hs]
  field_simp [hqne, hz1]

/-- The same identity expressed using Mathlib's `logDeriv`. -/
theorem logDeriv_hardyGauge_deriv_eq
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s ≠ 0) :
    logDeriv (deriv (hardyGauge q)) s = hardyF s + logDeriv zetaOne s := by
  unfold logDeriv
  exact hardyGauge_second_over_first_eq hεT hqa hqpow hs hz1

end HardyGaugeInvariantContourForm
end ZetaZero
