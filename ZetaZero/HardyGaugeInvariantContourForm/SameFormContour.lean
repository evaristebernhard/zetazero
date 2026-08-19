import ZetaZero.HardyGaugeInvariantContourForm.SameFormLogDerivative
import ZetaZero.HardyGaugeInvariantContourForm.ContourCancellation
import ZetaZero.HardyGaugeInvariantContourForm.ZetaCurvature
import Mathlib.Tactic.Ring

/-!
# Same-form contour bridge

This module connects the pointwise logarithmic-derivative identity with the
Cauchy--Goursat cancellation needed in the manuscript.  The packet
polarization is kept abstract as an analytic factor `B`; later packet modules
can instantiate it directly.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Curvature of the analytic Hardy gauge as a function on the contour region. -/
def hardyCurvature (q : ℂ → ℂ) (s : ℂ) : ℂ :=
  curvatureJet (hardyGauge q s) (deriv (hardyGauge q) s)
    (deriv (deriv (hardyGauge q)) s)

/-- The Hardy gauge is analytic throughout the enlarged high rectangle. -/
theorem analyticOnNhd_hardyGauge_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε)) :
    AnalyticOnNhd ℂ (hardyGauge q) (highRectangleNhd T₁ T₂ ε) := by
  intro s hs
  have him := highRectangleNhd_im_ne_zero hεT s hs
  unfold hardyGauge
  exact (hqa s hs).mul (riemannZeta_analyticAt_of_im_ne_zero him)

/-- The Hardy curvature source is analytic on the enlarged high rectangle. -/
theorem analyticOnNhd_hardyCurvature_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε)) :
    AnalyticOnNhd ℂ (hardyCurvature q) (highRectangleNhd T₁ T₂ ε) := by
  intro s hs
  have hG := analyticOnNhd_hardyGauge_highRectangle hεT hqa s hs
  unfold hardyCurvature curvatureJet
  exact (hG.mul hG.deriv.deriv).sub (hG.deriv.pow 2)

/-- Holomorphic correction separating `𝒵''/𝒵'` from `Z₁'/Z₁`. -/
def sameFormHolomorphicCorrection (q B : ℂ → ℂ) (s : ℂ) : ℂ :=
  hardyF s * hardyCurvature q s * B s

/-- If the packet factor is analytic, then the correction term is analytic on
the whole high rectangle. -/
theorem analyticOnNhd_sameFormHolomorphicCorrection
    {T₁ T₂ ε : ℝ} {q B : ℂ → ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hB : AnalyticOnNhd ℂ B (highRectangleNhd T₁ T₂ ε)) :
    AnalyticOnNhd ℂ (sameFormHolomorphicCorrection q B)
      (highRectangleNhd T₁ T₂ ε) := by
  intro s hs
  have him := highRectangleNhd_im_ne_zero hεT s hs
  unfold sameFormHolomorphicCorrection
  exact ((analyticAt_hardyF_of_im_ne_zero him).mul
    (analyticOnNhd_hardyCurvature_highRectangle hεT hqa s hs)).mul (hB s hs)

/-- The holomorphic correction has zero boundary integral on the manuscript
rectangle. -/
theorem sameFormHolomorphicCorrection_boundaryIntegral_eq_zero
    {T₁ T₂ ε : ℝ} {q B : ℂ → ℂ}
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hB : AnalyticOnNhd ℂ B (highRectangleNhd T₁ T₂ ε)) :
    rectangleBoundaryIntegral (sameFormHolomorphicCorrection q B)
      (highRectangleSW T₁) (highRectangleNE T₂) = 0 :=
  rectangleBoundaryIntegral_eq_zero_on_highRectangle hε hT
    (analyticOnNhd_sameFormHolomorphicCorrection hεT hqa hB)

/-- Away from zeros of `Z₁`, the two same-form logarithmic-derivative
integrands differ exactly by the holomorphic correction. -/
theorem sameForm_integrand_decomposition
    {T₁ T₂ ε : ℝ} {q B : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s ≠ 0) :
    (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
        hardyCurvature q s * B s =
      sameFormHolomorphicCorrection q B s +
        (deriv zetaOne s / zetaOne s) * hardyCurvature q s * B s := by
  rw [hardyGauge_second_over_first_eq hεT hqa hqpow hs hz1]
  unfold sameFormHolomorphicCorrection
  ring

end HardyGaugeInvariantContourForm
end ZetaZero
