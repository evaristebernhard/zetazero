import ZetaZero.HardyGaugeInvariantContourForm.CurvatureDerivativeBridge
import ZetaZero.HardyGaugeInvariantContourForm.GaugeSecondDerivative

/-!
# Curvature source for the analytic Hardy gauge

This file specializes the function-level curvature bridge to the Riemann zeta
function and the holomorphic square-root branch on the high rectangle.  It is
the direct analytic interface for the manuscript identity

`C_𝒵 = q² (ζ ζ'' - (ζ')² + f' ζ²)`.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Zeta is analytic at every point whose imaginary part is nonzero. -/
theorem riemannZeta_analyticAt_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) :
    AnalyticAt ℂ riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro h
    apply him
    rw [h]
    simp
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_compl_singleton.mem_nhds
    (by simpa using hs1 : s ∈ ({1}ᶜ : Set ℂ))] with z hz
  exact differentiableAt_riemannZeta (by simpa using hz)

/-- Exact curvature-source identity for the analytic Hardy gauge on the high
rectangle.  The exposed hypothesis `DifferentiableAt ℂ hardyF s` is the final
local regularity input needed before the logarithmic-derivative layer is closed. -/
theorem hardyGauge_curvature_source
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hf : DifferentiableAt ℂ hardyF s) :
    curvatureJet (hardyGauge q s)
      (deriv (hardyGauge q) s)
      (deriv (deriv (hardyGauge q)) s)
      = q s ^ 2 *
        (curvatureJet (riemannZeta s) (deriv riemannZeta s)
          (deriv (deriv riemannZeta) s) +
          deriv hardyF s * riemannZeta s ^ 2) := by
  have him := highRectangleNhd_im_ne_zero hεT s hs
  have hzeta : AnalyticAt ℂ riemannZeta s := riemannZeta_analyticAt_of_im_ne_zero him
  have hq₁ := deriv_branch_eq_hardyF_mul hεT hqa hqpow s hs
  have hq₂ := deriv2_branch_eq_hardyF hεT hqa hqpow hs hf
  have hcurv := curvature_deriv_mul_factorization
    (hqa s hs) hzeta hq₁ hq₂
  change curvatureJet ((q * riemannZeta) s)
      (deriv (q * riemannZeta) s)
      (deriv (deriv (q * riemannZeta)) s)
      = q s ^ 2 *
        (curvatureJet (riemannZeta s) (deriv riemannZeta s)
          (deriv (deriv riemannZeta) s) +
          deriv hardyF s * riemannZeta s ^ 2)
  exact hcurv

/-- Exact curvature-source identity on the high rectangle, with no additional
regularity hypothesis: analyticity and nonvanishing of `chiOneSub` imply the
required differentiability of `hardyF` automatically. -/
theorem hardyGauge_curvature_source_on_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    curvatureJet (hardyGauge q s)
      (deriv (hardyGauge q) s)
      (deriv (deriv (hardyGauge q)) s)
      = q s ^ 2 *
        (curvatureJet (riemannZeta s) (deriv riemannZeta s)
          (deriv (deriv riemannZeta) s) +
          deriv hardyF s * riemannZeta s ^ 2) := by
  have him := highRectangleNhd_im_ne_zero hεT s hs
  exact hardyGauge_curvature_source hεT hqa hqpow hs
    (analyticAt_hardyF_of_im_ne_zero him).differentiableAt

end HardyGaugeInvariantContourForm
end ZetaZero
