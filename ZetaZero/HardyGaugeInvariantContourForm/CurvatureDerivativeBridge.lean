import ZetaZero.HardyGaugeInvariantContourForm.CurvatureAlgebra
import ZetaZero.HardyGaugeInvariantContourForm.GaugeDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Function-level bridge for the curvature jet

`CurvatureAlgebra` contains the pointwise two-jet identity.  This module connects
that algebra to actual complex derivatives of analytic functions by proving the
first and second product rules in the exact shape required by the curvature
factorization.
-/

open Complex Filter Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Second derivative of a product of analytic complex functions, written in the
jet form used by `curvatureJet_mul_factorization`. -/
theorem deriv2_mul_eq_mulSecondJet
    {q z : ℂ → ℂ} {s : ℂ}
    (hq : AnalyticAt ℂ q s) (hz : AnalyticAt ℂ z s) :
    deriv (deriv (q * z)) s =
      mulSecondJet (q s) (deriv q s) (deriv (deriv q) s)
        (z s) (deriv z s) (deriv (deriv z) s) := by
  have hqev : ∀ᶠ w in 𝓝 s, DifferentiableAt ℂ q w :=
    analyticAt_iff_eventually_differentiableAt.mp hq
  have hzev : ∀ᶠ w in 𝓝 s, DifferentiableAt ℂ z w :=
    analyticAt_iff_eventually_differentiableAt.mp hz
  have hev : deriv (q * z) =ᶠ[𝓝 s] deriv q * z + q * deriv z := by
    filter_upwards [hqev, hzev] with w hqw hzw
    exact deriv_mul hqw hzw
  have h2 : deriv (deriv (q * z)) s = deriv (deriv q * z + q * deriv z) s :=
    hev.deriv_eq
  have hq' : DifferentiableAt ℂ (deriv q) s := hq.deriv.differentiableAt
  have hz' : DifferentiableAt ℂ (deriv z) s := hz.deriv.differentiableAt
  rw [deriv_add (hq'.mul hz.differentiableAt) (hq.differentiableAt.mul hz'),
    deriv_mul hq' hz.differentiableAt,
    deriv_mul hq.differentiableAt hz'] at h2
  rw [h2]
  simp [mulSecondJet]
  ring

/-- Function-level Hardy-gauge curvature factorization.  Once the gauge first
and second derivatives have the forms `q' = f q` and `q'' = (f' + f²)q`, the
curvature of the analytic product `q z` is the manuscript source
`q² (z z'' - (z')² + f' z²)`. -/
theorem curvature_deriv_mul_factorization
    {q z : ℂ → ℂ} {s : ℂ} {f f₁ : ℂ}
    (hq : AnalyticAt ℂ q s) (hz : AnalyticAt ℂ z s)
    (hq₁ : deriv q s = f * q s)
    (hq₂ : deriv (deriv q) s = (f₁ + f ^ 2) * q s) :
    curvatureJet ((q * z) s)
      (deriv (q * z) s)
      (deriv (deriv (q * z)) s)
      = q s ^ 2 *
        (curvatureJet (z s) (deriv z s) (deriv (deriv z) s) + f₁ * z s ^ 2) := by
  have hfirst : deriv (q * z) s =
      mulFirstJet (q s) (deriv q s) (z s) (deriv z s) := by
    rw [deriv_mul hq.differentiableAt hz.differentiableAt]
    rfl
  have hsecond := deriv2_mul_eq_mulSecondJet hq hz
  rw [show (q * z) s = q s * z s by rfl, hfirst, hsecond]
  exact curvatureJet_mul_factorization
    (q s) (deriv q s) (deriv (deriv q) s)
    (z s) (deriv z s) (deriv (deriv z) s) f f₁ hq₁ hq₂

end HardyGaugeInvariantContourForm
end ZetaZero
