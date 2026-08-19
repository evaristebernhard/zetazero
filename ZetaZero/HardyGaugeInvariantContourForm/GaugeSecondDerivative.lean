import ZetaZero.HardyGaugeInvariantContourForm.ZetaOneAnalytic
import Mathlib.Tactic.Ring

/-!
# Second derivative of the Hardy gauge branch

The first derivative module proves `q' = f q` on the open high rectangle.  This
file differentiates that identity once more.  The only local hypothesis exposed
here is differentiability of `hardyF`; analyticity of that logarithmic derivative
will be discharged separately from the nonvanishing of `chiOneSub`.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Differentiating `q' = f q` on the open high rectangle gives
`q'' = (f' + f²) q` at every point where `f` is differentiable. -/
theorem deriv2_branch_eq_hardyF
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hf : DifferentiableAt ℂ hardyF s) :
    deriv (deriv q) s = (deriv hardyF s + hardyF s ^ 2) * q s := by
  have hqdiff : DifferentiableAt ℂ q s := (hqa s hs).differentiableAt
  have hrect : highRectangleNhd T₁ T₂ ε ∈ 𝓝 s :=
    (isOpen_highRectangleNhd T₁ T₂ ε).mem_nhds hs
  have hev : deriv q =ᶠ[𝓝 s] hardyF * q := by
    filter_upwards [hrect] with z hz
    exact deriv_branch_eq_hardyF_mul hεT hqa hqpow z hz
  have hderivEq : deriv (deriv q) s = deriv (hardyF * q) s := hev.deriv_eq
  rw [deriv_mul hf hqdiff,
    deriv_branch_eq_hardyF_mul hεT hqa hqpow s hs] at hderivEq
  calc
    deriv (deriv q) s =
        deriv hardyF s * q s + hardyF s * (hardyF s * q s) := hderivEq
    _ = (deriv hardyF s + hardyF s ^ 2) * q s := by ring

/-- On the high rectangle the second branch derivative identity needs no
additional regularity hypothesis, since the rectangle stays off the real axis. -/
theorem deriv2_branch_eq_hardyF_on_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    deriv (deriv q) s = (deriv hardyF s + hardyF s ^ 2) * q s := by
  have him := highRectangleNhd_im_ne_zero hεT s hs
  exact deriv2_branch_eq_hardyF hεT hqa hqpow hs
    (analyticAt_hardyF_of_im_ne_zero him).differentiableAt

end HardyGaugeInvariantContourForm
end ZetaZero
