import ZetaZero.HardyGaugeInvariantContourForm.BranchReflection
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Derivative of the analytic Hardy gauge

The manuscript writes

`f(s) = - 1/2 χ'(s)/χ(s)`

and `Z₁ = ζ' + f ζ`.  Since our square-root branch satisfies
`q² = χ(1-s)`, the most direct formal definition is

`hardyF(s) = 1/2 logDeriv(chiOneSub)(s)`.

Differentiating `q² = chiOneSub` gives `q' = hardyF q`, and hence

`(q ζ)' = q (ζ' + hardyF ζ)`.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Logarithmic derivative coefficient attached to the Hardy gauge. -/
def hardyF (s : ℂ) : ℂ := (1 / 2 : ℂ) * logDeriv Analytic.chiOneSub s

/-- The `Z₁` detector appearing in the manuscript. -/
def zetaOne (s : ℂ) : ℂ :=
  deriv riemannZeta s + hardyF s * riemannZeta s

/-- Differentiating the square-root identity gives `q' = f q`. -/
theorem deriv_branch_eq_hardyF_mul
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z) :
    ∀ s ∈ highRectangleNhd T₁ T₂ ε,
      deriv q s = hardyF s * q s := by
  intro s hs
  have hqdiff : DifferentiableAt ℂ q s := (hqa s hs).differentiableAt
  have hev : q ^ 2 =ᶠ[𝓝 s] Analytic.chiOneSub := by
    filter_upwards with z
    exact hqpow z
  have hderivEq : deriv (q ^ 2) s = deriv Analytic.chiOneSub s := hev.deriv_eq
  rw [(hqdiff.hasDerivAt.pow 2).deriv] at hderivEq
  have hqne := branch_ne_zero_on_highRectangle hqpow hεT s hs
  rw [hardyF, logDeriv_apply, ← hqpow s]
  field_simp [hqne]
  linear_combination hderivEq

/-- Exact derivative identity `𝒵' = q Z₁` on the high rectangle. -/
theorem deriv_hardyGauge_eq_branch_mul_zetaOne
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z) :
    ∀ s ∈ highRectangleNhd T₁ T₂ ε,
      deriv (hardyGauge q) s = q s * zetaOne s := by
  intro s hs
  have hqdiff : DifferentiableAt ℂ q s := (hqa s hs).differentiableAt
  have him := highRectangleNhd_im_ne_zero hεT s hs
  have hzetaDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (Analytic.ne_one_of_im_ne_zero him)
  change deriv (q * riemannZeta) s = q s * zetaOne s
  rw [deriv_mul hqdiff hzetaDiff,
    deriv_branch_eq_hardyF_mul hεT hqa hqpow s hs, zetaOne]
  ring

/-- The branch is analytic and nonzero, so the Hardy gauge and zeta have the
same zeros on the high rectangle. -/
theorem hardyGauge_eq_zero_iff_zeta_eq_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hεT : ε < T₁)
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    {s : ℂ} (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    hardyGauge q s = 0 ↔ riemannZeta s = 0 := by
  change q s * riemannZeta s = 0 ↔ riemannZeta s = 0
  rw [mul_eq_zero]
  exact or_iff_right (branch_ne_zero_on_highRectangle hqpow hεT s hs)

end HardyGaugeInvariantContourForm
end ZetaZero
