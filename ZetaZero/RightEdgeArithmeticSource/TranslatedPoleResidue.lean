import ZetaZero.HardyGaugeInvariantContourForm.SimpleZeroLogResidue
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Exact translated-pole residue coefficient

For the frozen right-edge denominator

`D(z) = F - P(z)`

one has `D' = -P'`.  In the manuscript convention `Q = -P'`, so `Q/D` is
exactly the logarithmic derivative `D'/D`.  Consequently every simple zero of
`D` contributes simple-pole coefficient `+1`.

This file formalizes that exact local analytic statement.  It deliberately does
not assert the Rouché theorem locating the zero near `F⁻¹`; that is a separate
analytic milestone.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Frozen Perron denominator `F - P(z)`. -/
def translatedDenominator (F : ℂ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  F - P z

@[simp] theorem translatedDenominator_eq_zero_iff
    (F : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    translatedDenominator F P z = 0 ↔ P z = F := by
  simp [translatedDenominator, sub_eq_zero, eq_comm]

/-- Differentiating the frozen denominator introduces exactly one minus sign. -/
@[simp] theorem deriv_translatedDenominator
    (F : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    deriv (translatedDenominator F P) z = -deriv P z := by
  unfold translatedDenominator
  exact deriv_const_sub F

/-- Simplicity of a zero of `F-P` is equivalent to nonvanishing of `P'`. -/
theorem deriv_translatedDenominator_ne_zero_iff
    (F : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    deriv (translatedDenominator F P) z ≠ 0 ↔ deriv P z ≠ 0 := by
  simp

/-- At a simple zero of `F-P`, its logarithmic derivative has simple-pole
coefficient exactly `1`.  This is the local residue statement behind the
translated model scale. -/
theorem translatedLogDerivative_simpleZero_coefficient
    {F : ℂ} {P : ℂ → ℂ} {x : ℂ}
    (hP : AnalyticAt ℂ P x)
    (hzero : translatedDenominator F P x = 0)
    (hP' : deriv P x ≠ 0) :
    Tendsto
      (fun w => (w - x) *
        ((-deriv P w) / translatedDenominator F P w))
      (nhdsWithin x ({x}ᶜ : Set ℂ))
      (nhds 1) := by
  have hD : AnalyticAt ℂ (translatedDenominator F P) x := by
    change AnalyticAt ℂ (fun z : ℂ => F - P z) x
    exact analyticAt_const.sub hP
  have hD' : deriv (translatedDenominator F P) x ≠ 0 := by
    simpa using hP'
  have h :=
    HardyGaugeInvariantContourForm.tendsto_mul_deriv_div_mul_simple_zero
      (f := translatedDenominator F P)
      (A := fun _ : ℂ => (1 : ℂ))
      (x := x)
      hD hzero hD' continuousAt_const
  simpa using h

/-- General numerator form: whenever `Q=-P'` pointwise, `Q/(F-P)` has residue
coefficient `+1` at every simple zero of the denominator. -/
theorem translatedQuotient_simpleZero_coefficient
    {F : ℂ} {P Q : ℂ → ℂ} {x : ℂ}
    (hP : AnalyticAt ℂ P x)
    (hQ : ∀ z, Q z = -deriv P z)
    (hzero : translatedDenominator F P x = 0)
    (hP' : deriv P x ≠ 0) :
    Tendsto
      (fun w => (w - x) * (Q w / translatedDenominator F P w))
      (nhdsWithin x ({x}ᶜ : Set ℂ))
      (nhds 1) := by
  simpa [hQ] using
    translatedLogDerivative_simpleZero_coefficient hP hzero hP'

end RightEdgeArithmeticSource
end ZetaZero
