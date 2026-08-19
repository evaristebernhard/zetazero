import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Algebra of the Hardy-gauge curvature jet

The analytic M02 branch is responsible for proving the derivative identities
for the actual gauge and zeta functions.  This file isolates the pointwise
algebra that follows from those identities.  It is intentionally independent of
the high-rectangle construction, so it can be developed and checked in parallel.
-/

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Curvature of a two-jet `(value, first derivative, second derivative)`. -/
def curvatureJet (x x₁ x₂ : ℂ) : ℂ := x * x₂ - x₁ ^ 2

/-- The second symmetric-shift jet is twice the curvature jet.  Analytically,
this is the algebra behind
`(1/2) ∂ₐ²(F(s+a) F(s-a))|ₐ=0 = F F'' - (F')²`. -/
def symmetricShiftSecondJet (x x₁ x₂ : ℂ) : ℂ :=
  2 * x * x₂ - 2 * x₁ ^ 2

@[simp] theorem half_symmetricShiftSecondJet (x x₁ x₂ : ℂ) :
    (1 / 2 : ℂ) * symmetricShiftSecondJet x x₁ x₂ = curvatureJet x x₁ x₂ := by
  simp [symmetricShiftSecondJet, curvatureJet]
  ring

/-- Product rule at the level of two-jets. -/
def mulFirstJet (q q₁ z z₁ : ℂ) : ℂ := q₁ * z + q * z₁

/-- Second product rule at the level of two-jets. -/
def mulSecondJet (q q₁ q₂ z z₁ z₂ : ℂ) : ℂ :=
  q₂ * z + 2 * q₁ * z₁ + q * z₂

/-- Algebraic Hardy-gauge curvature factorization.

If the gauge jet satisfies
`q' = f q` and `q'' = (f' + f²) q`, then the curvature of `q z` factors as

`q² (z z'' - (z')² + f' z²)`.

This is exactly the algebraic content of the manuscript's curvature-source
identity; no analytic assumptions are needed in this lemma. -/
theorem curvatureJet_mul_factorization
    (q q₁ q₂ z z₁ z₂ f f₁ : ℂ)
    (hq₁ : q₁ = f * q)
    (hq₂ : q₂ = (f₁ + f ^ 2) * q) :
    curvatureJet (q * z)
      (mulFirstJet q q₁ z z₁)
      (mulSecondJet q q₁ q₂ z z₁ z₂)
      = q ^ 2 * (curvatureJet z z₁ z₂ + f₁ * z ^ 2) := by
  rw [hq₁, hq₂]
  simp [curvatureJet, mulFirstJet, mulSecondJet]
  ring

/-- Expanded form matching the source formula used on the right edge. -/
theorem curvatureJet_mul_factorization_expanded
    (q q₁ q₂ z z₁ z₂ f f₁ : ℂ)
    (hq₁ : q₁ = f * q)
    (hq₂ : q₂ = (f₁ + f ^ 2) * q) :
    curvatureJet (q * z)
      (mulFirstJet q q₁ z z₁)
      (mulSecondJet q q₁ q₂ z z₁ z₂)
      = q ^ 2 * (z * z₂ - z₁ ^ 2 + f₁ * z ^ 2) := by
  rw [curvatureJet_mul_factorization q q₁ q₂ z z₁ z₂ f f₁ hq₁ hq₂]
  rfl

end HardyGaugeInvariantContourForm
end ZetaZero
