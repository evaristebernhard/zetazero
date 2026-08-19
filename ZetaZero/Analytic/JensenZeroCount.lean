import Mathlib.Analysis.Complex.JensenFormula

/-!
# Jensen zero-counting interface

Mathlib 4.32 already contains Jensen's formula and a quantitative Jensen
inequality.  This module exposes the positive-radius form used by the paper, so
we do not need to vendor the older Blaschke `ZerosBound` implementation from the
local `zeta-23-lean` reference project.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace Analytic

/-- Jensen's inequality in the positive-radius form used for fixed local discs.
For an analytic function this divisor sum is the total zero multiplicity in the
inner closed ball. -/
theorem jensen_divisor_bound
    {c : ℂ} {r R M : ℝ} {F : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hFc : F c ≠ 0)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖F z‖ ≤ M) :
    ∑ᶠ z, MeromorphicOn.divisor F (Metric.closedBall c |r|) z ≤
      Real.log (M / ‖F c‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hrabs : 0 < |r| := by simpa [abs_of_pos hr] using hr
  have hrRabs : |r| < |R| := by simpa [abs_of_pos hr, abs_of_pos hR] using hrR
  have hFabs : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hR] using hF
  simpa [abs_of_pos hr, abs_of_pos hR] using
    (hFabs.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
      hrabs hrRabs hM hFc (by simpa [abs_of_pos hR] using hbound))

/-- If the boundary norm is bounded by `M` and the centre value is bounded below
by `m > 0`, Jensen gives the coarser but convenient bound `log(M/m)/log(R/r)`. -/
theorem jensen_divisor_bound_of_center_lower
    {c : ℂ} {r R M m : ℝ} {F : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hm : 0 < m)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hcenter : m ≤ ‖F c‖)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖F z‖ ≤ M) :
    ∑ᶠ z, MeromorphicOn.divisor F (Metric.closedBall c |r|) z ≤
      Real.log (M / m) / Real.log (R / r) := by
  have hnorm : 0 < ‖F c‖ := lt_of_lt_of_le hm hcenter
  have hFc : F c ≠ 0 := norm_ne_zero_iff.mp hnorm.ne'
  refine (jensen_divisor_bound hr hrR hM hF hFc hbound).trans ?_
  have hden : 0 < Real.log (R / r) := by
    exact Real.log_pos (by simpa [one_lt_div hr] using hrR)
  apply div_le_div_of_nonneg_right _ hden.le
  apply Real.log_le_log
  · exact div_pos (lt_of_lt_of_le one_pos hM) hnorm
  · exact div_le_div_of_nonneg_left (by positivity) hm hcenter

/-- Fixed-radius local zero count from polynomial growth.  Once the centre value
is at least one and the boundary grows like `U^A`, the total zero multiplicity
in the inner disk is at most a constant multiple of `log U`, with the exact
constant `A / log(R/r)`.  This is the abstract form needed for the manuscript's
local Jensen count for `zeta` and `Z1`. -/
theorem jensen_divisor_bound_of_polynomial_growth
    {c : ℂ} {r R U : ℝ} {A : ℕ} {F : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hU : 1 ≤ U)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hcenter : 1 ≤ ‖F c‖)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖F z‖ ≤ U ^ A) :
    ∑ᶠ z, MeromorphicOn.divisor F (Metric.closedBall c |r|) z ≤
      (A : ℝ) * Real.log U / Real.log (R / r) := by
  have hM : (1 : ℝ) ≤ U ^ A := one_le_pow₀ hU
  have h := jensen_divisor_bound_of_center_lower
    hr hrR hM one_pos hF hcenter hbound
  simpa [div_one, Real.log_pow] using h

end Analytic
end ZetaZero
