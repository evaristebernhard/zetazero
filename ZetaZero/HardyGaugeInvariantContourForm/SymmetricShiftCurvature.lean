import ZetaZero.HardyGaugeInvariantContourForm.ZetaCurvature
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Symmetric-shift generation of the curvature source

This module formalizes the elementary but structurally important identity used
before any contour movement in the manuscript:

`1/2 ∂ₐ² [F(s+a) F(s-a)]|ₐ=0 = F(s) F''(s) - F'(s)^2`.

It is stated for an arbitrary analytic complex function, so the Hardy-gauge
specialization is immediate once analyticity on the high rectangle is known.
-/

open Complex

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Symmetric shifted product whose second shift derivative generates the
curvature jet. -/
def symmetricShiftProduct (F : ℂ → ℂ) (s a : ℂ) : ℂ :=
  F (s + a) * F (s - a)

/-- The second derivative in the symmetric shift variable is twice the
curvature jet. -/
theorem half_iteratedDeriv_two_symmetricShiftProduct_eq_curvature
    {F : ℂ → ℂ} {s : ℂ} (hF : AnalyticAt ℂ F s) :
    (1 / 2 : ℂ) * iteratedDeriv 2 (symmetricShiftProduct F s) 0 =
      curvatureJet (F s) (deriv F s) (deriv (deriv F) s) := by
  have hplusA : AnalyticAt ℂ (fun a : ℂ => F (s + a)) 0 := by
    simpa [Function.comp_def] using
      hF.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun a : ℂ => s + a) 0) (by simp)
  have hminusA : AnalyticAt ℂ (fun a : ℂ => F (s - a)) 0 := by
    simpa [Function.comp_def] using
      hF.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun a : ℂ => s - a) 0) (by simp)
  have hmul := iteratedDeriv_mul (n := 2) (x := (0 : ℂ))
    hplusA.contDiffAt hminusA.contDiffAt
  change iteratedDeriv 2 (symmetricShiftProduct F s) 0 = _ at hmul
  rw [hmul]
  norm_num [Finset.sum_range_succ, iteratedDeriv_comp_const_add,
    iteratedDeriv_comp_const_sub, iteratedDeriv_succ, curvatureJet]
  ring

/-- Equivalent formulation using two ordinary derivatives. -/
theorem half_deriv2_symmetricShiftProduct_eq_curvature
    {F : ℂ → ℂ} {s : ℂ} (hF : AnalyticAt ℂ F s) :
    (1 / 2 : ℂ) * deriv (deriv (symmetricShiftProduct F s)) 0 =
      curvatureJet (F s) (deriv F s) (deriv (deriv F) s) := by
  simpa [iteratedDeriv_succ] using
    half_iteratedDeriv_two_symmetricShiftProduct_eq_curvature hF

/-- Manuscript specialization: the holomorphic Hardy gauge on the high
rectangle satisfies the exact symmetric-shift curvature identity. -/
theorem hardyGauge_half_deriv2_symmetricShift_eq_curvature
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    (1 / 2 : ℂ) * deriv (deriv (symmetricShiftProduct (hardyGauge q) s)) 0 =
      curvatureJet (hardyGauge q s) (deriv (hardyGauge q) s)
        (deriv (deriv (hardyGauge q)) s) := by
  have him := highRectangleNhd_im_ne_zero hεT s hs
  have hzeta : AnalyticAt ℂ riemannZeta s := riemannZeta_analyticAt_of_im_ne_zero him
  have hhardy : AnalyticAt ℂ (hardyGauge q) s := by
    unfold hardyGauge
    exact (hqa s hs).mul hzeta
  exact half_deriv2_symmetricShiftProduct_eq_curvature hhardy

end HardyGaugeInvariantContourForm
end ZetaZero
