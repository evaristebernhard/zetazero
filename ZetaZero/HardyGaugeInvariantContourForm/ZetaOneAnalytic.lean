import ZetaZero.HardyGaugeInvariantContourForm.GaugeDerivative

/-!
# Analyticity of the `Z₁` detector

The local Jensen and logarithmic-derivative arguments on the zero side require
`Z₁ = ζ' + f ζ` to be genuinely analytic on the high, non-real region.  This
module isolates that qualitative analytic fact from the later quantitative
growth estimates.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- The Hardy logarithmic-derivative coefficient is analytic away from the real
axis. -/
theorem analyticAt_hardyF_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ hardyF s := by
  have hchi := Analytic.analyticAt_chiOneSub_of_im_ne_zero hs
  have hchi0 := Analytic.chiOneSub_ne_zero_of_im_ne_zero hs
  unfold hardyF logDeriv
  exact analyticAt_const.mul (hchi.deriv.div hchi hchi0)

/-- `Z₁` is analytic away from the real axis. -/
theorem analyticAt_zetaOne_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ zetaOne s := by
  have hzeta := Analytic.analyticAt_riemannZeta (Analytic.ne_one_of_im_ne_zero hs)
  unfold zetaOne
  exact hzeta.deriv.add ((analyticAt_hardyF_of_im_ne_zero hs).mul hzeta)

/-- `Z₁` is analytic on every set disjoint from the real axis. -/
theorem analyticOnNhd_zetaOne_of_im_ne_zero {U : Set ℂ}
    (hU : ∀ s ∈ U, s.im ≠ 0) : AnalyticOnNhd ℂ zetaOne U := by
  intro s hs
  exact analyticAt_zetaOne_of_im_ne_zero (hU s hs)

/-- In particular, `Z₁` is analytic on the enlarged high contour rectangle. -/
theorem analyticOnNhd_zetaOne_highRectangle
    {T₁ T₂ ε : ℝ} (hεT : ε < T₁) :
    AnalyticOnNhd ℂ zetaOne (highRectangleNhd T₁ T₂ ε) :=
  analyticOnNhd_zetaOne_of_im_ne_zero (highRectangleNhd_im_ne_zero hεT)

end HardyGaugeInvariantContourForm
end ZetaZero
