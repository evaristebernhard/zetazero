import ZetaZero.HardyGaugeInvariantContourForm.PacketSameForm

/-!
# Automatic boundary integrability for the packet `Z₁'/Z₁` source

On a contour avoiding the zeros of `Z₁`, every factor in the packet-polarized
`Z₁'/Z₁` integrand is analytic at each boundary point.  This module turns that
local fact into the four interval-integrability hypotheses required by the
rectangle boundary API, removing the last auxiliary assumption from
`packetSameForm_boundaryIntegral_eq`.
-/

open Complex Set intervalIntegral MeasureTheory

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- The packet-polarized `Z₁'/Z₁` integrand is analytic at every high-rectangle
point which is not a zero of `Z₁`. -/
theorem analyticAt_zetaOne_packetIntegrand
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s ≠ 0) :
    AnalyticAt ℂ
      (fun z => (deriv zetaOne z / zetaOne z) * hardyCurvature q z *
        packetPolarization ψ v w z) s := by
  have him := highRectangleNhd_im_ne_zero hεT s hs
  have hzetaOne : AnalyticAt ℂ zetaOne s := analyticAt_zetaOne_of_im_ne_zero him
  have hlog : AnalyticAt ℂ (fun z => deriv zetaOne z / zetaOne z) s :=
    hzetaOne.deriv.div hzetaOne hz1
  have hcurv : AnalyticAt ℂ (hardyCurvature q) s :=
    analyticOnNhd_hardyCurvature_highRectangle hεT hqa s hs
  have hpacket : AnalyticAt ℂ (packetPolarization ψ v w) s :=
    (differentiable_packetPolarization hψ v w).analyticAt s
  exact (hlog.mul hcurv).mul hpacket

/-- Zero-free boundary data automatically imply interval-integrability of the
packet-polarized `Z₁'/Z₁` source on all four edges. -/
theorem zetaOne_packetIntegrand_boundaryIntervalIntegrable
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hz1 : NonzeroOnRectangleBoundary zetaOne
      (highRectangleSW T₁) (highRectangleNE T₂)) :
    RectangleBoundaryIntervalIntegrable
      (fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
        packetPolarization ψ v w s)
      (highRectangleSW T₁) (highRectangleNE T₂) := by
  let z := highRectangleSW T₁
  let w₀ := highRectangleNE T₂
  have hsub : (uIcc z.re w₀.re ×ℂ uIcc z.im w₀.im) ⊆
      highRectangleNhd T₁ T₂ ε := by
    simpa [z, w₀] using mathlibRectangle_subset_highRectangleNhd hε hT
  rcases hz1 with ⟨hzSouth, hzNorth, hzEast, hzWest⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ uIcc z.re w₀.re := by simpa [z, w₀] using hx
    have hs : (x : ℂ) + z.im * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
      rw [mem_reProdIm]
      constructor
      · simpa using hx'
      · simp)
    have ha := analyticAt_zetaOne_packetIntegrand (v := v) (w := w) hεT hqa hψ hs
      (hzSouth x (by simpa [z, w₀] using hx))
    simpa [z, w₀, Function.comp_def] using
      (ContinuousAt.comp'
        (f := fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I)
        ha.continuousAt (by fun_prop)).continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ uIcc z.re w₀.re := by simpa [z, w₀] using hx
    have hs : (x : ℂ) + w₀.im * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
      rw [mem_reProdIm]
      constructor
      · simpa using hx'
      · simp)
    have ha := analyticAt_zetaOne_packetIntegrand (v := v) (w := w) hεT hqa hψ hs
      (hzNorth x (by simpa [z, w₀] using hx))
    simpa [z, w₀, Function.comp_def] using
      (ContinuousAt.comp'
        (f := fun x : ℝ => (x : ℂ) + (w₀.im : ℂ) * I)
        ha.continuousAt (by fun_prop)).continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    have hy' : y ∈ uIcc z.im w₀.im := by simpa [z, w₀] using hy
    have hs : w₀.re + (y : ℂ) * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
      rw [mem_reProdIm]
      constructor
      · simp
      · simpa using hy')
    have ha := analyticAt_zetaOne_packetIntegrand (v := v) (w := w) hεT hqa hψ hs
      (hzEast y (by simpa [z, w₀] using hy))
    simpa [z, w₀, Function.comp_def] using
      (ContinuousAt.comp'
        (f := fun y : ℝ => (w₀.re : ℂ) + (y : ℂ) * I)
        ha.continuousAt (by fun_prop)).continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    have hy' : y ∈ uIcc z.im w₀.im := by simpa [z, w₀] using hy
    have hs : z.re + (y : ℂ) * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
      rw [mem_reProdIm]
      constructor
      · simp
      · simpa using hy')
    have ha := analyticAt_zetaOne_packetIntegrand (v := v) (w := w) hεT hqa hψ hs
      (hzWest y (by simpa [z, w₀] using hy))
    simpa [z, w₀, Function.comp_def] using
      (ContinuousAt.comp'
        (f := fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I)
        ha.continuousAt (by fun_prop)).continuousWithinAt

/-- Paper-facing same-form contour equality with no separate integrability
hypothesis: zero avoidance of `Z₁` on the contour is enough. -/
theorem packetSameForm_boundaryIntegral_eq_of_nonzero
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hz1 : NonzeroOnRectangleBoundary zetaOne
      (highRectangleSW T₁) (highRectangleNE T₂)) :
    rectangleBoundaryIntegral
        (fun s => (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
          hardyCurvature q s * packetPolarization ψ v w s)
        (highRectangleSW T₁) (highRectangleNE T₂) =
      rectangleBoundaryIntegral
        (fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
          packetPolarization ψ v w s)
        (highRectangleSW T₁) (highRectangleNE T₂) := by
  exact packetSameForm_boundaryIntegral_eq hψ hε hT hεT hqa hqpow hz1
    (zetaOne_packetIntegrand_boundaryIntervalIntegrable hε hT hεT hqa hψ hz1)

end HardyGaugeInvariantContourForm
end ZetaZero
