import ZetaZero.HardyGaugeInvariantContourForm.PacketPolarization
import ZetaZero.HardyGaugeInvariantContourForm.SameFormContour

/-!
# Packet-polarized same-form bridge

This module instantiates the abstract analytic factor in `SameFormContour` with
the finite entire packet polarization used by the manuscript.  It closes the
analytic glue between the packet family and the Cauchy cancellation step without
yet invoking any meromorphic residue theorem.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- The holomorphic correction in the same-form identity has zero boundary
integral after inserting the manuscript packet polarization. -/
theorem packetSameFormCorrection_boundaryIntegral_eq_zero
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hψ : ∀ ν, Differentiable ℂ (ψ ν)) :
    rectangleBoundaryIntegral
        (sameFormHolomorphicCorrection q (packetPolarization ψ v w))
        (highRectangleSW T₁) (highRectangleNE T₂) = 0 := by
  exact sameFormHolomorphicCorrection_boundaryIntegral_eq_zero
    hε hT hεT hqa
    (analyticOnNhd_packetPolarization hψ v w (highRectangleNhd T₁ T₂ ε))

/-- Pointwise same-form decomposition with the actual packet polarization.
Away from zeros of `Z₁`, the Hardy logarithmic-derivative integrand is the
`Z₁'/Z₁` integrand plus the holomorphic correction killed by Cauchy--Goursat. -/
theorem packetSameForm_integrand_decomposition
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s ≠ 0) :
    (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
          hardyCurvature q s * packetPolarization ψ v w s =
      sameFormHolomorphicCorrection q (packetPolarization ψ v w) s +
        (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
          packetPolarization ψ v w s := by
  exact sameForm_integrand_decomposition hεT hqa hqpow hs hz1

/-- Full packet-polarized same-form contour equality.  Once `Z₁` has no zero
on the four contour edges and the meromorphic `Z₁'/Z₁` integrand is integrable
there, the Hardy logarithmic-derivative form and the `Z₁'/Z₁` form have exactly
the same rectangle boundary integral. -/
theorem packetSameForm_boundaryIntegral_eq
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hz1 : NonzeroOnRectangleBoundary zetaOne
      (highRectangleSW T₁) (highRectangleNE T₂))
    (hzint : RectangleBoundaryIntervalIntegrable
      (fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
        packetPolarization ψ v w s)
      (highRectangleSW T₁) (highRectangleNE T₂)) :
    rectangleBoundaryIntegral
        (fun s => (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
          hardyCurvature q s * packetPolarization ψ v w s)
        (highRectangleSW T₁) (highRectangleNE T₂) =
      rectangleBoundaryIntegral
        (fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
          packetPolarization ψ v w s)
        (highRectangleSW T₁) (highRectangleNE T₂) := by
  let z := highRectangleSW T₁
  let w₀ := highRectangleNE T₂
  let correction := sameFormHolomorphicCorrection q (packetPolarization ψ v w)
  let rhs := fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
    packetPolarization ψ v w s
  let lhs := fun s =>
    (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
      hardyCurvature q s * packetPolarization ψ v w s
  have hsub : (uIcc z.re w₀.re ×ℂ uIcc z.im w₀.im) ⊆
      highRectangleNhd T₁ T₂ ε := by
    simpa [z, w₀] using mathlibRectangle_subset_highRectangleNhd hε hT
  rcases hz1 with ⟨hzSouth, hzNorth, hzEast, hzWest⟩
  have hEq : EqOnRectangleBoundary lhs (fun s => correction s + rhs s) z w₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      have hs : (x : ℂ) + z.im * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
        rw [mem_reProdIm]
        simpa using And.intro hx (left_mem_uIcc : z.im ∈ uIcc z.im w₀.im))
      simpa [lhs, correction, rhs, z, w₀] using
        packetSameForm_integrand_decomposition
          (v := v) (w := w) hεT hqa hqpow hs (hzSouth x (by simpa [z, w₀] using hx))
    · intro x hx
      have hs : (x : ℂ) + w₀.im * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
        rw [mem_reProdIm]
        simpa using And.intro hx (right_mem_uIcc : w₀.im ∈ uIcc z.im w₀.im))
      simpa [lhs, correction, rhs, z, w₀] using
        packetSameForm_integrand_decomposition
          (v := v) (w := w) hεT hqa hqpow hs (hzNorth x (by simpa [z, w₀] using hx))
    · intro y hy
      have hs : w₀.re + (y : ℂ) * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
        rw [mem_reProdIm]
        simpa using And.intro (right_mem_uIcc : w₀.re ∈ uIcc z.re w₀.re) hy)
      simpa [lhs, correction, rhs, z, w₀] using
        packetSameForm_integrand_decomposition
          (v := v) (w := w) hεT hqa hqpow hs (hzEast y (by simpa [z, w₀] using hy))
    · intro y hy
      have hs : z.re + (y : ℂ) * I ∈ highRectangleNhd T₁ T₂ ε := hsub (by
        rw [mem_reProdIm]
        simpa using And.intro (left_mem_uIcc : z.re ∈ uIcc z.re w₀.re) hy)
      simpa [lhs, correction, rhs, z, w₀] using
        packetSameForm_integrand_decomposition
          (v := v) (w := w) hεT hqa hqpow hs (hzWest y (by simpa [z, w₀] using hy))
  have hCorrAnalytic : AnalyticOnNhd ℂ correction (highRectangleNhd T₁ T₂ ε) := by
    simpa [correction] using analyticOnNhd_sameFormHolomorphicCorrection hεT hqa
      (analyticOnNhd_packetPolarization hψ v w (highRectangleNhd T₁ T₂ ε))
  have hCorrInt : RectangleBoundaryIntervalIntegrable correction z w₀ :=
    rectangleBoundaryIntervalIntegrable_of_analyticOnNhd hCorrAnalytic hsub
  have hCorrZero : rectangleBoundaryIntegral correction z w₀ = 0 := by
    simpa [correction, z, w₀] using
      packetSameFormCorrection_boundaryIntegral_eq_zero
        (v := v) (w := w) hε hT hεT hqa hψ
  have hRhsInt : RectangleBoundaryIntervalIntegrable rhs z w₀ := by
    simpa [rhs, z, w₀] using hzint
  have hMain := rectangleBoundaryIntegral_eq_of_eq_add_zero
    hEq hCorrInt hRhsInt hCorrZero
  simpa [lhs, rhs, z, w₀] using hMain

end HardyGaugeInvariantContourForm
end ZetaZero
