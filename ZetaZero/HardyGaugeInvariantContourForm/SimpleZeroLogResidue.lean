import ZetaZero.HardyGaugeInvariantContourForm.PacketBoundaryIntegrability
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Simple-zero logarithmic residue

The meromorphic step in the same-form contour argument only needs the local
simple-pole coefficient of a logarithmic derivative. Mathlib already proves
that `(w - x) * logDeriv f w → 1` at a simple zero `x` of an analytic `f`.
This module propagates that coefficient through an analytic amplitude and then
specializes it to the packet-polarized `Z₁'/Z₁` source.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Multiplying a logarithmic derivative by a continuous amplitude changes the
simple-pole coefficient from `1` to the value of the amplitude at the zero. -/
theorem tendsto_mul_logDeriv_mul_simple_zero
    {f A : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0)
    (hA : ContinuousAt A x) :
    Tendsto (fun w => (w - x) * (logDeriv f w * A w))
      (nhdsWithin x ({x}ᶜ : Set ℂ)) (nhds (A x)) := by
  have hlog := hf.tendsto_mul_logDeriv_simple_zero hfx hf'
  have hAmp : Tendsto A (nhdsWithin x ({x}ᶜ : Set ℂ)) (nhds (A x)) :=
    hA.tendsto.mono_left nhdsWithin_le_nhds
  simpa [mul_assoc] using hlog.mul hAmp

/-- The same coefficient statement written with the explicit quotient
`f'/f`, matching the manuscript integrand. -/
theorem tendsto_mul_deriv_div_mul_simple_zero
    {f A : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0)
    (hA : ContinuousAt A x) :
    Tendsto (fun w => (w - x) * ((deriv f w / f w) * A w))
      (nhdsWithin x ({x}ᶜ : Set ℂ)) (nhds (A x)) := by
  simpa [logDeriv_apply] using
    tendsto_mul_logDeriv_mul_simple_zero hf hfx hf' hA

/-- At a simple zero of `Z₁` in the high rectangle, the packet-polarized
`Z₁'/Z₁` source has singular coefficient exactly
`C_𝒵(x) * 𝓑_{v,w}(x)`. -/
theorem zetaOne_packetIntegrand_simpleZero_coefficient
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {x : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hx : x ∈ highRectangleNhd T₁ T₂ ε)
    (hz : zetaOne x = 0) (hz' : deriv zetaOne x ≠ 0) :
    Tendsto
      (fun s => (s - x) *
        ((deriv zetaOne s / zetaOne s) * hardyCurvature q s *
          packetPolarization ψ v w s))
      (nhdsWithin x ({x}ᶜ : Set ℂ))
      (nhds (hardyCurvature q x * packetPolarization ψ v w x)) := by
  have him := highRectangleNhd_im_ne_zero hεT x hx
  have hzetaOne : AnalyticAt ℂ zetaOne x := analyticAt_zetaOne_of_im_ne_zero him
  have hcurv : AnalyticAt ℂ (hardyCurvature q) x :=
    analyticOnNhd_hardyCurvature_highRectangle hεT hqa x hx
  have hpacket : AnalyticAt ℂ (packetPolarization ψ v w) x :=
    (differentiable_packetPolarization hψ v w).analyticAt x
  have hAmp : ContinuousAt
      (fun s => hardyCurvature q s * packetPolarization ψ v w s) x :=
    (hcurv.mul hpacket).continuousAt
  simpa [mul_assoc] using
    tendsto_mul_deriv_div_mul_simple_zero hzetaOne hz hz' hAmp

end HardyGaugeInvariantContourForm
end ZetaZero
