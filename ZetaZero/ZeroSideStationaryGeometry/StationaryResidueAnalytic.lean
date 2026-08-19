import ZetaZero.ZeroSideStationaryGeometry.StationaryResidueBlocks
import ZetaZero.HardyGaugeInvariantContourForm.SimpleZeroLogResidue
import Mathlib.Tactic.Ring

/-!
# Local analytic coefficient at a simple stationary zero

If `H'(c)=0` and `H''(c)≠0`, then the meromorphic stationary kernel

`-H(z) (H''(z))² / H'(z)`

has principal coefficient `-H(c)H''(c)`.  The proof is a direct specialization
of the simple-zero logarithmic-derivative coefficient proved in M02, applied
to `f = H'` with analytic amplitude `-H H''`.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace ZeroSideStationaryGeometry

open HardyGaugeInvariantContourForm

/-- The meromorphic stationary kernel before the positive `L⁻²` normalization. -/
def stationaryKernel (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  -H z * (deriv (deriv H) z) ^ 2 / deriv H z

/-- Algebraic rewrite of the stationary kernel as a logarithmic derivative of
`H'` times the analytic amplitude `-H H''`. -/
theorem stationaryKernel_eq_logDeriv_mul (H : ℂ → ℂ) (z : ℂ) :
    stationaryKernel H z =
      logDeriv (deriv H) z * (-H z * deriv (deriv H) z) := by
  simp only [stationaryKernel, logDeriv_apply]
  ring

/-- At a simple stationary zero, the punctured-neighbourhood principal
coefficient tends to the manuscript residue `-H(c)H''(c)`. -/
theorem tendsto_stationaryKernel_principalCoefficient
    {H : ℂ → ℂ} {c : ℂ}
    (hH : AnalyticAt ℂ H c)
    (hcrit : deriv H c = 0)
    (hsimple : deriv (deriv H) c ≠ 0) :
    Tendsto (fun z => (z - c) * stationaryKernel H z)
      (nhdsWithin c ({c}ᶜ : Set ℂ))
      (𝓝 (-H c * deriv (deriv H) c)) := by
  have hAmp : ContinuousAt
      (fun z => -H z * deriv (deriv H) z) c :=
    (hH.neg.mul hH.deriv.deriv).continuousAt
  have hlog := tendsto_mul_logDeriv_mul_simple_zero
    hH.deriv hcrit hsimple hAmp
  simpa [stationaryKernel_eq_logDeriv_mul, mul_assoc] using hlog

end ZeroSideStationaryGeometry
end ZetaZero
