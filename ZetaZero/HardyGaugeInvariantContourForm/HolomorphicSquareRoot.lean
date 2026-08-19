import ZetaZero.Analytic.FunctionalEquationFactor
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic square roots on simply connected domains

The topological branch theorem in Mathlib first gives a continuous square root.
For a nonvanishing analytic function, the identity `q^2 = g` then upgrades this
branch to a holomorphic one: locally the square map has nonzero derivative
`2q`, so differentiability of `q` follows from `HasDerivAt.of_comp_left`.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- A continuous square-root branch of a nonvanishing analytic function on an
open simply connected set is automatically analytic. -/
theorem exists_analyticOnNhd_squareRoot
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hga : AnalyticOnNhd ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q U ∧ ∀ z, q z ^ 2 = g z := by
  have himage : 0 ∉ g '' U := by
    rintro ⟨z, hz, hz0⟩
    exact (hg0 z hz) hz0
  rcases Complex.exists_continuousOn_pow_eq hUc hUo hga.continuousOn himage
      (n := 2) two_ne_zero with ⟨q, hqc, hqpow⟩
  have hqd : DifferentiableOn ℂ q U := by
    intro z hz
    have hqcont : ContinuousAt q z := hqc.continuousAt (hUo.mem_nhds hz)
    have hqne : q z ≠ 0 := by
      intro hq0
      apply hg0 z hz
      rw [← hqpow z, hq0]
      simp
    have hsquare : HasDerivAt (fun w : ℂ => w ^ 2) (2 * q z) (q z) := by
      simpa using (hasStrictDerivAt_pow 2 (q z)).hasDerivAt
    have hgderiv : HasDerivAt g (deriv g z) z :=
      (hga z hz).differentiableAt.hasDerivAt
    have hsquare_ne : (2 : ℂ) * q z ≠ 0 := mul_ne_zero two_ne_zero hqne
    have hcomp : (fun w : ℂ => w ^ 2) ∘ q =ᶠ[𝓝 z] g :=
      Filter.Eventually.of_forall fun y => hqpow y
    exact (HasDerivAt.of_comp_left hqcont hsquare hgderiv hsquare_ne hcomp).differentiableAt.differentiableWithinAt
  exact ⟨q, hqd.analyticOnNhd hUo, hqpow⟩

/-- On any open simply connected domain disjoint from the real axis, the
functional-equation factor `chiOneSub = χ(1-s)` admits a holomorphic square
root.  This is the analytic Hardy-gauge branch required by the manuscript. -/
theorem exists_hardyGaugeSquareRoot
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (hUhigh : ∀ z ∈ U, z.im ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q U ∧
      ∀ z, q z ^ 2 = Analytic.chiOneSub z := by
  apply exists_analyticOnNhd_squareRoot hUc hUo
  · intro z hz
    exact Analytic.analyticAt_chiOneSub_of_im_ne_zero (hUhigh z hz)
  · intro z hz
    exact Analytic.chiOneSub_ne_zero_of_im_ne_zero (hUhigh z hz)

end HardyGaugeInvariantContourForm
end ZetaZero
