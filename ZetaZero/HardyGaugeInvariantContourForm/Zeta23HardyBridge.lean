import ZetaZero.HardyGaugeInvariantContourForm.GaugeDerivative
import Zeta23.XiPrime.Hardy.Basic

/-!
# Identification of the manuscript `Z₁` with the proved Zeta23 Hardy source

The local `zeta-23-lean` development uses

`W = ζ' + L₂ ζ`,  with  `L₂ = -1/2 logDeriv χ`,

whereas the present manuscript uses

`Z₁ = ζ' + f ζ`,  with  `f = 1/2 logDeriv χ(1-s)`.

Off the real axis the two logarithmic-derivative coefficients are identical.
This bridge makes the equality local (hence derivative- and multiplicity-safe),
so the existing `W` zero-count, reflection, good-height, and Hardy-stationary
machinery can be reused without changing the manuscript normalization.
-/

open Complex Filter Set Topology

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- The manuscript Hardy coefficient has the symmetric Gamma logarithmic-
derivative formula used by the Zeta23 `L₂` source. -/
theorem hardyF_eq_gammaLogDeriv {s : ℂ} (hs : s.im ≠ 0) :
    hardyF s =
      (logDeriv Gammaℝ s + logDeriv Gammaℝ (1 - s)) / 2 := by
  have hG : Gammaℝ s ≠ 0 := Analytic.Gammaℝ_ne_zero_of_im_ne_zero hs
  have hG1 : Gammaℝ (1 - s) ≠ 0 :=
    Analytic.Gammaℝ_ne_zero_of_im_ne_zero (Analytic.im_one_sub_ne_zero hs)
  have hdG : DifferentiableAt ℂ Gammaℝ s :=
    Analytic.differentiableAt_Gammaℝ_of_im_ne_zero hs
  have hdG1 : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (1 - z)) s :=
    (Analytic.differentiableAt_Gammaℝ_of_im_ne_zero
      (Analytic.im_one_sub_ne_zero hs)).comp s
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
  have hden :
      logDeriv (fun z : ℂ => Gammaℝ (1 - z)) s =
        -logDeriv Gammaℝ (1 - s) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub]
    ring
  unfold hardyF Analytic.chiOneSub
  rw [logDeriv_div _ hG hG1 hdG hdG1, hden]
  ring

/-- Exact identification `f = L₂` at every non-real point. -/
theorem hardyF_eq_zeta23_L2 {s : ℂ} (hs : s.im ≠ 0) :
    hardyF s = Zeta23.XiPrime.L2 s := by
  rw [hardyF_eq_gammaLogDeriv hs, Zeta23.XiPrime.Hardy.L2_eq hs]

/-- Exact pointwise identification of the two stationary sources off the real
axis. -/
theorem zetaOne_eq_zeta23_hardyW {s : ℂ} (hs : s.im ≠ 0) :
    zetaOne s = Zeta23.XiPrime.hardyW s := by
  rw [zetaOne, Zeta23.XiPrime.hardyW, hardyF_eq_zeta23_L2 hs]

/-- Near any non-real point, `Z₁` and the Zeta23 `W` source are literally the
same germ.  This is the key form needed to transport derivatives and analytic
multiplicities. -/
theorem zetaOne_eventuallyEq_zeta23_hardyW {s : ℂ} (hs : s.im ≠ 0) :
    zetaOne =ᶠ[𝓝 s] Zeta23.XiPrime.hardyW := by
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} :=
    isOpen_ne_fun Complex.continuous_im continuous_const
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact zetaOne_eq_zeta23_hardyW hz

/-- The first derivatives agree at every non-real point. -/
theorem deriv_zetaOne_eq_zeta23_hardyW {s : ℂ} (hs : s.im ≠ 0) :
    deriv zetaOne s = deriv Zeta23.XiPrime.hardyW s :=
  (zetaOne_eventuallyEq_zeta23_hardyW hs).deriv_eq

/-- Analytic multiplicity is preserved by the identification `Z₁ = W`. -/
theorem analyticOrderAt_zetaOne_eq_zeta23_hardyW {s : ℂ} (hs : s.im ≠ 0) :
    analyticOrderAt zetaOne s = analyticOrderAt Zeta23.XiPrime.hardyW s :=
  analyticOrderAt_congr (zetaOne_eventuallyEq_zeta23_hardyW hs)

/-- Zerohood is identical for `Z₁` and Zeta23's `W` off the real axis. -/
theorem zetaOne_eq_zero_iff_zeta23_hardyW_eq_zero {s : ℂ} (hs : s.im ≠ 0) :
    zetaOne s = 0 ↔ Zeta23.XiPrime.hardyW s = 0 := by
  rw [zetaOne_eq_zeta23_hardyW hs]

end HardyGaugeInvariantContourForm
end ZetaZero
