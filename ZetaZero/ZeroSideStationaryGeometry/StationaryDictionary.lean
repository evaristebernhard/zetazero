import ZetaZero.HardyGaugeInvariantContourForm.Zeta23HardyBridge
import ZetaZero.HardyGaugeInvariantContourForm.CriticalLinePhase
import Zeta23.XiPrime.Hardy.ZFunction

/-!
# Critical-line dictionary: `Z₁` zeros are Hardy stationary points

The preceding bridge identifies the manuscript source `Z₁` with Zeta23's proved
Hardy source `W` off the real axis.  This file specializes that identification
to the critical line and imports the already-formalized Hardy-Z derivative
dictionary.  It closes the conceptual M02→M03 seam without redoing the phase
differentiation.
-/

open Complex

noncomputable section

namespace ZetaZero
namespace ZeroSideStationaryGeometry

open HardyGaugeInvariantContourForm

/-- The two projects use the same critical-line parametrization. -/
theorem criticalLine_eq_zeta23_sline (t : ℝ) :
    criticalLine t = Zeta23.XiPrime.sline t := by
  rfl

/-- On the nonzero critical line, the manuscript `Z₁` source is exactly the
already-formalized Zeta23 Hardy source `W`. -/
theorem zetaOne_criticalLine_eq_hardyW {t : ℝ} (ht : t ≠ 0) :
    zetaOne (criticalLine t) =
      Zeta23.XiPrime.hardyW (Zeta23.XiPrime.sline t) := by
  rw [zetaOne_eq_zeta23_hardyW (by simpa using ht), criticalLine_eq_zeta23_sline]

/-- A critical-line zero of `Z₁` is exactly a stationary point of the real Hardy
`Z` function. -/
theorem zetaOne_criticalLine_eq_zero_iff_stationary {t : ℝ} (ht : t ≠ 0) :
    zetaOne (criticalLine t) = 0 ↔ deriv Zeta23.XiPrime.hardyZ t = 0 := by
  rw [zetaOne_criticalLine_eq_hardyW ht]
  exact (Zeta23.XiPrime.deriv_hardyZ_eq_zero_iff ht).symm

/-- The first derivative of `Z₁` on the critical line agrees with the first
complex derivative of the Zeta23 Hardy source. -/
theorem deriv_zetaOne_criticalLine_eq_deriv_hardyW {t : ℝ} (ht : t ≠ 0) :
    deriv zetaOne (criticalLine t) =
      deriv Zeta23.XiPrime.hardyW (Zeta23.XiPrime.sline t) := by
  rw [deriv_zetaOne_eq_zeta23_hardyW (by simpa using ht), criticalLine_eq_zeta23_sline]

/-- A simple critical-line zero of `Z₁` is exactly a simple stationary point of
Hardy's real `Z`: `Z'(t)=0` and `Z''(t)≠0`. -/
theorem zetaOne_simpleZero_criticalLine_iff_simpleStationary
    {t : ℝ} (ht : t ≠ 0) :
    (zetaOne (criticalLine t) = 0 ∧ deriv zetaOne (criticalLine t) ≠ 0) ↔
      (deriv Zeta23.XiPrime.hardyZ t = 0 ∧
        deriv (deriv Zeta23.XiPrime.hardyZ) t ≠ 0) := by
  have hWval := zetaOne_criticalLine_eq_hardyW ht
  have hWder := deriv_zetaOne_criticalLine_eq_deriv_hardyW ht
  constructor
  · rintro ⟨hz, hz'⟩
    have hW : Zeta23.XiPrime.hardyW (Zeta23.XiPrime.sline t) = 0 := by
      rw [← hWval]
      exact hz
    have hW' : deriv Zeta23.XiPrime.hardyW (Zeta23.XiPrime.sline t) ≠ 0 := by
      rwa [hWder] at hz'
    exact ⟨(Zeta23.XiPrime.deriv_hardyZ_eq_zero_iff ht).2 hW,
      (Zeta23.XiPrime.deriv2_hardyZ_ne_zero_iff ht hW).2 hW'⟩
  · rintro ⟨hstat, hstat2⟩
    have hW : Zeta23.XiPrime.hardyW (Zeta23.XiPrime.sline t) = 0 :=
      (Zeta23.XiPrime.deriv_hardyZ_eq_zero_iff ht).1 hstat
    have hW' : deriv Zeta23.XiPrime.hardyW (Zeta23.XiPrime.sline t) ≠ 0 :=
      (Zeta23.XiPrime.deriv2_hardyZ_ne_zero_iff ht hW).1 hstat2
    constructor
    · rwa [hWval]
    · rwa [hWder]

/-- The multiplicity used by the packet zero sum is exactly Zeta23's `wMult`
on every nonzero critical-line point. -/
theorem analyticOrderNatAt_zetaOne_criticalLine_eq_wMult
    {t : ℝ} (ht : t ≠ 0) :
    analyticOrderNatAt zetaOne (criticalLine t) =
      Zeta23.XiPrime.wMult (Zeta23.XiPrime.sline t) := by
  unfold analyticOrderNatAt Zeta23.XiPrime.wMult
  rw [analyticOrderAt_zetaOne_eq_zeta23_hardyW (by simpa using ht),
    criticalLine_eq_zeta23_sline]

end ZeroSideStationaryGeometry
end ZetaZero
