import ZetaZero.Analytic.ZeroCountRelations
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Density-one endgame interface

This file records the paper-facing density-one target and proves the final
asymptotic normalization from an explicit off-critical gap estimate.  The
analytic work that supplies that estimate belongs to the M02--M09 interfaces;
it is intentionally not hidden behind an axiom or an unfinished theorem here.
-/

open Filter Topology Asymptotics

noncomputable section

namespace ZetaZero
namespace GenericPerturbationMinMaxEndgame

open ZetaZero.Analytic

section DensityOne

/-! The abstract count functions used by the final normalization step. -/

def densityOneRatio (N N₀ : ℝ → ℝ) : ℝ → ℝ :=
  fun T => N₀ T / N T

def relativeCountGap (N N₀ : ℝ → ℝ) : ℝ → ℝ :=
  fun T => N T - N₀ T

/-- The paper-facing density-one statement for a pair of count functions. -/
def DensityOne (N N₀ : ℝ → ℝ) : Prop :=
  Tendsto (densityOneRatio N N₀) atTop (𝓝 1)

/--
The finite-dimensional endgame only needs two asymptotic inputs at this final
stage: the total count tends to infinity, and the off-critical multiplicity
gap is little-o of the total count.  The pointwise count inequality supplies
the sign-free algebraic normalization of the ratio.
-/
theorem densityOne_of_relativeCountGap_isLittleO
    {N N₀ : ℝ → ℝ}
    (hNtop : Tendsto N atTop atTop)
    (_hN₀le : ∀ T, N₀ T ≤ N T)
    (hgap : relativeCountGap N N₀ =o[atTop] N) :
    DensityOne N N₀ := by
  have hgap_zero :
      Tendsto (fun T => relativeCountGap N N₀ T / N T) atTop (𝓝 0) := by
    simpa [relativeCountGap] using hgap.tendsto_div_nhds_zero
  have hN_event : ∀ᶠ T in atTop, N T ≥ 1 :=
    hNtop.eventually (eventually_ge_atTop (1 : ℝ))
  have hN_ne : ∀ᶠ T in atTop, N T ≠ 0 := by
    filter_upwards [hN_event] with T hT
    linarith
  have hratio :
      (fun T => densityOneRatio N N₀ T) =ᶠ[atTop]
        (fun T => 1 - relativeCountGap N N₀ T / N T) := by
    filter_upwards [hN_ne] with T hTN
    change N₀ T / N T = 1 - (N T - N₀ T) / N T
    field_simp [hTN]
    ring
  have hlimit :
      Tendsto (fun T => 1 - relativeCountGap N N₀ T / N T)
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hgap_zero
  exact hlimit.congr' hratio.symm

/-! Concrete paper-facing aliases for the dyadic zeta counts. -/

def dyadicDensityOne : Prop :=
  DensityOne
    (fun T : ℝ => (dyadicN T : ℝ))
    (fun T : ℝ => (dyadicN0 T : ℝ))

def dyadicOffCriticalGap (T : ℝ) : ℝ :=
  (dyadicN T : ℝ) - (dyadicN0 T : ℝ)

/--
M10's paper-facing density-one theorem.  The remaining analytic route must
construct `hgap`; this theorem supplies the checked final count normalization
without asserting that missing analytic input as an axiom.
-/
theorem density_one_critical_line
    (hNtop : Tendsto (fun T : ℝ => (dyadicN T : ℝ)) atTop atTop)
    (hgap : dyadicOffCriticalGap =o[atTop]
      (fun T : ℝ => (dyadicN T : ℝ))) :
    dyadicDensityOne := by
  apply densityOne_of_relativeCountGap_isLittleO hNtop
  · intro T
    exact_mod_cast dyadicN0_le_dyadicN T
  · change
      (fun T : ℝ =>
        (dyadicN T : ℝ) - (dyadicN0 T : ℝ)) =o[atTop]
        (fun T : ℝ => (dyadicN T : ℝ))
    exact hgap.congr_left (fun T => by rfl)

end DensityOne

end GenericPerturbationMinMaxEndgame
end ZetaZero
