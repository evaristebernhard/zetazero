import ZetaZero.HardyGaugeInvariantContourForm.PacketZeroSum
import ZetaZero.HardyGaugeInvariantContourForm.BranchReflection
import ZetaZero.ZeroSideStationaryGeometry.StationaryResidueAnalytic
import ZetaZero.ZeroSideStationaryGeometry.StationarySourceBridge
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# Straightening the critical line to zero coordinates

The paper passes from the spectral variable `s` to

`z = -i (s - 1/2)`, equivalently `s = 1/2 + i z`.

This module fixes the derivative signs under that affine change of variables and
connects the global `Z₁` zero-sum weight from M02 with the stationary residue
weight used in M03.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace ZeroSideStationaryGeometry

open HardyGaugeInvariantContourForm

/-- Spectral point corresponding to a straightened zero coordinate. -/
def spectralOfZeroCoordinate (z : ℂ) : ℂ := (1 / 2 : ℂ) + I * z

/-- Straightening of a complex function from the spectral plane to the zero
coordinate. -/
def straighten (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  G (spectralOfZeroCoordinate z)

@[simp] theorem contourCoordinate_spectralOfZeroCoordinate (z : ℂ) :
    contourCoordinate (spectralOfZeroCoordinate z) = z := by
  simp [contourCoordinate, spectralOfZeroCoordinate]
  simp [← mul_assoc, Complex.I_mul_I]

@[simp] theorem spectralOfZeroCoordinate_contourCoordinate (s : ℂ) :
    spectralOfZeroCoordinate (contourCoordinate s) = s := by
  simp [contourCoordinate, spectralOfZeroCoordinate]
  simp [← mul_assoc, Complex.I_mul_I]

/-- First derivative under `s = 1/2 + i z`: `F' = i G'`. -/
theorem deriv_straighten (G : ℂ → ℂ) :
    deriv (straighten G) =
      fun z => I * deriv G (spectralOfZeroCoordinate z) := by
  funext z
  unfold straighten spectralOfZeroCoordinate
  calc
    deriv (fun x : ℂ => (fun y : ℂ => G ((1 / 2 : ℂ) + y)) (I * x)) z =
        I • deriv (fun y : ℂ => G ((1 / 2 : ℂ) + y)) (I * z) := by
      simpa using
        (deriv_comp_mul_left I (fun y : ℂ => G ((1 / 2 : ℂ) + y)) z)
    _ = I * deriv G ((1 / 2 : ℂ) + I * z) := by
      rw [deriv_comp_const_add]
      simp [smul_eq_mul]

/-- Second derivative under straightening: `F'' = -G''`. -/
theorem secondDeriv_straighten (G : ℂ → ℂ) (z : ℂ) :
    deriv (deriv (straighten G)) z =
      -deriv (deriv G) (spectralOfZeroCoordinate z) := by
  rw [deriv_straighten]
  rw [deriv_const_mul_field]
  change I * deriv (straighten (deriv G)) z = _
  rw [congrFun (deriv_straighten (deriv G)) z]
  simp [← mul_assoc, Complex.I_mul_I]

/-- A `Z₁` zero is a stationary point of the analytic Hardy gauge. -/
theorem deriv_hardyGauge_eq_zero_of_zetaOne_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s = 0) :
    deriv (hardyGauge q) s = 0 := by
  rw [deriv_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow s hs, hz1, mul_zero]

/-- At a `Z₁` zero the curvature drops to `𝒵 𝒵''`. -/
theorem hardyCurvature_at_zetaOne_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {s : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hs : s ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne s = 0) :
    hardyCurvature q s =
      hardyGauge q s * deriv (deriv (hardyGauge q)) s := by
  have hstat := deriv_hardyGauge_eq_zero_of_zetaOne_zero hεT hqa hqpow hs hz1
  unfold hardyCurvature curvatureJet
  rw [hstat]
  ring

/-- The global zero-sum weight is exactly the stationary weight after
straightening.  If `s = 1/2 + i z` and `Z₁(s)=0`, then
`C_𝒵(s) = -F(z) F''(z)`. -/
theorem hardyCurvature_eq_neg_straightened_stationaryWeight
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {z : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ s, q s ^ 2 = Analytic.chiOneSub s)
    (hs : spectralOfZeroCoordinate z ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne (spectralOfZeroCoordinate z) = 0) :
    hardyCurvature q (spectralOfZeroCoordinate z) =
      -(straighten (hardyGauge q) z * deriv (deriv (straighten (hardyGauge q))) z) := by
  rw [hardyCurvature_at_zetaOne_zero hεT hqa hqpow hs hz1]
  rw [secondDeriv_straighten]
  unfold straighten
  ring

/-- A `Z₁` zero straightens to a stationary zero of `F`. -/
theorem deriv_straighten_hardyGauge_eq_zero_of_zetaOne_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {z : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ s, q s ^ 2 = Analytic.chiOneSub s)
    (hs : spectralOfZeroCoordinate z ∈ highRectangleNhd T₁ T₂ ε)
    (hz1 : zetaOne (spectralOfZeroCoordinate z) = 0) :
    deriv (straighten (hardyGauge q)) z = 0 := by
  have hstat := deriv_hardyGauge_eq_zero_of_zetaOne_zero hεT hqa hqpow hs hz1
  rw [congrFun (deriv_straighten (hardyGauge q)) z, hstat, mul_zero]

/-- Reflection in zero coordinates is ordinary complex conjugation. -/
@[simp] theorem hardyReflect_spectralOfZeroCoordinate (z : ℂ) :
    hardyReflect (spectralOfZeroCoordinate z) =
      spectralOfZeroCoordinate (conj z) := by
  apply Complex.ext <;> simp [hardyReflect, spectralOfZeroCoordinate] <;> ring

/-- Real zero coordinates parametrize the critical line used by the manuscript. -/
@[simp] theorem spectralOfZeroCoordinate_real (t : ℝ) :
    spectralOfZeroCoordinate (t : ℂ) = criticalLine t := by
  simp [spectralOfZeroCoordinate, criticalLine]
  ring

/-- The Hardy-gauge reflection law becomes the usual Schwarz reflection law for
its straightened zero-coordinate representative. -/
theorem straighten_hardyGauge_conj
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hT : T₁ < T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ s, q s ^ 2 = Analytic.chiOneSub s)
    (hz : spectralOfZeroCoordinate z ∈ highRectangleNhd T₁ T₂ ε) :
    straighten (hardyGauge q) (conj z) =
      conj (straighten (hardyGauge q) z) := by
  change hardyGauge q (spectralOfZeroCoordinate (conj z)) =
    conj (hardyGauge q (spectralOfZeroCoordinate z))
  rw [← hardyReflect_spectralOfZeroCoordinate]
  exact hardyGauge_reflection_on_highRectangle hε hT hεT hqa hqpow
    (spectralOfZeroCoordinate z) hz

/-- On real zero coordinates the straightened Hardy gauge is fixed by
conjugation, i.e. it is real-valued in the sense used in Section 02. -/
theorem straighten_hardyGauge_real_conj
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {t : ℝ}
    (hε : 0 < ε) (hT : T₁ < T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ s, q s ^ 2 = Analytic.chiOneSub s)
    (ht : criticalLine t ∈ highRectangleNhd T₁ T₂ ε) :
    straighten (hardyGauge q) (t : ℂ) =
      conj (straighten (hardyGauge q) (t : ℂ)) := by
  have hz : spectralOfZeroCoordinate (t : ℂ) ∈ highRectangleNhd T₁ T₂ ε := by
    simpa using ht
  simpa using straighten_hardyGauge_conj hε hT hεT hqa hqpow hz

/-- On the high rectangle, stationary zeros of the straightened Hardy gauge are
exactly zeros of the manuscript source `Z₁`. This is the precise `F' = i q Z₁`
zero-set dictionary used by the zero-counting argument. -/
theorem deriv_straighten_hardyGauge_eq_zero_iff_zetaOne_zero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {z : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ s, q s ^ 2 = Analytic.chiOneSub s)
    (hs : spectralOfZeroCoordinate z ∈ highRectangleNhd T₁ T₂ ε) :
    deriv (straighten (hardyGauge q)) z = 0 ↔
      zetaOne (spectralOfZeroCoordinate z) = 0 := by
  rw [congrFun (deriv_straighten (hardyGauge q)) z,
    deriv_hardyGauge_eq_branch_mul_zetaOne hεT hqa hqpow
      (spectralOfZeroCoordinate z) hs]
  have hqne := branch_ne_zero_on_highRectangle hqpow hεT
    (spectralOfZeroCoordinate z) hs
  simp [hqne]

/-- The same straightening dictionary preserves simplicity: a simple zero of
`Z₁` is exactly a simple stationary point of `F`. -/
theorem straighten_hardyGauge_simpleStationary_iff_zetaOne_simpleZero
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {z : ℂ}
    (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ s, q s ^ 2 = Analytic.chiOneSub s)
    (hs : spectralOfZeroCoordinate z ∈ highRectangleNhd T₁ T₂ ε) :
    (deriv (straighten (hardyGauge q)) z = 0 ∧
      deriv (deriv (straighten (hardyGauge q))) z ≠ 0) ↔
      (zetaOne (spectralOfZeroCoordinate z) = 0 ∧
        deriv zetaOne (spectralOfZeroCoordinate z) ≠ 0) := by
  have hqne := branch_ne_zero_on_highRectangle hqpow hεT
    (spectralOfZeroCoordinate z) hs
  constructor
  · rintro ⟨hstat, hsimple⟩
    have hz1 := (deriv_straighten_hardyGauge_eq_zero_iff_zetaOne_zero
      hεT hqa hqpow hs).1 hstat
    refine ⟨hz1, ?_⟩
    intro hz1'
    apply hsimple
    rw [secondDeriv_straighten,
      deriv2_hardyGauge_eq_branch_mul_deriv_zetaOne_of_zero
        hεT hqa hqpow hs hz1,
      hz1', mul_zero, neg_zero]
  · rintro ⟨hz1, hz1'⟩
    refine ⟨(deriv_straighten_hardyGauge_eq_zero_iff_zetaOne_zero
      hεT hqa hqpow hs).2 hz1, ?_⟩
    rw [secondDeriv_straighten,
      deriv2_hardyGauge_eq_branch_mul_deriv_zetaOne_of_zero
        hεT hqa hqpow hs hz1]
    exact neg_ne_zero.mpr (mul_ne_zero hqne hz1')

end ZeroSideStationaryGeometry
end ZetaZero
