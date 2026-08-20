import ZetaZero.RightEdgeArithmeticSource.StationaryOscillatoryApproximation
import ZetaZero.RightEdgeArithmeticSource.StationaryFresnelAbel

/-!
# Combined finite-window stationary main-term error

This module keeps the two rigorously established errors separate:

1. exact stationary phase -> quadratic phase on `[-R,R]`;
2. finite quadratic window -> full Fresnel constant.

Their sum is the error ledger needed before the final interval-integrability /
linearity bridge identifies it with the difference between the exact stationary
integral and its Fresnel main term.
-/

noncomputable section

open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The two definitions of the quadratic oscillatory kernel used by the local
stationary module and the Fresnel-tail module agree pointwise. -/
theorem quadraticOscillatoryKernel_eq_quadraticOscillation (y : ℝ) :
    quadraticOscillatoryKernel y = quadraticOscillation y := by
  unfold quadraticOscillatoryKernel quadraticGaussianPhase quadraticOscillation
  congr 2
  push_cast
  ring

/-- The quadratic Fresnel finite-window estimate in the local-kernel notation. -/
theorem norm_intervalIntegral_quadraticOscillatoryKernel_sub_standard_le_four_div
    {R : ℝ} (hR : 0 < R) :
    ‖(∫ y in -R..R, quadraticOscillatoryKernel y) -
        (Real.sqrt Real.pi : ℂ) * (1 + Complex.I)‖ ≤ 4 / R := by
  have h := norm_symmetricQuadraticIntegral_sub_standard_le_four_div hR
  have hint :
      (∫ y in -R..R, quadraticOscillatoryKernel y) =
        ∫ y in -R..R, quadraticOscillation y := by
    apply intervalIntegral.integral_congr
    intro y _
    exact quadraticOscillatoryKernel_eq_quadraticOscillation y
  rw [hint]
  exact h

/-- The exact stationary kernel is Borel measurable; continuity at the zero of
the real logarithm is not needed for finite-window integrability. -/
theorem measurable_stationaryOscillatoryKernel (eta : ℝ) :
    Measurable (stationaryOscillatoryKernel eta) := by
  unfold stationaryOscillatoryKernel stationaryGaussianPhase
    normalizedOneChiPhase stationaryGaussianCoordinate
  measurability

/-- The exact stationary kernel has unit norm. -/
theorem norm_stationaryOscillatoryKernel (eta y : ℝ) :
    ‖stationaryOscillatoryKernel eta y‖ = 1 := by
  unfold stationaryOscillatoryKernel
  exact Complex.norm_exp_I_mul_ofReal _

/-- Hence the exact stationary kernel is interval-integrable on every symmetric
finite window.  This uses only measurability and the unit-norm bound. -/
theorem intervalIntegrable_stationaryOscillatoryKernel
    (eta : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (stationaryOscillatoryKernel eta)
      MeasureTheory.volume (-R) R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  apply MeasureTheory.Measure.integrableOn_of_bounded
    (measure_Ioc_lt_top.ne)
    (measurable_stationaryOscillatoryKernel eta).aestronglyMeasurable
    (M := 1)
  filter_upwards with y
  rw [norm_stationaryOscillatoryKernel]

/-- Error ledger obtained by adding the local phase-replacement error and the
finite Fresnel-window error. -/
def stationaryMainTermError (eta R : ℝ) : ℂ :=
  (∫ y in -R..R,
      (stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y)) +
    ((∫ y in -R..R, quadraticOscillatoryKernel y) -
      (Real.sqrt Real.pi : ℂ) * (1 + Complex.I))

/-- Once the exact stationary kernel is known to be interval-integrable on the
finite window, the two-term error ledger is exactly the difference between the
exact stationary integral and the Fresnel constant.  This isolates the only
remaining local analytic bridge instead of hiding it inside the error estimate. -/
theorem stationaryMainTermError_eq_intervalIntegral_sub_standard
    {eta R : ℝ}
    (hstat : IntervalIntegrable (stationaryOscillatoryKernel eta)
      MeasureTheory.volume (-R) R) :
    stationaryMainTermError eta R =
      (∫ y in -R..R, stationaryOscillatoryKernel eta y) -
        (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) := by
  have hquad0 := intervalIntegrable_quadraticOscillation (-R) R
  have hquad :
      IntervalIntegrable quadraticOscillatoryKernel MeasureTheory.volume (-R) R :=
    hquad0.congr (fun y _ =>
      (quadraticOscillatoryKernel_eq_quadraticOscillation y).symm)
  unfold stationaryMainTermError
  rw [intervalIntegral.integral_sub hstat hquad]
  ring

/-- Combined quantitative stationary error before the final integral-linearity
bridge. -/
theorem norm_stationaryMainTermError_le
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hwindow : R ≤ Real.sqrt (stationaryScale eta) / 2) :
    ‖stationaryMainTermError eta R‖ ≤
      (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) + 4 / R := by
  unfold stationaryMainTermError
  calc
    ‖(∫ y in -R..R,
          (stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y)) +
        ((∫ y in -R..R, quadraticOscillatoryKernel y) -
          (Real.sqrt Real.pi : ℂ) * (1 + Complex.I))‖ ≤
        ‖(∫ y in -R..R,
          (stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y))‖ +
        ‖(∫ y in -R..R, quadraticOscillatoryKernel y) -
          (Real.sqrt Real.pi : ℂ) * (1 + Complex.I)‖ := norm_add_le _ _
    _ ≤ (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) + 4 / R := by
      exact add_le_add
        (norm_intervalIntegral_stationary_sub_quadratic_le heta hR.le hwindow)
        (norm_intervalIntegral_quadraticOscillatoryKernel_sub_standard_le_four_div hR)

/-- Exact finite-window stationary main-term bound.  No extra integrability
hypothesis is needed: the unit-modulus stationary kernel is automatically
interval-integrable on every finite window. -/
theorem norm_intervalIntegral_stationary_sub_standard_le
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hwindow : R ≤ Real.sqrt (stationaryScale eta) / 2) :
    ‖(∫ y in -R..R, stationaryOscillatoryKernel eta y) -
        (Real.sqrt Real.pi : ℂ) * (1 + Complex.I)‖ ≤
      (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) + 4 / R := by
  have hstat := intervalIntegrable_stationaryOscillatoryKernel eta hR.le
  rw [← stationaryMainTermError_eq_intervalIntegral_sub_standard hstat]
  exact norm_stationaryMainTermError_le heta hR hwindow

/-- If the window is chosen so that `R^5 <= sqrt(t_*)`, the cubic replacement
error is already at most `4/(3R)`, hence both stationary errors are `O(1/R)`. -/
theorem norm_stationaryMainTermError_le_sixteen_div_three_mul_inv
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hwindow : R ≤ Real.sqrt (stationaryScale eta) / 2)
    (hbalance : R ^ 5 ≤ Real.sqrt (stationaryScale eta)) :
    ‖stationaryMainTermError eta R‖ ≤ (16 / 3 : ℝ) / R := by
  have hsqrt : 0 < Real.sqrt (stationaryScale eta) :=
    Real.sqrt_pos.2 (stationaryScale_pos heta)
  have hR4 : R ^ 4 ≤ Real.sqrt (stationaryScale eta) / R := by
    rw [le_div_iff₀ hR]
    simpa [pow_succ] using hbalance
  have hfrac :
      R ^ 4 / Real.sqrt (stationaryScale eta) ≤ (1 : ℝ) / R := by
    rw [div_le_iff₀ hsqrt]
    simpa [div_eq_mul_inv, mul_comm] using hR4
  have hcubic :
      (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) ≤
        (4 / 3 : ℝ) / R := by
    calc
      (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) =
          (4 / 3 : ℝ) * (R ^ 4 / Real.sqrt (stationaryScale eta)) := by ring
      _ ≤ (4 / 3 : ℝ) * ((1 : ℝ) / R) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = (4 / 3 : ℝ) / R := by ring
  calc
    ‖stationaryMainTermError eta R‖ ≤
        (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) + 4 / R :=
      norm_stationaryMainTermError_le heta hR hwindow
    _ ≤ (4 / 3 : ℝ) / R + 4 / R := add_le_add hcubic le_rfl
    _ = (16 / 3 : ℝ) / R := by ring

/-- Balanced exact stationary main-term estimate. -/
theorem norm_intervalIntegral_stationary_sub_standard_le_sixteen_div_three_mul_inv
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 < R)
    (hwindow : R ≤ Real.sqrt (stationaryScale eta) / 2)
    (hbalance : R ^ 5 ≤ Real.sqrt (stationaryScale eta)) :
    ‖(∫ y in -R..R, stationaryOscillatoryKernel eta y) -
        (Real.sqrt Real.pi : ℂ) * (1 + Complex.I)‖ ≤ (16 / 3 : ℝ) / R := by
  have hstat := intervalIntegrable_stationaryOscillatoryKernel eta hR.le
  rw [← stationaryMainTermError_eq_intervalIntegral_sub_standard hstat]
  exact norm_stationaryMainTermError_le_sixteen_div_three_mul_inv
    heta hR hwindow hbalance

end RightEdgeArithmeticSource
end ZetaZero
