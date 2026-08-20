import ZetaZero.RightEdgeArithmeticSource.StationaryGaussianScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Oscillatory approximation in Gaussian coordinates

This file transfers the real phase remainder to the complex oscillatory kernel.
The key point is the unit-circle Lipschitz estimate

`‖exp(i a) - exp(i b)‖ ≤ |a-b|`,

which converts the cubic phase error into a pointwise kernel error.  A finite
stationary window then gives an explicit integral error without using any
improper Fresnel integral yet.
-/

noncomputable section

open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The complex unit-circle exponential is 1-Lipschitz in its real phase. -/
theorem norm_cexp_I_mul_real_sub_le
    (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have hfactor :
      Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
        Complex.exp (Complex.I * b) *
          (Complex.exp (Complex.I * (a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal]
  simp only [one_mul]
  simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- The exact centered stationary phase in Gaussian coordinates. -/
def stationaryGaussianPhase (eta y : ℝ) : ℝ :=
  stationaryScale eta *
    (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1)

/-- The universal quadratic Gaussian phase. -/
def quadraticGaussianPhase (y : ℝ) : ℝ :=
  y ^ 2 / 2

/-- Exact one-chi oscillatory kernel in Gaussian coordinates. -/
def stationaryOscillatoryKernel (eta y : ℝ) : ℂ :=
  Complex.exp (Complex.I * stationaryGaussianPhase eta y)

/-- Universal quadratic oscillatory kernel. -/
def quadraticOscillatoryKernel (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * quadraticGaussianPhase y)

/-- The cubic phase remainder transfers directly to the oscillatory kernel. -/
theorem stationaryOscillatoryKernel_sub_quadratic_norm_le
    {eta y : ℝ} (heta : 0 < eta)
    (hy : |y| ≤ Real.sqrt (stationaryScale eta) / 2) :
    ‖stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y‖ ≤
      (2 / 3 : ℝ) * |y| ^ 3 / Real.sqrt (stationaryScale eta) := by
  unfold stationaryOscillatoryKernel quadraticOscillatoryKernel
  refine (norm_cexp_I_mul_real_sub_le
    (stationaryGaussianPhase eta y) (quadraticGaussianPhase y)).trans ?_
  unfold stationaryGaussianPhase quadraticGaussianPhase
  exact stationaryGaussianCoordinate_phase_remainder heta hy

/-- On a symmetric Gaussian window `[-R,R]`, the pointwise oscillatory error is
uniformly bounded by the endpoint cubic error. -/
theorem stationaryOscillatoryKernel_sub_quadratic_norm_le_on_window
    {eta R y : ℝ} (heta : 0 < eta) (hR0 : 0 ≤ R)
    (hR : R ≤ Real.sqrt (stationaryScale eta) / 2)
    (hy : y ∈ Set.uIcc (-R) R) :
    ‖stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y‖ ≤
      (2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta) := by
  have hyabs : |y| ≤ R := by
    rw [Set.mem_uIcc] at hy
    rcases hy with hy | hy
    · rw [abs_le]
      exact ⟨by linarith [hy.1], hy.2⟩
    · rw [abs_le]
      exact ⟨by linarith [hy.1, hy.2, hR0], by linarith [hy.1, hy.2, hR0]⟩
  have hlocal : |y| ≤ Real.sqrt (stationaryScale eta) / 2 := hyabs.trans hR
  have hpoint := stationaryOscillatoryKernel_sub_quadratic_norm_le heta hlocal
  have hsqrtpos : 0 < Real.sqrt (stationaryScale eta) :=
    Real.sqrt_pos.2 (stationaryScale_pos heta)
  have hcubic : |y| ^ 3 ≤ R ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg y) hyabs 3
  calc
    ‖stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y‖ ≤
        (2 / 3 : ℝ) * |y| ^ 3 / Real.sqrt (stationaryScale eta) := hpoint
    _ ≤ (2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta) := by
      gcongr

/-- Finite-window stationary replacement: replacing the exact local phase by
its quadratic Gaussian model costs `O(R^4 / sqrt(t_*))` on `[-R,R]`. -/
theorem norm_intervalIntegral_stationary_sub_quadratic_le
    {eta R : ℝ} (heta : 0 < eta) (hR0 : 0 ≤ R)
    (hR : R ≤ Real.sqrt (stationaryScale eta) / 2) :
    ‖(∫ y in (-R)..R,
        (stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y))‖ ≤
      (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R)
    (C := (2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta))
    (f := fun y : ℝ => stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y)
    (fun y hy =>
      stationaryOscillatoryKernel_sub_quadratic_norm_le_on_window
        heta hR0 hR (Set.uIoc_subset_uIcc hy))
  have hwidth : |R - (-R)| = 2 * R := by
    rw [sub_neg_eq_add, ← two_mul,
      abs_of_nonneg (mul_nonneg (by norm_num) hR0)]
  rw [hwidth] at hbound
  calc
    ‖(∫ y in (-R)..R,
        (stationaryOscillatoryKernel eta y - quadraticOscillatoryKernel y))‖ ≤
      ((2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta)) * (2 * R) := hbound
    _ = (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) := by ring

end RightEdgeArithmeticSource
end ZetaZero
