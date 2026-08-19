import ZetaZero.RightEdgeArithmeticSource.StationaryGaussianScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Oscillatory control at the one-chi saddle

This module converts the real phase estimates from `StationaryGaussianScaling`
into estimates for the actual unit-modulus complex oscillatory factors.  This
is the final local bridge needed before integrating the Gaussian model against
an amplitude.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The unit-circle exponential is `1`-Lipschitz with respect to its real
phase. -/
theorem norm_cexp_I_mul_sub_cexp_I_mul_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have hfactor :
      Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
        Complex.exp (Complex.I * b) *
          (Complex.exp (Complex.I * (a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

/-- Joint amplitude/phase perturbation bound for unit-modulus oscillations. -/
theorem norm_mul_cexp_I_sub_mul_cexp_I_le
    (A A0 : ℂ) (a b : ℝ) :
    ‖A * Complex.exp (Complex.I * a) -
        A0 * Complex.exp (Complex.I * b)‖ ≤
      ‖A - A0‖ + ‖A0‖ * |a - b| := by
  have hsplit :
      A * Complex.exp (Complex.I * a) -
          A0 * Complex.exp (Complex.I * b) =
        (A - A0) * Complex.exp (Complex.I * a) +
          A0 * (Complex.exp (Complex.I * a) -
            Complex.exp (Complex.I * b)) := by
    ring
  rw [hsplit]
  calc
    ‖(A - A0) * Complex.exp (Complex.I * a) +
        A0 * (Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b))‖ ≤
        ‖(A - A0) * Complex.exp (Complex.I * a)‖ +
          ‖A0 * (Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b))‖ :=
      norm_add_le _ _
    _ = ‖A - A0‖ + ‖A0‖ *
        ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal]
      ring
    _ ≤ ‖A - A0‖ + ‖A0‖ * |a - b| := by
      gcongr
      exact norm_cexp_I_mul_sub_cexp_I_mul_le a b

/-- In Gaussian coordinates, replacing the exact centered phase by `y^2/2`
changes the unit-modulus oscillatory factor by at most the same cubic
stationary-phase error. -/
theorem stationaryGaussianCoordinate_oscillation_remainder
    {eta y : ℝ} (heta : 0 < eta)
    (hy : |y| ≤ Real.sqrt (stationaryScale eta) / 2) :
    ‖Complex.exp
          (Complex.I *
            ((stationaryScale eta *
              (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      (2 / 3 : ℝ) * |y| ^ 3 / Real.sqrt (stationaryScale eta) := by
  have hphase := stationaryGaussianCoordinate_phase_remainder heta hy
  exact (norm_cexp_I_mul_sub_cexp_I_mul_le
    (stationaryScale eta *
      (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1))
    (y ^ 2 / 2)).trans hphase

/-- Integral-level phase replacement on a finite Gaussian window.  The exact
centered oscillation may be replaced by the quadratic Gaussian oscillation at
cost `O(R^4 / sqrt(t_*))`.  The constant here is deliberately soft; it comes
from bounding `|y|^3` by `R^3` before integration. -/
theorem stationaryGaussianCoordinate_integral_oscillation_remainder
    {eta R : ℝ} (heta : 0 < eta) (hR : 0 ≤ R)
    (hwindow : R ≤ Real.sqrt (stationaryScale eta) / 2) :
    ‖∫ y in -R..R,
        (Complex.exp
            (Complex.I *
              ((stationaryScale eta *
                (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ)))‖ ≤
      (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) := by
  have hspos := stationaryScale_pos heta
  have hsqrtpos : 0 < Real.sqrt (stationaryScale eta) := Real.sqrt_pos.2 hspos
  have horder : -R ≤ R := by linarith
  have hpoint :
      ∀ y ∈ Set.uIoc (-R) R,
        ‖Complex.exp
              (Complex.I *
                ((stationaryScale eta *
                  (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ))‖ ≤
          (2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta) := by
    intro y hy
    rw [Set.uIoc_of_le horder] at hy
    have hyabs : |y| ≤ R := abs_le.2 ⟨hy.1.le, hy.2⟩
    have hlocal := stationaryGaussianCoordinate_oscillation_remainder
      heta (hyabs.trans hwindow)
    refine hlocal.trans ?_
    apply (div_le_div_iff₀ hsqrtpos hsqrtpos).2
    gcongr
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R)
    (C := (2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta))
    (f := fun y : ℝ =>
      Complex.exp
          (Complex.I *
            ((stationaryScale eta *
              (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ)))
    hpoint
  calc
    ‖∫ y in -R..R,
        (Complex.exp
            (Complex.I *
              ((stationaryScale eta *
                (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ)))‖ ≤
        ((2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta)) * |R - (-R)| := hint
    _ = (4 / 3 : ℝ) * R ^ 4 / Real.sqrt (stationaryScale eta) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ R - (-R))]
      ring

/-- Local stationary integral with a frozen complex amplitude.  Amplitude
variation contributes linearly in the window length, while phase replacement
contributes the cubic Gaussian-scale error. -/
theorem stationaryGaussianCoordinate_integral_amplitude_freezing_remainder
    {eta R ε M : ℝ} {A : ℝ → ℂ} {A0 : ℂ}
    (heta : 0 < eta) (hR : 0 ≤ R)
    (hwindow : R ≤ Real.sqrt (stationaryScale eta) / 2)
    (hA0 : ‖A0‖ ≤ M)
    (hA : ∀ y ∈ Set.uIoc (-R) R, ‖A y - A0‖ ≤ ε) :
    ‖∫ y in -R..R,
        (A y * Complex.exp
            (Complex.I *
              ((stationaryScale eta *
                (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
          A0 * Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ)))‖ ≤
      2 * R * ε +
        (4 / 3 : ℝ) * M * R ^ 4 / Real.sqrt (stationaryScale eta) := by
  have hspos := stationaryScale_pos heta
  have hsqrtpos : 0 < Real.sqrt (stationaryScale eta) := Real.sqrt_pos.2 hspos
  have hM : 0 ≤ M := (norm_nonneg A0).trans hA0
  have horder : -R ≤ R := by linarith
  let Cphase : ℝ := (2 / 3 : ℝ) * R ^ 3 / Real.sqrt (stationaryScale eta)
  have hCphase : 0 ≤ Cphase := by
    dsimp [Cphase]
    positivity
  have hpoint :
      ∀ y ∈ Set.uIoc (-R) R,
        ‖A y * Complex.exp
              (Complex.I *
                ((stationaryScale eta *
                  (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
            A0 * Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ))‖ ≤
          ε + M * Cphase := by
    intro y hy
    have hyIoc := hy
    rw [Set.uIoc_of_le horder] at hyIoc
    have hyabs : |y| ≤ R := abs_le.2 ⟨hyIoc.1.le, hyIoc.2⟩
    have hywindow : |y| ≤ Real.sqrt (stationaryScale eta) / 2 := hyabs.trans hwindow
    have hphase := stationaryGaussianCoordinate_phase_remainder heta hywindow
    have hphaseR :
        |stationaryScale eta *
              (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) -
            y ^ 2 / 2| ≤ Cphase := by
      refine hphase.trans ?_
      dsimp [Cphase]
      apply (div_le_div_iff₀ hsqrtpos hsqrtpos).2
      gcongr
    calc
      ‖A y * Complex.exp
            (Complex.I *
              ((stationaryScale eta *
                (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
          A0 * Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ))‖ ≤
          ‖A y - A0‖ + ‖A0‖ *
            |stationaryScale eta *
                (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) -
              y ^ 2 / 2| :=
        norm_mul_cexp_I_sub_mul_cexp_I_le _ _ _ _
      _ ≤ ε + M * Cphase := by
        gcongr
        exact hA y hy
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R) (C := ε + M * Cphase)
    (f := fun y : ℝ =>
      A y * Complex.exp
          (Complex.I *
            ((stationaryScale eta *
              (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
        A0 * Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ)))
    hpoint
  calc
    ‖∫ y in -R..R,
        (A y * Complex.exp
            (Complex.I *
              ((stationaryScale eta *
                (normalizedOneChiPhase (stationaryGaussianCoordinate eta y) + 1) : ℝ) : ℂ)) -
          A0 * Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ)))‖ ≤
        (ε + M * Cphase) * |R - (-R)| := hint
    _ = 2 * R * ε +
        (4 / 3 : ℝ) * M * R ^ 4 / Real.sqrt (stationaryScale eta) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ R - (-R))]
      dsimp [Cphase]
      ring

end RightEdgeArithmeticSource
end ZetaZero
