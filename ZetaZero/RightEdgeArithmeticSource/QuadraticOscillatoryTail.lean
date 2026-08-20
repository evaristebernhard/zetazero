import ZetaZero.RightEdgeArithmeticSource.StationaryOscillationControl
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Quantitative tail bound for the quadratic oscillatory model

We prove the Fresnel tail estimate using a real scalar integration-by-parts
weight `1/y`.  Keeping the reciprocal weight real avoids unnecessary
real/complex derivative-instance conversions while giving the same bound.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The universal quadratic oscillation `exp(i y^2/2)`. -/
def quadraticOscillation (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((y : ℂ) * (y : ℂ) / 2))

/-- Exact derivative of the quadratic oscillation. -/
theorem hasDerivAt_quadraticOscillation (y : ℝ) :
    HasDerivAt quadraticOscillation
      (Complex.I * (y : ℂ) * quadraticOscillation y) y := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y :=
    Complex.ofRealCLM.hasDerivAt
  have hphase0 := (hcast.mul hcast).div_const (2 : ℂ)
  have hphase := hphase0.congr_deriv (by ring)
  have hinner := hphase.const_mul Complex.I
  have hexp := hinner.cexp
  unfold quadraticOscillation
  simpa [mul_comm, mul_left_comm, mul_assoc] using hexp

/-- The quadratic oscillation has unit norm. -/
@[simp] theorem norm_quadraticOscillation (y : ℝ) :
    ‖quadraticOscillation y‖ = 1 := by
  unfold quadraticOscillation
  rw [Complex.norm_exp]
  simp

/-- The real integration-by-parts weight, written in the native pointwise
inverse form used by Mathlib's derivative lemma. -/
def quadraticRealIBPWeight : ℝ → ℝ := id⁻¹

/-- Its derivative away from the origin. -/
def quadraticRealIBPWeightDeriv (y : ℝ) : ℝ := -1 / y ^ 2

/-- Exact derivative of the reciprocal weight away from zero. -/
theorem hasDerivAt_quadraticRealIBPWeight
    {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt quadraticRealIBPWeight (quadraticRealIBPWeightDeriv y) y := by
  simpa [quadraticRealIBPWeight, quadraticRealIBPWeightDeriv] using
    (hasDerivAt_id y).inv hy

/-- The reciprocal-weight derivative is interval integrable on a positive
finite interval. -/
theorem intervalIntegrable_quadraticRealIBPWeightDeriv
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    IntervalIntegrable quadraticRealIBPWeightDeriv volume R S := by
  have hpos : ∀ y ∈ Set.uIcc R S, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hRS] at hy
    exact hR.trans_le hy.1
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hy0 := (hpos y hy).ne'
  have hpow : ContinuousAt (fun x : ℝ => x ^ 2) y := continuousAt_id.pow 2
  have hminusOne : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) y := continuousAt_const
  have hdiv := hminusOne.div hpow (pow_ne_zero 2 hy0)
  change ContinuousWithinAt (fun z : ℝ => (-1 : ℝ) / z ^ 2) (Set.uIcc R S) y
  exact hdiv.continuousWithinAt

/-- Elementary antiderivative for the positive reciprocal-square tail. -/
theorem integral_one_div_sq
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ y in R..S, (1 / y ^ 2 : ℝ)) = 1 / R - 1 / S := by
  have hpos : ∀ y ∈ Set.uIcc R S, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hRS] at hy
    exact hR.trans_le hy.1
  have hderiv : ∀ y ∈ Set.uIcc R S,
      HasDerivAt (fun x : ℝ => -quadraticRealIBPWeight x)
        (-quadraticRealIBPWeightDeriv y) y := by
    intro y hy
    exact (hasDerivAt_quadraticRealIBPWeight (hpos y hy).ne').neg
  have hint := (intervalIntegrable_quadraticRealIBPWeightDeriv hR hRS).neg
  have hftc :
      (∫ y in R..S, -quadraticRealIBPWeightDeriv y) =
        -quadraticRealIBPWeight S - (-quadraticRealIBPWeight R) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ y in R..S, (1 / y ^ 2 : ℝ)) =
        ∫ y in R..S, -quadraticRealIBPWeightDeriv y := by
          apply intervalIntegral.integral_congr
          intro y _
          unfold quadraticRealIBPWeightDeriv
          ring
    _ = -quadraticRealIBPWeight S - (-quadraticRealIBPWeight R) := hftc
    _ = 1 / R - 1 / S := by
      simp [quadraticRealIBPWeight, one_div]
      ring

/-- The scalar-weighted Gaussian derivative simplifies to `i` times the
oscillation on a positive interval. -/
theorem quadraticRealIBPWeight_smul_deriv
    {y : ℝ} (hy : y ≠ 0) :
    quadraticRealIBPWeight y •
        (Complex.I * (y : ℂ) * quadraticOscillation y) =
      Complex.I * quadraticOscillation y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  rw [Complex.real_smul]
  change (((y⁻¹ : ℝ) : ℂ) *
      (Complex.I * (y : ℂ) * quadraticOscillation y)) =
    Complex.I * quadraticOscillation y
  rw [Complex.ofReal_inv]
  field_simp [hyC]

/-- Norm of the differentiated real IBP weight times the unit oscillation. -/
theorem norm_quadraticRealIBPWeightDeriv_smul_oscillation
    {y : ℝ} (hy : 0 < y) :
    ‖quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ = 1 / y ^ 2 := by
  rw [norm_smul, norm_quadraticOscillation, mul_one]
  unfold quadraticRealIBPWeightDeriv
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hy]

/-- One integration by parts gives the quantitative positive Fresnel tail
`2/R`, uniformly in the upper endpoint. -/
theorem norm_intervalIntegral_quadraticOscillation_le_two_div
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    ‖∫ y in R..S, quadraticOscillation y‖ ≤ 2 / R := by
  have hS : 0 < S := hR.trans_le hRS
  have hpos : ∀ y ∈ Set.uIcc R S, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hRS] at hy
    exact hR.trans_le hy.1
  have hu : ∀ y ∈ Set.uIcc R S,
      HasDerivAt quadraticRealIBPWeight (quadraticRealIBPWeightDeriv y) y := by
    intro y hy
    exact hasDerivAt_quadraticRealIBPWeight (hpos y hy).ne'
  have hv : ∀ y ∈ Set.uIcc R S,
      HasDerivAt quadraticOscillation
        (Complex.I * (y : ℂ) * quadraticOscillation y) y := by
    intro y _
    exact hasDerivAt_quadraticOscillation y
  have hu' : IntervalIntegrable quadraticRealIBPWeightDeriv volume R S :=
    intervalIntegrable_quadraticRealIBPWeightDeriv hR hRS
  have hv' : IntervalIntegrable
      (fun y : ℝ => Complex.I * (y : ℂ) * quadraticOscillation y) volume R S := by
    apply Continuous.intervalIntegrable
    unfold quadraticOscillation
    fun_prop
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (𝕜 := ℝ) (E := ℂ) hu hv hu' hv'
  have hibpNorm :
      (∫ y in R..S,
          quadraticRealIBPWeight y •
            (Complex.I * (y : ℂ) * quadraticOscillation y)) =
        quadraticRealIBPWeight S • quadraticOscillation S -
          quadraticRealIBPWeight R • quadraticOscillation R -
        ∫ y in R..S,
          quadraticRealIBPWeightDeriv y • quadraticOscillation y := by
    simpa [quadraticRealIBPWeight, quadraticRealIBPWeightDeriv] using hibp
  have hleft :
      (∫ y in R..S,
          quadraticRealIBPWeight y •
            (Complex.I * (y : ℂ) * quadraticOscillation y)) =
        Complex.I * (∫ y in R..S, quadraticOscillation y) := by
    calc
      (∫ y in R..S,
          quadraticRealIBPWeight y •
            (Complex.I * (y : ℂ) * quadraticOscillation y)) =
          ∫ y in R..S, Complex.I * quadraticOscillation y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact quadraticRealIBPWeight_smul_deriv (hpos y hy).ne'
      _ = Complex.I * (∫ y in R..S, quadraticOscillation y) := by
        rw [intervalIntegral.integral_const_mul]
  rw [hleft] at hibpNorm
  have hibpDef :
      Complex.I * (∫ y in R..S, quadraticOscillation y) =
        quadraticRealIBPWeight S • quadraticOscillation S -
          quadraticRealIBPWeight R • quadraticOscillation R -
        ∫ y in R..S,
          quadraticRealIBPWeightDeriv y • quadraticOscillation y :=
    hibpNorm
  have hrem :
      ‖∫ y in R..S,
          quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ ≤
        1 / R - 1 / S := by
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume)
      (f := fun y : ℝ => quadraticRealIBPWeightDeriv y • quadraticOscillation y) hRS
    have hnormeq :
        (∫ y in R..S,
            ‖quadraticRealIBPWeightDeriv y • quadraticOscillation y‖) =
          ∫ y in R..S, (1 / y ^ 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact norm_quadraticRealIBPWeightDeriv_smul_oscillation (hpos y hy)
    rw [hnormeq, integral_one_div_sq hR hRS] at hnorm
    exact hnorm
  have hweightR : ‖quadraticRealIBPWeight R‖ = 1 / R := by
    simp [quadraticRealIBPWeight, Real.norm_eq_abs, abs_of_pos hR]
  have hweightS : ‖quadraticRealIBPWeight S‖ = 1 / S := by
    simp [quadraticRealIBPWeight, Real.norm_eq_abs, abs_of_pos hS]
  calc
    ‖∫ y in R..S, quadraticOscillation y‖ =
        ‖Complex.I * (∫ y in R..S, quadraticOscillation y)‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖quadraticRealIBPWeight S • quadraticOscillation S -
          quadraticRealIBPWeight R • quadraticOscillation R -
          ∫ y in R..S,
            quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ := by rw [hibpDef]
    _ ≤ ‖quadraticRealIBPWeight S • quadraticOscillation S‖ +
          ‖quadraticRealIBPWeight R • quadraticOscillation R‖ +
          ‖∫ y in R..S,
            quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ := by
          calc
            _ ≤ ‖quadraticRealIBPWeight S • quadraticOscillation S -
                  quadraticRealIBPWeight R • quadraticOscillation R‖ +
                ‖∫ y in R..S,
                  quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ := norm_sub_le _ _
            _ ≤ (‖quadraticRealIBPWeight S • quadraticOscillation S‖ +
                  ‖quadraticRealIBPWeight R • quadraticOscillation R‖) +
                ‖∫ y in R..S,
                  quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ := by
                    gcongr
                    exact norm_sub_le _ _
    _ = 1 / S + 1 / R +
          ‖∫ y in R..S,
            quadraticRealIBPWeightDeriv y • quadraticOscillation y‖ := by
          rw [norm_smul, norm_smul, norm_quadraticOscillation,
            norm_quadraticOscillation, mul_one, mul_one, hweightS, hweightR]
    _ ≤ 1 / S + 1 / R + (1 / R - 1 / S) := by gcongr
    _ = 2 / R := by ring

end RightEdgeArithmeticSource
end ZetaZero
