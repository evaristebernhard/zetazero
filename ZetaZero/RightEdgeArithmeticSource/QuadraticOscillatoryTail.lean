import ZetaZero.RightEdgeArithmeticSource.StationaryOscillationControl
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Tail bound for the quadratic oscillatory model

The quadratic model `exp(i y^2 / 2)` is not Lebesgue integrable on the whole
line.  Its truncated integrals are nevertheless Cauchy by one integration by
parts.  This file proves the finite tail estimate needed for a later Fresnel
limit, without pretending absolute integrability.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The universal quadratic oscillation, written directly as a complex
polynomial in the real variable. -/
def quadraticOscillation (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * (y : ℂ) ^ 2 / 2)

/-- The integration-by-parts weight `1/(i y) = -i/y`. -/
def quadraticIBPWeight (y : ℝ) : ℂ :=
  -Complex.I / (y : ℂ)

/-- Exact derivative of the quadratic oscillation. -/
theorem hasDerivAt_quadraticOscillation (y : ℝ) :
    HasDerivAt quadraticOscillation
      (Complex.I * (y : ℂ) * quadraticOscillation y) y := by
  have hinnerC :
      HasDerivAt (fun z : ℂ => Complex.I * z ^ 2 / 2)
        (Complex.I * (y : ℂ)) (y : ℂ) := by
    convert (((hasDerivAt_id (y : ℂ)).pow 2).const_mul Complex.I).div_const 2 using 1 <;>
      ring
  have hinner :
      HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ) ^ 2 / 2)
        (Complex.I * (y : ℂ)) y := by
    simpa using hinnerC.comp_ofReal
  have hexp := (Complex.hasDerivAt_exp _).comp y hinner
  simpa [quadraticOscillation, mul_assoc] using hexp

/-- Exact derivative of the integration-by-parts weight away from zero. -/
theorem hasDerivAt_quadraticIBPWeight
    {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt quadraticIBPWeight
      (Complex.I / (y : ℂ) ^ 2) y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hC :
      HasDerivAt (fun z : ℂ => -Complex.I / z)
        (Complex.I / (y : ℂ) ^ 2) (y : ℂ) := by
    convert (hasDerivAt_const (y : ℂ) (-Complex.I)).div (hasDerivAt_id (y : ℂ)) hyC using 1 <;>
      ring
  simpa [quadraticIBPWeight] using hC.comp_ofReal

/-- The weighted derivative of the quadratic oscillation collapses back to the
oscillation itself. -/
theorem quadraticIBPWeight_mul_deriv
    {y : ℝ} (hy : y ≠ 0) :
    quadraticIBPWeight y *
        (Complex.I * (y : ℂ) * quadraticOscillation y) =
      quadraticOscillation y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  unfold quadraticIBPWeight
  field_simp [hyC]
  ring

/-- Norm of the IBP boundary weight on the positive axis. -/
theorem norm_quadraticIBPWeight
    {y : ℝ} (hy : 0 < y) :
    ‖quadraticIBPWeight y‖ = 1 / y := by
  unfold quadraticIBPWeight
  rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hy]
  norm_num

/-- Norm of the differentiated IBP weight times the unit-modulus oscillation. -/
theorem norm_quadraticIBPWeight_deriv_mul_oscillation
    {y : ℝ} (hy : 0 < y) :
    ‖(Complex.I / (y : ℂ) ^ 2) * quadraticOscillation y‖ = 1 / y ^ 2 := by
  rw [norm_mul, norm_div, Complex.norm_I, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy]
  have hosc : ‖quadraticOscillation y‖ = 1 := by
    unfold quadraticOscillation
    rw [Complex.norm_exp]
    simp
  rw [hosc]
  norm_num

/-- Exact integration-by-parts identity on a positive finite interval. -/
theorem integral_quadraticOscillation_eq_boundary_sub_remainder
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ y in R..S, quadraticOscillation y) =
      quadraticIBPWeight S * quadraticOscillation S -
        quadraticIBPWeight R * quadraticOscillation R -
      ∫ y in R..S,
        (Complex.I / (y : ℂ) ^ 2) * quadraticOscillation y := by
  have hpos : ∀ y ∈ Set.uIcc R S, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hRS] at hy
    exact hR.trans_le hy.1
  have hu : ∀ y ∈ Set.uIcc R S,
      HasDerivAt quadraticIBPWeight (Complex.I / (y : ℂ) ^ 2) y := by
    intro y hy
    exact hasDerivAt_quadraticIBPWeight (hpos y hy).ne'
  have hv : ∀ y ∈ Set.uIcc R S,
      HasDerivAt quadraticOscillation
        (Complex.I * (y : ℂ) * quadraticOscillation y) y := by
    intro y _
    exact hasDerivAt_quadraticOscillation y
  have hu' : IntervalIntegrable
      (fun y : ℝ => Complex.I / (y : ℂ) ^ 2) volume R S := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    have hy0 : y ≠ 0 := (hpos y hy).ne'
    fun_prop
  have hv' : IntervalIntegrable
      (fun y : ℝ => Complex.I * (y : ℂ) * quadraticOscillation y) volume R S := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hleft :
      (∫ y in R..S,
          quadraticIBPWeight y *
            (Complex.I * (y : ℂ) * quadraticOscillation y)) =
        ∫ y in R..S, quadraticOscillation y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hypos : 0 < y := by
      rw [Set.uIoc_of_le hRS] at hy
      exact hR.trans_le hy.1.le
    exact quadraticIBPWeight_mul_deriv hypos.ne'
  rw [hleft] at hibp
  exact hibp

end RightEdgeArithmeticSource
end ZetaZero
