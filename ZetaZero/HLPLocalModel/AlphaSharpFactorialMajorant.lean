import ZetaZero.HLPLocalModel.FactorialInduction
import ZetaZero.HLPLocalModel.AlphaDerivativeIdentity

/-!
# Sharpened factorial majorant for the actual HLP coefficients

This module is deliberately independent of `AlphaFactorialMajorant.lean`, so it
can be developed without touching the parallel workstream using that file.  It
retains the exact derivative factor `1/(k+1)` before squaring.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Exponential-cutoff square sum of the actual level `α_{k+1}`. -/
def hlpAlphaSharpMeanSquareExp (k : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, (hlpAlphaSucc k n) ^ 2

/-- Exact transfer from the actual HLP coefficients to the next Mangoldt
convolution mean square, retaining `1/(k+1)^2`. -/
theorem hlpAlphaSharpMeanSquareExp_le_lambda
    (k : ℕ) {y : ℝ} :
    hlpAlphaSharpMeanSquareExp k y ≤
      (y / (((k + 1 : ℕ) : ℝ))) ^ 2 * lambdaMeanSquareExp (k + 1) y := by
  have hkpos : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  calc
    hlpAlphaSharpMeanSquareExp k y =
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, (hlpAlphaSucc k n) ^ 2 := rfl
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
        (y / (((k + 1 : ℕ) : ℝ))) ^ 2 *
          (mangoldtConvolutionPower (k + 1) n) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hlog : Real.log n ≤ y :=
        Zeta23.XiPrime.log_le_of_mem_Ioc_floor_exp hn
      have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have hfrac0 : 0 ≤ Real.log n / (((k + 1 : ℕ) : ℝ)) :=
        div_nonneg hlog0 hkpos.le
      have hfrac :
          Real.log n / (((k + 1 : ℕ) : ℝ)) ≤
            y / (((k + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hlog hkpos.le
      have hsq :
          (Real.log n / (((k + 1 : ℕ) : ℝ))) ^ 2 ≤
            (y / (((k + 1 : ℕ) : ℝ))) ^ 2 := by
        nlinarith
      rw [hlpAlphaSucc_eq_log_div_mangoldtPower]
      calc
        (Real.log n / (((k + 1 : ℕ) : ℝ)) *
            mangoldtConvolutionPower (k + 1) n) ^ 2 =
            (Real.log n / (((k + 1 : ℕ) : ℝ))) ^ 2 *
              (mangoldtConvolutionPower (k + 1) n) ^ 2 := by ring
        _ ≤ (y / (((k + 1 : ℕ) : ℝ))) ^ 2 *
              (mangoldtConvolutionPower (k + 1) n) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = (y / (((k + 1 : ℕ) : ℝ))) ^ 2 *
        lambdaMeanSquareExp (k + 1) y := by
      unfold lambdaMeanSquareExp lambdaMeanSquare
      rw [lambda_Icc_one_eq_Ioc_zero, Finset.mul_sum]

/-- Scalar inequality that converts the squared derivative denominator into one
factorial step. -/
theorem log_div_square_le_factorial_gain
    (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (y / (((k + 1 : ℕ) : ℝ))) ^ 2 ≤
      (1 + y) ^ 2 / (((k + 1 : ℕ) : ℝ)) := by
  let d : ℝ := (((k + 1 : ℕ) : ℝ))
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hd1 : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hy2 : y ^ 2 ≤ (1 + y) ^ 2 := by nlinarith
  have hd2 : d ≤ d ^ 2 := by nlinarith
  rw [show (((k + 1 : ℕ) : ℝ)) = d by rfl, div_pow,
    div_le_div_iff₀ (sq_pos_of_pos hdpos) hdpos]
  calc
    y ^ 2 * d ≤ (1 + y) ^ 2 * d :=
      mul_le_mul_of_nonneg_right hy2 hdpos.le
    _ ≤ (1 + y) ^ 2 * d ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)

/-- Sharpened factorial square-sum majorant for `α_{k+1}`.

Compared with the Mangoldt-power bound, the exact derivative identity contributes
one additional factorial denominator. -/
theorem hlpAlphaSharpMeanSquareExp_factorial_majorant
    (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    hlpAlphaSharpMeanSquareExp k y ≤
      Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          (k + 1).factorial *
        Real.exp y * (1 + y) ^ (2 * k + 3) := by
  have halpha := hlpAlphaSharpMeanSquareExp_le_lambda k (y := y)
  have hlambda := lambdaMeanSquareExp_factorial_majorant k hy
  have hscalar := log_div_square_le_factorial_gain k hy
  have hfac0 : 0 ≤ (y / (((k + 1 : ℕ) : ℝ))) ^ 2 := sq_nonneg _
  have hbound0 :
      0 ≤ Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          k.factorial * Real.exp y * (1 + y) ^ (2 * k + 1) := by
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg
          (mul_nonneg Zeta23.XiPrime.KM_nonneg
            (pow_nonneg factorialMajorantStepConstant_nonneg k))
          (by positivity))
        (Real.exp_pos y).le)
      (pow_nonneg (by linarith) _)
  calc
    hlpAlphaSharpMeanSquareExp k y ≤
        (y / (((k + 1 : ℕ) : ℝ))) ^ 2 *
          lambdaMeanSquareExp (k + 1) y := halpha
    _ ≤ (y / (((k + 1 : ℕ) : ℝ))) ^ 2 *
        (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            k.factorial * Real.exp y * (1 + y) ^ (2 * k + 1)) := by
      exact mul_le_mul_of_nonneg_left hlambda hfac0
    _ ≤ ((1 + y) ^ 2 / (((k + 1 : ℕ) : ℝ))) *
        (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            k.factorial * Real.exp y * (1 + y) ^ (2 * k + 1)) := by
      exact mul_le_mul_of_nonneg_right hscalar hbound0
    _ = Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          (k + 1).factorial *
        Real.exp y * (1 + y) ^ (2 * k + 3) := by
      rw [Nat.factorial_succ,
        show 2 * k + 3 = 2 + (2 * k + 1) by omega, pow_add]
      push_cast
      field_simp
      ring

end HLPLocalModel
end ZetaZero
