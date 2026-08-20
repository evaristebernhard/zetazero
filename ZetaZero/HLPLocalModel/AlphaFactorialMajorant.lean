import ZetaZero.HLPLocalModel.MeanSquareRecurrence
import ZetaZero.HLPLocalModel.AlphaDerivativeIdentity
import Zeta23.XiPrime.Coeff.Basic

/-!
# Factorial majorant for the actual HLP coefficients

`FactorialInduction` controls the Mangoldt convolution powers `Λ^(k+1)`.
The manuscript, however, uses the coefficients of `P^k Q`.  These are exactly
the vendored `lamLogConv k`, so `XiPrime.lamLogConv_le` transfers the factorial
bound to the actual HLP hierarchy without introducing a new asymptotic input.

The final lemmas also use the exact derivative identity
`α_{k+1}(n) = log(n)/(k+1) Λ_{k+1}(n)` to retain the sharper square factor
`1/(k+1)^2`.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Our coefficient `Λ(n) log n` is the same arithmetic function as the
vendored Xi-prime coefficient `lamLog`. -/
theorem mangoldtLogCoefficient_eq_lamLog :
    mangoldtLogCoefficient = Zeta23.XiPrime.lamLog := by
  ext n
  simp [mangoldtLogCoefficient, Zeta23.XiPrime.lamLog_apply]

/-- The HLP coefficient level `P^k Q` agrees with the existing Xi-prime
`lamLogConv k` hierarchy. -/
theorem hlpAlphaSucc_eq_lamLogConv (k : ℕ) :
    hlpAlphaSucc k = Zeta23.XiPrime.lamLogConv k := by
  rw [hlpAlphaSucc, mangoldtConvolutionPower,
    Zeta23.XiPrime.lamLogConv_eq, mangoldtLogCoefficient_eq_lamLog]
  exact mul_comm _ _

/-- HLP coefficients are nonnegative. -/
theorem hlpAlphaSucc_nonneg (k n : ℕ) : 0 ≤ hlpAlphaSucc k n := by
  rw [hlpAlphaSucc_eq_lamLogConv]
  exact Zeta23.XiPrime.lamLogConv_nonneg k n

/-- Pointwise comparison of the actual HLP level with the next Mangoldt
convolution power:

`alpha_{k+1}(n) <= log(n) * Lambda_{k+1}(n)`.

The sharper exact factor `1/(k+1)` is proved separately in
`AlphaDerivativeIdentity`; this weaker form is retained because it is useful as
a monotone comparison without division. -/
theorem hlpAlphaSucc_le_log_mangoldtPower (k n : ℕ) :
    hlpAlphaSucc k n ≤
      Real.log n * mangoldtConvolutionPower (k + 1) n := by
  rw [hlpAlphaSucc_eq_lamLogConv, mangoldtConvolutionPower]
  exact Zeta23.XiPrime.lamLogConv_le k n

/-- Mean square of `P^k Q` up to the exponential cutoff `floor(exp y)`. -/
def hlpMeanSquareExp (k : ℕ) (y : ℝ) : ℝ :=
  hlpMeanSquare k ⌊Real.exp y⌋₊

/-- The actual HLP mean square is bounded by `y^2` times the next Mangoldt
mean square. -/
theorem hlpMeanSquareExp_le_log_sq_lambda
    (k : ℕ) {y : ℝ} :
    hlpMeanSquareExp k y ≤ y ^ 2 * lambdaMeanSquareExp (k + 1) y := by
  unfold hlpMeanSquareExp lambdaMeanSquareExp
  rw [hlpMeanSquare_eq_sum_Ioc, lambdaMeanSquare, lambda_Icc_one_eq_Ioc_zero]
  calc
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, (hlpAlphaSucc k n) ^ 2) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          y ^ 2 * (mangoldtConvolutionPower (k + 1) n) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hlog : Real.log n ≤ y :=
        Zeta23.XiPrime.log_le_of_mem_Ioc_floor_exp hn
      have hlam0 : 0 ≤ mangoldtConvolutionPower (k + 1) n := by
        simpa [mangoldtConvolutionPower] using
          Zeta23.XiPrime.lamPow_nonneg (k + 1) n
      have halpha0 : 0 ≤ hlpAlphaSucc k n := hlpAlphaSucc_nonneg k n
      have halpha : hlpAlphaSucc k n ≤
          y * mangoldtConvolutionPower (k + 1) n := by
        calc
          hlpAlphaSucc k n ≤
              Real.log n * mangoldtConvolutionPower (k + 1) n :=
            hlpAlphaSucc_le_log_mangoldtPower k n
          _ ≤ y * mangoldtConvolutionPower (k + 1) n :=
            mul_le_mul_of_nonneg_right hlog hlam0
      nlinarith
    _ = y ^ 2 *
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          (mangoldtConvolutionPower (k + 1) n) ^ 2 := by
      rw [Finset.mul_sum]

/-- Uniform factorial square-sum majorant for the actual HLP coefficients
`P^k Q`.  In the manuscript's level convention this is `alpha_{k+1}`.

The exponent `2k+3` is exactly `2(k+1)+1`. -/
theorem hlpMeanSquareExp_factorial_majorant
    (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    hlpMeanSquareExp k y ≤
      Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          k.factorial *
        Real.exp y * (1 + y) ^ (2 * k + 3) := by
  have halpha := hlpMeanSquareExp_le_log_sq_lambda k (y := y)
  have hlambda := lambdaMeanSquareExp_factorial_majorant k hy
  have hcoeff :
      0 ≤ Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
        k.factorial := by
    exact div_nonneg
      (mul_nonneg Zeta23.XiPrime.KM_nonneg
        (pow_nonneg factorialMajorantStepConstant_nonneg k))
      (by positivity)
  have hexp : 0 ≤ Real.exp y := (Real.exp_pos y).le
  have hbase : 0 ≤ 1 + y := by linarith
  have hybase : y ^ 2 ≤ (1 + y) ^ 2 := by nlinarith
  calc
    hlpMeanSquareExp k y ≤ y ^ 2 * lambdaMeanSquareExp (k + 1) y := halpha
    _ ≤ y ^ 2 *
        (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            k.factorial *
          Real.exp y * (1 + y) ^ (2 * k + 1)) := by
      exact mul_le_mul_of_nonneg_left hlambda (sq_nonneg y)
    _ ≤ (1 + y) ^ 2 *
        (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            k.factorial *
          Real.exp y * (1 + y) ^ (2 * k + 1)) := by
      apply mul_le_mul_of_nonneg_right hybase
      positivity
    _ = Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          k.factorial *
        Real.exp y * (1 + y) ^ (2 * k + 3) := by
      rw [show 2 * k + 3 = 2 + (2 * k + 1) by omega, pow_add]
      ring

/-- Exact square-sum transfer retaining the derivative factor `1/(k+1)^2`. -/
theorem hlpMeanSquareExp_le_log_div_sq_lambda
    (k : ℕ) {y : ℝ} :
    hlpMeanSquareExp k y ≤
      (y / (((k + 1 : ℕ) : ℝ))) ^ 2 * lambdaMeanSquareExp (k + 1) y := by
  have hkpos : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  unfold hlpMeanSquareExp lambdaMeanSquareExp
  rw [hlpMeanSquare_eq_sum_Ioc, lambdaMeanSquare, lambda_Icc_one_eq_Ioc_zero]
  calc
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, (hlpAlphaSucc k n) ^ 2) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
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
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          (mangoldtConvolutionPower (k + 1) n) ^ 2 := by
      rw [Finset.mul_sum]

end HLPLocalModel
end ZetaZero
