import ZetaZero.HLPLocalModel.FactorialMajorant
import Zeta23.Chebyshev

/-!
# Uniform factorial induction for Mangoldt convolution mean squares

This file closes the induction begun in `FactorialMajorant`.  The level `k+1`
is indexed by `k`, so the natural logarithmic exponent is `2*k+1` and each
propagation step contributes a denominator `2*k+2`, which is stronger than the
`k+1` needed for a factorial.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Replace the outer factor `y` in the one-step propagation theorem by `1+y`.
This raises the logarithmic exponent by exactly two and keeps the denominator
`m+1`. -/
theorem lambdaMeanSquareExp_succ_le_of_polynomial_majorant_clean
    (k m : ℕ) {y C B : ℝ} (hy : 0 ≤ y) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmajor : ∀ u : ℝ, 0 ≤ u → u ≤ y →
      lambdaMeanSquareExp k u ≤ C * Real.exp u * (1 + u) ^ m)
    (hdegree : ((m + 1 : ℕ) : ℝ) ≤ B * (1 + y)) :
    lambdaMeanSquareExp (k + 1) y ≤
      C * (1 + Zeta23.XiPrime.KM * B) * Real.exp y *
        (1 + y) ^ (m + 2) / ((m + 1 : ℕ) : ℝ) := by
  have hstep := lambdaMeanSquareExp_succ_le_of_polynomial_majorant
    k m hy hC hmajor hdegree
  have hinner :
      0 ≤ C * Real.exp y *
        ((1 + Zeta23.XiPrime.KM * B) *
          (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ)) := by
    have hD : 0 ≤ 1 + Zeta23.XiPrime.KM * B := by
      nlinarith [Zeta23.XiPrime.KM_nonneg, hB]
    positivity
  calc
    lambdaMeanSquareExp (k + 1) y ≤
        y *
          (C * Real.exp y *
            ((1 + Zeta23.XiPrime.KM * B) *
              (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ))) := hstep
    _ ≤ (1 + y) *
          (C * Real.exp y *
            ((1 + Zeta23.XiPrime.KM * B) *
              (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hinner
    _ = C * (1 + Zeta23.XiPrime.KM * B) * Real.exp y *
        (1 + y) ^ (m + 2) / ((m + 1 : ℕ) : ℝ) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring

/-- Base level `Λ_1 = Λ`: Chebyshev's `psi(x) ≪ x` and `Λ(n) ≤ log n`
give the required square-sum estimate. -/
theorem lambdaMeanSquareExp_one_le {y : ℝ} (hy : 0 ≤ y) :
    lambdaMeanSquareExp 1 y ≤
      Zeta23.XiPrime.KM * Real.exp y * (1 + y) := by
  have hcheb := Zeta23.Cheb.sum_vonMangoldt_le (x := Real.exp y) (Real.exp_pos y).le
  have hsum :
      (∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          (ArithmeticFunction.vonMangoldt n) ^ 2) ≤
        y * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt n := by
    calc
      (∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          (ArithmeticFunction.vonMangoldt n) ^ 2) ≤
          ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
            y * ArithmeticFunction.vonMangoldt n := by
        refine Finset.sum_le_sum ?_
        intro n hn
        have hlog : Real.log n ≤ y :=
          Zeta23.XiPrime.log_le_of_mem_Ioc_floor_exp hn
        have hLam : ArithmeticFunction.vonMangoldt n ≤ y :=
          ArithmeticFunction.vonMangoldt_le_log.trans hlog
        have hLam0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
          ArithmeticFunction.vonMangoldt_nonneg
        nlinarith
      _ = y * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt n := by
        rw [Finset.mul_sum]
  calc
    lambdaMeanSquareExp 1 y =
        ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          (ArithmeticFunction.vonMangoldt n) ^ 2 := by
      simp [lambdaMeanSquareExp, lambdaMeanSquare, lambda_Icc_one_eq_Ioc_zero,
        mangoldtConvolutionPower]
    _ ≤ y * ∑ n ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
        ArithmeticFunction.vonMangoldt n := hsum
    _ ≤ y * ((Real.log 4 + 4) * Real.exp y) := by
      exact mul_le_mul_of_nonneg_left hcheb hy
    _ ≤ Zeta23.XiPrime.KM * Real.exp y * (1 + y) := by
      rw [Zeta23.XiPrime.KM]
      have hK : 0 ≤ Real.log 4 + 4 := by positivity
      have hE : 0 ≤ Real.exp y := (Real.exp_pos y).le
      nlinarith [mul_nonneg hK hE]

/-- Fixed loss per HLP convolution level after absorbing the Mertens error. -/
def factorialMajorantStepConstant : ℝ := 1 + Zeta23.XiPrime.KM * 4

lemma factorialMajorantStepConstant_nonneg : 0 ≤ factorialMajorantStepConstant := by
  unfold factorialMajorantStepConstant
  exact add_nonneg (by norm_num)
    (mul_nonneg Zeta23.XiPrime.KM_nonneg (by norm_num))

/-- Uniform factorial square-sum majorant for the Mangoldt convolution powers in
exponential coordinates.  This is the manuscript's factorial induction before
converting from `Λ_k` to the actual coefficients `α_k`. -/
theorem lambdaMeanSquareExp_factorial_majorant :
    ∀ k : ℕ, ∀ {y : ℝ}, 0 ≤ y →
      lambdaMeanSquareExp (k + 1) y ≤
        Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            k.factorial *
          Real.exp y * (1 + y) ^ (2 * k + 1) := by
  intro k
  induction k with
  | zero =>
      intro y hy
      simpa [factorialMajorantStepConstant] using lambdaMeanSquareExp_one_le hy
  | succ k ih =>
      intro y hy
      by_cases hzero : lambdaMeanSquareExp (k + 2) y = 0
      · rw [hzero]
        have hD := factorialMajorantStepConstant_nonneg
        have hcoeff :
            0 ≤ Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ (k + 1) /
              (k + 1).factorial :=
          div_nonneg
            (mul_nonneg Zeta23.XiPrime.KM_nonneg (pow_nonneg hD _))
            (by positivity)
        exact mul_nonneg
          (mul_nonneg hcoeff (Real.exp_pos y).le)
          (pow_nonneg (by linarith) _)
      · let C : ℝ :=
          Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k / k.factorial
        have hC : 0 ≤ C := by
          dsimp [C]
          exact div_nonneg
            (mul_nonneg Zeta23.XiPrime.KM_nonneg
              (pow_nonneg factorialMajorantStepConstant_nonneg k))
            (by positivity)
        have hmajor : ∀ u : ℝ, 0 ≤ u → u ≤ y →
            lambdaMeanSquareExp (k + 1) u ≤
              C * Real.exp u * (1 + u) ^ (2 * k + 1) := by
          intro u hu huy
          simpa [C] using ih hu
        have hdegree_big := factorialDegree_control_of_ne_zero (k + 2) hzero
        have hdegree :
            ((((2 * k + 1) + 1 : ℕ) : ℝ)) ≤ 4 * (1 + y) := by
          push_cast at hdegree_big ⊢
          nlinarith
        have hstep := lambdaMeanSquareExp_succ_le_of_polynomial_majorant_clean
          (k + 1) (2 * k + 1) hy hC (by norm_num : (0 : ℝ) ≤ 4)
          hmajor hdegree
        have hnum :
            0 ≤ C * factorialMajorantStepConstant * Real.exp y *
              (1 + y) ^ (2 * k + 3) := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg hC factorialMajorantStepConstant_nonneg)
              (Real.exp_pos y).le)
            (pow_nonneg (by linarith) _)
        have hden :
            (((k + 1 : ℕ) : ℝ)) ≤ ((((2 * k + 1) + 1 : ℕ) : ℝ)) := by
          exact_mod_cast (show k + 1 ≤ (2 * k + 1) + 1 by omega)
        calc
          lambdaMeanSquareExp (k + 2) y ≤
              C * factorialMajorantStepConstant * Real.exp y *
                (1 + y) ^ (2 * k + 3) /
                  ((((2 * k + 1) + 1 : ℕ) : ℝ)) := by
            simpa [factorialMajorantStepConstant, C] using hstep
          _ ≤ C * factorialMajorantStepConstant * Real.exp y *
                (1 + y) ^ (2 * k + 3) / (((k + 1 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_left hnum (by positivity) hden
          _ = Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ (k + 1) /
                (k + 1).factorial *
              Real.exp y * (1 + y) ^ (2 * (k + 1) + 1) := by
            dsimp [C]
            rw [pow_succ, Nat.factorial_succ]
            push_cast
            field_simp
            ring

end HLPLocalModel
end ZetaZero
