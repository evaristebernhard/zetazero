import ZetaZero.HLPLocalModel.WeightedCauchy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Mean-square recurrence for Mangoldt convolution powers

This module formalizes the exact finite recurrence used in the manuscript's
factorial-majorant argument.  The induction is run first on

`S_k(X) = ∑_{1 ≤ n ≤ X} Λ_k(n)^2`,

where `Λ_k` is the `k`-fold Dirichlet convolution of the von Mangoldt function.
No asymptotic estimate is used here: the result stops at the exact
Mangoldt-weighted shortened-range recurrence.
-/

open Finset Nat
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Finite mean square of the `k`-fold Mangoldt convolution on `1 ≤ n ≤ X`. -/
def lambdaMeanSquare (k X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, (mangoldtConvolutionPower k n) ^ 2

/-- Package the square of a Mangoldt convolution level as an arithmetic function. -/
def lambdaSquare (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (mangoldtConvolutionPower k n) ^ 2, by simp⟩

@[simp] theorem lambdaSquare_apply (k n : ℕ) :
    lambdaSquare k n = (mangoldtConvolutionPower k n) ^ 2 := rfl

/-- On natural numbers, `1 ≤ n ≤ X` is the same interval as `0 < n ≤ X`. -/
theorem lambda_Icc_one_eq_Ioc_zero (X : ℕ) :
    Finset.Icc 1 X = Finset.Ioc 0 X := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- Below the intrinsic support threshold `2^k`, the finite mean square vanishes. -/
theorem lambdaMeanSquare_eq_zero_of_lt {k X : ℕ} (hX : X < 2 ^ k) :
    lambdaMeanSquare k X = 0 := by
  unfold lambdaMeanSquare
  apply Finset.sum_eq_zero
  intro n hn
  have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
  have hnlt : n < 2 ^ k := lt_of_le_of_lt hnX hX
  simp [mangoldtConvolutionPower_eq_zero_of_lt hnlt]

/-- If the `k`th Mangoldt mean square is nonzero, the summation range has already
reached the natural convolution support `2^k`. -/
theorem pow_le_of_lambdaMeanSquare_ne_zero {k X : ℕ}
    (hS : lambdaMeanSquare k X ≠ 0) :
    2 ^ k ≤ X := by
  by_contra hnot
  have hX : X < 2 ^ k := Nat.lt_of_not_ge hnot
  exact hS (lambdaMeanSquare_eq_zero_of_lt hX)

/-- The Mangoldt convolution recurrence with the new von Mangoldt factor placed
on the first divisor coordinate. -/
theorem mangoldtConvolutionPower_succ_apply_first (k n : ℕ) :
    mangoldtConvolutionPower (k + 1) n =
      ∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 * mangoldtConvolutionPower k x.2 := by
  have hrec : mangoldtConvolutionPower (k + 1) =
      ArithmeticFunction.vonMangoldt * mangoldtConvolutionPower k := by
    rw [mangoldtConvolutionPower_succ, mul_comm]
  rw [hrec, ArithmeticFunction.mul_apply]

/-- Pointwise weighted Cauchy--Schwarz for one `Λ_k → Λ_{k+1}` step. -/
theorem mangoldtConvolutionPower_succ_sq_le_log_weighted (k n : ℕ) :
    (mangoldtConvolutionPower (k + 1) n) ^ 2 ≤
      Real.log n *
        ∑ x ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt x.1 *
            (mangoldtConvolutionPower k x.2) ^ 2 := by
  rw [mangoldtConvolutionPower_succ_apply_first]
  calc
    (∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 * mangoldtConvolutionPower k x.2) ^ 2 ≤
        (∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.1) *
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 *
              (mangoldtConvolutionPower k x.2) ^ 2 := by
      exact weighted_sum_sq_le n.divisorsAntidiagonal
        (fun x => ArithmeticFunction.vonMangoldt x.1)
        (fun x => mangoldtConvolutionPower k x.2)
        (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log n *
        ∑ x ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt x.1 *
            (mangoldtConvolutionPower k x.2) ^ 2 := by
      rw [sum_vonMangoldt_first_divisorsAntidiagonal]

/-- Sum the pointwise recurrence over the finite interval `1 ≤ n ≤ X`. -/
theorem lambdaMeanSquare_succ_le_log_antidiagonal (k X : ℕ) :
    lambdaMeanSquare (k + 1) X ≤
      ∑ n ∈ Finset.Icc 1 X,
        Real.log n *
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 *
              (mangoldtConvolutionPower k x.2) ^ 2 := by
  unfold lambdaMeanSquare
  exact Finset.sum_le_sum fun n hn =>
    mangoldtConvolutionPower_succ_sq_le_log_weighted k n

/-- Replace the outer logarithm by the uniform bound `log X`. -/
theorem lambdaMeanSquare_succ_le_logX_antidiagonal (k X : ℕ) :
    lambdaMeanSquare (k + 1) X ≤
      Real.log X *
        ∑ n ∈ Finset.Icc 1 X,
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 *
              (mangoldtConvolutionPower k x.2) ^ 2 := by
  calc
    lambdaMeanSquare (k + 1) X ≤
        ∑ n ∈ Finset.Icc 1 X,
          Real.log n *
            ∑ x ∈ n.divisorsAntidiagonal,
              ArithmeticFunction.vonMangoldt x.1 *
                (mangoldtConvolutionPower k x.2) ^ 2 :=
      lambdaMeanSquare_succ_le_log_antidiagonal k X
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
        Real.log X *
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 *
              (mangoldtConvolutionPower k x.2) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hXpos : (0 : ℝ) < (X : ℝ) := by
        exact lt_of_lt_of_le hnpos (by exact_mod_cast hnX)
      have hlog : Real.log n ≤ Real.log X := by
        exact Real.strictMonoOn_log.monotoneOn hnpos hXpos (by exact_mod_cast hnX)
      have hnonneg :
          0 ≤ ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 *
              (mangoldtConvolutionPower k x.2) ^ 2 := by
        refine Finset.sum_nonneg ?_
        intro x hx
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hlog hnonneg
    _ = Real.log X *
        ∑ n ∈ Finset.Icc 1 X,
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 *
              (mangoldtConvolutionPower k x.2) ^ 2 := by
      rw [Finset.mul_sum]

/-- Exact Dirichlet-hyperbola rearrangement of the finite antidiagonal sum. -/
theorem lambda_antidiagonal_sum_eq_mangoldt_meanSquare (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
      ∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 *
          (mangoldtConvolutionPower k x.2) ^ 2) =
      ∑ a ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt a * lambdaMeanSquare k (X / a) := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    ArithmeticFunction.vonMangoldt (lambdaSquare k) X
  simpa [ArithmeticFunction.mul_apply, lambdaSquare_apply, lambdaMeanSquare,
    lambda_Icc_one_eq_Ioc_zero] using h

/-- The exact global recurrence used for the factorial-majorant induction:

`S_{k+1}(X) ≤ log X * ∑_{d≤X} Λ(d) S_k(X/d)`.
-/
theorem lambdaMeanSquare_succ_le_logX_mangoldt (k X : ℕ) :
    lambdaMeanSquare (k + 1) X ≤
      Real.log X *
        ∑ a ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt a * lambdaMeanSquare k (X / a) := by
  calc
    lambdaMeanSquare (k + 1) X ≤
        Real.log X *
          ∑ n ∈ Finset.Icc 1 X,
            ∑ x ∈ n.divisorsAntidiagonal,
              ArithmeticFunction.vonMangoldt x.1 *
                (mangoldtConvolutionPower k x.2) ^ 2 :=
      lambdaMeanSquare_succ_le_logX_antidiagonal k X
    _ = Real.log X *
        ∑ a ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt a * lambdaMeanSquare k (X / a) := by
      rw [lambda_antidiagonal_sum_eq_mangoldt_meanSquare]

end HLPLocalModel
end ZetaZero
