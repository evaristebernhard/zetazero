import ZetaZero.HLPLocalModel.LambdaMeanSquareRecurrence
import ZetaZero.HLPLocalModel.WeightedChebyshev
import Zeta23.XiPrime.Coeff.PowerSums
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Factorial-majorant propagation in exponential coordinates

The manuscript induction is most naturally expressed at the cutoff
`X = floor (exp y)`.  In these coordinates the exact identity

`floor (exp y) / d = floor (exp (y - log d))`

preserves the shortened logarithmic range after one Dirichlet-convolution step.
This file turns the finite recurrence for `lambdaMeanSquare` into an exponential-
coordinate recurrence and couples it to the weighted Chebyshev--Mertens kernel.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Mean square of the `k`-fold Mangoldt convolution up to `floor (exp y)`. -/
def lambdaMeanSquareExp (k : ℕ) (y : ℝ) : ℝ :=
  lambdaMeanSquare k ⌊Real.exp y⌋₊

/-- Every finite Mangoldt mean square is nonnegative. -/
theorem lambdaMeanSquare_nonneg (k X : ℕ) : 0 ≤ lambdaMeanSquare k X := by
  unfold lambdaMeanSquare
  exact Finset.sum_nonneg fun n hn => sq_nonneg _

/-- The support inequality `2^k ≤ floor(exp y)` forces the convolution level to
be at most twice the logarithmic range.  The deliberately loose constant `2`
uses only the elementary numerical lower bound `log 2 > 1/2`. -/
theorem level_le_two_mul_y_of_pow_le_floor_exp
    {k : ℕ} {y : ℝ} (hpow : 2 ^ k ≤ ⌊Real.exp y⌋₊) :
    (k : ℝ) ≤ 2 * y := by
  have hpowreal : (2 : ℝ) ^ k ≤ Real.exp y := by
    calc
      (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by norm_num
      _ ≤ (⌊Real.exp y⌋₊ : ℝ) := by exact_mod_cast hpow
      _ ≤ Real.exp y := Nat.floor_le (Real.exp_pos y).le
  have hlog : Real.log ((2 : ℝ) ^ k) ≤ y :=
    (Real.log_le_iff_le_exp (pow_pos (by norm_num) k)).2 hpowreal
  rw [Real.log_pow] at hlog
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hhalfk : (k : ℝ) / 2 ≤ (k : ℝ) * Real.log 2 := by
    nlinarith
  linarith

/-- Consequently the manuscript degree `m = 2k-1` satisfies the fixed degree
condition with `B=4`. -/
theorem twice_level_le_four_one_add_y_of_pow_le_floor_exp
    {k : ℕ} {y : ℝ} (hpow : 2 ^ k ≤ ⌊Real.exp y⌋₊) :
    (2 * k : ℝ) ≤ 4 * (1 + y) := by
  have hk := level_le_two_mul_y_of_pow_le_floor_exp hpow
  have hy : 0 ≤ y := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  linarith

/-- Exponential-coordinate form of the exact global recurrence.

The outer `log floor(exp y)` is bounded by `y`, while the shortened natural
cutoff is rewritten exactly as `floor(exp (y - log d))`. -/
theorem lambdaMeanSquareExp_succ_le (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    lambdaMeanSquareExp (k + 1) y ≤
      y *
        ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquareExp k (y - Real.log d) := by
  have hrec :=
    lambdaMeanSquare_succ_le_logX_mangoldt k ⌊Real.exp y⌋₊
  rw [lambda_Icc_one_eq_Ioc_zero] at hrec
  have hX1 : 1 ≤ ⌊Real.exp y⌋₊ := Zeta23.XiPrime.one_le_floor_exp hy
  have hXpos : (0 : ℝ) < (⌊Real.exp y⌋₊ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX1)
  have hlogX : Real.log (⌊Real.exp y⌋₊ : ℝ) ≤ y := by
    exact (Real.log_le_iff_le_exp hXpos).2 (Nat.floor_le (Real.exp_pos y).le)
  have hsum_nonneg :
      0 ≤ ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
        ArithmeticFunction.vonMangoldt d *
          lambdaMeanSquare k (⌊Real.exp y⌋₊ / d) := by
    refine Finset.sum_nonneg ?_
    intro d hd
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (lambdaMeanSquare_nonneg k (⌊Real.exp y⌋₊ / d))
  calc
    lambdaMeanSquareExp (k + 1) y =
        lambdaMeanSquare (k + 1) ⌊Real.exp y⌋₊ := rfl
    _ ≤ Real.log (⌊Real.exp y⌋₊ : ℝ) *
        ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquare k (⌊Real.exp y⌋₊ / d) := hrec
    _ ≤ y *
        ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquare k (⌊Real.exp y⌋₊ / d) :=
      mul_le_mul_of_nonneg_right hlogX hsum_nonneg
    _ = y *
        ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquareExp k (y - Real.log d) := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
      unfold lambdaMeanSquareExp
      rw [← Zeta23.XiPrime.floor_exp_div y hd0]

/-- One factorial-majorant propagation step.

Assume the previous level is bounded on every shortened logarithmic range by
`C * exp(u) * (1+u)^m`.  The exact recurrence and the weighted Mertens kernel
then produce the crucial `1/(m+1)` gain. -/
theorem lambdaMeanSquareExp_succ_le_of_polynomial_majorant
    (k m : ℕ) {y C B : ℝ} (hy : 0 ≤ y) (hC : 0 ≤ C)
    (hmajor : ∀ u : ℝ, 0 ≤ u → u ≤ y →
      lambdaMeanSquareExp k u ≤ C * Real.exp u * (1 + u) ^ m)
    (hdegree : ((m + 1 : ℕ) : ℝ) ≤ B * (1 + y)) :
    lambdaMeanSquareExp (k + 1) y ≤
      y *
        (C * Real.exp y *
          ((1 + Zeta23.XiPrime.KM * B) *
            (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ))) := by
  have hrec := lambdaMeanSquareExp_succ_le k hy
  have hsum :
      (∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquareExp k (y - Real.log d)) ≤
        C * Real.exp y * weightedMangoldtKernel m y := by
    calc
      (∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquareExp k (y - Real.log d)) ≤
          ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
            ArithmeticFunction.vonMangoldt d *
              (C * Real.exp (y - Real.log d) *
                (1 + (y - Real.log d)) ^ m) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hlog : Real.log d ≤ y :=
          Zeta23.XiPrime.log_le_of_mem_Ioc_floor_exp hd
        have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
        apply mul_le_mul_of_nonneg_left
          (hmajor (y - Real.log d) (by linarith) (by linarith))
          ArithmeticFunction.vonMangoldt_nonneg
      _ = C * Real.exp y * weightedMangoldtKernel m y := by
        unfold weightedMangoldtKernel
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
        have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
        rw [Real.exp_sub, Real.exp_log hdreal]
        ring
  have hkernel := weightedMangoldtKernel_le_degree_control m hy hdegree
  have hCexp : 0 ≤ C * Real.exp y :=
    mul_nonneg hC (Real.exp_pos y).le
  have hsum' :
      (∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d *
            lambdaMeanSquareExp k (y - Real.log d)) ≤
        C * Real.exp y *
          ((1 + Zeta23.XiPrime.KM * B) *
            (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ)) := by
    exact hsum.trans (mul_le_mul_of_nonneg_left hkernel hCexp)
  exact hrec.trans (mul_le_mul_of_nonneg_left hsum' hy)

/-- The intrinsic support `2^k` converts the HLP level into the degree condition
needed by the weighted Chebyshev kernel.  The deliberately loose constant `4`
keeps the statement elementary: nonvanishing at logarithmic range `y` forces
`k / 2 ≤ y`, hence `2k ≤ 4(1+y)`. -/
theorem factorialDegree_control_of_ne_zero
    (k : ℕ) {y : ℝ}
    (hS : lambdaMeanSquareExp k y ≠ 0) :
    (((2 * k : ℕ) : ℝ)) ≤ 4 * (1 + y) := by
  have hpow : 2 ^ k ≤ ⌊Real.exp y⌋₊ := by
    apply pow_le_of_lambdaMeanSquare_ne_zero
    simpa [lambdaMeanSquareExp] using hS
  have hcast : (((2 ^ k : ℕ) : ℝ)) ≤ Real.exp y := by
    calc
      (((2 ^ k : ℕ) : ℝ)) ≤ (⌊Real.exp y⌋₊ : ℝ) := by
        exact_mod_cast hpow
      _ ≤ Real.exp y := Nat.floor_le (Real.exp_pos y).le
  have hpowpos : (0 : ℝ) < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hlogpow : Real.log (((2 ^ k : ℕ) : ℝ)) ≤ y :=
    (Real.log_le_iff_le_exp hpowpos).2 hcast
  have hklog : (k : ℝ) * Real.log 2 ≤ y := by
    rw [Nat.cast_pow, Real.log_pow] at hlogpow
    simpa using hlogpow
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hkhalf : (k : ℝ) / 2 ≤ y := by
    calc
      (k : ℝ) / 2 ≤ (k : ℝ) * Real.log 2 := by
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
      _ ≤ y := hklog
  push_cast
  nlinarith

/-- The manuscript's factorial step with its natural exponent `2k-1`.

For `k ≥ 1`, support automatically supplies the degree hypothesis required by
`weightedMangoldtKernel_le_degree_control`.  Thus a level-`k` majorant of shape
`C exp(u) (1+u)^(2k-1)` propagates to level `k+1` with the explicit gain
`1/(2k)`.  The zero case is separated so no artificial lower bound on `y` is
needed. -/
theorem lambdaMeanSquareExp_succ_le_factorial_step
    (k : ℕ) {y C : ℝ} (hk : 1 ≤ k) (hy : 0 ≤ y) (hC : 0 ≤ C)
    (hmajor : ∀ u : ℝ, 0 ≤ u → u ≤ y →
      lambdaMeanSquareExp k u ≤ C * Real.exp u * (1 + u) ^ (2 * k - 1)) :
    lambdaMeanSquareExp (k + 1) y ≤
      y *
        (C * Real.exp y *
          ((1 + Zeta23.XiPrime.KM * 4) *
            (1 + y) ^ (2 * k) / ((2 * k : ℕ) : ℝ))) := by
  by_cases hzero : lambdaMeanSquareExp (k + 1) y = 0
  · rw [hzero]
    have hbase : 0 ≤ 1 + y := by linarith
    have hconst : 0 ≤ 1 + Zeta23.XiPrime.KM * 4 := by
      nlinarith [Zeta23.XiPrime.KM_nonneg]
    positivity
  · have hsupp := factorialDegree_control_of_ne_zero (k + 1) hzero
    have hdegree : (((2 * k - 1 + 1 : ℕ) : ℝ)) ≤ 4 * (1 + y) := by
      have hnat : 2 * k - 1 + 1 = 2 * k := by omega
      rw [hnat]
      have hle : 2 * k ≤ 2 * (k + 1) := by omega
      exact (by exact_mod_cast hle : ((2 * k : ℕ) : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ)).trans hsupp
    have hnat : 2 * k - 1 + 1 = 2 * k := by omega
    simpa only [hnat] using
      (lambdaMeanSquareExp_succ_le_of_polynomial_majorant
        k (2 * k - 1) hy hC hmajor hdegree)

end HLPLocalModel
end ZetaZero
