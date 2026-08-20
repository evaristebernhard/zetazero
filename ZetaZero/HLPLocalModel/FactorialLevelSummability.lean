import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summability of square-root factorial HLP level weights

The HLP carrier assembly needs the one-dimensional convergence

`sum_k A^k / sqrt(k!) < ∞`.

A useful formal proof avoids a separate ratio-test calculation: write the term
as a product of two `ℓ²` sequences and apply Hölder/Cauchy--Schwarz.  The first
square is an exponential-series coefficient and the second is geometric.
-/

open Real
open scoped BigOperators Topology

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- The nonnegative square-root factorial weight used by the HLP level sum. -/
def sqrtFactorialWeight (A : ℝ) (k : ℕ) : ℝ :=
  |A| ^ k / Real.sqrt k.factorial

/-- Auxiliary first `ℓ²` factor. -/
def sqrtFactorialL2Factor (A : ℝ) (k : ℕ) : ℝ :=
  (2 * |A|) ^ k / Real.sqrt k.factorial

/-- Auxiliary geometric `ℓ²` factor. -/
def halfGeometricFactor (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ k

lemma sqrtFactorialL2Factor_nonneg (A : ℝ) (k : ℕ) :
    0 ≤ sqrtFactorialL2Factor A k := by
  unfold sqrtFactorialL2Factor
  positivity

lemma halfGeometricFactor_nonneg (k : ℕ) : 0 ≤ halfGeometricFactor k := by
  unfold halfGeometricFactor
  positivity

/-- Squaring the first auxiliary factor gives an ordinary exponential-series
coefficient. -/
theorem sqrtFactorialL2Factor_rpow_two (A : ℝ) (k : ℕ) :
    (sqrtFactorialL2Factor A k) ^ (2 : ℝ) =
      (4 * A ^ 2) ^ k / k.factorial := by
  rw [Real.rpow_two]
  unfold sqrtFactorialL2Factor
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hnum : ((2 * |A|) ^ k) ^ 2 = (4 * A ^ 2) ^ k := by
    rw [pow_two, ← mul_pow]
    congr 1
    calc
      2 * |A| * (2 * |A|) = 4 * |A| ^ 2 := by ring
      _ = 4 * A ^ 2 := by rw [sq_abs]
  simp [hnum]

/-- Squaring the geometric auxiliary factor gives ratio `1/4`. -/
theorem halfGeometricFactor_rpow_two (k : ℕ) :
    (halfGeometricFactor k) ^ (2 : ℝ) = (1 / 4 : ℝ) ^ k := by
  rw [Real.rpow_two]
  unfold halfGeometricFactor
  rw [pow_two, ← mul_pow]
  congr 1
  norm_num

/-- The square-root factorial weights are summable for every real parameter. -/
theorem summable_sqrtFactorialWeight (A : ℝ) :
    Summable (sqrtFactorialWeight A) := by
  have hf2 : Summable (fun k => (sqrtFactorialL2Factor A k) ^ (2 : ℝ)) := by
    refine (Real.summable_pow_div_factorial (4 * A ^ 2)).congr ?_
    intro k
    exact (sqrtFactorialL2Factor_rpow_two A k).symm
  have hg2 : Summable (fun k => (halfGeometricFactor k) ^ (2 : ℝ)) := by
    have hgeom : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine hgeom.congr ?_
    intro k
    exact (halfGeometricFactor_rpow_two k).symm
  have hprod := Real.summable_mul_of_Lp_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (sqrtFactorialL2Factor_nonneg A)
    halfGeometricFactor_nonneg hf2 hg2
  refine hprod.congr ?_
  intro k
  unfold sqrtFactorialWeight sqrtFactorialL2Factor halfGeometricFactor
  rw [div_mul_eq_mul_div, ← mul_pow]
  congr 1
  ring

/-- Elementary domination of linear growth by powers of two. -/
theorem nat_succ_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k
  | 0 => by simp
  | k + 1 => by
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 (nat_succ_le_two_pow k)
        _ = 2 ^ (k + 1) := by rw [pow_succ']

/-- A fixed polynomial factor in the level index is absorbed by enlarging the
exponential parameter in the square-root factorial weight. -/
theorem polynomial_mul_sqrtFactorialWeight_le
    (A : ℝ) (q k : ℕ) :
    (((k + 1 : ℕ) : ℝ)) ^ q * sqrtFactorialWeight A k ≤
      sqrtFactorialWeight (|A| * (2 : ℝ) ^ q) k := by
  have hk : (((k + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast nat_succ_le_two_pow k
  have hpoly :
      (((k + 1 : ℕ) : ℝ)) ^ q ≤ ((2 : ℝ) ^ q) ^ k := by
    calc
      (((k + 1 : ℕ) : ℝ)) ^ q ≤ ((2 : ℝ) ^ k) ^ q := by
        exact pow_le_pow_left₀ (by positivity) hk q
      _ = ((2 : ℝ) ^ q) ^ k := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold sqrtFactorialWeight
  have hden : 0 ≤ Real.sqrt (k.factorial : ℝ) := Real.sqrt_nonneg _
  have hnum :
      (((k + 1 : ℕ) : ℝ)) ^ q * |A| ^ k ≤
        ((2 : ℝ) ^ q) ^ k * |A| ^ k :=
    mul_le_mul_of_nonneg_right hpoly (pow_nonneg (abs_nonneg A) k)
  calc
    (((k + 1 : ℕ) : ℝ)) ^ q * (|A| ^ k / Real.sqrt (k.factorial : ℝ)) =
        ((((k + 1 : ℕ) : ℝ)) ^ q * |A| ^ k) /
          Real.sqrt (k.factorial : ℝ) := by ring
    _ ≤ (((2 : ℝ) ^ q) ^ k * |A| ^ k) /
          Real.sqrt (k.factorial : ℝ) :=
      div_le_div_of_nonneg_right hnum hden
    _ = |(|A| * (2 : ℝ) ^ q)| ^ k /
          Real.sqrt (k.factorial : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg A) (pow_nonneg (by norm_num) q)), mul_pow]
      ring

/-- Fixed polynomial losses in the HLP level preserve square-root factorial
summability. -/
theorem summable_polynomial_mul_sqrtFactorialWeight
    (A : ℝ) (q : ℕ) :
    Summable (fun k : ℕ =>
      (((k + 1 : ℕ) : ℝ)) ^ q * sqrtFactorialWeight A k) := by
  have hdom := summable_sqrtFactorialWeight (|A| * (2 : ℝ) ^ q)
  exact hdom.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (by positivity) q)
      (by unfold sqrtFactorialWeight; positivity))
    (fun k => polynomial_mul_sqrtFactorialWeight_le A q k)

end HLPLocalModel
end ZetaZero
