import ZetaZero.HLPLocalModel.NaturalCutoffFactorialMajorant

/-!
# Normalized direct-carrier square bounds

The stationary/right-edge source uses the level `α_{k+1}` after multiplication
by a deterministic factor `(C/L)^(k+1)`.  This module transfers the natural
cutoff factorial majorant through that normalization and isolates the scalar
cancellation supplied by `1 + log X ≤ L`.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Square sum of one normalized HLP level at the natural cutoff `X`. -/
def normalizedAlphaLevelSquare
    (k X : ℕ) (C L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    (((C / L) ^ (k + 1)) * hlpAlphaSucc k n) ^ 2

/-- A scalar factor may be pulled through the finite HLP square sum exactly. -/
theorem normalizedAlphaLevelSquare_eq
    (k X : ℕ) (C L : ℝ) :
    normalizedAlphaLevelSquare k X C L =
      (C / L) ^ (2 * (k + 1)) *
        ∑ n ∈ Finset.Icc 1 X, (hlpAlphaSucc k n) ^ 2 := by
  unfold normalizedAlphaLevelSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

/-- Direct transfer of the factorial majorant through the deterministic level
normalization. -/
theorem normalizedAlphaLevelSquare_factorial
    (k X : ℕ) (C L : ℝ) (hX : 1 ≤ X) :
    normalizedAlphaLevelSquare k X C L ≤
      (C / L) ^ (2 * (k + 1)) *
        (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            (k + 1).factorial *
          (X : ℝ) * (1 + Real.log X) ^ (2 * k + 3)) := by
  rw [normalizedAlphaLevelSquare_eq]
  have hscale : 0 ≤ (C / L) ^ (2 * (k + 1)) := by
    simpa [show 2 * (k + 1) = (k + 1) * 2 by omega, pow_mul] using
      (sq_nonneg ((C / L) ^ (k + 1)))
  exact mul_le_mul_of_nonneg_left
    (hlpAlpha_nat_factorial_majorant k X hX) hscale

/-- Scalar cancellation behind the completed direct-carrier estimate.
If `0 ≤ a ≤ L`, then the `L^{-r}` normalization removes all but one copy of
`a` from `(C/L)^(2r) a^(2r+1)`. -/
theorem normalized_power_cancel
    (r : ℕ) {a C L : ℝ}
    (ha : 0 ≤ a) (hL : 0 < L) (haL : a ≤ L) (hC : 0 ≤ C) :
    (C / L) ^ (2 * r) * a ^ (2 * r + 1) ≤
      C ^ (2 * r) * a := by
  have hratio0 : 0 ≤ a / L := div_nonneg ha hL.le
  have hratio1 : a / L ≤ 1 := (div_le_one hL).2 haL
  have hpow : (a / L) ^ (2 * r) ≤ 1 := by
    exact (pow_le_one₀ hratio0 hratio1 : (a / L) ^ (2 * r) ≤ 1)
  have hCpow : 0 ≤ C ^ (2 * r) := pow_nonneg hC _
  have ha' : 0 ≤ a := ha
  calc
    (C / L) ^ (2 * r) * a ^ (2 * r + 1) =
        C ^ (2 * r) * (a / L) ^ (2 * r) * a := by
      field_simp [hL.ne']
      ring
    _ ≤ C ^ (2 * r) * 1 * a := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hCpow) ha'
    _ = C ^ (2 * r) * a := by ring

/-- Completed one-level direct-carrier budget.  Under the manuscript range
condition `1 + log X ≤ L`, all logarithmic powers created by level `k+1` are
absorbed by the deterministic `L^{-(k+1)}` normalization, leaving a single
factor `1 + log X`. -/
theorem normalizedAlphaLevelSquare_completed
    (k X : ℕ) {C L : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hC : 0 ≤ C)
    (hlog : 1 + Real.log X ≤ L) :
    normalizedAlphaLevelSquare k X C L ≤
      Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          (k + 1).factorial *
        (X : ℝ) * C ^ (2 * (k + 1)) * (1 + Real.log X) := by
  have hbase0 : 0 ≤ 1 + Real.log X := by
    have hlog0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hX)
    linarith
  have hscalar := normalized_power_cancel (k + 1)
    hbase0 hL hlog hC
  have hfac :
      0 ≤ Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          (k + 1).factorial * (X : ℝ) := by
    have hfact : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg Zeta23.XiPrime.KM_nonneg
          (pow_nonneg factorialMajorantStepConstant_nonneg k))
        hfact.le)
      hX0
  calc
    normalizedAlphaLevelSquare k X C L ≤
      (C / L) ^ (2 * (k + 1)) *
        (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            (k + 1).factorial *
          (X : ℝ) * (1 + Real.log X) ^ (2 * k + 3)) :=
      normalizedAlphaLevelSquare_factorial k X C L hX
    _ = (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            (k + 1).factorial * (X : ℝ)) *
        ((C / L) ^ (2 * (k + 1)) *
          (1 + Real.log X) ^ (2 * (k + 1) + 1)) := by
      ring_nf
    _ ≤ (Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            (k + 1).factorial * (X : ℝ)) *
        (C ^ (2 * (k + 1)) * (1 + Real.log X)) := by
      exact mul_le_mul_of_nonneg_left hscalar hfac
    _ = Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          (k + 1).factorial *
        (X : ℝ) * C ^ (2 * (k + 1)) * (1 + Real.log X) := by
      ring

end HLPLocalModel
end ZetaZero
