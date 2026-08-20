import Zeta23.XiPrime.Coeff.PowerSums

/-!
# Weighted Chebyshev--Mertens kernel for the HLP factorial majorant

The factorial induction needs a uniform bound for the decreasing polynomial
weight

`sum_{d ≤ exp y} (Λ(d)/d) * (1 + y - log d)^m`.

The vendored Zeta23 library already proves the general Abel/Mertens step for an
arbitrary `C¹` weight.  This file specializes that theorem to the polynomial
kernel used in the manuscript and keeps the exact `1/(m+1)` gain visible.
-/

open Finset Real MeasureTheory Set
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

open Zeta23 XiPrime

/-- The logarithmically weighted Mangoldt kernel in exponential coordinates. -/
def weightedMangoldtKernel (m : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
    ArithmeticFunction.vonMangoldt d / d * (1 + y - Real.log d) ^ m

/-- Exact Abel/Mertens upper bound for the decreasing polynomial kernel.

The main integral contributes the crucial factor `1/(m+1)`; the error is only
`KM * (1+y)^m`.  A later support argument (`2^k ≤ X`) absorbs that error
uniformly in the HLP level. -/
theorem weightedMangoldtKernel_le (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    weightedMangoldtKernel m y ≤
      ((1 + y) ^ (m + 1) - 1) / (m + 1) +
        Zeta23.XiPrime.KM * (1 + y) ^ m := by
  let c : ℝ := 1 + y
  let f : ℝ → ℝ := fun v => (c - v) ^ m
  let f' : ℝ → ℝ := fun v => -(m * (c - v) ^ (m - 1))
  have hc0 : 0 ≤ c := by
    dsimp [c]
    linarith
  have hcy : c - y = 1 := by
    dsimp [c]
    ring
  have hderiv : ∀ v ∈ Set.Icc 0 y, HasDerivAt f (f' v) v := by
    intro v hv
    have h := ((hasDerivAt_id v).const_sub c).fun_pow m
    exact h.congr_deriv (by
      dsimp [f']
      ring)
  have hf'c : ContinuousOn f' (Set.Icc 0 y) := by
    dsimp [f']
    fun_prop
  have hstep := Zeta23.XiPrime.mertens_step hy hderiv hf'c
  have hint_f :
      ∫ v in (0 : ℝ)..y, f v =
        ((1 + y) ^ (m + 1) - 1) / (m + 1) := by
    dsimp [f]
    rw [Zeta23.XiPrime.integral_const_sub_pow]
    rw [hcy]
    simp [c]
  have hfu : |f y| = 1 := by
    dsimp [f]
    rw [hcy]
    simp
  have hint_f' :
      ∫ v in (0 : ℝ)..y, |f' v| = (1 + y) ^ m - 1 := by
    have heq : ∀ v ∈ Set.uIcc (0 : ℝ) y,
        |f' v| = (m : ℝ) * (c - v) ^ (m - 1) := by
      intro v hv
      rw [Set.uIcc_of_le hy] at hv
      have hcv : 0 ≤ c - v := by
        dsimp [c]
        linarith [hv.2]
      dsimp [f']
      rw [abs_neg, abs_of_nonneg]
      exact mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hcv _)
    rw [intervalIntegral.integral_congr heq]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst m
      simp
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [intervalIntegral.integral_const_mul,
        Zeta23.XiPrime.integral_const_sub_pow]
      rw [hcy]
      push_cast
      field_simp
      ring
  have hsum_le :
      (∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d / d * f (Real.log d)) ≤
        (∫ v in (0 : ℝ)..y, f v) +
          Zeta23.XiPrime.KM *
            (|f y| + ∫ v in (0 : ℝ)..y, |f' v|) := by
    have habs := (abs_sub_le_iff.mp hstep).1
    linarith
  calc
    weightedMangoldtKernel m y =
        ∑ d ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊,
          ArithmeticFunction.vonMangoldt d / d * f (Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [f, c]
    _ ≤ (∫ v in (0 : ℝ)..y, f v) +
        Zeta23.XiPrime.KM *
          (|f y| + ∫ v in (0 : ℝ)..y, |f' v|) := hsum_le
    _ = ((1 + y) ^ (m + 1) - 1) / (m + 1) +
        Zeta23.XiPrime.KM * (1 + y) ^ m := by
      rw [hint_f, hfu, hint_f']
      ring

/-- Absorb the Mertens error into the main `1/(m+1)` term whenever the degree is
at most a fixed multiple of the logarithmic range.  This is the uniform form
used after the support inequality `2^k ≤ X` converts the HLP level into an
`O(log X)` degree restriction. -/
theorem weightedMangoldtKernel_le_degree_control
    (m : ℕ) {y B : ℝ} (hy : 0 ≤ y)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ B * (1 + y)) :
    weightedMangoldtKernel m y ≤
      (1 + Zeta23.XiPrime.KM * B) *
        (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) := by
  have hbase := weightedMangoldtKernel_le m hy
  have hc : 0 < 1 + y := by linarith
  have hc0 : 0 ≤ 1 + y := hc.le
  have hden : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hpow : 0 ≤ (1 + y) ^ m := pow_nonneg hc0 m
  have hKMpow : 0 ≤ Zeta23.XiPrime.KM * (1 + y) ^ m :=
    mul_nonneg Zeta23.XiPrime.KM_nonneg hpow
  have herr :
      Zeta23.XiPrime.KM * (1 + y) ^ m ≤
        Zeta23.XiPrime.KM * B * (1 + y) ^ (m + 1) /
          ((m + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hm hKMpow
    calc
      Zeta23.XiPrime.KM * (1 + y) ^ m * ((m + 1 : ℕ) : ℝ) ≤
          Zeta23.XiPrime.KM * (1 + y) ^ m * (B * (1 + y)) := hmul
      _ = Zeta23.XiPrime.KM * B * (1 + y) ^ (m + 1) := by
        rw [pow_succ]
        ring
  have hmain :
      ((1 + y) ^ (m + 1) - 1) / ((m + 1 : ℕ) : ℝ) ≤
        (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  calc
    weightedMangoldtKernel m y ≤
        ((1 + y) ^ (m + 1) - 1) / ((m + 1 : ℕ) : ℝ) +
          Zeta23.XiPrime.KM * (1 + y) ^ m := by
      simpa using hbase
    _ ≤ (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) +
        Zeta23.XiPrime.KM * B * (1 + y) ^ (m + 1) /
          ((m + 1 : ℕ) : ℝ) := add_le_add hmain herr
    _ = (1 + Zeta23.XiPrime.KM * B) *
        (1 + y) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) := by
      ring

end HLPLocalModel
end ZetaZero
