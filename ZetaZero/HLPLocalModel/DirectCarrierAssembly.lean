import ZetaZero.HLPLocalModel.NormalizedDirectCarrier
import ZetaZero.HLPLocalModel.FactorialLevelSummability
import ZetaZero.HLPLocalModel.FiniteCarrierAssembly

/-!
# Direct HLP carrier assembly

This file glues the arithmetic factorial majorant to the abstract finite-carrier
Minkowski theorem.  The resulting estimate is uniform over every finite subset
of HLP levels, matching the structural content of the manuscript's completed
direct-carrier bound.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- A deliberately loose exponential parameter for the assembled HLP levels. -/
def directCarrierParameter (C : ℝ) : ℝ :=
  C * (factorialMajorantStepConstant + 1)

lemma directCarrierParameter_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ directCarrierParameter C := by
  unfold directCarrierParameter
  exact mul_nonneg hC (add_nonneg factorialMajorantStepConstant_nonneg (by norm_num))

/-- The exact level coefficient from the factorial theorem is dominated by a
square-root-factorial weight with one fixed enlarged exponential parameter. -/
theorem directCarrier_factorial_factor_le
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    factorialMajorantStepConstant ^ k /
          (((k + 1).factorial : ℕ) : ℝ) * C ^ (2 * (k + 1)) ≤
      C ^ 2 * (sqrtFactorialWeight (directCarrierParameter C) k) ^ 2 := by
  let D : ℝ := factorialMajorantStepConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    exact factorialMajorantStepConstant_nonneg
  have hDstep : D ≤ (D + 1) ^ 2 := by nlinarith
  have hDpow : D ^ k ≤ ((D + 1) ^ 2) ^ k :=
    pow_le_pow_left₀ hD hDstep k
  have hfac : (0 : ℝ) < (k.factorial : ℕ) := by positivity
  have hsuccfac : (0 : ℝ) < ((k + 1).factorial : ℕ) := by positivity
  have hfac_le : ((k.factorial : ℕ) : ℝ) ≤ (((k + 1).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    have hk : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hkfac : (0 : ℝ) ≤ ((k.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hnum0 : 0 ≤ D ^ k * C ^ (2 * (k + 1)) :=
    mul_nonneg (pow_nonneg hD _) (pow_nonneg hC _)
  calc
    factorialMajorantStepConstant ^ k /
          (((k + 1).factorial : ℕ) : ℝ) * C ^ (2 * (k + 1)) =
        (D ^ k * C ^ (2 * (k + 1))) /
          (((k + 1).factorial : ℕ) : ℝ) := by
      dsimp [D]
      ring
    _ ≤ (D ^ k * C ^ (2 * (k + 1))) /
          ((k.factorial : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_left hnum0 hfac hfac_le
    _ ≤ (((D + 1) ^ 2) ^ k * C ^ (2 * (k + 1))) /
          ((k.factorial : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      exact mul_le_mul_of_nonneg_right hDpow (pow_nonneg hC _)
    _ = C ^ 2 * (sqrtFactorialWeight (directCarrierParameter C) k) ^ 2 := by
      unfold sqrtFactorialWeight directCarrierParameter
      rw [abs_of_nonneg (mul_nonneg hC (add_nonneg hD (by norm_num)))]
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_pow]
      rw [← pow_mul (D + 1) 2 k]
      rw [mul_pow, ← pow_mul C k 2, ← pow_mul (D + 1) k 2]
      field_simp
      ring

/-- The natural square-root-factorial level weight for the direct carrier. -/
def directCarrierWeight (C : ℝ) (k : ℕ) : ℝ :=
  C * sqrtFactorialWeight (directCarrierParameter C) k

lemma directCarrierWeight_nonneg {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ directCarrierWeight C k := by
  unfold directCarrierWeight sqrtFactorialWeight
  positivity

lemma summable_directCarrierWeight (C : ℝ) :
    Summable (directCarrierWeight C) := by
  unfold directCarrierWeight
  exact (summable_sqrtFactorialWeight (directCarrierParameter C)).mul_left C

/-- Fixed polynomial losses in the level index preserve summability of the direct
carrier weights. -/
lemma summable_polynomial_directCarrierWeight (C : ℝ) (q : ℕ) :
    Summable (fun k : ℕ =>
      (((k + 1 : ℕ) : ℝ)) ^ q * directCarrierWeight C k) := by
  unfold directCarrierWeight
  have h := summable_polynomial_mul_sqrtFactorialWeight
    (directCarrierParameter C) q
  exact h.mul_left C |>.congr (fun k => by ring)

/-- One normalized HLP level is bounded by the common carrier scale times the
square of `directCarrierWeight`. -/
theorem normalizedAlphaLevelSquare_direct_weight
    (k X : ℕ) {C L : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hC : 0 ≤ C)
    (hlog : 1 + Real.log X ≤ L) :
    normalizedAlphaLevelSquare k X C L ≤
      (Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X)) *
        (directCarrierWeight C k) ^ 2 := by
  have hbase := normalizedAlphaLevelSquare_completed k X hX hL hC hlog
  have hfactor := directCarrier_factorial_factor_le k hC
  have hcommon : 0 ≤ Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X) := by
    have hlog0 : 0 ≤ 1 + Real.log X := by
      have hxlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
      linarith
    exact mul_nonneg (mul_nonneg Zeta23.XiPrime.KM_nonneg (Nat.cast_nonneg X)) hlog0
  calc
    normalizedAlphaLevelSquare k X C L ≤
        Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
            (k + 1).factorial *
          (X : ℝ) * C ^ (2 * (k + 1)) * (1 + Real.log X) := hbase
    _ = (Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X)) *
        (factorialMajorantStepConstant ^ k /
          (((k + 1).factorial : ℕ) : ℝ) * C ^ (2 * (k + 1))) := by
      ring
    _ ≤ (Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X)) *
        (C ^ 2 * (sqrtFactorialWeight (directCarrierParameter C) k) ^ 2) :=
      mul_le_mul_of_nonneg_left hfactor hcommon
    _ = (Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X)) *
        (directCarrierWeight C k) ^ 2 := by
      unfold directCarrierWeight
      ring

/-- Any finite subset of normalized HLP levels has one common `ell^2` carrier
bound, independent of the chosen subset.  This is the coefficient-level core of
`lem:direct-carrier-square`. -/
theorem normalizedDirectCarrier_finiteSubset_le
    (K : Finset ℕ) (X : ℕ) {C L : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hC : 0 ≤ C)
    (hlog : 1 + Real.log X ≤ L) :
    Real.sqrt
        (∑ n ∈ Finset.Icc 1 X,
          (∑ k ∈ K, (C / L) ^ (k + 1) * hlpAlphaSucc k n) ^ 2) ≤
      Real.sqrt (Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X)) *
        ∑' k, directCarrierWeight C k := by
  let s : Finset ℕ := Finset.Icc 1 X
  let a : ℕ → ℕ → ℝ := fun k n =>
    (C / L) ^ (k + 1) * hlpAlphaSucc k n
  let M : ℝ := Zeta23.XiPrime.KM * (X : ℝ) * (1 + Real.log X)
  have hlog0 : 0 ≤ 1 + Real.log X := by
    have hxlog : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hX)
    linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg Zeta23.XiPrime.KM_nonneg (Nat.cast_nonneg X)) hlog0
  have hlevel : ∀ k ∈ K,
      (∑ n ∈ s, (a k n) ^ 2) ≤ M * (directCarrierWeight C k) ^ 2 := by
    intro k hk
    dsimp [s, a, M]
    exact normalizedAlphaLevelSquare_direct_weight k X hX hL hC hlog
  have h := finiteCarrierAssembly_le_tsum
    s K a M (directCarrierWeight C)
    hM (directCarrierWeight_nonneg hC)
    (summable_directCarrierWeight C) hlevel
  simpa [s, a, M] using h

/-- Generic finite-subset assembly when a fixed derivative contributes a
polynomial factor `(k+1)^q` to the level weight.  The bound remains uniform in
the chosen finite subset of levels. -/
theorem directCarrier_polynomialWeight_finiteSubset_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (K : Finset ℕ) (a : ℕ → ι → ℝ)
    (M C : ℝ) (q : ℕ)
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hlevel : ∀ k ∈ K,
      (∑ i ∈ s, (a k i) ^ 2) ≤
        M * ((((k + 1 : ℕ) : ℝ)) ^ q * directCarrierWeight C k) ^ 2) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) ≤
      Real.sqrt M *
        ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ q * directCarrierWeight C k := by
  apply finiteCarrierAssembly_le_tsum
  · exact hM
  · intro k
    exact mul_nonneg (pow_nonneg (by positivity) q)
      (directCarrierWeight_nonneg hC k)
  · exact summable_polynomial_directCarrierWeight C q
  · exact hlevel

end HLPLocalModel
end ZetaZero
