import ZetaZero.HLPLocalModel.FiniteLevelMinkowski

/-!
# Finite carrier assembly from levelwise square budgets

This is the abstract functional-analytic closure used by the HLP direct carrier:
if level `k` has square norm at most `M * w_k^2`, then any finite sum of levels
has `ell^2` norm at most `sqrt(M) * sum w_k`.
-/

open Finset Real
open scoped BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Convert a square budget into a norm budget. -/
theorem sqrt_le_sqrt_mul_weight
    {x M w : ℝ} (hM : 0 ≤ M) (hw : 0 ≤ w)
    (hx : x ≤ M * w ^ 2) :
    Real.sqrt x ≤ Real.sqrt M * w := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) hw
  · calc
      x ≤ M * w ^ 2 := hx
      _ = (Real.sqrt M * w) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hM]

/-- Finite carrier assembly theorem. -/
theorem finiteCarrierAssembly_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (K : Finset κ) (a : κ → ι → ℝ)
    (M : ℝ) (w : κ → ℝ)
    (hM : 0 ≤ M) (hw : ∀ k ∈ K, 0 ≤ w k)
    (hlevel : ∀ k ∈ K,
      (∑ i ∈ s, (a k i) ^ 2) ≤ M * (w k) ^ 2) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) ≤
      Real.sqrt M * ∑ k ∈ K, w k := by
  calc
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) ≤
        ∑ k ∈ K, Real.sqrt (∑ i ∈ s, (a k i) ^ 2) :=
      sqrt_sum_sq_sum_levels_le s K a
    _ ≤ ∑ k ∈ K, Real.sqrt M * w k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact sqrt_le_sqrt_mul_weight hM (hw k hk) (hlevel k hk)
    _ = Real.sqrt M * ∑ k ∈ K, w k := by
      rw [Finset.mul_sum]

/-- A summable nonnegative level weight gives one uniform constant for every
finite level subset. -/
theorem finiteCarrierAssembly_le_tsum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (K : Finset ℕ) (a : ℕ → ι → ℝ)
    (M : ℝ) (w : ℕ → ℝ)
    (hM : 0 ≤ M) (hw : ∀ k, 0 ≤ w k) (hsum : Summable w)
    (hlevel : ∀ k ∈ K,
      (∑ i ∈ s, (a k i) ^ 2) ≤ M * (w k) ^ 2) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) ≤
      Real.sqrt M * ∑' k, w k := by
  calc
    Real.sqrt (∑ i ∈ s, (∑ k ∈ K, a k i) ^ 2) ≤
        Real.sqrt M * ∑ k ∈ K, w k :=
      finiteCarrierAssembly_le s K a M w hM (fun k hk => hw k) hlevel
    _ ≤ Real.sqrt M * ∑' k, w k := by
      exact mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum K (fun k hk => hw k))
        (Real.sqrt_nonneg M)

end HLPLocalModel
end ZetaZero
