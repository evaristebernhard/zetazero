import ZetaZero.HLPLocalModel.NormalizedDirectCarrier
import ZetaZero.HLPLocalModel.FiniteLevelMinkowski

/-!
# Finite normalized HLP carrier assembly

This file combines the one-level factorial estimate with the finite-dimensional
Minkowski interface.  It is the bridge needed by a finite resolvent truncation:
any finite set of normalized `P^k Q` levels may be assembled before taking the
coefficient `ℓ²` norm, at the cost of summing the individual level norms.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Coefficient square sum of a finite collection of normalized HLP levels. -/
def normalizedAlphaFiniteCarrierSquare
    (K : Finset ℕ) (X : ℕ) (C L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    (∑ k ∈ K, (C / L) ^ (k + 1) * hlpAlphaSucc k n) ^ 2

/-- Finite-level Minkowski for the normalized HLP carrier. -/
theorem sqrt_normalizedAlphaFiniteCarrierSquare_le_sum_levels
    (K : Finset ℕ) (X : ℕ) (C L : ℝ) :
    Real.sqrt (normalizedAlphaFiniteCarrierSquare K X C L) ≤
      ∑ k ∈ K, Real.sqrt (normalizedAlphaLevelSquare k X C L) := by
  simpa [normalizedAlphaFiniteCarrierSquare, normalizedAlphaLevelSquare] using
    (sqrt_sum_sq_sum_levels_le
      (Finset.Icc 1 X) K
      (fun k n => (C / L) ^ (k + 1) * hlpAlphaSucc k n))

/-- The explicit one-level budget appearing after the safe-line normalization. -/
def normalizedAlphaLevelBudget
    (k X : ℕ) (C : ℝ) : ℝ :=
  Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
      (k + 1).factorial *
    (X : ℝ) * C ^ (2 * (k + 1)) * (1 + Real.log X)

/-- Any finite collection of normalized HLP levels is controlled by the sum of
square roots of the factorial one-level budgets.  No orthogonality between HLP
levels is assumed; this is precisely the robust finite-truncation estimate used
before treating the exact resolvent tail. -/
theorem sqrt_normalizedAlphaFiniteCarrierSquare_completed
    (K : Finset ℕ) (X : ℕ) {C L : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hC : 0 ≤ C)
    (hlog : 1 + Real.log X ≤ L) :
    Real.sqrt (normalizedAlphaFiniteCarrierSquare K X C L) ≤
      ∑ k ∈ K, Real.sqrt (normalizedAlphaLevelBudget k X C) := by
  calc
    Real.sqrt (normalizedAlphaFiniteCarrierSquare K X C L) ≤
        ∑ k ∈ K, Real.sqrt (normalizedAlphaLevelSquare k X C L) :=
      sqrt_normalizedAlphaFiniteCarrierSquare_le_sum_levels K X C L
    _ ≤ ∑ k ∈ K, Real.sqrt (normalizedAlphaLevelBudget k X C) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Real.sqrt_le_sqrt
      simpa [normalizedAlphaLevelBudget] using
        (normalizedAlphaLevelSquare_completed k X hX hL hC hlog)

end HLPLocalModel
end ZetaZero
