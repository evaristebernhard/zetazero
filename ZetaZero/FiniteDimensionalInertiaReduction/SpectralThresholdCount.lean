import ZetaZero.FiniteDimensionalInertiaReduction.RankPlusGoodSpace

/-!
# Finite-dimensional inertia reduction: spectral threshold counting

This file isolates the numerical heart of the Hilbert--Schmidt deletion step.
If every index in a bad set carries spectral mass at least `τ`, then the size of
that set is controlled by the total squared spectral mass.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section SpectralThresholdCount

variable {ι : Type*} [Fintype ι]

/-- Indices whose spectral value has magnitude at least `τ`. -/
noncomputable def thresholdSet (vals : ι → ℝ) (τ : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => τ ≤ |vals i|

/-- The elementary counting estimate behind the Hilbert--Schmidt threshold
argument. -/
theorem card_thresholdSet_mul_sq_le_sum_sq
    (vals : ι → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((thresholdSet vals τ).card : ℝ) * τ ^ 2 ≤ ∑ i, (vals i) ^ 2 := by
  classical
  let S := thresholdSet vals τ
  have hpoint : ∀ i ∈ S, τ ^ 2 ≤ (vals i) ^ 2 := by
    intro i hi
    have hi' : τ ≤ |vals i| := by
      simpa [S, thresholdSet] using (Finset.mem_filter.mp hi).2
    have hsquare : τ * τ ≤ |vals i| * |vals i| := mul_self_le_mul_self hτ hi'
    simpa [pow_two, abs_mul_abs_self] using hsquare
  calc
    (S.card : ℝ) * τ ^ 2 = ∑ i ∈ S, τ ^ 2 := by simp
    _ ≤ ∑ i ∈ S, (vals i) ^ 2 := by
      exact Finset.sum_le_sum fun i hi => hpoint i hi
    _ ≤ ∑ i, (vals i) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => sq_nonneg (vals i))

end SpectralThresholdCount

end FiniteDimensionalInertiaReduction
end ZetaZero
