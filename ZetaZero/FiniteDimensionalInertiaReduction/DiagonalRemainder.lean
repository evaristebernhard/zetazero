import ZetaZero.FiniteDimensionalInertiaReduction.CoordinateGoodSpace
import Mathlib.Analysis.RCLike.Basic

/-!
# Finite-dimensional inertia reduction: diagonal remainder bounds

After diagonalizing a Hermitian remainder, deleting the coordinates with
`|λᵢ| ≥ τ` leaves a subspace on which the diagonal quadratic form is bounded
below by `-τ` times the coordinate norm square.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section DiagonalRemainder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- Squared Euclidean norm written in coordinates. -/
noncomputable def coordinateNormSq (x : n → 𝕜) : ℝ :=
  ∑ i, RCLike.normSq (x i)

/-- Real quadratic form of a real diagonal operator. -/
noncomputable def diagonalQuadratic (vals : n → ℝ) (x : n → 𝕜) : ℝ :=
  ∑ i, vals i * RCLike.normSq (x i)

/-- Coordinate norm square is nonnegative. -/
theorem coordinateNormSq_nonneg (x : n → 𝕜) :
    0 ≤ coordinateNormSq x := by
  unfold coordinateNormSq
  exact Finset.sum_nonneg fun i _ => RCLike.normSq_nonneg (x i)

/-- Outside the threshold set, every diagonal value is at least `-τ`. -/
theorem neg_threshold_le_of_not_mem
    (vals : n → ℝ) {τ : ℝ} {i : n}
    (hi : i ∉ thresholdSet vals τ) :
    -τ ≤ vals i := by
  classical
  have habs : |vals i| < τ := by
    have hnot : ¬ τ ≤ |vals i| := by
      simpa [thresholdSet] using hi
    exact lt_of_not_ge hnot
  have hleft : -τ ≤ -|vals i| := neg_le_neg habs.le
  exact hleft.trans (neg_abs_le (vals i))

/-- On the coordinate good space, the diagonal quadratic form has lower bound
`-τ ‖x‖²`. -/
theorem diagonalQuadratic_lower_on_coordinateGoodSpace
    (vals : n → ℝ) {τ : ℝ}
    {x : n → 𝕜}
    (hx : x ∈ coordinateGoodSpace (𝕜 := 𝕜) (thresholdSet vals τ)) :
    -τ * coordinateNormSq x ≤ diagonalQuadratic vals x := by
  classical
  have hvanish : ∀ i : thresholdSet vals τ, x i.1 = 0 :=
    (mem_coordinateGoodSpace_iff (𝕜 := 𝕜)).1 hx
  have hpoint : ∀ i : n,
      -τ * RCLike.normSq (x i) ≤ vals i * RCLike.normSq (x i) := by
    intro i
    by_cases hi : i ∈ thresholdSet vals τ
    · have hxi : x i = 0 := hvanish ⟨i, hi⟩
      simp [hxi]
    · exact mul_le_mul_of_nonneg_right
        (neg_threshold_le_of_not_mem vals hi)
        (RCLike.normSq_nonneg (x i))
  unfold coordinateNormSq diagonalQuadratic
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hpoint i

end DiagonalRemainder

end FiniteDimensionalInertiaReduction
end ZetaZero
