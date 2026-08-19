import ZetaZero.FiniteDimensionalInertiaReduction.SpectralThresholdCount
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FieldSimp

/-!
# Finite-dimensional inertia reduction: Hermitian spectral threshold

This file connects the abstract threshold-counting lemma to the eigenvalues of
a finite Hermitian matrix.  It still uses spectral mass
`∑ i, λᵢ²`; identification with the Frobenius/Hilbert--Schmidt norm belongs in
a separate bridge.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section HermitianThreshold

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜}

/-- Squared spectral mass of a Hermitian matrix. -/
noncomputable def spectralMass (hA : A.IsHermitian) : ℝ :=
  ∑ i, (hA.eigenvalues i) ^ 2

/-- Eigenvalues of magnitude at least `τ` consume at least `τ²` units of
spectral mass each. -/
theorem card_badEigenvalues_mul_sq_le_spectralMass
    (hA : A.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((thresholdSet hA.eigenvalues τ).card : ℝ) * τ ^ 2 ≤ spectralMass hA := by
  simpa [spectralMass] using card_thresholdSet_mul_sq_le_sum_sq hA.eigenvalues hτ

/-- Division form of the threshold estimate. -/
theorem card_badEigenvalues_le_spectralMass_div_sq
    (hA : A.IsHermitian) {τ : ℝ} (hτ : 0 < τ) :
    ((thresholdSet hA.eigenvalues τ).card : ℝ) ≤ spectralMass hA / τ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).2
  exact card_badEigenvalues_mul_sq_le_spectralMass hA hτ.le

/-- At the paper's threshold `c₀/4`, the bad eigenvalue count costs exactly the
factor `16 c₀⁻²`. -/
theorem card_badEigenvalues_quarter_le_sixteen
    (hA : A.IsHermitian) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ((thresholdSet hA.eigenvalues (c₀ / 4)).card : ℝ)
      ≤ 16 * (c₀ ^ 2)⁻¹ * spectralMass hA := by
  have h := card_badEigenvalues_le_spectralMass_div_sq hA (div_pos hc₀ (by norm_num : (0 : ℝ) < 4))
  calc
    ((thresholdSet hA.eigenvalues (c₀ / 4)).card : ℝ)
        ≤ spectralMass hA / (c₀ / 4) ^ 2 := h
    _ = 16 * (c₀ ^ 2)⁻¹ * spectralMass hA := by
      field_simp [hc₀.ne']
      ring

end HermitianThreshold

end FiniteDimensionalInertiaReduction
end ZetaZero
