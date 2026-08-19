import ZetaZero.FiniteDimensionalInertiaReduction.HermitianThreshold
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Finite-dimensional inertia reduction: Hilbert--Schmidt bridge

For a finite matrix the squared Hilbert--Schmidt norm is represented by
`Re (trace (Aᴴ * A))`.  For Hermitian matrices this equals the sum of the
squares of the real eigenvalues, which is exactly the spectral mass used by the
threshold-counting module.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section HilbertSchmidtBridge

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜}

/-- Squared Hilbert--Schmidt norm in finite coordinates. -/
noncomputable def hilbertSchmidtSq (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re ((A.conjTranspose * A).trace)

/-- For a Hermitian matrix, squared Hilbert--Schmidt norm is the sum of squared
real eigenvalues. -/
theorem hilbertSchmidtSq_eq_spectralMass (hA : A.IsHermitian) :
    hilbertSchmidtSq A = spectralMass hA := by
  classical
  let U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  let D : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hunit : star U * U = 1 := by
    dsimp [U]
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hilbertSchmidtSq, hA.eq]
  have hsquareA : A * A = U * (D * D) * star U := by
    rw [hspec]
    calc
      (U * D * star U) * (U * D * star U)
          = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * (D * D) * star U := by
        rw [hunit]
        noncomm_ring
  rw [hsquareA]
  have htrace : (U * (D * D) * star U).trace = (D * D).trace := by
    rw [Matrix.trace_mul_cycle]
    simp [hunit]
  rw [htrace]
  simp [D, spectralMass, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]

/-- The threshold count can therefore be stated directly in Hilbert--Schmidt
language. -/
theorem card_badEigenvalues_mul_sq_le_hilbertSchmidtSq
    (hA : A.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((thresholdSet hA.eigenvalues τ).card : ℝ) * τ ^ 2 ≤ hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq_eq_spectralMass hA]
  exact card_badEigenvalues_mul_sq_le_spectralMass hA hτ

/-- At threshold `c₀/4`, the bad spectral dimension is bounded by the paper's
`16 c₀⁻²` Hilbert--Schmidt budget. -/
theorem card_badEigenvalues_quarter_le_hilbertSchmidt
    (hA : A.IsHermitian) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ((thresholdSet hA.eigenvalues (c₀ / 4)).card : ℝ)
      ≤ 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq_eq_spectralMass hA]
  exact card_badEigenvalues_quarter_le_sixteen hA hc₀

end HilbertSchmidtBridge

end FiniteDimensionalInertiaReduction
end ZetaZero
