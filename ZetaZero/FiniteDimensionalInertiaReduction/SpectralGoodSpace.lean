import ZetaZero.FiniteDimensionalInertiaReduction.DiagonalRemainder
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite-dimensional inertia reduction: Hermitian spectral good space

For a Hermitian matrix `A`, the unitary eigenvector matrix supplies spectral
coordinates.  The good space is defined intrinsically as the kernel obtained by
first passing to spectral coordinates and then restricting to the bad
coordinates `|λᵢ| ≥ τ`.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section SpectralGoodSpace

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜}

/-- Change from physical coordinates to the Hermitian eigenbasis coordinates. -/
noncomputable def spectralCoordinateMap (hA : A.IsHermitian) :
    (n → 𝕜) →ₗ[𝕜] (n → 𝕜) :=
  (star (hA.eigenvectorUnitary : Matrix n n 𝕜)).mulVecLin

/-- Read only the bad spectral coordinates. -/
noncomputable def spectralBadCoordinateMap
    (hA : A.IsHermitian) (τ : ℝ) :
    (n → 𝕜) →ₗ[𝕜] (thresholdSet hA.eigenvalues τ → 𝕜) :=
  (badCoordinateMap (𝕜 := 𝕜) (thresholdSet hA.eigenvalues τ)).comp
    (spectralCoordinateMap hA)

/-- Physical vectors whose bad Hermitian spectral coordinates vanish. -/
noncomputable def hermitianGoodSpace (hA : A.IsHermitian) (τ : ℝ) :
    Submodule 𝕜 (n → 𝕜) :=
  LinearMap.ker (spectralBadCoordinateMap hA τ)

/-- Membership means precisely that every bad spectral coordinate vanishes. -/
theorem mem_hermitianGoodSpace_iff
    (hA : A.IsHermitian) (τ : ℝ) {x : n → 𝕜} :
    x ∈ hermitianGoodSpace hA τ ↔
      ∀ i : thresholdSet hA.eigenvalues τ,
        spectralCoordinateMap hA x i.1 = 0 := by
  constructor
  · intro hx i
    have hker : spectralBadCoordinateMap hA τ x = 0 := hx
    have hi := congrFun hker i
    simpa [spectralBadCoordinateMap, badCoordinateMap] using hi
  · intro hx
    rw [hermitianGoodSpace, LinearMap.mem_ker]
    funext i
    simpa [spectralBadCoordinateMap, badCoordinateMap] using hx i

/-- The physical good space costs at most the number of bad eigenvalues. -/
theorem codim_hermitianGoodSpace_le_card
    (hA : A.IsHermitian) (τ : ℝ) :
    codim (hermitianGoodSpace hA τ) ≤
      (thresholdSet hA.eigenvalues τ).card := by
  unfold hermitianGoodSpace
  rw [codim_ker_eq_finrank_range]
  calc
    Module.finrank 𝕜 (LinearMap.range (spectralBadCoordinateMap hA τ))
        ≤ Module.finrank 𝕜 (thresholdSet hA.eigenvalues τ → 𝕜) :=
          Submodule.finrank_le _
    _ = Fintype.card (thresholdSet hA.eigenvalues τ) :=
          Module.finrank_fintype_fun_eq_card 𝕜
    _ = (thresholdSet hA.eigenvalues τ).card :=
          Fintype.card_coe _

/-- At threshold `c₀/4`, the actual physical good space has exactly the
Hilbert--Schmidt codimension budget required by the manuscript. -/
theorem codim_hermitianGoodSpace_quarter_le_hilbertSchmidt
    (hA : A.IsHermitian) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    (codim (hermitianGoodSpace hA (c₀ / 4)) : ℝ)
      ≤ 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq A := by
  have hcod := codim_hermitianGoodSpace_le_card hA (c₀ / 4)
  have hcount := card_badEigenvalues_quarter_le_hilbertSchmidt hA hc₀
  have hcodReal :
      (codim (hermitianGoodSpace hA (c₀ / 4)) : ℝ)
        ≤ ((thresholdSet hA.eigenvalues (c₀ / 4)).card : ℝ) := by
    exact_mod_cast hcod
  exact hcodReal.trans hcount

end SpectralGoodSpace

end FiniteDimensionalInertiaReduction
end ZetaZero
