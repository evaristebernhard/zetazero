import ZetaZero.FiniteDimensionalInertiaReduction.SpectralGoodSpace
import ZetaZero.FiniteDimensionalInertiaReduction.CongruenceTransport

/-!
# Finite-dimensional inertia reduction: whitened min--max theorem

This module closes the abstract M01 chain at the level used by the paper.  A
Hermitian whitened remainder supplies an intrinsic spectral good space; deleting
that space together with the kernel complement of a finite-rank perturbation
produces the required codimension budget and the `3 c₀ / 4` lower bound.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section WhitenedMinMax

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- On the Hermitian spectral good space, the diagonalized remainder is bounded
below by `-τ` times the whitened coordinate norm square. -/
theorem diagonalQuadratic_lower_on_hermitianGoodSpace
    {B : Matrix n n 𝕜} (hB : B.IsHermitian) {τ : ℝ}
    {x : n → 𝕜}
    (hx : x ∈ hermitianGoodSpace hB τ) :
    -τ * coordinateNormSq (spectralCoordinateMap hB x) ≤
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x) := by
  have hcoord :
      spectralCoordinateMap hB x ∈
        coordinateGoodSpace (𝕜 := 𝕜) (thresholdSet hB.eigenvalues τ) := by
    apply (mem_coordinateGoodSpace_iff (𝕜 := 𝕜)).2
    exact (mem_hermitianGoodSpace_iff hB τ).1 hx
  exact diagonalQuadratic_lower_on_coordinateGoodSpace hB.eigenvalues hcoord

/-- A quadratic form represented by the Hermitian spectral coordinates inherits
the spectral good-space lower bound. -/
theorem remainder_lower_on_hermitianGoodSpace
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {Rq Gq : (n → 𝕜) → ℝ} {τ : ℝ}
    (hRdiag : ∀ x, Rq x =
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x))
    (hGcoord : ∀ x, Gq x = coordinateNormSq (spectralCoordinateMap hB x)) :
    ∀ x, x ∈ hermitianGoodSpace hB τ → -τ * Gq x ≤ Rq x := by
  intro x hx
  rw [hRdiag x, hGcoord x]
  exact diagonalQuadratic_lower_on_hermitianGoodSpace hB hx

/-- The concrete good space used by the rank-plus-Hilbert--Schmidt argument. -/
noncomputable def whitenedGoodSpace
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    (E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)) (c₀ : ℝ) :
    Submodule 𝕜 (n → 𝕜) :=
  LinearMap.ker E ⊓ hermitianGoodSpace hB (c₀ / 4)

/-- The paper's good space has codimension at most rank plus the
Hilbert--Schmidt spectral budget. -/
theorem codim_whitenedGoodSpace_le_rank_add_hilbertSchmidt
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ} {r : ℕ}
    (hc₀ : 0 < c₀)
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r) :
    (codim (whitenedGoodSpace hB E c₀) : ℝ) ≤
      (r : ℝ) + 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq B := by
  have hInfNat := codim_inf_le (LinearMap.ker E) (hermitianGoodSpace hB (c₀ / 4))
  have hKerNat := codim_ker_le hE
  have hSpec := codim_hermitianGoodSpace_quarter_le_hilbertSchmidt hB hc₀
  calc
    (codim (whitenedGoodSpace hB E c₀) : ℝ)
        ≤ (codim (LinearMap.ker E) + codim (hermitianGoodSpace hB (c₀ / 4)) : ℕ) := by
          exact_mod_cast hInfNat
    _ = (codim (LinearMap.ker E) : ℝ) +
        (codim (hermitianGoodSpace hB (c₀ / 4)) : ℝ) := by norm_num
    _ ≤ (r : ℝ) + 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq B := by
      apply add_le_add
      · exact_mod_cast hKerNat
      · exact hSpec

/-- Paper-facing finite-dimensional inertia reduction after whitening the
remainder.  The hypotheses `hRdiag` and `hGcoord` are exactly the change-of-basis
identities supplied by the whitening step. -/
theorem rank_plus_hilbertSchmidt_minmax
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {Aq Pq Eq Rq Gq : (n → 𝕜) → ℝ}
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ} {r : ℕ}
    (hc₀ : 0 < c₀)
    (hG : ∀ x, 0 ≤ Gq x)
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hRdiag : ∀ x, Rq x =
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x))
    (hGcoord : ∀ x, Gq x = coordinateNormSq (spectralCoordinateMap hB x))
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r) :
    NegativeIndexBound (𝕜 := 𝕜) Aq
      ((r : ℝ) + 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq B) := by
  apply negativeIndexBound_rank_plus_hilbertSchmidt_budget
    (T := hermitianGoodSpace hB (c₀ / 4)) hc₀ hG hdecomp hP hEzero
  · intro x hx
    simpa using remainder_lower_on_hermitianGoodSpace
      hB hRdiag hGcoord x hx
  · exact hE
  · exact codim_hermitianGoodSpace_quarter_le_hilbertSchmidt hB hc₀

/-- The same hypotheses give the stronger lower bound on the explicit good
space, matching the first boxed conclusion of the manuscript lemma. -/
theorem three_quarters_lower_on_whitenedGoodSpace
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {Aq Pq Eq Rq Gq : (n → 𝕜) → ℝ}
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ}
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hRdiag : ∀ x, Rq x =
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x))
    (hGcoord : ∀ x, Gq x = coordinateNormSq (spectralCoordinateMap hB x)) :
    ∀ x, x ∈ whitenedGoodSpace hB E c₀ → (3 * c₀ / 4) * Gq x ≤ Aq x := by
  apply three_quarters_lower_bound_on_good_space hdecomp hP hEzero
  intro x hx
  simpa using remainder_lower_on_hermitianGoodSpace
    hB hRdiag hGcoord x hx

section PhysicalCoordinates

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- Pull the explicit whitened good space back through an arbitrary invertible
whitening map.  This is the physical-coordinate subspace appearing in the
manuscript. -/
noncomputable def physicalGoodSpace
    (e : V ≃ₗ[𝕜] (n → 𝕜))
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    (E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)) (c₀ : ℝ) :
    Submodule 𝕜 V :=
  transportedSubspace e (whitenedGoodSpace hB E c₀)

/-- The rank-plus-Hilbert--Schmidt codimension budget survives the inverse
whitening map unchanged. -/
theorem codim_physicalGoodSpace_le_rank_add_hilbertSchmidt
    [FiniteDimensional 𝕜 V]
    (e : V ≃ₗ[𝕜] (n → 𝕜))
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ} {r : ℕ}
    (hc₀ : 0 < c₀)
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r) :
    (codim (physicalGoodSpace e hB E c₀) : ℝ) ≤
      (r : ℝ) + 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq B := by
  rw [physicalGoodSpace, codim_transportedSubspace_eq e]
  exact codim_whitenedGoodSpace_le_rank_add_hilbertSchmidt hB hc₀ hE

/-- The `3 c₀ / 4` lower bound on the explicit good space is invariant under
whitening congruence. -/
theorem three_quarters_lower_on_physicalGoodSpace
    (e : V ≃ₗ[𝕜] (n → 𝕜))
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {Aq Pq Eq Rq Gq : (n → 𝕜) → ℝ}
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ}
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hRdiag : ∀ x, Rq x =
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x))
    (hGcoord : ∀ x, Gq x = coordinateNormSq (spectralCoordinateMap hB x)) :
    ∀ x, x ∈ physicalGoodSpace e hB E c₀ →
      (3 * c₀ / 4) * pullbackForm e Gq x ≤ pullbackForm e Aq x := by
  apply lower_bound_on_transportedSubspace e
  exact three_quarters_lower_on_whitenedGoodSpace
    hB hdecomp hP hEzero hRdiag hGcoord

/-- Full paper-facing M01 conclusion in physical coordinates.  The only
whitening datum required by M01 is an invertible linear equivalence from the
physical space to coordinates in which the reference form is Euclidean and the
remainder is represented by the Hermitian matrix `B`. -/
theorem rank_plus_hilbertSchmidt_minmax_after_linearEquiv
    (e : V ≃ₗ[𝕜] (n → 𝕜))
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {Aq Pq Eq Rq Gq : (n → 𝕜) → ℝ}
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ} {r : ℕ}
    (hc₀ : 0 < c₀)
    (hG : ∀ x, 0 ≤ Gq x)
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hRdiag : ∀ x, Rq x =
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x))
    (hGcoord : ∀ x, Gq x = coordinateNormSq (spectralCoordinateMap hB x))
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r) :
    NegativeIndexBound (𝕜 := 𝕜) (pullbackForm e Aq)
      ((r : ℝ) + 16 * (c₀ ^ 2)⁻¹ * hilbertSchmidtSq B) := by
  apply negativeIndexBound_pullback e
  exact rank_plus_hilbertSchmidt_minmax
    hB hc₀ hG hdecomp hP hEzero hRdiag hGcoord hE

end PhysicalCoordinates

end WhitenedMinMax

end FiniteDimensionalInertiaReduction
end ZetaZero
