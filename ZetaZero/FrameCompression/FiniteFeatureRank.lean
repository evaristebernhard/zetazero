import ZetaZero.FiniteDimensionalInertiaReduction.FiniteRankPerturbation
import Mathlib.Tactic

/-!
# M08: finite-feature rank bounds

A large class of edge terms in the manuscript depend on a vector only through
finitely many linear features.  This file isolates the purely linear-algebraic
consequence: any operator that factors through the feature space has rank at
most the dimension of that space.  No small operator-norm estimate is needed.
-/

namespace ZetaZero
namespace FrameCompression

section FiniteFeatureRank

variable {𝕜 V F W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup F] [Module 𝕜 F]
  [AddCommGroup W] [Module 𝕜 W]

/-- The range of a composite linear map is contained in the range of its final
factor. -/
theorem range_comp_le_range (M : V →ₗ[𝕜] F) (N : F →ₗ[𝕜] W) :
    LinearMap.range (N.comp M) ≤ LinearMap.range N := by
  rintro y ⟨x, rfl⟩
  exact ⟨M x, rfl⟩

variable [FiniteDimensional 𝕜 F]

/-- The rank of a linear map is at most the dimension of its domain. -/
theorem finrank_range_le_domain (N : F →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range N) ≤ Module.finrank 𝕜 F := by
  have hquot := (LinearMap.ker N).finrank_quotient_add_finrank
  have hiso := N.quotKerEquivRange.finrank_eq
  lia

/-- Any operator that factors through a finite feature space has rank at most
that feature-space dimension. -/
theorem finrank_range_comp_le_middle (M : V →ₗ[𝕜] F) (N : F →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N.comp M)) ≤ Module.finrank 𝕜 F := by
  calc
    Module.finrank 𝕜 (LinearMap.range (N.comp M))
        ≤ Module.finrank 𝕜 (LinearMap.range N) :=
      Submodule.finrank_mono (range_comp_le_range M N)
    _ ≤ Module.finrank 𝕜 F := finrank_range_le_domain N

variable {ι : Type*} [Fintype ι]

/-- Coordinate version: `ι` scalar features cost at most `|ι|` rank. -/
theorem finrank_range_factor_through_coordinates_le_card
    (M : V →ₗ[𝕜] (ι → 𝕜)) (N : (ι → 𝕜) →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N.comp M)) ≤ Fintype.card ι := by
  calc
    Module.finrank 𝕜 (LinearMap.range (N.comp M))
        ≤ Module.finrank 𝕜 (ι → 𝕜) := finrank_range_comp_le_middle M N
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card 𝕜

variable {β : Type*} [Fintype β] {r : ℕ}

/-- If every block contributes `r` scalar features, any operator factoring
through all block features has rank at most `r * (# blocks)`. -/
theorem finrank_range_block_features_le
    (M : V →ₗ[𝕜] ((β × Fin r) → 𝕜))
    (N : ((β × Fin r) → 𝕜) →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N.comp M)) ≤ r * Fintype.card β := by
  have h := finrank_range_factor_through_coordinates_le_card M N
  simpa [Fintype.card_prod, Nat.mul_comm] using h

/-- The HLZ completed `I`-kernel has nine separable features per block, so once
its factorization through those features is supplied, its rank is at most nine
times the number of blocks. -/
theorem finrank_range_nine_features_per_block_le
    (M : V →ₗ[𝕜] ((β × Fin 9) → 𝕜))
    (N : ((β × Fin 9) → 𝕜) →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N.comp M)) ≤ 9 * Fintype.card β := by
  exact finrank_range_block_features_le M N

/-- The range of a sum of two operators lies in the sum of their ranges. -/
theorem range_add_le_sup (A B : V →ₗ[𝕜] W) :
    LinearMap.range (A + B) ≤ LinearMap.range A ⊔ LinearMap.range B := by
  rintro y ⟨x, rfl⟩
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _
    (show A x ∈ LinearMap.range A ⊔ LinearMap.range B from
      (show LinearMap.range A ≤ LinearMap.range A ⊔ LinearMap.range B from le_sup_left) ⟨x, rfl⟩)
    (show B x ∈ LinearMap.range A ⊔ LinearMap.range B from
      (show LinearMap.range B ≤ LinearMap.range A ⊔ LinearMap.range B from le_sup_right) ⟨x, rfl⟩)

variable [FiniteDimensional 𝕜 W]

/-- Ranks are subadditive under addition of linear operators. -/
theorem finrank_range_add_le (A B : V →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (A + B)) ≤
      Module.finrank 𝕜 (LinearMap.range A) + Module.finrank 𝕜 (LinearMap.range B) := by
  have hmono := Submodule.finrank_mono (range_add_le_sup A B)
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A) (LinearMap.range B)
  lia

variable {F₁ F₂ : Type*}
  [AddCommGroup F₁] [Module 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [AddCommGroup F₂] [Module 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

/-- Two finite-feature operators cost at most the sum of their feature-space
sizes.  This is the abstract rank bookkeeping needed after Hermitianizing a
non-symmetric finite-feature term. -/
theorem finrank_range_add_of_two_factors_le
    (M₁ : V →ₗ[𝕜] F₁) (N₁ : F₁ →ₗ[𝕜] W)
    (M₂ : V →ₗ[𝕜] F₂) (N₂ : F₂ →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N₁.comp M₁ + N₂.comp M₂)) ≤
      Module.finrank 𝕜 F₁ + Module.finrank 𝕜 F₂ := by
  exact (finrank_range_add_le (N₁.comp M₁) (N₂.comp M₂)).trans
    (Nat.add_le_add
      (finrank_range_comp_le_middle M₁ N₁)
      (finrank_range_comp_le_middle M₂ N₂))

end FiniteFeatureRank

end FrameCompression
end ZetaZero
