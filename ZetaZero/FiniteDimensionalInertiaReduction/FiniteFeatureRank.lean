import ZetaZero.FiniteDimensionalInertiaReduction.FiniteRankPerturbation

/-!
# Finite-feature rank reduction

A perturbation which factors through finitely many features should be removed at
feature level, before any analytic smallness estimate is attempted.  This file
records that principle without introducing adjoints or spectral theory.

If `M : V → F` is the feature map and an error factors as `N.comp M`, then the
whole error vanishes on `ker M`; the deletion cost is exactly the rank of `M`.
For two feature families the intersection of the two feature kernels kills the
sum of the two factored errors, with the corresponding additive codimension
budget.  The latter is the algebraic pattern needed after Hermitianizing a
non-symmetric finite-feature term.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section FiniteFeatureRank

variable {𝕜 V F₁ F₂ W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  [AddCommGroup F₁] [Module 𝕜 F₁]
  [AddCommGroup F₂] [Module 𝕜 F₂]
  [AddCommGroup W] [Module 𝕜 W]

/-- Any operator factoring through a feature map vanishes on the feature
kernel.  No norm bound on the middle/final operator is needed. -/
theorem ker_le_ker_comp_of_feature
    (M : V →ₗ[𝕜] F₁) (N : F₁ →ₗ[𝕜] W) :
    LinearMap.ker M ≤ LinearMap.ker (N.comp M) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  simp [hv]

/-- A single finite-feature family can be deleted at the rank cost of its
feature map, independently of the size of the operator acting on the features. -/
theorem finiteFeature_kernel_budget
    (M : V →ₗ[𝕜] F₁) (N : F₁ →ₗ[𝕜] W) {r : ℕ}
    (hM : Module.finrank 𝕜 (LinearMap.range M) ≤ r) :
    codim (LinearMap.ker M) ≤ r ∧
      LinearMap.ker M ≤ LinearMap.ker (N.comp M) := by
  exact ⟨codim_ker_le hM, ker_le_ker_comp_of_feature M N⟩

/-- The intersection of two feature kernels kills a sum of two independently
factored errors.  This is the rank-first form of the usual `B + B*` bookkeeping:
one pays only for the two feature families, not for an operator norm estimate. -/
theorem inf_ker_le_ker_add_comp_of_features
    (M₁ : V →ₗ[𝕜] F₁) (N₁ : F₁ →ₗ[𝕜] W)
    (M₂ : V →ₗ[𝕜] F₂) (N₂ : F₂ →ₗ[𝕜] W) :
    LinearMap.ker M₁ ⊓ LinearMap.ker M₂ ≤
      LinearMap.ker ((N₁.comp M₁) + (N₂.comp M₂)) := by
  intro v hv
  have h₁ : M₁ v = 0 := (LinearMap.mem_ker).mp hv.1
  have h₂ : M₂ v = 0 := (LinearMap.mem_ker).mp hv.2
  rw [LinearMap.mem_ker]
  simp [h₁, h₂]

/-- Two finite-feature families have additive deletion cost and kill the sum of
all errors factoring through them. -/
theorem twoFiniteFeature_kernel_budget
    (M₁ : V →ₗ[𝕜] F₁) (N₁ : F₁ →ₗ[𝕜] W)
    (M₂ : V →ₗ[𝕜] F₂) (N₂ : F₂ →ₗ[𝕜] W)
    {r₁ r₂ : ℕ}
    (hM₁ : Module.finrank 𝕜 (LinearMap.range M₁) ≤ r₁)
    (hM₂ : Module.finrank 𝕜 (LinearMap.range M₂) ≤ r₂) :
    codim (LinearMap.ker M₁ ⊓ LinearMap.ker M₂) ≤ r₁ + r₂ ∧
      LinearMap.ker M₁ ⊓ LinearMap.ker M₂ ≤
        LinearMap.ker ((N₁.comp M₁) + (N₂.comp M₂)) := by
  constructor
  · calc
      codim (LinearMap.ker M₁ ⊓ LinearMap.ker M₂)
          ≤ codim (LinearMap.ker M₁) + codim (LinearMap.ker M₂) :=
            codim_inf_le _ _
      _ ≤ r₁ + r₂ := Nat.add_le_add (codim_ker_le hM₁) (codim_ker_le hM₂)
  · exact inf_ker_le_ker_add_comp_of_features M₁ N₁ M₂ N₂

end FiniteFeatureRank

end FiniteDimensionalInertiaReduction
end ZetaZero
