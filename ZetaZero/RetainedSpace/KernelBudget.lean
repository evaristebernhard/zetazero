import ZetaZero.FiniteDimensionalInertiaReduction

/-!
# Retained-space kernel and intersection budgets

This file isolates the finite-dimensional bookkeeping behind the global/local
mean constraints and the final retained-space intersection.  It is deliberately
independent of the analytic definitions of the mean maps.
-/

namespace ZetaZero
namespace RetainedSpace

open FiniteDimensionalInertiaReduction

section KernelBudget

variable {𝕜 V W₁ W₂ : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W₁] [Module 𝕜 W₁]
  [AddCommGroup W₂] [Module 𝕜 W₂]

/-- Intersecting the kernels of two linear constraints costs at most the sum of
the ranks of the two constraint maps. -/
theorem codim_inf_ker_le_range_sum (M₁ : V →ₗ[𝕜] W₁) (M₂ : V →ₗ[𝕜] W₂) :
    codim (LinearMap.ker M₁ ⊓ LinearMap.ker M₂) ≤
      Module.finrank 𝕜 (LinearMap.range M₁) +
        Module.finrank 𝕜 (LinearMap.range M₂) := by
  calc
    codim (LinearMap.ker M₁ ⊓ LinearMap.ker M₂) ≤
        codim (LinearMap.ker M₁) + codim (LinearMap.ker M₂) :=
      codim_inf_le _ _
    _ = Module.finrank 𝕜 (LinearMap.range M₁) +
          Module.finrank 𝕜 (LinearMap.range M₂) := by
      rw [codim_ker_eq_finrank_range, codim_ker_eq_finrank_range]

/-- Three retained-space restrictions have codimension bounded by the sum of
their individual codimensions. -/
theorem codim_threefold_inf_le (S T U : Submodule 𝕜 V) :
    codim ((S ⊓ T) ⊓ U) ≤ codim S + codim T + codim U := by
  calc
    codim ((S ⊓ T) ⊓ U) ≤ codim (S ⊓ T) + codim U := codim_inf_le _ _
    _ ≤ (codim S + codim T) + codim U :=
      Nat.add_le_add_right (codim_inf_le S T) _
    _ = codim S + codim T + codim U := rfl

end KernelBudget

end RetainedSpace
end ZetaZero
