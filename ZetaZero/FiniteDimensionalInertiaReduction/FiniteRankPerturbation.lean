import ZetaZero.FiniteDimensionalInertiaReduction.SubspaceBudget

/-!
# Finite-dimensional inertia reduction: finite-rank perturbations

The finite-rank error is removed by restricting to its kernel.  This file
records the exact codimension cost of that operation.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section FiniteRankPerturbation

variable {𝕜 V W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- The codimension of the kernel of a linear map equals the dimension of its
range.  The codomain need not equal the domain. -/
theorem codim_ker_eq_finrank_range (E : V →ₗ[𝕜] W) :
    codim (LinearMap.ker E) = Module.finrank 𝕜 (LinearMap.range E) := by
  unfold codim
  exact E.quotKerEquivRange.finrank_eq

/-- A rank bound gives the corresponding codimension bound for the kernel. -/
theorem codim_ker_le {E : V →ₗ[𝕜] W} {r : ℕ}
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r) :
    codim (LinearMap.ker E) ≤ r := by
  rw [codim_ker_eq_finrank_range]
  exact hE

end FiniteRankPerturbation

end FiniteDimensionalInertiaReduction
end ZetaZero
