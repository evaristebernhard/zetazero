import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic

/-!
# Finite-dimensional inertia reduction: basic notions

This file contains the stable algebraic vocabulary used by the M01 facade.
It deliberately does not mention zeta-functions, contour integrals, or the
paper's asymptotic parameters.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section Basic

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Finite-dimensional codimension, defined intrinsically by the quotient. -/
noncomputable def codim (S : Submodule 𝕜 V) : ℕ :=
  Module.finrank 𝕜 (V ⧸ S)

/-- A real-valued form is nonnegative on a subspace. -/
def NonnegativeOn (q : V → ℝ) (S : Submodule 𝕜 V) : Prop :=
  ∀ x, x ∈ S → 0 ≤ q x

/-- A real-valued form is strictly negative on every nonzero vector of a subspace. -/
def StrictlyNegativeOn (q : V → ℝ) (S : Submodule 𝕜 V) : Prop :=
  ∀ x, x ∈ S → x ≠ 0 → q x < 0

end Basic

end FiniteDimensionalInertiaReduction
end ZetaZero
