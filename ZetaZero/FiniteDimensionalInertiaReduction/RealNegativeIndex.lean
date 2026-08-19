import ZetaZero.FiniteDimensionalInertiaReduction.NegativeIndex

/-!
# Finite-dimensional inertia reduction: real-valued inertia bounds

The paper bounds an integer-valued negative inertia by a real expression such
as `r + 16 * c₀⁻² * s`.  This predicate records that statement without
introducing an artificial ceiling.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section RealNegativeIndex

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- `NegativeIndexBound q b` means that every strictly negative subspace has
(real-coerced) dimension at most `b`. -/
def NegativeIndexBound (q : V → ℝ) (b : ℝ) : Prop :=
  ∀ N : Submodule 𝕜 V, StrictlyNegativeOn q N → (Module.finrank 𝕜 N : ℝ) ≤ b

/-- A nonnegative subspace bounds the real-valued negative index by its
codimension. -/
theorem negativeIndexBound_codim_of_nonnegativeOn
    {q : V → ℝ} {W : Submodule 𝕜 V}
    (hW : NonnegativeOn q W) :
    NegativeIndexBound (𝕜 := 𝕜) q (codim W : ℝ) := by
  intro N hN
  exact_mod_cast finrank_le_codim_of_nonnegativeOn_of_strictlyNegativeOn hW hN

/-- Any real upper bound for the codimension of a nonnegative subspace bounds
its negative index. -/
theorem negativeIndexBound_of_nonnegativeOn_of_codim_le
    {q : V → ℝ} {W : Submodule 𝕜 V} {b : ℝ}
    (hW : NonnegativeOn q W) (hcod : (codim W : ℝ) ≤ b) :
    NegativeIndexBound (𝕜 := 𝕜) q b := by
  intro N hN
  have hdim : (Module.finrank 𝕜 N : ℝ) ≤ (codim W : ℝ) := by
    exact_mod_cast finrank_le_codim_of_nonnegativeOn_of_strictlyNegativeOn hW hN
  exact hdim.trans hcod

end RealNegativeIndex

end FiniteDimensionalInertiaReduction
end ZetaZero
