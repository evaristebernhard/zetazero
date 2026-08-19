import ZetaZero.FiniteDimensionalInertiaReduction.FiniteRankPerturbation

/-!
# Finite-dimensional inertia reduction: negative-index bounds

For the formal core it is more robust to express an inertia estimate as the
statement that every strictly negative subspace has bounded dimension.  A
numerical negative index can be introduced later as a derived notion.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section NegativeIndex

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- `NegativeIndexLE q n` means that every subspace on which `q` is strictly
negative away from zero has dimension at most `n`. -/
def NegativeIndexLE (q : V → ℝ) (n : ℕ) : Prop :=
  ∀ N : Submodule 𝕜 V, StrictlyNegativeOn q N → Module.finrank 𝕜 N ≤ n

/-- A nonnegative subspace gives a negative-index bound by its codimension. -/
theorem negativeIndexLE_codim_of_nonnegativeOn
    {q : V → ℝ} {W : Submodule 𝕜 V}
    (hW : NonnegativeOn q W) :
    NegativeIndexLE (𝕜 := 𝕜) q (codim W) := by
  intro N hN
  exact finrank_le_codim_of_nonnegativeOn_of_strictlyNegativeOn hW hN

/-- Any upper bound for the codimension of a nonnegative subspace is an upper
bound for the negative index. -/
theorem negativeIndexLE_of_nonnegativeOn_of_codim_le
    {q : V → ℝ} {W : Submodule 𝕜 V} {n : ℕ}
    (hW : NonnegativeOn q W) (hcod : codim W ≤ n) :
    NegativeIndexLE (𝕜 := 𝕜) q n := by
  intro N hN
  exact (finrank_le_codim_of_nonnegativeOn_of_strictlyNegativeOn hW hN).trans hcod

/-- Intersecting two good subspaces adds their codimension budgets. -/
theorem negativeIndexLE_inf_of_nonnegativeOn
    {q : V → ℝ} {S T : Submodule 𝕜 V}
    (hgood : NonnegativeOn q (S ⊓ T)) :
    NegativeIndexLE (𝕜 := 𝕜) q (codim S + codim T) := by
  apply negativeIndexLE_of_nonnegativeOn_of_codim_le hgood
  exact codim_inf_le S T

end NegativeIndex

end FiniteDimensionalInertiaReduction
end ZetaZero
