import ZetaZero.FiniteDimensionalInertiaReduction.RealNegativeIndex

/-!
# Finite-dimensional inertia reduction: rank plus good-space assembly

This is the algebraic assembly used by the paper's min--max lemma.  The
analytic Hilbert--Schmidt argument is responsible only for constructing the
second good subspace and proving its codimension bound.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section RankPlusGoodSpace

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- If a form is nonnegative after removing the range of a finite-rank error
and a second bad subspace, then its negative index is bounded by the sum of the
two dimension budgets. -/
theorem negativeIndexBound_rank_plus_goodSpace
    {q : V → ℝ} {E : V →ₗ[𝕜] V} {T : Submodule 𝕜 V}
    {r : ℕ} {h : ℝ}
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r)
    (hT : (codim T : ℝ) ≤ h)
    (hgood : NonnegativeOn q (LinearMap.ker E ⊓ T)) :
    NegativeIndexBound (𝕜 := 𝕜) q ((r : ℝ) + h) := by
  apply negativeIndexBound_of_nonnegativeOn_of_codim_le hgood
  have hInfNat := codim_inf_le (LinearMap.ker E) T
  have hKerNat := codim_ker_le hE
  calc
    (codim (LinearMap.ker E ⊓ T) : ℝ)
        ≤ (codim (LinearMap.ker E) + codim T : ℕ) := by
            exact_mod_cast hInfNat
    _ = (codim (LinearMap.ker E) : ℝ) + (codim T : ℝ) := by
          norm_num
    _ ≤ (r : ℝ) + h := by
          apply add_le_add
          · exact_mod_cast hKerNat
          · exact hT

end RankPlusGoodSpace

end FiniteDimensionalInertiaReduction
end ZetaZero
