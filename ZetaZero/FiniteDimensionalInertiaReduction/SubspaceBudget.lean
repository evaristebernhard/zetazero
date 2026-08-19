import ZetaZero.FiniteDimensionalInertiaReduction.Basic
import Mathlib.Tactic

/-!
# Finite-dimensional inertia reduction: subspace budgets

This file isolates the dimension bookkeeping used when finitely many bad
subspaces are removed from the ambient finite-dimensional space.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section SubspaceBudget

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Codimensions are subadditive under intersection. -/
theorem codim_inf_le (S T : Submodule 𝕜 V) :
    codim (S ⊓ T) ≤ codim S + codim T := by
  have hS := S.finrank_quotient_add_finrank
  have hT := T.finrank_quotient_add_finrank
  have hInf := (S ⊓ T).finrank_quotient_add_finrank
  have hGrassmann := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hSup : Module.finrank 𝕜 (S ⊔ T : Submodule 𝕜 V) ≤ Module.finrank 𝕜 V :=
    Submodule.finrank_le _
  unfold codim
  lia

omit [FiniteDimensional 𝕜 V] in
/-- A nonnegative subspace and a strictly negative subspace meet trivially. -/
theorem disjoint_of_nonnegativeOn_of_strictlyNegativeOn
    {q : V → ℝ} {W N : Submodule 𝕜 V}
    (hW : NonnegativeOn q W) (hN : StrictlyNegativeOn q N) :
    Disjoint W N := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hnonneg : 0 ≤ q x := hW x hx.1
  have hneg : q x < 0 := hN x hx.2 hx0
  exact (not_lt_of_ge hnonneg) hneg

/-- Every strictly negative subspace has dimension at most the codimension of a
subspace on which the same form is nonnegative. -/
theorem finrank_le_codim_of_nonnegativeOn_of_strictlyNegativeOn
    {q : V → ℝ} {W N : Submodule 𝕜 V}
    (hW : NonnegativeOn q W) (hN : StrictlyNegativeOn q N) :
    Module.finrank 𝕜 N ≤ codim W := by
  have hdisjoint := disjoint_of_nonnegativeOn_of_strictlyNegativeOn hW hN
  have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
  have hcod := W.finrank_quotient_add_finrank
  unfold codim
  lia

end SubspaceBudget

end FiniteDimensionalInertiaReduction
end ZetaZero
