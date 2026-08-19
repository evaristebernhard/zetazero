import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Abstract positive Gram pullbacks

Later divisor and Euler-product arguments construct concrete analysis maps and
compare their pullback Grams.  This file isolates the universal positivity and
kernel facts for a finite complex analysis map.
-/

open Complex Finset
open scoped BigOperators

noncomputable section

namespace ZetaZero
namespace DivisorGramArithmeticTransfer

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]

/-- Quadratic form of the positive Gram `W* W`, written without choosing a
matrix representation. -/
def gramQuadratic (W : V →ₗ[ℂ] (ι → ℂ)) (v : V) : ℝ :=
  ∑ i, Complex.normSq (W v i)

/-- Every Gram pullback is nonnegative. -/
theorem gramQuadratic_nonnegative (W : V →ₗ[ℂ] (ι → ℂ)) (v : V) :
    0 ≤ gramQuadratic W v := by
  unfold gramQuadratic
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (W v i)

/-- The Gram quadratic form vanishes exactly on the kernel of the analysis map. -/
theorem gramQuadratic_eq_zero_iff (W : V →ₗ[ℂ] (ι → ℂ)) (v : V) :
    gramQuadratic W v = 0 ↔ W v = 0 := by
  constructor
  · intro hsum
    funext i
    have hterm : Complex.normSq (W v i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg (W v j))).mp hsum i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hterm
  · intro hv
    simp [gramQuadratic, hv]

/-- An injective analysis map gives a positive-definite Gram form. -/
theorem gramQuadratic_pos_of_injective
    (W : V →ₗ[ℂ] (ι → ℂ)) (hW : Function.Injective W) {v : V} (hv : v ≠ 0) :
    0 < gramQuadratic W v := by
  have hnonneg := gramQuadratic_nonnegative W v
  apply lt_of_le_of_ne hnonneg
  intro hz
  have hker : W v = 0 := (gramQuadratic_eq_zero_iff W v).mp hz.symm
  have : v = 0 := hW (by simpa using hker)
  exact hv this

/-- Precomposing the analysis map is exactly pullback of the Gram quadratic
form.  This is the abstract algebra behind divisor-coordinate transfer. -/
theorem gramQuadratic_comp
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    (W : V →ₗ[ℂ] (ι → ℂ)) (D : U →ₗ[ℂ] V) (u : U) :
    gramQuadratic (W.comp D) u = gramQuadratic W (D u) := by
  rfl

end DivisorGramArithmeticTransfer
end ZetaZero
