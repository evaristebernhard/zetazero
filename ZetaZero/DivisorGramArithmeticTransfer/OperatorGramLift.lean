import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Operator-valued Gram lifts

The arithmetic comparison in M07 uses scalar positive kernels together with
packet/divisor translations.  The paper phrases this as an operator-valued
positive lift.  The finite-dimensional core is even more general: no
unitarity assumption on the translated maps is needed once the scalar kernel
has been given by Gram coordinates.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace ZetaZero
namespace DivisorGramArithmeticTransfer

variable {ι κ V W : Type*}
  [Fintype ι] [Fintype κ]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The vector in the `j`-th Gram channel after applying the labelled maps
`U n` and scalar coefficients `a n * x j n`. -/
def gramChannel
    (x : κ → ι → ℂ) (a : ι → ℂ) (U : ι → V →ₗ[ℂ] W) (v : V) (j : κ) : W :=
  ∑ n, (a n * x j n) • U n v

/-- A scalar kernel presented by finite Gram coordinates. -/
def scalarGramKernel (x : κ → ι → ℂ) (m n : ι) : ℂ :=
  ∑ j, conj (x j m) * x j n

/-- The operator-valued quadratic form obtained by lifting a scalar Gram
kernel through a labelled family of linear maps. -/
def liftedGramForm
    (x : κ → ι → ℂ) (a : ι → ℂ) (U : ι → V →ₗ[ℂ] W) (v : V) : ℂ :=
  ∑ m, ∑ n,
    conj (a m) * a n * scalarGramKernel x m n * ⟪U m v, U n v⟫_ℂ

/-- Expanding the Gram channels gives exactly the lifted kernel quadratic
form.  This is the algebraic identity behind the operator-valued positive
lift in the manuscript. -/
theorem sum_inner_gramChannel_eq_liftedGramForm
    (x : κ → ι → ℂ) (a : ι → ℂ) (U : ι → V →ₗ[ℂ] W) (v : V) :
    (∑ j, ⟪gramChannel x a U v j, gramChannel x a U v j⟫_ℂ) =
      liftedGramForm x a U v := by
  calc
    (∑ j, ⟪gramChannel x a U v j, gramChannel x a U v j⟫_ℂ) =
        ∑ j, ∑ m, ∑ n,
          conj (a m) * a n * conj (x j m) * x j n * ⟪U m v, U n v⟫_ℂ := by
      simp_rw [gramChannel, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      simp
      ring
    _ = ∑ m, ∑ n, ∑ j,
          conj (a m) * a n * conj (x j m) * x j n * ⟪U m v, U n v⟫_ℂ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
    _ = liftedGramForm x a U v := by
      unfold liftedGramForm scalarGramKernel
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The lifted Gram form is real. -/
theorem liftedGramForm_im_eq_zero
    (x : κ → ι → ℂ) (a : ι → ℂ) (U : ι → V →ₗ[ℂ] W) (v : V) :
    (liftedGramForm x a U v).im = 0 := by
  rw [← sum_inner_gramChannel_eq_liftedGramForm]
  simp

/-- Positivity of the operator-valued Gram lift.  Notice that `U n` are only
assumed linear; isometry or unitarity is unnecessary for positivity. -/
theorem liftedGramForm_re_nonnegative
    (x : κ → ι → ℂ) (a : ι → ℂ) (U : ι → V →ₗ[ℂ] W) (v : V) :
    0 ≤ (liftedGramForm x a U v).re := by
  rw [← sum_inner_gramChannel_eq_liftedGramForm]
  simp [inner_self_eq_norm_sq]

end DivisorGramArithmeticTransfer
end ZetaZero
