import ZetaZero.RightEdgeArithmeticSource.SourceAlgebra
import Mathlib.Tactic

/-!
# Exact finite resolvent expansion for the HLP hierarchy

The HLP local hierarchy comes from expanding `1 / (F-P)` as a finite geometric
series in `P/F`.  This file fixes that expansion and its exact tail algebraically,
with no smallness or convergence hypothesis.  Analytic work later only has to
bound the displayed remainder.
-/

open Complex Finset

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Partial geometric sum through level `K`. -/
def resolventPartialSum (x : ℂ) (K : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (K + 1), x ^ k

/-- Exact finite geometric resolvent identity. -/
theorem inv_one_sub_eq_partial_add_tail
    {x : ℂ} (K : ℕ) (hx : 1 - x ≠ 0) :
    (1 - x)⁻¹ = resolventPartialSum x K + x ^ (K + 1) * (1 - x)⁻¹ := by
  have hgeom := geom_sum_mul x (K + 1)
  unfold resolventPartialSum
  apply (mul_left_cancel₀ hx)
  rw [mul_add]
  have h1 : (1 - x) * (∑ k ∈ Finset.range (K + 1), x ^ k) = 1 - x ^ (K + 1) := by
    calc
      (1 - x) * (∑ k ∈ Finset.range (K + 1), x ^ k) =
          -((∑ k ∈ Finset.range (K + 1), x ^ k) * (x - 1)) := by ring
      _ = -(x ^ (K + 1) - 1) := by rw [hgeom]
      _ = 1 - x ^ (K + 1) := by ring
  rw [h1]
  field_simp [hx]
  ring

/-- Exact finite expansion of `Q/(F-P)` through HLP level `K`, with an explicit
algebraic tail. -/
theorem quotient_eq_hlp_partial_add_tail
    {F P Q : ℂ} (K : ℕ) (hF : F ≠ 0) (hden : F - P ≠ 0) :
    Q / (F - P) =
      (Q / F) * resolventPartialSum (P / F) K +
        (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ := by
  have hxid : 1 - P / F = (F - P) / F := by
    field_simp [hF]
  have hx : 1 - P / F ≠ 0 := by
    rw [hxid]
    exact div_ne_zero hden hF
  have hres := inv_one_sub_eq_partial_add_tail K hx
  have hfactor : Q / (F - P) = (Q / F) * (1 - P / F)⁻¹ := by
    field_simp [hF, hden]
  calc
    Q / (F - P) = (Q / F) * (1 - P / F)⁻¹ := hfactor
    _ = (Q / F) *
        (resolventPartialSum (P / F) K + (P / F) ^ (K + 1) * (1 - P / F)⁻¹) :=
          congrArg (fun z => (Q / F) * z) hres
    _ = (Q / F) * resolventPartialSum (P / F) K +
        (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ := by ring

/-- The exact completed source decomposes into the finite HLP hierarchy plus a
single explicit tail. -/
theorem completedExactSource_eq_hlp_partial_add_tail
    {F P Q : ℂ} (K : ℕ) (hF : F ≠ 0) (hden : F - P ≠ 0) :
    RightEdgeArithmeticSource.completedExactSource F P Q =
      F - P + (Q / F) * resolventPartialSum (P / F) K +
        (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ := by
  unfold RightEdgeArithmeticSource.completedExactSource
  rw [quotient_eq_hlp_partial_add_tail K hF hden]
  ring

end HLPLocalModel
end ZetaZero
