import ZetaZero.HLPLocalModel.WeightedCauchy
import ZetaZero.HLPLocalModel.LambdaMeanSquareRecurrence
import ZetaZero.HLPLocalModel.WeightedChebyshev
import ZetaZero.HLPLocalModel.FactorialMajorant
import ZetaZero.HLPLocalModel.FactorialInduction
import ZetaZero.HLPLocalModel.AlphaDerivativeIdentity
import ZetaZero.HLPLocalModel.AlphaSharpFactorialMajorant
import ZetaZero.HLPLocalModel.NaturalCutoffFactorialMajorant
import ZetaZero.HLPLocalModel.NormalizedDirectCarrier
import ZetaZero.HLPLocalModel.FiniteLevelMinkowski
import ZetaZero.HLPLocalModel.FactorialLevelSummability
import ZetaZero.HLPLocalModel.FiniteCarrierAssembly
import ZetaZero.HLPLocalModel.DirectCarrierAssembly
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Zeta23.FromPNTPlus.Mertens

/-!
# Finite mean-square recurrence for the HLP hierarchy

This module starts the global part of the factorial-majorant argument.  The
pointwise weighted recurrence from `WeightedCauchy` is summed over a finite
initial segment, but no asymptotic estimate is inserted here.
-/

open Finset Nat
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Finite mean square of the `k`th HLP coefficient level on `1 ≤ n ≤ X`. -/
def hlpMeanSquare (k X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, (hlpAlphaSucc k n) ^ 2

/-- The square of one HLP level, packaged as an arithmetic function so that
Mathlib's finite Dirichlet-convolution summation identities can be reused. -/
def hlpAlphaSquare (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (hlpAlphaSucc k n) ^ 2, by simp⟩

@[simp] theorem hlpAlphaSquare_apply (k n : ℕ) :
    hlpAlphaSquare k n = (hlpAlphaSucc k n) ^ 2 := rfl

/-- On natural numbers, `1 ≤ n ≤ X` is the same finite interval as
`0 < n ≤ X`. -/
theorem Icc_one_eq_Ioc_zero (X : ℕ) : Finset.Icc 1 X = Finset.Ioc 0 X := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- The finite mean square written on Mathlib's standard positive interval. -/
theorem hlpMeanSquare_eq_sum_Ioc (k X : ℕ) :
    hlpMeanSquare k X = ∑ n ∈ Finset.Ioc 0 X, (hlpAlphaSucc k n) ^ 2 := by
  rw [hlpMeanSquare, Icc_one_eq_Ioc_zero]

/-- The pointwise weighted Cauchy recurrence summed over `1 ≤ n ≤ X`.

This is the first genuinely global step in the factorial-majorant chain: the
remaining work is to rearrange the divisor-antidiagonal sum and estimate its
logarithmic weight. -/
theorem hlpMeanSquare_succ_le_log_antidiagonal (k X : ℕ) :
    hlpMeanSquare (k + 1) X ≤
      ∑ n ∈ Finset.Icc 1 X,
        Real.log n *
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
  unfold hlpMeanSquare
  exact Finset.sum_le_sum fun n hn => hlpAlphaSucc_succ_sq_le_log_weighted k n

/-- A version exposing the outer logarithmic weight as the uniform bound
`log X`.  This step is deliberately elementary and uses only monotonicity of
`Real.log`; it leaves the divisor-antidiagonal sum untouched. -/
theorem hlpMeanSquare_succ_le_logX_antidiagonal (k X : ℕ) :
    hlpMeanSquare (k + 1) X ≤
      Real.log X *
        ∑ n ∈ Finset.Icc 1 X,
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
  calc
    hlpMeanSquare (k + 1) X ≤
        ∑ n ∈ Finset.Icc 1 X,
          Real.log n *
            ∑ x ∈ n.divisorsAntidiagonal,
              ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 :=
      hlpMeanSquare_succ_le_log_antidiagonal k X
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
          Real.log X *
            ∑ x ∈ n.divisorsAntidiagonal,
              ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hXpos : (0 : ℝ) < (X : ℝ) := by
        exact lt_of_lt_of_le hnpos (by exact_mod_cast hnX)
      have hlog : Real.log n ≤ Real.log X := by
        exact Real.strictMonoOn_log.monotoneOn hnpos hXpos (by exact_mod_cast hnX)
      have hnonneg :
          0 ≤ ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
        refine Finset.sum_nonneg ?_
        intro x hx
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hlog hnonneg
    _ = Real.log X *
        ∑ n ∈ Finset.Icc 1 X,
          ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
      rw [Finset.mul_sum]

/-- Exact rearrangement of the finite divisor-antidiagonal sum.  This is the
finite Dirichlet-hyperbola identity needed by the factorial-majorant induction:
the outer convolution variable becomes a Mangoldt-weighted sum of lower-level
mean squares at the shortened range `X / a`. -/
theorem hlp_antidiagonal_sum_eq_mangoldt_meanSquare (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
      ∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2) =
      ∑ a ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt a * hlpMeanSquare k (X / a) := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    ArithmeticFunction.vonMangoldt (hlpAlphaSquare k) X
  simpa [ArithmeticFunction.mul_apply, hlpAlphaSquare_apply,
    hlpMeanSquare_eq_sum_Ioc, Icc_one_eq_Ioc_zero] using h

/-- Global finite HLP mean-square recurrence after divisor-sum rearrangement. -/
theorem hlpMeanSquare_succ_le_logX_mangoldt (k X : ℕ) :
    hlpMeanSquare (k + 1) X ≤
      Real.log X *
        ∑ a ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt a * hlpMeanSquare k (X / a) := by
  calc
    hlpMeanSquare (k + 1) X ≤
        Real.log X *
          ∑ n ∈ Finset.Icc 1 X,
            ∑ x ∈ n.divisorsAntidiagonal,
              ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 :=
      hlpMeanSquare_succ_le_logX_antidiagonal k X
    _ = Real.log X *
        ∑ a ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt a * hlpMeanSquare k (X / a) := by
      rw [hlp_antidiagonal_sum_eq_mangoldt_meanSquare]

/-- The Mertens input needed to turn the convolution recurrence into a
logarithmic induction.  This is imported from the vendored `Zeta23` proof, not
assumed: for `X ≥ 1`, the harmonic Mangoldt weight is at most
`log X + log 4 + 4`. -/
theorem sum_vonMangoldt_div_le_log_add_const {X : ℕ} (hX : 1 ≤ X) :
    (∑ a ∈ Finset.Icc 1 X,
      ArithmeticFunction.vonMangoldt a / (a : ℝ)) ≤
      Real.log X + (Real.log 4 + 4) := by
  have h := Mertens.sum_mangoldt_div_eq_log (x := (X : ℝ)) (by exact_mod_cast hX)
  have hupper :
      (∑ a ∈ Finset.Ioc 0 X,
        ArithmeticFunction.vonMangoldt a / (a : ℝ)) - Real.log X ≤
        Real.log 4 + 4 := by
    simpa using (le_trans (le_abs_self _) h)
  rw [Icc_one_eq_Ioc_zero]
  linarith

/-- One-step propagation of a linear mean-square majorant through the HLP
convolution recurrence.  The only analytic number theory used here is the
proved Mertens bound above. -/
theorem hlpMeanSquare_succ_le_of_linear_majorant
    {k X : ℕ} {C : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hmajor : ∀ Y ≤ X, hlpMeanSquare k Y ≤ C * (Y : ℝ)) :
    hlpMeanSquare (k + 1) X ≤
      Real.log X *
        (C * (X : ℝ) * (Real.log X + (Real.log 4 + 4))) := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  calc
    hlpMeanSquare (k + 1) X ≤
        Real.log X *
          ∑ a ∈ Finset.Icc 1 X,
            ArithmeticFunction.vonMangoldt a * hlpMeanSquare k (X / a) :=
      hlpMeanSquare_succ_le_logX_mangoldt k X
    _ ≤ Real.log X *
        ∑ a ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt a * (C * ((X / a : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hlog
      refine Finset.sum_le_sum ?_
      intro a ha
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      exact hmajor (X / a) (Nat.div_le_self X a)
    _ ≤ Real.log X *
        ∑ a ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt a * (C * ((X : ℝ) / (a : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hlog
      refine Finset.sum_le_sum ?_
      intro a ha
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      exact mul_le_mul_of_nonneg_left (Nat.cast_div_le (m := X) (n := a)) hC
    _ = Real.log X *
        (C * (X : ℝ) *
          ∑ a ∈ Finset.Icc 1 X,
            ArithmeticFunction.vonMangoldt a / (a : ℝ)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ Real.log X *
        (C * (X : ℝ) * (Real.log X + (Real.log 4 + 4))) := by
      apply mul_le_mul_of_nonneg_left _ hlog
      apply mul_le_mul_of_nonneg_left
      · exact sum_vonMangoldt_div_le_log_add_const hX
      · exact mul_nonneg hC (by positivity)

end HLPLocalModel
end ZetaZero
