import ZetaZero.HLPLocalModel.ConvolutionRecurrence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weighted Cauchy step for the HLP mean-square hierarchy

This module isolates the finite weighted Cauchy--Schwarz inequality used in the
factorial-majorant induction and applies it to one von-Mangoldt convolution step.
It deliberately stops before summing over `n`; the global mean-square recurrence
remains a separate analytic/arithmetic task.
-/

open Finset Nat
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Weighted finite Cauchy--Schwarz in the form used for von Mangoldt weights. -/
theorem weighted_sum_sq_le
    {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * a i) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (a i) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · exact hw
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg (a i))
  · intro i hi
    ring_nf
    exact le_rfl

/-- One exact HLP recurrence step followed by weighted Cauchy--Schwarz. -/
theorem hlpAlphaSucc_succ_sq_le_weighted (k n : ℕ) :
    (hlpAlphaSucc (k + 1) n) ^ 2 ≤
      (∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.1) *
        ∑ x ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
  rw [hlpAlphaSucc_succ_apply]
  exact weighted_sum_sq_le n.divisorsAntidiagonal
    (fun x => ArithmeticFunction.vonMangoldt x.1)
    (fun x => hlpAlphaSucc k x.2)
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- The total von-Mangoldt weight on a divisor antidiagonal is `log n`. -/
theorem sum_vonMangoldt_first_divisorsAntidiagonal (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.1) =
      Real.log n := by
  rw [Nat.sum_divisorsAntidiagonal (fun i _ => ArithmeticFunction.vonMangoldt i)]
  simpa using (ArithmeticFunction.vonMangoldt_sum (n := n))

/-- Weighted Cauchy with the first factor simplified to the classical `log n`. -/
theorem hlpAlphaSucc_succ_sq_le_log_weighted (k n : ℕ) :
    (hlpAlphaSucc (k + 1) n) ^ 2 ≤
      Real.log n *
        ∑ x ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt x.1 * (hlpAlphaSucc k x.2) ^ 2 := by
  simpa [sum_vonMangoldt_first_divisorsAntidiagonal] using
    hlpAlphaSucc_succ_sq_le_weighted k n

end HLPLocalModel
end ZetaZero
