import ZetaZero.HLPLocalModel.ArithmeticHierarchy

/-!
# Convolution recurrence for HLP coefficients

The uniform HLP estimates are ultimately inductive in the hierarchy level.  This
module isolates the exact recurrence `P^(k+1) Q = Lambda * (P^k Q)` and its
coefficient-level divisor-antidiagonal form.  Later mean-square/factorial bounds
can build on this without reopening the arithmetic-function algebra.
-/

open Finset Nat
open scoped ArithmeticFunction

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Successive HLP levels satisfy the exact von-Mangoldt convolution recurrence. -/
theorem hlpAlphaSucc_succ (k : ℕ) :
    hlpAlphaSucc (k + 1) = ArithmeticFunction.vonMangoldt * hlpAlphaSucc k := by
  unfold hlpAlphaSucc mangoldtConvolutionPower
  rw [pow_succ]
  ac_rfl

/-- Coefficient form of the HLP recurrence, indexed by divisor-antidiagonal
factorizations `ab=n`. -/
theorem hlpAlphaSucc_succ_apply (k n : ℕ) :
    hlpAlphaSucc (k + 1) n =
      ∑ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt x.1 * hlpAlphaSucc k x.2 := by
  rw [hlpAlphaSucc_succ, ArithmeticFunction.mul_apply]

/-- Symmetric coefficient form, useful when the inductive level is placed on the
first divisor coordinate. -/
theorem hlpAlphaSucc_succ_apply_symm (k n : ℕ) :
    hlpAlphaSucc (k + 1) n =
      ∑ x ∈ n.divisorsAntidiagonal,
        hlpAlphaSucc k x.1 * ArithmeticFunction.vonMangoldt x.2 := by
  have hrec : hlpAlphaSucc (k + 1) =
      hlpAlphaSucc k * ArithmeticFunction.vonMangoldt := by
    rw [hlpAlphaSucc_succ, mul_comm]
  rw [hrec, ArithmeticFunction.mul_apply]

end HLPLocalModel
end ZetaZero
