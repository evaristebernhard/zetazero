import ZetaZero.DivisorGramArithmeticTransfer.GcdGramIdentity
import Mathlib.Tactic

/-!
# Concrete operator-valued gcd Gram lift

Section 09 uses the arithmetic kernel `gcd(m,n)/(mn)` after packet/divisor
translations.  `GcdGramIdentity` already identifies this scalar kernel with a
finite totient-weighted Gram system.  This file records the concrete
operator-valued consequence: after arbitrary labelled linear maps `U n`, the
resulting quadratic form is still a sum of squared divisor channels.

No isometry or unitarity hypothesis on `U n` is needed for positivity.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace ZetaZero
namespace DivisorGramArithmeticTransfer

section Hilbert

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The Hilbert-valued family obtained after applying the labelled maps and
scalar packet coefficients. -/
def operatorGcdFamily {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W) (v : V) :
    DivisorIndex Y → W :=
  fun n => a n • U n v

/-- The concrete operator-valued gcd quadratic form. -/
def operatorGcdForm {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W) (v : V) : ℂ :=
  gcdHilbertForm (operatorGcdFamily a U v)

/-- The form expands to the literal gcd kernel coupled to the translated
vectors `U n v`. -/
theorem operatorGcdForm_eq_explicit {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W) (v : V) :
    operatorGcdForm a U v =
      ∑ m : DivisorIndex Y, ∑ n : DivisorIndex Y,
        conj (a m) * a n *
          ((Nat.gcd m.1 n.1 : ℂ) / ((m.1 : ℂ) * (n.1 : ℂ))) *
          inner ℂ (U m v) (U n v) := by
  unfold operatorGcdForm gcdHilbertForm operatorGcdFamily
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  simp only [inner_smul_left, inner_smul_right]
  ring

/-- The `d`-th divisor channel of the operator-valued family. -/
def operatorGcdChannel {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W)
    (v : V) (d : ℕ) : W :=
  gcdDivisorChannel (operatorGcdFamily a U v) d

/-- Exact Gram-channel decomposition of the operator-valued gcd form. -/
theorem operatorGcdForm_eq_sum_inner_channels {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W) (v : V) :
    operatorGcdForm a U v =
      ∑ d ∈ Finset.Icc 1 Y,
        inner ℂ (operatorGcdChannel a U v d) (operatorGcdChannel a U v d) := by
  simpa [operatorGcdForm, operatorGcdChannel] using
    (gcdHilbertForm_eq_sum_inner_channels (operatorGcdFamily a U v))

/-- Real quadratic-form version: the concrete operator-valued gcd kernel is a
totient-weighted sum of squared unweighted divisor tails. -/
theorem operatorGcdForm_re_eq_totient_norm_sum {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W) (v : V) :
    (operatorGcdForm a U v).re =
      ∑ d ∈ Finset.Icc 1 Y,
        (Nat.totient d : ℝ) *
          ‖divisorTailChannel (operatorGcdFamily a U v) d‖ ^ 2 := by
  simpa [operatorGcdForm] using
    (gcdHilbertForm_re_eq_totient_norm_sum (operatorGcdFamily a U v))

/-- Concrete operator-valued positivity for the gcd kernel. -/
theorem operatorGcdForm_re_nonnegative {Y : ℕ}
    (a : DivisorIndex Y → ℂ) (U : DivisorIndex Y → V →ₗ[ℂ] W) (v : V) :
    0 ≤ (operatorGcdForm a U v).re := by
  exact gcdHilbertForm_re_nonnegative (operatorGcdFamily a U v)

end Hilbert

end DivisorGramArithmeticTransfer
end ZetaZero
