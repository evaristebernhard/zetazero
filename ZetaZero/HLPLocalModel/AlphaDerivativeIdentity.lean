import ZetaZero.HLPLocalModel.ArithmeticHierarchy
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Logarithmic derivation identity for HLP coefficients

The manuscript uses

`α_k(n) = (log n / k) Λ_k(n)`.

Rather than compare analytic Dirichlet series, we prove the coefficient identity
purely algebraically.  Multiplication by `log n` is a derivation for Dirichlet
convolution because `log(ab)=log a + log b` on every divisor antidiagonal.
-/

open Finset Nat
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Pointwise logarithmic weight on an arithmetic function. -/
def arithmeticLogWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n * f n, by simp⟩

@[simp] theorem arithmeticLogWeight_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticLogWeight f n = Real.log n * f n := rfl

/-- Multiplication by `log n` satisfies the Leibniz rule for Dirichlet convolution. -/
theorem arithmeticLogWeight_mul (f g : ArithmeticFunction ℝ) :
    arithmeticLogWeight (f * g) =
      arithmeticLogWeight f * g + f * arithmeticLogWeight g := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [arithmeticLogWeight]
  · simp only [arithmeticLogWeight_apply, ArithmeticFunction.mul_apply,
      ArithmeticFunction.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hxprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx1ne : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    have hx2ne : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
    have hlog : Real.log n = Real.log x.1 + Real.log x.2 := by
      rw [← hxprod, Nat.cast_mul, Real.log_mul]
      · exact_mod_cast hx1ne
      · exact_mod_cast hx2ne
    rw [hlog]
    ring

/-- Power rule for the logarithmic derivation, indexed without subtraction.
The scalar is taken in the base field `ℝ`, so evaluation remains pointwise and
does not pass through the Dirichlet-convolution scalar action. -/
theorem arithmeticLogWeight_pow_succ (f : ArithmeticFunction ℝ) :
    ∀ k : ℕ,
      arithmeticLogWeight (f ^ (k + 1)) =
        (((k + 1 : ℕ) : ℝ)) • (f ^ k * arithmeticLogWeight f)
  | 0 => by simp [arithmeticLogWeight]
  | k + 1 => by
      rw [show f ^ (k + 1 + 1) = f ^ (k + 1) * f by rw [pow_succ]]
      rw [arithmeticLogWeight_mul, arithmeticLogWeight_pow_succ f k]
      rw [show f ^ (k + 1) = f ^ k * f by rw [pow_succ]]
      rw [smul_mul_assoc]
      have hbase :
          (f ^ k * arithmeticLogWeight f) * f =
            (f ^ k * f) * arithmeticLogWeight f := by
        ring
      rw [hbase]
      calc
        (((k + 1 : ℕ) : ℝ)) • ((f ^ k * f) * arithmeticLogWeight f) +
            (f ^ k * f) * arithmeticLogWeight f =
            (((k + 1 : ℕ) : ℝ)) • ((f ^ k * f) * arithmeticLogWeight f) +
              (1 : ℝ) • ((f ^ k * f) * arithmeticLogWeight f) := by rw [one_smul]
        _ = ((((k + 1 : ℕ) : ℝ)) + 1) •
              ((f ^ k * f) * arithmeticLogWeight f) := by rw [← add_smul]
        _ = (((k + 1 + 1 : ℕ) : ℝ)) •
              ((f ^ k * f) * arithmeticLogWeight f) := by
          congr 1
          push_cast
          ring

/-- The logarithmic weight of von Mangoldt is exactly the `Q=-P'` coefficient. -/
theorem arithmeticLogWeight_vonMangoldt :
    arithmeticLogWeight ArithmeticFunction.vonMangoldt = mangoldtLogCoefficient := by
  ext n
  simp [arithmeticLogWeight, mangoldtLogCoefficient, mul_comm]

/-- Arithmetic-function form of the manuscript derivative identity. -/
theorem logWeight_mangoldtConvolutionPower_succ (k : ℕ) :
    arithmeticLogWeight (mangoldtConvolutionPower (k + 1)) =
      (((k + 1 : ℕ) : ℝ)) • hlpAlphaSucc k := by
  simpa [mangoldtConvolutionPower, hlpAlphaSucc, arithmeticLogWeight_vonMangoldt]
    using arithmeticLogWeight_pow_succ ArithmeticFunction.vonMangoldt k

/-- Coefficient form: `(k+1) α_{k+1}(n) = log(n) Λ_{k+1}(n)`. -/
theorem cast_succ_mul_hlpAlphaSucc (k n : ℕ) :
    (((k + 1 : ℕ) : ℝ)) * hlpAlphaSucc k n =
      Real.log n * mangoldtConvolutionPower (k + 1) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (logWeight_mangoldtConvolutionPower_succ k)
  rw [arithmeticLogWeight_apply, ArithmeticFunction.smul_map] at h
  simpa [smul_eq_mul] using h.symm

/-- The manuscript identity `α_{k+1}(n) = log(n)/(k+1) * Λ_{k+1}(n)`. -/
theorem hlpAlphaSucc_eq_log_div_mangoldtPower (k n : ℕ) :
    hlpAlphaSucc k n =
      Real.log n / (((k + 1 : ℕ) : ℝ)) * mangoldtConvolutionPower (k + 1) n := by
  have h := cast_succ_mul_hlpAlphaSucc k n
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hk]
  simpa [mul_comm] using h

end HLPLocalModel
end ZetaZero
