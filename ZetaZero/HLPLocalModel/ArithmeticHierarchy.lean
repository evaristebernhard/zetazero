import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Arithmetic support of the HLP convolution hierarchy

This is the first purely arithmetic layer of M05.  Dirichlet convolution powers
of the von Mangoldt function are represented by Mathlib's `ArithmeticFunction`
ring.  The key support fact used in the manuscript is formalized independently
of any contour or stationary-phase argument:

`Λ^[k](n) ≠ 0  ->  2^k ≤ n`.

This support estimate is what makes logarithmic-uniform estimates in the HLP
level `k` compatible with the finite Dirichlet range.
-/

open Finset Nat
open scoped ArithmeticFunction

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- The `k`-fold Dirichlet convolution of the von Mangoldt function. -/
def mangoldtConvolutionPower (k : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt ^ k

@[simp] theorem mangoldtConvolutionPower_zero :
    mangoldtConvolutionPower 0 = (1 : ArithmeticFunction ℝ) := by
  simp [mangoldtConvolutionPower]

@[simp] theorem mangoldtConvolutionPower_succ (k : ℕ) :
    mangoldtConvolutionPower (k + 1) =
      mangoldtConvolutionPower k * ArithmeticFunction.vonMangoldt := by
  simp [mangoldtConvolutionPower, pow_succ, mul_comm]

/-- Dirichlet convolution multiplies lower support bounds: if nonzero values of
`f` occur only at indices at least `A`, and nonzero values of `g` occur only at
indices at least `B`, then nonzero values of `f * g` occur only at indices at
least `A * B`. -/
theorem dirichletConvolution_support_lower_bound
    {f g : ArithmeticFunction ℝ} {A B n : ℕ}
    (hf : ∀ {m : ℕ}, f m ≠ 0 → A ≤ m)
    (hg : ∀ {m : ℕ}, g m ≠ 0 → B ≤ m)
    (hfg : (f * g) n ≠ 0) :
    A * B ≤ n := by
  have hsum :
      (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2) ≠ 0 := by
    simpa [ArithmeticFunction.mul_apply] using hfg
  have hex : ∃ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2 ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hsum
    exact Finset.sum_eq_zero fun x hx => hnone x hx
  obtain ⟨x, hx, hxne⟩ := hex
  have hx1 : A ≤ x.1 := hf (left_ne_zero_of_mul hxne)
  have hx2 : B ≤ x.2 := hg (right_ne_zero_of_mul hxne)
  have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  calc
    A * B ≤ x.1 * x.2 := Nat.mul_le_mul hx1 hx2
    _ = n := hprod

/-- Nonzero coefficients of the `k`-fold Mangoldt convolution are supported on
integers at least `2^k`. -/
theorem mangoldtConvolutionPower_support
    {k n : ℕ} (h : mangoldtConvolutionPower k n ≠ 0) :
    2 ^ k ≤ n := by
  induction k generalizing n with
  | zero =>
      have hn : n = 1 := by
        simpa [mangoldtConvolutionPower, ArithmeticFunction.one_apply] using h
      simp [hn]
  | succ k ih =>
      have hsum :
          (∑ x ∈ n.divisorsAntidiagonal,
            mangoldtConvolutionPower k x.1 * ArithmeticFunction.vonMangoldt x.2) ≠ 0 := by
        simpa [mangoldtConvolutionPower, pow_succ, ArithmeticFunction.mul_apply] using h
      have hex : ∃ x ∈ n.divisorsAntidiagonal,
          mangoldtConvolutionPower k x.1 * ArithmeticFunction.vonMangoldt x.2 ≠ 0 := by
        by_contra hnone
        push Not at hnone
        apply hsum
        exact Finset.sum_eq_zero fun x hx => hnone x hx
      obtain ⟨x, hx, hxne⟩ := hex
      have hk : mangoldtConvolutionPower k x.1 ≠ 0 :=
        left_ne_zero_of_mul hxne
      have hΛ : ArithmeticFunction.vonMangoldt x.2 ≠ 0 :=
        right_ne_zero_of_mul hxne
      have hx1 : 2 ^ k ≤ x.1 := ih hk
      have hx2 : 2 ≤ x.2 := by
        exact (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ).one_lt
      have hprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
      calc
        2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
        _ ≤ x.1 * x.2 := Nat.mul_le_mul hx1 hx2
        _ = n := hprod

/-- Contrapositive support form used to truncate the HLP hierarchy at a fixed
Dirichlet index. -/
theorem mangoldtConvolutionPower_eq_zero_of_lt
    {k n : ℕ} (h : n < 2 ^ k) :
    mangoldtConvolutionPower k n = 0 := by
  by_contra hne
  exact (not_le_of_gt h) (mangoldtConvolutionPower_support hne)

/-- Coefficient sequence of the safe-line factor `Q=-P'`:
`Q(n)=Λ(n) log n`. -/
def mangoldtLogCoefficient : ArithmeticFunction ℝ :=
  ⟨fun n => ArithmeticFunction.vonMangoldt n * Real.log n, by simp⟩

/-- The HLP level indexed by `k+1`, i.e. the coefficient sequence of
`P^k Q`.  Using a successor index avoids an artificial level zero. -/
def hlpAlphaSucc (k : ℕ) : ArithmeticFunction ℝ :=
  mangoldtConvolutionPower k * mangoldtLogCoefficient

/-- A nonzero `Q` coefficient is supported on integers at least two. -/
theorem mangoldtLogCoefficient_support {n : ℕ}
    (h : mangoldtLogCoefficient n ≠ 0) : 2 ≤ n := by
  have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hz
    apply h
    simp [mangoldtLogCoefficient, hz]
  exact (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ).one_lt

/-- Support of the actual HLP level `P^k Q`: a nonzero coefficient at level
`k+1` forces `n ≥ 2^(k+1)`. -/
theorem hlpAlphaSucc_support {k n : ℕ} (h : hlpAlphaSucc k n ≠ 0) :
    2 ^ (k + 1) ≤ n := by
  rw [pow_succ]
  exact dirichletConvolution_support_lower_bound
    (fun hm => mangoldtConvolutionPower_support hm)
    (fun hm => mangoldtLogCoefficient_support hm) h

/-- Contrapositive support form for the actual HLP coefficient level `P^k Q`. -/
theorem hlpAlphaSucc_eq_zero_of_lt {k n : ℕ} (h : n < 2 ^ (k + 1)) :
    hlpAlphaSucc k n = 0 := by
  by_contra hne
  exact (not_le_of_gt h) (hlpAlphaSucc_support hne)

end HLPLocalModel
end ZetaZero
