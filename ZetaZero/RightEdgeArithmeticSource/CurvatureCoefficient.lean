import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Positive curvature coefficients on the right edge

The manuscript uses the exact coefficient identity

`sum_{ab=n} ((log b)^2 - log a * log b)
  = (1/2) * sum_{ab=n} (log a - log b)^2`.

This file proves the underlying finite factor-pair identity in a form that does
not depend on special properties of the logarithm.  Positivity of the actual
curvature coefficient is then immediate from the square representation.
-/

open scoped BigOperators

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Sum of a function over the ordered factor pairs `a*b=n`. -/
def factorPairSum (n : ℕ) (g : ℕ × ℕ → ℝ) : ℝ :=
  (n.divisorsAntidiagonalList.map g).sum

/-- The factor-pair list is invariant, at the level of sums, under swapping the
left and right divisor. -/
theorem factorPairSum_swap (n : ℕ) (g : ℕ × ℕ → ℝ) :
    factorPairSum n g = factorPairSum n (fun p => g p.swap) := by
  unfold factorPairSum
  calc
    (n.divisorsAntidiagonalList.map g).sum =
        (n.divisorsAntidiagonalList.reverse.map g).sum := by simp
    _ = ((n.divisorsAntidiagonalList.map Prod.swap).map g).sum := by
      rw [Nat.reverse_divisorsAntidiagonalList]
    _ = (n.divisorsAntidiagonalList.map (fun p => g p.swap)).sum := by
      simp [List.map_map, Function.comp_def]

/-- The sum of the left-square channel equals the sum of the right-square
channel on the factor antidiagonal. -/
theorem factorPairSum_left_sq_eq_right_sq
    (n : ℕ) (φ : ℕ → ℝ) :
    factorPairSum n (fun p => (φ p.1) ^ 2) =
      factorPairSum n (fun p => (φ p.2) ^ 2) := by
  simpa using factorPairSum_swap n (fun p => (φ p.1) ^ 2)

/-- The asymmetric convolution coefficient appearing in
`ζ ζ'' - (ζ')^2`. -/
def curvatureConvolutionCoeff (φ : ℕ → ℝ) (n : ℕ) : ℝ :=
  factorPairSum n (fun p => (φ p.2) ^ 2 - φ p.1 * φ p.2)

/-- The symmetric square-energy representation of the same coefficient. -/
def curvatureSquareCoeff (φ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * factorPairSum n (fun p => (φ p.1 - φ p.2) ^ 2)

/-- Pointwise algebra summed over an arbitrary finite list of factor pairs. -/
theorem curvature_list_decomposition
    (φ : ℕ → ℝ) (L : List (ℕ × ℕ)) :
    (L.map (fun p => (φ p.2) ^ 2 - φ p.1 * φ p.2)).sum =
      (1 / 2 : ℝ) * (L.map (fun p => (φ p.1 - φ p.2) ^ 2)).sum +
        (1 / 2 : ℝ) *
          ((L.map (fun p => (φ p.2) ^ 2)).sum -
            (L.map (fun p => (φ p.1) ^ 2)).sum) := by
  induction L with
  | nil => norm_num
  | cons p ps ih =>
      simp [ih]
      ring

/-- Pure factor-pair algebra behind the positive curvature coefficient. -/
theorem curvatureConvolutionCoeff_eq_squareCoeff
    (φ : ℕ → ℝ) (n : ℕ) :
    curvatureConvolutionCoeff φ n = curvatureSquareCoeff φ n := by
  unfold curvatureConvolutionCoeff curvatureSquareCoeff factorPairSum
  rw [curvature_list_decomposition]
  have hsq :
      (n.divisorsAntidiagonalList.map (fun p => (φ p.1) ^ 2)).sum =
        (n.divisorsAntidiagonalList.map (fun p => (φ p.2) ^ 2)).sum := by
    simpa [factorPairSum] using factorPairSum_left_sq_eq_right_sq n φ
  rw [← hsq]
  ring

/-- The square representation is nonnegative for every real factor weight. -/
theorem curvatureSquareCoeff_nonneg (φ : ℕ → ℝ) (n : ℕ) :
    0 ≤ curvatureSquareCoeff φ n := by
  unfold curvatureSquareCoeff factorPairSum
  refine mul_nonneg (by norm_num) ?_
  refine List.sum_nonneg fun x => ?_
  simp only [List.mem_map]
  rintro ⟨p, -, rfl⟩
  positivity

/-- Hence the asymmetric convolution coefficient is nonnegative as well. -/
theorem curvatureConvolutionCoeff_nonneg (φ : ℕ → ℝ) (n : ℕ) :
    0 ≤ curvatureConvolutionCoeff φ n := by
  rw [curvatureConvolutionCoeff_eq_squareCoeff]
  exact curvatureSquareCoeff_nonneg φ n

/-- Natural logarithm weight used by the right-edge Dirichlet source. -/
def logNat (n : ℕ) : ℝ := Real.log n

/-- The manuscript's curvature coefficient. -/
def curvatureCoeff (n : ℕ) : ℝ :=
  curvatureSquareCoeff logNat n

/-- Exact finite identity for the manuscript coefficient. -/
theorem curvatureCoeff_eq_convolution (n : ℕ) :
    curvatureCoeff n = curvatureConvolutionCoeff logNat n := by
  rw [curvatureConvolutionCoeff_eq_squareCoeff]
  rfl

/-- Positivity of the exact right-edge curvature coefficient. -/
theorem curvatureCoeff_nonneg (n : ℕ) : 0 ≤ curvatureCoeff n := by
  exact curvatureSquareCoeff_nonneg logNat n

end RightEdgeArithmeticSource
end ZetaZero
