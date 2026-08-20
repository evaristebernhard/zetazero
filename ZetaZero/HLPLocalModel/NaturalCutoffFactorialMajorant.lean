import ZetaZero.HLPLocalModel.AlphaSharpFactorialMajorant

/-!
# Natural-cutoff form of the HLP factorial majorant

The analytic proof is most convenient at the exponential cutoff
`floor(exp y)`.  The manuscript is stated with a natural cutoff `X`.  Setting
`y = log X` for `X ≥ 1` identifies the two exactly.
-/

open Finset Real
open scoped ArithmeticFunction BigOperators

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- The sharpened factorial majorant at an ordinary natural cutoff.

In the manuscript's notation this controls `α_{k+1}` on `n ≤ X`; the logarithmic
exponent is `2(k+1)+1 = 2k+3`. -/
theorem hlpAlpha_nat_factorial_majorant
    (k X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, (hlpAlphaSucc k n) ^ 2) ≤
      Zeta23.XiPrime.KM * factorialMajorantStepConstant ^ k /
          (k + 1).factorial *
        (X : ℝ) * (1 + Real.log X) ^ (2 * k + 3) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hy : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hmain := hlpAlphaSharpMeanSquareExp_factorial_majorant
    k (y := Real.log (X : ℝ)) hy
  have hexp : Real.exp (Real.log (X : ℝ)) = (X : ℝ) :=
    Real.exp_log hXpos
  have hfloor : ⌊Real.exp (Real.log (X : ℝ))⌋₊ = X := by
    rw [hexp]
    simp
  rw [lambda_Icc_one_eq_Ioc_zero]
  simpa [hlpAlphaSharpMeanSquareExp, hfloor, hexp] using hmain

end HLPLocalModel
end ZetaZero
