import ZetaZero.RightEdgeArithmeticSource.SourceAlgebra
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

/-!
# Quantitative freezing bounds for the completed right-edge source

The exact algebraic freezing identity is already contained in `SourceAlgebra`.
This file turns it into the norm inequalities used by the blockwise stationary
analysis.  No asymptotic estimate is assumed here: the caller supplies a bound
for the slow variation `‖f-F‖` and for the frozen resolvent factor.
-/

open Complex

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Exact norm form of the slow-factor freezing identity. -/
theorem norm_completedExactSource_sub_frozen
    {f F P Q : ℂ} (hf : f - P ≠ 0) (hF : F - P ≠ 0) :
    ‖completedExactSource f P Q - completedExactSource F P Q‖ =
      ‖f - F‖ * ‖1 - Q / ((f - P) * (F - P))‖ := by
  rw [completedExactSource_sub_frozen hf hF, norm_mul]

/-- The exact freezing error is bounded by the slow variation times one plus
one resolvent factor. -/
theorem norm_completedExactSource_sub_frozen_le
    {f F P Q : ℂ} (hf : f - P ≠ 0) (hF : F - P ≠ 0) :
    ‖completedExactSource f P Q - completedExactSource F P Q‖ ≤
      ‖f - F‖ * (1 + ‖Q / ((f - P) * (F - P))‖) := by
  rw [norm_completedExactSource_sub_frozen hf hF]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa using
    (norm_sub_le (1 : ℂ) (Q / ((f - P) * (F - P))))

/-- Blockwise freezing estimate with explicit caller-supplied variation and
resolvent bounds. -/
theorem norm_completedExactSource_sub_frozen_le_of_bounds
    {f F P Q : ℂ} {η M : ℝ}
    (hf : f - P ≠ 0) (hF : F - P ≠ 0)
    (hη : 0 ≤ η)
    (hvar : ‖f - F‖ ≤ η)
    (hres : ‖Q / ((f - P) * (F - P))‖ ≤ M) :
    ‖completedExactSource f P Q - completedExactSource F P Q‖ ≤
      η * (1 + M) := by
  calc
    ‖completedExactSource f P Q - completedExactSource F P Q‖ ≤
        ‖f - F‖ * (1 + ‖Q / ((f - P) * (F - P))‖) :=
      norm_completedExactSource_sub_frozen_le hf hF
    _ ≤ η * (1 + M) := by
      apply mul_le_mul hvar
      · linarith
      · positivity
      · exact hη

/-- The same freezing estimate after multiplication by an arbitrary curvature
or packet amplitude.  This is the form used at the integrand level. -/
theorem norm_mul_completedExactSource_sub_frozen_le_of_bounds
    {C f F P Q : ℂ} {η M : ℝ}
    (hf : f - P ≠ 0) (hF : F - P ≠ 0)
    (hη : 0 ≤ η)
    (hvar : ‖f - F‖ ≤ η)
    (hres : ‖Q / ((f - P) * (F - P))‖ ≤ M) :
    ‖C * (completedExactSource f P Q - completedExactSource F P Q)‖ ≤
      ‖C‖ * (η * (1 + M)) := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg C)
  exact norm_completedExactSource_sub_frozen_le_of_bounds
    hf hF hη hvar hres

end RightEdgeArithmeticSource
end ZetaZero
