import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Algebra of the completed right-edge source

This file isolates the exact rational identities behind the manuscript's
right-edge source.  No zeta-function, contour, or asymptotic input appears here.
The difficult analytic stages may therefore treat these identities as fixed
interfaces rather than redoing the source algebra inside estimates.
-/

open Complex

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Completed frozen right-edge source
`F - P + Q / (F - P)`. -/
def completedExactSource (F P Q : ℂ) : ℂ :=
  F - P + Q / (F - P)

/-- Two-master comparison source `F - 2P + Pshift`. -/
def completedModelSource (F P Pshift : ℂ) : ℂ :=
  F - 2 * P + Pshift

/-- Exact source-model defect. -/
def sourceDefect (F P Q Pshift : ℂ) : ℂ :=
  P + Q / (F - P) - Pshift

/-- The completed exact source is exactly model plus defect. -/
theorem completedExactSource_eq_model_add_defect
    (F P Q Pshift : ℂ) :
    completedExactSource F P Q =
      completedModelSource F P Pshift + sourceDefect F P Q Pshift := by
  unfold completedExactSource completedModelSource sourceDefect
  ring

/-- Exact slow-factor freezing identity.  The error caused by replacing `f` by
`F` factors through the scalar difference `f-F`. -/
theorem completedExactSource_sub_frozen
    {f F P Q : ℂ} (hf : f - P ≠ 0) (hF : F - P ≠ 0) :
    completedExactSource f P Q - completedExactSource F P Q =
      (f - F) * (1 - Q / ((f - P) * (F - P))) := by
  unfold completedExactSource
  field_simp [hf, hF]
  ring

/-- Equivalent additive form of the freezing error, useful before factoring the
slow variation. -/
theorem completedExactSource_sub_frozen_additive
    {f F P Q : ℂ} (hf : f - P ≠ 0) (hF : F - P ≠ 0) :
    completedExactSource f P Q - completedExactSource F P Q =
      (f - F) + Q * ((f - P)⁻¹ - (F - P)⁻¹) := by
  unfold completedExactSource
  field_simp [hf, hF]
  ring

/-- Exact source-ledger separation of the archimedean derivative terms.  The
principal product is `C * H`; every remaining summand contains at least one
factor `fp`, matching the manuscript's `f'` remainder ownership. -/
theorem derivativeSource_separation
    (C Z H fp D : ℂ) :
    (C + fp * Z) * (H + fp / D) =
      C * H + (fp * Z * H + (fp / D) * C + (fp ^ 2 / D) * Z) := by
  field_simp
  ring

end RightEdgeArithmeticSource
end ZetaZero
