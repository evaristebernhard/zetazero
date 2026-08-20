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

/-- Exact source-model defect when the same slow factor is used in both the
exact and model sources. -/
def sourceDefect (F P Q Pshift : ℂ) : ℂ :=
  P + Q / (F - P) - Pshift

/-- Direct exact--model residual in the revised main proof.  Unlike
`sourceDefect`, its resolvent keeps the physical slow factor `f`; the finite
model may use a separately frozen value `F`. -/
def directExactModelResidual (f P Q Pshift : ℂ) : ℂ :=
  P + Q / (f - P) - Pshift

/-- The completed exact source is exactly model plus defect when both use the
same slow factor. -/
theorem completedExactSource_eq_model_add_defect
    (F P Q Pshift : ℂ) :
    completedExactSource F P Q =
      completedModelSource F P Pshift + sourceDefect F P Q Pshift := by
  unfold completedExactSource completedModelSource sourceDefect
  ring

/-- Authoritative source split for the revised unconditional route:

`exact = finite model + direct exact--model residual + self-freezing`.

This is a purely algebraic identity on the safe right edge.  In particular it
does not expand the exact resolvent around the frozen value `F`, so the whole
exact HLP hierarchy remains owned by the direct residual. -/
theorem completedExactSource_eq_model_add_directResidual_add_freezing
    (f F P Q Pshift : ℂ) :
    completedExactSource f P Q =
      completedModelSource F P Pshift + directExactModelResidual f P Q Pshift + (f - F) := by
  unfold completedExactSource completedModelSource directExactModelResidual
  ring

/-- The direct residual reduces to the older source defect when no separate
freezing value is introduced. -/
theorem directExactModelResidual_eq_sourceDefect
    (f P Q Pshift : ℂ) :
    directExactModelResidual f P Q Pshift = sourceDefect f P Q Pshift := by
  rfl

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

/-! ## Additive safe-edge interface

The generic additive version is the stable home of the former parallel
`SafeEdgeSourceSplit` experiment.  It lets the split pass through an arbitrary
additive contour/source operator before any field-valued realization is chosen.
-/

namespace SafeEdgeSourceSplit

section Additive

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def exactSource (f P R : A) : A := f - P + R
def finiteModel (F P Pshift : A) : A := F - P - P + Pshift
def directResidual (P R Pshift : A) : A := P + R - Pshift
def selfFreeze (f F : A) : A := f - F

theorem exact_eq_finiteModel_add_directResidual_add_selfFreeze
    (f F P Pshift R : A) :
    exactSource f P R =
      finiteModel F P Pshift + directResidual P R Pshift + selfFreeze f F := by
  simp [exactSource, finiteModel, directResidual, selfFreeze]
  abel

theorem map_exact_eq_split
    (Φ : A →+ B) (f F P Pshift R : A) :
    Φ (exactSource f P R) =
      Φ (finiteModel F P Pshift) +
        Φ (directResidual P R Pshift) + Φ (selfFreeze f F) := by
  rw [exact_eq_finiteModel_add_directResidual_add_selfFreeze f F P Pshift R]
  simp

theorem exact_sub_finiteModel_eq_directResidual_add_selfFreeze
    (f F P Pshift R : A) :
    exactSource f P R - finiteModel F P Pshift =
      directResidual P R Pshift + selfFreeze f F := by
  rw [exact_eq_finiteModel_add_directResidual_add_selfFreeze f F P Pshift R]
  abel

end Additive

section FieldValued

variable {𝕜 : Type*} [Field 𝕜]

def exactQuotientSource (f P Q : 𝕜) : 𝕜 := f - P + Q / (f - P)
def quotientDirectResidual (f P Pshift Q : 𝕜) : 𝕜 := P + Q / (f - P) - Pshift

theorem exactQuotientSource_eq_split
    (f F P Pshift Q : 𝕜) :
    exactQuotientSource f P Q =
      finiteModel F P Pshift + quotientDirectResidual f P Pshift Q + selfFreeze f F := by
  exact exact_eq_finiteModel_add_directResidual_add_selfFreeze
    f F P Pshift (Q / (f - P))

end FieldValued

end SafeEdgeSourceSplit

end RightEdgeArithmeticSource
end ZetaZero
