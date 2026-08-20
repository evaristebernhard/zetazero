import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite-model scalar-functional Fubini lift

This file formalizes the dimension-free linearity/Fubini mechanism used by the
revised main proof for the *finite model only*.

The analytic HLZ contour calculation is represented here by a continuous linear
map `L`.  Packet labels occur only through the scalar one-sided coefficient

`b_s(t) * conj (b_r(t))`,

while all Cauchy-shift/Mellin dependence is contained in one common carrier
`c t`.  The Bochner integral can therefore be passed through `L` before packet
assembly.  The same statement applies to the scalar contour error because an
error defined as `exact - principal` is itself a continuous linear map.

No zeta-function or HLZ estimate is asserted in this file; it isolates the
functional-analytic interface needed to lift such a scalar theorem without an
entrywise packet-valued hypothesis.
-/

open Complex MeasureTheory

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

variable {α ι E F : Type*}
  [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The one-sided packet-pair coefficient on a fibre.  Packet indices occur
only here; the common analytic carrier is kept separate. -/
def packetPairCoefficient (b : ι → α → ℂ) (r s : ι) (t : α) : ℂ :=
  b s t * star (b r t)

/-- A packet pair inserted into a common vector-valued analytic carrier. -/
def packetWeightedCarrier
    (b : ι → α → ℂ) (r s : ι) (c : α → E) (t : α) : E :=
  packetPairCoefficient b r s t • c t

/-- A continuous scalar functional commutes with the packet fibre integral.
This is the abstract Fubini step behind `lem:model-HLZ-Fubini-lift`: after the
scalar functional is applied fibrewise, the packet coefficient remains an
external scalar multiplier. -/
theorem continuousLinearMap_packetIntegral
    [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (b : ι → α → ℂ) (r s : ι) (c : α → E)
    (μ : Measure α)
    (hInt : Integrable (packetWeightedCarrier b r s c) μ) :
    L (∫ t, packetWeightedCarrier b r s c t ∂μ) =
      ∫ t, packetPairCoefficient b r s t • L (c t) ∂μ := by
  rw [← L.integral_comp_comm hInt]
  apply integral_congr_ae
  filter_upwards with t
  simp [packetWeightedCarrier]

/-- The scalar HLZ error functional, defined exactly as completed quantity minus
principal diagonal quantity.  Linearity is inherited automatically. -/
def scalarFunctionalError (T D : E →L[ℂ] F) : E →L[ℂ] F :=
  T - D

/-- Pointwise meaning of the scalar error functional. -/
theorem scalarFunctionalError_apply
    (T D : E →L[ℂ] F) (x : E) :
    scalarFunctionalError T D x = T x - D x := by
  rfl

/-- The scalar error therefore has the same packet/Fubini lift as the main
functional, without any vector-valued global error theorem. -/
theorem scalarFunctionalError_packetIntegral
    [CompleteSpace E] [CompleteSpace F]
    (T D : E →L[ℂ] F) (b : ι → α → ℂ) (r s : ι) (c : α → E)
    (μ : Measure α)
    (hInt : Integrable (packetWeightedCarrier b r s c) μ) :
    scalarFunctionalError T D (∫ t, packetWeightedCarrier b r s c t ∂μ) =
      ∫ t, packetPairCoefficient b r s t • scalarFunctionalError T D (c t) ∂μ := by
  exact continuousLinearMap_packetIntegral (scalarFunctionalError T D) b r s c μ hInt

/-- Finite linear combinations of inserted auxiliary weights preserve the error
identity.  This is the algebraic form used when taking finitely many Cauchy
residues/shift derivatives after the scalar deformation. -/
theorem scalarFunctionalError_add_smul
    (T D : E →L[ℂ] F) (a d : ℂ) (x y : E) :
    scalarFunctionalError T D (a • x + d • y) =
      a • scalarFunctionalError T D x + d • scalarFunctionalError T D y := by
  simp only [scalarFunctionalError_apply, map_add, map_smul]

end RightEdgeArithmeticSource
end ZetaZero
