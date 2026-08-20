import ZetaZero.HardyGaugeInvariantContourForm.HighRectangle
import ZetaZero.HardyGaugeInvariantContourForm.BranchReflection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite entire packets and holomorphic polarization

The contour form only needs a small analytic interface from the packet family:
finite linear combinations are entire, the Schwarz sharp

`B♯(z) = conj (B (conj z))`

is entire whenever `B` is entire, and therefore the manuscript polarization
`B_w(z(s)) B_v♯(z(s))` is analytic in the contour variable `s`.
-/

open Complex Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Finite packet superposition with coefficient vector `v`. -/
def packetSum {ι : Type*} [Fintype ι]
    (ψ : ι → ℂ → ℂ) (v : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ ν, v ν * ψ ν z

/-- A finite linear combination of entire packets is complex differentiable
everywhere. -/
theorem differentiable_packetSum
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν)) (v : ι → ℂ) :
    Differentiable ℂ (packetSum ψ v) := by
  intro z
  unfold packetSum
  exact DifferentiableAt.fun_sum fun ν _ =>
    (differentiableAt_const (v ν)).mul (hψ ν z)

/-- Schwarz sharp of an entire packet function. -/
def sharp (B : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (B ((starRingEnd ℂ) z))

/-- Schwarz sharp preserves complex differentiability. -/
theorem differentiable_sharp {B : ℂ → ℂ} (hB : Differentiable ℂ B) :
    Differentiable ℂ (sharp B) := by
  intro z
  change DifferentiableAt ℂ
    ((starRingEnd ℂ) ∘ B ∘ (starRingEnd ℂ)) z
  exact differentiableAt_conj_conj_iff.mpr (hB ((starRingEnd ℂ) z))

/-- Straightening coordinate from the `s`-plane to the Hardy `z`-plane. -/
def contourCoordinate (s : ℂ) : ℂ := -I * (s - (1 / 2 : ℂ))

/-- Straightening commutes with reflection across the critical line: the
conjugate-reflected spectral coordinate is the complex conjugate coordinate.
This is the coordinate identity needed before taking an adjoint of a packet
boundary integral. -/
@[simp] theorem contourCoordinate_hardyReflect (s : ℂ) :
    contourCoordinate (hardyReflect s) = (starRingEnd ℂ) (contourCoordinate s) := by
  unfold contourCoordinate hardyReflect
  simp [map_inv₀, map_ofNat]
  ring

/-- The Schwarz sharp of a function evaluated at a conjugate point is the
conjugate of the original function. -/
@[simp] theorem sharp_conj (B : ℂ → ℂ) (z : ℂ) :
    sharp B ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B z) := by
  unfold sharp
  simp

/-- The contour straightening map is entire. -/
theorem differentiable_contourCoordinate : Differentiable ℂ contourCoordinate := by
  unfold contourCoordinate
  fun_prop

/-- Paper-facing holomorphic packet polarization
`B_w(z(s)) B_v♯(z(s))`. -/
def packetPolarization {ι : Type*} [Fintype ι]
    (ψ : ι → ℂ → ℂ) (v w : ι → ℂ) (s : ℂ) : ℂ :=
  packetSum ψ w (contourCoordinate s) *
    sharp (packetSum ψ v) (contourCoordinate s)

/- The packet polarization has the reflected-adjoint symmetry used by the
paper's Hermitian contour form.  No analyticity assumption is needed here;
analyticity is supplied separately by `differentiable_packetPolarization`. -/
@[simp] theorem packetPolarization_hardyReflect_swap
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ}
    (v w : ι → ℂ) (s : ℂ) :
    packetPolarization ψ w v (hardyReflect s) =
      (starRingEnd ℂ) (packetPolarization ψ v w s) := by
  unfold packetPolarization
  rw [contourCoordinate_hardyReflect, sharp_conj]
  simp [sharp, map_mul, mul_comm]

/-- The packet polarization is entire in the contour variable whenever every
packet is entire. -/
theorem differentiable_packetPolarization
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν)) (v w : ι → ℂ) :
    Differentiable ℂ (packetPolarization ψ v w) := by
  have hw : Differentiable ℂ (packetSum ψ w) := differentiable_packetSum hψ w
  have hv : Differentiable ℂ (sharp (packetSum ψ v)) :=
    differentiable_sharp (differentiable_packetSum hψ v)
  intro s
  unfold packetPolarization
  exact ((hw (contourCoordinate s)).comp s (differentiable_contourCoordinate s)).mul
    ((hv (contourCoordinate s)).comp s (differentiable_contourCoordinate s))

/-- The packet polarization is analytic on every set, in particular on the
high contour rectangle. -/
theorem analyticOnNhd_packetPolarization
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν)) (v w : ι → ℂ) (U : Set ℂ) :
    AnalyticOnNhd ℂ (packetPolarization ψ v w) U := by
  intro s _
  exact (differentiable_packetPolarization hψ v w).analyticAt s

end HardyGaugeInvariantContourForm
end ZetaZero
