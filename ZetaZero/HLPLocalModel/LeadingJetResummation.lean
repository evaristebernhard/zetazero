import ZetaZero.HLPLocalModel.FiniteResolventExpansion
import Mathlib.Tactic

/-!
# M05: leading HLP jet resummation

At principal Laurent order the HLP hierarchy is represented by a rational
resolvent.  The important translated-cluster identity is purely algebraic, so
it can be formalized without any infinite-series convergence argument.
-/

namespace ZetaZero
namespace HLPLocalModel

section LeadingJetResummation

/-- The translated denominator is the original resolvent denominator divided
by `F`. -/
theorem shifted_denominator_eq
    {F u : ℂ} (hF : F ≠ 0) :
    u - F⁻¹ = (F * u - 1) / F := by
  field_simp [hF]

/-- Principal Laurent resolvent partial fraction:

`1 / (u (F u - 1)) = -1/u + 1/(u-F⁻¹)`.

This is the finite algebraic content behind the resummation of the complete
leading HLP hierarchy. -/
theorem leading_resolvent_partial_fraction
    {F u : ℂ} (hF : F ≠ 0) (hu : u ≠ 0) (hFu : F * u - 1 ≠ 0) :
    1 / (u * (F * u - 1)) = -1 / u + 1 / (u - F⁻¹) := by
  have hFu' : -1 + u * F ≠ 0 := by
    intro h
    apply hFu
    calc
      F * u - 1 = -1 + u * F := by ring
      _ = 0 := h
  have hFuComm : u * F - 1 ≠ 0 := by
    simpa [mul_comm] using hFu
  rw [shifted_denominator_eq hF]
  field_simp [hF, hu, hFu, hFu', hFuComm]
  ring

/-- Adding the separate principal part `-u⁻¹` gives the completed translated
cluster `-2/u + 1/(u-F⁻¹)`. -/
theorem completed_leading_cluster
    {F u : ℂ} (hF : F ≠ 0) (hu : u ≠ 0) (hFu : F * u - 1 ≠ 0) :
    -1 / u + 1 / (u * (F * u - 1)) =
      -2 / u + 1 / (u - F⁻¹) := by
  rw [leading_resolvent_partial_fraction hF hu hFu]
  ring

end LeadingJetResummation

end HLPLocalModel
end ZetaZero
