import ZetaZero.HardyGaugeInvariantContourForm.Zeta23HardyBridge
import Zeta23.XiPrime.Hardy.Count
import Zeta23.XiPrime.Hardy.ZeroFree

/-!
# Counting zeros of the manuscript stationary source `Z₁`

The manuscript source `Z₁` agrees off the real axis with the `hardyW` source of
`zeta-23-lean`.  This module transports the zero set and analytic multiplicity
pointwise, then identifies the resulting window counts.  It is the counting
bridge needed by the M03 packet-dimension and good-height arguments.
-/

open scoped BigOperators
open Complex Set

noncomputable section

namespace ZetaZero
namespace Analytic

open HardyGaugeInvariantContourForm

/-- A non-real zero of the manuscript stationary source. -/
def IsZetaOneZero (ρ : ℂ) : Prop := zetaOne ρ = 0 ∧ ρ.im ≠ 0

/-- Analytic multiplicity of a `Z₁` zero. -/
def zetaOneMultiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt zetaOne ρ

/-- `Z₁` zeros in the half-open height window `(T₁,T₂]`. -/
def zetaOneZerosIn (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ | IsZetaOneZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- Multiplicity-weighted `Z₁` zero count in `(T₁,T₂]`. -/
def NcountZetaOne (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zetaOneZerosIn T₁ T₂, zetaOneMultiplicity ρ

/-- The manuscript `Z₁` zero predicate agrees exactly with Zeta23's `W` zero
predicate away from the real axis. -/
theorem isZetaOneZero_iff_isWZero {ρ : ℂ} :
    IsZetaOneZero ρ ↔ Zeta23.XiPrime.IsWZero ρ := by
  constructor
  · rintro ⟨h0, him⟩
    exact ⟨(zetaOne_eq_zero_iff_zeta23_hardyW_eq_zero him).mp h0, him⟩
  · rintro ⟨h0, him⟩
    exact ⟨(zetaOne_eq_zero_iff_zeta23_hardyW_eq_zero him).mpr h0, him⟩

/-- Therefore the two height-window zero sets are definitionally the same after
using the source identification. -/
theorem zetaOneZerosIn_eq_zerosInW (T₁ T₂ : ℝ) :
    zetaOneZerosIn T₁ T₂ = Zeta23.XiPrime.zerosInW T₁ T₂ := by
  ext ρ
  simp only [zetaOneZerosIn, Zeta23.XiPrime.zerosInW, mem_setOf_eq]
  rw [isZetaOneZero_iff_isWZero]

/-- Analytic multiplicity agrees with Zeta23's `wMult` at every non-real point. -/
theorem zetaOneMultiplicity_eq_wMult {ρ : ℂ} (him : ρ.im ≠ 0) :
    zetaOneMultiplicity ρ = Zeta23.XiPrime.wMult ρ := by
  unfold zetaOneMultiplicity analyticOrderNatAt Zeta23.XiPrime.wMult
  rw [analyticOrderAt_zetaOne_eq_zeta23_hardyW him]

/-- The manuscript stationary-source count is literally the already-formalized
`W` count. -/
theorem NcountZetaOne_eq_NcountW (T₁ T₂ : ℝ) :
    NcountZetaOne T₁ T₂ = Zeta23.XiPrime.NcountW T₁ T₂ := by
  rw [NcountZetaOne, Zeta23.XiPrime.NcountW, zetaOneZerosIn_eq_zerosInW]
  apply finsum_mem_congr rfl
  intro ρ hρ
  exact zetaOneMultiplicity_eq_wMult hρ.1.2

/-- Unconditionally, above some positive height all zeros of `Z₁` lie in the
open critical strip.  This is the manuscript form of Zeta23's proved `Z6`. -/
theorem zetaOneZerosInStrip_holds :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ ρ : ℂ, zetaOne ρ = 0 → t₀ ≤ |ρ.im| → 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨t₀, ht₀, hstrip⟩ := Zeta23.XiPrime.wZerosInStrip_holds
  refine ⟨t₀, ht₀, ?_⟩
  intro ρ hz hheight
  have him : ρ.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hheight
    linarith
  exact hstrip ρ ((zetaOne_eq_zero_iff_zeta23_hardyW_eq_zero him).mp hz) hheight

end Analytic
end ZetaZero
