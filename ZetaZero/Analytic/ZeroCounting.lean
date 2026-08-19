import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Set.Finite.Basic

/-!
# Analytic foundation: zeta zeros and multiplicities

This module fixes the zero-counting interface used by the zero-side and final
asymptotic parts of the formalization.  The design follows the Mathlib-backed
interface used successfully in the public `zeta-23-lean` formalization: zeros
are zeros of `riemannZeta`, and multiplicity is the analytic order of vanishing.

The analytic theorems asserting finiteness of height windows and asymptotics for
these counting functions are deliberately not assumed here; they belong to
later modules.
-/

open scoped BigOperators
open Complex Set

noncomputable section

namespace ZetaZero
namespace Analytic

/-- A nontrivial zero of the Riemann zeta function in the open critical strip. -/
def IsNontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- Multiplicity of a zeta zero, represented by Mathlib's analytic order. -/
def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

/-- Nontrivial zeta zeros whose ordinates lie in the half-open window `(T₁, T₂]`. -/
def zetaZerosIn (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ | IsNontrivialZetaZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- Nontrivial zeta zeros in `(T₁,T₂]` that lie on the critical line. -/
def criticalLineZetaZerosIn (T₁ T₂ : ℝ) : Set ℂ :=
  zetaZerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}

/-- `N(T₁,T₂)`: nontrivial zeta zeros in `(T₁,T₂]`, counted with multiplicity. -/
def Ncount (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zetaZerosIn T₁ T₂, zetaZeroMultiplicity ρ

/-- `N₀(T₁,T₂)`: critical-line zeros in `(T₁,T₂]`, counted with multiplicity. -/
def N0count (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ criticalLineZetaZerosIn T₁ T₂, zetaZeroMultiplicity ρ

/-- Number of distinct nontrivial zeta zeros in `(T₁,T₂]`. -/
def Ndist (T₁ T₂ : ℝ) : ℕ :=
  (zetaZerosIn T₁ T₂).ncard

/-- Number of distinct critical-line zeta zeros in `(T₁,T₂]`. -/
def N0dist (T₁ T₂ : ℝ) : ℕ :=
  (criticalLineZetaZerosIn T₁ T₂).ncard

/-- Number of simple critical-line zeta zeros in `(T₁,T₂]`. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (criticalLineZetaZerosIn T₁ T₂ ∩ {ρ | zetaZeroMultiplicity ρ = 1}).ncard

/-- Dyadic total zero count used by the manuscript. -/
def dyadicN (T : ℝ) : ℕ := Ncount T (2 * T)

/-- Dyadic critical-line zero count used by the manuscript. -/
def dyadicN0 (T : ℝ) : ℕ := N0count T (2 * T)

@[simp] theorem mem_zetaZerosIn_iff {T₁ T₂ : ℝ} {ρ : ℂ} :
    ρ ∈ zetaZerosIn T₁ T₂ ↔
      IsNontrivialZetaZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂ := by
  rfl

@[simp] theorem mem_criticalLineZetaZerosIn_iff {T₁ T₂ : ℝ} {ρ : ℂ} :
    ρ ∈ criticalLineZetaZerosIn T₁ T₂ ↔
      IsNontrivialZetaZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂ ∧ ρ.re = 1 / 2 := by
  simp [criticalLineZetaZerosIn, zetaZerosIn, and_assoc]

end Analytic
end ZetaZero
