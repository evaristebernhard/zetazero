import ZetaZero.FiniteDimensionalInertiaReduction.HilbertSchmidtBridge
import Mathlib.Tactic.NormNum

/-!
# Finite-dimensional inertia reduction: min--max assembly

This module contains the paper-facing algebra after the Hilbert--Schmidt bad
space has been constructed.  It does not construct that space; it records the
exact hypotheses needed from the spectral threshold step.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section MinMaxAssembly

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Principal positivity, vanishing of the finite-rank term on its kernel, and
a `c₀/4` lower bound for the remainder imply the paper's `3c₀/4` lower bound
on the intersection of the two good spaces. -/
theorem three_quarters_lower_bound_on_good_space
    {Aq Pq Eq Rq Gq : V → ℝ} {E : V →ₗ[𝕜] V} {T : Submodule 𝕜 V}
    {c₀ : ℝ}
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hR : ∀ x, x ∈ T → -(c₀ / 4) * Gq x ≤ Rq x) :
    ∀ x, x ∈ LinearMap.ker E ⊓ T → (3 * c₀ / 4) * Gq x ≤ Aq x := by
  intro x hx
  have hxE : x ∈ LinearMap.ker E := hx.1
  have hxT : x ∈ T := hx.2
  have hPx := hP x
  have hEx := hEzero x hxE
  have hRx := hR x hxT
  rw [hdecomp x, hEx]
  norm_num only [add_zero]
  nlinarith

/-- Under the same hypotheses, the form is nonnegative on the good space. -/
theorem nonnegativeOn_good_space
    {Aq Pq Eq Rq Gq : V → ℝ} {E : V →ₗ[𝕜] V} {T : Submodule 𝕜 V}
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hG : ∀ x, 0 ≤ Gq x)
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hR : ∀ x, x ∈ T → -(c₀ / 4) * Gq x ≤ Rq x) :
    NonnegativeOn Aq (LinearMap.ker E ⊓ T) := by
  intro x hx
  have hlower := three_quarters_lower_bound_on_good_space hdecomp hP hEzero hR x hx
  have hGx := hG x
  have hcoef : 0 ≤ 3 * c₀ / 4 := by positivity
  exact le_trans (mul_nonneg hcoef hGx) hlower

/-- Rank plus a real codimension budget for the spectral bad space gives a
real-valued negative-inertia bound. -/
theorem negativeIndexBound_rank_plus_remainder_good_space
    [FiniteDimensional 𝕜 V]
    {Aq Pq Eq Rq Gq : V → ℝ} {E : V →ₗ[𝕜] V} {T : Submodule 𝕜 V}
    {c₀ h : ℝ} {r : ℕ} (hc₀ : 0 < c₀)
    (hG : ∀ x, 0 ≤ Gq x)
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hR : ∀ x, x ∈ T → -(c₀ / 4) * Gq x ≤ Rq x)
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r)
    (hT : (codim T : ℝ) ≤ h) :
    NegativeIndexBound (𝕜 := 𝕜) Aq ((r : ℝ) + h) := by
  apply negativeIndexBound_rank_plus_goodSpace hE hT
  exact nonnegativeOn_good_space hc₀ hG hdecomp hP hEzero hR

/-- Specialization to the Hilbert--Schmidt budget appearing in the manuscript. -/
theorem negativeIndexBound_rank_plus_hilbertSchmidt_budget
    [FiniteDimensional 𝕜 V]
    {Aq Pq Eq Rq Gq : V → ℝ} {E : V →ₗ[𝕜] V} {T : Submodule 𝕜 V}
    {c₀ s : ℝ} {r : ℕ} (hc₀ : 0 < c₀)
    (hG : ∀ x, 0 ≤ Gq x)
    (hdecomp : ∀ x, Aq x = Pq x + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hR : ∀ x, x ∈ T → -(c₀ / 4) * Gq x ≤ Rq x)
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r)
    (hT : (codim T : ℝ) ≤ 16 * (c₀ ^ 2)⁻¹ * s) :
    NegativeIndexBound (𝕜 := 𝕜) Aq ((r : ℝ) + 16 * (c₀ ^ 2)⁻¹ * s) := by
  exact negativeIndexBound_rank_plus_remainder_good_space hc₀ hG hdecomp hP hEzero hR hE hT

end MinMaxAssembly

end FiniteDimensionalInertiaReduction
end ZetaZero
