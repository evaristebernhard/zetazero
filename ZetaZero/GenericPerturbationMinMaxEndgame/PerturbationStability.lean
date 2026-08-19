import ZetaZero.FiniteDimensionalInertiaReduction
import Mathlib.Tactic

/-!
# Generic-perturbation stability of a positive floor

This file formalizes the purely finite-dimensional step used after the analytic
perturbation has been chosen: a relative pointwise perturbation smaller than the
principal lower bound preserves a positive lower bound, hence preserves the
input needed by the inertia reduction.
-/

namespace ZetaZero
namespace GenericPerturbationMinMaxEndgame

open FiniteDimensionalInertiaReduction

section PerturbationStability

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- `LowerBoundOn p g c S` means `p ≥ c g` pointwise on `S`. -/
def LowerBoundOn (p g : V → ℝ) (c : ℝ) (S : Submodule 𝕜 V) : Prop :=
  ∀ x, x ∈ S → c * g x ≤ p x

/-- `RelativeAbsBoundOn δ g ε S` is the pointwise relative perturbation estimate
`|δ| ≤ ε g` on `S`. -/
def RelativeAbsBoundOn (δ g : V → ℝ) (ε : ℝ) (S : Submodule 𝕜 V) : Prop :=
  ∀ x, x ∈ S → |δ x| ≤ ε * g x

/-- Subtracting a relative perturbation budget from a positive floor preserves
a lower bound. -/
theorem lowerBoundOn_add_of_relativeAbsBoundOn
    {p δ g : V → ℝ} {c ε : ℝ} {S : Submodule 𝕜 V}
    (hp : LowerBoundOn p g c S)
    (hδ : RelativeAbsBoundOn δ g ε S) :
    LowerBoundOn (fun x => p x + δ x) g (c - ε) S := by
  intro x hx
  have hp_x := hp x hx
  have hδ_x := hδ x hx
  have hδ_lower : -(ε * g x) ≤ δ x := (abs_le.mp hδ_x).1
  calc
    (c - ε) * g x = c * g x - ε * g x := by ring
    _ ≤ p x - ε * g x := sub_le_sub_right hp_x _
    _ ≤ p x + δ x := by
      simpa [sub_eq_add_neg] using add_le_add_left hδ_lower (p x)

/-- If the reference form is nonnegative and the surviving coefficient is
nonnegative, the perturbed form is nonnegative on the retained subspace. -/
theorem nonnegativeOn_add_of_relativeAbsBoundOn
    {p δ g : V → ℝ} {c ε : ℝ} {S : Submodule 𝕜 V}
    (hg : NonnegativeOn g S)
    (hp : LowerBoundOn p g c S)
    (hδ : RelativeAbsBoundOn δ g ε S)
    (hεc : ε ≤ c) :
    NonnegativeOn (fun x => p x + δ x) S := by
  have hlower := lowerBoundOn_add_of_relativeAbsBoundOn hp hδ
  intro x hx
  have hg_x := hg x hx
  have hlower_x := hlower x hx
  have hcoef : 0 ≤ c - ε := sub_nonneg.mpr hεc
  have hbase : 0 ≤ (c - ε) * g x := mul_nonneg hcoef hg_x
  exact hbase.trans hlower_x

/-- The perturbation-stable positive subspace immediately gives a negative-index
bound by its codimension. -/
theorem negativeIndexLE_of_relative_perturbation
    [FiniteDimensional 𝕜 V]
    {p δ g : V → ℝ} {c ε : ℝ} {S : Submodule 𝕜 V}
    (hg : NonnegativeOn g S)
    (hp : LowerBoundOn p g c S)
    (hδ : RelativeAbsBoundOn δ g ε S)
    (hεc : ε ≤ c) :
    NegativeIndexLE (𝕜 := 𝕜) (fun x => p x + δ x) (codim S) := by
  exact negativeIndexLE_codim_of_nonnegativeOn
    (nonnegativeOn_add_of_relativeAbsBoundOn hg hp hδ hεc)

/-- The numerical specialization used in the manuscript: a `c/4` perturbation
leaves a `3c/4` floor. -/
theorem three_quarters_lowerBoundOn
    {p δ g : V → ℝ} {c : ℝ} {S : Submodule 𝕜 V}
    (hp : LowerBoundOn p g c S)
    (hδ : RelativeAbsBoundOn δ g (c / 4) S) :
    LowerBoundOn (fun x => p x + δ x) g (3 * c / 4) S := by
  have h := lowerBoundOn_add_of_relativeAbsBoundOn hp hδ
  have hc : c - c / 4 = 3 * c / 4 := by ring
  rw [hc] at h
  exact h

end PerturbationStability

end GenericPerturbationMinMaxEndgame
end ZetaZero
