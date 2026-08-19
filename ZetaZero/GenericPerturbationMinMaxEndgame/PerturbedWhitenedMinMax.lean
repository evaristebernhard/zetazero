import ZetaZero.GenericPerturbationMinMaxEndgame.PerturbationStability

/-!
# Perturbed whitened min--max assembly

This is the M10 glue between the fixed-height perturbation estimate and the M01
rank-plus-Hilbert--Schmidt theorem.  The perturbation is absorbed into the
principal form, reducing its floor from `c₀` to `3 c₀ / 4`.
-/

namespace ZetaZero
namespace GenericPerturbationMinMaxEndgame

open FiniteDimensionalInertiaReduction

section PerturbedWhitenedMinMax

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A `c₀/4` relative perturbation of the principal form can be absorbed before
applying the M01 rank-plus-Hilbert--Schmidt theorem. -/
theorem rank_plus_hilbertSchmidt_minmax_after_quarter_perturbation
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {Aq Pq Δq Eq Rq Gq : (n → 𝕜) → ℝ}
    {E : (n → 𝕜) →ₗ[𝕜] (n → 𝕜)} {c₀ : ℝ} {r : ℕ}
    (hc₀ : 0 < c₀)
    (hG : ∀ x, 0 ≤ Gq x)
    (hdecomp : ∀ x, Aq x = (Pq x + Δq x) + Eq x + Rq x)
    (hP : ∀ x, c₀ * Gq x ≤ Pq x)
    (hΔ : ∀ x, |Δq x| ≤ (c₀ / 4) * Gq x)
    (hEzero : ∀ x, x ∈ LinearMap.ker E → Eq x = 0)
    (hRdiag : ∀ x, Rq x =
      diagonalQuadratic hB.eigenvalues (spectralCoordinateMap hB x))
    (hGcoord : ∀ x, Gq x = coordinateNormSq (spectralCoordinateMap hB x))
    (hE : Module.finrank 𝕜 (LinearMap.range E) ≤ r) :
    NegativeIndexBound (𝕜 := 𝕜) Aq
      ((r : ℝ) + 16 * ((3 * c₀ / 4) ^ 2)⁻¹ * hilbertSchmidtSq B) := by
  have hpOn : LowerBoundOn Pq Gq c₀ (⊤ : Submodule 𝕜 (n → 𝕜)) := by
    intro x _
    exact hP x
  have hΔOn : RelativeAbsBoundOn Δq Gq (c₀ / 4) (⊤ : Submodule 𝕜 (n → 𝕜)) := by
    intro x _
    exact hΔ x
  have hPpert : ∀ x, (3 * c₀ / 4) * Gq x ≤ Pq x + Δq x := by
    intro x
    exact three_quarters_lowerBoundOn hpOn hΔOn x (by simp)
  have hcstar : 0 < 3 * c₀ / 4 := by positivity
  exact rank_plus_hilbertSchmidt_minmax hB hcstar hG hdecomp hPpert
    hEzero hRdiag hGcoord hE

end PerturbedWhitenedMinMax

end GenericPerturbationMinMaxEndgame
end ZetaZero
