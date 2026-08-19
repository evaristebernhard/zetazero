import Zeta23.Analytic.RectangleLogDeriv

/-!
# Rectangle weighted argument principle

This module exposes the mature rectangle logarithmic-derivative machinery from
our local `zeta-23-lean` reference formalization inside the main `ZetaZero`
namespace.  Keeping the bridge here avoids duplicating the residue calculus and
lets the Hardy same-form contour line use a proved finite-zero residue theorem.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace Analytic

/-- Weighted argument principle on a closed rectangle, re-exported from the
locally vendored `Zeta23` formalization. -/
theorem rectangleWeightedArgumentPrinciple
    {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (Z : Finset ℂ)
    (hZ : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ Z)
    (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w =
      ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  exact Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    hre him hf hg hborder Z hZ hZsub

end Analytic
end ZetaZero
