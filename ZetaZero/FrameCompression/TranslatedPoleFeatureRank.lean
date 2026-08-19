import ZetaZero.FrameCompression.FiniteFeatureRank

/-!
# M08: translated-pole jet rank bookkeeping

A finite-order translated-pole residue only sees finitely many jets of each
packet transform.  The analytic residue calculation is deliberately kept out
of this file: once a contribution is shown to factor through the corresponding
block/pole/jet coordinates, its rank bound is automatic.
-/

namespace ZetaZero
namespace FrameCompression

section TranslatedPoleFeatureRank

variable {𝕜 V W : Type*} [DivisionRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

/-- Feature labels for `r` jets at every translated pole in every block. -/
abbrev TranslatedPoleJetIndex (β σ : Type*) (r : ℕ) := (β × σ) × Fin r

variable {β σ : Type*} [Fintype β] [Fintype σ] {r : ℕ}

/-- A contribution that depends only on `r` jets at each pole of a finite pole
set has rank at most `(# blocks) * (# poles) * r`. -/
theorem finrank_range_translatedPoleJets_le
    (M : V →ₗ[𝕜] (TranslatedPoleJetIndex β σ r → 𝕜))
    (N : (TranslatedPoleJetIndex β σ r → 𝕜) →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N.comp M)) ≤
      Fintype.card β * Fintype.card σ * r := by
  have h := finrank_range_factor_through_coordinates_le_card M N
  simpa [TranslatedPoleJetIndex, Fintype.card_prod, Nat.mul_assoc] using h

/-- In particular, a single translated pole of order at most `r` costs at most
`r` features per block. -/
theorem finrank_range_singleTranslatedPoleJets_le
    (M : V →ₗ[𝕜] (TranslatedPoleJetIndex β (Fin 1) r → 𝕜))
    (N : (TranslatedPoleJetIndex β (Fin 1) r → 𝕜) →ₗ[𝕜] W) :
    Module.finrank 𝕜 (LinearMap.range (N.comp M)) ≤ Fintype.card β * r := by
  simpa using (finrank_range_translatedPoleJets_le M N)

end TranslatedPoleFeatureRank

end FrameCompression
end ZetaZero
