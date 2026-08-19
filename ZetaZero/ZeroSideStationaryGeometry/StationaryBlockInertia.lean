import ZetaZero.ZeroSideStationaryGeometry.StationaryResidueBlocks
import ZetaZero.FiniteDimensionalInertiaReduction.CoordinateGoodSpace
import ZetaZero.FiniteDimensionalInertiaReduction.NegativeIndex

/-!
# Inertia interface for a stationary conjugate-pair block

This module connects the explicit `2 × 2` residue algebra to the abstract
negative-index API from M01.  No spectral theorem is needed: after deleting one
coordinate the off-diagonal quadratic form vanishes identically, giving a
codimension-one nonnegative subspace.  An explicit vector supplies the matching
negative direction when the residue weight is nonzero.
-/

open Complex

noncomputable section

namespace ZetaZero
namespace ZeroSideStationaryGeometry

open FiniteDimensionalInertiaReduction

/-- The coordinate hyperplane `x₁ = 0` used to control the pair-block inertia. -/
def conjugatePairGoodSpace : Submodule ℂ (Fin 2 → ℂ) :=
  coordinateGoodSpace (𝕜 := ℂ) ({(1 : Fin 2)} : Finset (Fin 2))

/-- The conjugate-pair quadratic form vanishes on the codimension-one good
space, hence is nonnegative there. -/
theorem conjugatePairQuadratic_nonnegativeOn_goodSpace (w : ℂ) :
    NonnegativeOn (conjugatePairQuadratic w) conjugatePairGoodSpace := by
  intro x hx
  have hcoords := (mem_coordinateGoodSpace_iff
    (𝕜 := ℂ) (S := ({(1 : Fin 2)} : Finset (Fin 2))) (x := x)).mp hx
  have hx1 : x (1 : Fin 2) = 0 := hcoords ⟨(1 : Fin 2), by simp⟩
  simp [conjugatePairQuadratic, hx1]

/-- The good space has codimension at most one. -/
theorem codim_conjugatePairGoodSpace_le_one :
    codim conjugatePairGoodSpace ≤ 1 := by
  simpa [conjugatePairGoodSpace] using
    (codim_coordinateGoodSpace_le (𝕜 := ℂ)
      ({(1 : Fin 2)} : Finset (Fin 2)))

/-- Every strictly negative subspace for a conjugate-pair block has dimension at
most one. -/
theorem conjugatePair_negativeIndexLE_one (w : ℂ) :
    NegativeIndexLE (𝕜 := ℂ) (conjugatePairQuadratic w) 1 := by
  exact negativeIndexLE_of_nonnegativeOn_of_codim_le
    (conjugatePairQuadratic_nonnegativeOn_goodSpace w)
    codim_conjugatePairGoodSpace_le_one

/-- For nonzero residue weight, the pair block has an actual nonzero negative
direction.  Together with `conjugatePair_negativeIndexLE_one`, this is the
paper-facing algebraic statement that a nonreal conjugate pair contributes
exactly one negative direction. -/
theorem conjugatePair_exists_negativeDirection {w : ℂ} (hw : w ≠ 0) :
    ∃ x : Fin 2 → ℂ, x ≠ 0 ∧ conjugatePairQuadratic w x < 0 := by
  refine ⟨conjugatePairNegativeVector w, ?_,
    conjugatePairQuadratic_negativeVector_neg hw⟩
  intro hzero
  have h0 := congrFun hzero (0 : Fin 2)
  simp [conjugatePairNegativeVector] at h0

end ZeroSideStationaryGeometry
end ZetaZero
