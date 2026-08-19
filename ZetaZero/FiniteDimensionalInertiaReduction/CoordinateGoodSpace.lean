import ZetaZero.FiniteDimensionalInertiaReduction.MinMaxAssembly
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-dimensional inertia reduction: coordinate good spaces

A finite set of bad spectral coordinates is removed by restricting to the
kernel of the coordinate restriction map.  This realizes the bad-index count
as an actual codimension bound, independently of any spectral theorem.
-/

namespace ZetaZero
namespace FiniteDimensionalInertiaReduction

section CoordinateGoodSpace

variable {𝕜 n : Type*} [DivisionRing 𝕜] [Fintype n]

/-- Restriction of a coordinate vector to the finite set `S`. -/
def badCoordinateMap (S : Finset n) : (n → 𝕜) →ₗ[𝕜] (S → 𝕜) where
  toFun x i := x i.1
  map_add' x y := by
    ext i
    rfl
  map_smul' a x := by
    ext i
    rfl

/-- Vectors whose coordinates vanish on every index in `S`. -/
def coordinateGoodSpace (S : Finset n) : Submodule 𝕜 (n → 𝕜) :=
  LinearMap.ker (badCoordinateMap (𝕜 := 𝕜) S)

omit [Fintype n] in
/-- Membership in the coordinate good space is exactly coordinate vanishing on
`S`. -/
theorem mem_coordinateGoodSpace_iff {S : Finset n} {x : n → 𝕜} :
    x ∈ coordinateGoodSpace (𝕜 := 𝕜) S ↔ ∀ i : S, x i.1 = 0 := by
  constructor
  · intro hx i
    have hker : badCoordinateMap (𝕜 := 𝕜) S x = 0 := hx
    have hi := congrFun hker i
    simpa [badCoordinateMap] using hi
  · intro hx
    rw [coordinateGoodSpace, LinearMap.mem_ker]
    funext i
    simpa [badCoordinateMap] using hx i

/-- Removing `S` coordinate directions costs at most `#S` dimensions. -/
theorem codim_coordinateGoodSpace_le (S : Finset n) :
    codim (coordinateGoodSpace (𝕜 := 𝕜) S) ≤ S.card := by
  unfold coordinateGoodSpace
  change codim (LinearMap.ker (badCoordinateMap (𝕜 := 𝕜) S)) ≤ S.card
  rw [codim_ker_eq_finrank_range]
  calc
    Module.finrank 𝕜 (LinearMap.range (badCoordinateMap (𝕜 := 𝕜) S))
        ≤ Module.finrank 𝕜 (S → 𝕜) := Submodule.finrank_le _
    _ = Fintype.card S := Module.finrank_fintype_fun_eq_card 𝕜
    _ = S.card := Fintype.card_coe S

end CoordinateGoodSpace

end FiniteDimensionalInertiaReduction
end ZetaZero
