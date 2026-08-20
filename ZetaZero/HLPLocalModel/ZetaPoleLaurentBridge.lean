import Zeta23.FromPNTPlus.ZetaBounds

/-!
# Local Laurent bridge for the zeta logarithmic derivative

The HLP/Perron local variable uses

`P(s) = -ζ'(s)/ζ(s)`.

The vendored `Zeta23.FromPNTPlus.ZetaBounds` development already proves that the
simple pole at `s=1` has principal part `(s-1)⁻¹` and bounded remainder.  This
file merely exposes that result in the notation used by the current project.

It deliberately does **not** claim the stronger packet-uniform derivative bounds
from the manuscript.  Those remain a separate analytic input.
-/

open Complex Topology Filter Set Asymptotics

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- The local HLP source `P=-ζ'/ζ`. -/
def zetaPoleP : ℂ → ℂ :=
  -deriv riemannZeta / riemannZeta

/-- Near `s=1`, `P(s)` has principal part `(s-1)⁻¹` with bounded remainder. -/
theorem zetaPoleP_sub_principal_isBigO :
    (zetaPoleP - fun s : ℂ => (s - 1)⁻¹) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  simpa [zetaPoleP, Pi.sub_apply] using riemannZetaLogDerivResidueBigO

/-- Neighborhood-bounded version of the same Laurent statement. -/
theorem exists_bddAbove_zetaPoleP_sub_principal :
    ∃ U ∈ 𝓝 (1 : ℂ),
      BddAbove
        (norm ∘ (zetaPoleP - fun s : ℂ => (s - 1)⁻¹) '' (U \ {(1 : ℂ)})) := by
  exact IsBigO_to_BddAbove zetaPoleP_sub_principal_isBigO

/-- Pointwise decomposition of the HLP source into its principal pole and a
remainder.  The content is algebraic; the preceding theorems provide the local
boundedness of this remainder. -/
def zetaPoleRemainder : ℂ → ℂ :=
  zetaPoleP - fun s : ℂ => (s - 1)⁻¹

/-- Exact reconstruction from principal part plus remainder. -/
theorem zetaPoleP_eq_principal_add_remainder (s : ℂ) :
    zetaPoleP s = (s - 1)⁻¹ + zetaPoleRemainder s := by
  simp [zetaPoleRemainder]

/-- The project remainder is bounded in a punctured neighborhood of `1`. -/
theorem zetaPoleRemainder_isBigO :
    zetaPoleRemainder =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  simpa [zetaPoleRemainder] using zetaPoleP_sub_principal_isBigO

/-- Translation by `1` carries the punctured neighborhood of `0` to the
punctured neighborhood of the zeta pole `1`. -/
theorem tendsto_one_add_punctured :
    Tendsto (fun u : ℂ => 1 + u) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hid : Tendsto (fun u : ℂ => u) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
      tendsto_id.mono_left inf_le_left
    simpa using tendsto_const_nhds.add hid
  · filter_upwards [self_mem_nhdsWithin] with u hu
    simpa using hu

/-- The bounded Laurent remainder remains bounded after the local coordinate
change `s=1+u`. -/
theorem translatedZetaPoleRemainder_isBigO :
    (fun u : ℂ => zetaPoleRemainder (1 + u)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  have h := zetaPoleRemainder_isBigO.comp_tendsto tendsto_one_add_punctured
  exact h.congr (fun _ => rfl) (fun _ => rfl)

/-- The normalized pole factor used in the manuscript before filling in its
removable value at `u=0`. -/
def normalizedZetaPoleFactor (u : ℂ) : ℂ :=
  u * zetaPoleP (1 + u)

/-- Away from `u=0`, the normalized pole factor is `1 + u` times the bounded
Laurent remainder. -/
theorem normalizedZetaPoleFactor_eventuallyEq :
    (fun u : ℂ => normalizedZetaPoleFactor u) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun u => 1 + u * zetaPoleRemainder (1 + u)) := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := by simpa using hu
  rw [normalizedZetaPoleFactor, zetaPoleP_eq_principal_add_remainder]
  have hone : (1 + u - 1 : ℂ) = u := by ring
  rw [hone, mul_add]
  field_simp [hu0]

/-- The normalized zeta logarithmic-derivative pole has removable limit `1`.
This is the formal content behind the manuscript normalization `A(0)=1`; it does
not yet assert holomorphic extension or derivative bounds. -/
theorem tendsto_normalizedZetaPoleFactor_one :
    Tendsto normalizedZetaPoleFactor (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  have hidO : (fun u : ℂ => u) =O[𝓝[≠] (0 : ℂ)] (fun u : ℂ => u) :=
    Asymptotics.isBigO_refl _ _
  have hprod := hidO.mul translatedZetaPoleRemainder_isBigO
  have hprod' :
      (fun u : ℂ => u * zetaPoleRemainder (1 + u)) =O[𝓝[≠] (0 : ℂ)]
        (fun u : ℂ => u) := by
    simpa using hprod
  have hidT : Tendsto (fun u : ℂ => u) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    tendsto_id.mono_left inf_le_left
  have hzero :
      Tendsto (fun u : ℂ => u * zetaPoleRemainder (1 + u))
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    hprod'.trans_tendsto hidT
  have hone :
      Tendsto (fun u : ℂ => 1 + u * zetaPoleRemainder (1 + u))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using tendsto_const_nhds.add hzero
  exact (tendsto_congr' normalizedZetaPoleFactor_eventuallyEq).2 hone

/-- Fill the removable value of the normalized pole factor by its limit `1`. -/
def normalizedZetaPoleFactorExt (u : ℂ) : ℂ :=
  if u = 0 then 1 else normalizedZetaPoleFactor u

@[simp] theorem normalizedZetaPoleFactorExt_zero :
    normalizedZetaPoleFactorExt 0 = 1 := by
  simp [normalizedZetaPoleFactorExt]

/-- On the punctured neighborhood, the filled function agrees with the original
normalized pole factor. -/
theorem normalizedZetaPoleFactorExt_eventuallyEq :
    normalizedZetaPoleFactorExt =ᶠ[𝓝[≠] (0 : ℂ)] normalizedZetaPoleFactor := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := by simpa using hu
  simp [normalizedZetaPoleFactorExt, hu0]

/-- The removable extension with value `1` is continuous at the zeta pole in the
local coordinate.  Holomorphic extension and derivative bounds are intentionally
left to the next analytic layer. -/
theorem continuousAt_normalizedZetaPoleFactorExt :
    ContinuousAt normalizedZetaPoleFactorExt 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simp only [normalizedZetaPoleFactorExt_zero]
  exact (tendsto_congr' normalizedZetaPoleFactorExt_eventuallyEq).2
    tendsto_normalizedZetaPoleFactor_one

end HLPLocalModel
end ZetaZero
