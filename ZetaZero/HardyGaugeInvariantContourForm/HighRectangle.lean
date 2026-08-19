import ZetaZero.HardyGaugeInvariantContourForm.HolomorphicSquareRoot
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# A holomorphic Hardy gauge on the high contour rectangle

The paper integrates over the closed rectangle `-1 ≤ Re s ≤ 2`,
`T₁ ≤ Im s ≤ T₂`.  For analytic constructions we use a slightly enlarged open
rectangle.  It is convex, hence contractible and simply connected, and for
`ε < T₁` it stays strictly above the real axis.  The abstract square-root theorem
therefore supplies a holomorphic branch of `χ(1-s)^(1/2)` on this neighbourhood.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Open `ε`-neighbourhood rectangle around the manuscript contour rectangle. -/
def highRectangleNhd (T₁ T₂ ε : ℝ) : Set ℂ :=
  {s | -1 - ε < s.re} ∩ {s | s.re < 2 + ε} ∩
    ({s | T₁ - ε < s.im} ∩ {s | s.im < T₂ + ε})

/-- The enlarged high rectangle is open. -/
theorem isOpen_highRectangleNhd (T₁ T₂ ε : ℝ) :
    IsOpen (highRectangleNhd T₁ T₂ ε) := by
  unfold highRectangleNhd
  exact
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))

/-- The enlarged high rectangle is convex. -/
theorem convex_highRectangleNhd (T₁ T₂ ε : ℝ) :
    Convex ℝ (highRectangleNhd T₁ T₂ ε) := by
  unfold highRectangleNhd
  exact
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))

/-- Under the natural parameter inequalities, the enlarged rectangle is
nonempty. -/
theorem highRectangleNhd_nonempty {T₁ T₂ ε : ℝ}
    (hε : 0 < ε) (hT : T₁ < T₂) :
    (highRectangleNhd T₁ T₂ ε).Nonempty := by
  let z : ℂ := (1 / 2 : ℂ) + (((T₁ + T₂) / 2 : ℝ) : ℂ) * Complex.I
  refine ⟨z, ?_⟩
  simp only [highRectangleNhd, mem_inter_iff, mem_setOf_eq]
  have hzre : z.re = 1 / 2 := by
    simp [z]
  have hzim : z.im = (T₁ + T₂) / 2 := by
    simp [z]
  rw [hzre, hzim]
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- The enlarged high rectangle is simply connected. -/
theorem isSimplyConnected_highRectangleNhd {T₁ T₂ ε : ℝ}
    (hε : 0 < ε) (hT : T₁ < T₂) :
    IsSimplyConnected (highRectangleNhd T₁ T₂ ε) := by
  letI : ContractibleSpace (highRectangleNhd T₁ T₂ ε) :=
    (convex_highRectangleNhd T₁ T₂ ε).contractibleSpace
      (highRectangleNhd_nonempty hε hT)
  exact (inferInstance : SimplyConnectedSpace (highRectangleNhd T₁ T₂ ε))

/-- If the enlargement is smaller than the lower height, the whole analytic
neighbourhood stays strictly above the real axis. -/
theorem highRectangleNhd_im_ne_zero {T₁ T₂ ε : ℝ}
    (hεT : ε < T₁) :
    ∀ z ∈ highRectangleNhd T₁ T₂ ε, z.im ≠ 0 := by
  intro z hz hz0
  simp only [highRectangleNhd, mem_inter_iff, mem_setOf_eq] at hz
  rcases hz with ⟨⟨_, _⟩, ⟨himLower, _⟩⟩
  rw [hz0] at himLower
  linarith

/-- The high rectangle is invariant under reflection across the critical line. -/
theorem highRectangleNhd_reflect_mem {T₁ T₂ ε : ℝ} {z : ℂ}
    (hz : z ∈ highRectangleNhd T₁ T₂ ε) :
    1 - conj z ∈ highRectangleNhd T₁ T₂ ε := by
  simp only [highRectangleNhd, mem_inter_iff, mem_setOf_eq] at hz ⊢
  rcases hz with ⟨⟨hreL, hreR⟩, ⟨himL, himR⟩⟩
  constructor
  · constructor <;> simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] <;> linarith
  · constructor <;> simp only [Complex.sub_im, Complex.one_im, Complex.conj_im] <;> linarith

/-- Every point of the closed manuscript contour rectangle belongs to its open
`ε`-enlargement. -/
theorem closedRectangle_subset_highRectangleNhd {T₁ T₂ ε : ℝ}
    (hε : 0 < ε) :
    {s : ℂ | -1 ≤ s.re ∧ s.re ≤ 2 ∧ T₁ ≤ s.im ∧ s.im ≤ T₂} ⊆
      highRectangleNhd T₁ T₂ ε := by
  intro s hs
  simp only [highRectangleNhd, mem_inter_iff, mem_setOf_eq]
  rcases hs with ⟨hreL, hreR, himL, himR⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The paper's Hardy gauge exists holomorphically on an open neighbourhood of
the entire high contour rectangle. -/
theorem exists_hardyGauge_on_highRectangle
    {T₁ T₂ ε : ℝ} (hε : 0 < ε) (hT : T₁ < T₂) (hεT : ε < T₁) :
    ∃ q : ℂ → ℂ,
      AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε) ∧
      ∀ z, q z ^ 2 = Analytic.chiOneSub z := by
  exact exists_hardyGaugeSquareRoot
    (isSimplyConnected_highRectangleNhd hε hT)
    (isOpen_highRectangleNhd T₁ T₂ ε)
    (highRectangleNhd_im_ne_zero hεT)

end HardyGaugeInvariantContourForm
end ZetaZero
