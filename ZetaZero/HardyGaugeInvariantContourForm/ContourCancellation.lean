import ZetaZero.HardyGaugeInvariantContourForm.HighRectangle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Cauchy cancellation on the high contour rectangle

This module isolates the Cauchy--Goursat step used repeatedly in the invariant
contour construction. Holomorphic summands on the closed manuscript rectangle
have zero boundary integral. The first application is the `f C_𝒵 B` term in
the same-form identity; later right-edge reductions can reuse the same API.
-/

open Complex Set intervalIntegral MeasureTheory

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- South-west corner of the manuscript rectangle. -/
def highRectangleSW (T : ℝ) : ℂ := (-1 : ℂ) + (T : ℂ) * I

/-- North-east corner of the manuscript rectangle. -/
def highRectangleNE (T : ℝ) : ℂ := (2 : ℂ) + (T : ℂ) * I

@[simp] theorem highRectangleSW_re (T : ℝ) : (highRectangleSW T).re = -1 := by
  simp [highRectangleSW]

@[simp] theorem highRectangleSW_im (T : ℝ) : (highRectangleSW T).im = T := by
  simp [highRectangleSW]

@[simp] theorem highRectangleNE_re (T : ℝ) : (highRectangleNE T).re = 2 := by
  simp [highRectangleNE]

@[simp] theorem highRectangleNE_im (T : ℝ) : (highRectangleNE T).im = T := by
  simp [highRectangleNE]

/-- Positively oriented boundary integral in Mathlib's rectangle normalization. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- Any function analytic on a neighbourhood containing a closed rectangle has
zero boundary integral around that rectangle. -/
theorem rectangleBoundaryIntegral_eq_zero_of_analyticOnNhd
    {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hsub : (uIcc z.re w.re ×ℂ uIcc z.im w.im) ⊆ U) :
    rectangleBoundaryIntegral f z w = 0 := by
  have hdiff : DifferentiableOn ℂ f (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    intro x hx
    exact (hf x (hsub hx)).differentiableAt.differentiableWithinAt
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using
    integral_boundary_rect_eq_zero_of_differentiableOn f z w hdiff

/-- Interval-integrability of an integrand on all four oriented rectangle edges. -/
def RectangleBoundaryIntervalIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im

/-- Pointwise continuity of an integrand at every boundary point. -/
def ContinuousAtOnRectangleBoundary (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  (∀ x ∈ uIcc z.re w.re, ContinuousAt f (x + z.im * I)) ∧
  (∀ x ∈ uIcc z.re w.re, ContinuousAt f (x + w.im * I)) ∧
  (∀ y ∈ uIcc z.im w.im, ContinuousAt f (w.re + y * I)) ∧
  (∀ y ∈ uIcc z.im w.im, ContinuousAt f (z.re + y * I))

/-- Pointwise continuity on the four edges implies interval-integrability. -/
theorem rectangleBoundaryIntervalIntegrable_of_continuousAtOnBoundary
    {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousAtOnRectangleBoundary f z w) :
    RectangleBoundaryIntervalIntegrable f z w := by
  rcases hf with ⟨hs, hn, he, hw⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    simpa [Function.comp_def] using
      ContinuousAt.comp_continuousWithinAt
        (f := fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I) (hs x hx) (by fun_prop)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    simpa [Function.comp_def] using
      ContinuousAt.comp_continuousWithinAt
        (f := fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I) (hn x hx) (by fun_prop)
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    simpa [Function.comp_def] using
      ContinuousAt.comp_continuousWithinAt
        (f := fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I) (he y hy) (by fun_prop)
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    simpa [Function.comp_def] using
      ContinuousAt.comp_continuousWithinAt
        (f := fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I) (hw y hy) (by fun_prop)

/-- Continuity on the closed rectangle implies interval-integrability on all
four boundary edges. -/
theorem rectangleBoundaryIntervalIntegrable_of_continuousOn
    {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (uIcc z.re w.re ×ℂ uIcc z.im w.im)) :
    RectangleBoundaryIntervalIntegrable f z w := by
  let rect : Set ℂ := uIcc z.re w.re ×ℂ uIcc z.im w.im
  have hSouthMap : MapsTo (fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I)
      (uIcc z.re w.re) rect := by
    intro x hx
    change (x : ℂ) + (z.im : ℂ) * I ∈ rect
    rw [mem_reProdIm]
    simpa using And.intro hx (left_mem_uIcc : z.im ∈ uIcc z.im w.im)
  have hNorthMap : MapsTo (fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I)
      (uIcc z.re w.re) rect := by
    intro x hx
    change (x : ℂ) + (w.im : ℂ) * I ∈ rect
    rw [mem_reProdIm]
    simpa using And.intro hx (right_mem_uIcc : w.im ∈ uIcc z.im w.im)
  have hEastMap : MapsTo (fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I)
      (uIcc z.im w.im) rect := by
    intro y hy
    change (w.re : ℂ) + (y : ℂ) * I ∈ rect
    rw [mem_reProdIm]
    simpa using And.intro (right_mem_uIcc : w.re ∈ uIcc z.re w.re) hy
  have hWestMap : MapsTo (fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I)
      (uIcc z.im w.im) rect := by
    intro y hy
    change (z.re : ℂ) + (y : ℂ) * I ∈ rect
    rw [mem_reProdIm]
    simpa using And.intro (left_mem_uIcc : z.re ∈ uIcc z.re w.re) hy
  have hSouthCont : ContinuousOn (fun x : ℝ => f (x + z.im * I))
      (uIcc z.re w.re) := by
    simpa [rect, Function.comp_def] using
      hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I)
        (uIcc z.re w.re)) hSouthMap
  have hNorthCont : ContinuousOn (fun x : ℝ => f (x + w.im * I))
      (uIcc z.re w.re) := by
    simpa [rect, Function.comp_def] using
      hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I)
        (uIcc z.re w.re)) hNorthMap
  have hEastCont : ContinuousOn (fun y : ℝ => f (w.re + y * I))
      (uIcc z.im w.im) := by
    simpa [rect, Function.comp_def] using
      hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I)
        (uIcc z.im w.im)) hEastMap
  have hWestCont : ContinuousOn (fun y : ℝ => f (z.re + y * I))
      (uIcc z.im w.im) := by
    simpa [rect, Function.comp_def] using
      hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I)
        (uIcc z.im w.im)) hWestMap
  exact ⟨hSouthCont.intervalIntegrable, hNorthCont.intervalIntegrable,
    hEastCont.intervalIntegrable, hWestCont.intervalIntegrable⟩

/-- Analyticity on a neighbourhood containing the closed rectangle implies
interval-integrability on all four boundary edges. -/
theorem rectangleBoundaryIntervalIntegrable_of_analyticOnNhd
    {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hsub : (uIcc z.re w.re ×ℂ uIcc z.im w.im) ⊆ U) :
    RectangleBoundaryIntervalIntegrable f z w := by
  apply rectangleBoundaryIntervalIntegrable_of_continuousOn
  intro s hs
  exact (hf s (hsub hs)).continuousAt.continuousWithinAt

/-- Boundary integration is additive once both summands are interval-integrable
on the four edges. -/
theorem rectangleBoundaryIntegral_add
    {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntervalIntegrable f z w)
    (hg : RectangleBoundaryIntervalIntegrable g z w) :
    rectangleBoundaryIntegral (fun s => f s + g s) z w =
      rectangleBoundaryIntegral f z w + rectangleBoundaryIntegral g z w := by
  rcases hf with ⟨hfs, hfn, hfe, hfw⟩
  rcases hg with ⟨hgs, hgn, hge, hgw⟩
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hfs hgs,
    intervalIntegral.integral_add hfn hgn,
    intervalIntegral.integral_add hfe hge,
    intervalIntegral.integral_add hfw hgw]
  ring

/-- A scalar function is nonzero on all four rectangle edges. -/
def NonzeroOnRectangleBoundary (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  (∀ x ∈ uIcc z.re w.re, F (x + z.im * I) ≠ 0) ∧
  (∀ x ∈ uIcc z.re w.re, F (x + w.im * I) ≠ 0) ∧
  (∀ y ∈ uIcc z.im w.im, F (w.re + y * I) ≠ 0) ∧
  (∀ y ∈ uIcc z.im w.im, F (z.re + y * I) ≠ 0)

/-- Two integrands agree on all four oriented edges of a rectangle. -/
def EqOnRectangleBoundary (f g : ℂ → ℂ) (z w : ℂ) : Prop :=
  (∀ x ∈ uIcc z.re w.re, f (x + z.im * I) = g (x + z.im * I)) ∧
  (∀ x ∈ uIcc z.re w.re, f (x + w.im * I) = g (x + w.im * I)) ∧
  (∀ y ∈ uIcc z.im w.im, f (w.re + y * I) = g (w.re + y * I)) ∧
  (∀ y ∈ uIcc z.im w.im, f (z.re + y * I) = g (z.re + y * I))

/-- Boundary integration only depends on the values of the integrand on the
four edges. -/
theorem rectangleBoundaryIntegral_congr
    {f g : ℂ → ℂ} {z w : ℂ} (hfg : EqOnRectangleBoundary f g z w) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral g z w := by
  rcases hfg with ⟨hSouth, hNorth, hEast, hWest⟩
  have hs : (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) =
      ∫ x : ℝ in z.re..w.re, g (x + z.im * I) :=
    intervalIntegral.integral_congr hSouth
  have hn : (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) =
      ∫ x : ℝ in z.re..w.re, g (x + w.im * I) :=
    intervalIntegral.integral_congr hNorth
  have he : (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) =
      ∫ y : ℝ in z.im..w.im, g (w.re + y * I) :=
    intervalIntegral.integral_congr hEast
  have hw : (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      ∫ y : ℝ in z.im..w.im, g (z.re + y * I) :=
    intervalIntegral.integral_congr hWest
  simp [rectangleBoundaryIntegral, hs, hn, he, hw]

/-- If `f = correction + g` on the four edges, the correction has zero boundary
integral, and both summands are interval-integrable, then `f` and `g` have the
same rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_eq_of_eq_add_zero
    {f correction g : ℂ → ℂ} {z w : ℂ}
    (hfg : EqOnRectangleBoundary f (fun s => correction s + g s) z w)
    (hcint : RectangleBoundaryIntervalIntegrable correction z w)
    (hgint : RectangleBoundaryIntervalIntegrable g z w)
    (hc0 : rectangleBoundaryIntegral correction z w = 0) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral g z w := by
  rw [rectangleBoundaryIntegral_congr hfg]
  rw [rectangleBoundaryIntegral_add hcint hgint, hc0, zero_add]

/-- The Mathlib closed rectangle determined by the manuscript corners lies in
its open `ε`-enlargement. -/
theorem mathlibRectangle_subset_highRectangleNhd
    {T₁ T₂ ε : ℝ} (hε : 0 < ε) (hT : T₁ ≤ T₂) :
    (uIcc (highRectangleSW T₁).re (highRectangleNE T₂).re ×ℂ
      uIcc (highRectangleSW T₁).im (highRectangleNE T₂).im) ⊆
      highRectangleNhd T₁ T₂ ε := by
  intro z hz
  rw [mem_reProdIm] at hz
  rcases hz with ⟨hre, him⟩
  rw [highRectangleSW_re, highRectangleNE_re,
    uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2), mem_Icc] at hre
  rw [highRectangleSW_im, highRectangleNE_im, uIcc_of_le hT, mem_Icc] at him
  exact closedRectangle_subset_highRectangleNhd hε
    ⟨hre.1, hre.2, him.1, him.2⟩

/-- Cauchy--Goursat on the actual high contour rectangle. This is the reusable
seam used to remove a holomorphic correction from the invariant contour
integrand. -/
theorem rectangleBoundaryIntegral_eq_zero_on_highRectangle
    {f : ℂ → ℂ} {T₁ T₂ ε : ℝ}
    (hε : 0 < ε) (hT : T₁ ≤ T₂)
    (hf : AnalyticOnNhd ℂ f (highRectangleNhd T₁ T₂ ε)) :
    rectangleBoundaryIntegral f (highRectangleSW T₁) (highRectangleNE T₂) = 0 :=
  rectangleBoundaryIntegral_eq_zero_of_analyticOnNhd hf
    (mathlibRectangle_subset_highRectangleNhd hε hT)

end HardyGaugeInvariantContourForm
end ZetaZero
