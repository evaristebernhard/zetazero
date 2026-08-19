import ZetaZero.HardyGaugeInvariantContourForm.PacketBoundaryIntegrability
import ZetaZero.Analytic.RectangleArgumentPrinciple

/-!
# Packet same-form contour to the zero sum

This is the first genuinely global residue step in the main Hardy-gauge line.
It combines the packet same-form contour identity with the weighted rectangle
argument principle imported through `ZetaZero.Analytic.RectangleArgumentPrinciple`.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- The normalized rectangle integral used by the imported residue calculus is
exactly `1/(2πi)` times the manuscript boundary integral. -/
theorem rectangleIntegral'_eq_normalizedBoundaryIntegral
    {f : ℂ → ℂ} {z w : ℂ} :
    RectangleIntegral' f z w =
      (1 / (2 * (Real.pi : ℂ) * I)) * rectangleBoundaryIntegral f z w := by
  simp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
    rectangleBoundaryIntegral, smul_eq_mul]

/-- Convert the four-edge nonvanishing predicate used by the manuscript contour
API into the set-theoretic `RectangleBorder` predicate used by the residue
calculus. -/
theorem rectangleBorder_nonzero_of_nonzeroOnRectangleBoundary
    {F : ℂ → ℂ} {z w : ℂ}
    (hF : NonzeroOnRectangleBoundary F z w) :
    ∀ s ∈ RectangleBorder z w, F s ≠ 0 := by
  rcases hF with ⟨hSouth, hNorth, hEast, hWest⟩
  intro s hs
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hs
  rcases hs with ((hsSouth | hsWest) | hsNorth) | hsEast
  · have hsEq : (s.re : ℂ) + (z.im : ℂ) * I = s := by
      apply Complex.ext
      · simp
      · simp [hsSouth.2]
    rw [← hsEq]
    exact hSouth s.re hsSouth.1
  · have hsEq : (z.re : ℂ) + (s.im : ℂ) * I = s := by
      apply Complex.ext
      · simp [hsWest.1]
      · simp
    rw [← hsEq]
    exact hWest s.im hsWest.2
  · have hsEq : (s.re : ℂ) + (w.im : ℂ) * I = s := by
      apply Complex.ext
      · simp
      · simp [hsNorth.2]
    rw [← hsEq]
    exact hNorth s.re hsNorth.1
  · have hsEq : (w.re : ℂ) + (s.im : ℂ) * I = s := by
      apply Complex.ext
      · simp [hsEast.1]
      · simp
    rw [← hsEq]
    exact hEast s.im hsEast.2

/-- Weighted argument principle for the actual packet-polarized `Z₁'/Z₁`
integrand on the high rectangle.  The finite set `Z` is any exact enumeration
of the zeros of `Z₁` in the closed rectangle. -/
theorem packetZetaOne_weightedArgumentPrinciple
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {Z : Finset ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hz1 : NonzeroOnRectangleBoundary zetaOne
      (highRectangleSW T₁) (highRectangleNE T₂))
    (hZ : ∀ s ∈ Rectangle (highRectangleSW T₁) (highRectangleNE T₂),
      zetaOne s = 0 ↔ s ∈ Z)
    (hZsub : (Z : Set ℂ) ⊆ Rectangle (highRectangleSW T₁) (highRectangleNE T₂)) :
    (1 / (2 * (Real.pi : ℂ) * I)) *
        rectangleBoundaryIntegral
          (fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
            packetPolarization ψ v w s)
          (highRectangleSW T₁) (highRectangleNE T₂) =
      ∑ ρ ∈ Z, (analyticOrderNatAt zetaOne ρ : ℂ) *
        (hardyCurvature q ρ * packetPolarization ψ v w ρ) := by
  let z := highRectangleSW T₁
  let w₀ := highRectangleNE T₂
  let g := fun s => hardyCurvature q s * packetPolarization ψ v w s
  have hre : z.re ≤ w₀.re := by norm_num [z, w₀]
  have him : z.im ≤ w₀.im := by simpa [z, w₀] using hT
  have hsub : Rectangle z w₀ ⊆ highRectangleNhd T₁ T₂ ε := by
    simpa [Rectangle, z, w₀] using mathlibRectangle_subset_highRectangleNhd hε hT
  have hf : AnalyticOnNhd ℂ zetaOne (Rectangle z w₀) := by
    intro s hs
    exact analyticOnNhd_zetaOne_highRectangle hεT s (hsub hs)
  have hgHigh : AnalyticOnNhd ℂ g (highRectangleNhd T₁ T₂ ε) := by
    exact (analyticOnNhd_hardyCurvature_highRectangle hεT hqa).mul
      (analyticOnNhd_packetPolarization hψ v w (highRectangleNhd T₁ T₂ ε))
  have hg : AnalyticOnNhd ℂ g (Rectangle z w₀) := by
    intro s hs
    exact hgHigh s (hsub hs)
  have hborder : ∀ s ∈ RectangleBorder z w₀, zetaOne s ≠ 0 := by
    exact rectangleBorder_nonzero_of_nonzeroOnRectangleBoundary hz1
  have harg := ZetaZero.Analytic.rectangleWeightedArgumentPrinciple
    (f := zetaOne) (g := g) hre him hf hg hborder Z
    (by simpa [z, w₀] using hZ) (by simpa [z, w₀] using hZsub)
  rw [rectangleIntegral'_eq_normalizedBoundaryIntegral] at harg
  simpa [z, w₀, g, logDeriv_apply, mul_assoc, mul_left_comm, mul_comm] using harg

/-- Main zero-side contour identity: the normalized Hardy logarithmic-derivative
packet form is exactly the multiplicity-weighted finite sum over the `Z₁` zeros
inside the high rectangle. -/
theorem packetSameForm_zeroSum
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ} {Z : Finset ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hz1 : NonzeroOnRectangleBoundary zetaOne
      (highRectangleSW T₁) (highRectangleNE T₂))
    (hZ : ∀ s ∈ Rectangle (highRectangleSW T₁) (highRectangleNE T₂),
      zetaOne s = 0 ↔ s ∈ Z)
    (hZsub : (Z : Set ℂ) ⊆ Rectangle (highRectangleSW T₁) (highRectangleNE T₂)) :
    (1 / (2 * (Real.pi : ℂ) * I)) *
        rectangleBoundaryIntegral
          (fun s => (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
            hardyCurvature q s * packetPolarization ψ v w s)
          (highRectangleSW T₁) (highRectangleNE T₂) =
      ∑ ρ ∈ Z, (analyticOrderNatAt zetaOne ρ : ℂ) *
        (hardyCurvature q ρ * packetPolarization ψ v w ρ) := by
  have hsame := packetSameForm_boundaryIntegral_eq_of_nonzero
    (v := v) (w := w) hψ hε hT hεT hqa hqpow hz1
  calc
    (1 / (2 * (Real.pi : ℂ) * I)) *
        rectangleBoundaryIntegral
          (fun s => (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
            hardyCurvature q s * packetPolarization ψ v w s)
          (highRectangleSW T₁) (highRectangleNE T₂) =
      (1 / (2 * (Real.pi : ℂ) * I)) *
        rectangleBoundaryIntegral
          (fun s => (deriv zetaOne s / zetaOne s) * hardyCurvature q s *
            packetPolarization ψ v w s)
          (highRectangleSW T₁) (highRectangleNE T₂) := by rw [hsame]
    _ = ∑ ρ ∈ Z, (analyticOrderNatAt zetaOne ρ : ℂ) *
        (hardyCurvature q ρ * packetPolarization ψ v w ρ) :=
      packetZetaOne_weightedArgumentPrinciple hψ hε hT hεT hqa hz1 hZ hZsub

/-- Self-contained zero-sum form: zero avoidance on the contour automatically
produces the finite set of interior `Z₁` zeros needed by the residue theorem. -/
theorem exists_packetSameForm_zeroSum
    {ι : Type*} [Fintype ι] {ψ : ι → ℂ → ℂ} {v w : ι → ℂ}
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hψ : ∀ ν, Differentiable ℂ (ψ ν))
    (hε : 0 < ε) (hT : T₁ ≤ T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hz1 : NonzeroOnRectangleBoundary zetaOne
      (highRectangleSW T₁) (highRectangleNE T₂)) :
    ∃ Z : Finset ℂ,
      (∀ s ∈ Rectangle (highRectangleSW T₁) (highRectangleNE T₂),
        zetaOne s = 0 ↔ s ∈ Z) ∧
      (1 / (2 * (Real.pi : ℂ) * I)) *
          rectangleBoundaryIntegral
            (fun s => (deriv (deriv (hardyGauge q)) s / deriv (hardyGauge q) s) *
              hardyCurvature q s * packetPolarization ψ v w s)
            (highRectangleSW T₁) (highRectangleNE T₂) =
        ∑ ρ ∈ Z, (analyticOrderNatAt zetaOne ρ : ℂ) *
          (hardyCurvature q ρ * packetPolarization ψ v w ρ) := by
  let z := highRectangleSW T₁
  let w₀ := highRectangleNE T₂
  have hsub : Rectangle z w₀ ⊆ highRectangleNhd T₁ T₂ ε := by
    simpa [Rectangle, z, w₀] using mathlibRectangle_subset_highRectangleNhd hε hT
  have hf : AnalyticOnNhd ℂ zetaOne (Rectangle z w₀) := by
    intro s hs
    exact analyticOnNhd_zetaOne_highRectangle hεT s (hsub hs)
  have hborder : ∀ s ∈ RectangleBorder z w₀, zetaOne s ≠ 0 :=
    rectangleBorder_nonzero_of_nonzeroOnRectangleBoundary hz1
  have hz0 : zetaOne z ≠ 0 := by
    exact hborder z (Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩)))
  let zeroSet : Set ℂ := Rectangle z w₀ ∩ zetaOne ⁻¹' {0}
  have hfinite : zeroSet.Finite := by
    simpa [zeroSet] using Zeta23.Analytic.finite_zeros_rectangle
      hf (left_mem_rect z w₀) hz0
  let Z : Finset ℂ := hfinite.toFinset
  have hZ : ∀ s ∈ Rectangle z w₀, zetaOne s = 0 ↔ s ∈ Z := by
    intro s hs
    simp [Z, zeroSet, Set.Finite.mem_toFinset, hs]
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w₀ := by
    intro s hs
    have hs' : s ∈ zeroSet := by
      simpa [Z, Set.Finite.mem_toFinset] using hs
    exact hs'.1
  refine ⟨Z, ?_, ?_⟩
  · simpa [z, w₀] using hZ
  · exact packetSameForm_zeroSum hψ hε hT hεT hqa hqpow hz1
      (by simpa [z, w₀] using hZ) (by simpa [z, w₀] using hZsub)

end HardyGaugeInvariantContourForm
end ZetaZero
