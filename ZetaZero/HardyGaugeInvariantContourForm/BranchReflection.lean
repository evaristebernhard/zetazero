import ZetaZero.Analytic.ZetaReflection
import ZetaZero.HardyGaugeInvariantContourForm.CriticalLinePhase
import ZetaZero.HardyGaugeInvariantContourForm.HighRectangle
import Mathlib.Topology.Algebra.Field

/-!
# Reflection law for the holomorphic Hardy branch

For a holomorphic square-root branch `q² = χ(1-s)` on the high rectangle, put

`q†(s) = conj (q (1-conj s))`.

Both `q†` and `q⁻¹` are continuous square roots of the same nonvanishing
function.  They agree at any critical-line point in the rectangle, because every
square-root branch there is unitary.  Preconnectedness therefore gives
`q† = q⁻¹` throughout the rectangle.  Combining this with the zeta functional
equation yields the exact Hardy-gauge reflection law.
-/

open Complex Filter Set Topology
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Reflection across the critical line. -/
def hardyReflect (s : ℂ) : ℂ := 1 - conj s

/-- Conjugate-reflected branch. -/
def branchDagger (q : ℂ → ℂ) (s : ℂ) : ℂ := conj (q (hardyReflect s))

/-- The analytic Hardy gauge attached to a square-root branch. -/
def hardyGauge (q : ℂ → ℂ) (s : ℂ) : ℂ := q s * riemannZeta s

@[simp] theorem hardyReflect_criticalLine (t : ℝ) :
    hardyReflect (criticalLine t) = criticalLine t := by
  exact one_sub_conj_criticalLine t

/-- The enlarged high rectangle is invariant under `hardyReflect`. -/
theorem hardyReflect_mem_highRectangle {T₁ T₂ ε : ℝ} {s : ℂ}
    (hs : s ∈ highRectangleNhd T₁ T₂ ε) :
    hardyReflect s ∈ highRectangleNhd T₁ T₂ ε := by
  exact highRectangleNhd_reflect_mem hs

/-- A square-root branch is nonzero throughout a high rectangle that stays off
the real axis. -/
theorem branch_ne_zero_on_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hεT : ε < T₁) :
    ∀ z ∈ highRectangleNhd T₁ T₂ ε, q z ≠ 0 := by
  intro z hz hq0
  have hchi := Analytic.chiOneSub_ne_zero_of_im_ne_zero
    (highRectangleNhd_im_ne_zero hεT z hz)
  apply hchi
  rw [← hqpow z, hq0]
  simp

/-- The dagger branch and inverse branch have the same square. -/
theorem branchDagger_sq_eq_inv_sq
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (hεT : ε < T₁) :
    ∀ s ∈ highRectangleNhd T₁ T₂ ε,
      branchDagger q s ^ 2 = (q s)⁻¹ ^ 2 := by
  intro s hs
  have him := highRectangleNhd_im_ne_zero hεT s hs
  rw [branchDagger, ← map_pow, hqpow, hardyReflect]
  rw [Analytic.conj_chiOneSub_one_sub_conj him]
  rw [← hqpow s, inv_pow]

/-- The conjugate-reflected branch equals the inverse branch everywhere on the
high rectangle. -/
theorem branchDagger_eq_inv_on_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hε : 0 < ε) (hT : T₁ < T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z) :
    ∀ s ∈ highRectangleNhd T₁ T₂ ε,
      branchDagger q s = (q s)⁻¹ := by
  let U := highRectangleNhd T₁ T₂ ε
  have hqcont : ContinuousOn q U := hqa.continuousOn
  have hrefcont : ContinuousOn hardyReflect U := by
    unfold hardyReflect
    exact (continuous_const.sub continuous_star).continuousOn
  have hrefmaps : MapsTo hardyReflect U U := by
    intro s hs
    exact hardyReflect_mem_highRectangle hs
  have hqcomp : ContinuousOn (fun s => q (hardyReflect s)) U :=
    hqcont.comp hrefcont hrefmaps
  have hdagger : ContinuousOn (branchDagger q) U := by
    exact continuous_star.comp_continuousOn hqcomp
  have hqne : ∀ z ∈ U, q z ≠ 0 := by
    exact branch_ne_zero_on_highRectangle hqpow hεT
  have hinv : ContinuousOn (fun s => (q s)⁻¹) U :=
    ContinuousOn.inv₀ hqcont hqne
  have hinvne : ∀ z ∈ U, (q z)⁻¹ ≠ 0 := by
    intro z hz
    exact inv_ne_zero (hqne z hz)
  have hsq : EqOn ((branchDagger q) ^ 2) ((fun s => (q s)⁻¹) ^ 2) U := by
    intro s hs
    exact branchDagger_sq_eq_inv_sq hqpow hεT s hs
  let t₀ : ℝ := (T₁ + T₂) / 2
  have ht₀ : criticalLine t₀ ∈ U := by
    change criticalLine t₀ ∈ highRectangleNhd T₁ T₂ ε
    simp only [highRectangleNhd, mem_inter_iff, mem_setOf_eq, criticalLine_re,
      criticalLine_im, t₀]
    constructor
    · constructor <;> linarith
    · constructor <;> linarith
  have hbase : branchDagger q (criticalLine t₀) = (q (criticalLine t₀))⁻¹ := by
    rw [branchDagger, hardyReflect_criticalLine]
    exact conj_branch_eq_inv_on_criticalLine hqpow t₀
  exact (convex_highRectangleNhd T₁ T₂ ε).isPreconnected.eq_of_sq_eq
    hdagger hinv hsq (fun {z} hz => hinvne z hz) ht₀ hbase

/-- Exact Hardy-gauge reflection law on the high rectangle. -/
theorem hardyGauge_reflection_on_highRectangle
    {T₁ T₂ ε : ℝ} {q : ℂ → ℂ}
    (hε : 0 < ε) (hT : T₁ < T₂) (hεT : ε < T₁)
    (hqa : AnalyticOnNhd ℂ q (highRectangleNhd T₁ T₂ ε))
    (hqpow : ∀ z, q z ^ 2 = Analytic.chiOneSub z) :
    ∀ s ∈ highRectangleNhd T₁ T₂ ε,
      hardyGauge q (hardyReflect s) = conj (hardyGauge q s) := by
  intro s hs
  have him := highRectangleNhd_im_ne_zero hεT s hs
  have hsref := hardyReflect_mem_highRectangle hs
  have hqne := branch_ne_zero_on_highRectangle hqpow hεT s hs
  have hdag := branchDagger_eq_inv_on_highRectangle hε hT hεT hqa hqpow s hs
  have hqref : q (hardyReflect s) = (conj (q s))⁻¹ := by
    have hc := congrArg conj hdag
    simpa [branchDagger, hardyReflect, map_inv₀] using hc
  have hzeta : riemannZeta (hardyReflect s) =
      Analytic.chiOneSub (conj s) * conj (riemannZeta s) := by
    rw [hardyReflect,
      Analytic.riemannZeta_one_sub_eq_chiOneSub_mul_of_im_ne_zero (by simpa using him),
      Analytic.riemannZeta_conj (by
        intro h
        apply him
        have hc := congrArg Complex.im h
        simpa using hc)]
  have hchi : Analytic.chiOneSub (conj s) = (conj (q s)) ^ 2 := by
    rw [Analytic.chiOneSub_conj, ← map_pow, hqpow]
  rw [hardyGauge, hardyGauge, hqref, hzeta, hchi, map_mul]
  have hconjq : conj (q s) ≠ 0 := by simp [hqne]
  field_simp [hconjq]

end HardyGaugeInvariantContourForm
end ZetaZero
