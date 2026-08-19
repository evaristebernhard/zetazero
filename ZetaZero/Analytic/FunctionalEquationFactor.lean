import ZetaZero.Analytic.CompletedZeta
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Functional-equation factors for the Hardy gauge

For formalization it is substantially cleaner to use the completed-zeta
normalization

`chiFE(s) = Gammaℝ(1-s) / Gammaℝ(s)`

so that `ζ(s) = chiFE(s) ζ(1-s)`.  The manuscript uses the reciprocal factor
`χ(1-s)` under the square root; we therefore set

`chiOneSub(s) = chiFE(1-s) = Gammaℝ(s) / Gammaℝ(1-s)`.

Off the real axis all Gamma factors below are analytic units.  On the open
critical strip the same is true by positivity of the real parts.
-/

open Complex Filter Set Topology
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace Analytic

/-- A non-real complex number cannot be a non-positive integer. -/
theorem ne_neg_nat_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) :
    s ≠ -(m : ℂ) := by
  intro h
  apply hs
  rw [h]
  simp

/-- A non-real complex number is not `0`. -/
theorem ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := by
  intro h
  apply hs
  rw [h]
  simp

/-- A non-real complex number is not `1`. -/
theorem ne_one_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := by
  intro h
  apply hs
  rw [h]
  simp

/-- `1-s` is non-real whenever `s` is. -/
theorem im_one_sub_ne_zero {s : ℂ} (hs : s.im ≠ 0) : (1 - s).im ≠ 0 := by
  simpa using hs

/-- `Gammaℝ` is nonzero away from the real axis. -/
theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h
  apply hs
  rw [h]
  simp

/-- `Gammaℝ` is differentiable away from the real axis. -/
theorem differentiableAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine DifferentiableAt.const_cpow ?_ (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    exact differentiableAt_id.neg.div_const 2
  have hgamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma _ (fun m => by
      intro h
      apply hs
      have him := congrArg Complex.im h
      simpa using him)).comp s (differentiableAt_id.div_const 2)
  have hdef : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
    funext Gammaℝ_def
  rw [hdef]
  exact hpow.mul hgamma

/-- `Gammaℝ` is analytic away from the real axis. -/
theorem analyticAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} :=
    isOpen_ne_fun Complex.continuous_im continuous_const
  exact DifferentiableOn.analyticAt
    (fun z hz => (differentiableAt_Gammaℝ_of_im_ne_zero hz).differentiableWithinAt)
    (hopen.mem_nhds hs)

/-- Complex conjugation commutes with `Gammaℝ`. -/
theorem Gammaℝ_conj (s : ℂ) :
    Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gammaℝ s) := by
  have cpow_ofReal_conj {x : ℝ} (hx : 0 < x) (w : ℂ) :
      (x : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ ((x : ℂ) ^ w) := by
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0, ← Complex.exp_conj, map_mul,
      ← Complex.ofReal_log hx.le, Complex.conj_ofReal]
  have h1 : -(starRingEnd ℂ s) / 2 = starRingEnd ℂ (-s / 2) := by
    simp [map_div₀, map_neg, map_ofNat]
  have h2 : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by
    simp [map_div₀, map_ofNat]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, h1, h2,
    cpow_ofReal_conj Real.pi_pos, Complex.Gamma_conj, map_mul]

/-- Classical functional-equation factor `χ(s)`. -/
def chiFE (s : ℂ) : ℂ := Gammaℝ (1 - s) / Gammaℝ s

/-- The factor appearing in the manuscript's Hardy gauge: `χ(1-s)`. -/
def chiOneSub (s : ℂ) : ℂ := Gammaℝ s / Gammaℝ (1 - s)

@[simp] theorem chiFE_one_sub (s : ℂ) : chiFE (1 - s) = chiOneSub s := by
  simp [chiFE, chiOneSub]

@[simp] theorem chiOneSub_one_sub (s : ℂ) : chiOneSub (1 - s) = chiFE s := by
  simp [chiFE, chiOneSub]

/-- `χ(s)χ(1-s)=1` away from the real axis. -/
theorem chiFE_mul_chiFE_one_sub {s : ℂ} (hs : s.im ≠ 0) :
    chiFE s * chiFE (1 - s) = 1 := by
  rw [chiFE, chiFE, sub_sub_cancel]
  field_simp [Gammaℝ_ne_zero_of_im_ne_zero hs,
    Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)]

/-- The two reciprocal factors multiply to one off the real axis. -/
theorem chiFE_mul_chiOneSub {s : ℂ} (hs : s.im ≠ 0) :
    chiFE s * chiOneSub s = 1 := by
  simpa using chiFE_mul_chiFE_one_sub hs

/-- `χ(1-s)` has no zeros away from the real axis. -/
theorem chiOneSub_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    chiOneSub s ≠ 0 :=
  div_ne_zero (Gammaℝ_ne_zero_of_im_ne_zero hs)
    (Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs))

/-- `χ(1-s)` is analytic away from the real axis. -/
theorem analyticAt_chiOneSub_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ chiOneSub s := by
  have hnum := analyticAt_Gammaℝ_of_im_ne_zero hs
  have hden : AnalyticAt ℂ (fun z : ℂ => Gammaℝ (1 - z)) s :=
    (analyticAt_Gammaℝ_of_im_ne_zero (im_one_sub_ne_zero hs)).comp
      (analyticAt_const.sub analyticAt_id)
  have hdef : chiOneSub = fun z : ℂ => Gammaℝ z / Gammaℝ (1 - z) := rfl
  rw [hdef]
  exact hnum.div hden (Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs))

/-- `χ(1-s)` has no zeros in the open critical strip. -/
theorem chiOneSub_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    chiOneSub s ≠ 0 := by
  have hs : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have h1s : 0 < (1 - s).re := by simp; linarith
  exact div_ne_zero hs (Gammaℝ_ne_zero_of_re_pos h1s)

/-- `χ(1-s)` is analytic in the open critical strip. -/
theorem analyticAt_chiOneSub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    AnalyticAt ℂ chiOneSub s := by
  have h1s : 0 < (1 - s).re := by simp; linarith
  have hden : AnalyticAt ℂ (fun z : ℂ => Gammaℝ (1 - z)) s :=
    (analyticAt_Gammaℝ h1s).comp (analyticAt_const.sub analyticAt_id)
  have hdef : chiOneSub = fun z : ℂ => Gammaℝ z / Gammaℝ (1 - z) := rfl
  rw [hdef]
  exact (analyticAt_Gammaℝ h0).div hden (Gammaℝ_ne_zero_of_re_pos h1s)

/-- Completed zeta equals `Gammaℝ * ζ` whenever the displayed Gamma factor is
nonzero. -/
theorem completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ}
    (hs0 : s ≠ 0) (hGamma : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- Functional equation written in the manuscript normalization, valid off the
real axis. -/
theorem riemannZeta_one_sub_eq_chiOneSub_mul_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) :
    riemannZeta (1 - s) = chiOneSub s * riemannZeta s := by
  have hs0 := ne_zero_of_im_ne_zero hs
  have h1s0 : (1 - s) ≠ 0 := ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)
  have hGs := Gammaℝ_ne_zero_of_im_ne_zero hs
  have hG1 := Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)
  have hEqS := completedRiemannZeta_eq_Gammaℝ_mul hs0 hGs
  have hEq1 := completedRiemannZeta_eq_Gammaℝ_mul h1s0 hG1
  have hLambda : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  rw [chiOneSub]
  field_simp [hG1]
  rw [hEqS, hEq1] at hLambda
  linear_combination hLambda

/-- Functional equation in the open critical strip. -/
theorem riemannZeta_one_sub_eq_chiOneSub_mul_of_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = chiOneSub s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have h1sre : 0 < (1 - s).re := by simp; linarith
  have h1s0 : (1 - s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hGs := Gammaℝ_ne_zero_of_re_pos h0
  have hG1 := Gammaℝ_ne_zero_of_re_pos h1sre
  have hEqS := completedRiemannZeta_eq_Gammaℝ_mul hs0 hGs
  have hEq1 := completedRiemannZeta_eq_Gammaℝ_mul h1s0 hG1
  have hLambda : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  rw [chiOneSub]
  field_simp [hG1]
  rw [hEqS, hEq1] at hLambda
  linear_combination hLambda

/-- Conjugation symmetry of the functional-equation factor. -/
theorem chiFE_conj (s : ℂ) : chiFE (conj s) = conj (chiFE s) := by
  rw [chiFE, chiFE, Gammaℝ_conj]
  have hone : (1 : ℂ) - conj s = conj (1 - s) := by simp
  rw [hone, Gammaℝ_conj, ← map_div₀]

/-- Conjugation symmetry of the reciprocal Hardy-gauge factor. -/
theorem chiOneSub_conj (s : ℂ) : chiOneSub (conj s) = conj (chiOneSub s) := by
  rw [chiOneSub, chiOneSub, Gammaℝ_conj]
  have hone : (1 : ℂ) - conj s = conj (1 - s) := by simp
  rw [hone, Gammaℝ_conj, ← map_div₀]

/-- The conjugate-reflected square of the Hardy branch is the reciprocal factor
needed in the reflection argument. -/
theorem conj_chiOneSub_one_sub_conj {s : ℂ} (hs : s.im ≠ 0) :
    conj (chiOneSub (1 - conj s)) = (chiOneSub s)⁻¹ := by
  rw [chiOneSub_one_sub, chiFE_conj, Complex.conj_conj]
  have hprod := chiFE_mul_chiOneSub hs
  exact (mul_eq_one_iff_eq_inv₀ (chiOneSub_ne_zero_of_im_ne_zero hs)).1 hprod

/-- `chiOneSub` is analytic on the open critical strip. -/
theorem analyticOnNhd_chiOneSub_criticalStrip :
    AnalyticOnNhd ℂ chiOneSub {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs
  exact analyticAt_chiOneSub hs.1 hs.2

/-- `chiOneSub` is nowhere zero on the open critical strip. -/
theorem chiOneSub_ne_zero_on_criticalStrip :
    ∀ s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1}, chiOneSub s ≠ 0 := by
  intro s hs
  exact chiOneSub_ne_zero hs.1 hs.2

end Analytic
end ZetaZero
