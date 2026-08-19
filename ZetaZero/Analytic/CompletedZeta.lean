import ZetaZero.Analytic.ZeroCounting
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Completed zeta on the critical strip

This module records the Mathlib normalization of the completed Riemann zeta
function and the analytic identities needed by the Hardy-gauge layer.  The
proof architecture follows the classical seam already formalized in the local
`zeta-23-lean` reference project, but the declarations here live entirely in
the `ZetaZero` namespace and are checked against this project's Mathlib version.
-/

open Complex Filter Topology

noncomputable section

namespace ZetaZero
namespace Analytic

/-- `Gammaℝ` is differentiable throughout the open right half-plane. -/
theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hpow : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hgamma : DifferentiableAt ℂ (fun u : ℂ => Gamma (u / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp s
      (differentiableAt_id.div_const _)
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdef : Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Gamma (u / 2) :=
    funext Gammaℝ_def
  rw [hdef]
  exact hpow.mul hgamma

/-- `Gammaℝ` is analytic throughout the open right half-plane. -/
theorem analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt
    (fun u hu => (differentiableAt_Gammaℝ hu).differentiableWithinAt)
    (hopen.mem_nhds hs)

/-- Away from its pole at `1`, `riemannZeta` is analytic. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun _ hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- On the open right half-plane, the completed zeta germ is `Gammaℝ * ζ`. -/
theorem completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hGamma := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp

/-- On the zero-free part of the right half-plane,
`Λ'/Λ = Gammaℝ'/Gammaℝ + ζ'/ζ`. -/
theorem logDeriv_completedZeta (s : ℂ) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) (hre : 0 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := completedZeta_eventuallyEq_mul hre
  have heq :
      logDeriv completedRiemannZeta s =
        logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hre) hzeta
    (differentiableAt_Gammaℝ hre) (differentiableAt_riemannZeta hs1)

/-- Log-derivative form of the completed-zeta functional equation. -/
theorem logDeriv_completedZeta_one_sub (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) =
      -logDeriv completedRiemannZeta s := by
  have hcomp : completedRiemannZeta =
      completedRiemannZeta ∘ (fun u : ℂ => 1 - u) := by
    funext u
    simp [completedRiemannZeta_one_sub]
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (sub_ne_zero.mpr (Ne.symm hs1)) (by
      intro h
      apply hs0
      linear_combination -h)
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hkey := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at hkey
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [hkey, hderiv]
  ring

/-- In the open critical strip, completed zeta and zeta have exactly the same
zeros and the same analytic order. -/
theorem completedZeta_zeros_strip {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    (completedRiemannZeta rho = 0 ↔ IsNontrivialZetaZero rho) ∧
      analyticOrderAt completedRiemannZeta rho = analyticOrderAt riemannZeta rho := by
  have hrho1 : rho ≠ 1 := fun h => by simp [h] at h1
  have hGamma : Gammaℝ rho ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hev := completedZeta_eventuallyEq_mul h0
  have hval : completedRiemannZeta rho = Gammaℝ rho * riemannZeta rho := hev.eq_of_nhds
  have hGammaAn := analyticAt_Gammaℝ h0
  have hzetaAn := analyticAt_riemannZeta hrho1
  refine ⟨?_, ?_⟩
  · rw [hval, mul_eq_zero, IsNontrivialZetaZero]
    constructor
    · rintro (hGamma0 | hzeta)
      · exact absurd hGamma0 hGamma
      · exact ⟨hzeta, h0, h1⟩
    · rintro ⟨hzeta, -, -⟩
      exact Or.inr hzeta
  · rw [analyticOrderAt_congr hev]
    have hmul := analyticOrderAt_mul hGammaAn hzetaAn
    rw [show (Gammaℝ * riemannZeta) =
      (fun u => Gammaℝ u * riemannZeta u) from rfl] at hmul
    rw [hmul, hGammaAn.analyticOrderAt_eq_zero.mpr hGamma, zero_add]

end Analytic
end ZetaZero
