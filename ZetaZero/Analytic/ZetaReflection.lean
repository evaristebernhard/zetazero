/-
Portions of the proof architecture in this file are adapted from
`zeta-23-lean/Zeta23/ZetaReflect.lean`, copyright (c) 2026 Anthropic, PBC,
released under the Apache 2.0 license.
-/

import ZetaZero.Analytic.FunctionalEquationFactor
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Reflection symmetry of zeta zeros

This module proves, from Mathlib's zeta function and functional equation, that
`rho ↦ 1 - conj rho` preserves nontrivial zeta zeros and their analytic
multiplicity.  These are the symmetry facts used later when off-critical-line
zeros are paired on the zero side of the contour form.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace Analytic

/-- Reflection across the critical line. -/
def reflectZetaZero (rho : ℂ) : ℂ := 1 - conj rho

private theorem zeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  have hs' : (1 : ℝ) < (conj s).re := by
    rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs', zeta_eq_tsum_one_div_nat_cpow hs]
  have hstar :
      star (∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (conj s)) =
        ∑' n : ℕ, star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := tsum_star
  calc
    conj (∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (conj s)) =
        ∑' n : ℕ, star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := hstar
    _ = ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s := by
      congr 1
      funext n
      have harg : ((n : ℂ)).arg ≠ Real.pi := by
        rw [Complex.natCast_arg]
        exact Ne.symm Real.pi_ne_zero
      have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
        have h := Complex.cpow_conj (n : ℂ) s harg
        rwa [Complex.conj_natCast] at h
      show star ((1 : ℂ) / (n : ℂ) ^ (conj s)) = 1 / (n : ℂ) ^ s
      rw [star_div₀, star_one, hpow]
      simp

/-- Schwarz reflection for the Riemann zeta function away from its pole. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected
  have hzeta : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have hzetaConj :
      AnalyticOnNhd ℂ (fun z => conj (riemannZeta (conj z))) ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hz1 : conj z ≠ 1 := by
      intro h
      have h2 := congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj, map_one] at h2
      exact (by simpa using hz : z ≠ 1) h2
    have hd : DifferentiableAt ℂ riemannZeta (conj z) := differentiableAt_riemannZeta hz1
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hagree :
      (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact zeta_conj_of_one_lt_re hz
  have heq := hzetaConj.eqOn_of_preconnected_of_eventuallyEq hzeta hconn h2mem hagree
  have h3 : conj (riemannZeta (conj s)) = riemannZeta s := heq (by simpa using hs)
  calc
    riemannZeta (conj s) = conj (conj (riemannZeta (conj s))) :=
      (Complex.conj_conj _).symm
    _ = conj (riemannZeta s) := by rw [h3]

private theorem tendsto_conj_nhds (w : ℂ) :
    Filter.Tendsto (fun z => conj z) (nhds (conj w)) (nhds w) := by
  have h := Complex.continuous_conj.tendsto (conj w)
  rwa [Complex.conj_conj] at h

private theorem analyticAt_conj_conj {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(tendsto_conj_nhds w).eventually hf] with z hz
  have h2 := hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

/-- Analytic order is invariant under simultaneous conjugation of argument and
value. -/
theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (w : ℂ) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj w) = analyticOrderAt f w := by
  by_cases hf : AnalyticAt ℂ f w
  · by_cases htop : analyticOrderAt f w = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [(tendsto_conj_nhds w).eventually
        (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g, hg, hgne, hfg⟩ := hn
      rw [(analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simpa using hgne, ?_⟩
      filter_upwards [(tendsto_conj_nhds w).eventually hfg] with z hz
      have heq : conj (f (conj z)) = conj ((conj z - w) ^ n * g (conj z)) := by
        rw [hz]
        rfl
      rw [heq]
      simp only [map_mul, map_pow, map_sub, Complex.conj_conj]
      rfl
  · have hf' : ¬ AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
      intro hcon
      apply hf
      have h2 := analyticAt_conj_conj hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u => by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf']

/-- Zeta's analytic order is conjugation-symmetric away from the pole. -/
theorem analyticOrderAt_zeta_conj {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta (conj w) = analyticOrderAt riemannZeta w := by
  have hne : conj w ≠ 1 := by
    intro h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj, map_one] at h2
    exact hw h2
  have hcong :
      (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (conj w)] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (by simpa using hne : conj w ∈ ({(1 : ℂ)}ᶜ))] with z hz
    rw [riemannZeta_conj (by simpa using hz), Complex.conj_conj]
  calc
    analyticOrderAt riemannZeta (conj w) =
        analyticOrderAt (fun z => conj (riemannZeta (conj z))) (conj w) :=
      (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt riemannZeta w := analyticOrderAt_conj_conj _ _

/-- Analytic order is preserved by `s ↦ 1-s` in the open critical strip. -/
theorem analyticOrderAt_zeta_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev :
      (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[nhds w]
        (chiOneSub * riemannZeta) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with z hz
    exact riemannZeta_one_sub_eq_chiOneSub_mul_of_strip hz.1 hz.2
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have hderiv : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]
      simp
    rw [hderiv]
    simp
  have hpref := analyticAt_chiOneSub h0 h1
  have hprefOrder : analyticOrderAt chiOneSub w = 0 :=
    hpref.analyticOrderAt_eq_zero.mpr (chiOneSub_ne_zero h0 h1)
  calc
    analyticOrderAt riemannZeta (1 - w) =
        analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
      rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (chiOneSub * riemannZeta) w :=
      analyticOrderAt_congr hev
    _ = analyticOrderAt chiOneSub w + analyticOrderAt riemannZeta w := by
      have hzetaAn : AnalyticAt ℂ riemannZeta w := analyticAt_riemannZeta (by
        intro hw1
        rw [hw1] at h1
        simp at h1)
      exact analyticOrderAt_mul hpref hzetaAn
    _ = analyticOrderAt riemannZeta w := by rw [hprefOrder, zero_add]

/-- Reflection across the critical line preserves nontrivial zeta zeros. -/
theorem reflectZetaZero_mem {rho : ℂ} (hrho : IsNontrivialZetaZero rho) :
    IsNontrivialZetaZero (reflectZetaZero rho) := by
  rcases hrho with ⟨hzero, h0, h1⟩
  have hrhoNe : ∀ n : ℕ, rho ≠ -n := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have hrhoNe1 : rho ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have honeSubNe : (1 : ℂ) - rho ≠ 1 := by
    intro h
    have hrho0 : rho = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [hrho0] at h0
    simp at h0
  have hreflect : reflectZetaZero rho = conj (1 - rho) := by
    unfold reflectZetaZero
    rw [map_sub, map_one]
  constructor
  · rw [hreflect, riemannZeta_conj honeSubNe,
      riemannZeta_one_sub hrhoNe hrhoNe1, hzero]
    simp
  constructor
  · unfold reflectZetaZero
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · unfold reflectZetaZero
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-- Reflection across the critical line preserves zeta-zero multiplicity. -/
theorem zetaZeroMultiplicity_reflect {rho : ℂ} (hrho : IsNontrivialZetaZero rho) :
    zetaZeroMultiplicity (reflectZetaZero rho) = zetaZeroMultiplicity rho := by
  rcases hrho with ⟨_, h0, h1⟩
  have honeSubNe : (1 : ℂ) - rho ≠ 1 := by
    intro h
    have hrho0 : rho = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [hrho0] at h0
    simp at h0
  have hreflect : reflectZetaZero rho = conj (1 - rho) := by
    unfold reflectZetaZero
    rw [map_sub, map_one]
  unfold zetaZeroMultiplicity
  rw [hreflect, analyticOrderAt_zeta_conj honeSubNe,
    analyticOrderAt_zeta_one_sub h0 h1]

end Analytic
end ZetaZero
