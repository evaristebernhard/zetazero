/-
Portions of the proof architecture in this file are adapted from
`zeta-23-lean/Zeta23/Statement/Seam.lean`, copyright (c) 2026 Anthropic, PBC,
released under the Apache 2.0 license.
-/

import ZetaZero.Analytic.ZeroCounting
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Finiteness and positive multiplicity of zeta zeros

These are structural facts about Mathlib's `riemannZeta`, not asymptotic inputs:

* at a nontrivial zero the analytic order is finite and at least one;
* nontrivial zeros are locally finite, hence every bounded ordinate window is
  finite.

They turn the counting definitions in `ZeroCounting` into genuinely finite
objects and are the foundation for good-height selection.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZetaZero
namespace Analytic

/-- Zeta is analytic on the complement of its pole at `1`. -/
theorem riemannZeta_analyticOnNhd_compl_one :
    AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- The punctured plane `ℂ \ {1}` is connected. -/
theorem isConnected_compl_one : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank
    (by simp [Complex.rank_real_complex]) 1

/-- Zeta is not locally identically zero at any point away from its pole. -/
theorem analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine riemannZeta_analyticOnNhd_compl_one.analyticOrderAt_ne_top_of_isPreconnected
    isConnected_compl_one.isPreconnected h2 hs ?_
  rw [(riemannZeta_analyticOnNhd_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

/-- A nontrivial zeta zero is not the pole at `1`. -/
theorem nontrivialZetaZero_ne_one {rho : ℂ} (hrho : IsNontrivialZetaZero rho) :
    rho ≠ 1 := by
  intro h
  have hlt := hrho.2.2
  rw [h] at hlt
  norm_num at hlt

/-- Every nontrivial zeta zero has positive analytic multiplicity. -/
theorem one_le_zetaZeroMultiplicity {rho : ℂ} (hrho : IsNontrivialZetaZero rho) :
    1 ≤ zetaZeroMultiplicity rho := by
  have hrho1 : rho ≠ 1 := nontrivialZetaZero_ne_one hrho
  have han : AnalyticAt ℂ riemannZeta rho :=
    riemannZeta_analyticOnNhd_compl_one rho (by simpa using hrho1)
  have hne0 : analyticOrderAt riemannZeta rho ≠ 0 :=
    han.analyticOrderAt_ne_zero.mpr hrho.1
  have hnetop := analyticOrderAt_riemannZeta_ne_top hrho1
  unfold zetaZeroMultiplicity
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

/-- Away from the pole, the zero set of zeta is locally finite. -/
theorem riemannZeta_zeros_locallyFinite (z : ℂ) :
    ∃ t ∈ 𝓝 z, (t ∩ {rho : ℂ | rho ≠ 1 ∧ riemannZeta rho = 0}).Finite := by
  by_cases hz : z = 1
  · subst hz
    have hres := riemannZeta_residue_one
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
      have hne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
        hres.eventually_ne one_ne_zero
      exact hne.mono fun s hs h => hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s ∈ ({1}ᶜ : Set ℂ) → riemannZeta s ≠ 0}, hev, ?_⟩
    refine Set.finite_empty.subset ?_
    rintro s ⟨hs, hs1, hs0⟩
    exact hs hs1 hs0
  · have hcod :=
      riemannZeta_analyticOnNhd_compl_one.eqOn_zero_or_eventually_ne_zero_of_preconnected
        isConnected_compl_one.isPreconnected
    rcases hcod with hzero | hcod
    · exfalso
      have h2zero : riemannZeta 2 = 0 :=
        hzero (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) h2zero
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z hz
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs1, hs0⟩
      exact ⟨hst, hs1, by simpa using hs0⟩

/-- Every bounded ordinate window of nontrivial zeta zeros is finite. -/
theorem zetaZerosIn_finite (T₁ T₂ : ℝ) : (zetaZerosIn T₁ T₂).Finite := by
  set K : Set ℂ := (Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU :
      (⋃ z ∈ I, (t z ∩ {rho : ℂ | rho ≠ 1 ∧ riemannZeta rho = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro rho ⟨hrho, hT₁, hT₂⟩
  have hrhoK : rho ∈ K := by
    refine ⟨⟨hrho.2.1.le, hrho.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, hrhoz⟩ := mem_iUnion₂.mp (hcover hrhoK)
  have hrho1 : rho ≠ 1 := nontrivialZetaZero_ne_one hrho
  exact mem_iUnion₂.mpr ⟨z, hzI, hrhoz, hrho1, hrho.1⟩

/-- The critical-line subwindow is finite as well. -/
theorem criticalLineZetaZerosIn_finite (T₁ T₂ : ℝ) :
    (criticalLineZetaZerosIn T₁ T₂).Finite :=
  (zetaZerosIn_finite T₁ T₂).inter_of_left _

end Analytic
end ZetaZero
