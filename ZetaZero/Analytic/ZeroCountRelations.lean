/-
Portions of the elementary counting architecture in this file are adapted from
`zeta-23-lean/Zeta23/Defs/Counting.lean`, copyright (c) 2026 Anthropic, PBC,
released under the Apache 2.0 license.
-/

import ZetaZero.Analytic.ZeroFiniteness

/-!
# Elementary relations between zeta zero counts

This module isolates the finite combinatorics relating distinct zero counts,
critical-line counts, simple critical-line counts, and counts with
multiplicity.  No Riemann--von Mangoldt asymptotic input is used here.
-/

open Set

noncomputable section

namespace ZetaZero
namespace Analytic

/-- A finite subset of a zeta-zero window has cardinality at most its total
multiplicity. -/
lemma ncard_le_finsum_zetaZeroMultiplicity
    {T₁ T₂ : ℝ} {s : Set ℂ} (hs : s ⊆ zetaZerosIn T₁ T₂) :
    s.ncard ≤ ∑ᶠ ρ ∈ s, zetaZeroMultiplicity ρ := by
  have hfin : s.Finite := (zetaZerosIn_finite T₁ T₂).subset hs
  rw [Set.ncard_eq_toFinset_card s hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  exact one_le_zetaZeroMultiplicity (hs (hfin.mem_toFinset.mp hρ)).1

/-- Total multiplicity is monotone under inclusion of finite subsets of a
zeta-zero window. -/
lemma finsum_zetaZeroMultiplicity_mono
    {T₁ T₂ : ℝ} {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ zetaZerosIn T₁ T₂) :
    ∑ᶠ ρ ∈ s, zetaZeroMultiplicity ρ ≤
      ∑ᶠ ρ ∈ t, zetaZeroMultiplicity ρ := by
  have htf : t.Finite := (zetaZerosIn_finite T₁ T₂).subset ht
  have hsf : s.Finite := htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf,
    finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst

/-- Cardinality is monotone for subsets of a finite zeta-zero window. -/
lemma ncard_mono_in_zetaWindow
    {T₁ T₂ : ℝ} {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ zetaZerosIn T₁ T₂) :
    s.ncard ≤ t.ncard :=
  Set.ncard_le_ncard hst ((zetaZerosIn_finite T₁ T₂).subset ht)

/-- The elementary zero-count chain used by the zero-side argument:

`N₀,simple ≤ N₀,distinct ≤ N₀ ≤ N`, and independently
`N₀,distinct ≤ N_distinct ≤ N`.
-/
theorem zero_count_chain (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ ≤ N0dist T₁ T₂ ∧
      N0dist T₁ T₂ ≤ N0count T₁ T₂ ∧
      N0count T₁ T₂ ≤ Ncount T₁ T₂ ∧
      N0dist T₁ T₂ ≤ Ndist T₁ T₂ ∧
      Ndist T₁ T₂ ≤ Ncount T₁ T₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ncard_mono_in_zetaWindow
      (T₁ := T₁) (T₂ := T₂)
      inter_subset_left inter_subset_left
  · exact ncard_le_finsum_zetaZeroMultiplicity
      (T₁ := T₁) (T₂ := T₂) inter_subset_left
  · exact finsum_zetaZeroMultiplicity_mono
      (T₁ := T₁) (T₂ := T₂) inter_subset_left subset_rfl
  · exact ncard_mono_in_zetaWindow
      (T₁ := T₁) (T₂ := T₂) inter_subset_left subset_rfl
  · exact ncard_le_finsum_zetaZeroMultiplicity
      (T₁ := T₁) (T₂ := T₂) subset_rfl

lemma N0simple_le_N0count (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ ≤ N0count T₁ T₂ :=
  (zero_count_chain T₁ T₂).1.trans (zero_count_chain T₁ T₂).2.1

lemma N0count_le_Ncount (T₁ T₂ : ℝ) :
    N0count T₁ T₂ ≤ Ncount T₁ T₂ :=
  (zero_count_chain T₁ T₂).2.2.1

lemma Ndist_le_Ncount (T₁ T₂ : ℝ) :
    Ndist T₁ T₂ ≤ Ncount T₁ T₂ :=
  (zero_count_chain T₁ T₂).2.2.2.2

lemma N0dist_le_Ndist (T₁ T₂ : ℝ) :
    N0dist T₁ T₂ ≤ Ndist T₁ T₂ :=
  (zero_count_chain T₁ T₂).2.2.2.1

/-- Dyadic specialization of `N₀ ≤ N`. -/
lemma dyadicN0_le_dyadicN (T : ℝ) : dyadicN0 T ≤ dyadicN T := by
  exact N0count_le_Ncount T (2 * T)

/-- Simple critical-line zeros in a dyadic window are bounded by the dyadic
critical-line count with multiplicity. -/
lemma N0simple_dyadic_le_dyadicN0 (T : ℝ) :
    N0simple T (2 * T) ≤ dyadicN0 T := by
  exact N0simple_le_N0count T (2 * T)

/-- Distinct zeros in a dyadic window are bounded by the total dyadic count
with multiplicity. -/
lemma Ndist_dyadic_le_dyadicN (T : ℝ) :
    Ndist T (2 * T) ≤ dyadicN T := by
  exact Ndist_le_Ncount T (2 * T)

end Analytic
end ZetaZero
