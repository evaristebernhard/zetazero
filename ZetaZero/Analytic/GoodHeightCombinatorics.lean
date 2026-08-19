/-
Portions of the proof architecture in this file are adapted from
`zeta-23-lean/Zeta23/WeilEF/GoodHeights.lean`, copyright (c) 2026 Anthropic,
PBC, released under the Apache 2.0 license.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite-set avoidance for good horizontal heights

The analytic good-height argument ultimately needs only a simple pigeonhole
fact: among `|S|+1` equally spaced midpoints of a unit interval, one stays a
controlled distance from every point of a finite forbidden set `S`.

This lemma is independent of zeta and is kept in the shared analytic layer so
that the later Riemann--von Mangoldt/local-partial-fraction machinery only has
to provide a finite forbidden set and a cardinality bound.
-/

open Finset

namespace ZetaZero
namespace Analytic

/-- For a finite set `S` of real ordinates and any real `a`, there is a point
`R ∈ [a,a+1]` at distance at least `1 / (2(|S|+1))` from every element of `S`. -/
theorem exists_far_point (S : Finset ℝ) (a : ℝ) :
    ∃ R : ℝ, a ≤ R ∧ R ≤ a + 1 ∧
      ∀ y ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |R - y| := by
  classical
  set n : ℕ := S.card with hn
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδn : 2 * ((n : ℝ) + 1) * δ = 1 := by rw [hδ]; field_simp
  set cand : ℕ → ℝ := fun k => a + (2 * (k : ℝ) + 1) * δ with hcand
  by_contra hcon
  push Not at hcon
  have hbad : ∀ k ∈ Finset.range (n + 1), ∃ y ∈ S, |cand k - y| < δ := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : a ≤ cand k := by simp only [hcand]; nlinarith
    have h2 : cand k ≤ a + 1 := by
      simp only [hcand]
      have hle : (2 * (k : ℝ) + 1) * δ ≤ (2 * (n : ℝ) + 1) * δ := by gcongr
      nlinarith
    obtain ⟨y, hy, hlt⟩ := hcon (cand k) h1 h2
    exact ⟨y, hy, hlt⟩
  choose! f hf using hbad
  have hmaps : Set.MapsTo f (Finset.range (n + 1)) S := fun k hk => (hf k hk).1
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hn]) hmaps
  have h1 := (hf x hx).2
  have h2 := (hf y hy).2
  rw [hfxy] at h1
  have hdist : |cand x - cand y| = 2 * |(x : ℝ) - y| * δ := by
    simp only [hcand]
    rw [show a + (2 * (x : ℝ) + 1) * δ - (a + (2 * (y : ℝ) + 1) * δ) =
        (2 * δ) * ((x : ℝ) - y) by ring,
      abs_mul, abs_of_pos (by positivity)]
    ring
  have hxy1 : (1 : ℝ) ≤ |(x : ℝ) - y| := by
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have hcast : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hcast : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have htri : |cand x - cand y| < 2 * δ := by
    calc
      |cand x - cand y| = |(cand x - f y) - (cand y - f y)| := by ring_nf
      _ ≤ |cand x - f y| + |cand y - f y| := abs_sub _ _
      _ < δ + δ := add_lt_add h1 h2
      _ = 2 * δ := by ring
  rw [hdist] at htri
  nlinarith

end Analytic
end ZetaZero
