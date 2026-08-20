import ZetaZero.RightEdgeArithmeticSource.QuadraticOscillatoryTail
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Cauchy control for the quadratic stationary model

`QuadraticOscillatoryTail` proves the finite positive-tail estimate

`‖∫ y in R..S, exp (i y^2 / 2)‖ ≤ 2 / R`.

This file packages that bound in the form needed for constructing the positive
Fresnel limit: truncated integrals from `0` form a quantitative Cauchy family.
No improper integral is introduced yet.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The quadratic oscillation is interval integrable on every finite interval. -/
theorem intervalIntegrable_quadraticOscillation (a b : ℝ) :
    IntervalIntegrable quadraticOscillation volume a b := by
  apply Continuous.intervalIntegrable
  unfold quadraticOscillation
  fun_prop

/-- Moving the positive truncation point from `R` to `S` changes the quadratic
oscillatory integral by at most `2/R`. -/
theorem norm_positiveTruncation_sub_le_two_div
    {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    ‖(∫ y in 0..S, quadraticOscillation y) -
        ∫ y in 0..R, quadraticOscillation y‖ ≤ 2 / R := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_quadraticOscillation 0 R)
    (intervalIntegrable_quadraticOscillation R S)
  calc
    ‖(∫ y in 0..S, quadraticOscillation y) -
        ∫ y in 0..R, quadraticOscillation y‖ =
      ‖∫ y in R..S, quadraticOscillation y‖ := by
        rw [← hadd]
        congr 1
        abel
    _ ≤ 2 / R := norm_intervalIntegral_quadraticOscillation_le_two_div hR hRS

/-- Two sufficiently far positive truncations are uniformly close.  This is the
quantitative Cauchy estimate used to construct the positive Fresnel limit. -/
theorem norm_positiveTruncations_sub_le_four_div
    {A R S : ℝ} (hA : 0 < A) (hAR : A ≤ R) (hAS : A ≤ S) :
    ‖(∫ y in 0..R, quadraticOscillation y) -
        ∫ y in 0..S, quadraticOscillation y‖ ≤ 4 / A := by
  have hRA := norm_positiveTruncation_sub_le_two_div hA hAR
  have hSA := norm_positiveTruncation_sub_le_two_div hA hAS
  have htri :
      ‖((∫ y in 0..R, quadraticOscillation y) -
          ∫ y in 0..A, quadraticOscillation y) -
        ((∫ y in 0..S, quadraticOscillation y) -
          ∫ y in 0..A, quadraticOscillation y)‖ ≤
        ‖(∫ y in 0..R, quadraticOscillation y) -
            ∫ y in 0..A, quadraticOscillation y‖ +
          ‖(∫ y in 0..S, quadraticOscillation y) -
            ∫ y in 0..A, quadraticOscillation y‖ :=
    norm_sub_le _ _
  have hsum :
      ‖(∫ y in 0..R, quadraticOscillation y) -
          ∫ y in 0..A, quadraticOscillation y‖ +
        ‖(∫ y in 0..S, quadraticOscillation y) -
          ∫ y in 0..A, quadraticOscillation y‖ ≤ 4 / A := by
    calc
      _ ≤ 2 / A + 2 / A := add_le_add hRA hSA
      _ = 4 / A := by ring
  calc
    ‖(∫ y in 0..R, quadraticOscillation y) -
        ∫ y in 0..S, quadraticOscillation y‖ =
      ‖((∫ y in 0..R, quadraticOscillation y) -
          ∫ y in 0..A, quadraticOscillation y) -
        ((∫ y in 0..S, quadraticOscillation y) -
          ∫ y in 0..A, quadraticOscillation y)‖ := by
            congr 1
            abel
    _ ≤ ‖(∫ y in 0..R, quadraticOscillation y) -
            ∫ y in 0..A, quadraticOscillation y‖ +
          ‖(∫ y in 0..S, quadraticOscillation y) -
            ∫ y in 0..A, quadraticOscillation y‖ := htri
    _ ≤ 4 / A := hsum

/-- Positive integer truncations of the quadratic oscillatory integral.  The
shift by one keeps every truncation radius strictly positive. -/
def positiveQuadraticTruncation (n : ℕ) : ℂ :=
  ∫ y in 0..(((n + 1 : ℕ) : ℝ)), quadraticOscillation y

/-- The positive integer truncations form a Cauchy sequence. -/
theorem cauchySeq_positiveQuadraticTruncation :
    CauchySeq positiveQuadraticTruncation := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hA : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hAm : (((N + 1 : ℕ) : ℝ)) ≤ (((m + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ hm
  have hAn : (((N + 1 : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hbound := norm_positiveTruncations_sub_le_four_div hA hAm hAn
  have hfourN : (4 : ℝ) < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hNA : (N : ℝ) < (((N + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.lt_succ_self N
  have hfourA : (4 : ℝ) < (((N + 1 : ℕ) : ℝ)) * ε :=
    hfourN.trans (mul_lt_mul_of_pos_right hNA hε)
  have hratio : (4 : ℝ) / (((N + 1 : ℕ) : ℝ)) < ε :=
    (div_lt_iff₀ hA).2 (by simpa [mul_comm] using hfourA)
  calc
    dist (positiveQuadraticTruncation m) (positiveQuadraticTruncation n) =
        ‖(∫ y in 0..(((m + 1 : ℕ) : ℝ)), quadraticOscillation y) -
          ∫ y in 0..(((n + 1 : ℕ) : ℝ)), quadraticOscillation y‖ := by
            simp [positiveQuadraticTruncation, dist_eq_norm]
    _ ≤ 4 / (((N + 1 : ℕ) : ℝ)) := hbound
    _ < ε := hratio

/-- Existence of the positive Fresnel limit follows from completeness of
`ℂ`, independently of any evaluation of that limit. -/
theorem exists_positiveFresnelLimit :
    ∃ L : ℂ, Tendsto positiveQuadraticTruncation atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete cauchySeq_positiveQuadraticTruncation

/-- The positive Fresnel limit, defined from the Cauchy sequence of finite
quadratic oscillatory integrals. -/
def positiveFresnelLimit : ℂ :=
  Classical.choose exists_positiveFresnelLimit

/-- The positive integer truncations converge to `positiveFresnelLimit`. -/
theorem tendsto_positiveQuadraticTruncation :
    Tendsto positiveQuadraticTruncation atTop (𝓝 positiveFresnelLimit) :=
  Classical.choose_spec exists_positiveFresnelLimit

/-- The same Fresnel limit is obtained along arbitrary real truncation radii,
not only the integer subsequence used to construct it. -/
theorem tendsto_positiveQuadraticIntegral :
    Tendsto (fun R : ℝ => ∫ y in 0..R, quadraticOscillation y)
      atTop (𝓝 positiveFresnelLimit) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ :=
    Metric.tendsto_atTop.mp tendsto_positiveQuadraticTruncation (ε / 2) hhalf
  obtain ⟨M, hM⟩ := exists_nat_gt (4 / ε)
  let N := max N₀ M
  refine ⟨(((N + 1 : ℕ) : ℝ)), ?_⟩
  intro R hR
  have hN0N : N₀ ≤ N := le_max_left _ _
  have hMN : M ≤ N := le_max_right _ _
  have hseq : dist (positiveQuadraticTruncation N) positiveFresnelLimit < ε / 2 :=
    hN₀ N hN0N
  have hA : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have htail := norm_positiveTruncation_sub_le_two_div hA hR
  have hfourN : (4 : ℝ) / ε < (N : ℝ) :=
    hM.trans_le (by exact_mod_cast hMN)
  have hfourA : (4 : ℝ) / ε < (((N + 1 : ℕ) : ℝ)) :=
    hfourN.trans (by exact_mod_cast Nat.lt_succ_self N)
  have htwoA : (2 : ℝ) / (((N + 1 : ℕ) : ℝ)) < ε / 2 := by
    have hfour : (4 : ℝ) < ε * (((N + 1 : ℕ) : ℝ)) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hfourA
    have hposA : 0 < (((N + 1 : ℕ) : ℝ)) := hA
    apply (div_lt_iff₀ hposA).2
    nlinarith
  have htail' :
      ‖(∫ y in 0..R, quadraticOscillation y) - positiveQuadraticTruncation N‖ < ε / 2 :=
    htail.trans_lt htwoA
  calc
    dist (∫ y in 0..R, quadraticOscillation y) positiveFresnelLimit =
        ‖(∫ y in 0..R, quadraticOscillation y) - positiveFresnelLimit‖ :=
      dist_eq_norm _ _
    _ = ‖((∫ y in 0..R, quadraticOscillation y) - positiveQuadraticTruncation N) +
          (positiveQuadraticTruncation N - positiveFresnelLimit)‖ := by
            congr 1
            abel
    _ ≤ ‖(∫ y in 0..R, quadraticOscillation y) - positiveQuadraticTruncation N‖ +
          ‖positiveQuadraticTruncation N - positiveFresnelLimit‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
      gcongr
      simpa [dist_eq_norm] using hseq
    _ = ε := by ring

end RightEdgeArithmeticSource
end ZetaZero
