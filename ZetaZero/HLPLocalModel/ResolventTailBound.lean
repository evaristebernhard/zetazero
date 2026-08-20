import ZetaZero.HLPLocalModel.FiniteResolventExpansion

/-!
# Quantitative bound for the exact finite resolvent remainder

`FiniteResolventExpansion` isolates the exact remainder

`x^(K+1) * (1-x)⁻¹`.

On the safe side where `‖x‖ ≤ ρ < 1`, this file gives the standard geometric
bound with the denominator kept explicit.  No infinite-series expansion is used.
-/

open Complex

noncomputable section

namespace ZetaZero
namespace HLPLocalModel

/-- Norm bound for the resolvent denominator on a strict norm ball. -/
theorem norm_inv_one_sub_le
    {x : ℂ} {ρ : ℝ} (hρ1 : ρ < 1) (hx : ‖x‖ ≤ ρ) :
    ‖(1 - x)⁻¹‖ ≤ (1 - ρ)⁻¹ := by
  have hgap : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hlower : 1 - ρ ≤ ‖(1 : ℂ) - x‖ := by
    calc
      1 - ρ ≤ 1 - ‖x‖ := sub_le_sub_left hx 1
      _ = ‖(1 : ℂ)‖ - ‖x‖ := by norm_num
      _ ≤ ‖(1 : ℂ) - x‖ := norm_sub_norm_le _ _
  have hden : 0 < ‖(1 : ℂ) - x‖ := hgap.trans_le hlower
  rw [norm_inv]
  exact (inv_le_inv₀ hden hgap).2 hlower

/-- The exact geometric remainder is bounded by `ρ^(K+1)/(1-ρ)`. -/
theorem norm_resolvent_tail_le
    {x : ℂ} {ρ : ℝ} (K : ℕ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hx : ‖x‖ ≤ ρ) :
    ‖x ^ (K + 1) * (1 - x)⁻¹‖ ≤ ρ ^ (K + 1) / (1 - ρ) := by
  have hpow : ‖x‖ ^ (K + 1) ≤ ρ ^ (K + 1) := by
    exact pow_le_pow_left₀ (norm_nonneg x) hx (K + 1)
  have hinv := norm_inv_one_sub_le hρ1 hx
  rw [norm_mul, norm_pow, div_eq_mul_inv]
  exact mul_le_mul hpow hinv (norm_nonneg _) (pow_nonneg hρ0 _)

/-- Quantitative bound for the exact remainder in `Q/(F-P)` after truncating the
HLP hierarchy at level `K`. -/
theorem norm_quotient_hlp_tail_le
    {F P Q : ℂ} {ρ : ℝ} (K : ℕ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hratio : ‖P / F‖ ≤ ρ) :
    ‖(Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹‖ ≤
      ‖Q / F‖ * (ρ ^ (K + 1) / (1 - ρ)) := by
  have htail := norm_resolvent_tail_le K hρ0 hρ1 hratio
  calc
    ‖(Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹‖ =
        ‖Q / F‖ * ‖(P / F) ^ (K + 1) * (1 - P / F)⁻¹‖ := by
      simp only [norm_mul]
      ring
    _ ≤ ‖Q / F‖ * (ρ ^ (K + 1) / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)

/-- The exact quotient differs from its finite HLP hierarchy by at most the
geometric resolvent remainder.  This is the quantitative companion to the exact
finite expansion, with no infinite-series identity involved. -/
theorem norm_quotient_sub_hlp_partial_le
    {F P Q : ℂ} {ρ : ℝ} (K : ℕ)
    (hF : F ≠ 0) (hden : F - P ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hratio : ‖P / F‖ ≤ ρ) :
    ‖Q / (F - P) - (Q / F) * resolventPartialSum (P / F) K‖ ≤
      ‖Q / F‖ * (ρ ^ (K + 1) / (1 - ρ)) := by
  rw [quotient_eq_hlp_partial_add_tail K hF hden]
  have hEq :
      (Q / F) * resolventPartialSum (P / F) K +
          (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ -
        (Q / F) * resolventPartialSum (P / F) K =
      (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ := by
    ring
  rw [hEq]
  exact norm_quotient_hlp_tail_le K hρ0 hρ1 hratio

/-- The completed exact source has the same finite-HLP truncation error. -/
theorem norm_completedExactSource_sub_hlp_partial_le
    {F P Q : ℂ} {ρ : ℝ} (K : ℕ)
    (hF : F ≠ 0) (hden : F - P ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hratio : ‖P / F‖ ≤ ρ) :
    ‖RightEdgeArithmeticSource.completedExactSource F P Q -
        (F - P + (Q / F) * resolventPartialSum (P / F) K)‖ ≤
      ‖Q / F‖ * (ρ ^ (K + 1) / (1 - ρ)) := by
  rw [completedExactSource_eq_hlp_partial_add_tail K hF hden]
  have hEq :
      F - P + (Q / F) * resolventPartialSum (P / F) K +
          (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ -
        (F - P + (Q / F) * resolventPartialSum (P / F) K) =
      (Q / F) * (P / F) ^ (K + 1) * (1 - P / F)⁻¹ := by
    ring
  rw [hEq]
  exact norm_quotient_hlp_tail_le K hρ0 hρ1 hratio

end HLPLocalModel
end ZetaZero
