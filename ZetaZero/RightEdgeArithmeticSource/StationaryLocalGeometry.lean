import ZetaZero.RightEdgeArithmeticSource.StationaryQuadraticControl
import Mathlib.Tactic

/-!
# Uniform local geometry near the one-chi saddle

The normalized one-chi phase has universal saddle at `v = 1`.  This file
records the derivative bounds on the fixed neighborhood `[1/2, 3/2]` that are
needed by a later quantitative stationary-phase/Taylor argument.  In
particular, the Hessian is uniformly elliptic and the third derivative is
uniformly bounded there.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- On the standard saddle neighborhood, the normalized Hessian is bounded
below by `2/3`. -/
theorem secondDeriv_normalizedOneChiPhase_lower
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (hvhi : v ≤ 3 / 2) :
    (2 / 3 : ℝ) ≤ deriv (deriv normalizedOneChiPhase) v := by
  have hvpos : 0 < v := by linarith
  rw [secondDeriv_normalizedOneChiPhase hvpos.ne']
  rw [le_div_iff₀ hvpos]
  nlinarith

/-- On the standard saddle neighborhood, the normalized Hessian is bounded
above by `2`. -/
theorem secondDeriv_normalizedOneChiPhase_upper
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (_hvhi : v ≤ 3 / 2) :
    deriv (deriv normalizedOneChiPhase) v ≤ 2 := by
  have hvpos : 0 < v := by linarith
  rw [secondDeriv_normalizedOneChiPhase hvpos.ne']
  rw [div_le_iff₀ hvpos]
  nlinarith

/-- The third derivative of the normalized phase has absolute value at most
`4` throughout the standard saddle neighborhood. -/
theorem abs_thirdDeriv_normalizedOneChiPhase_le_four
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (_hvhi : v ≤ 3 / 2) :
    |deriv (deriv (deriv normalizedOneChiPhase)) v| ≤ 4 := by
  have hvpos : 0 < v := by linarith
  rw [thirdDeriv_normalizedOneChiPhase hvpos.ne']
  rw [abs_neg, abs_inv, abs_pow, abs_of_pos hvpos]
  have hprod : 0 ≤ (v - (1 / 2 : ℝ)) * (v + 1 / 2) := by positivity
  have hsq : (1 / 4 : ℝ) ≤ v ^ 2 := by
    nlinarith
  have hsqpos : 0 < v ^ 2 := sq_pos_of_pos hvpos
  have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
  have hinv : (v ^ 2)⁻¹ ≤ ((1 / 4 : ℝ))⁻¹ :=
    (inv_le_inv₀ hsqpos hquarter).2 hsq
  norm_num at hinv ⊢
  exact hinv

/-- The Hessian bounds packaged as a single interval statement. -/
theorem secondDeriv_normalizedOneChiPhase_mem_Icc
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (hvhi : v ≤ 3 / 2) :
    deriv (deriv normalizedOneChiPhase) v ∈ Set.Icc (2 / 3 : ℝ) 2 := by
  exact ⟨secondDeriv_normalizedOneChiPhase_lower hvlo hvhi,
    secondDeriv_normalizedOneChiPhase_upper hvlo hvhi⟩

/-- To the right of the saddle, `Psi'(v)=log v` is quantitatively comparable
to the displacement `v-1`. -/
theorem deriv_normalizedOneChiPhase_right_linear_bounds
    {v : ℝ} (hvone : 1 ≤ v) (hvhi : v ≤ 3 / 2) :
    (2 / 3 : ℝ) * (v - 1) ≤ deriv normalizedOneChiPhase v ∧
      deriv normalizedOneChiPhase v ≤ v - 1 := by
  have hvpos : 0 < v := lt_of_lt_of_le zero_lt_one hvone
  rw [deriv_normalizedOneChiPhase hvpos.ne']
  constructor
  · have hlog := Real.one_sub_inv_le_log_of_pos hvpos
    have hid : 1 - v⁻¹ = (v - 1) / v := by
      field_simp [hvpos.ne']
    rw [hid] at hlog
    have hfrac : (2 / 3 : ℝ) * (v - 1) ≤ (v - 1) / v := by
      rw [le_div_iff₀ hvpos]
      nlinarith
    exact hfrac.trans hlog
  · exact Real.log_le_sub_one_of_pos hvpos

/-- To the left of the saddle, the absolute derivative is quantitatively
comparable to `1-v`. -/
theorem abs_deriv_normalizedOneChiPhase_left_linear_bounds
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (hvone : v ≤ 1) :
    1 - v ≤ |deriv normalizedOneChiPhase v| ∧
      |deriv normalizedOneChiPhase v| ≤ 2 * (1 - v) := by
  have hvpos : 0 < v := by linarith
  rw [deriv_normalizedOneChiPhase hvpos.ne']
  have hlognonpos : Real.log v ≤ 0 := Real.log_nonpos hvpos.le hvone
  rw [abs_of_nonpos hlognonpos]
  constructor
  · have hlogUpper := Real.log_le_sub_one_of_pos hvpos
    linarith
  · have hlogLower := Real.one_sub_inv_le_log_of_pos hvpos
    have hid : v⁻¹ - 1 = (1 - v) / v := by
      field_simp [hvpos.ne']
    have hfrac : (1 - v) / v ≤ 2 * (1 - v) := by
      rw [div_le_iff₀ hvpos]
      nlinarith
    have hinv : -Real.log v ≤ v⁻¹ - 1 := by linarith
    rw [hid] at hinv
    exact hinv.trans hfrac

/-- Uniform linearization of the normalized phase derivative around its unique
saddle on the standard neighborhood. -/
theorem abs_deriv_normalizedOneChiPhase_comparable
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (hvhi : v ≤ 3 / 2) :
    (2 / 3 : ℝ) * |v - 1| ≤ |deriv normalizedOneChiPhase v| ∧
      |deriv normalizedOneChiPhase v| ≤ 2 * |v - 1| := by
  by_cases hvone : v ≤ 1
  · have hleft := abs_deriv_normalizedOneChiPhase_left_linear_bounds hvlo hvone
    have habs : |v - 1| = 1 - v := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [habs]
    constructor
    · nlinarith [hleft.1]
    · exact hleft.2
  · have hvone' : 1 ≤ v := le_of_not_ge hvone
    have hright := deriv_normalizedOneChiPhase_right_linear_bounds hvone' hvhi
    have hdisp : |v - 1| = v - 1 := abs_of_nonneg (sub_nonneg.mpr hvone')
    have hderivnonneg : 0 ≤ deriv normalizedOneChiPhase v := by
      nlinarith [hright.1]
    rw [hdisp, abs_of_nonneg hderivnonneg]
    constructor
    · exact hright.1
    · nlinarith [hright.2]

/-- Cubic Taylor remainder on the standard saddle neighborhood. -/
theorem normalizedOneChiPhase_quadratic_remainder_abs_le
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (hvhi : v ≤ 3 / 2) :
    |normalizedOneChiPhase v - (-1 + (v - 1) ^ 2 / 2)| ≤
      (2 / 3 : ℝ) * |v - 1| ^ 3 := by
  have hvpos : 0 < v := by linarith
  by_cases hvone : v = 1
  · subst v
    norm_num [normalizedOneChiPhase]
  · obtain ⟨xi, hxi, heq⟩ :=
      exists_normalizedOneChiPhase_quadratic_remainder hvpos hvone
    have hxiu : xi ∈ Set.uIcc 1 v := Set.uIoo_subset_uIcc_self hxi
    rw [Set.mem_uIcc] at hxiu
    have hxilo : (1 / 2 : ℝ) ≤ xi := by
      rcases hxiu with hxiu | hxiu
      · linarith [hxiu.1]
      · linarith [hxiu.1]
    have hxihi : xi ≤ (3 / 2 : ℝ) := by
      rcases hxiu with hxiu | hxiu
      · linarith [hxiu.2]
      · linarith [hxiu.2]
    have hcoef : |-(xi ^ 2)⁻¹| ≤ 4 := by
      have hthird := abs_thirdDeriv_normalizedOneChiPhase_le_four hxilo hxihi
      rw [thirdDeriv_normalizedOneChiPhase (by linarith : xi ≠ 0)] at hthird
      exact hthird
    rw [heq]
    calc
      |-(xi ^ 2)⁻¹ * (v - 1) ^ 3 / 6| =
          |-(xi ^ 2)⁻¹| * |v - 1| ^ 3 / 6 := by
            rw [abs_div, abs_mul, abs_pow]
            norm_num
      _ ≤ 4 * |v - 1| ^ 3 / 6 := by
            gcongr
      _ = (2 / 3 : ℝ) * |v - 1| ^ 3 := by ring

/-- On a quarter-sized saddle window the centered phase is uniformly
quadratic, with explicit constants around the Gaussian coefficient `1/2`. -/
theorem normalizedOneChiPhase_centered_quadratic_bounds
    {v : ℝ} (hv : |v - 1| ≤ (1 / 4 : ℝ)) :
    (1 / 3 : ℝ) * (v - 1) ^ 2 ≤ normalizedOneChiPhase v + 1 ∧
      normalizedOneChiPhase v + 1 ≤ (2 / 3 : ℝ) * (v - 1) ^ 2 := by
  have habs := abs_le.mp hv
  have hvlo : (1 / 2 : ℝ) ≤ v := by linarith [habs.1]
  have hvhi : v ≤ (3 / 2 : ℝ) := by linarith [habs.2]
  have hrem := normalizedOneChiPhase_quadratic_remainder_abs_le hvlo hvhi
  have hcube0 : |v - 1| ^ 3 ≤ (1 / 4 : ℝ) * |v - 1| ^ 2 := by
    have hnonneg : 0 ≤ |v - 1| ^ 2 := sq_nonneg |v - 1|
    have hgap : 0 ≤ (1 / 4 : ℝ) - |v - 1| := sub_nonneg.mpr hv
    nlinarith [mul_nonneg hnonneg hgap]
  have hcube :
      (2 / 3 : ℝ) * |v - 1| ^ 3 ≤ (1 / 6 : ℝ) * (v - 1) ^ 2 := by
    calc
      (2 / 3 : ℝ) * |v - 1| ^ 3 ≤
          (2 / 3 : ℝ) * ((1 / 4 : ℝ) * |v - 1| ^ 2) := by
            gcongr
      _ = (1 / 6 : ℝ) * (v - 1) ^ 2 := by
            rw [sq_abs]
            ring
  have hR :
      |normalizedOneChiPhase v - (-1 + (v - 1) ^ 2 / 2)| ≤
        (1 / 6 : ℝ) * (v - 1) ^ 2 := hrem.trans hcube
  have hRbounds := abs_le.mp hR
  constructor <;> nlinarith [hRbounds.1, hRbounds.2]

/-- Physical quadratic trapping of the one-chi phase around its saddle. -/
theorem oneChiPhase_centered_quadratic_bounds
    {eta t : ℝ} (heta : 0 < eta)
    (ht : |t / stationaryScale eta - 1| ≤ (1 / 4 : ℝ)) :
    (1 / 3 : ℝ) * (t - stationaryScale eta) ^ 2 / stationaryScale eta ≤
        oneChiPhase eta t - oneChiPhase eta (stationaryScale eta) ∧
      oneChiPhase eta t - oneChiPhase eta (stationaryScale eta) ≤
        (2 / 3 : ℝ) * (t - stationaryScale eta) ^ 2 / stationaryScale eta := by
  have hspos := stationaryScale_pos heta
  have hsne := hspos.ne'
  have hnorm := normalizedOneChiPhase_centered_quadratic_bounds ht
  have htdecomp : stationaryScale eta * (t / stationaryScale eta) = t := by
    field_simp [hsne]
  have hrescale :
      oneChiPhase eta t =
        stationaryScale eta * normalizedOneChiPhase (t / stationaryScale eta) - Real.pi / 4 := by
    calc
      oneChiPhase eta t =
          oneChiPhase eta (stationaryScale eta * (t / stationaryScale eta)) := by
            rw [htdecomp]
      _ = stationaryScale eta * normalizedOneChiPhase (t / stationaryScale eta) -
          Real.pi / 4 := oneChiPhase_rescale heta _
  have hphase :
      oneChiPhase eta t - oneChiPhase eta (stationaryScale eta) =
        stationaryScale eta * (normalizedOneChiPhase (t / stationaryScale eta) + 1) := by
    rw [hrescale, oneChiPhase_stationaryScale heta]
    ring
  have hquad :
      stationaryScale eta * (t / stationaryScale eta - 1) ^ 2 =
        (t - stationaryScale eta) ^ 2 / stationaryScale eta := by
    field_simp [hsne]
  have hlow := mul_le_mul_of_nonneg_left hnorm.1 hspos.le
  have hupp := mul_le_mul_of_nonneg_left hnorm.2 hspos.le
  have hlow' :
      (1 / 3 : ℝ) * (t - stationaryScale eta) ^ 2 / stationaryScale eta ≤
        stationaryScale eta * (normalizedOneChiPhase (t / stationaryScale eta) + 1) := by
    calc
      (1 / 3 : ℝ) * (t - stationaryScale eta) ^ 2 / stationaryScale eta =
          (1 / 3 : ℝ) *
            (stationaryScale eta * (t / stationaryScale eta - 1) ^ 2) := by
            rw [hquad]
            ring
      _ = stationaryScale eta *
          ((1 / 3 : ℝ) * (t / stationaryScale eta - 1) ^ 2) := by ring
      _ ≤ stationaryScale eta *
          (normalizedOneChiPhase (t / stationaryScale eta) + 1) := hlow
  have hupp' :
      stationaryScale eta * (normalizedOneChiPhase (t / stationaryScale eta) + 1) ≤
        (2 / 3 : ℝ) * (t - stationaryScale eta) ^ 2 / stationaryScale eta := by
    calc
      stationaryScale eta * (normalizedOneChiPhase (t / stationaryScale eta) + 1) ≤
          stationaryScale eta *
            ((2 / 3 : ℝ) * (t / stationaryScale eta - 1) ^ 2) := hupp
      _ = (2 / 3 : ℝ) *
          (stationaryScale eta * (t / stationaryScale eta - 1) ^ 2) := by ring
      _ = (2 / 3 : ℝ) * (t - stationaryScale eta) ^ 2 / stationaryScale eta := by
            rw [hquad]
            ring
  constructor
  · rwa [hphase]
  · rwa [hphase]

/-- Physical-variable form of the local derivative comparison.  On the fixed
relative saddle window, the one-chi phase derivative is comparable to the
relative displacement from `t_*`. -/
theorem abs_deriv_oneChiPhase_comparable_relative_displacement
    {eta t : ℝ} (heta : 0 < eta)
    (htlo : (1 / 2 : ℝ) * stationaryScale eta ≤ t)
    (hthi : t ≤ (3 / 2 : ℝ) * stationaryScale eta) :
    (2 / 3 : ℝ) * |t / stationaryScale eta - 1| ≤
        |deriv (oneChiPhase eta) t| ∧
      |deriv (oneChiPhase eta) t| ≤
        2 * |t / stationaryScale eta - 1| := by
  have hspos := stationaryScale_pos heta
  have htpos : 0 < t := by
    have hhalfpos : 0 < (1 / 2 : ℝ) * stationaryScale eta := by positivity
    exact hhalfpos.trans_le htlo
  have hvlo : (1 / 2 : ℝ) ≤ t / stationaryScale eta := by
    exact (le_div_iff₀ hspos).2 htlo
  have hvhi : t / stationaryScale eta ≤ (3 / 2 : ℝ) := by
    exact (div_le_iff₀ hspos).2 hthi
  have hcomp := abs_deriv_normalizedOneChiPhase_comparable hvlo hvhi
  rw [deriv_normalizedOneChiPhase (div_pos htpos hspos).ne'] at hcomp
  rw [deriv_oneChiPhase heta htpos.ne']
  exact hcomp

/-- Uniform cubic error after replacing the normalized phase by its Gaussian
quadratic model on the standard saddle window. -/
theorem normalizedOneChiPhase_quadratic_remainder_bound
    {v : ℝ} (hvlo : (1 / 2 : ℝ) ≤ v) (hvhi : v ≤ 3 / 2) :
    |normalizedOneChiPhase v - (-1 + (v - 1) ^ 2 / 2)| ≤
      (2 / 3 : ℝ) * |v - 1| ^ 3 := by
  by_cases hvone : v = 1
  · subst v
    simp [normalizedOneChiPhase]
  · have hvpos : 0 < v := by linarith
    obtain ⟨xi, hxi, hrem⟩ :=
      exists_normalizedOneChiPhase_quadratic_remainder hvpos hvone
    have hxiStd : xi ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) := by
      apply Set.uIoo_subset_Ioo (a₁ := (1 : ℝ)) (b₁ := v)
      · norm_num
      · exact ⟨hvlo, hvhi⟩
      · exact hxi
    have hxilo : (1 / 2 : ℝ) ≤ xi := le_of_lt hxiStd.1
    have hxihi : xi ≤ (3 / 2 : ℝ) := le_of_lt hxiStd.2
    have hcoef := abs_thirdDeriv_normalizedOneChiPhase_le_four hxilo hxihi
    have hxipos : 0 < xi := by linarith
    rw [thirdDeriv_normalizedOneChiPhase hxipos.ne'] at hcoef
    have hcoef' : (xi ^ 2)⁻¹ ≤ 4 := by
      simpa [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg xi))] using hcoef
    rw [hrem, abs_div, abs_mul, abs_pow, abs_neg]
    norm_num
    calc
      (xi ^ 2)⁻¹ * |v - 1| ^ 3 / 6 ≤
          4 * |v - 1| ^ 3 / 6 := by
            gcongr
      _ = (2 / 3 : ℝ) * |v - 1| ^ 3 := by ring

/-- Carrier-dependent form of the Gaussian phase replacement.  After the exact
rescaling `t = t_* v`, the cubic error grows by precisely the saddle scale. -/
theorem oneChiPhase_rescaled_quadratic_remainder_bound
    {eta v : ℝ} (heta : 0 < eta)
    (hvlo : (1 / 2 : ℝ) ≤ v) (hvhi : v ≤ 3 / 2) :
    |oneChiPhase eta (stationaryScale eta * v) -
        (-stationaryScale eta - Real.pi / 4 +
          stationaryScale eta * (v - 1) ^ 2 / 2)| ≤
      stationaryScale eta * ((2 / 3 : ℝ) * |v - 1| ^ 3) := by
  have hspos := stationaryScale_pos heta
  rw [oneChiPhase_rescale heta]
  have hnorm := normalizedOneChiPhase_quadratic_remainder_bound hvlo hvhi
  have hrewrite :
      stationaryScale eta * normalizedOneChiPhase v - Real.pi / 4 -
          (-stationaryScale eta - Real.pi / 4 +
            stationaryScale eta * (v - 1) ^ 2 / 2) =
        stationaryScale eta *
          (normalizedOneChiPhase v - (-1 + (v - 1) ^ 2 / 2)) := by
    ring
  rw [hrewrite, abs_mul, abs_of_pos hspos]
  exact mul_le_mul_of_nonneg_left hnorm hspos.le

/-- Gaussian-scale form of the local phase approximation.  Writing
`v = 1 + u / sqrt(t_*)`, the quadratic phase becomes exactly `u^2/2`, while
the cubic error is `O(|u|^3 / sqrt(t_*))` with an explicit constant. -/
theorem oneChiPhase_gaussian_rescaling_remainder_bound
    {eta u : ℝ} (heta : 0 < eta)
    (hu : |u| ≤ Real.sqrt (stationaryScale eta) / 2) :
    |oneChiPhase eta
          (stationaryScale eta *
            (1 + u / Real.sqrt (stationaryScale eta))) -
        (-stationaryScale eta - Real.pi / 4 + u ^ 2 / 2)| ≤
      (2 / 3 : ℝ) * |u| ^ 3 / Real.sqrt (stationaryScale eta) := by
  have hspos := stationaryScale_pos heta
  have hsqrtpos : 0 < Real.sqrt (stationaryScale eta) := Real.sqrt_pos.2 hspos
  have hsqrtne := hsqrtpos.ne'
  have hratio : |u / Real.sqrt (stationaryScale eta)| ≤ (1 / 2 : ℝ) := by
    rw [abs_div, abs_of_pos hsqrtpos]
    apply (div_le_iff₀ hsqrtpos).2
    nlinarith
  have hratioBounds := abs_le.mp hratio
  have hvlo :
      (1 / 2 : ℝ) ≤ 1 + u / Real.sqrt (stationaryScale eta) := by
    have hneg : -(1 / 2 : ℝ) ≤ u / Real.sqrt (stationaryScale eta) := hratioBounds.1
    linarith
  have hvhi :
      1 + u / Real.sqrt (stationaryScale eta) ≤ (3 / 2 : ℝ) := by
    have hpos : u / Real.sqrt (stationaryScale eta) ≤ (1 / 2 : ℝ) := hratioBounds.2
    linarith
  have hbase := oneChiPhase_rescaled_quadratic_remainder_bound
    (eta := eta) (v := 1 + u / Real.sqrt (stationaryScale eta)) heta hvlo hvhi
  have hsquare : Real.sqrt (stationaryScale eta) ^ 2 = stationaryScale eta :=
    Real.sq_sqrt hspos.le
  have hquad :
      stationaryScale eta *
          ((1 + u / Real.sqrt (stationaryScale eta)) - 1) ^ 2 / 2 =
        u ^ 2 / 2 := by
    field_simp [hsqrtne]
    nlinarith [hsquare]
  have hrhs :
      stationaryScale eta *
          ((2 / 3 : ℝ) *
            |(1 + u / Real.sqrt (stationaryScale eta)) - 1| ^ 3) =
        (2 / 3 : ℝ) * |u| ^ 3 / Real.sqrt (stationaryScale eta) := by
    rw [show (1 + u / Real.sqrt (stationaryScale eta)) - 1 =
        u / Real.sqrt (stationaryScale eta) by ring]
    rw [abs_div, abs_of_pos hsqrtpos]
    field_simp [hsqrtne]
    rw [hsquare]
    ring
  rw [hquad] at hbase
  rwa [hrhs] at hbase

end RightEdgeArithmeticSource
end ZetaZero
