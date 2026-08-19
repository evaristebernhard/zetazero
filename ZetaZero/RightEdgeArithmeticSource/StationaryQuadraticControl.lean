import ZetaZero.RightEdgeArithmeticSource.StationaryPhaseGeometry
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

/-!
# Local quadratic control near the one-chi saddle

The normalized phase

`Psi(v) = v * log v - v`

has saddle at `v = 1` and Hessian `1 / v`.  This module records the uniform
curvature control on a relative window `|v - 1| <= delta < 1`.  It is the
local analytic input needed before turning the saddle contribution into a
Gaussian main term with a controlled remainder.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- On a relative saddle window, the normalized Hessian is trapped between
its endpoint reciprocal values. -/
theorem normalizedOneChiPhase_hessian_bounds
    {delta v : ℝ}
    (hdelta1 : delta < 1)
    (hv : |v - 1| ≤ delta) :
    1 / (1 + delta) ≤ deriv (deriv normalizedOneChiPhase) v ∧
      deriv (deriv normalizedOneChiPhase) v ≤ 1 / (1 - delta) := by
  have habs := (abs_le.mp hv)
  have hvlow : 1 - delta ≤ v := by linarith [habs.1]
  have hvupper : v ≤ 1 + delta := by linarith [habs.2]
  have hcutpos : 0 < 1 - delta := by linarith
  have hvpos : 0 < v := hcutpos.trans_le hvlow
  rw [secondDeriv_normalizedOneChiPhase hvpos.ne']
  constructor
  · exact one_div_le_one_div_of_le hvpos hvupper
  · exact one_div_le_one_div_of_le hcutpos hvlow

/-- The normalized Hessian differs from its saddle value `1` by at most the
relative displacement divided by the distance of the window from zero. -/
theorem normalizedOneChiPhase_hessian_deviation_bound
    {delta v : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    (hv : |v - 1| ≤ delta) :
    |deriv (deriv normalizedOneChiPhase) v - 1| ≤ delta / (1 - delta) := by
  have habs := (abs_le.mp hv)
  have hvlow : 1 - delta ≤ v := by linarith [habs.1]
  have hcutpos : 0 < 1 - delta := by linarith
  have hvpos : 0 < v := hcutpos.trans_le hvlow
  rw [secondDeriv_normalizedOneChiPhase hvpos.ne']
  have hformula : 1 / v - 1 = -(v - 1) / v := by
    field_simp [hvpos.ne']
    ring
  rw [hformula, abs_div, abs_neg, abs_of_pos hvpos]
  apply (div_le_div_iff₀ hvpos hcutpos).2
  have hmul1 : |v - 1| * (1 - delta) ≤ delta * (1 - delta) :=
    mul_le_mul_of_nonneg_right hv hcutpos.le
  have hmul2 : delta * (1 - delta) ≤ delta * v :=
    mul_le_mul_of_nonneg_left hvlow hdelta0
  exact hmul1.trans hmul2

/-- Exact third derivative of the universal phase.  This is the derivative
level from which the cubic Taylor remainder is controlled. -/
theorem thirdDeriv_normalizedOneChiPhase
    {v : ℝ} (hv : v ≠ 0) :
    deriv (deriv (deriv normalizedOneChiPhase)) v = -(v ^ 2)⁻¹ := by
  have hlocal : ∀ᶠ x in nhds v, x ≠ 0 := eventually_ne_nhds hv
  have heq :
      deriv (deriv normalizedOneChiPhase) =ᶠ[nhds v] (fun x : ℝ => x⁻¹) := by
    filter_upwards [hlocal] with x hx
    simpa [one_div] using secondDeriv_normalizedOneChiPhase hx
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact (hasDerivAt_inv hv).deriv

/-- Uniform third-derivative bound on a relative saddle window. -/
theorem thirdDeriv_normalizedOneChiPhase_abs_bound
    {delta v : ℝ}
    (hdelta1 : delta < 1)
    (hv : |v - 1| ≤ delta) :
    |deriv (deriv (deriv normalizedOneChiPhase)) v| ≤ 1 / (1 - delta) ^ 2 := by
  have habs := (abs_le.mp hv)
  have hvlow : 1 - delta ≤ v := by linarith [habs.1]
  have hcutpos : 0 < 1 - delta := by linarith
  have hvpos : 0 < v := hcutpos.trans_le hvlow
  rw [thirdDeriv_normalizedOneChiPhase hvpos.ne']
  rw [abs_neg, abs_inv, abs_pow, abs_of_pos hvpos]
  have hsquare : (1 - delta) ^ 2 ≤ v ^ 2 := by
    nlinarith
  simpa [one_div] using inv_anti₀ (sq_pos_of_pos hcutpos) hsquare

/-- The normalized phase is `C^3` on the positive axis. -/
theorem normalizedOneChiPhase_contDiffOn_pos :
    ContDiffOn ℝ 3 normalizedOneChiPhase (Set.Ioi 0) := by
  intro x hx
  have hlog : ContDiffAt ℝ 3 Real.log x := (Real.contDiffAt_log).2 hx.ne'
  change ContDiffWithinAt ℝ 3 (fun y : ℝ => y * Real.log y - y) (Set.Ioi 0) x
  exact ((contDiffAt_id.mul hlog).sub contDiffAt_id).contDiffWithinAt

/-- The quadratic Taylor polynomial of the normalized phase at the universal
saddle is exactly `-1 + (v-1)^2/2`. -/
theorem normalizedOneChiPhase_taylorWithin_two
    {v : ℝ} (hvne : v ≠ 1) :
    taylorWithinEval normalizedOneChiPhase 2 (Set.uIcc 1 v) 1 v =
      -1 + (v - 1) ^ 2 / 2 := by
  have hu : UniqueDiffOn ℝ (Set.uIcc 1 v) := uniqueDiffOn_uIcc hvne.symm
  have hmem : 1 ∈ Set.uIcc 1 v := by simp
  have hcont : ContDiffAt ℝ 3 normalizedOneChiPhase 1 := by
    have hlog : ContDiffAt ℝ 3 Real.log 1 := (Real.contDiffAt_log).2 one_ne_zero
    change ContDiffAt ℝ 3 (fun y : ℝ => y * Real.log y - y) 1
    exact (contDiffAt_id.mul hlog).sub contDiffAt_id
  have hwithin1 :
      iteratedDerivWithin 1 normalizedOneChiPhase (Set.uIcc 1 v) 1 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hcont.of_le (by norm_num)) hmem]
    simp [iteratedDeriv_succ]
  have hwithin2 :
      iteratedDerivWithin 2 normalizedOneChiPhase (Set.uIcc 1 v) 1 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hcont.of_le (by norm_num)) hmem]
    simp [iteratedDeriv_succ]
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
  simp [hwithin1, hwithin2, normalizedOneChiPhase]
  ring

/-- Lagrange form of the cubic remainder around the normalized saddle. -/
theorem exists_normalizedOneChiPhase_quadratic_remainder
    {v : ℝ} (hvpos : 0 < v) (hvne : v ≠ 1) :
    ∃ xi ∈ Set.uIoo 1 v,
      normalizedOneChiPhase v - (-1 + (v - 1) ^ 2 / 2) =
        -(xi ^ 2)⁻¹ * (v - 1) ^ 3 / 6 := by
  have hsubset : Set.uIcc 1 v ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with hx | hx
    · exact one_pos.trans_le hx.1
    · exact hvpos.trans_le hx.1
  have hcont : ContDiffOn ℝ 3 normalizedOneChiPhase (Set.uIcc 1 v) :=
    normalizedOneChiPhase_contDiffOn_pos.mono hsubset
  obtain ⟨xi, hxi, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hvne.symm hcont
  have hxipos : 0 < xi := hsubset (Set.uIoo_subset_uIcc_self hxi)
  have hiter3 : iteratedDeriv 3 normalizedOneChiPhase xi = -(xi ^ 2)⁻¹ := by
    simpa [iteratedDeriv_succ] using thirdDeriv_normalizedOneChiPhase hxipos.ne'
  refine ⟨xi, hxi, ?_⟩
  rw [normalizedOneChiPhase_taylorWithin_two hvne] at heq
  rw [hiter3] at heq
  norm_num at heq ⊢
  exact heq

end RightEdgeArithmeticSource
end ZetaZero
