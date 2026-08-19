import ZetaZero.RightEdgeArithmeticSource.StationaryPhaseGeometry
import Mathlib.Tactic

/-!
# Quantitative nonstationary bounds for the one-chi phase

After the exact normalization `t = t_* v`, the derivative of the universal
phase is `log v`.  This file records explicit lower bounds for its absolute
value away from the saddle `v=1`, and transfers them back to the physical
one-chi phase.  These are the quantitative inputs needed for the
nonstationary integration-by-parts region of the later stationary-phase proof.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Positive derivative margin on the right of the normalized saddle. -/
def rightNonstationaryMargin (delta : ℝ) : ℝ :=
  Real.log (1 + delta)

/-- Positive derivative margin on the left of the normalized saddle. -/
def leftNonstationaryMargin (delta : ℝ) : ℝ :=
  -Real.log (1 - delta)

/-- The right-hand derivative margin is strictly positive for every positive
relative separation from the saddle. -/
theorem rightNonstationaryMargin_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    0 < rightNonstationaryMargin delta := by
  unfold rightNonstationaryMargin
  exact Real.log_pos (by linarith)

/-- The left-hand derivative margin is strictly positive while the relative
separation remains smaller than one. -/
theorem leftNonstationaryMargin_pos
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    0 < leftNonstationaryMargin delta := by
  unfold leftNonstationaryMargin
  have hpos : 0 < 1 - delta := by linarith
  have hlt : 1 - delta < 1 := by linarith
  have hlog : Real.log (1 - delta) < 0 := by
    exact (Real.log_neg_iff hpos).2 hlt
  linarith

/-- To the right of `v=1+delta`, the normalized phase derivative is uniformly
bounded away from zero by `log(1+delta)`. -/
theorem rightNonstationary_deriv_bound
    {delta v : ℝ} (hdelta : 0 < delta) (hv : 1 + delta ≤ v) :
    rightNonstationaryMargin delta ≤
      |deriv normalizedOneChiPhase v| := by
  have hvpos : 0 < v := by linarith
  rw [deriv_normalizedOneChiPhase hvpos.ne']
  have hmono : Real.log (1 + delta) ≤ Real.log v := by
    exact Real.log_le_log (by linarith) hv
  have hvone : 1 ≤ v := by linarith
  rw [abs_of_nonneg (Real.log_nonneg hvone)]
  exact hmono

/-- To the left of `v=1-delta`, the normalized phase derivative is uniformly
bounded away from zero by `-log(1-delta)`. -/
theorem leftNonstationary_deriv_bound
    {delta v : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hvpos : 0 < v) (hv : v ≤ 1 - delta) :
    leftNonstationaryMargin delta ≤
      |deriv normalizedOneChiPhase v| := by
  rw [deriv_normalizedOneChiPhase hvpos.ne']
  have hcutpos : 0 < 1 - delta := by linarith
  have hmono : Real.log v ≤ Real.log (1 - delta) :=
    (Real.log_le_log_iff hvpos hcutpos).2 hv
  have hvone : v ≤ 1 := by linarith
  rw [abs_of_nonpos (Real.log_nonpos hvpos.le hvone)]
  unfold leftNonstationaryMargin
  linarith

/-- Physical right-side nonstationary bound: once `t` lies at least a relative
factor `1+delta` above the saddle, the phase derivative has the same universal
margin as in normalized coordinates. -/
theorem oneChiPhase_rightNonstationary_deriv_bound
    {eta delta t : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta)
    (ht : (1 + delta) * stationaryScale eta ≤ t) :
    rightNonstationaryMargin delta ≤ |deriv (oneChiPhase eta) t| := by
  have hspos := stationaryScale_pos heta
  have htpos : 0 < t := by
    have hfactor : 0 < 1 + delta := by linarith
    exact (mul_pos hfactor hspos).trans_le ht
  rw [deriv_oneChiPhase heta htpos.ne']
  have hratio : 1 + delta ≤ t / stationaryScale eta := by
    exact (le_div_iff₀ hspos).2 ht
  have hmono : Real.log (1 + delta) ≤
      Real.log (t / stationaryScale eta) := by
    exact Real.log_le_log (by linarith) hratio
  have hratioOne : 1 ≤ t / stationaryScale eta := by linarith
  rw [abs_of_nonneg (Real.log_nonneg hratioOne)]
  exact hmono

/-- Physical left-side nonstationary bound: below the relative saddle factor
`1-delta`, the absolute phase derivative is bounded below by the universal
left margin. -/
theorem oneChiPhase_leftNonstationary_deriv_bound
    {eta delta t : ℝ}
    (heta : 0 < eta)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (htpos : 0 < t)
    (ht : t ≤ (1 - delta) * stationaryScale eta) :
    leftNonstationaryMargin delta ≤ |deriv (oneChiPhase eta) t| := by
  have hspos := stationaryScale_pos heta
  rw [deriv_oneChiPhase heta htpos.ne']
  have hratioPos : 0 < t / stationaryScale eta := div_pos htpos hspos
  have hratio : t / stationaryScale eta ≤ 1 - delta := by
    exact (div_le_iff₀ hspos).2 ht
  have hcutpos : 0 < 1 - delta := by linarith
  have hmono : Real.log (t / stationaryScale eta) ≤
      Real.log (1 - delta) :=
    (Real.log_le_log_iff hratioPos hcutpos).2 hratio
  have hratioOne : t / stationaryScale eta ≤ 1 := by linarith
  rw [abs_of_nonpos (Real.log_nonpos hratioPos.le hratioOne)]
  unfold leftNonstationaryMargin
  linarith

end RightEdgeArithmeticSource
end ZetaZero
