import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact geometry of the one-chi stationary phase

This module formalizes the exact calculus preceding any oscillatory-integral
asymptotic.  For the manuscript phase

`Phi_eta(t) = t * log (t / (2*pi*eta)) - t - pi/4`,

the unique formal saddle scale is `t_* = 2*pi*eta`, the first derivative
vanishes there, and the Hessian is `1/t_*`.  The dependence of the saddle on a
logarithmic packet displacement is exactly multiplicative, giving the geometric
core of dilation covariance.

No stationary-phase expansion or remainder estimate is asserted here.
-/

noncomputable section

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The physical saddle scale attached to a positive carrier ratio `eta`. -/
def stationaryScale (eta : ℝ) : ℝ := 2 * Real.pi * eta

/-- The one-chi phase used after Stirling reduction. -/
def oneChiPhase (eta t : ℝ) : ℝ :=
  t * Real.log (t / stationaryScale eta) - t - Real.pi / 4

/-- Packet displacement acts on the saddle scale by exact dilation. -/
theorem stationaryScale_dilation (w xi : ℝ) :
    stationaryScale (Real.exp w * xi) = Real.exp w * stationaryScale xi := by
  unfold stationaryScale
  ring

/-- Positivity of the physical saddle scale. -/
theorem stationaryScale_pos {eta : ℝ} (heta : 0 < eta) :
    0 < stationaryScale eta := by
  unfold stationaryScale
  positivity

/-- The logarithmic factor has derivative `1/t`; the carrier scale cancels
exactly. -/
theorem hasDerivAt_log_div_stationaryScale
    {eta t : ℝ} (heta : 0 < eta) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (x / stationaryScale eta)) (1 / t) t := by
  have hs : stationaryScale eta ≠ 0 := (stationaryScale_pos heta).ne'
  have hratio : t / stationaryScale eta ≠ 0 := div_ne_zero ht hs
  have hinner : HasDerivAt (fun x : ℝ => x / stationaryScale eta)
      (1 / stationaryScale eta) t := by
    simpa using (hasDerivAt_id t).div_const (stationaryScale eta)
  have hlog := (Real.hasDerivAt_log hratio).comp t hinner
  have hlog' : HasDerivAt
      (fun x : ℝ => Real.log (x / stationaryScale eta))
      ((stationaryScale eta * t⁻¹) * (stationaryScale eta)⁻¹) t := by
    simpa [Function.comp_def, div_eq_mul_inv] using hlog
  have hcoef :
      (stationaryScale eta * t⁻¹) * (stationaryScale eta)⁻¹ = t⁻¹ := by
    calc
      (stationaryScale eta * t⁻¹) * (stationaryScale eta)⁻¹ =
          t⁻¹ * (stationaryScale eta * (stationaryScale eta)⁻¹) := by ring
      _ = t⁻¹ := by simp [hs]
  rw [hcoef] at hlog'
  simpa [one_div] using hlog'

/-- Exact first derivative of the one-chi phase. -/
theorem hasDerivAt_oneChiPhase
    {eta t : ℝ} (heta : 0 < eta) (ht : t ≠ 0) :
    HasDerivAt (oneChiPhase eta) (Real.log (t / stationaryScale eta)) t := by
  have hlog := hasDerivAt_log_div_stationaryScale heta ht
  have hraw :=
    ((((hasDerivAt_id t).mul hlog).sub (hasDerivAt_id t)).sub
      (hasDerivAt_const t (Real.pi / 4)))
  have hcoef :
      1 * Real.log (t / stationaryScale eta) + t * (1 / t) - 1 - 0 =
        Real.log (t / stationaryScale eta) := by
    simp [ht]
  have hraw' := hraw.congr_deriv hcoef
  refine hraw'.congr_of_eventuallyEq ?_
  filter_upwards with x
  simp [oneChiPhase, id_eq]

/-- The derivative of the phase is the logarithmic saddle equation. -/
theorem deriv_oneChiPhase
    {eta t : ℝ} (heta : 0 < eta) (ht : t ≠ 0) :
    deriv (oneChiPhase eta) t = Real.log (t / stationaryScale eta) :=
  (hasDerivAt_oneChiPhase heta ht).deriv

/-- The saddle equation vanishes at `t_* = 2*pi*eta`. -/
@[simp] theorem deriv_oneChiPhase_stationaryScale
    {eta : ℝ} (heta : 0 < eta) :
    deriv (oneChiPhase eta) (stationaryScale eta) = 0 := by
  rw [deriv_oneChiPhase heta (stationaryScale_pos heta).ne']
  simp

/-- The second derivative of the phase is `1/t` away from zero. -/
theorem secondDeriv_oneChiPhase
    {eta t : ℝ} (heta : 0 < eta) (ht : t ≠ 0) :
    deriv (deriv (oneChiPhase eta)) t = 1 / t := by
  have hlocal :
      ∀ᶠ x in nhds t, x ≠ 0 := by
    exact eventually_ne_nhds ht
  have heq :
      deriv (oneChiPhase eta) =ᶠ[nhds t]
        (fun x : ℝ => Real.log (x / stationaryScale eta)) := by
    filter_upwards [hlocal] with x hx
    exact deriv_oneChiPhase heta hx
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact (hasDerivAt_log_div_stationaryScale heta ht).deriv

/-- The Hessian at the saddle is exactly `1/t_*`. -/
@[simp] theorem secondDeriv_oneChiPhase_stationaryScale
    {eta : ℝ} (heta : 0 < eta) :
    deriv (deriv (oneChiPhase eta)) (stationaryScale eta) =
      1 / stationaryScale eta := by
  exact secondDeriv_oneChiPhase heta (stationaryScale_pos heta).ne'

/-- The saddle is nondegenerate for every positive carrier ratio. -/
theorem secondDeriv_oneChiPhase_stationaryScale_ne_zero
    {eta : ℝ} (heta : 0 < eta) :
    deriv (deriv (oneChiPhase eta)) (stationaryScale eta) ≠ 0 := by
  rw [secondDeriv_oneChiPhase_stationaryScale heta]
  exact one_div_ne_zero (stationaryScale_pos heta).ne'

/-- Exact value of the phase at the saddle.  This is the real-variable content
behind the carrier `exp(-2*pi*i*eta)` after the Gaussian `+pi/4` correction. -/
theorem oneChiPhase_stationaryScale
    {eta : ℝ} (heta : 0 < eta) :
    oneChiPhase eta (stationaryScale eta) =
      -stationaryScale eta - Real.pi / 4 := by
  unfold oneChiPhase
  rw [Real.log_div (stationaryScale_pos heta).ne' (stationaryScale_pos heta).ne']
  simp

/-- Universal normalized phase after the exact change of variables `t=t_* v`. -/
def normalizedOneChiPhase (v : ℝ) : ℝ :=
  v * Real.log v - v

/-- After rescaling by the saddle, all carrier dependence is pulled out as the
single prefactor `t_*`; the shape of the phase is universal. -/
theorem oneChiPhase_rescale
    {eta : ℝ} (heta : 0 < eta) (v : ℝ) :
    oneChiPhase eta (stationaryScale eta * v) =
      stationaryScale eta * normalizedOneChiPhase v - Real.pi / 4 := by
  have hs : stationaryScale eta ≠ 0 := (stationaryScale_pos heta).ne'
  have hdiv : stationaryScale eta * v / stationaryScale eta = v := by
    field_simp [hs]
  unfold oneChiPhase normalizedOneChiPhase
  rw [hdiv]
  ring

/-- First derivative of the universal normalized phase. -/
theorem hasDerivAt_normalizedOneChiPhase
    {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt normalizedOneChiPhase (Real.log v) v := by
  have hlog := Real.hasDerivAt_log hv
  have hraw := ((hasDerivAt_id v).mul hlog).sub (hasDerivAt_id v)
  have hcoef : 1 * Real.log v + v * v⁻¹ - 1 = Real.log v := by
    simp [hv]
  have hraw' := hraw.congr_deriv hcoef
  refine hraw'.congr_of_eventuallyEq ?_
  filter_upwards with x
  simp [normalizedOneChiPhase, id_eq]

/-- Exact first derivative of the normalized phase away from zero. -/
theorem deriv_normalizedOneChiPhase
    {v : ℝ} (hv : v ≠ 0) :
    deriv normalizedOneChiPhase v = Real.log v :=
  (hasDerivAt_normalizedOneChiPhase hv).deriv

/-- Exact second derivative of the normalized phase away from zero. -/
theorem secondDeriv_normalizedOneChiPhase
    {v : ℝ} (hv : v ≠ 0) :
    deriv (deriv normalizedOneChiPhase) v = 1 / v := by
  have hlocal : ∀ᶠ x in nhds v, x ≠ 0 := eventually_ne_nhds hv
  have heq :
      deriv normalizedOneChiPhase =ᶠ[nhds v] Real.log := by
    filter_upwards [hlocal] with x hx
    exact deriv_normalizedOneChiPhase hx
  rw [Filter.EventuallyEq.deriv_eq heq]
  simp [one_div]

/-- The normalized phase is strictly convex on the positive carrier axis. -/
theorem secondDeriv_normalizedOneChiPhase_pos
    {v : ℝ} (hv : 0 < v) :
    0 < deriv (deriv normalizedOneChiPhase) v := by
  rw [secondDeriv_normalizedOneChiPhase hv.ne']
  exact one_div_pos.mpr hv

/-- On the positive axis, `v=1` is the unique stationary point. -/
theorem deriv_normalizedOneChiPhase_eq_zero_iff
    {v : ℝ} (hv : 0 < v) :
    deriv normalizedOneChiPhase v = 0 ↔ v = 1 := by
  rw [deriv_normalizedOneChiPhase hv.ne']
  constructor
  · intro h
    exact Real.eq_one_of_pos_of_log_eq_zero hv h
  · rintro rfl
    simp

/-- The normalized saddle sits at `v=1`. -/
@[simp] theorem deriv_normalizedOneChiPhase_one :
    deriv normalizedOneChiPhase 1 = 0 := by
  exact (deriv_normalizedOneChiPhase_eq_zero_iff one_pos).2 rfl

/-- The normalized Hessian is exactly `1` at the universal saddle. -/
@[simp] theorem secondDeriv_normalizedOneChiPhase_one :
    deriv (deriv normalizedOneChiPhase) 1 = 1 := by
  rw [secondDeriv_normalizedOneChiPhase one_ne_zero]
  norm_num

/-- On the physical positive axis, the one-chi phase has exactly one stationary
point, namely `t = 2*pi*eta`. -/
theorem deriv_oneChiPhase_eq_zero_iff_stationaryScale
    {eta t : ℝ} (heta : 0 < eta) (ht : 0 < t) :
    deriv (oneChiPhase eta) t = 0 ↔ t = stationaryScale eta := by
  rw [deriv_oneChiPhase heta ht.ne']
  have hspos := stationaryScale_pos heta
  have hratio : 0 < t / stationaryScale eta := div_pos ht hspos
  constructor
  · intro h
    have hone := Real.eq_one_of_pos_of_log_eq_zero hratio h
    exact (div_eq_one_iff_eq hspos.ne').1 hone
  · intro h
    rw [h]
    simp

end RightEdgeArithmeticSource
end ZetaZero
