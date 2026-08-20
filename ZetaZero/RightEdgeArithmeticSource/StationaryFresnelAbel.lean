import ZetaZero.RightEdgeArithmeticSource.StationaryGaussianTail
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Abel damping for the quadratic Fresnel model

For `ε > 0` we use the genuinely integrable Gaussian

`exp (-(ε - i/2) y^2)`.

Its Gaussian parameter has positive real part, so Mathlib's complex Gaussian
integral applies directly.  This file deliberately stays inside `ε > 0`; the
passage `ε ↓ 0` is a separate limit step.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- Complex Gaussian parameter for Abel damping of `exp(i y^2/2)`. -/
def abelGaussianParameter (ε : ℝ) : ℂ :=
  (ε : ℂ) - Complex.I / 2

@[simp] theorem abelGaussianParameter_re (ε : ℝ) :
    (abelGaussianParameter ε).re = ε := by
  simp [abelGaussianParameter]

@[simp] theorem abelGaussianParameter_im (ε : ℝ) :
    (abelGaussianParameter ε).im = -(1 / 2 : ℝ) := by
  simp [abelGaussianParameter]

/-- The imaginary part keeps the Abel parameter uniformly away from zero. -/
theorem one_half_le_norm_abelGaussianParameter (ε : ℝ) :
    (1 / 2 : ℝ) ≤ ‖abelGaussianParameter ε‖ := by
  have h := Complex.abs_im_le_norm (abelGaussianParameter ε)
  simpa using h

/-- The coefficient appearing after reciprocal-weight integration by parts has
norm at least one, uniformly in the damping parameter. -/
theorem one_le_norm_neg_two_mul_abelGaussianParameter (ε : ℝ) :
    (1 : ℝ) ≤ ‖(-2 : ℂ) * abelGaussianParameter ε‖ := by
  rw [norm_mul]
  have h := one_half_le_norm_abelGaussianParameter ε
  norm_num at ⊢
  linarith

/-- Positive damping gives a Gaussian parameter in the open right half-plane. -/
theorem abelGaussianParameter_re_pos
    {ε : ℝ} (hε : 0 < ε) :
    0 < (abelGaussianParameter ε).re := by
  simpa using hε

/-- Abel-damped quadratic oscillation. -/
def abelDampedQuadratic (ε y : ℝ) : ℂ :=
  Complex.exp (-abelGaussianParameter ε * (y : ℂ) ^ 2)

/-- Exact real derivative of the Abel-damped quadratic kernel. -/
theorem hasDerivAt_abelDampedQuadratic (ε y : ℝ) :
    HasDerivAt (abelDampedQuadratic ε)
      ((-2 : ℂ) * abelGaussianParameter ε * (y : ℂ) * abelDampedQuadratic ε y) y := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y :=
    Complex.ofRealCLM.hasDerivAt
  have hsq := hcast.mul hcast
  have hphase := hsq.const_mul (-abelGaussianParameter ε)
  have hexp := hphase.cexp
  unfold abelDampedQuadratic
  convert hexp using 1
  all_goals simp [pow_two]
  all_goals ring

/-- For nonnegative damping the Abel kernel has norm at most one. -/
theorem norm_abelDampedQuadratic_le_one
    {ε y : ℝ} (hε : 0 ≤ ε) :
    ‖abelDampedQuadratic ε y‖ ≤ 1 := by
  unfold abelDampedQuadratic
  rw [Complex.norm_exp]
  have hexp :
      (-abelGaussianParameter ε * (y : ℂ) ^ 2).re = -ε * y ^ 2 := by
    simp [abelGaussianParameter, pow_two, Complex.mul_re]
  rw [hexp]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hε (sq_nonneg y)])

/-- The reciprocal real weight cancels the factor `y` in the damped derivative. -/
theorem quadraticRealIBPWeight_smul_abelDamped_deriv
    {ε y : ℝ} (hy : y ≠ 0) :
    quadraticRealIBPWeight y •
        ((-2 : ℂ) * abelGaussianParameter ε * (y : ℂ) * abelDampedQuadratic ε y) =
      ((-2 : ℂ) * abelGaussianParameter ε) * abelDampedQuadratic ε y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  rw [Complex.real_smul]
  change (((y⁻¹ : ℝ) : ℂ) *
      (((-2 : ℂ) * abelGaussianParameter ε * (y : ℂ)) * abelDampedQuadratic ε y)) =
    ((-2 : ℂ) * abelGaussianParameter ε) * abelDampedQuadratic ε y
  rw [Complex.ofReal_inv]
  field_simp [hyC]

/-- The damped kernel factors into real Gaussian decay times the undamped
quadratic oscillation. -/
theorem abelDampedQuadratic_eq_decay_mul
    (ε y : ℝ) :
    abelDampedQuadratic ε y =
      Complex.exp (-(ε : ℂ) * (y : ℂ) ^ 2) * quadraticOscillation y := by
  unfold abelDampedQuadratic abelGaussianParameter quadraticOscillation
  rw [← Complex.exp_add]
  congr 1
  ring

@[simp] theorem abelDampedQuadratic_zero (y : ℝ) :
    abelDampedQuadratic 0 y = quadraticOscillation y := by
  rw [abelDampedQuadratic_eq_decay_mul]
  simp

/-- On every finite interval, the Abel-damped integral is continuous at zero
damping from the nonnegative side.  This is an ordinary dominated-convergence
step; the conditional convergence issue only occurs at infinity. -/
theorem continuousWithinAt_intervalIntegral_abelDampedQuadratic_zero (R : ℝ) :
    ContinuousWithinAt
      (fun ε : ℝ => ∫ y in 0..R, abelDampedQuadratic ε y)
      (Set.Ici 0) 0 := by
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (μ := volume) (bound := fun _ : ℝ => (1 : ℝ))
  · filter_upwards with ε
    have hc : Continuous (abelDampedQuadratic ε) := by
      unfold abelDampedQuadratic abelGaussianParameter
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ fun y _ =>
      norm_abelDampedQuadratic_le_one (ε := ε) (y := y) hε
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun y _ => by
      apply Continuous.continuousWithinAt
      unfold abelDampedQuadratic abelGaussianParameter
      fun_prop

/-- The finite Abel integral converges to the finite undamped quadratic integral
as `ε ↓ 0`. -/
theorem tendsto_intervalIntegral_abelDampedQuadratic_zero (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ y in 0..R, abelDampedQuadratic ε y)
      (𝓝[Set.Ici 0] 0) (𝓝 (∫ y in 0..R, quadraticOscillation y)) := by
  have h := continuousWithinAt_intervalIntegral_abelDampedQuadratic_zero R
  unfold ContinuousWithinAt at h
  simpa using h

/-- For positive damping the Abel kernel is absolutely integrable on the real
line. -/
theorem integrable_abelDampedQuadratic
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (abelDampedQuadratic ε) := by
  unfold abelDampedQuadratic
  exact integrable_cexp_neg_mul_sq (abelGaussianParameter_re_pos hε)

/-- One reciprocal-weight integration by parts gives the same `2/R` tail
bound for every nonnegative Abel damping parameter.  The constant is uniform in
`ε` because `‖ε - i/2‖ ≥ 1/2`. -/
theorem norm_intervalIntegral_abelDampedQuadratic_le_two_div
    {ε R S : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) (hRS : R ≤ S) :
    ‖∫ y in R..S, abelDampedQuadratic ε y‖ ≤ 2 / R := by
  have hS : 0 < S := hR.trans_le hRS
  have hpos : ∀ y ∈ Set.uIcc R S, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hRS] at hy
    exact hR.trans_le hy.1
  have hu : ∀ y ∈ Set.uIcc R S,
      HasDerivAt quadraticRealIBPWeight (quadraticRealIBPWeightDeriv y) y := by
    intro y hy
    exact hasDerivAt_quadraticRealIBPWeight (hpos y hy).ne'
  have hv : ∀ y ∈ Set.uIcc R S,
      HasDerivAt (abelDampedQuadratic ε)
        ((-2 : ℂ) * abelGaussianParameter ε * (y : ℂ) * abelDampedQuadratic ε y) y := by
    intro y _
    exact hasDerivAt_abelDampedQuadratic ε y
  have hu' : IntervalIntegrable quadraticRealIBPWeightDeriv volume R S :=
    intervalIntegrable_quadraticRealIBPWeightDeriv hR hRS
  have hv' : IntervalIntegrable
      (fun y : ℝ =>
        (-2 : ℂ) * abelGaussianParameter ε * (y : ℂ) * abelDampedQuadratic ε y)
      volume R S := by
    apply Continuous.intervalIntegrable
    unfold abelDampedQuadratic abelGaussianParameter
    fun_prop
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (𝕜 := ℝ) (E := ℂ) hu hv hu' hv'
  have hibpNorm :
      (∫ y in R..S,
          quadraticRealIBPWeight y •
            ((-2 : ℂ) * abelGaussianParameter ε * (y : ℂ) * abelDampedQuadratic ε y)) =
        quadraticRealIBPWeight S • abelDampedQuadratic ε S -
          quadraticRealIBPWeight R • abelDampedQuadratic ε R -
        ∫ y in R..S,
          quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y := by
    simpa [quadraticRealIBPWeight, quadraticRealIBPWeightDeriv] using hibp
  have hleft :
      (∫ y in R..S,
          quadraticRealIBPWeight y •
            ((-2 : ℂ) * abelGaussianParameter ε * (y : ℂ) * abelDampedQuadratic ε y)) =
        ((-2 : ℂ) * abelGaussianParameter ε) *
          (∫ y in R..S, abelDampedQuadratic ε y) := by
    calc
      _ = ∫ y in R..S,
          ((-2 : ℂ) * abelGaussianParameter ε) * abelDampedQuadratic ε y := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact quadraticRealIBPWeight_smul_abelDamped_deriv (hpos y hy).ne'
      _ = ((-2 : ℂ) * abelGaussianParameter ε) *
          (∫ y in R..S, abelDampedQuadratic ε y) := by
            rw [intervalIntegral.integral_const_mul]
  rw [hleft] at hibpNorm
  have hrem :
      ‖∫ y in R..S,
          quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y‖ ≤
        1 / R - 1 / S := by
    have hgcont : ContinuousOn (abelDampedQuadratic ε) [[R, S]] := by
      apply Continuous.continuousOn
      unfold abelDampedQuadratic abelGaussianParameter
      fun_prop
    have hint : IntervalIntegrable
        (fun y : ℝ => quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y)
        volume R S := hu'.smul_continuousOn hgcont
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume)
      (f := fun y : ℝ => quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y) hRS
    have hrecip : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) volume R S := by
      apply ContinuousOn.intervalIntegrable
      intro y hy
      have hy0 : y ≠ 0 := (hpos y hy).ne'
      have hpow : ContinuousAt (fun x : ℝ => x ^ 2) y := continuousAt_id.pow 2
      exact (continuousAt_const.div hpow (pow_ne_zero 2 hy0)).continuousWithinAt
    have hmono :
        (∫ y in R..S,
            ‖quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y‖) ≤
          ∫ y in R..S, (1 / y ^ 2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hRS hint.norm hrecip
      intro y hy
      have hypos : 0 < y := hR.trans_le hy.1
      rw [norm_smul]
      have hw : ‖quadraticRealIBPWeightDeriv y‖ = 1 / y ^ 2 := by
        unfold quadraticRealIBPWeightDeriv
        rw [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hypos]
      rw [hw]
      have hg := norm_abelDampedQuadratic_le_one (ε := ε) (y := y) hε
      exact mul_le_of_le_one_right (by positivity) hg
    exact hnorm.trans (hmono.trans_eq (integral_one_div_sq hR hRS))
  have hweightR : ‖quadraticRealIBPWeight R‖ = 1 / R := by
    simp [quadraticRealIBPWeight, Real.norm_eq_abs, abs_of_pos hR]
  have hweightS : ‖quadraticRealIBPWeight S‖ = 1 / S := by
    simp [quadraticRealIBPWeight, Real.norm_eq_abs, abs_of_pos hS]
  have hboundR :
      ‖quadraticRealIBPWeight R • abelDampedQuadratic ε R‖ ≤ 1 / R := by
    rw [norm_smul, hweightR]
    have hg := norm_abelDampedQuadratic_le_one (ε := ε) (y := R) hε
    exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _)
  have hboundS :
      ‖quadraticRealIBPWeight S • abelDampedQuadratic ε S‖ ≤ 1 / S := by
    rw [norm_smul, hweightS]
    have hg := norm_abelDampedQuadratic_le_one (ε := ε) (y := S) hε
    exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _)
  have hcoef :
      ‖∫ y in R..S, abelDampedQuadratic ε y‖ ≤
        ‖((-2 : ℂ) * abelGaussianParameter ε) *
          (∫ y in R..S, abelDampedQuadratic ε y)‖ := by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right
      (one_le_norm_neg_two_mul_abelGaussianParameter ε)
      (norm_nonneg (∫ y in R..S, abelDampedQuadratic ε y))
  calc
    ‖∫ y in R..S, abelDampedQuadratic ε y‖ ≤
        ‖((-2 : ℂ) * abelGaussianParameter ε) *
          (∫ y in R..S, abelDampedQuadratic ε y)‖ := hcoef
    _ = ‖quadraticRealIBPWeight S • abelDampedQuadratic ε S -
          quadraticRealIBPWeight R • abelDampedQuadratic ε R -
          ∫ y in R..S,
            quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y‖ := by
          rw [hibpNorm]
    _ ≤ ‖quadraticRealIBPWeight S • abelDampedQuadratic ε S‖ +
          ‖quadraticRealIBPWeight R • abelDampedQuadratic ε R‖ +
          ‖∫ y in R..S,
            quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y‖ := by
          calc
            _ ≤ ‖quadraticRealIBPWeight S • abelDampedQuadratic ε S -
                  quadraticRealIBPWeight R • abelDampedQuadratic ε R‖ +
                ‖∫ y in R..S,
                  quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y‖ := norm_sub_le _ _
            _ ≤ (‖quadraticRealIBPWeight S • abelDampedQuadratic ε S‖ +
                  ‖quadraticRealIBPWeight R • abelDampedQuadratic ε R‖) +
                ‖∫ y in R..S,
                  quadraticRealIBPWeightDeriv y • abelDampedQuadratic ε y‖ := by
                    gcongr
                    exact norm_sub_le _ _
    _ ≤ 1 / S + 1 / R + (1 / R - 1 / S) := by
          gcongr
    _ = 2 / R := by ring

/-- For positive damping, the improper positive tail inherits the same uniform
`2/R` bound by passing the finite upper endpoint to infinity. -/
theorem norm_integral_abelDampedQuadratic_Ioi_le_two_div
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ‖∫ y : ℝ in Set.Ioi R, abelDampedQuadratic ε y‖ ≤ 2 / R := by
  have hint : IntegrableOn (abelDampedQuadratic ε) (Set.Ioi R) volume :=
    (integrable_abelDampedQuadratic hε).integrableOn
  have ht := intervalIntegral_tendsto_integral_Ioi
    (μ := volume) R hint tendsto_id
  apply le_of_tendsto ht.norm
  filter_upwards [eventually_ge_atTop R] with S hRS
  exact norm_intervalIntegral_abelDampedQuadratic_le_two_div hε.le hR hRS

/-- Abel damping converges to the genuinely constructed positive Fresnel limit.
The proof uses a three-piece decomposition: finite-window dominated convergence,
the undamped truncation limit, and the uniform `2/R` damped tail. -/
theorem tendsto_integral_abelDampedQuadratic_Ioi :
    Tendsto (fun ε : ℝ => ∫ y : ℝ in Set.Ioi 0, abelDampedQuadratic ε y)
      (𝓝[Set.Ioi 0] 0) (𝓝 positiveFresnelLimit) := by
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr ?_
  intro δ hδ
  have hthird : 0 < δ / 3 := by positivity
  obtain ⟨N₀, hN₀⟩ :=
    Metric.tendsto_atTop.mp tendsto_positiveQuadraticTruncation (δ / 3) hthird
  obtain ⟨M, hM⟩ := exists_nat_gt (6 / δ)
  let N := max N₀ M
  let A : ℝ := (((N + 1 : ℕ) : ℝ))
  have hN₀N : N₀ ≤ N := le_max_left _ _
  have hMN : M ≤ N := le_max_right _ _
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hseq :
      dist (positiveQuadraticTruncation N) positiveFresnelLimit < δ / 3 :=
    hN₀ N hN₀N
  have hseq' :
      ‖(∫ y in 0..A, quadraticOscillation y) - positiveFresnelLimit‖ < δ / 3 := by
    simpa [positiveQuadraticTruncation, A, dist_eq_norm] using hseq
  have hsixA : (6 : ℝ) / δ < A := by
    have hMNreal : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hNsucc : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self N
    exact hM.trans_le hMNreal |>.trans hNsucc
  have hsix : (6 : ℝ) < δ * A := by
    have := (div_lt_iff₀ hδ).mp hsixA
    simpa [mul_comm] using this
  have htailSmall : (2 : ℝ) / A < δ / 3 := by
    apply (div_lt_iff₀ hA).2
    nlinarith
  have hfin :
      Tendsto (fun ε : ℝ => ∫ y in 0..A, abelDampedQuadratic ε y)
        (𝓝[Set.Ioi 0] 0) (𝓝 (∫ y in 0..A, quadraticOscillation y)) :=
    (tendsto_intervalIntegral_abelDampedQuadratic_zero A).mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hfinEv :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] 0,
        dist (∫ y in 0..A, abelDampedQuadratic ε y)
          (∫ y in 0..A, quadraticOscillation y) < δ / 3 := by
    have hball :
        Metric.ball (∫ y in 0..A, quadraticOscillation y) (δ / 3) ∈
          𝓝 (∫ y in 0..A, quadraticOscillation y) :=
      Metric.ball_mem_nhds _ hthird
    exact (hfin.eventually hball).mono fun ε hε => by
      simpa [Metric.mem_ball] using hε
  filter_upwards [hfinEv, self_mem_nhdsWithin] with ε hfinite hεpos
  have hε : 0 < ε := hεpos
  have hgint := integrable_abelDampedQuadratic hε
  have hdecomp := intervalIntegral.integral_interval_add_Ioi
    (a := (0 : ℝ)) (b := A) (f := abelDampedQuadratic ε)
    hgint.integrableOn hgint.integrableOn
  have htail := norm_integral_abelDampedQuadratic_Ioi_le_two_div hε hA
  have htail' :
      ‖∫ y : ℝ in Set.Ioi A, abelDampedQuadratic ε y‖ < δ / 3 :=
    htail.trans_lt htailSmall
  have hfinite' :
      ‖(∫ y in 0..A, abelDampedQuadratic ε y) -
          ∫ y in 0..A, quadraticOscillation y‖ < δ / 3 := by
    simpa [dist_eq_norm] using hfinite
  rw [Metric.mem_ball, dist_eq_norm]
  calc
    ‖(∫ y : ℝ in Set.Ioi 0, abelDampedQuadratic ε y) - positiveFresnelLimit‖ =
        ‖((∫ y in 0..A, abelDampedQuadratic ε y) -
            ∫ y in 0..A, quadraticOscillation y) +
          ((∫ y in 0..A, quadraticOscillation y) - positiveFresnelLimit) +
          (∫ y : ℝ in Set.Ioi A, abelDampedQuadratic ε y)‖ := by
            congr 1
            rw [← hdecomp]
            abel
    _ ≤ ‖(∫ y in 0..A, abelDampedQuadratic ε y) -
            ∫ y in 0..A, quadraticOscillation y‖ +
          ‖(∫ y in 0..A, quadraticOscillation y) - positiveFresnelLimit‖ +
          ‖∫ y : ℝ in Set.Ioi A, abelDampedQuadratic ε y‖ := by
            calc
              _ ≤ ‖((∫ y in 0..A, abelDampedQuadratic ε y) -
                      ∫ y in 0..A, quadraticOscillation y) +
                    ((∫ y in 0..A, quadraticOscillation y) - positiveFresnelLimit)‖ +
                    ‖∫ y : ℝ in Set.Ioi A, abelDampedQuadratic ε y‖ := norm_add_le _ _
              _ ≤ (‖(∫ y in 0..A, abelDampedQuadratic ε y) -
                      ∫ y in 0..A, quadraticOscillation y‖ +
                    ‖(∫ y in 0..A, quadraticOscillation y) - positiveFresnelLimit‖) +
                    ‖∫ y : ℝ in Set.Ioi A, abelDampedQuadratic ε y‖ := by
                      gcongr
                      exact norm_add_le _ _
    _ < δ / 3 + δ / 3 + δ / 3 := by
          gcongr
    _ = δ := by ring

/-- Exact half-line value of the Abel-damped quadratic model.  This is a direct
application of Mathlib's complex Gaussian integral with `Re b > 0`. -/
theorem integral_abelDampedQuadratic_Ioi
    {ε : ℝ} (hε : 0 < ε) :
    (∫ y : ℝ in Set.Ioi 0, abelDampedQuadratic ε y) =
      ((Real.pi : ℂ) / abelGaussianParameter ε) ^ (1 / 2 : ℂ) / 2 := by
  simpa [abelDampedQuadratic] using
    (integral_gaussian_complex_Ioi (b := abelGaussianParameter ε)
      (abelGaussianParameter_re_pos hε))

/-- Closed form appearing in the Abel-damped half-line Gaussian integral. -/
def abelFresnelClosedForm (ε : ℝ) : ℂ :=
  ((Real.pi : ℂ) / abelGaussianParameter ε) ^ (1 / 2 : ℂ) / 2

/-- The limiting closed form at zero damping. -/
def fresnelBoundaryClosedForm : ℂ :=
  abelFresnelClosedForm 0

@[simp] theorem abelGaussianParameter_zero :
    abelGaussianParameter 0 = -Complex.I / 2 := by
  simp [abelGaussianParameter]
  ring

/-- The zero-damping parameter is nonzero. -/
theorem abelGaussianParameter_zero_ne :
    abelGaussianParameter 0 ≠ 0 := by
  simp [abelGaussianParameter]

/-- At zero damping, the base of the principal complex square root lies in the
slit plane (in fact it lies on the positive imaginary axis). -/
theorem pi_div_abelGaussianParameter_zero_mem_slitPlane :
    ((Real.pi : ℂ) / abelGaussianParameter 0) ∈ Complex.slitPlane := by
  right
  simp [abelGaussianParameter, Complex.div_im, Complex.normSq, Real.pi_ne_zero]

/-- The Gaussian closed form is continuous through zero damping.  This is the
branch-control step needed before taking the Abel boundary value. -/
theorem continuousAt_abelFresnelClosedForm :
    ContinuousAt abelFresnelClosedForm 0 := by
  have hparam : ContinuousAt abelGaussianParameter 0 := by
    unfold abelGaussianParameter
    fun_prop
  have hbase :
      ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) / abelGaussianParameter ε) 0 :=
    continuousAt_const.div hparam abelGaussianParameter_zero_ne
  have hpow :
      ContinuousAt
        (fun ε : ℝ =>
          ((Real.pi : ℂ) / abelGaussianParameter ε) ^ (1 / 2 : ℂ)) 0 := by
    exact hbase.cpow tendsto_const_nhds
      pi_div_abelGaussianParameter_zero_mem_slitPlane
  unfold abelFresnelClosedForm
  exact hpow.div_const 2

/-- Consequently the Abel Gaussian closed forms converge to the boundary closed
form as damping tends to zero. -/
theorem tendsto_abelFresnelClosedForm :
    Tendsto abelFresnelClosedForm (𝓝 0) (𝓝 fresnelBoundaryClosedForm) := by
  simpa [fresnelBoundaryClosedForm] using continuousAt_abelFresnelClosedForm.tendsto

/-- Identification of the genuinely convergent positive Fresnel limit with the
boundary value of the Abel-regularized Gaussian closed form.  This is obtained
by uniqueness of limits on the right-hand punctured neighborhood of zero. -/
theorem positiveFresnelLimit_eq_fresnelBoundaryClosedForm :
    positiveFresnelLimit = fresnelBoundaryClosedForm := by
  have hclosed :
      Tendsto abelFresnelClosedForm (𝓝[Set.Ioi 0] 0)
        (𝓝 fresnelBoundaryClosedForm) :=
    tendsto_abelFresnelClosedForm.mono_left inf_le_left
  have heq :
      (fun ε : ℝ => ∫ y : ℝ in Set.Ioi 0, abelDampedQuadratic ε y) =ᶠ[𝓝[Set.Ioi 0] 0]
        abelFresnelClosedForm := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [abelFresnelClosedForm] using integral_abelDampedQuadratic_Ioi hε
  have hintegralBoundary :
      Tendsto (fun ε : ℝ => ∫ y : ℝ in Set.Ioi 0, abelDampedQuadratic ε y)
        (𝓝[Set.Ioi 0] 0) (𝓝 fresnelBoundaryClosedForm) :=
    hclosed.congr' heq.symm
  exact tendsto_nhds_unique
    tendsto_integral_abelDampedQuadratic_Ioi hintegralBoundary

/-- At zero damping the Gaussian base is the positive imaginary number
`2πi`. -/
theorem pi_div_abelGaussianParameter_zero_eq_two_pi_mul_I :
    (Real.pi : ℂ) / abelGaussianParameter 0 =
      (2 * (Real.pi : ℂ)) * Complex.I := by
  apply (div_eq_iff abelGaussianParameter_zero_ne).2
  rw [abelGaussianParameter_zero]
  rw [div_eq_mul_inv]
  field_simp [Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- The branch-controlled boundary value is the standard positive Fresnel
constant `√π (1+i) / 2`. -/
theorem fresnelBoundaryClosedForm_eq_standard :
    fresnelBoundaryClosedForm =
      (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) / 2 := by
  unfold fresnelBoundaryClosedForm abelFresnelClosedForm
  rw [pi_div_abelGaussianParameter_zero_eq_two_pi_mul_I]
  rw [one_div]
  let x : ℂ := (2 * (Real.pi : ℂ)) * Complex.I
  have hxnorm : ‖x‖ = 2 * Real.pi := by
    simp [x, Real.norm_of_nonneg Real.pi_nonneg]
  have hxre : x.re = 0 := by
    simp [x]
  have hxim : x.im = 2 * Real.pi := by
    simp [x]
  have hre : (x ^ (2⁻¹ : ℂ)).re = Real.sqrt Real.pi := by
    rw [Complex.cpow_inv_two_re]
    rw [hxnorm, hxre]
    congr 1
    ring
  have him : (x ^ (2⁻¹ : ℂ)).im = Real.sqrt Real.pi := by
    rw [Complex.cpow_inv_two_im_eq_sqrt]
    · rw [hxnorm, hxre]
      congr 1
      ring
    · rw [hxim]
      positivity
  change x ^ (2⁻¹ : ℂ) / 2 =
    (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) / 2
  apply Complex.ext
  · simp [hre]
  · simp [him]

/-- Standard positive-half-line Fresnel evaluation for the quadratic phase
`exp(i y²/2)`. -/
theorem positiveFresnelLimit_eq_standard :
    positiveFresnelLimit =
      (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) / 2 := by
  rw [positiveFresnelLimit_eq_fresnelBoundaryClosedForm,
    fresnelBoundaryClosedForm_eq_standard]

@[simp] theorem quadraticOscillation_neg (y : ℝ) :
    quadraticOscillation (-y) = quadraticOscillation y := by
  unfold quadraticOscillation
  congr 1
  push_cast
  ring

/-- On a symmetric finite window, the quadratic model is exactly twice its
positive-half contribution. -/
theorem symmetricQuadraticIntegral_eq_two_mul (R : ℝ) :
    (∫ y in -R..R, quadraticOscillation y) =
      2 * (∫ y in 0..R, quadraticOscillation y) := by
  have hcomp :
      (∫ y in 0..R, quadraticOscillation (-y)) =
        ∫ y in -R..0, quadraticOscillation y := by
    simpa only [neg_zero] using
      (intervalIntegral.integral_comp_neg
        (f := quadraticOscillation) (a := 0) (b := R))
  have hneg :
      (∫ y in -R..0, quadraticOscillation y) =
        ∫ y in 0..R, quadraticOscillation y := by
    calc
      (∫ y in -R..0, quadraticOscillation y) =
          ∫ y in 0..R, quadraticOscillation (-y) := hcomp.symm
      _ = ∫ y in 0..R, quadraticOscillation y := by
        apply intervalIntegral.integral_congr
        intro y _
        simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_quadraticOscillation (-R) 0)
    (intervalIntegrable_quadraticOscillation 0 R)
  calc
    (∫ y in -R..R, quadraticOscillation y) =
        (∫ y in -R..0, quadraticOscillation y) +
          ∫ y in 0..R, quadraticOscillation y := hadd.symm
    _ = (∫ y in 0..R, quadraticOscillation y) +
          ∫ y in 0..R, quadraticOscillation y := by rw [hneg]
    _ = 2 * (∫ y in 0..R, quadraticOscillation y) := by ring

/-- Standard full symmetric Fresnel limit used by the stationary-phase main
term. -/
theorem tendsto_symmetricQuadraticIntegral :
    Tendsto (fun R : ℝ => ∫ y in -R..R, quadraticOscillation y)
      atTop (𝓝 ((Real.sqrt Real.pi : ℂ) * (1 + Complex.I))) := by
  have hmul :
      Tendsto (fun R : ℝ => (2 : ℂ) * (∫ y in 0..R, quadraticOscillation y))
        atTop (𝓝 ((2 : ℂ) * positiveFresnelLimit)) :=
    tendsto_const_nhds.mul tendsto_positiveQuadraticIntegral
  have hsym :
      Tendsto (fun R : ℝ => ∫ y in -R..R, quadraticOscillation y)
        atTop (𝓝 ((2 : ℂ) * positiveFresnelLimit)) :=
    hmul.congr' (Eventually.of_forall fun R => by
      simpa using (symmetricQuadraticIntegral_eq_two_mul R).symm)
  rw [positiveFresnelLimit_eq_standard] at hsym
  convert hsym using 1
  ring

/-- Quantitative positive-half Fresnel tail after passing the finite endpoint to
the constructed limit. -/
theorem norm_positiveQuadraticIntegral_sub_limit_le_two_div
    {R : ℝ} (hR : 0 < R) :
    ‖(∫ y in 0..R, quadraticOscillation y) - positiveFresnelLimit‖ ≤ 2 / R := by
  have ht :
      Tendsto
        (fun S : ℝ =>
          ‖(∫ y in 0..S, quadraticOscillation y) -
            ∫ y in 0..R, quadraticOscillation y‖)
        atTop
        (𝓝 ‖positiveFresnelLimit -
          ∫ y in 0..R, quadraticOscillation y‖) :=
    (tendsto_positiveQuadraticIntegral.sub tendsto_const_nhds).norm
  have hlim :
      ‖positiveFresnelLimit -
          ∫ y in 0..R, quadraticOscillation y‖ ≤ 2 / R := by
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop R] with S hRS
    exact norm_positiveTruncation_sub_le_two_div hR hRS
  simpa [norm_sub_rev] using hlim

/-- Quantitative symmetric Fresnel evaluation.  This is the finite-window error
bound directly suited to the stationary-phase main term. -/
theorem norm_symmetricQuadraticIntegral_sub_standard_le_four_div
    {R : ℝ} (hR : 0 < R) :
    ‖(∫ y in -R..R, quadraticOscillation y) -
        (Real.sqrt Real.pi : ℂ) * (1 + Complex.I)‖ ≤ 4 / R := by
  have hpos := norm_positiveQuadraticIntegral_sub_limit_le_two_div hR
  have hstd :
      (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) =
        (2 : ℂ) * positiveFresnelLimit := by
    rw [positiveFresnelLimit_eq_standard]
    ring
  rw [symmetricQuadraticIntegral_eq_two_mul, hstd]
  calc
    ‖(2 : ℂ) * (∫ y in 0..R, quadraticOscillation y) -
        (2 : ℂ) * positiveFresnelLimit‖ =
      2 * ‖(∫ y in 0..R, quadraticOscillation y) - positiveFresnelLimit‖ := by
        rw [← mul_sub, norm_mul]
        norm_num
    _ ≤ 2 * (2 / R) := mul_le_mul_of_nonneg_left hpos (by norm_num)
    _ = 4 / R := by ring

end RightEdgeArithmeticSource
end ZetaZero
