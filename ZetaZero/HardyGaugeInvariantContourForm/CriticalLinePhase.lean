import ZetaZero.Analytic.FunctionalEquationFactor
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Branch-free phase on the critical line

The critical-line phase is defined without choosing a logarithm or square-root
branch:

`e(t) = Gammaℝ(1/2+it) / ‖Gammaℝ(1/2+it)‖`.

It has unit norm and its square is exactly the manuscript factor `χ(1-s)` on
the critical line.  This gives a canonical comparison point for any
holomorphic Hardy-gauge branch constructed on the high rectangle.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

/-- Critical-line parametrization. -/
def criticalLine (t : ℝ) : ℂ := 1 / 2 + t * Complex.I

/-- The completed-zeta Gamma factor on the critical line. -/
def gammaPhaseCarrier (t : ℝ) : ℂ := Gammaℝ (criticalLine t)

/-- Branch-free Hardy phase. -/
def criticalPhase (t : ℝ) : ℂ :=
  gammaPhaseCarrier t / (‖gammaPhaseCarrier t‖ : ℂ)

@[simp] theorem criticalLine_re (t : ℝ) : (criticalLine t).re = 1 / 2 := by
  simp [criticalLine]

@[simp] theorem criticalLine_im (t : ℝ) : (criticalLine t).im = t := by
  simp [criticalLine]

/-- Reflection fixes the critical line pointwise in the `s ↦ 1-conj s` sense. -/
theorem one_sub_conj_criticalLine (t : ℝ) :
    1 - conj (criticalLine t) = criticalLine t := by
  apply Complex.ext <;> norm_num [criticalLine]

/-- `Gammaℝ` is nonzero on the critical line. -/
theorem gammaPhaseCarrier_ne_zero (t : ℝ) : gammaPhaseCarrier t ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos (by simp [criticalLine])

/-- The branch-free phase has unit norm. -/
theorem norm_criticalPhase (t : ℝ) : ‖criticalPhase t‖ = 1 := by
  rw [criticalPhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (norm_pos_iff.mpr (gammaPhaseCarrier_ne_zero t)),
    div_self (norm_pos_iff.mpr (gammaPhaseCarrier_ne_zero t)).ne']

/-- The phase is a unit: `conj e * e = 1`. -/
theorem conj_criticalPhase_mul (t : ℝ) :
    conj (criticalPhase t) * criticalPhase t = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    norm_criticalPhase]
  norm_num

/-- On the critical line, the classical factor is `conj Gammaℝ / Gammaℝ`. -/
theorem chiFE_criticalLine (t : ℝ) :
    Analytic.chiFE (criticalLine t) =
      conj (gammaPhaseCarrier t) / gammaPhaseCarrier t := by
  rw [Analytic.chiFE, gammaPhaseCarrier]
  have hsub : 1 - criticalLine t = conj (criticalLine t) := by
    apply Complex.ext <;> norm_num [criticalLine]
  rw [hsub, Analytic.Gammaℝ_conj]

/-- The branch-free phase squares to the Hardy-gauge factor `χ(1-s)`. -/
theorem criticalPhase_sq (t : ℝ) :
    criticalPhase t ^ 2 = Analytic.chiOneSub (criticalLine t) := by
  have hG := gammaPhaseCarrier_ne_zero t
  have hconjG : conj (gammaPhaseCarrier t) ≠ 0 := by simp [hG]
  have hn : ((‖gammaPhaseCarrier t‖ : ℂ)) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hG).ne'
  have hnormsq : ((‖gammaPhaseCarrier t‖ : ℂ)) ^ 2 =
      conj (gammaPhaseCarrier t) * gammaPhaseCarrier t := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hsubGamma : Gammaℝ (1 - criticalLine t) = conj (gammaPhaseCarrier t) := by
    rw [gammaPhaseCarrier]
    have hsub : 1 - criticalLine t = conj (criticalLine t) := by
      apply Complex.ext <;> norm_num [criticalLine]
    rw [hsub, Analytic.Gammaℝ_conj]
  rw [criticalPhase, Analytic.chiOneSub, hsubGamma, div_pow]
  rw [gammaPhaseCarrier] at hG hconjG hn hnormsq ⊢
  field_simp [hG, hconjG, hn]
  rw [hnormsq]
  ring

/-- Any square root of the Hardy factor at a critical-line point differs from
`criticalPhase` by at most a sign. -/
theorem eq_or_eq_neg_criticalPhase {q : ℂ → ℂ} (hq : ∀ z, q z ^ 2 = Analytic.chiOneSub z)
    (t : ℝ) :
    q (criticalLine t) = criticalPhase t ∨
      q (criticalLine t) = -criticalPhase t := by
  have hsq : q (criticalLine t) * q (criticalLine t) =
      criticalPhase t * criticalPhase t := by
    calc
      q (criticalLine t) * q (criticalLine t) = q (criticalLine t) ^ 2 := by ring
      _ = Analytic.chiOneSub (criticalLine t) := hq (criticalLine t)
      _ = criticalPhase t ^ 2 := (criticalPhase_sq t).symm
      _ = criticalPhase t * criticalPhase t := by ring
  exact mul_self_eq_mul_self_iff.mp hsq

/-- At a critical-line point, every square-root branch is unitary. -/
theorem conj_branch_eq_inv_on_criticalLine {q : ℂ → ℂ}
    (hq : ∀ z, q z ^ 2 = Analytic.chiOneSub z) (t : ℝ) :
    conj (q (criticalLine t)) = (q (criticalLine t))⁻¹ := by
  rcases eq_or_eq_neg_criticalPhase hq t with h | h
  · rw [h]
    apply (mul_eq_one_iff_eq_inv₀ (by
      exact div_ne_zero (gammaPhaseCarrier_ne_zero t)
        (by exact_mod_cast (norm_pos_iff.mpr (gammaPhaseCarrier_ne_zero t)).ne'))).1
    simpa [mul_comm] using conj_criticalPhase_mul t
  · rw [h, map_neg, inv_neg]
    congr 1
    apply (mul_eq_one_iff_eq_inv₀ (by
      exact div_ne_zero (gammaPhaseCarrier_ne_zero t)
        (by exact_mod_cast (norm_pos_iff.mpr (gammaPhaseCarrier_ne_zero t)).ne'))).1
    simpa [mul_comm] using conj_criticalPhase_mul t

end HardyGaugeInvariantContourForm
end ZetaZero
