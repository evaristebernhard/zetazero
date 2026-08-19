import ZetaZero.Analytic.ZetaReflection
import ZetaZero.Analytic.ZeroCounting

/-!
# Reflection pairing of nontrivial zeta zeros

This module packages the elementary geometry of

`rho ↦ 1 - conj rho`

needed by the zero-side counting argument.  It is deliberately independent of
any contour rectangle: reflection preserves height exactly, fixes precisely the
critical line, and preserves both nontriviality and multiplicity.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace ZetaZero
namespace Analytic

@[simp] theorem reflectZetaZero_re (rho : ℂ) :
    (reflectZetaZero rho).re = 1 - rho.re := by
  simp [reflectZetaZero]

@[simp] theorem reflectZetaZero_im (rho : ℂ) :
    (reflectZetaZero rho).im = rho.im := by
  simp [reflectZetaZero]

@[simp] theorem reflectZetaZero_involutive (rho : ℂ) :
    reflectZetaZero (reflectZetaZero rho) = rho := by
  apply Complex.ext
  · simp [reflectZetaZero]
  · simp [reflectZetaZero]

/-- Reflection fixes exactly the critical line. -/
theorem reflectZetaZero_eq_self_iff (rho : ℂ) :
    reflectZetaZero rho = rho ↔ rho.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [reflectZetaZero] at hre
    linarith
  · intro hre
    apply Complex.ext
    · norm_num [reflectZetaZero, hre]
    · simp [reflectZetaZero]

/-- A zero off the critical line has a distinct reflected partner. -/
theorem reflectZetaZero_ne_self_of_re_ne_half {rho : ℂ} (h : rho.re ≠ 1 / 2) :
    reflectZetaZero rho ≠ rho := by
  exact fun heq => h ((reflectZetaZero_eq_self_iff rho).mp heq)

/-- Reflection preserves every ordinate window exactly. -/
theorem reflectZetaZero_mem_zetaZerosIn {T₁ T₂ : ℝ} {rho : ℂ}
    (hrho : rho ∈ zetaZerosIn T₁ T₂) :
    reflectZetaZero rho ∈ zetaZerosIn T₁ T₂ := by
  rcases hrho with ⟨hz, hT₁, hT₂⟩
  exact ⟨reflectZetaZero_mem hz, by simpa using hT₁, by simpa using hT₂⟩

/-- Membership in a zero window is reflection-invariant. -/
theorem reflectZetaZero_mem_zetaZerosIn_iff {T₁ T₂ : ℝ} {rho : ℂ} :
    reflectZetaZero rho ∈ zetaZerosIn T₁ T₂ ↔ rho ∈ zetaZerosIn T₁ T₂ := by
  constructor
  · intro h
    have hh := reflectZetaZero_mem_zetaZerosIn h
    simpa using hh
  · exact reflectZetaZero_mem_zetaZerosIn

/-- Reflection fixes every critical-line zero pointwise. -/
theorem reflectZetaZero_eq_self_of_mem_criticalLine {T₁ T₂ : ℝ} {rho : ℂ}
    (hrho : rho ∈ criticalLineZetaZerosIn T₁ T₂) :
    reflectZetaZero rho = rho := by
  exact (reflectZetaZero_eq_self_iff rho).2 hrho.2

/-- Off-critical-line zeros in a fixed window occur in distinct reflected pairs
with equal multiplicity. -/
theorem offCritical_reflection_pair {T₁ T₂ : ℝ} {rho : ℂ}
    (hrho : rho ∈ zetaZerosIn T₁ T₂) (hoff : rho.re ≠ 1 / 2) :
    reflectZetaZero rho ∈ zetaZerosIn T₁ T₂ ∧
      reflectZetaZero rho ≠ rho ∧
      zetaZeroMultiplicity (reflectZetaZero rho) = zetaZeroMultiplicity rho := by
  refine ⟨reflectZetaZero_mem_zetaZerosIn hrho,
    reflectZetaZero_ne_self_of_re_ne_half hoff, ?_⟩
  exact zetaZeroMultiplicity_reflect hrho.1

end Analytic
end ZetaZero
