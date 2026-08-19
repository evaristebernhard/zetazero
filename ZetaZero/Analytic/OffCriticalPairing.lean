import ZetaZero.Analytic.ReflectionPairing
import ZetaZero.Analytic.ZeroFiniteness

/-!
# Fixed-point-free reflection on off-critical zeta zeros

This module packages the reflection symmetry on a bounded height window as an
actual self-equivalence of the off-critical zero set.  The construction is the
finite-set interface needed later for pair counting: reflection is involutive,
preserves the window and multiplicity, and has no fixed points off the critical
line.
-/

open Complex Set

noncomputable section

namespace ZetaZero
namespace Analytic

/-- Nontrivial zeta zeros in `(T₁,T₂]` which do not lie on the critical line. -/
def offCriticalZetaZerosIn (T₁ T₂ : ℝ) : Set ℂ :=
  zetaZerosIn T₁ T₂ \ criticalLineZetaZerosIn T₁ T₂

/-- The off-critical part of a bounded zero window is finite. -/
theorem offCriticalZetaZerosIn_finite (T₁ T₂ : ℝ) :
    (offCriticalZetaZerosIn T₁ T₂).Finite := by
  exact (zetaZerosIn_finite T₁ T₂).sdiff

/-- Reflection preserves the off-critical part of every ordinate window. -/
theorem reflectZetaZero_mem_offCriticalZetaZerosIn {T₁ T₂ : ℝ} {rho : ℂ}
    (hrho : rho ∈ offCriticalZetaZerosIn T₁ T₂) :
    reflectZetaZero rho ∈ offCriticalZetaZerosIn T₁ T₂ := by
  refine ⟨reflectZetaZero_mem_zetaZerosIn hrho.1, ?_⟩
  intro hrefCrit
  apply hrho.2
  refine ⟨hrho.1, ?_⟩
  have hrefl : (reflectZetaZero rho).re = 1 / 2 := hrefCrit.2
  simpa using (show rho.re = 1 / 2 by
    rw [reflectZetaZero_re] at hrefl
    linarith)

/-- Reflection is a self-equivalence of the off-critical zero set in a fixed
height window. -/
def reflectOffCriticalEquiv (T₁ T₂ : ℝ) :
    offCriticalZetaZerosIn T₁ T₂ ≃ offCriticalZetaZerosIn T₁ T₂ where
  toFun rho := ⟨reflectZetaZero rho.1,
    reflectZetaZero_mem_offCriticalZetaZerosIn rho.2⟩
  invFun rho := ⟨reflectZetaZero rho.1,
    reflectZetaZero_mem_offCriticalZetaZerosIn rho.2⟩
  left_inv rho := by
    apply Subtype.ext
    exact reflectZetaZero_involutive rho.1
  right_inv rho := by
    apply Subtype.ext
    exact reflectZetaZero_involutive rho.1

@[simp] theorem reflectOffCriticalEquiv_apply_val {T₁ T₂ : ℝ}
    (rho : offCriticalZetaZerosIn T₁ T₂) :
    (reflectOffCriticalEquiv T₁ T₂ rho).1 = reflectZetaZero rho.1 := rfl

/-- The reflection equivalence has no fixed point on the off-critical zero set. -/
theorem reflectOffCriticalEquiv_ne_self {T₁ T₂ : ℝ}
    (rho : offCriticalZetaZerosIn T₁ T₂) :
    reflectOffCriticalEquiv T₁ T₂ rho ≠ rho := by
  intro h
  have hval : reflectZetaZero rho.1 = rho.1 := congrArg Subtype.val h
  have hhalf : rho.1.re = 1 / 2 := (reflectZetaZero_eq_self_iff rho.1).1 hval
  exact rho.2.2 ⟨rho.2.1, hhalf⟩

/-- Multiplicity is invariant under the off-critical reflection equivalence. -/
theorem zetaZeroMultiplicity_reflectOffCriticalEquiv {T₁ T₂ : ℝ}
    (rho : offCriticalZetaZerosIn T₁ T₂) :
    zetaZeroMultiplicity (reflectOffCriticalEquiv T₁ T₂ rho).1 =
      zetaZeroMultiplicity rho.1 := by
  exact zetaZeroMultiplicity_reflect rho.2.1.1

end Analytic
end ZetaZero
