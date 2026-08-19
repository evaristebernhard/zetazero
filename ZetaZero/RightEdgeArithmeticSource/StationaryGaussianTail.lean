import ZetaZero.RightEdgeArithmeticSource.StationaryOscillationControl
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Oscillatory Gaussian tails

This module starts the genuine Fresnel-tail part of the one-chi stationary-phase
argument.  The first goal is a finite-interval integration-by-parts identity for
`exp (i y^2 / 2)` on a positive interval.  This avoids introducing an improper
Fresnel integral until convergence has been proved quantitatively.
-/

noncomputable section

open scoped Interval

namespace ZetaZero
namespace RightEdgeArithmeticSource

/-- The universal quadratic oscillatory kernel used in stationary phase. -/
def gaussianOscillatoryKernel (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((y ^ 2 / 2 : ℝ) : ℂ))

/-- Derivative of the universal quadratic oscillatory kernel. -/
theorem hasDerivAt_gaussianOscillatoryKernel (y : ℝ) :
    HasDerivAt gaussianOscillatoryKernel
      (Complex.I * (y : ℂ) * gaussianOscillatoryKernel y) y := by
  have hy : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y :=
    Complex.ofRealCLM.hasDerivAt
  have hsq : HasDerivAt (fun x : ℝ => ((x : ℂ) ^ 2)) (2 * (y : ℂ)) y := by
    convert hy.pow 2 using 1 <;> ring
  have hhalf :
      HasDerivAt (fun x : ℝ => ((x : ℂ) ^ 2) / 2) (y : ℂ) y := by
    convert hsq.div_const 2 using 1 <;> ring
  have hphase :
      HasDerivAt (fun x : ℝ => Complex.I * (((x : ℂ) ^ 2) / 2))
        (Complex.I * (y : ℂ)) y := by
    convert hhalf.const_mul Complex.I using 1 <;> ring
  simpa [gaussianOscillatoryKernel, mul_assoc] using hphase.cexp

/-- The reciprocal integration-by-parts weight `1/(i y) = -i/y`. -/
def gaussianIBPWeight (y : ℝ) : ℂ :=
  -Complex.I * ((y : ℂ)⁻¹)

/-- Derivative of the reciprocal integration-by-parts weight away from zero. -/
theorem hasDerivAt_gaussianIBPWeight {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt gaussianIBPWeight (Complex.I * ((y : ℂ)⁻¹) ^ 2) y := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y :=
    Complex.ofRealCLM.hasDerivAt
  have hinv := hcast.inv (by exact_mod_cast hy)
  simpa [gaussianIBPWeight] using hinv.const_mul (-Complex.I)

/-- Multiplying the Gaussian derivative by `1/(i y)` recovers the Gaussian
kernel exactly away from zero. -/
theorem gaussianIBPWeight_mul_deriv {y : ℝ} (hy : y ≠ 0) :
    gaussianIBPWeight y *
        (Complex.I * (y : ℂ) * gaussianOscillatoryKernel y) =
      gaussianOscillatoryKernel y := by
  unfold gaussianIBPWeight
  field_simp [by exact_mod_cast hy]
  ring

end RightEdgeArithmeticSource
end ZetaZero
