import ZetaZero.HardyGaugeInvariantContourForm.CurvatureAlgebra
import ZetaZero.HardyGaugeInvariantContourForm.CurvatureDerivativeBridge
import ZetaZero.HardyGaugeInvariantContourForm.GaugeDerivative
import ZetaZero.HardyGaugeInvariantContourForm.GaugeSecondDerivative
import ZetaZero.HardyGaugeInvariantContourForm.ZetaCurvature
import ZetaZero.HardyGaugeInvariantContourForm.SameFormLogDerivative
import ZetaZero.HardyGaugeInvariantContourForm.SymmetricShiftCurvature
import ZetaZero.HardyGaugeInvariantContourForm.ContourCancellation
import ZetaZero.HardyGaugeInvariantContourForm.SameFormContour
import ZetaZero.HardyGaugeInvariantContourForm.PacketPolarization
import ZetaZero.HardyGaugeInvariantContourForm.PacketSameForm
import ZetaZero.HardyGaugeInvariantContourForm.PacketBoundaryIntegrability
import ZetaZero.HardyGaugeInvariantContourForm.SimpleZeroLogResidue
import ZetaZero.HardyGaugeInvariantContourForm.PacketZeroSum
import ZetaZero.HardyGaugeInvariantContourForm.Zeta23HardyBridge

/-!
# M02: Hardy gauge and invariant contour form

Stable facade for `sec:common-matrix` and the analytic Hardy-gauge and
curvature-form construction in `main.tex`.

The analytic Hardy-gauge foundation is now implemented: the high rectangle,
holomorphic square-root branch, critical-line phase, branch reflection law, the
exact derivative identity `𝒵' = q Z₁`, the second branch derivative
`q'' = (f' + f²)q`, the analytic curvature-source factorization, the symmetric-
shift generation of curvature, entire packet polarization, the exact
packet-polarized boundary equality between the Hardy logarithmic derivative and
`Z₁'/Z₁` whenever the contour avoids `Z₁` zeros, and the weighted rectangle
argument-principle reduction of that common form to a finite multiplicity-weighted
sum over the internal `Z₁` zeros. The remaining M02/M03 seam is the
straightening/generic-simple specialization identifying these zero weights with
the stationary kernel and its block decomposition.
-/

namespace ZetaZero
namespace HardyGaugeInvariantContourForm

end HardyGaugeInvariantContourForm
end ZetaZero
