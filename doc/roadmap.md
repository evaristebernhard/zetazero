# Formalization roadmap

The major-node IDs and facade module paths below are stable.  Internal lemmas
and submodules may be split, merged, or renamed as the formalization exposes
the right abstractions, but public imports must continue to work.

| ID | Major node | Stable facade | Paper location | Dependencies |
|---|---|---|---|---|
| M01 | Finite-dimensional inertia reduction | `ZetaZero.FiniteDimensionalInertiaReduction` | `sections/13_minmax.tex` | none |
| M02 | Hardy gauge and invariant contour form | `ZetaZero.HardyGaugeInvariantContourForm` | `main.tex`, `sec:common-matrix` | none |
| M03 | Zero-side stationary geometry and packet evaluation | `ZetaZero.ZeroSideStationaryGeometry` | `main.tex`, `sec:zero-side` | M02 |
| M04 | Right-edge arithmetic source and dilation covariance | `ZetaZero.RightEdgeArithmeticSource` | `main.tex`, `sec:right-edge`, `sec:stationary` | M02 |
| M05 | HLP/HLZ local model and principal operator | `ZetaZero.HLPLocalModel` | `main.tex`, `sec:threeZ`, `sec:hlp-local`, `sec:local-projector` | M04 |
| M06 | Global model and spectral floor | `ZetaZero.GlobalModelSpectralFloor` | `main.tex`, `sec:model-floor` | M05 |
| M07 | Divisor Gram and arithmetic transfer | `ZetaZero.DivisorGramArithmeticTransfer` | `main.tex`, `sec:divisor-gram` | M05 |
| M08 | Frame compression, edge rank, and regular remainder | `ZetaZero.FrameCompression` | `main.tex`, `sec:shell-frame`, `sec:edge-rank`, `sec:ledger` | M03, M06, M07 |
| M09 | Retained space and parameter hierarchy | `ZetaZero.RetainedSpace` | `sections/12_retained_space.tex`, `sec:retained` | M08 |
| M10 | Generic perturbation, min--max, and density-one endgame | `ZetaZero.GenericPerturbationMinMaxEndgame` | `sections/00_main_theorem.tex`, `sec:minmax`, `sec:multiplicity-endgame` | M01, M03, M09 |

The dependency DAG is therefore:

```text
M01 ---------------------------------------------> M10
M02 -> M03 --------------------------------------> M10
  `-> M04 -> M05 -> M06 --.
                  `-> M07 ---+-> M08 -> M09 -----> M10
M03 -------------------------'
```

## First green route: M01

`ZetaZero.FiniteDimensionalInertiaReduction` remains the stable public facade.
Its internal implementation is split by mathematical responsibility rather than
by paragraph boundaries in the paper:

```text
Basic
  -> SubspaceBudget
  -> FiniteRankPerturbation
  -> NegativeIndex
  -> RealNegativeIndex
  -> RankPlusGoodSpace
  -> SpectralThresholdCount
  -> CoordinateGoodSpace
  -> DiagonalRemainder
  -> HermitianThreshold
  -> HilbertSchmidtBridge
  -> SpectralGoodSpace
  -> MinMaxAssembly
  -> CongruenceTransport
  -> WhitenedMinMax
```

The M01 chain now covers codimension bookkeeping, removal of a finite-rank
perturbation, natural-number and real-valued negative-index bounds, Hermitian
threshold counting, the exact Hilbert--Schmidt identity

```text
#bad * tau^2 <= ||R||_HS^2,
```

construction of the explicit spectral good space, the diagonal remainder lower
bound there, rank-plus-Hilbert--Schmidt min--max assembly, and transport back to
physical coordinates through an invertible linear equivalence.  At
`tau = c0 / 4` the formal theorem carries the manuscript's exact factor
`16 * c0^-2` and the `3 * c0 / 4` lower bound on the explicit good space.

The public facade ends in `WhitenedMinMax`.  M01 takes the whitening equivalence
and the corresponding coordinate identities as interface data; constructing
that equivalence from the concrete positive reference Gram belongs to the later
reference-metric integration, not to the finite-dimensional min--max core.

These internal modules are not stable Blueprint nodes and may be refined while
the public facade remains unchanged.

## Analytic route: M02 to M03

The analytic number-theory layer is being developed as reusable infrastructure
rather than as one monolithic translation of the paper.  The current shared
chain is:

```text
Analytic/ZeroCounting
  -> CompletedZeta
  -> FunctionalEquationFactor
  -> ZetaReflection
  -> ZeroFiniteness
  -> ReflectionPairing
  -> GoodHeightCombinatorics
```

For M02 the implemented Hardy-gauge and contour chain is now:

```text
FunctionalEquationFactor
  -> HolomorphicSquareRoot
  -> HighRectangle
  -> CriticalLinePhase
  -> BranchReflection
  -> GaugeDerivative / GaugeSecondDerivative
  -> CurvatureAlgebra / ZetaCurvature
  -> SymmetricShiftCurvature
  -> PacketPolarization
  -> PacketPolarization reflection/adjoint swap
  -> ContourCancellation
  -> SameFormContour
  -> PacketSameForm
  -> PacketBoundaryIntegrability
  -> SimpleZeroLogResidue
```

Thus the holomorphic branch `q^2 = chiOneSub`, reflection, `𝒵' = q Z₁`, the
second derivative bridge, exact curvature source, symmetric-shift generation,
and the packet-polarized same-form boundary identity are formalized on the high
rectangle.  The vendored weighted argument principle assembles the internal
residues into a finite multiplicity-weighted `Z₁` zero sum.  The normalization
bridge to Zeta23 is also verified off the real axis (`hardyF = L₂`, hence
`Z₁ = hardyW`), so derivative and analytic-order transport are available.  The
remaining M02 responsibility is to specialize the global zero-sum weights to the
stationary packet kernel and complete the good-height/log-derivative estimates.

For M03, two independent strands are now visible.  The zero-count/good-height
strand still requires local control of both `zeta` and `Z1`, while the stationary
strand has already advanced through its local residue and finite-dimensional
inertia algebra:

```text
zero-count strand:
generic Blaschke/Jensen zero bound
  -> local zeta and Z1 zero counts
  -> local logarithmic-derivative factorization
  -> simultaneous zero-avoidance height
  -> Z1/zeta argument-principle decrement

stationary strand:
simple stationary zero
  -> local coefficient  -H(c) H''(c)
  -> real / conjugate-pair residue blocks
  -> pair-block NegativeIndexLE <= 1 + explicit negative direction
  -> zero-coordinate straightening / Schwarz reflection
  -> Z₁ simple-zero <-> straightened simple stationary point
  -> finite evaluation pullback negative-index upper bound
  -> global packet-weight specialization
  -> packet-evaluation surjectivity
```

The local clone `zeta-23-lean/` is exposed by `lakefile.toml` as a second source
library `Zeta23` and is rebuilt against this project's Lean/Mathlib 4.32.1, so
reuse does not depend on the clone's original 4.33.0-rc2 toolchain.  Small stable
interfaces may either be ported into `ZetaZero` or wrapped directly when the
vendored implementation is already mature.  The weighted rectangle argument
principle is now reused in this way through
`ZetaZero.Analytic.RectangleArgumentPrinciple`, yielding the global finite zero
sum in `PacketZeroSum`.  The generic Blaschke/Jensen `ZerosBound` machinery
remains the next major candidate for reuse on the good-height strand.

## Parallel algebraic layers: M05 to M08

Several later nodes now have verified algebraic cores even though their analytic
inputs are not yet complete:

```text
M05:
ArithmeticHierarchy / ConvolutionRecurrence / WeightedCauchy
  -> MeanSquareRecurrence
  -> FiniteResolventExpansion
  -> LeadingJetResummation

M07:
PositiveGram / OperatorGramLift
  -> GcdGramIdentity
  -> OperatorGcdGramLift

M08:
FiniteFeatureRank
  -> TranslatedPoleFeatureRank / FixedEdgeRange
```

The current targeted gates `hlp-meansquare`, `previous-unverified`, and the
extended `gcd-gram` all pass.  In particular, the finite-feature rank theorem
now carries the required finite-dimensional hypotheses explicitly, the leading
translated-pole resolvent identity is verified by exact field algebra, and the
concrete gcd kernel has a totient-weighted Hilbert/operator Gram decomposition.

The implementation-facing stabilization and density-one interface plan is
recorded in `doc/lean_formalization_plan.md`.  The external `Zeta23` tree is a
reference dependency only: project gates build selected imported modules, not
the external `Zeta23` root library.

M06 has also started with the verified abstract interface in
`PrimitiveSchurFloor.lean`; it records the cusp-minus-Schur mechanism and the
`0.06` to `0.03` relative-error transfer, not the concrete analytic estimates.
Likewise, these algebraic foundations do not by themselves make any later node
green.

M10 now also exports a proved `density_one_critical_line` normalization
interface.  Its off-critical little-o estimate remains an explicit input from
the future zero-side/source-ledger certificate; the declaration does not make
the overall density-one theorem green.
