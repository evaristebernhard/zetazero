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

M01 is the first node to be formalized.  Its intended internal sequence is:

1. foundations for Hermitian forms and operators on finite-dimensional complex
   inner-product spaces;
2. restricted subspaces, finite-rank perturbations, and negative inertia
   dimension;
3. whitening by a positive-definite Gram operator;
4. the Hilbert--Schmidt threshold-dimension estimate;
5. the paper's rank-plus-relative-Hilbert--Schmidt min--max conclusion.

These are planning units, not stable global Blueprint nodes.  Their exact Lean
interfaces will be chosen only while implementing M01.
