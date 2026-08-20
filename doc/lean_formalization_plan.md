# Lean formalization plan

This document is the implementation-facing plan for the ZetaZero Lean
formalization.  It is deliberately separate from the manuscript route: the
paper may describe the intended analytic argument, while this file records
which interfaces are checked in Lean, which are only abstract contracts, and
what must happen before a major node is green.

## 1. Scope and verification baseline

`ZetaZero/` is the project being formalized.  `zeta-23-lean/` is an external
reference development whose selected declarations are reused through imports;
its headline theorem and its full source tree are not project targets.  In
particular, the routine project gates must not run `lake build Zeta23`.

Only the smallest required external targets should be built, for example:

```text
lake build Zeta23.XiPrime.Hardy.Basic
```

The current project baseline is:

```text
python3 scripts/check_lean_placeholders.py   PASS
lake build                                    PASS
npm test -- lean-all                          PASS
npm test -- blueprint-decls                   PASS
```

The Blueprint gate now loads only the selected external Zeta23 roots imported
by `ZetaZero`; it no longer requires the external `Zeta23.olean` headline
object.  This keeps the reference project out of the ZetaZero build target
while preserving declaration checking for the reused modules.

The source policy remains strict: no `sorry`, `admit`, project-defined
`axiom`, empty theorem shell, or unproved analytic assertion hidden in an
interface.

## 2. Density-one theorem interface (M10)

The project must expose a paper-facing target even before all analytic inputs
are available.  The first M10 interface is therefore split into two layers.

### 2.1 Checked final normalization

`ZetaZero.GenericPerturbationMinMaxEndgame.DensityOne` defines:

```text
DensityOne N N₀ :=
  Tendsto (fun T => N₀ T / N T) atTop (𝓝 1)
```

and proves `densityOne_of_relativeCountGap_isLittleO`: if the total count tends
to infinity, the critical-line count is pointwise at most the total count, and
the relative gap `N - N₀` is `o(N)`, then the ratio tends to one.

The concrete paper-facing aliases use `dyadicN` and `dyadicN0` from the
analytic counting layer.  The exported theorem
`density_one_critical_line` is a proved normalization theorem with the
remaining off-critical gap estimate as an explicit input.

This is an honest acceptance interface, not a claim that the missing M02--M09
analytic estimates have already been proved.  The future analytic work must
construct the gap estimate from the zero-side/inertia certificate and the
source ledger.

### 2.2 Future endgame certificate

The next M10 layer should package the actual certificate that produces the
little-o gap.  Its fields must remain mathematical, not implementation-shaped:

1. total dyadic zero count tends to infinity;
2. generic perturbation preserves the relevant zero counts and simplicity
   dictionary;
3. zero-side off-axis multiplicity is bounded by the negative inertia of the
   perturbed contour form, up to the stated count error;
4. M01/M09 provide `o(N_T)` bounds for retained-space codimension, edge rank,
   and relative Hilbert--Schmidt remainder;
5. the zero-count comparison converts those bounds into an `o(N_T)`
   off-critical gap.

No field may simply restate the desired density-one conclusion under another
name.  Each field must correspond to a future theorem chain and have a named
owner in M02--M09.

## 3. Stable layers and remaining analytic frontier

### Stable or nearly stable Lean interfaces

* **M01:** finite-dimensional codimension, spectral good space, Hilbert--Schmidt
  budget, and physical-coordinate rank-plus-Hilbert--Schmidt min--max.
* **M02:** Hardy gauge, square-root branch, curvature identities, packet
  polarization, same-form contour cancellation, weighted `Z₁` zero sum, and
  the selected Zeta23 normalization bridge.
* **M03:** reflection/counting infrastructure, stationary residue blocks, and
  the affine straightening dictionary.  `StraighteningBridge` is now a public
  facade import; good-height and Jensen estimates remain inputs rather than a
  completed global chain.
* **M04:** exact right-edge source algebra, finite-model Fubini lift, stationary
  geometry and normalization, Fresnel/Abel tail, and the quantitative finite
  window main-term error.
* **M05:** Mangoldt hierarchy, factorial square-sum/direct-carrier bounds,
  finite resolvent expansion, and scalar resolvent-tail/Laurent interfaces.
* **M06--M07:** abstract Schur-floor and positive-Gram/gcd interfaces are
  reusable foundations, not concrete global spectral or arithmetic transfer
  theorems.

### Remaining theorem-sized analytic work

1. simultaneous good heights and local `Z₁` logarithmic-derivative control;
2. global specialization of the M02 zero sum to stationary packet weights;
3. packet evaluation surjectivity and matrix-adjoint contour transport;
4. safe-line ratio and derivative estimates for the actual source;
5. Perron/Laurent/translated-zero transfer without hiding a Rouché step;
6. concrete global model spectral floor and divisor-Gram deformation;
7. stationary-shell frame, retained-space rank budgets, and relative `S₂`
   remainder;
8. construction of the M10 endgame certificate and the density-one gap.

The coefficient-free fixed-edge range interface now has the stable M08
destination `ZetaZero.FrameCompression.FixedEdgeRange`; no parallel duplicate
API is retained.  Generic Jensen and good-height lemmas may compile under
`lean-all` without being advertised as a green M03 chain.

## 4. Integration and commit tranches

Commit vertically by theorem chain:

```text
feat(M03): integrate straightening bridge
feat(M05): stabilize resolvent and Laurent interfaces
feat(M06-M07): integrate abstract floor and Gram foundations
feat(M10): add density-one endgame interface
docs(formalization): add Lean progress and stabilization plan
chore(blueprint): repair project declaration gate
```

Generated files, `node_modules/`, package-lock changes unrelated to the Lean
gate, `.lake/`, `.ai-bridge/`, and the Route-B archive are not staged.
Manuscript-route edits remain a separate documentation commit and do not enter
Lean theorem commits.

After every two to four focused commits, run the project-only integration
tranche:

```text
lake build
npm test -- lean-all
python3 scripts/check_lean_placeholders.py
```

Each node also needs its directed gate and, before green status, the Blueprint
declaration check plus the complete Blueprint PDF/web/dependency build.

## 5. Green criteria and status discipline

A node is green only when its prerequisites are green, its facade and all
required source modules build with warnings as errors, its Blueprint links
resolve, both statement and proof carry `\\leanok`, and the full Blueprint
build succeeds.

Until then use `planned`, `in progress`, `abstract foundation`, or
`Lean-complete; Blueprint-pending`.  In particular, the new M10 density-one
interface is a checked theorem contract, not evidence that the analytic
density-one theorem is complete.
