# Analytic-number-theory formalization frontier

This note records the difficult analytic route beyond the currently implemented
local contour/residue interfaces.  It separates exact algebra that is already
formalized from theorem-sized analytic input that is still missing.  The purpose
is to let later work proceed in parallel without turning conjectural or
paper-level estimates into hidden Lean assumptions.

## Current boundary of the formalization

The implemented chain currently reaches

```text
Hardy gauge / high rectangle
  -> symmetric-shift curvature
  -> packet polarization
  -> Cauchy cancellation
  -> exact Hardy-vs-Z1'/Z1 boundary equality
  -> local simple-zero logarithmic coefficient
  -> local stationary coefficient -H(c) H''(c)
  -> real / conjugate-pair stationary inertia blocks
```

Thus the remaining difficulty is no longer the elementary Cauchy integral or the
local residue coefficient.  It is the global analytic assembly and the
right-edge number theory.

## F1. Global rectangle zero sum and straightening

**Already formalized**

- zero-free boundary predicate and boundary integrability;
- equality of the packet-polarized Hardy and `Z1'/Z1` boundary forms;
- a wrapped weighted rectangle argument principle from the vendored `Zeta23`
  library, rebuilt against the same Mathlib revision;
- the exact global identity

```text
(1/(2*pi*i)) * boundaryIntegral(packet Z1'/Z1 source)
  = sum_{rho in Z} ord_rho(Z1) * C_Z(rho) * packet(rho);
```

  for any exact finite enumeration `Z` of the internal `Z1` zeros;
- local simple-zero coefficient of `f'/f` times an analytic amplitude;
- local stationary-kernel coefficient `-H(c)H''(c)`;
- the finite-dimensional inertia of the resulting stationary blocks.

**Straightening bridge now formalized**

`ZeroSideStationaryGeometry/StraighteningBridge` now fixes the affine coordinate
change `s = 1/2 + i z`, including the inverse coordinate identities, the exact
derivative signs `F' = i G'` and `F'' = -G''`, Schwarz reflection in zero
coordinates, and the zero/simplicity dictionaries

```text
deriv(F)(z)=0 <-> Z1(1/2+i z)=0,
(deriv(F)(z)=0 and deriv2(F)(z)!=0)
  <-> (Z1(1/2+i z)=0 and Z1'(1/2+i z)!=0).
```

At a `Z1` zero it also proves the exact weight conversion

```text
C_Z(1/2+i z) = -F(z) F''(z).
```

Thus the former straightening seam is closed.  What remains on this interface is
only the global generic-simple/multiplicity specialization and the final
stationary scalar/conjugate-pair block assembly; the residue theorem and the
affine Hardy/stationary dictionary are no longer part of the analytic gap.

## F2. Good heights and local Z1 control

**Already formalized**

- finite-window zeta-zero counting definitions and finiteness;
- reflection pairing and off-critical pairing;
- finite-set good-height avoidance combinatorics.

**Missing analytic chain**

```text
generic Jensen/Blaschke zero bound
  -> O(log T) local zeta zero count
  -> O(log T) local Z1 zero count
  -> local logarithmic-derivative factorization
  -> simultaneous horizontal zero avoidance
  -> argument-principle comparison N(Z1)-N(zeta)=polylog(T).
```

The generic zero-bound layer is a good candidate for selective extraction from
`zeta-23-lean`; the `Z1` specialization still requires the Hardy-gauge growth and
nonvanishing estimates used in the paper.

## F3. Right-edge exact source and stationary transfer

**Already formalized**

The pure source algebra is fixed in `RightEdgeArithmeticSource/SourceAlgebra`:

```text
completedExactSource F P Q = F - P + Q/(F-P),
completedModelSource F P Pshift = F - 2P + Pshift,
completedExactSource = completedModelSource + sourceDefect,
```

including exact slow-factor freezing identities and the exact separation of all
terms containing the archimedean derivative factor `f'` from the principal
source.

The right-edge track now contains several independent exact interfaces.  The
first three below have current targeted build greens; the stationary-phase
geometry/normalization layers also obtained true Lean greens before their most
recent extension, while the newly added quantitative nonstationary bounds are
awaiting a re-gate because the workspace execution channel is currently
returning 502 rather than Lean diagnostics.

- `CurvatureCoefficient` proves the exact factor-pair identity

  ```text
  sum_{ab=n} ((phi b)^2 - phi a * phi b)
    = (1/2) * sum_{ab=n} (phi a - phi b)^2,
  ```

  and hence the manuscript logarithmic coefficient `c(n) >= 0`;
- `TranslatedPoleResidue` proves that for `D=F-P` and `Q=-P'`, every simple
  zero of `D` gives simple-pole coefficient exactly `+1` for `Q/D`;
- `FreezingEstimate` upgrades the exact freezing identity to the quantitative
  bound

  ```text
  |H_ex(f)-H_ex(F)| <= |f-F| * (1 + |Q/((f-P)(F-P))|),
  ```

  together with the corresponding bound after multiplication by an arbitrary
  curvature/packet amplitude;
- `StationaryPhaseGeometry` fixes the exact one-chi phase

  ```text
  Phi_eta(t) = t log(t/(2*pi*eta)) - t - pi/4,
  t_* = 2*pi*eta,
  Phi_eta'(t_*) = 0,
  Phi_eta''(t_*) = 1/t_* != 0,
  ```

  and the exact dilation law for packet displacement.  After `t=t_* v` it
  proves the universal normalized phase `Psi(v)=v log(v)-v`, with
  `Psi'(v)=log(v)` and `Psi''(v)=1/v`; the latest extension also states strict
  convexity and uniqueness of the positive saddle `v=1` and is awaiting the
  post-extension re-gate;
- `StationaryNormalization` proves the exact stationary main-term cancellation

  ```text
  saddle Stirling amplitude = eta^(-1/2),
  Gaussian Hessian factor   = 2*pi*sqrt(eta),
  external factor           = 1/(2*pi),
  total scalar prefactor    = 1.
  ```

  Thus the paper's absence of an extra pair-dependent Hessian weight is already
  an exact Lean identity, not a heuristic cancellation;
- `NonstationaryPhaseBounds` has now been written for the complement of the
  saddle window.  It gives the explicit normalized margins

  ```text
  v >= 1+delta  -> |Psi'(v)| >= log(1+delta),
  0 < v <= 1-delta -> |Psi'(v)| >= -log(1-delta),
  ```

  and transfers the same inequalities to the physical `Phi_eta`.  This file is
  pending its first Lean gate because the execution connector failed with 502
  immediately after it was added.

These close the local coefficient, simple translated-residue coefficient,
algebra-to-norm, exact saddle geometry, and main-term normalization parts of the
right-edge transfer.  The actual oscillatory-integral asymptotic and its uniform
remainder remain genuinely analytic.

**Missing analytic chain**

```text
left/right contour reflection
  -> completed right-edge source
  -> prove blockwise bounds for f(s)-F_b and the resolvent factor
  -> one-chi stationary phase
  -> Perron transform
  -> Laurent remainder / translated-zero location
  -> carrier-preserving arithmetic kernel.
```

The translated-zero location used in the manuscript,
`u_*(F_b)=F_b^{-1}+O(F_b^{-2})`, is still genuinely analytic.  The present
Mathlib tree and the vendored `zeta-23-lean` tree contain no Rouché theorem, so
formalizing that step currently requires either building a Rouché/zero-count
lemma from argument-principle machinery or proving an equivalent local zero
existence/uniqueness statement from explicit Laurent remainder estimates.  It
must not be hidden behind the already-proved `+1` residue coefficient.

This is one of the genuinely difficult parts of the project.  The Lean strategy
should keep the spectral contour variable and the Perron variable in distinct
modules and never encode stationary phase as an algebraic rewrite.

## F4. HLP hierarchy and factorial-uniform control

**Already formalized**

- von Mangoldt convolution powers;
- support `Lambda^[k](n) != 0 -> 2^k <= n`;
- support of the actual `P^k Q` levels;
- exact recurrence `alpha_{k+2} = Lambda * alpha_{k+1}` and both
  divisor-antidiagonal coefficient forms;
- exact finite resolvent expansion

```text
1/(1-x) = sum_{k<=K} x^k + x^(K+1)/(1-x),
```

hence an exact decomposition of `Q/(F-P)` into a finite HLP hierarchy plus one
explicit tail.

The factorial-majorant chain now reaches a genuinely global finite recurrence.
Finite weighted Cauchy--Schwarz is specialized to the HLP recurrence and the
first weight factor is simplified by the exact Mathlib identity
`sum_{d|n} Lambda(d) = log n`, giving

```text
alpha_{k+2}(n)^2
  <= log(n) * sum_{ab=n} Lambda(a) * alpha_{k+1}(b)^2.
```

`MeanSquareRecurrence.lean` then sums this over `1 <= n <= X`, bounds the outer
logarithm by `log X`, and uses Mathlib's finite Dirichlet-hyperbola identity to
rearrange the divisor antidiagonals.  With

```text
S_k(X) = sum_{1 <= n <= X} alpha_{k+1}(n)^2,
```

Lean now proves the exact global recurrence

```text
S_{k+1}(X)
  <= log(X) * sum_{a <= X} Lambda(a) * S_k(X / a).
```

The same module reuses the vendored `Zeta23.FromPNTPlus.Mertens` proof of
Mertens' first theorem to obtain

```text
sum_{a <= X} Lambda(a) / a <= log(X) + log(4) + 4,
```

and packages this into a one-step propagation theorem: any linear envelope for
`S_k(Y)` on `Y <= X` yields an explicit linear-logarithmic envelope for
`S_{k+1}(X)`.

**Missing analytic/arithmetic chain**

```text
exploit the sharper k/log(n) coefficient structure
  -> choose a level-dependent majorant C_k
  -> factorial majorant uniform in k
  -> geometric/factorial control of the resolvent tail
  -> packet-uniform stationary-phase estimates.
```

Thus finite summation, divisor reindexing, the basic mean-square recurrence, and
the Mertens harmonic Mangoldt input are no longer gaps.  The remaining issue is
the genuinely level-uniform factorial induction rather than finite-sum algebra.

## F5. HLZ bilinear and carrier-preserving lift

This remains a major analytic frontier.  The needed statement is not a scalar
mean-value theorem: it must retain the packet/carrier dependence through the
small-moduli arithmetic decomposition.

The formal target should separate three outputs:

1. a positive self-energy/Gram contribution;
2. a finite-rank or separable mean-product contribution;
3. a quantitatively controlled remainder in the reference metric.

A useful intermediate module can be built once the paper-level bilinear
small-moduli formula is frozen; until then Lean should only contain generic
bilinear/Gram algebra, not a guessed HLZ statement.

## F6. Global model spectral floor

The difficult analytic content is the concrete lower frame/spectral estimate.
The finite-dimensional min--max machinery is already available in M01, and M07
now supplies the abstract positive-Gram pullback layer.  Therefore the future M06
Lean theorem should ideally expose only

```text
A_global(v) >= c0 * G(v)
```

on the intended space, with all analytic work hidden behind a proved model-floor
lemma rather than duplicated spectral algebra.

## F7. Divisor Gram and arithmetic transfer

**Already formalized**

For a finite complex analysis map `W`,

```text
gramQuadratic W v = sum_i |W v i|^2 >= 0,
gramQuadratic W v = 0 <-> W v = 0,
```

with strict positivity under injectivity and exact compatibility with
precomposition.  This is the universal algebra of `W*W`.

**Missing arithmetic content**

Construct the actual divisor/Euler analysis maps, identify the common-divisor
positive Gram, and prove the quantitative deformation from the finite arithmetic
coordinates to the reference Gram.  Any truncation parameter must be introduced
as a comparison device, not silently as a truncation of the exact source.

## F8. Frame compression, edge rank, and relative S2 remainder

The later assembly should be formalized only after the source classes are frozen.
The target decomposition is

```text
A_T = P_T + E_T + R_T,
rank(E_T) = o(N_T),
||G_T^(-1/2) R_T G_T^(-1/2)||_HS^2 = o(N_T).
```

M01, M09, and M10 already contain the abstract rank/codimension/perturbation
endgame.  What remains here is analytic ownership and quantitative summation:
stationary margins, high sidebands, terminal tails, translated poles, `f'`
classes, and the global shell sum must each enter exactly one owner.

## Parallelization rule

Safe forward formalization may proceed on exact algebra, finite combinatorics,
Gram positivity, convolution recurrences, and abstract norm/rank transfer.  It
should not pre-state any of the following as axioms or placeholder theorems:

- stationary-phase asymptotics;
- Perron/local residue formulas not yet proved in Lean;
- HLP factorial bounds;
- HLZ carrier-preserving small-moduli estimates;
- global model spectral floors;
- relative Hilbert--Schmidt remainder estimates.

Those are the actual analytic milestones whose proofs determine whether the
corresponding major node can turn green.

## Concurrent verification notes (2026-08-19)

The M02/M03 straightening file now passes the targeted front of `npm run
typecheck`; the command advances beyond `StraighteningBridge.lean`.  The next
observed global typecheck blocker is in the parallel-worker-owned
`FrameCompression/FiniteFeatureRank.lean`, where Lean currently fails to
synthesize `Module.Finite 𝕜 F` and `Module.Finite 𝕜 N.range`.  This M04 track does
not modify that file.

A separate worker is also actively extending `HLPLocalModel/MeanSquareRecurrence`
(the repository gained a dedicated `lean:hlp-meansquare` gate during this work),
so the present track intentionally avoids M05 files.

The three new M04 modules `CurvatureCoefficient`, `TranslatedPoleResidue`, and
`FreezingEstimate` each build independently.  Building the full M04 facade is
currently intercepted earlier by the pre-existing M02 dependency
`HardyGaugeInvariantContourForm/Zeta23HardyBridge.lean`, at the rewrite of
`Analytic.chiOneSub`.  That dependency bug is recorded here rather than repaired
from this parallel M04 track.  The manuscript `main.tex` is intentionally left
unchanged until these parallel edits are consolidated.
