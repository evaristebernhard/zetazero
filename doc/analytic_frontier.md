# Analytic-number-theory formalization frontier

The project-wide stabilization and density-one interface plan is maintained in
`doc/lean_formalization_plan.md`.  This frontier note records analytic theorem
content; it does not treat the external `zeta-23-lean/` root target as part of
the ZetaZero build.

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
  `Psi'(v)=log(v)` and `Psi''(v)=1/v`, together with strict convexity and
  uniqueness of the positive saddle `v=1`;
- `StationaryNormalization` proves the exact stationary main-term cancellation

  ```text
  saddle Stirling amplitude = eta^(-1/2),
  Gaussian Hessian factor   = 2*pi*sqrt(eta),
  external factor           = 1/(2*pi),
  total scalar prefactor    = 1.
  ```

  Thus the paper's absence of an extra pair-dependent Hessian weight is already
  an exact Lean identity, not a heuristic cancellation;
- `NonstationaryPhaseBounds` controls the complement of the saddle window by the
  explicit normalized margins

  ```text
  v >= 1+delta  -> |Psi'(v)| >= log(1+delta),
  0 < v <= 1-delta -> |Psi'(v)| >= -log(1-delta),
  ```

  and transfers them to the physical `Phi_eta`;
- `QuadraticOscillatoryTail` and `StationaryFresnelAbel` now give a rigorous
  oscillatory Gaussian route rather than a formal imaginary-parameter
  substitution into the positive-real-part Gaussian theorem.  In particular,

  ```text
  || integral_R^S exp(i y^2/2) dy || <= 2/R,
  integral_{-R}^R exp(i y^2/2) dy -> sqrt(pi)*(1+i),
  || integral_{-R}^R exp(i y^2/2) dy - sqrt(pi)*(1+i) || <= 4/R.
  ```

  `StationaryFresnelAbel` is included in the successful fresh all-source build;
- `StationaryOscillatoryApproximation` transfers the cubic real-phase remainder
  through the unit-circle Lipschitz estimate and proves, on `[-R,R]`,

  ```text
  || exactKernel(eta,y) - exp(i y^2/2) ||
      <= (2/3) * |y|^3 / sqrt(t_*),
  || integral_{-R}^R (exactKernel - quadraticKernel) ||
      <= (4/3) * R^4 / sqrt(t_*).
  ```

- `StationaryMainTermError.lean` now closes the finite-window main term itself.
  It proves the exact stationary kernel is Borel measurable and has norm one,
  hence is interval-integrable on every finite window, and then combines the
  previous replacement estimate with the quantitative Fresnel tail:

  ```text
  || integral_{-R}^R exactKernel(eta,y) - sqrt(pi)*(1+i) ||
    <= (4/3) * R^4 / sqrt(t_*) + 4/R.
  ```

  Moreover, under the transparent balancing condition

  ```text
  R^5 <= sqrt(t_*),
  ```

  Lean obtains the single error

  ```text
  || integral_{-R}^R exactKernel(eta,y) - sqrt(pi)*(1+i) ||
    <= 16/(3R).
  ```

  Thus finite-window integrability/linearity is no longer a hidden hypothesis.
  The extended `stationary-oscillatory` gate and fresh `lean-all` both pass.

These close the local coefficient, exact saddle geometry/normalization, Fresnel
constant, and the complete finite-window stationary main-term estimate.  The
genuinely analytic frontier is now the uniform choice/insertion of this window
inside the actual packet source, its combination with the nonstationary
complement, and the subsequent Perron/arithmetic transfer.

**Missing analytic/formalization chain**

The manuscript-level left/right reflection seam has now been repaired: the
correct scalar identity retains the conjugation at
`iota(s)=1-conj(s)`, while the complete Hardy source
`H=f+L1=Z''/Z'`, the curvature factor, the packet polarization, and the reversed
left-edge orientation combine into an exact matrix-adjoint identity.  What is
still missing on the Lean side is the corresponding sesquilinear contour
transport theorem; it should not be formalized as a scalar rewrite of
`L1(1-conj(s))`.

```text
matrix-adjoint left/right contour transport (Lean)
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

The factorial-majorant chain is now closed through the actual `P^k Q`
coefficients.  It is useful to distinguish the auxiliary Mangoldt square sum

```text
S_k(X) = sum_{1 <= n <= X} Lambda_k(n)^2
```

from the final HLP coefficient square sum.  `LambdaMeanSquareRecurrence.lean`
proves the exact finite recurrence

```text
S_{k+1}(X)
  <= log(X) * sum_{a <= X} Lambda(a) * S_k(X / a).
```

`WeightedChebyshev.lean` then specializes the vendored Abel--Mertens machinery
to the decreasing polynomial weight and keeps the decisive denominator visible:

```text
sum_{d <= exp(y)} Lambda(d)/d * (1+y-log d)^m
  <= (1 + KM*B) * (1+y)^(m+1)/(m+1)
```

whenever `m+1 <= B(1+y)`.  The support implication `S_k != 0 -> 2^k <= X` is
now connected to this hypothesis in `FactorialMajorant.lean`: at the exponential
cutoff `X=floor(exp y)`, nonvanishing implies the explicit bound

```text
2*k <= 4*(1+y).
```

Thus the manuscript's qualitative condition `m << log(ex)` is no longer an
informal uniformity clause in Lean.  `FactorialInduction.lean` uses the support
bound and the `1/(m+1)` gain to prove the level-uniform estimate

```text
lambdaMeanSquareExp (k+1) y
  <= KM * D^k/k! * exp(y) * (1+y)^(2*k+1),
D = 1 + 4*KM.
```

Finally `AlphaFactorialMajorant.lean` identifies our `P^k Q` hierarchy with the
vendored Xi-prime `lamLogConv k` coefficients and uses the already-proved
pointwise inequality

```text
alpha_{k+1}(n) <= log(n) * Lambda_{k+1}(n)
```

to obtain the actual HLP square-sum majorant

```text
sum_{n <= floor(exp y)} alpha_{k+1}(n)^2
  <= KM * D^k/k! * exp(y) * (1+y)^(2*k+3).
```

This entire chain is included in the targeted `hlp-meansquare` Lean gate.
`AlphaDerivativeIdentity.lean` now also proves the sharper manuscript identity

```text
(k+1) * alpha_{k+1}(n) = log(n) * Lambda_{k+1}(n),
```

purely from the logarithmic derivation rule for Dirichlet convolution.  Thus the
formalization now has both routes: the exact coefficient identity used in the
paper, and the shorter `lamLogConv_le` comparison sufficient for the factorial
square-sum conclusion.  The exact identity is no longer a paper-alignment gap.

The safe-line normalization layer has now also been formalized.  First,
`NaturalCutoffFactorialMajorant.lean` converts the exponential cutoff exactly to
an ordinary natural cutoff `X`.  Then `NormalizedDirectCarrier.lean` proves that
under

```text
1 + log X <= L,
```

the deterministic factor `(C/L)^(k+1)` absorbs all but one logarithmic factor:

```text
sum_{n<=X} |(C/L)^(k+1) alpha_{k+1}(n)|^2
  <= KM * D^k/(k+1)! * X * C^(2(k+1)) * (1+log X).
```

`FiniteLevelMinkowski.lean`, `FiniteCarrierAssembly.lean`, and
`DirectCarrierAssembly.lean` now assemble an arbitrary finite set `K` of HLP
levels without assuming orthogonality and then remove the dependence on `K`:

```text
sqrt(sum_n |sum_{k in K} normalized_alpha_k(n)|^2)
  <= sqrt(KM * X * (1+log X)) * tsum_k directCarrierWeight(C,k).
```

`FactorialLevelSummability.lean` proves the weight series is summable and that
multiplication by any fixed `(k+1)^q` remains summable after enlarging the
exponential parameter.  Thus fixed derivative losses in the HLP level are
already harmless before the contour deformation.

The exact finite-resolvent remainder is also quantitatively closed at the scalar
level.  `ResolventTailBound.lean` combines the exact algebraic expansion with the
strict safe-line gap: if `||P/F|| <= rho < 1`, then

```text
|| (P/F)^(K+1) * (1-P/F)^(-1) ||
  <= rho^(K+1)/(1-rho),
```

and hence

```text
|| Q/(F-P) - (Q/F) * sum_{k<=K} (P/F)^k ||
  <= ||Q/F|| * rho^(K+1)/(1-rho).
```

The same theorem is exposed directly for the completed exact source.  No
infinite geometric-series identity is used: finite algebra and the norm gap are
separate Lean lemmas.

These modules are included in both the targeted `hlp-meansquare` gate and the
latest successful fresh `lean-all`.

**Missing analytic/arithmetic chain**

```text
factorial square-sum bound for P^k Q                 [closed]
  -> safe-line normalization of each HLP level       [closed]
  -> subset-independent finite carrier assembly      [closed]
  -> scalar sqrt-factorial level summability         [closed]
  -> exact geometric resolvent truncation bound      [closed]
  -> prove the actual safe-line ratio |P/F_b| <= q<1 and derivative bounds
  -> carrier-preserving HLZ / Perron / stationary transfer.
```

Accordingly, the remaining M05 gap is no longer a formal resolvent-tail problem.
It is the manuscript's genuine analytic estimate at
`eq:cluster-geometric-ratio` (together with `HLP-zero-free-derivatives`) and its
transport through the actual packet carrier without discarding the coordinates
required later by HLZ.

## F5. HLZ bilinear and carrier-preserving lift

This remains a major analytic frontier.  The manuscript now exposes it
explicitly as `Hypothesis~\ref{hyp:packet-bilinear-HLZ}` and states the
density-one theorem conditionally on that hypothesis.  The former collision
problem in the scalar auxiliary factor has been removed separately: the HLZ
Cauchy variables are put on separated nested circles and, for fixed
$\mathbf z$, one uses
$H_{\mathbf z}(u)=e^{u^2}(2u-z_2+z_1)(2u-z_2+z_3)/((z_1-z_2)(z_3-z_2))$.
Thus the scalar HLZ step no longer asks one jointly analytic function to equal
both $0$ and $1$ at a colliding shift triple.

The remaining needed statement is not a scalar mean-value theorem: it must
retain the packet/carrier dependence through the small-moduli arithmetic
decomposition.

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
