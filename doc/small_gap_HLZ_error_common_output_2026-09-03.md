# Small Gap Closure: Common-Output Lift of the Scalar HLZ Contour Error

Date: 2026-09-03

## Problem

The density-one proof needs more than an entrywise scalar HLZ error estimate. If one only knew

\[
|(R_T)_{rs}|\le \varepsilon_T,
\]

then converting this to an operator or Hilbert--Schmidt estimate could lose a factor proportional to the packet dimension.

The desired form is instead

\[
R_T^{\rm com}
=\mathscr C^*M_{\varepsilon}\mathscr C,
\]

with

\[
\|M_{\varepsilon}\|_{\rm op}\ll \varepsilon_T.
\]

The narrow question addressed here is whether the **scalar HLZ contour error itself**, before any physical-curvature differentiation that may alter the packet map, lives on the same packet output channel as the scalar main term.

## Input

For a fixed retained physical shift \(p\), the auxiliary-shift rigidity lemma gives the exact pre-HLZ factorization

\[
W_{rs,L}(u,\mathbf z)
=
\int
(\mathscr C_{T,p}e_s)(t)
\overline{(\mathscr C_{T,p}e_r)(t)}
F_{T,p,t}(u,\mathbf z)\,dt,
\]

where \(\mathscr C_{T,p}\) is independent of the auxiliary Cauchy variables \(\mathbf z\).

For every fixed fibre coordinate \(t\), the scalar slice \(H_{\mathbf z}F_{T,p,t}\) satisfies the parametric HLZ diagonal lemma uniformly in \(t\).

## Error as a linear functional

In the proof of the parametric HLZ diagonal lemma, the error is not merely an unnamed big-\(O\) term. It is explicitly the sum of:

- the displaced left-edge integral;
- the two horizontal connector integrals;
- the Gaussian truncation tails.

For fixed \(\mathbf z\), denote this scalar functional by

\[
\mathfrak E_{T,\mathbf z}[F].
\]

Every component is linear in the auxiliary analytic weight \(F\).

The Gaussian truncation gives absolute convergence on the finite contour pieces and uniform domination of the tails. Therefore Fubini is legitimate for the slice family.

Hence

\[
\mathcal E_{rs}(p,\mathbf z)
=
\int
(\mathscr C_{T,p}e_s)(t)
\overline{(\mathscr C_{T,p}e_r)(t)}
\varepsilon_{p,\mathbf z}(t)\,dt,
\]

where

\[
\varepsilon_{p,\mathbf z}(t)
:=
\mathfrak E_{T,\mathbf z}
[H_{\mathbf z}F_{T,p,t}].
\]

Thus

\[
\boxed{
\mathcal E(p,\mathbf z)
=
\mathscr C_{T,p}^*
M_{\varepsilon,p,\mathbf z}
\mathscr C_{T,p}.
}
\]

This identity is exact at the scalar-HLZ-error stage.

## Uniform multiplier bound

The parametric HLZ lemma gives uniformly in \(t\) and \(\mathbf z\)

\[
|\varepsilon_{p,\mathbf z}(t)|
\ll
L^C T^{-2/\log_3T}\log_3T+L^{-A'}.
\]

Because

\[
T^{-2/\log_3T}L^D\log_3T\ll_{A,D}L^{-A}
\]

for every fixed \(A,D\), and because the arbitrary scalar exponent \(A'\) can be chosen after all fixed packet/Cauchy losses, one gets

\[
\boxed{
\|M_{\varepsilon,p,\mathbf z}\|_{\rm op}
=
\|\varepsilon_{p,\mathbf z}\|_{L^\infty}
\ll_A L^{-A+C}.
}
\]

## Finite auxiliary-Cauchy residues

Since

\[
\partial_{z_j}\mathscr C_{T,p}=0,
\]

all finite Cauchy extraction in \(\mathbf z\) acts only on the scalar multiplier. Thus after the three-face residue extraction the error is still a pullback through the same \(\mathscr C_{T,p}\).

The separated circles contribute only fixed powers of \(L\), which are absorbed by requesting a stronger arbitrary logarithmic saving in the scalar lemma.

Therefore no factor involving the packet dimension \(|\mathcal I_T|\) is introduced.

## Manuscript change

`sections/06_threeZ_common_prefix.tex` now contains Lemma

`lem:HLZ-error-common-output`

which states and proves this common-output representation explicitly.

## Status

The **entrywise-versus-operator gap at the scalar HLZ / auxiliary-Cauchy stage is closed** in the working manuscript.

The manuscript compiles successfully with

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

and currently produces a 100-page PDF.

## Remaining scope

This does not by itself prove that the final curvature-differentiated error uses one physical-shift-independent packet map. The present lemma is for each fixed physical shift \(p\):

\[
\mathscr C_{T,p}.
\]

If differentiating in the physical curvature shift produces

\[
\partial_p\mathscr C_{T,p}\ne0,
\]

additional packet-map jet terms may appear. That issue remains part of the larger A2 physical-shift compatibility gap and should not be hidden inside the now-closed auxiliary-Cauchy/operator step.
