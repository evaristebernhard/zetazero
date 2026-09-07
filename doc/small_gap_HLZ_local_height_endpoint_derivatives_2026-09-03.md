# Small Gap Closure: HLZ Local-Height Rescaling under Physical Endpoint Derivatives

Date: 2026-09-03

## Problem

The finite-model HLZ diagonal is rescaled from the fixed Mellin factor

\[
T^{2u}(mn)^{-u}
\]

to the physical local-height factor

\[
X(\tau)^{2u}(mn)^{-u},
\qquad
X(\tau)=\frac{\tau}{2\pi}.
\]

The manuscript already observed that this replacement leaves the \(u=0\) residue unchanged because the ratio multiplier

\[
R_\tau(u)
:=
\left(\frac{X(\tau)}T\right)^{2u}
\]

satisfies \(R_\tau(0)=1\).

However, later endpoint estimates use the physical total derivative

\[
D_U=\partial_U+L\tau\partial_\tau,
\qquad
\tau=2\pi e^{LU},
\]

whereas the local-height rescaling proof had only written ordinary \(\partial_\tau^j\) bounds. The gap was small, but the stated derivative closure was stronger than the displayed calculation.

## Exact calculation

Because

\[
R_\tau(u)
=
\exp\left(2u\log\frac{\tau}{2\pi T}\right),
\]

we have the exact identities

\[
(\tau\partial_\tau)^jR_\tau(u)
=(2u)^jR_\tau(u),
\]

and therefore

\[
(L\tau\partial_\tau)^jR_\tau(u)
=(2Lu)^jR_\tau(u).
\]

On the HLZ deformation strip

\[
-\frac1{\log_3T}\le\Re u\le\frac{c_+}{L},
\]

where the fixed $c_+>0$ is the same absolutely-convergent right-edge constant used in Lemma `lem:parametric-HLZ-diagonal`,

the ratio \(X(\tau)/T\) stays in a fixed compact subset of \((0,\infty)\) for \(\tau\in[T,2T]\), hence

\[
|R_\tau(u)|\ll1.
\]

The extra factors \((Lu)^j\) are only polynomial in the vertical variable and are absorbed by the Gaussian decay in the parametric HLZ lemma. They merely increase the fixed polylogarithmic exponent.

## Main-residue stability

For every \(j\ge1\),

\[
(L\tau\partial_\tau)^jR_\tau(0)=0.
\]

Thus applying physical-height derivatives to the scale multiplier does not generate any new \(u=0\) residue. The main residue remains

\[
(R_\tau H_{\mathbf z}W)(0,\mathbf z)Z_{\mathbf z,1,1}
=
W(0,\mathbf z)Z_{\mathbf z,1,1}.
\]

The \(\partial_U\) component of \(D_U\) acts on the pre-existing packet/endpoint weight and is already included in the packet derivative hypotheses. Hence the first two total endpoint derivatives preserve the same arbitrary-log HLZ error class.

## Manuscript change

Lemma `lem:HLZ-local-height-rescaling` in `sections/06_threeZ_common_prefix.tex` now explicitly states and proves stability under

\[
D_U=\partial_U+L\tau\partial_\tau
\]

through second order.

## Status

This small derivative gap is **closed in the working manuscript**.

The manuscript compiles successfully with

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

and currently produces a 98-page PDF.

## Scope

This closure only concerns the local-height scale multiplier. It does not settle the larger theorem-sized question of whether the full physical packetized source factors exactly into the common scalar HLZ output used by the finite-model principal operator.
