# Small Gap Closure: Dimension-Free Scalar-to-Operator Lift of the Finite-Model HLZ Error

Date: 2026-09-03

## Problem

The scalar packet-weighted HLZ lemma gives an arbitrarily strong logarithmic error on each common output fibre.  The final matrix argument needs a relative operator/Hilbert--Schmidt estimate, not an entrywise estimate.

The dangerous implication would be

\[
|(R_T)_{rs}|\le \varepsilon_T
\quad\Longrightarrow\quad
\|R_T\|_{\rm op}\ll \varepsilon_T,
\]

which is false without paying a packet-dimension factor.

The manuscript instead uses the common-output form

\[
R_T^{\rm com}
=\mathscr C_T^*M_{\varepsilon_T}\mathscr C_T,
\qquad
\|M_{\varepsilon_T}\|_{\rm op}\le \|\varepsilon_T\|_\infty.
\]

However, there was still a missing bridge in the written proof: it normalized first by

\[
G_{\rm out}=\mathscr C_T^*\mathscr C_T
\]

and then immediately invoked the local/global comparison for \(\Gfr_T\), without explicitly proving that \(G_{\rm out}\) is compatible with the triangular reference metric.

## New compatibility lemma

The manuscript now contains Lemma `lem:HLZ-output-reference-compatibility` in `sections/11_reference_remainder.tex`.

On the stable core and on the common retained mean-zero space \(V_{\rm mean}\), the unit-multiplier common HLZ output has packet-pair overlap

\[
\rho_{rs}^{(T)}
=\nu_T-\frac{|w_r-w_s|}{L}
=\rho_{rs}^{(0)}+\delta(\tau).
\]

The deformation \(\delta(\tau)\) is independent of the packet pair.  Its quadratic form is therefore a constant-kernel term and factors through the global mean functional.  It vanishes on \(V_{\rm mean}\).

The surviving kernel is

\[
\rho_{rs}^{(0)}
=1-\frac{|w_r-w_s|}{L},
\]

which is exactly the flat triangular lag kernel.  On mean-zero inputs,

\[
\iint (1-|r-s|)q(r)\overline{q(s)}\,dr\,ds
=
2\int\left|\int_0^r q(v)\,dv\right|^2dr.
\]

This is the triangular primitive form used to define \(\Gfr_T\).  The exact stationary dilation and the common normalized one-sided factors preserve this feature factorization.  The remaining fixed archimedean, block, curvature and finite-Cauchy factors cost at most a fixed power of \(L\), independent of packet dimension.  Consequently

\[
G_{\rm out}
\preceq
L^{C_{\rm out}}\Gfr_T
\]

on every finite retained compression of \(V_{\rm mean}\).

The nonnegative height partition causes no cross-block problem: using the orthogonal direct sum with weights \(\omega_b^{1/2}\) reproduces the linear sum \(\sum_b\omega_b(\cdots)\).

## Dimension-free operator step

Because

\[
R_T^{\rm com}
=\mathscr C_T^*M_{\varepsilon_T}\mathscr C_T,
\]

we have, on the support of \(G_{\rm out}\),

\[
\left\|
G_{\rm out}^{-1/2}R_T^{\rm com}G_{\rm out}^{-1/2}
\right\|_{\rm op}
\le
\|\varepsilon_T\|_\infty.
\]

Put

\[
A=G_{\rm out}^{1/2}\Gfr_T^{-1/2}.
\]

The compatibility lemma gives

\[
\|A\|_{\rm op}^2\ll L^{C_{\rm out}}.
\]

Since the range of \(R_T^{\rm com}\) lies in the support of \(G_{\rm out}\),

\[
\Gfr_T^{-1/2}R_T^{\rm com}\Gfr_T^{-1/2}
=
A^*
\left(
G_{\rm out}^{-1/2}R_T^{\rm com}G_{\rm out}^{-1/2}
\right)
A.
\]

Thus

\[
\left\|
\Gfr_T^{-1/2}R_T^{\rm com}\Gfr_T^{-1/2}
\right\|_{\rm op}
\ll
L^{C_{\rm out}}\varepsilon_{\rm diag}.
\]

The fixed power \(L^{C_{\rm out}}\) is absorbed by choosing the arbitrary scalar HLZ exponent \(A_{\rm diag}\) larger.  Only after this operator estimate is established do we use

\[
\|B\|_{S_2}^2
\le d_T\|B\|_{\rm op}^2,
\qquad d_T=O(N_T),
\]

which gives

\[
\left\|
\Gfr_T^{-1/2}R_T^{\rm com}\Gfr_T^{-1/2}
\right\|_{S_2}^2
=o(N_T).
\]

Hence the packet dimension appears exactly once, in the final Hilbert--Schmidt conversion, and not in the scalar-to-operator lift.

## Scope

This closes the **operator-lift subgap** once the exact common-output representation is available.

It does **not** prove the theorem-sized source identity audited as A2.  If A2 fails, this lemma has no source to apply to.  If A2 is proved, there is no additional entrywise-versus-operator obstruction left at this stage.

## Verification

The manuscript compiles successfully with

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

and currently produces a 98-page PDF.
