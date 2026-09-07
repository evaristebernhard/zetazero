# Small Gap Closure: Auxiliary-Cauchy-Shift Rigidity of the Finite-Model Packet Map

Date: 2026-09-03

## Problem

The density-one proof needs the finite-model packet form to be represented through a packet analysis map that is independent of the auxiliary HLZ Cauchy variables

\[
\mathbf z=(z_1,z_2,z_3).
\]

The manuscript previously stated that the packet map \(\mathscr C_T\) is shift-independent, but the proof compressed several stages:

1. the packet polarization in the original contour form;
2. the scalar finite-model replacement \(H_{\rm mod}\);
3. the later three-face Cauchy completion;
4. the one-\(\chi\) stationary reduction;
5. the packet dilation and support transport.

The narrow question addressed here is only:

\[
\boxed{\text{Do the auxiliary Cauchy variables }\mathbf z\text{ enter the principal packet analysis map?}}
\]

No claim is made here that the packet map is independent of the physical curvature shift \(p\).

## Source chronology

The packet polarization is already fixed in the invariant contour form:

\[
\mathcal B_{e_r,e_s}(s)
=
\psi_s(z(s))\psi_r^\#(z(s)).
\]

It contains neither the physical Hardy shift nor any HLZ auxiliary Cauchy variable.

The finite-model replacement

\[
H_{\rm mod}(s;F_b)=F_b-2P(s)+P(s-2/L)
\]

is a scalar logarithmic-derivative source. Multiplication by this source cannot introduce packet-label dependence.

Only afterwards are \(z_1,z_2,z_3\) introduced by the exact scalar three-face Cauchy identity. Hence before stationary reduction all \(\mathbf z\)-dependent shifted-zeta factors, Cauchy denominators and archimedean factors are scalar with respect to packet labels.

## Stationary-phase issue

A possible hidden problem is that shifted zeta/functional-equation factors could alter the stationary phase and thereby alter the packet dilation or support.

For a fixed auxiliary shift, the shifted one-\(\chi\) kernel can instead be written exactly as

\[
A_{\mathbf z}(t,\xi)\,
\chi(1-c-it)\xi^{-c-it},
\]

where the ratios of shifted gamma factors and the Dirichlet powers such as \(n^{-z_j}\) are placed in the scalar amplitude \(A_{\mathbf z}\).

On the separated Cauchy tori

\[
|z_j|\asymp L^{-1},
\]

Stirling gives only fixed polylogarithmic derivative losses for these ratios. Thus the rapidly oscillatory phase remains the unshifted one-\(\chi\) phase from the stationary section:

\[
\Phi_\eta(t)=t\log\frac{t}{2\pi\eta}-t-\frac\pi4,
\]

with

\[
t_*=2\pi\eta.
\]

Therefore the saddle, saddle cutoff and principal Hessian normalization are independent of \(\mathbf z\).

## Exact rigidity statement

For each fixed retained physical shift \(p\), there are one-sided packet intervals \(I_r(p)\) and factors \(b_{r,T,p}\), independent of \(\mathbf z\), such that the principal finite-model packet-pair coefficient has the form

\[
\mathbf 1_{I_r(p)\cap I_s(p)}(t)
 b_{s,T,p}(t)\overline{b_{r,T,p}(t)}
 c_{T,p}(t;u,\mathbf z),
\]

where all auxiliary Cauchy dependence is contained in the common scalar factor \(c_{T,p}\).

Hence, defining

\[
(\mathscr C_{T,p}e_r)(t)
:=
\mathbf 1_{I_r(p)}(t)b_{r,T,p}(t),
\]

one has literally

\[
\boxed{
\partial_{z_j}\mathscr C_{T,p}=0,
\qquad j=1,2,3.
}
\]

This is an exact pre-HLZ statement at principal stationary level, not an asymptotic consequence of the later scalar diagonalization.

## Important scope restriction

The lemma deliberately does **not** assert

\[
\partial_p\mathscr C_{T,p}=0.
\]

The physical curvature shift may interact with the packet displacement/dilation, and proving its independence would be a stronger statement. The present small-gap closure only establishes auxiliary-Cauchy-shift rigidity.

Higher stationary corrections and nonstationary leakage are also excluded from this principal-map lemma and remain owned by the regular remainder ledger.

## Manuscript changes

`sections/06_threeZ_common_prefix.tex` now contains Lemma

`lem:aux-shift-rigidity-packet-map`

which:

- traces the source chronology from the invariant contour form;
- separates shifted gamma/Dirichlet factors into a common scalar amplitude;
- uses exact principal dilation covariance;
- proves \(\partial_{z_j}\mathscr C_{T,p}=0\);
- is then cited by the finite-model Fubini lift instead of reasserting the separation informally.

## Status

This small gap is **closed in the working manuscript**.

The manuscript compiles successfully with

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

and currently produces a 99-page PDF.

## Remaining A2 question

This closure removes only one sub-interface of the larger packet/HLZ factorization gap.

The next narrow question is whether the **scalar HLZ contour error**, not just the main residue, is represented on the same packet output channel:

\[
R_T^{\rm com}
=
\mathscr C_{T,p}^*M_{\varepsilon}\mathscr C_{T,p},
\]

with a uniform multiplier bound, rather than merely giving an entrywise error estimate.
