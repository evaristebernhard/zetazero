# Small Gap Closure: Parametric HLZ Diagonal Lemma for Packet Mellin Weights

Date: 2026-09-03

## Problem

The finite-model packet argument uses the Heap--Li--Zhao scalar diagonal contour with an auxiliary factor

\[
K_{T,\mathbf z}(u)=H_{\mathbf z}(u)W(u,\mathbf z),
\]

where \(H_{\mathbf z}\) cancels the two moving zeta poles and supplies Gaussian vertical decay, while \(W\) is a compactly supported packet Mellin weight.  The original HLZ lemma is printed for a normalized auxiliary \(H(0)=1\).  The manuscript instead needs an auxiliary with

\[
K_{T,\mathbf z}(0)=W(0,\mathbf z),
\]

and with fixed polylogarithmic losses after packet derivatives.  Saying that the HLZ proof "still applies" was not sufficiently explicit because this estimate feeds the later operator remainder.

## Original HLZ input

In `external/HLZ_arxiv_2003.09368v1/hlz_original.tex`, lines 755--804, HLZ prove their diagonal lemma by:

1. writing the diagonal Euler factor;
2. truncating the Mellin integral using Gaussian decay;
3. moving the contour to \(\Re u=-1/\log_3T\) inside the classical zero-free region;
4. cancelling the two moving numerator-zeta poles with zeros of the auxiliary function;
5. taking only the residue at \(u=0\);
6. bounding the displaced contour by a factor of size \(T^{-2/\log_3T}\) times polylogarithms, with an arbitrary logarithmic truncation saving.

Their remark immediately afterwards allows an auxiliary of the form

\[
Q_{\mathbf z}(u)e^{u^2}.
\]

No later RH-dependent contour displacement is used here.

## Explicit parametric lemma now used

The working manuscript now contains Lemma `lem:parametric-HLZ-diagonal` in `sections/06_threeZ_common_prefix.tex`.

For \(h=k=1\), define the exact scalar Euler factor

\[
D_{\mathbf z}(u)
=
\frac{\zeta(1+z_1-z_2+2u)\zeta(1-z_2+z_3+2u)}
     {\zeta(1-z_2+2u)}.
\]

A fixed constant \(c_+>0\) is chosen large enough, in terms of the separated Cauchy-torus radii, that the right line

\[
\Re u=\frac{c_+}{L}
\]

lies in the absolute-convergence region of the three Euler factors uniformly in \(\mathbf z\).  This is slightly safer than writing the right line as \(1/L\), because the Cauchy shifts themselves are of size \(r_j/L\).

Let \(K_{T,\mathbf z}\) be analytic on the rectangle between \(c_+/L\) and \(-1/\log_3T\), vanish at

\[
2u=z_2-z_1,
\qquad
2u=z_2-z_3,
\]

and satisfy, for every fixed packet-parameter derivative \(\mathcal D\) required later,

\[
|\mathcal D K_{T,\mathbf z}(\sigma+iv)|
\ll
L^{C_K}(1+|v|)^{C_K}e^{-c_Kv^2}.
\]

Then

\[
K_{T,\mathbf z}(0)Z_{\mathbf z,1,1}
=
\widetilde Z_{\mathbf z,1,1}[K]
+
\mathcal E_K(\mathbf z),
\]

with

\[
\sup_{\mathbf z}|\mathcal D\mathcal E_K(\mathbf z)|
\ll
L^{C_K+C_0}T^{-2/\log_3T}\log_3T+L^{-A}
\]

for every prescribed fixed \(A>0\).

## Contour estimate

The proof is now written rather than delegated to a phrase such as "apply the HLZ proof".

Take

\[
V=B\sqrt{\log L}.
\]

On the right line the Euler product is absolutely convergent, and the Gaussian bound for \(K\) makes the tails \(|\Im u|>V\) smaller than \(L^{-A}\) once \(B\) is chosen sufficiently large.

On the truncated rectangle, the same zero-free region used by HLZ excludes zeros of the denominator \(\zeta(1-z_2+2u)\).  The only crossed poles are therefore \(u=0\) and the two numerator-zeta poles.  The latter are removed by the two prescribed zeros of \(K\), while

\[
\operatorname{Res}_{u=0}
\frac{K(u)}uD_{\mathbf z}(u)
=
K(0)Z_{\mathbf z,1,1}.
\]

Thus no division by \(K(0)\) is ever needed; the statement remains valid even when \(K(0)=0\).

On the left line,

\[
|T^{2u}|=T^{-2/\log_3T},
\]

and the zeta/inverse-zeta factors cost only a fixed power of \(L\).  The factor \(1/u\) contributes at most the usual \(\log_3T\) loss near the short part of the contour, while the Gaussian controls the vertical integral.  The two horizontal segments are \(O_A(L^{-A})\).

Consequently every fixed polylogarithmic loss is harmless because

\[
T^{-2/\log_3T}L^D\log_3T\ll_{A,D}L^{-A}
\]

for fixed \(A,D\).

## Application to packet Mellin weights

For

\[
W(u,\mathbf z)
=
\int_0^{C_*}a_{\rho,p,\mathbf z,T}(t)e^{Lut}\,dt
\]

and every fixed packet derivative, the smooth Mellin class gives only \(L^{O(1)}\) amplitude loss.  On

\[
-\frac1{\log_3T}
\le \Re u\le
\frac{c_+}{L},
\]

we have \(|e^{Lut}|\le e^{c_+C_*}\) on the right and \(|e^{Lut}|\le1\) on the left.  The explicit pole-cancelling factor

\[
H_{\mathbf z}(u)
=e^{u^2}
\frac{(2u-z_2+z_1)(2u-z_2+z_3)}
     {(z_1-z_2)(z_3-z_2)}
\]

has only a fixed polynomial \(L\)-loss on the separated torus and supplies the Gaussian decay.  Therefore \(K=H_{\mathbf z}W\) satisfies the parametric lemma uniformly.

Physical zeta-shift derivatives are still extracted afterwards by finite Cauchy residues.  The parametric lemma is differentiated only in packet variables such as \(\rho,p\), so differentiating a moving cancellation zero is never required.

## Status

This small gap is **closed in the working manuscript**.

The closure is independent of the theorem-sized packet-factorization issue: it proves that once a scalar packet slice has the required common-output form, the scalar HLZ diagonalization remains valid with the packet Mellin weight and all fixed packet derivatives used later.
