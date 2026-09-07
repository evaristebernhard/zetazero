# Independent HLZ Face Audit of the Frozen Principal Profile

Date: 2026-09-03

## Goal

The density-one audit treated the profile

\[
\mathscr G_{\lambda,\mu,\rho}(p)
=
e^{\lambda p}
\left[
\mu E_\rho(2p)
-2E_\rho(p)^2
+e^{2\lambda}E_\rho(p+2)E_\rho(p-2)
\right]
\]

as the highest-risk unresolved interface, because every later spectral floor depends on every sign and factor in this formula.

This note recomputes the three terms independently from the original Heap--Li--Zhao local factors and the exact Hardy-gauge shift identity.  It does not use the manuscript's already-written profile as an input.

## 1. Physical Hardy shift and the universal \(e^{\lambda p}\)

Let

\[
a=\frac pL,
\qquad
X=\frac{\tau}{2\pi}=e^{\lambda L}.
\]

The Hardy-gauge product is

\[
\mathscr Z(s+a)\mathscr Z(s-a)
=q(s+a)q(s-a)\zeta(s+a)\zeta(s-a),
\qquad q(s)^2=\chi(1-s).
\]

Using

\[
\zeta(s-a)=\chi(s-a)\zeta(1-s+a)
\]

and

\[
\chi(s-a)=\chi(1-s+a)^{-1}=q(s-a)^{-2},
\]

we obtain the exact identity

\[
\boxed{
\mathscr Z(s+a)\mathscr Z(s-a)
=
\frac{q(s+a)}{q(s-a)}
\zeta(s+a)\zeta(1-s+a).
}
\]

Thus the two HLZ physical shifts are

\[
\alpha=\beta=a.
\]

Since \(q'/q=f\) and, on the retained high block,

\[
2f(s)=\log X+O(T^{-1}),
\]

the principal part of the gauge ratio is

\[
\frac{q(s+a)}{q(s-a)}
=X^a(1+\text{regular error})
=e^{\lambda p}(1+\text{regular error}).
\]

This is the common \(e^{\lambda p}\) factor multiplying every principal face.  It is an archimedean height factor, not a packet endpoint factor.

## 2. Self face: \(\mu E_\rho(2p)\)

For the self/J contribution, the original HLZ pole bracket at \(h=k=1\) is

\[
\zeta(1+\alpha+\beta)
+X^{-\alpha-\beta}\zeta(1-\alpha-\beta).
\]

With \(\alpha=\beta=a\), its principal pole part is

\[
\frac1{2a}-\frac{X^{-2a}}{2a}.
\]

Multiplying the common Hardy factor gives

\[
X^a\left(\frac1{2a}-\frac{X^{-2a}}{2a}\right)
=
L e^{\lambda p}E_\lambda(2p).
\]

The complete Hermitian self source is \(2F_b\).  The local principal normalization contains the common positive \(L^2\) factor, hence

\[
\frac{2F_b}{L^2}
\left[L e^{\lambda p}E_\lambda(2p)\right]
=
\frac{2F_b}{L}e^{\lambda p}E_\lambda(2p).
\]

Therefore

\[
\boxed{
\mu_b=\frac{2F_b}{L}
}
\]

and the full-fibre self term is

\[
\boxed{
\mu_b e^{\lambda p}E_\lambda(2p).
}
\]

The argument \(2p\) is also independently confirmed by the exact shifted-product AFE, where the sharp diagonal fibre depends only on

\[
A+B=L(\alpha+\beta)=2p.
\]

## 3. One unshifted \(P\)-source: the missing \(1/2\) check

For \(h=k=1\), the principal pole part of the original HLZ factor is

\[
Z^{\rm pole}_{A,B,C}
=
\frac{B}{(A+B)(B+C)}.
\]

Set \(A=B=a\).  The three completed faces give

\[
F_a(\gamma)
=
\frac1{2(a+\gamma)}
-
\frac{X^{-2a}}{2(a-\gamma)}
+
X^{-a-\gamma}\frac{\gamma}{a^2-\gamma^2}.
\]

Our convention is

\[
P=-\frac{\zeta'}\zeta,
\]

so the logarithmic-derivative insertion is \(-\partial_\gamma\).  Direct differentiation gives

\[
\boxed{
-\partial_\gamma F_a(0)
=
\frac{(1-X^{-a})^2}{2a^2}
=
\frac{L^2}{2}E_\lambda(p)^2.
}
\]

This \(1/2\) is the contribution of **one** right-edge orientation.  The adjoint orientation gives the same real principal scalar.  Hence after Hermitian reassembly and division by the common \(L^2\) normalization, one unit \(P\)-source contributes

\[
\boxed{
e^{\lambda p}E_\lambda(p)^2.
}
\]

This is the factor that was most vulnerable to a hidden factor-of-two mistake.  The computation shows explicitly that the \(1/2\) from one HLZ orientation is exactly cancelled by the two Hermitian orientations, and nowhere else.

Since the finite model contains \(-2P\), the unshifted logarithmic contribution is therefore

\[
\boxed{
-2e^{\lambda p}E_\lambda(p)^2.
}
\]

## 4. Translated source \(P(s-2/L)\)

Put

\[
\delta=\frac2L.
\]

The exact translated HLZ diagonal coefficient carries

\[
X^\delta(n_2n_3)^{-\delta}.
\]

For the unshifted logarithmic face, before the second leg is reflected into the common positive coordinate, the two one-sided factors are

\[
n_2^{-a},
\qquad
n_3^{a}.
\]

The translation changes them to

\[
n_2^{-(a+\delta)},
\qquad
n_3^{a-\delta}.
\]

Consequently the two positive fibre exponents change from

\[
(p,p)
\]

to

\[
\boxed{(p+2,p-2)}.
\]

At the same time the explicit physical-height factor is

\[
X^\delta=e^{2\lambda}.
\]

The simple-pole residue and the one-orientation/adjoint factor are unchanged.  Thus the translated unit source contributes

\[
\boxed{
e^{\lambda p}e^{2\lambda}
E_\lambda(p+2)E_\lambda(p-2).
}
\]

The model coefficient of this source is \(+1\), so there is no extra sign.

## 5. Why the product \(E(p)^2\) does not mean two arithmetic radial variables

The scalar HLZ diagonal has only one radial arithmetic variable when \(h=k=1\):

\[
m=n=\ell.
\]

The two factors in

\[
E_\rho(p)^2
\]

come from the two one-sided pole/packet legs after the completed three-face source is placed on the common output fibre.  They are not two independent copies of \(\ell\).

This is now justified independently by the pre-HLZ packet-separation lemma: before the scalar HLZ contour is moved, the packetized principal source is a lag operator

\[
\iint a_s(x)\overline{a_r(y)}\kappa(y-x)\,dx\,dy,
\]

which Fourier-diagonalizes into one common multiplication-output channel.  The two \(E\)-factors are the two legs of that single channel.

## 6. Replacing the full endpoint \(\lambda\) by the packet endpoint \(\rho\)

The full scalar calculations above naturally produce \(E_\lambda\), because the local physical diagonal scale is

\[
X=e^{\lambda L}.
\]

The packet core restriction acts only on the two one-sided output legs.  Therefore it replaces

\[
E_\lambda(q)\longmapsto E_\rho(q)
\]

inside the fibre features, while leaving the explicit archimedean factors

\[
X^a=e^{\lambda p},
\qquad
X^{2/L}=e^{2\lambda}
\]

unchanged.

This is exactly the distinction required to rule out the erroneous replacement of an explicit physical-height factor by a packet endpoint factor.

## 7. Final independently recovered profile

Combining the three audited contributions gives

\[
\boxed{
\mathscr G_{\lambda,\mu_b,\rho}(p)
=
e^{\lambda p}
\left[
\mu_bE_\rho(2p)
-2E_\rho(p)^2
+e^{2\lambda}E_\rho(p+2)E_\rho(p-2)
\right].
}
\]

Thus the profile used by the spectral-floor argument is recovered independently with:

- the self coefficient \(\mu_b=2F_b/L\);
- the argument \(2p\) in the self fibre;
- the coefficient \(-2\) of the unshifted logarithmic term;
- the one-orientation \(1/2\) and its exact Hermitian cancellation;
- the translated signs \(p+2,p-2\);
- the positive translated coefficient;
- the explicit \(e^{2\lambda}\) factor;
- the universal \(e^{\lambda p}\) factor;
- a single arithmetic radial variable throughout.

## Status

The A1 finite-model profile interface is **closed in the working manuscript** by Lemma `lem:finite-model-face-audit`, together with the already-proved pre-HLZ packet separation.

This statement concerns the finite model used in the final route.  It does not certify the optional stronger levelwise exact-HLP comparison hypothesis.
