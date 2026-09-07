# Small Gap Closure: Exact Pre-HLZ Packet Separation for the Finite-Model Principal Source

Date: 2026-09-03

## Target

The remaining A2 question in the density-one audit was whether, before the scalar Heap--Li--Zhao contour deformation, the actual packetized finite-model principal source really has one common output channel

\[
\mathscr C_T^*M_{u,\mathbf z,p}\mathscr C_T
\]

with the packet map \(\mathscr C_T\) independent of the HLZ Cauchy shifts, the curvature parameter, and the diagonal Mellin variable.

The issue is not Fubini itself.  The issue is whether the operations preceding HLZ can mix the two packet legs with the scalar source.

## Exact packet identity on the right edge

Let

\[
s=c+it,
\qquad
\sigma_0=c-\frac12,
\qquad
z(s)=t-i\sigma_0.
\]

The packet family is

\[
\psi_{L,\tau}(z)
=\int_{\mathbb R}\phi_L(x)e^{ix(z-\tau)}\,dx,
\]

with real \(\phi_L\).  For basis packets \(e_r,e_s\), the invariant polarization is therefore exactly

\[
\boxed{
\mathcal B_{e_r,e_s}(c+it)
=
\iint
\phi_L(x)\phi_L(y)
 e^{-i\tau_sx+i\tau_ry}
 e^{\sigma_0(x-y)}e^{it(x-y)}\,dx\,dy .
}
\]

This already proves three useful facts:

1. the packet labels occur only in the two phases \(e^{-i\tau_sx}\) and \(e^{i\tau_ry}\);
2. the packet multiplier is evaluated at the unshifted central point \(s\), so the normalized curvature shift \(p\) does not enter either packet leg;
3. the later HLZ Cauchy variables \(\mathbf z\) do not occur in the packet legs at all.

Thus the original contour integrand is already a two-leg packet factor times a scalar source.

## Why principal stationarity preserves the separation

Take one scalar one-\(\chi\) Dirichlet monomial

\[
\xi^{-c-it}.
\]

Put

\[
d=y-x.
\]

Then there is the exact algebraic identity

\[
\boxed{
 e^{\sigma_0(x-y)}e^{it(x-y)}\xi^{-c-it}
 =e^{d/2}(\xi e^d)^{-c-it}.
}
\]

Hence, after removing the two packet phases, every occurrence of the packet Fourier coordinates \(x,y\) enters the one-\(\chi\) scalar integral only through the single lag variable

\[
d=y-x.
\]

In particular there is no \(x+y\) dependence.

For

\[
\eta=\xi e^d,
\]

the stationary point is exactly

\[
t_*=2\pi\eta.
\]

The principal stationary calculation already proved that the Stirling amplitude contributes \(\eta^{-1/2}\), while the Gaussian Hessian contributes \(\eta^{1/2}\); these powers cancel exactly.  Therefore principal stationary phase does not create any new factor depending separately on \(x\) or \(y\).

The smooth height cutoff is transported by the same exact dilation

\[
\mathcal S_d^{\rm pr}=D_d\mathcal S_0^{\rm pr}.
\]

Every remaining frozen archimedean factor, curvature factor, translated face, Cauchy factor and scalar Dirichlet coefficient is packet-label independent.  Evaluated at the saddle it is therefore still only a function of \(d\) and the scalar source parameters.

Consequently, after the exact decomposition into the retained principal stationary term plus the already-assigned regular stationary remainder, the finite-model principal slice has the form

\[
\boxed{
\mathcal Q_{rs}^{\rm preHLZ}(u,\mathbf z,p)
=
\iint
 a_{s,T}(x)\overline{a_{r,T}(y)}
 \kappa_T(y-x;u,\mathbf z,p)\,dx\,dy,
}
\]

where

\[
a_{s,T}(x)=\phi_L(x)e^{-i\tau_sx}
\]

is independent of \((u,\mathbf z,p)\).

This is the exact source-level statement that was missing from the earlier prose.

## From lag kernel to one common output fibre

A kernel depending only on \(y-x\) is a convolution operator.  Since the packet Fourier support is compact, one may insert a fixed smooth cutoff equal to one on the full packet difference set; the resulting convolution kernel is compactly supported and smooth on the relevant retained sector.

Therefore

\[
T_{u,\mathbf z,p}
=
\mathcal F^{-1}M_{u,\mathbf z,p}\mathcal F
\]

for a packet-label-independent Fourier multiplier.

Taking

\[
\mathscr C_Te_s
=
\mathcal F a_{s,T}
\]

and adjoining the common normalized principal stationary factors yields

\[
\boxed{
\mathcal Q_{rs}^{\rm preHLZ}
=
\langle
M_{u,\mathbf z,p}\mathscr C_Te_s,
\mathscr C_Te_r
\rangle .
}
\]

The map \(\mathscr C_T\) is independent of \(u\), \(\mathbf z\), and \(p\).  Therefore

\[
\partial_p^j\partial_{\mathbf z}^{\nu}
\mathcal Q_{rs}^{\rm preHLZ}
=
\left\langle
(\partial_p^j\partial_{\mathbf z}^{\nu}M_{u,\mathbf z,p})
\mathscr C_Te_s,
\mathscr C_Te_r
\right\rangle,
\]

with no terms of the form

\[
(\partial\mathscr C_T)^*M\mathscr C_T.
\]

In the diagonal Mellin/Perron representation the multiplier is the common-prefix scalar weight

\[
c_T(t,\mathbf z,p)e^{Lut},
\]

which gives the manuscript's one-sided formula

\[
W_{rs,L}(u,\mathbf z,p)
=
\int b_{s,T}(t)\overline{b_{r,T}(t)}
 c_T(t,\mathbf z,p)e^{Lut}\,dt.
\]

## Support endpoints and transition caps

The support split does not invalidate the factorization.

Let \(P_{\rm core}\) be the fixed restriction of one packet leg to the central flat principal region and \(P_{\rm ext}=I-P_{\rm core}\).  Then the two-leg product decomposes exactly into

\[
P_{\rm core}\otimes P_{\rm core},
\quad
P_{\rm core}\otimes P_{\rm ext},
\quad
P_{\rm ext}\otimes P_{\rm core},
\quad
P_{\rm ext}\otimes P_{\rm ext}.
\]

The first term is the frozen principal source.  The other three terms are exactly the one-leg and two-leg exterior reserve/transition-cap terms already assigned to the exterior-support decomposition.

Because these restrictions are independent of \(p\), \(\mathbf z\), and the HLZ Mellin variable, differentiating the scalar source cannot generate packet-support endpoint jets.

The pairwise intersection \(J_{rs}=I_r\cap I_s\) used later is simply the coordinate representation of the product of the two one-sided support indicators; it is not an independently differentiated endpoint.

## Scope of the word "exact"

The full physical oscillatory integral is first decomposed into:

1. the explicitly defined principal stationary term; and
2. the higher stationary/Stirling/nonstationary remainder already assigned to the regular ledger.

The factorization above is exact for the retained finite-model **principal term**.  It does not claim that stationary phase itself is an exact evaluation of the original oscillatory integral.

This distinction is essential: the source-level packet separation is exact after the manuscript's exact principal/remainder decomposition, and no stationary error is silently absorbed into the HLZ main term.

## Status

For the finite-model route actually used in the final proof, the A2 source-factorization gap is **closed in the working manuscript** by Lemma `lem:pre-HLZ-packet-separation`.

This does not prove the optional stronger exact-HLP levelwise hypothesis `hyp:packet-bilinear-HLZ`.  That hypothesis is not used by the final route; the exact--model difference remains a direct one-\(\chi\) family instead.
