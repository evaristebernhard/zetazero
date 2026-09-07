# Audit of the lagwise scalar-HLZ bridge

## Status

**Fatal gap in the current manuscript route.**

The structural cleanup on `fix/lagwise-hlz-log-only` is useful, but the theorem-facing proposition `prop:lagwise-packet-HLZ` is not presently proved. The obstruction is not the earlier one-sided-prefix identification; it occurs one step earlier, at the attempted passage from the physical one-chi stationary carrier to the untwisted scalar HLZ Euler diagonal.

The audit below separates this upstream obstruction from two downstream issues: the closed form of `G_log`, which is repairable, and the relative-remainder exponent ledger, which still needs explicit normalized jump bounds.

## 1. The stationary carrier retains an additive phase

On the absolute-convergence right edge the theorem-facing logarithmic source is

```text
C(s) H_log(s),
H_log(s) = -2 P(s) + P(s-2/L).
```

For one Dirichlet monomial `xi^{-c-it}`, the exact packet polarization with `d=y-x` gives

```math
e^{\sigma_0(x-y)}e^{it(x-y)}\xi^{-c-it}
= e^{d/2}(\xi e^d)^{-c-it}.
```

The one-chi stationary calculation therefore has

```math
\eta=\xi e^d,
\qquad t_*=2\pi\eta,
```

and its leading oscillatory factor is

```math
\boxed{e(-\xi e^d).}
```

This factor is not a packet-label-independent scalar after the arithmetic carrier is exposed. In the invariant source the old manuscript's own carrier bookkeeping identifies the physical stationary carrier with the diagonal integer `ell` (equivalently `N=ell` after the auxiliary outer indices are trivial), and records the physical saddle relation

```math
t_*=2\pi\ell x.
```

Thus, at fixed lag, the leading arithmetic sum contains an additive carrier twist of the schematic form

```math
\sum_{\ell} a_{\ell}\,e(-e^d\ell)\,\ell^{-1-2u},
```

or the corresponding convolutional total-carrier version before the coefficient variables are collapsed.

## 2. The scalar HLZ lemma used in Section 6 is untwisted

The theorem-facing scalar core instead uses

```math
D_{\mathbf z}(u)
=\frac{\zeta(1+z_1-z_2+2u)\zeta(1-z_2+z_3+2u)}
       {\zeta(1-z_2+2u)},
```

which is the ordinary multiplicative Euler diagonal. The scalar HLZ diagonal has the relation `hm=kn`; for `h=k=1` this becomes `m=n=ell`. It does **not** contain the additional character `e(-e^d ell)`.

Therefore the sentence in `sections/06_lagwise_packet_hlz.tex` which removes the "universal stationary carrier" and then applies the scalar HLZ diagonal pointwise in `d` is not justified. The omitted factor depends on the arithmetic carrier. It cannot be absorbed into the current admissible Mellin amplitude with only fixed polylogarithmic derivative losses.

An additively twisted divisor/Euler sum is an Estermann/Voronoi-type object, not the same Euler product. A replacement theorem would have to control this twist uniformly in the continuous parameter `e^d`, including the packet/endpoint derivatives used later.

## 3. Internal rank-versus-floor no-go certificate

There is a second, representation-independent way to see the same obstruction.

Keep the physical carrier in the unit-shell Fourier representation. For one retained shell,

```math
\mathcal I_j
=\left[\frac{T}{2\pi(J_j+1)},\frac{2T}{2\pi J_j}\right].
```

A stationary direct carrier `m in I_j` acts by a compressed Fourier shift `P_j S_m P_j`. All such forward shifts have range in the same low-edge interval, with

```math
\dim E_j^-
\ll \frac{T}{J_j^2}+R_j+1,
```

and the adjoints have the same bound. Summing over shells gives `O(T)+o(T)=o(N_T)` rank for all low sidebands, independently of their scalar coefficients.

For the present source the required coefficient-square estimate does not depend on the discarded HLP hierarchy. After the total Dirichlet carrier is collapsed, the coefficients of

```math
\mathcal C(s)H_{\log}(s)=\zeta(s)^2Q(s)H_{\log}(s)
```

are bounded by a fixed power of `log n` times a fixed-order divisor function; a deliberately crude majorant is `d_4(n)(log n)^3`. The standard fixed-`k` divisor mean-square estimate therefore gives

```math
\sum_{m\le x}|c_m|^2\ll x(\log x)^C
```

through the finitely many normalized source derivatives. Arbitrary Fourier decay of the smooth stationary symbol then places the complementary high sidebands in relative Hilbert--Schmidt square `o(N_T)`. The nonstationary and endpoint pieces have the same low-rank/relative-HS form.

Consequently the direct physical realization of the log-only one-chi source has the schematic decomposition

```math
A_{\log}^{\rm dir}=E_{\rm dir}+R_{\rm dir},
\qquad
\operatorname{rank}E_{\rm dir}=o(N_T),
\qquad
\|\mathfrak G_T^{-1/2}R_{\rm dir}\mathfrak G_T^{-1/2}\|_{S_2}^2=o(N_T).
```

If the present lagwise scalar-HLZ proposition were also valid, the same source would satisfy

```math
A_{\log}^{\rm dir}=P_T+E'+R',
```

with `rank E'=o(N_T)`, relative-HS square `o(N_T)`, and a fixed positive floor

```math
P_T \succeq c\,\mathfrak G_T
```

for some fixed `c>0` on a retained space of dimension `(1-o(1))N_T`.

These statements are incompatible. After whitening by `mathfrak G_T`, combine the two decompositions and write

```math
\widetilde P = E + R,
\qquad \operatorname{rank}E=r=o(N_T),
\qquad \|R\|_{S_2}^2=o(N_T),
\qquad \widetilde P\succeq cI.
```

On `ker(E)` (or, for a Hermitian rank correction, the orthogonal complement of its range) there are at least `N-r` dimensions and the compression of `R` equals the compression of `P`. Hence

```math
\|R\|_{S_2}^2
\ge c^2(N-r)
\asymp N_T,
```

contradicting `o(N_T)`.

Thus a fixed-floor bulk lag operator cannot be obtained from the physical direct-carrier matrix with only the stated low-rank and relative-HS errors. Some order-one term is missing from the scalar lift; the additive carrier phase is the explicit missing structure.

## 4. The current `G_log` closed form is also wrong, but this is downstream and repairable

Starting from the manuscript's own frozen profile definition

```math
G_{\log}(\rho)
=[p^2]e^p\left[-2E_\rho(p)^2
+e^2E_\rho(p+2)E_\rho(p-2)\right],
```

direct coefficient extraction gives

```math
\boxed{
G_{\log}(\rho)
=-\frac76\rho^4+2\rho^3-\rho^2
+\frac{e^2}{8}
\left[(2\rho^2-4\rho+3)\cosh(2\rho)
      -4\rho^2+4\rho-3\right].
}
```

The current `sinh(2 rho)` formula in Section 8 is therefore not the coefficient of the displayed source profile.

For this corrected function, numerical high-precision audit gives

```text
2 G_log'(1)                 ~= 4.6771480760
sup_x int_0^1 |G_log''(1-|x-y|)| dy ~= 4.6016390616
```

so the Schur margin is about `0.075509 ||Q||^2`, i.e. about `0.037754 Q_triangle`. The previous `0.98 Q_triangle` claim is false, but a rigorous conservative target `0.03 Q_triangle` appears feasible, and the endgame constant `c0=0.02` would still fit **if** the upstream principal bridge were repaired.

A convenient rigorous route is to reuse the existing rational Taylor enclosure for `exp(x)`: prove strict convexity of `g=G_log''`, bracket its two roots near `0.24838` and `0.64641`, locate the row-sum maximum near `0.31446`, certify `sup M<4.61`, and certify the cusp coefficient `>4.67`.

This downstream repair does not address the fatal additive-twist problem.

## 5. The remainder ledger still needs an explicit exponent ledger

The primitive criterion requires the normalized diagonal jump to satisfy

```math
\delta_T=o(1).
```

In `sections/11_logonly_remainder.tex`, the finite-height and direct-residual arguments currently use bounds written schematically as

```text
O(L^{-1+C})
O(L^{-2+C_dir})
```

and then appeal to a large `A0`. A large `A0` helps the **sum over shells**, but it cannot make a single-shell normalized jump small. The proof therefore needs the stronger diagonal fact used in the previous reference-remainder argument: after all common positive packet/stationary weights are put into the reference map, the remaining diagonal amplitude is `O(1)`. Then the profile derivatives themselves give `O(L^-1)` and `O(L^-2)` normalized jumps.

The HLZ contour-error class is not affected by this issue because its logarithmic saving exponent is arbitrary; the `f'` class also has the much stronger `T^-1` factor.

## 6. What would actually repair GAP1?

At least one new theorem/mechanism is needed. Plausible directions are:

1. **Additively twisted HLZ/Estermann route.** Keep `e(-e^d ell)` and prove a uniform transformation for the shifted divisor coefficients. Existing Voronoi formulas for additively twisted shifted divisor functions show that this is a genuinely different analytic object. The required theorem would have to be uniform in the continuous twist and compatible with the packet derivatives.

2. **Second stationary phase in the lag variable.** After the `t`-stationary step the remaining `d`-phase contains
   `tau_r d - 2 pi ell e^d`; its stationary point satisfies `2 pi ell e^d=tau_r`. This converts the additive phase back into a multiplicative oscillation in `ell`, but it also reintroduces the fine packet centre. A complete two-stage stationary/large-sieve analysis would be required; it is not the current scalar HLZ proof.

3. **Redesign the invariant contour/test matrix.** Seek a source whose principal right-edge carrier has a genuine zero/net shift and therefore a bulk positive component before any disputed arithmetic lift. This would be a substantially different argument.

Until one of these is proved, `prop:lagwise-packet-HLZ`, the log-only principal decomposition, and the density-one theorem are not established.

## 7. Citation correction in the scalar core

The current proof of the three-face Cauchy identity says it is "HLZ formula (28)". In Heap--Li--Zhao, the three principal faces occur earlier (their main three-face expansion), while formula (28) is a later definition and is not this triple Cauchy identity.

The triple Cauchy identity used in the manuscript is nevertheless an elementary residue identity and can be proved directly. Let

```math
P(z)=(z-\alpha)(z+\beta)(z-\gamma).
```

Only the six permutations of the three distinct roots survive the Vandermonde square. For a monic cubic,

```math
\frac{\Delta(r_1,r_2,r_3)^2}{P'(r_1)P'(r_2)P'(r_3)}=-1.
```

The prefactor `-1/2` therefore gives `+1/2` per permutation; symmetry under `z1 <-> z3` pairs the six residues into exactly the three displayed faces. The manuscript should use this direct proof and cite HLZ only for the scalar diagonal/Euler input, not for a nonexistent formula-(28) identity.
