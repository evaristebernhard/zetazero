# Original contour matrix and archimedean self-block audit (2026-09-25)

## M02/M04/M08 observation

The manuscript's inference from the closed holomorphic $f$ integral to
elimination of the Hermitian archimedean self block is false. This is an
orientation error, independent of numerical precision.

Let $I_f$ be the upward right-side matrix for the holomorphic integrand
$f(s)C_{\mathscr Z}^{\rm norm}(s)\mathcal B_{v,w}(s)$. Reflection across
$s\mapsto1-\bar s$ leaves $f$ conjugate-even, while the left side is traversed
downward. Therefore

```text
I_f,left = -I_f*,
I_f,hor  = I_f* - I_f,
I_f + I_f,left + I_f,hor = 0.
```

The closed integral cancels `I_f-I_f*`, the anti-Hermitian vertical part.
It says nothing about `J_arch=I_f+I_f*`, the Hermitian self block in
`sections/03_right_edge.tex`. In particular, the former proof of
Lemma `holomorphic-self-elimination` did not establish the sentence that
removed `J_arch` before the source split. Section 03 now records the correct
identity, and Section 11 states that controlling this block is an unresolved
input to the conditional decomposition.

## Direct finite calculation of the original $A_F$

`scripts/compute_original_contour.py` evaluates the original closed contour
matrix from the $Z_1'/Z_1$ curvature integrand. Independently, it evaluates
the $H=f+Z_1'/Z_1$ representation and the zero-coordinate-equivalent raw term
$q^2\zeta Z_2^2/(L^2Z_1)$. No stationary approximation or arithmetic
diagonal is used. The contour has right side `Re s=2`, left side `Re s=-1`,
and good sampled horizontal heights in `[T,T+1]`, `[2T,2T+1]`.

The packet is exactly flat on `[-L_pkt/2,L_pkt/2]` and has an explicit
$C^\infty$ transition of width `0.1` on each side. The core is
`[-L/2,-L/2+W_T]`, with `A_0=C_pkt=0.1`, and centres are on the exact packet
lattice. These are finite test parameters; they are not the eventual
large-buffer asymptotic regime or the paper's unspecified retained projection.

On the 34-dimensional packet space at `T=80`, the refined contour is
`[80.1,160.95]`. The matrices have:

| Matrix | Negative count | Smallest eigenvalue | Frobenius norm |
|---|---:|---:|---:|
| Original closed-contour $A_F$ | 0 | 0.5929 | 34.4951 |
| Core $A_T^{\rm true}$ | 19 | -3.3037 | 8.2273 |
| Full arithmetic source $A_{\rm ar}$ | 18 | -5.2929 | 11.5362 |
| Hermitian $J_{\rm arch}$ alone | 0 | 1.3501 | 33.8924 |

The exact finite split is

```text
A_F = A_true_core + A_geom_exact + J_arch
      + A_fprime_right + A_horizontal_H.
```

Its relative Frobenius residual is `3.34e-7`. Leaving out `J_arch` gives a
relative discrepancy of `0.9825`, and the negative directions remain until
that block is added. The $f'$ right block has Frobenius norm `0.1009` and
the horizontal $H$ block `5.0652`; neither explains the missing self block.

Independent consistency checks at the refined grid give

```text
||A_F(Z1'/Z1) - A_F(H)||_F / ||A_F(H)||_F = 5.43e-6,
||A_F(raw zero term) - A_F(H)||_F / ||A_F(H)||_F = 1.70e-4,
||I_f,left + I_f*||_F / ||A_F(H)||_F = 3.29e-7.
```

The first two differences are quadrature/derivative errors in equal closed
contour integrals and shrink under mesh refinement. The smallest eigenvalue
of $A_F$ moves from `0.592889` to `0.592901` between the two finest smooth
packet runs, so the zero negative count at `T=80` is stable at this precision.
At `T=160`, both tested meshes also give zero negative eigenvalues versus
46 for the core operator, but the smallest original eigenvalue is only about
`0.004` on the finer mesh; its sign requires tighter error control and is not
used as a certificate.

## Manuscript impact and next interface

The paper now writes the exact normalized four-block identity
`A_F=A_true+L_geom+J_arch+R_exact`, where
`R_exact=A_fprime_right+A_horizontal_H`. Its right-edge operator includes
the necessary `L^-2` curvature normalization. The conditional theorem
separately assumes that `L_geom+J_arch` can be written as a small-rank edge
operator plus a relative-Hilbert--Schmidt-small residual. That bound does not
follow from the exact source algebra. The missing $J_arch$ must be kept in
the principal operator, or a new argument must place it in an allowed
remainder class. The finite calculation suggests it is leading size, but
the exact orientation identity alone is enough to invalidate the claimed
holomorphic elimination. The previously observed near-half negative spectrum
of $A_true$ was a correct calculation for that core matrix; using it as a
proxy for the original $A_F$ was the wrong decomposition step.

Reproduce the 12-column directed test with `npm test -- original-contour`.
For the 34-column run:

```bash
python3 scripts/compute_original_contour.py --height 80 --smooth-cap 0.1 --height-step 0.0075 --horizontal-nodes 2048 --derivative-step 0.001 --output output/numerics/original_T80_smooth_superfine.json --matrix-output output/numerics/original_T80_smooth_superfine.npz
```

The generated JSON and NPZ matrices are ignored by Git; the script and this
audit are tracked.
