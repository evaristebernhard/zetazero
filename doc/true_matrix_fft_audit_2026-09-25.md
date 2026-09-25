# Finite-scale FFT audit of the true right-edge matrix (2026-09-25)

## M05/M06/M10 observation

The sign count of the raw matrix is not the paper's defect criterion.  The
criterion is the negative **squared spectral mass after reference-Gram
whitening and subtraction of the positive model**.  This audit computes the
actual right-edge integral defining `A_T^true` for a stated, reproducible
packet/core choice.  It retains the complete `H_ar` source and therefore the
oscillatory one-chi carrier; it does not insert the unproved scalar-HLZ lag
kernel.

The finite experiments below have close to half of the raw eigenvalues
negative.  Their raw negative squared mass is sizeable in this realization.
Thus a sign count alone cannot support the claim that the negative spectrum is
harmless, and this experiment does not verify the manuscript's `beta_-`
hypothesis.  Conversely, these finite data do not disprove an asymptotic
statement on the paper's eventual retained subspace.

## Matrix and computation

On `s=2+it`, with `L=log(T/(2*pi))`, the program evaluates

```text
F_T(t) = chi(1-s) zeta(s)^2 Q(s)
         [-P(s) + Q(s)/(f(s)-P(s))] / L^2,
P=-zeta'/zeta, Q=(zeta'/zeta)', f=-(chi'/chi)/2.
```

For the flat core `[u_0,u_0+W_T]`, it forms the two packet legs

```text
B_+(t,tau) = L_pkt^(-1/2) integral_core exp((3/2+i(t-tau))u) du,
B_-(t,tau) = L_pkt^(-1/2) integral_core exp((-3/2+i(t-tau))u) du.
```

The right-edge matrix is

```text
I_ij = (1/(2*pi)) integral_T^(2T)
       F_T(t) conj(B_-(t,tau_i)) B_+(t,tau_j) dt,
A_true = I + I*.
```

The code uses an FFT of the sampled core legs on a height lattice, then a
weighted matrix product.  It checks the FFT legs against their analytic
exponential integrals.  SciPy's complex zeta evaluator and fourth-order
finite differences provide the right-edge source; height and packet sampling
are refined independently.  The companion NPZ contains `A_true`, a Gaussian
quadrature of the triangular primitive reference Gram, the mean row, packet centres,
and height nodes/weights.

The experiment fixes `C_pkt=0.1`, `A_0=0.1`, exact lattice centres,
`u_0=-L/2`, and `W_T=L-A_0 log L`.  For these accessible heights this small
`A_0` is needed to keep the core nonempty and close to the full logarithmic
band.  It is **not** the manuscript's eventual large-buffer asymptotic regime.
The paper leaves the smooth packet cap, exact near-lattice centre perturbations,
and the retained subspace unspecified; this file records a concrete
specialization of the right-edge matrix, not a unique canonical finite matrix.
The vertical interval is exactly `[T,2T]` rather than the admissible
`[T_1,T_2]` with endpoints shifted by at most one.

| `T` | dimension | raw negative count | mean-zero negative count | raw negative squared mass / total | min / max eigenvalue | `|lambda| < 10^-8 max|lambda|` |
|---:|---:|---:|---:|---:|---:|---:|
| 80 | 34 | 19 | 18 | 0.62746 | -3.312 / 2.870 | 0 |
| 160 | 85 | 46 | 45 | 0.66001 | -6.324 / 4.891 | 1 |
| 320 | 207 | 108 | 108 | 0.68282 | -10.609 / 7.767 | 8 |
| 640 | 487 | 256 | 256 | 0.69465 | -17.950 / 11.929 | 25 |

The near-zero column is a numerical accuracy warning; those eigenvalues
remain in the raw sign counts.  At `T=80`, the full FFT matrix differs from
the matrix made with analytic packet integrals by `1.32e-5` in relative
Frobenius norm.  At `T=640` that error is `1.26e-4`.  Refining the height
grid, Fourier grid and derivative step from the baseline changes the largest
eigenvalue by at most `0.044` at `T=640` (about `0.25%` of the spectral
radius); the negative squared mass fraction changes by less than `1e-4`.
Small eigenvalue signs are less stable.

## Comparison with the paper's positive kernel at one finite height

`scripts/compare_true_reference.py` puts
`K(r,s)=G_log(1-|r-s|)` on the **same** finite packet basis and projects both
matrices to the mean-zero space. At `T=80`, 1024-point Gauss quadrature gives
dimension `33`, a reference Gram condition number about `707`, and

```text
min eig(P,G) = 0.57636 (> kappa_* = 0.02),
negative count of eig(A_true - P,G) = 18,
sum of squares of negative generalized eigenvalues = 5.3269e11,
min eig(A_true - P,G) = -6.6443e5.
```

Here `eig(B,G)` means the Hermitian generalized eigenproblem `Bv=mu Gv`.
The same negative squared mass changes by less than `5e-7` relatively when
the model quadrature is halved to 512 nodes.  The large number is a
finite-scale diagnostic on the mean-zero space only: the paper's additional
core/end retained projection and asymptotic large-`A_0` regime are not in
this calculation. It nevertheless shows that, for this explicit matrix,
smallness of the raw eigenvalues cannot be inferred from their signs or from
the positive comparison floor.

At `T=80`, the exact source split also gives
`||A_ar||_F=8.27`, `||A_log||_F=26.22`, and
`||A_direct_residual||_F=24.64`, with
`||A_ar-A_log-A_direct_residual||_F/||A_ar||_F < 3e-15`.
Thus replacing the exact source by the log-only source is already a poor
finite-scale numerical approximation at this height.  The source identity is
an algebraic check, not an asymptotic estimate.

## Manuscript impact and next interface

The current conditional theorem may keep `beta_-` as an explicit hypothesis,
but no numerical sign count establishes it. The positive comparison operator
can now be computed on the same finite basis; the next interface is the
paper's precise retained projection and a verified treatment of the very
small eigenvalues of `G` at larger heights. To turn this into a theorem, one needs uniform
estimates for that spectral mass as `T` grows; finite FFT data alone cannot
provide them.  The unproved additive-twist bridge in M05 remains open.

Reproduce the main files with:

```bash
python3 scripts/compute_true_matrix.py --height 80 --a0 0.1 --packet-reserve 0.1 --height-oversample 24 --u-step 0.001 --derivative-step 0.001 --direct-check --output output/numerics/true_T80_fine.json --matrix-output output/numerics/true_T80_fine.npz
npm test -- true-matrix
python3 scripts/compare_true_reference.py --matrix output/numerics/true_T80_fine.npz --metadata output/numerics/true_T80_fine.json --nodes 1024 --output output/numerics/compare_T80_fine.json
```

Replace `80` with `160`, `320`, or `640` for the other rows.  Generated NPZ
and JSON files are ignored by Git.
