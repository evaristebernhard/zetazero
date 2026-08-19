# Formalization status

This table is the human-readable status ledger.  The Blueprint is the
machine-rendered dependency view.  Update both in the same change whenever a
major node changes state.

| ID | Status | Lean declarations linked | Notes |
|---|---|---:|---|
| M01 | Lean core complete; Blueprint certification pending | 1 | The physical-coordinate rank-plus-Hilbert--Schmidt min--max theorem builds with warnings-as-errors and resolves under `leanblueprint checkdecls`; `\leanok` plus the full Blueprint build are still pending, so M01 is not yet green by project policy. |
| M02 | In progress; packet same-form and global weighted zero sum complete | 1 | The high-rectangle branch/reflection law, `𝒵' = q Z₁`, exact curvature source, symmetric-shift generation, packet polarization, Cauchy cancellation, and zero-free boundary integrability all build. The Hardy and `Z₁'/Z₁` packet boundary forms are exactly equal, and the vendored weighted rectangle argument principle now converts the normalized common form into the finite multiplicity-weighted sum over all internal `Z₁` zeros. The remaining seam is no longer a global residue theorem; it is the straightening/generic-simple specialization connecting those weights to the zero-side stationary kernel and block decomposition. |
| M03 | Zero-sum input plus stationary residue/inertia local theory started | 1 | Shared zero infrastructure covers multiplicity/counting, finite ordinate windows, critical-line/off-critical reflection pairing, and finite-set good-height avoidance. M02 now supplies the global multiplicity-weighted `Z₁` zero sum. On the stationary side Lean proves `(z-c)(-H(H'')²/H') → -H(c)H''(c)` at a simple stationary zero, and formalizes the real/conjugate-pair block inertia. Remaining work is the straightening/simple-zero specialization of the global sum, packet-evaluation surjectivity, and the `Z₁` Jensen/log-derivative good-height estimates. |
| M04 | Algebraic right-edge source foundation started; analytic contour transfer awaits M02 | 0 | The completed frozen source `F-P+Q/(F-P)`, two-master model, exact source defect, and exact slow-factor freezing identities are formalized independently of zeta asymptotics. What remains is the analytic identification of the actual right-edge contour source, block freezing bounds, dilation/stationary-phase transfer, and Perron/residue analysis. |
| M05 | Arithmetic, resolvent, and first factorial-majorant inequality layer started | 1 | Mathlib `ArithmeticFunction` formalization covers von Mangoldt convolution powers, `Q(n)=Λ(n) log n`, support/truncation of `P^kQ`, and the exact recurrence `α_{k+2}=Λ*α_{k+1}` with divisor-antidiagonal coefficient formulas. The finite resolvent identity is exact, giving the source as a finite HLP hierarchy plus one tail. The weighted Cauchy step is now also formalized and specialized to the recurrence, including `Σ_{d|n}Λ(d)=log n`; thus the pointwise squared recurrence used by the factorial majorant is in Lean. Summing it into a uniform mean-square/factorial bound, the HLZ bilinear structure, and the local projector remain difficult analytic work. |
| M06 | Planned; awaiting M05 | 0 | Stable facade only; its future spectral-floor arguments can consume the abstract positive-Gram and min--max interfaces without redoing linear algebra. |
| M07 | Abstract positive-Gram foundation started; arithmetic deformation awaits M05 | 0 | For a finite complex analysis map `W`, Lean now formalizes the pullback Gram quadratic `Σ|Wv|²`, its nonnegativity, zero set `ker W`, positivity under injectivity, and exact behavior under precomposition. Concrete divisor/Euler analysis maps and their quantitative comparison remain pending. |
| M08 | Planned; awaiting M03, M06, M07 | 0 | Stable facade only. |
| M09 | Abstract retained-space bookkeeping started; analytic maps await M08 | 0 | The reusable kernel/intersection budget now proves `codim(ker M₁ ∩ ker M₂) ≤ rank M₁ + rank M₂` and the threefold retained-intersection codimension bound. The actual global/local mean maps and their asymptotic rank estimates still depend on M08. |
| M10 | Abstract perturbation/min--max glue started; zero-side endgame pending | 0 | Perturbation stability `P ≥ cG`, `|Δ| ≤ εG` ⇒ `P+Δ ≥ (c-ε)G` is formalized, including the manuscript's `ε=c/4` floor, and is connected to the existing rank-plus-Hilbert--Schmidt min--max theorem. The remaining work is the analytic `F→H` perturbation/zero-count transfer and insertion of the actual M09 retained space. |

No major node is green yet.  M01 is already linked and passes `checkdecls`, but
project policy still requires `\leanok` certification and a complete Blueprint
build before the node can turn green.  Both the default Lean build and the
all-source `lean-all` gate currently pass; the latter explicitly compiles every
`ZetaZero/**/*.lean` file so unimported modules cannot remain silently broken.

