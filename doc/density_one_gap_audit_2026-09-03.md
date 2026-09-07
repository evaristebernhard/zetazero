# Density-One Proof Gap Audit

Date: 2026-09-03

Scope: **Only the proof of the manuscript's density-one theorem**

\[
\frac{N_0(T)}{N(T)}\to 1.
\]

This document deliberately does **not** discuss the stronger Riemann Hypothesis statement. The only question here is whether the current manuscript actually closes the density-one proof chain it states.

---

## 1. Current proof architecture

The present main route is

\[
\text{Hardy-gauge contour matrix}
\longrightarrow
\text{right-edge exact source split}
\longrightarrow
\begin{cases}
\text{finite model principal source},\\
\text{direct exact--model residual},\\
\text{self-freezing remainder},
\end{cases}
\]

followed by

\[
A_T=P_T+E_T^{\rm edge}+R_T^{\rm tri},
\]

with the desired three estimates

\[
P_T\succeq c_0\mathfrak G_T,
\qquad
\operatorname{rank}E_T^{\rm edge}=o(N_T),
\qquad
\|\mathfrak G_T^{-1/2}R_T^{\rm tri}\mathfrak G_T^{-1/2}\|_{S_2}^2=o(N_T).
\]

These are then fed into the finite-dimensional inertia argument and the generic perturbation / zero-count endgame.

The old packet-valued HLZ hypothesis is no longer part of the main theorem. This is an important improvement. The remaining risks are concentrated at a smaller number of interfaces.

---

# A. Theorem-sized gaps / high-risk interfaces

## A1. Exact derivation of the frozen principal profile \(\mathscr G_{\lambda,\mu,\rho}(p)\)

### Current claimed profile

The manuscript uses

\[
\mathscr G_{\lambda,\mu,\rho}(p)
=
 e^{\lambda p}
\left[
\mu E_\rho(2p)
-2E_\rho(p)^2
+e^{2\lambda}E_\rho(p+2)E_\rho(p-2)
\right].
\]

The frozen model is then

\[
G(\rho)
=[p^2]e^p
\left[
E_\rho(2p)-2E_\rho(p)^2
+e^2E_\rho(p+2)E_\rho(p-2)
\right].
\]

All later spectral positivity rests on this exact formula.

### Why this is high risk

The global Schur-floor calculation in Section 8 can be correct while the theorem is still wrong if the profile fed into it has any of the following errors:

- a missing or extra factor of 2;
- an incorrect Hermitian orientation factor;
- an incorrect sign in one of the three faces;
- an endpoint mismatch;
- an incorrect \(+2/-2\) normalized shift;
- a wrong outer factor \(e^{2\lambda}\);
- a mistaken conversion of a single arithmetic diagonal variable into a product of two packet-fibre integrals.

The present derivation of the three contributions is too compressed relative to the importance of the conclusion.

The most delicate point is the passage from the scalar HLZ diagonal, where after \(h=k=1\) the arithmetic condition reduces to a common radial variable, to packet expressions of the form

\[
E_\rho(p)^2,
\qquad
E_\rho(p+2)E_\rho(p-2).
\]

These products can be correct if they arise from the two one-sided packet legs rather than from two independent arithmetic variables, but that distinction must be proved explicitly.

### Required closure

Recompute the finite model independently from the original Heap--Li--Zhao three-face formula, without using the manuscript's already-derived profile.

The audit should prove, face by face,

\[
\text{HLZ scalar three-face residue}
\longrightarrow
\text{physical-shift curvature coefficient}
\longrightarrow
\text{packet diagonal}
\longrightarrow
\begin{cases}
\mu E_\rho(2p),\\
-2E_\rho(p)^2,\\
e^{2\lambda}E_\rho(p+2)E_\rho(p-2).
\end{cases}
\]

Every sign, normalization and factor must be tracked.

### Current assessment

**Closed for the finite-model route used in the final proof on 2026-09-03.** Lemma `lem:finite-model-face-audit` independently recomputes the profile from the original HLZ pole factors and the Hardy-gauge shift identity. It tracks the common factor $e^{\lambda p}$ from $q(s+a)/q(s-a)$, obtains the self fibre $E_\rho(2p)$ and coefficient $\mu_b=2F_b/L$, computes the one-orientation logarithmic face exactly as $\frac{L^2}{2}E_\lambda(p)^2$ and shows that Hermitian reassembly removes precisely this $1/2$, and derives the translated $(p+2,p-2)$ exponents together with the explicit $e^{2\lambda}$ tag. Lemma `lem:pre-HLZ-packet-separation` then shows that passing to the packet common prefix replaces only $E_\lambda$ by $E_\rho$ and does not alter the explicit physical-height factors. See `doc/small_gap_independent_HLZ_face_profile_audit_2026-09-03.md`.

---

## A2. Exact source-level factorization before applying scalar HLZ

### Current idea

For a packet pair the manuscript writes the finite-model weight as

\[
W_{rs,L}(u,\mathbf z)
=
\int_{J_{rs}}
 b_{s,T}(t)\overline{b_{r,T}(t)}
 c_T(t,\mathbf z)e^{Lut}\,dt,
\]

and therefore places all packet dependence into one common analysis map

\[
\mathscr C_T,
\]

while the scalar arithmetic / Cauchy / Mellin factor acts by multiplication on the output fibre.

Once this identity is valid, the subsequent Fubini step is natural.

### Actual risk

The dangerous statement is not Fubini's theorem itself. The dangerous statement is the stronger source identity

\[
\boxed{
\text{actual physical packetized finite-model source}
=
\int b_s\overline{b_r}\,\mathcal S_{\rm scalar}(t)\,dt
}
\]

**before** the HLZ deformation.

The current prose derives this separation from packet polarization, stationary dilation and shift-independence of the completed scalar factors. That is plausible, but this interface is important enough that an exact pre-deformation identity should appear explicitly.

If some auxiliary shift, stationary Jacobian, support endpoint, packet-cap factor or curvature derivative acts on the packet map itself, then terms of the schematic form

\[
(\partial_{\mathbf z}\mathscr C_T)^*M\mathscr C_T
\]

or endpoint jets could appear, destroying the clean multiplication-operator representation.

### Required closure

Insert and prove a source-level lemma of the form

\[
\mathcal S_{rs}^{\rm finite\ model}
=
\int_{J_{rs}}
 b_s(t)\overline{b_r(t)}
 \mathcal S_{\rm scalar}(t;u,\mathbf z,p)\,dt
\]

on the original contour, before residue extraction and before HLZ contour movement.

Then verify explicitly that:

1. packet labels occur only in the two one-sided factors;
2. auxiliary Cauchy shifts occur only in the common scalar multiplier;
3. physical-shift differentiation does not differentiate the packet analysis map;
4. moving support endpoints are already accounted for;
5. transition caps / reserve pieces are excluded from the frozen principal source and assigned elsewhere exactly once.

### Current assessment

**Closed for the finite-model route used in the final proof on 2026-09-03.** Lemma `lem:pre-HLZ-packet-separation` now derives the source factorization directly from the Fourier definition of the packet polarization. On the right edge the exact packet double integral and any scalar one-$\chi$ monomial depend on the two packet Fourier coordinates only through their separated packet phases and the lag $d=y-x$; the principal stationary saddle is $t_*=2\pi\xi e^d$, and the Stirling/Hessian powers cancel, so no $x+y$ or separately leg-dependent scalar factor is generated. The resulting lag operator is Fourier-diagonalized into one common multiplication-output channel, with $(u,\mathbf z,p)$ acting only in the multiplier. The flat-core/exterior split is made by parameter-independent leg restrictions, so reserve/cap terms are assigned separately without packet-analysis or endpoint jets. This strengthens the earlier auxiliary-shift-rigidity sublemma and also closes the physical-shift/endpoint part. See `doc/small_gap_pre_HLZ_packet_source_factorization_2026-09-03.md`.

This closure is deliberately limited to the finite-model principal source after the explicit stationary principal/remainder split. It does not prove the optional stronger exact-HLP levelwise Hypothesis `hyp:packet-bilinear-HLZ`, which the final proof does not use.

---

## A3. Exhaustion of the direct exact--model residual by edge + relative-HS classes

### Current exact split

The manuscript uses

\[
\widehat H_{\rm ex}(s)
=
H_{\rm mod}(s;F_b)
+
\Delta H_{\rm dir}(s)
+
(f(s)-F_b),
\]

with

\[
\Delta H_{\rm dir}(s)
=
P(s)+\frac{Q(s)}{f(s)-P(s)}-P(s-2/L).
\]

The HLP resolvent remains on the absolute-convergence right edge:

\[
\frac{Q}{f-P}
=
\sum_{k\ge1}f^{-k}P^{k-1}Q.
\]

The claim is that every stationary term of \(\Delta H_{\rm dir}\) remains a direct physical one-\(\chi\) carrier with

\[
t_*=2\pi My,
\qquad
e(-My),
\]

so low sidebands have low rank and high sidebands are relative Hilbert--Schmidt small.

### Why this remains high risk

The coefficient-level observation

\[
\text{all levels preserve the total index }M
\]

is not by itself the full operator decomposition.

The proof still needs to show that after every later operation the residual produces no unassigned family:

- stationary main region;
- low Fourier sidebands;
- high Fourier sidebands;
- nonstationary region;
- stationary-window boundaries;
- differentiated height partitions;
- terminal logarithmic tail;
- packet reserve outside the physical band;
- smooth transition caps;
- one-leg exterior terms;
- two-leg exterior terms;
- core--tail cross terms;
- adjoint/Hermitian counterpart terms.

The recent need to add an explicit exterior packet-support decomposition is evidence that source exhaustion is not automatic.

### Required closure

Construct a literal source-to-final-matrix table

\[
\text{exact source monomial}
\to
\text{functional-equation orientation}
\to
\text{stationary/nonstationary}
\to
\text{sideband/support class}
\to
P_T/E_T^{\rm edge}/R_T^{\rm tri}.
\]

The table should satisfy two properties:

1. **Exhaustive:** every source term appears.
2. **Disjoint:** every source term appears exactly once.

This should be checked for finite partial HLP sums first and then passed to the norm-convergent hierarchy.

### Current assessment

**Priority 3. Theorem-sized global bookkeeping risk.**

---

# B. Important but probably repairable analytic gaps

## B1. Parametric extension of the Heap--Li--Zhao diagonal lemma

### What the original HLZ source actually gives

The original arXiv LaTeX permits an analytic auxiliary function \(H(s)\) satisfying

\[
H(0)=1,
\]

vanishing at the two moving divisors and having Gaussian vertical decay. It explicitly suggests

\[
H(s)=Q_{\mathbf z}(s)e^{s^2}.
\]

Its diagonal error contains an arbitrary logarithmic saving.

Thus the manuscript's use of a \(\mathbf z\)-dependent cancelling polynomial is consistent with the original proof.

### Remaining extension

The manuscript effectively replaces the HLZ auxiliary by something like

\[
H_{\mathbf z}(u)W_T(u,\mathbf z),
\]

where the packet Mellin weight may have fixed polylogarithmic size.

On the relevant HLZ strip this appears harmless:

\[
W_T(u)=\int_0^{C_*}a_T(t)e^{Lut}\,dt
\]

has no vertical exponential growth, and its real-direction growth is bounded on the narrow contour strip. A fixed \(L^C\) loss should be absorbable into the arbitrary logarithmic saving.

However, this is a generalized lemma proved from HLZ's argument, not literally the theorem as printed.

### Required closure

State a parametric diagonal lemma with assumptions such as

\[
|H_T(u+iv)|
\ll
L^{C_H}(1+|v|)^{C_H}e^{-c_Hv^2}
\]

uniformly on the deformation strip, including the needed finite shift and curvature derivatives.

Then reproduce the short contour proof showing

\[
E_{\rm HLZ}
=
O_A(L^{-A+C_H})
+
O\!\left(
L^{C_H}
\left(\frac{T^2}{hk}\right)^{-1/\log_3T}
\operatorname{polylog}T
\right).
\]

### Current assessment

**Closed in the working manuscript on 2026-09-03.** Lemma `lem:parametric-HLZ-diagonal` now writes the exact scalar Euler factor, starts from a uniformly absolutely convergent right line, and reproduces the truncated zero-free-region contour shift with arbitrary $K(0)$ and fixed polylogarithmic packet losses. See `doc/small_gap_parametric_HLZ_packet_weight_2026-09-03.md`.

---

## B2. Operator-level error versus entrywise HLZ error

The final proof needs the finite-model HLZ error in a common output form

\[
R_T^{\rm com}
=
\mathscr C_T^*M_{\varepsilon_T}\mathscr C_T,
\qquad
\|M_{\varepsilon_T}\|_{\rm op}=o(1),
\]

not merely

\[
|(R_T)_{rs}|\le o(1).
\]

The difference matters because the packet dimension is \(\asymp N_T\); an entrywise bound can lose a dimension factor.

This gap is largely coupled to A2. Once the exact source-level common-output factorization is established and the scalar HLZ error is uniform in the fibre variable, the operator lift is straightforward.

### Current assessment

**Closed as an independent operator-lift subgap, conditional on A2.** Lemma `lem:HLZ-output-reference-compatibility` now identifies the common-output unit Gram with the triangular reference geometry up to a fixed polylogarithmic factor on `V_mean`; the pair-independent finite-height endpoint shift factors through the global mean map and vanishes there. Lemma `lem:HLZ-diagonal-operator-lift` therefore obtains the relative operator bound before the sole final Hilbert--Schmidt dimension factor. This does not close A2 itself. See `doc/small_gap_HLZ_scalar_to_operator_lift_2026-09-03.md`.

---

## B3. Extension of direct-carrier square bounds into the exterior reserve

The direct-carrier square lemma was originally stated for \(x\le T\). The exterior packet reserve can push the effective coefficient range to

\[
x\le T L^C
\]

for fixed \(C\).

The proof appears to extend because

\[
\log(ex)\asymp L
\]

still holds and the factorial HLP majorant is unchanged up to fixed powers of \(L\).

Nevertheless, this should not remain as an informal "extends verbatim" statement if it feeds a new operator-HS estimate.

### Required closure

Restate the direct-carrier square lemma uniformly for

\[
x\le T L^C
\]

for every fixed \(C\), with the dependence of the polylog exponent made explicit.

### Current assessment

**Closed in the working manuscript on 2026-09-03.** Lemma `lem:direct-carrier-square` now holds uniformly for every fixed range \(x\le T L^{C_x}\), and the exterior-support proof invokes that strengthened statement directly. See `doc/small_gap_direct_carrier_polylog_extension_2026-09-03.md`.

---

# C. Interfaces currently looking substantially healthier

These are not certified correct merely because they appear below, but they are no longer the highest-priority gap candidates.

## C1. Smoothed AFE \(\to\) sharp critical-\(J\) fibre

The earlier concern that a smoothed approximate functional equation was silently replaced by a sharp cutoff has been substantially addressed.

The present manuscript explicitly uses a pure Mellin weight satisfying

\[
V(x)+V(x^{-1})=1
\]

and keeps:

- primal and dual gamma-ratio errors;
- the functional-equation multiplier error;
- the four remote polar residues;
- endpoint and parameter derivative control.

It then derives

\[
\mathcal E^J_{U,T}(A,B;\tau)
=
E_U(A+B)+\mathcal R^J_{U,T}
\]

with a quantitative derivative remainder.

### Current assessment

**Previous major gap appears substantially repaired. Continue checking normalization, but no longer Priority 1.**

---

## C2. Global spectral floor once \(G\) is accepted

The frozen kernel positivity is no longer inferred from pointwise scalar positivity. The manuscript uses the primitive identity and an explicit Schur bound.

Schematically,

\[
Q_G(q)
=
a_G\|Q\|_2^2
-
\iint g(1-|x-y|)Q(x)\overline{Q(y)}\,dxdy,
\]

with certified bounds yielding

\[
K_G\succeq0.06Q_\triangle.
\]

The main remaining danger is therefore upstream: whether the actual finite-model principal operator is indeed the pullback of this exact \(G\).

### Current assessment

**Internally strong, conditional on A1/A2.**

---

## C3. Finite-dimensional min--max / perturbation endgame

Given

\[
P_T\succeq c_0\mathfrak G_T,
\qquad
\operatorname{rank}E_T=o(N_T),
\qquad
\|\mathfrak G_T^{-1/2}R_T\mathfrak G_T^{-1/2}\|_{S_2}^2=o(N_T),
\]

the current inertia argument appears structurally coherent.

The generic affine perturbation is used at fixed \(T\), and Rouché is used to transfer the off-axis zero count back to the original function.

### Current assessment

**Not presently a leading gap candidate. Reaudit only after the analytic decomposition is closed.**

---

# D. External HLZ dependency boundary

The original HLZ arXiv source has now been extracted locally as

`external/HLZ_arxiv_2003.09368v1/hlz_original.tex`.

A critical distinction is required when citing it.

The diagonal lemma and its narrow zero-free-region contour shift are suitable for unconditional use. However, later in HLZ's own application they also move a different contour to

\[
\Re w=-1/4+\varepsilon
\]

under RH.

The present manuscript must use only the unconditional diagonal machinery and must not silently import the later RH-dependent evaluation.

### Current assessment

**No current evidence that the main route imports the RH-dependent step, but citations should make the boundary explicit.**

---

# E. Recommended audit order

The next work should be concentrated, not broad.

## Step 1: independently recompute the principal profile

Start from the original HLZ three-face formula and derive the manuscript's

\[
\mathscr G_{\lambda,\mu,\rho}(p)
\]

from scratch.

Do not assume the current Section 6 formula during this audit.

## Step 2: prove the exact pre-HLZ packet factorization

Establish the source-level identity that puts the packet labels only in the two one-sided factors and all HLZ/Cauchy dependence in a common scalar multiplier.

## Step 3: package a parametric HLZ lemma

State and prove the exact uniform variant needed for the packet Mellin class, including all finite derivatives used after curvature and Cauchy extraction.

## Step 4: perform a full source-exhaustion audit

For the complete exact--model residual, map every source term into exactly one of

\[
P_T,
\qquad
E_T^{\rm edge},
\qquad
R_T^{\rm tri}.
\]

Only after these four steps should the proof be regarded as ready for another end-to-end audit.

---

# F. Current severity table

| Priority | Interface | Assessment |
|---|---|---|
| 1 | Original HLZ / critical-\(J\) sources \(\to\) exact frozen profile \(G\) | **High risk / theorem-sized** |
| 2 | Physical packet source \(\to\) common scalar-HLZ output factorization | **Closed for the finite-model route 2026-09-03** |
| 3 | Complete \(\Delta H_{\rm dir}\) source exhaustion into edge + HS classes | **High risk / global theorem bookkeeping** |
| 4 | Parametric HLZ diagonal lemma for the packet Mellin class | **Closed 2026-09-03** |
| 5 | Operator-level HLZ error rather than entrywise error | **Closed conditional on the finite-model source factorization; no packet-dimension loss** |
| 6 | Exterior-reserve extension of carrier square bounds | **Closed 2026-09-03** |
| 7 | Smoothed AFE \(\to\) sharp \(J\) fibre | **Substantially repaired** |
| 8 | Global Schur spectral floor | **Strong conditional on correct profile** |
| 9 | Min--max / generic perturbation endgame | **Currently low concern** |

---

## Bottom line

The current density-one proof is no longer best described as being blocked by the old packet-valued HLZ hypothesis. That obstacle has been structurally removed.

The remaining theorem-sized uncertainty is now concentrated in two interfaces:

\[
\boxed{
\begin{aligned}
&\text{(1) exact derivation of the finite-model profile }G,\\
&\text{(2) exhaustive edge/HS ownership of the direct residual}.
\end{aligned}
}
\]

The finite-model source-level packet/HLZ factorization has been closed by the exact pre-HLZ lag-kernel separation and the common-output scalar-error lift. These two remaining interfaces should therefore be treated as the authoritative density-one gap list until they are independently closed or a new contradiction is found.
