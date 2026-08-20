# Main manuscript unconditional-route modification and audit

Date: 2026-08-20

Status: **MAIN PROOF DEPENDENCY HAS BEEN REORGANIZED SO THAT `hyp:packet-bilinear-HLZ` IS NOT USED BY THE MAIN THEOREM.  THE INTERNAL SOURCE LEDGER, LATEX BUILD, SYMBOLIC CERTIFICATES, AND ALL NON-BLUEPRINT LEAN TESTS PASS.  THIS IS AN INTERNAL CONSISTENCY / DEPENDENCY AUDIT, NOT INDEPENDENT EXTERNAL VALIDATION OF A NEW DENSITY-ONE THEOREM.**

---

## 1. Why the manuscript was changed

The previous main proof sent the exact low HLP hierarchy through a stronger packet-valued completion hypothesis

\[
\texttt{hyp:packet-bilinear-HLZ},
\]

whose clauses asserted:

1. exact source ownership by the scalar three-\(Z\) master;
2. contraction of the internal HLP Dirichlet carrier inside a common packet output;
3. a packet-dimension-free lift of scalar HLZ/Perron contour errors.

The parallel audit showed that this is stronger than what the inertia endgame actually needs.  The exact source already admits an algebraic split on the original absolute-convergence right edge which separates a **finite model principal source** from a **direct physical exact--model residual**.  Once this split is made before any exact-HLP local Perron projection, the strong packet-valued hypothesis is unnecessary.

---

## 2. Authoritative exact source split

On a retained height block let

\[
F_b=f(1/2+i\tau_b),
\]

and retain the exact pointwise source

\[
\widehat H_{\rm ex}(s)
=f(s)-P(s)+\frac{Q(s)}{f(s)-P(s)}.
\]

The finite model is

\[
H_{\rm mod}(s;F_b)
=F_b-2P(s)+P(s-2/L).
\]

Define the direct exact--model residual

\[
\boxed{
\Delta H_{\rm dir}(s)
:=P(s)+\frac{Q(s)}{f(s)-P(s)}-P(s-2/L).
}
\]

Then, literally on the safe right edge,

\[
\boxed{
\widehat H_{\rm ex}(s)
=H_{\rm mod}(s;F_b)
+\Delta H_{\rm dir}(s)
+\bigl(f(s)-F_b\bigr).
}
\]

This identity is the source-level organizing principle of the revised final proof.

Its three owners are now mutually exclusive:

| source | final owner |
|---|---|
| finite model \(H_{\rm mod}\) | critical-\(J\) self + scalar HLZ three-\(Z\) logarithmic-derivative faces; principal operator \(P_T\) |
| direct residual \(\Delta H_{\rm dir}\) | physical one-\(\chi\) carrier; low sidebands \(E_T^{\rm edge}\), high sidebands/nonstationary terms \(R_T\) |
| self freezing \(f-F_b\) | small critical-\(J\) regular remainder only |

No exact HLP level is simultaneously represented in \(P_T\) and in a direct sideband family.

---

## 3. Finite model: what uses HLZ and what does not

The finite model has two analytically different components.

### 3.1 Critical-\(J\) self face

The frozen self coefficient \(F_b\) is inherited from the exact critical-\(J\) contour identity.  It is **not** an HLZ three-\(Z\) face.

### 3.2 Logarithmic-derivative faces

The source

\[
-2P(s)+P(s-2/L)
\]

is evaluated by the scalar Heap--Li--Zhao three-\(Z\) construction.  The manuscript retains the separated Cauchy tori, the finite three-face residue identity, and the scalar diagonal contour estimate with arbitrary logarithmic saving.

The finite model principal faces are then reassembled by the common-core congruence into the scalar lag profile

\[
\mathscr G_{\lambda,\mu,\rho}(p)
=e^{\lambda p}
\left[
\mu E_\rho(2p)-2E_\rho(p)^2
+e^{2\lambda}E_\rho(p+2)E_\rho(p-2)
\right].
\]

The existing global model certificate and finite-\(T\) perturbation remain unchanged:

\[
A_T^G\succeq0.06\,\mathfrak G_T,
\qquad
\|\mathfrak G_T^{-1/2}(P_T-A_T^G)\mathfrak G_T^{-1/2}\|_{\rm op}
\ll L^{-1},
\]

hence, for sufficiently large \(T\),

\[
P_T\succeq c_0\mathfrak G_T,
\qquad c_0=0.03
\]

is still available.

---

## 4. New unconditional finite-model packet lift

A new lemma

`lem:model-HLZ-Fubini-lift`

has been inserted for the finite-model three-\(Z\) faces.

Before scalar HLZ deformation, for a packet pair \(r,s\) the weight is kept in the exact one-sided form

\[
W_{rs,L}(u,\mathbf z)
=\int_{J_{rs}}
 b_{s,T}(t)\overline{b_{r,T}(t)}
 c_T(t,\mathbf z)e^{Lut}\,dt,
\qquad
J_{rs}=I_r\cap I_s.
\]

The packet labels occur only in the two one-sided factors.  The auxiliary Cauchy shifts and Mellin variable occur only in the common scalar multiplier.

For each fixed fibre slice \(t\), the scalar HLZ identity applies to

\[
c_T(t,\mathbf z)e^{Lut}
\]

uniformly on the deformation strip.  Since the scalar contour identity is linear in the inserted analytic auxiliary weight, Fubini yields

\[
\mathscr C_T^*M\mathscr C_T
\]

for both the finite-model scalar main term and its scalar contour error.  Finite physical-shift Cauchy residues act only on the common scalar multiplier.

Therefore no packet-dimension loss is incurred before the final Hilbert--Schmidt conversion.

---

## 5. Exact HLP hierarchy remains direct

On the fixed safe right edge,

\[
\frac{Q}{f-P}
=\sum_{k\ge1}f^{-k}P^{k-1}Q
\]

is absolutely convergent.

The current direct-carrier lemma proves that multiplication of the Dirichlet series only changes the coefficient of the total positive integer index \(M\).  The physical one-\(\chi\) saddle and phase remain

\[
t_*=2\pi My,
\qquad
 e(-My).
\]

The factorial square-sum estimate gives, uniformly over the full hierarchy,

\[
\left(\sum_{m\le x}|f^{-k}\alpha_k(m)|^2\right)^{1/2}
\ll (xL)^{1/2}\frac{C^k}{\sqrt{k!}},
\]

and therefore

\[
\sum_{k\ge1}
\frac{C^k(1+k)^q}{\sqrt{k!}}<\infty
\]

for every fixed curvature derivative order \(q\).

The direct-carrier square bound is now stated for the **full norm-summable HLP hierarchy**, not only \(k>K_0\).

---

## 6. Edge rank for the whole exact--model residual

The shell edge-rank proposition is coefficient-free: for arbitrary coefficients and signs, all retained low-sideband shifts on a shell have range in the same fixed edge coordinate space.

It also applies to norm-convergent sums because every partial sum has range in that same space.

Consequently the full direct residual, including

- the complete HLP hierarchy;
- the ordinary \(+P(s)\) term;
- the translated coefficient shift \(-P(s-2/L)\),

has low-sideband rank

\[
\boxed{
\operatorname{rank}E_T^{\rm shift}\ll T=o(N_T).
}
\]

After boundary and terminal-tail edge terms are included, the existing global estimate remains

\[
\boxed{
\operatorname{rank}E_T^{\rm edge}
\ll T\log L=o(N_T).
}
\]

No centering assumption is used in this rank argument.

---

## 7. High sidebands and nonstationary residual

The stationary-symbol lemma already treats the **summed exact HLP hierarchy** uniformly.  It constructs a uniformly smooth height symbol after the universal carrier is extracted and proves fixed-order derivative bounds independent of the HLP level sum.

Together with the direct-carrier square bound, this supplies the two inputs to the high-sideband Hilbert--Schmidt estimate:

1. coefficient \(\ell^2\) control;
2. arbitrary fixed-order Fourier decay of the shell symbol.

The regular ledger has therefore been rewritten so that class (vii) contains the high sidebands of the entire direct residual.

The same height-symbol argument, before stationary expansion, also gives the required fixed derivative bounds in the nonstationary sector.  The regular ledger now states this explicitly before invoking repeated integration by parts.

---

## 8. Terminal logarithmic tail audit

The terminal band

\[
W_T<u\le L
\]

is independent of the old exact-HLP local-projector organization.

Its stationary portion is controlled by geometric row count and hence is independent of source coefficients.  For the full direct residual, the direct-carrier square bound and uniform HLP height-symbol estimate contribute only fixed polylogarithmic losses, which have now been stated explicitly in the terminal-tail proof.

Thus

\[
\operatorname{rank}E_T^{\rm tail}\ll T\log L=o(N_T)
\]

and

\[
\|\mathfrak G_T^{-1/2}R_T^{\rm tail}
\mathfrak G_T^{-1/2}\|_{S_2}^2=o(N_T)
\]

continue to hold for the new source organization, including core--tail cross terms.

---

## 9. Critical-J self freezing is independent of HLP projection

The previous block-freezing lemma mixed two logically different statements.  The final route needs only the self term.

A new explicit estimate has therefore been inserted:

`eq:self-freezing-kernel`.

Since the normalized critical-\(J\) self coefficient is \(2f/L\) and

\[
|f(c+it)-F_b|\ll L^{-D},
\]

one obtains, independently of any HLP local projector,

\[
\boxed{
\partial_\rho^r\partial_p^q
\bigl(K_{J,{\rm var},b}-K_{J,{\rm fr},b}\bigr)
=O(L^{-D-1+C_{\rm fr}}),
\qquad r,q\le2.
}
\]

The same estimate holds for the diagonal derivative jump.  This is the only freezing estimate used by the final source ledger.

The older low-level HLP freezing/local-comparison estimate remains only in the optional comparison subsection.

---

## 10. Common scalar HLZ error lift

The regular ledger class (ix) now contains only the finite-model scalar HLZ diagonalization error.

By the Fubini lift it has the form

\[
R_T^{\rm com}
=\mathscr C_T^*M_{\varepsilon_T}\mathscr C_T,
\]

with

\[
\|\varepsilon_T\|_\infty
\ll \varepsilon_{\rm diag}=o(1).
\]

Hence, on the output Gram support,

\[
\|G_{\rm out}^{-1/2}R_T^{\rm com}G_{\rm out}^{-1/2}\|_{\rm op}
\le \|\varepsilon_T\|_\infty.
\]

After the fixed local-to-global Gram comparison and compression to \(O(N_T)\) dimensions,

\[
\boxed{
\|\mathfrak G_T^{-1/2}R_T^{\rm com}
\mathfrak G_T^{-1/2}\|_{S_2}^2
\ll N_T\varepsilon_{\rm diag}^2=o(N_T).
}
\]

There is no exact-HLP levelwise Perron connector in the final route.

---

## 11. What happened to the old exact-HLP local projector

The following machinery remains in the manuscript:

- `hyp:packet-bilinear-HLZ`;
- `lem:internal-principal-contraction`;
- `lem:cluster-levelwise`;
- `eq:no-exact-translated-poles`;
- `eq:levelwise-Perron-deformation`;
- exact/leading/model local Laurent comparison.

It is now explicitly marked as an **optional stronger exact-HLP local comparison route**.

A dependency search confirms that none of these is referenced by the final source ledger or endgame.  In particular:

- `sections/11_reference_remainder.tex`: no `Hypothesis` occurrence;
- `sections/14_endgame.tex`: no main-theorem hypothesis assumption;
- `internal-principal-contraction`: only its optional definition remains;
- `levelwise-Perron-deformation`: only its optional Section 7 lemma/proof remains;
- `no-exact-translated-poles`: only optional Section 6/7 route remains.

The optional hypothesis is retained as research documentation, not as a theorem assumption.

---

## 12. Final source ledger after modification

The current final proof uses the exact algebraic operator definition

\[
R_T^{\rm tri}:=A_T-P_T-E_T^{\rm edge}
\]

and verifies the following ownership:

| class | owner |
|---|---|
| principal finite model | \(P_T\) |
| exact--model residual, low sidebands | \(E_T^{\rm edge}\) |
| exact--model residual, high sidebands | regular class (vii) |
| critical-J self freezing \(f-F_b\) | regular class (ii) |
| \(f'\) source | regular class (iii) |
| horizontal connectors | regular class (iv) |
| finite-model stationary/Stirling corrections | regular class (v) |
| nonstationary / smooth height partition | regular class (vi), endpoint jets to edge |
| exact-HLP local projection remainder | absent in final route |
| exact-HLP local holomorphic/Perron complement | absent in final route |
| finite-model scalar HLZ contour error | regular class (ix) |
| terminal logarithmic tail | stationary/endpoint edge + nonstationary regular |
| auxiliary outer arithmetic annulus | absent by trivial outer twist |

This is acyclic: every source is assigned exactly once.

---

## 13. Main theorem and title changes

The manuscript title is now

> **A Hardy-Gauge Contour Method for Density One of Zeta Zeros on the Critical Line**

The main theorem is now stated as

> **Density one on the critical line**

without `Assume Hypothesis~\ref{hyp:packet-bilinear-HLZ}`.

The abstract and introduction were rewritten to describe the actual proof organization:

\[
\text{critical-J + finite scalar three-Z model}
\quad+\quad
\text{direct exact--model residual}.
\]

The endgame no longer assumes the optional packet-HLZ hypothesis.

---

## 14. Canonical proof guard was updated

`test_compile.py::test_canonical_proof_guards` now requires the new route:

- unconditional `Density one on the critical line` theorem title;
- `lem:model-HLZ-Fubini-lift`;
- `eq:direct-exact-model-residual`;
- `eq:direct-model-source-split`;
- `eq:self-freezing-kernel`.

It no longer treats the following optional machinery as canonical requirements:

- packet-HLZ hypothesis;
- levelwise exact-HLP Perron deformation;
- exact translated-pole exclusion;
- exact local principal projector.

It also forbids reintroduction of the previous conditional theorem title / abstract wording.

---

## 15. Verification matrix

### 15.1 Main verification suite

The following command was run after the final source edits:

```text
npm test -- global-floor source-profile proof-guards lean lean-all hlp-meansquare gcd-gram mainline-bridge previous-unverified straightening stationary-oscillatory latex
```

Result:

```text
12 passed
```

The passing checks are:

1. global floor certificate;
2. source-profile symbolic certificate;
3. canonical proof guards;
4. Lean default build;
5. all Lean modules build;
6. HLP mean-square/factorial modules;
7. GCD/Gram modules;
8. Hardy/stationary mainline bridge;
9. previously unverified formal modules;
10. straightening bridge;
11. stationary oscillatory modules;
12. LaTeX compilation.

### 15.2 LaTeX audit

The LaTeX test runs `pdflatex` three times with

```text
-interaction=nonstopmode -halt-on-error
```

and rejects:

- undefined control sequences;
- any LaTeX warning;
- any hyperref warning;
- overfull hbox/vbox.

It passes cleanly.

### 15.3 Blueprint declaration check

The only failing project check is

```text
npm test -- blueprint-decls
```

with

```text
object file '/home/ubuntu/zetazero/.lake/build/lib/lean/Zeta23.olean'
of module Zeta23 does not exist
```

This is a module-layout/build-artifact issue in `checkdecls`, not a failure of the paper proof chain or of a Lean theorem introduced by the manuscript changes.

The local source root

```text
zeta-23-lean/Zeta23.lean
```

exists, and the explicit project target

```text
npm run build:zeta23-hardy
```

succeeds (`Build completed successfully`, 3612 jobs).  The project `lakefile.toml` declares

```text
[[lean_lib]]
name = "Zeta23"
srcDir = "zeta-23-lean"
```

but `checkdecls` still looks for the root-workspace object path above.  No `.olean` file was copied or fabricated merely to force the check to pass.

---

## 16. External scalar HLZ input audit

The scalar external input was checked against Heap--Li--Zhao, *Lower bounds for discrete negative moments of the Riemann zeta function*, arXiv:2003.09368 / Algebraic Number Theory 16 (2022), 1589--1625.

The relevant external content is:

1. their twisted discrete moment theorem gives an arbitrary-log error term;
2. their formula (28) is the finite three-face Cauchy residue identity used for the three \(Z\) faces;
3. their diagonal lemma introduces an analytic auxiliary \(H\) with \(H(0)=1\), zeros at the moving divisors, and Gaussian vertical decay;
4. the contour argument is linear in the inserted analytic auxiliary function, so multiplying the auxiliary by a uniformly controlled scalar Mellin weight changes the residue by its value at zero and preserves the contour structure;
5. after the invariant-source specialization, the auxiliary outer twist is \(h=k=1\).

What the external paper does **not** supply is the old stronger statement that the complete exact HLP resolvent hierarchy automatically contracts into one packet-valued three-Z output.  The revised proof no longer asks it to do so.

---

## 17. Files whose main-proof content was modified in this audit

The current proof organization was changed in or propagated through:

- `main.tex`;
- `sections/00_main_theorem.tex`;
- `sections/06_threeZ_common_prefix.tex`;
- `sections/07_hlp_local_replacement.tex`;
- `sections/08_global_model_floor.tex`;
- `sections/10_shell_edge.tex`;
- `sections/11_reference_remainder.tex`;
- `sections/12_retained_space.tex`;
- `sections/14_endgame.tex` (the previous conditional assumption was removed, returning that line to the unconditional endgame form);
- `test_compile.py`.

The workspace contains many other pre-existing modified/untracked research and Lean files.  They were not reset or overwritten as part of this audit.

---

## 18. Current assessment

The strongest justified internal statement after this modification is:

\[
\boxed{
\texttt{THE MAIN MANUSCRIPT NO LONGER DEPENDS ON THE PACKET-VALUED HLZ HYPOTHESIS.}
}
\]

The final dependency graph is now

\[
\boxed{
\begin{aligned}
\text{exact contour}
&\longrightarrow
\text{safe-line exact source split}\\
&\longrightarrow
\begin{cases}
\text{finite model: critical-J + scalar HLZ + Fubini},\\
\text{direct residual: low-rank/high-HS sidebands},\\
\text{self freezing: small regular},
\end{cases}\\
&\longrightarrow
A_T=P_T+E_T^{\rm edge}+R_T^{\rm tri}\\
&\longrightarrow
P_T\succeq c_0\mathfrak G_T,\quad
\operatorname{rank}E_T^{\rm edge}=o(N_T),\quad
\|\mathfrak G_T^{-1/2}R_T^{\rm tri}\mathfrak G_T^{-1/2}\|_{S_2}^2=o(N_T)\\
&\longrightarrow
\text{finite-dimensional inertia endgame.}
\end{aligned}
}
\]

All internally executable checks except the independent blueprint module-path check pass.

However, the conclusion claimed by the manuscript is a major result in analytic number theory.  Passing internal symbolic checks, Lean modules for supporting sublemmas, LaTeX compilation, and a line-by-line dependency audit is **not equivalent to independent expert verification of the entire analytic argument**.  Before treating the theorem as externally established, the revised source split and in particular the finite-model scalar-HLZ/Fubini transfer and the direct-residual sideband exhaustion should be read independently by specialists with no dependence on this audit.

---

## 19. Recommended next audit

The next useful action is no longer to add another local lemma.  It is an adversarial independent reread of exactly four interfaces:

1. the exact Hardy-gauge contour -> right-edge source separation;
2. critical-J self + scalar three-Z finite-model reassembly and relative normalization;
3. the claim that every term of \(\Delta H_{\rm dir}\) stays in the direct one-\(\chi\) shell geometry through the complete stationary/nonstationary partition;
4. the final finite-dimensional inertia count and multiplicity bookkeeping.

Those four interfaces now contain essentially all remaining theorem-sized risk.
