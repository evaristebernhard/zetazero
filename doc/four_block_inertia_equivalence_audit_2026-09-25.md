# Four-block inertia equivalence route audit (2026-09-25)

## Purpose

This note reorganizes the structural equivalences suggested by the corrected
four-block contour identity and the latest finite computations.

The main point is that the theorem-facing object should be the **complete
closed-contour form**, not the spectrum of (A_T^{\rm true}) in isolation.
Several transformations below are exact algebraic identities. Others are only
generic/asymptotic consequences already present in the manuscript, and the
generalized Nevanlinna / Krein--Langer interpretation remains a proposed route.

Status labels used below:

- **EXACT**: follows algebraically from definitions already in the manuscript.
- **GENERIC EXACT**: exact after the standard real-symmetric generic
  perturbation used in Section 14.
- **ASYMPTOTIC (proved in current manuscript)**: uses the current
  (N(Z_1)-N(\zeta)=o(N_T)) zero-count decrement and endpoint bookkeeping.
- **CANDIDATE**: mathematically compatible with the exact identities but still
  needs a new theorem before it can be used in the proof.

No claim in this note changes the current conditional status of the main
theorem.

---

## 1. The four blocks recombine to one vertical Hardy source

**Status: EXACT.**

The current normalized contour identity is

[
A_F
=
A_T^{\rm true}
+L_T^{\rm geom}
+J_T^{\rm arch}
+R_T^{\rm exact},
]

with

[
R_T^{\rm exact}=R_T^{f'}+R_T^{\rm hor,H}.
]

Write

[
\mathcal C=\zeta^2Q,
\qquad
H_{\rm ar}=-P+\frac{Q}{f-P},
]

and on the right edge define

[
D_{\rm ar}=\mathcal C H_{\rm ar},
]

[
D_f=f(\mathcal C+f'\zeta^2),
]

[
D_{f'}
=
\frac{f'}{f-P}\mathcal C
+f'\zeta^2H_{\rm ar}
+\frac{(f')^2}{f-P}\zeta^2.
]

Since

[
H=f+H_{\rm ar}+\frac{f'}{f-P}
=\frac{\mathscr Z''}{\mathscr Z'},
]

and

[
C_{\mathscr Z}^{\rm norm}
=
\frac{q^2}{L^2}(\mathcal C+f'\zeta^2),
]

one has pointwise

[
H C_{\mathscr Z}^{\rm norm}
=
\frac{q^2}{L^2}
(D_{\rm ar}+D_f+D_{f'}).
]

Therefore the complete vertical contribution is

[
V_T:=
A_T^{\rm true}
+L_T^{\rm geom}
+J_T^{\rm arch}
+R_T^{f'},
]

and

[
\boxed{A_F=V_T+R_T^{\rm hor,H}.}
]

This is the first simplification: the four-block split is bookkeeping.  The
vertical part comes from one Hardy source.  In particular, no individual sign
interpretation should be assigned to (A_T^{\rm true}), (J_T^{\rm arch}),
or any other partial sum before an additional argument is proved.

The finite spectra in `numerical.tex` strongly support this warning: large
negative index can appear in intermediate sums and disappear after the missing
blocks are restored.

---

## 2. Collapse the full source with (X=\mathscr Z'/\mathscr Z)

**Status: EXACT.**

Put

[
X(s):=\frac{\mathscr Z'(s)}{\mathscr Z(s)}
=f(s)-P(s)
=\frac{Z_1(s)}{\zeta(s)}.
]

Then

[
X'=f'+Q,
]

[
C_{\mathscr Z}
=
\mathscr Z\mathscr Z''
-(\mathscr Z')^2
=
\mathscr Z^2X',
]

and

[
H=\frac{\mathscr Z''}{\mathscr Z'}
=
X+\frac{X'}{X}.
]

Hence

[
\boxed{
H C_{\mathscr Z}
=
\mathscr Z^2X'
\left(
X+\frac{X'}{X}
\right).
}
]

Equivalently,

[
H C_{\mathscr Z}
=
\mathscr Z\frac{(\mathscr Z'')^2}{\mathscr Z'}
-
\mathscr Z'\mathscr Z''.
]

Since

[
\mathscr Z'\mathscr Z''
=
\frac12\bigl((\mathscr Z')^2\bigr)',
]

we get

[
\boxed{
H C_{\mathscr Z}
=
\mathscr Z\frac{(\mathscr Z'')^2}{\mathscr Z'}
-
\frac12\bigl((\mathscr Z')^2\bigr)'.
}
]

On the high rectangle all factors in the second term, including the packet
polarization, are holomorphic.  Therefore its closed contour integral is zero.
Consequently the complete closed-contour form is equivalently controlled by
the meromorphic pole term

[
\mathscr Z\frac{(\mathscr Z'')^2}{\mathscr Z'}.
]

This is exactly the structure that becomes the stationary-residue kernel after
straightening.

---

## 3. Straightening gives the stationary residue form

**Status: EXACT / GENERIC EXACT.**

Let

[
F(z):=\mathscr Z\left(\frac12+iz\right).
]

Then (F(\bar z)=\overline{F(z)}), so (F) is real on the real axis, and
the same contour form becomes

[
\boxed{
\mathcal A_F(h_1,h_2)
=
\frac{1}{2\pi i}
\int_{\partial\Omega_T}
L^{-2}
\left(
-F(z)\frac{F''(z)^2}{F'(z)}
\right)
h_2(z)h_1^\#(z)\,dz.
}
]

For a generic real-symmetric perturbation (G) with simple stationary points,
the only poles are the zeros of (G').  At a real stationary point (c),

[
\operatorname{Res}_{z=c}
L^{-2}
\left(
-G\frac{G''^2}{G'}
\right)
=
-L^{-2}G(c)G''(c).
]

Thus a real stationary point contributes one negative direction exactly when

[
G(c)G''(c)>0.
]

A nonreal conjugate stationary pair contributes a (2\times2) Hermitian
block with one positive and one negative eigenvalue.

With the packet evaluation map chosen surjective as in Section 02, Sylvester
inertia gives the exact generic identity

[
\boxed{
n_-(A_G)=B(G)+P(G'),
}
]

where (B(G)) counts the bad real stationary points and (P(G')) the nonreal
conjugate pairs of zeros of (G').

This is already the correct sense in which the **number** of negative
directions is rigid while their magnitudes are irrelevant.

---

## 4. The residue form is naturally encoded by (M=F/F')

**Status: EXACT at the contour/residue level.**

Define

[
M(z):=\frac{F(z)}{F'(z)}.
]

Because (F^\#=F), multiplication by (F'') respects the reflected test
function.  Hence

[
\boxed{
\mathcal A_F(h_1,h_2)
=
-
\frac{1}{2\pi iL^2}
\int_{\partial\Omega_T}
M(z)
\,[F''h_2](z)
\,[F''h_1]^\#(z)
\,dz.
}
]

At every simple zero of (F'), (F''\neq0).  Therefore multiplication by
(F'') is an invertible diagonal congruence on the stationary residue
coordinates.  The inertia of the original contour residue form is thus the
inertia of the corresponding pole-residue form of (-M).

For a real simple stationary point,

[
\operatorname{Res}_{z=c}M(z)
=
\frac{F(c)}{F''(c)}.
]

The bad-point condition satisfies

[
F(c)F''(c)>0
\quad\Longleftrightarrow\quad
\operatorname{Res}_{c}M>0.
]

So the sign defect is encoded directly in the real pole residues of (F/F').

### What is not yet proved

The exact identity above is a **contour residue statement**.  It is not yet a
proof that the manuscript matrix is literally a finite compression of the
standard generalized Nevanlinna Pick kernel

[
K_M(z,w)
=
\frac{M(z)-\overline{M(w)}}{z-\bar w}.
]

There is, however, an exact Bezoutian identity

[
K_M(z,w)
=
\frac{
F(z)\overline{F'(w)}
-F'(z)\overline{F(w)}
}{
F'(z)\overline{F'(w)}(z-\bar w)
}.
]

Thus the proposed generalized Nevanlinna interpretation is structurally
natural, but a local theorem matching the sign convention, pole
multiplicities, boundary truncation, and the packet residue form is still
needed.

Generalized Nevanlinna theory defines the class (N_\kappa) through kernels
with exactly (\kappa) negative squares, and generalized Schur functions have
Krein--Langer factorizations by finite Blaschke products.  Those facts motivate
the route; they are not inserted here as a proved identification for this
specific (F/F').

---

## 5. Cayley / Hermite--Biehler variables

**Status: EXACT algebra.**

Define

[
E(z):=F(z)+iF'(z),
\qquad
E^\#(z)=F(z)-iF'(z).
]

Because

[
F'(z)=i\mathscr Z'(s),
\qquad
s=\frac12+iz,
]

we have

[
E(z)
=
\mathscr Z(s)-\mathscr Z'(s)
=
\mathscr Z(s)(1-X(s)),
]

and

[
E^\#(z)
=
\mathscr Z(s)+\mathscr Z'(s)
=
\mathscr Z(s)(1+X(s)).
]

Therefore

[
\boxed{
\Theta(z)
:=
\frac{E^\#(z)}{E(z)}
=
\frac{1+X(s)}{1-X(s)}.
}
]

For real (z), (F,F'\in\mathbb R), hence

[
|\Theta(z)|=1
]

whenever the quotient is defined.

This is exactly the algebraic shape of a Hermite--Biehler / Schur Cayley
transform.  Ordinary de Branges theory would ask (E) to be
Hermite--Biehler, while a generalized Schur version allows a finite
negative-square defect.  Membership in a particular generalized Schur class is
**not proved here**.

---

## 6. The curvature is a Wronskian of the two Cayley factors

**Status: EXACT.**

In (s)-coordinates put

[
Y_+(s):=\mathscr Z(s)+\mathscr Z'(s)
=\mathscr Z(1+X),
]

[
Y_-(s):=\mathscr Z(s)-\mathscr Z'(s)
=\mathscr Z(1-X).
]

With the convention

[
W_*(Y_+,Y_-):=Y_+'Y_- -Y_+Y_-',
]

a direct calculation gives

[
\boxed{
W_*(Y_+,Y_-)
=
2\left(
\mathscr Z\mathscr Z''
-(\mathscr Z')^2
\right)
=
2C_{\mathscr Z}.
}
]

Also,

[
\boxed{
\frac{d}{ds}
\log\frac{Y_+}{Y_-}
=
\frac{2X'}{1-X^2}.
}
]

Thus the curvature used by the contour construction is naturally the
Wronskian of the two functions appearing in the Cayley transform.  This is a
more coherent structural description than assigning separate spectral meaning
to the four right-edge bookkeeping blocks.

---

## 7. Poles of the Cayley transform become a Levinson-type auxiliary function

**Status: EXACT algebra; zero-count equivalence still needs boundary control.**

A pole of (\Theta) in the upper (z)-half-plane is a zero of

[
E=F+iF',
]

hence, in (s=1/2+iz),

[
X(s)=1.
]

The upper (z)-half-plane corresponds to the left half of the (s)-strip.
The Hardy reflection gives

[
X(1-\bar s)=-\overline{X(s)}.
]

Therefore a left-side solution (X=1) reflects to a right-side solution

[
X=-1.
]

On the right side,

[
X=-1
\quad\Longleftrightarrow\quad
\frac{Z_1}{\zeta}=-1
\quad\Longleftrightarrow\quad
Z_1+\zeta=0.
]

Since (Z_1=\zeta'+f\zeta),

[
\boxed{
G_+(s):=
\zeta'(s)+(f(s)+1)\zeta(s)=0.
}
]

Equivalently, where (f+1\neq0),

[
\boxed{
\widetilde G_+(s)
=
\zeta(s)+\frac{\zeta'(s)}{f(s)+1}.
}
]

For (t\asymp T),

[
f(s)
=
\frac12\log\frac{t}{2\pi}
+O(1),
]

so the normalized function is of the same structural type as the classical
Levinson auxiliary combinations

[
\zeta(s)+O\!\left(\frac1{\log T}\right)\zeta'(s).
]

This observation does **not** supply a zero-density theorem for (G_+); it
identifies the scalar function that the Cayley route would have to control.

---

## 8. A homotopy route from (F) to (F+iF')

**Status: CANDIDATE lemma; local mechanism is elementary, dyadic boundary
control is still required.**

Consider

[
E_a(z):=F(z)+iaF'(z),
\qquad 0<a\le1.
]

For real (x),

[
E_a(x)=0
\quad\Longrightarrow\quad
F(x)=F'(x)=0.
]

Thus for a generic (F) with simple real zeros, no zero of (E_a) can cross
the real axis as (a) varies.

Near a simple real zero (x_j) of (F),

[
F(z)=F'(x_j)(z-x_j)+O((z-x_j)^2),
]

so

[
E_a(z)=0
\quad\Longrightarrow\quad
z=x_j-ia+O(a^2).
]

Hence real zeros move initially into the **lower** half-plane, while nonreal
upper-half-plane zeros of (F) persist under sufficiently small (a).

On any fixed bounded domain whose remaining boundary is zero-free for all
(a\in[a_0,1]), the argument principle then makes the upper-half-plane zero
count of (E_a) homotopy invariant.  To use this on the dyadic rectangle one
still has to control zeros crossing the vertical/height boundaries as (a)
varies.

So the desired statement

[
N_{\mathbb C_+}(F+iF')
=
N_{\mathbb C_+}(F)
+o(N_T)
]

is a plausible concrete target, **not yet a theorem of the repository**.

---

## 9. The manuscript already identifies inertia with off-axis zero pairs
asymptotically

**Status: ASYMPTOTIC, proved in the current manuscript after generic
perturbation.**

For the generic perturbation (G),

[
n_-(A_G)=B(G)+P(G').
]

The current good-rectangle zero-count decrement gives

[
N(G')-N(G)=o(N_T).
]

Writing

[
N(G)=R(G)+2D(G),
\qquad
N(G')=R(G')+2P(G'),
]

and using the real Rolle bookkeeping

[
R(G')=R(G)+2B(G)+O(1),
]

one obtains

[
\boxed{
D(G)
=
B(G)+P(G')
+o(N_T)
=
n_-(A_G)+o(N_T).
}
]

This is already Lemma `generic-zero-count` in Section 14.

Therefore the contour negative index is, up to the already controlled
(o(N_T)) bookkeeping, the number of reflected nonreal zero pairs.  The new
Cayley/Levinson route should be viewed as a possible **alternative scalar
encoding of this same integer defect**, not as an additional independent
conclusion.

---

## 10. What is actually equivalent, and what is only proposed

The safest current chain is

[
\boxed{
\begin{array}{c}
\text{four-block closed contour matrix}
\\[2mm]
\Updownarrow\quad\text{EXACT}
\\[2mm]
\text{complete Hardy source }HC_{\mathscr Z}
\\[2mm]
\Updownarrow\quad\text{EXACT}
\\[2mm]
-F\,F''^2/F'\text{ stationary pole form}
\\[2mm]
\Updownarrow\quad\text{GENERIC EXACT}
\\[2mm]
B(G)+P(G')
\\[2mm]
=\quad\text{ASYMPTOTIC in current manuscript}
\\[2mm]
D(G)+o(N_T).
\end{array}
}
]

A second, proposed chain starts from the same pole form:

[
\boxed{
\begin{array}{c}
-F\,F''^2/F'
\\[2mm]
\longleftrightarrow\quad\text{EXACT residue congruence}
\\[2mm]
M=F/F'
\\[2mm]
\dashrightarrow\quad\text{CANDIDATE local theorem}
\\[2mm]
\text{generalized Nevanlinna negative squares}
\\[2mm]
\dashrightarrow\quad\text{CANDIDATE Krein--Langer localization}
\\[2mm]
\text{Blaschke / generalized Schur defect of }
\Theta=\dfrac{1+X}{1-X}
\\[2mm]
\dashrightarrow\quad\text{needs homotopy + boundary control}
\\[2mm]
N_{\Re s>1/2}(G_+).
\end{array}
}
]

The dashed arrows are the new research problem.  They must not be used as
proved steps in the main theorem yet.

---

## 11. Consequence for the current research strategy

The finite data and exact algebra both argue against treating
(A_T^{\rm true}) as a separately positive principal matrix.  A more coherent
route is:

1. keep the complete four-block contour form intact;
2. use the exact collapse to the stationary pole form;
3. treat negative inertia as a **counting** invariant rather than a
   negative-energy magnitude;
4. investigate whether the residue form admits a local generalized
   Nevanlinna/Bezoutian theorem;
5. in parallel, study the concrete auxiliary function

   [
   G_+(s)=\zeta'(s)+(f(s)+1)\zeta(s)
   ]

   and test whether its right-half-strip zero count tracks the contour negative
   index up to endpoint corrections.

A successful proof of

[
N_{G_+}\left(
\frac12<\sigma<2,\ T<t<2T
\right)
=o(N_T)
]

together with the missing homotopy/negative-square bridge would give exactly
the type of information wanted here: an (o(N_T)) count of bad directions,
with no need to bound how negative the corresponding eigenvalues are.

At present this is a **reformulation program**, not an unconditional proof.

---

## 12. Immediate numerical and analytic checks

The next useful checks are more targeted than raw eigenvalue plots.

1. Extend the original-contour script to compute zeros of
   (G_+=Z_1+\zeta) in the same good rectangle.
2. Compare
   - (n_-(A_F)),
   - the number of nonreal stationary pairs of (F'),
   - the number of right-half-strip zeros of (G_+),
   on the same finite contour.
3. Track these counts under the homotopy (E_a=F+iaF').
4. Check whether any changes occur only through the top/bottom boundary
   collars.
5. Only after that numerical audit, formulate a local generalized
   Nevanlinna/Bezoutian lemma with exactly the sign convention needed by the
   contour residue form.

This route deliberately avoids using the magnitude of negative eigenvalues as
the primary invariant.
