# Generic principal-part / negative-square equivalence audit (2026-09-25)

## Scope

This note records a fully audited **generic zero-side re-encoding** of the
stationary inertia already used in the manuscript.

It deliberately does **not** claim that the original four-block matrix
\(A_F\) has the same inertia as the object below. The exact four-block identity
belongs to the unperturbed Hardy-gauge function \(F\). The negative-square
equivalence in this note begins only after the existing generic perturbation
of Section 14,

\[
H(z)=F(z)+\eta z+\varepsilon,
\]

has made the zeros of \(H'\) simple and removed common zeros of \(H,H'\).

Thus the correct logical chain is

\[
A_F
\quad\stackrel{\text{existing small perturbation}}{\longrightarrow}\quad
A_H
\quad\Longleftrightarrow\quad
M_{\Omega,H}
\quad\Longleftrightarrow\quad
N_\kappa
\quad\Longleftrightarrow\quad
S_\kappa
\quad\Longleftrightarrow\quad
\deg B_\Omega=\kappa.
\]

The last four arrows are exact. The first arrow is the perturbative transfer
already present in Lemma generic-affine; it is not an equality of inertias.

No node status and no conditional/unconditional theorem status changes because
of this note.

---

## 1. Generic stationary contour form

Let \(\Omega=\Omega_T\) be the conjugation-symmetric good rectangle in the
straightened \(z\)-coordinate. Let \(H\) be a real-symmetric holomorphic
function on a neighbourhood of \(\overline\Omega\),

\[
H(\bar z)=\overline{H(z)},
\]

such that

1. \(H'\) has no zero on \(\partial\Omega\);
2. every zero of \(H'\) in \(\Omega\) is simple;
3. \(H\) and \(H'\) have no common zero.

For a packet test function \(h\), the manuscript contour form is

\[
\mathcal A_H(h_1,h_2)
=
\frac{1}{2\pi i L^2}
\oint_{\partial\Omega}
\left(
-H(z)\frac{H''(z)^2}{H'(z)}
\right)
h_2(z)h_1^\#(z)\,dz.
\]

Define

\[
M(z):=\frac{H(z)}{H'(z)},
\qquad
U_h(z):=H''(z)h(z).
\]

Because \(H^\#=H\), also \((U_h)^\#=H''h^\#\), and therefore

\[
\boxed{
\mathcal A_H(h_1,h_2)
=
-\frac{1}{2\pi iL^2}
\oint_{\partial\Omega}
M(z)U_{h_2}(z)U_{h_1}^\#(z)\,dz.
}
\tag{1}
\]

---

## 2. Remove the holomorphic background exactly

Let the real zeros of \(H'\) in \(\Omega\) be

\[
c_1,\dots,c_r,
\]

and let the nonreal zeros be

\[
\rho_1,\bar\rho_1,\dots,\rho_p,\bar\rho_p,
\qquad
\Im\rho_k>0.
\]

Since the zeros are simple and \(H,H'\) have no common zero, define nonzero
residues

\[
a_j
:=
\operatorname{Res}_{z=c_j}M(z)
=
\frac{H(c_j)}{H''(c_j)}
\in\mathbb R\setminus\{0\},
\]

and

\[
b_k
:=
\operatorname{Res}_{z=\rho_k}M(z)
=
\frac{H(\rho_k)}{H''(\rho_k)}
\in\mathbb C\setminus\{0\}.
\]

Real symmetry gives the residue \(\overline{b_k}\) at \(\bar\rho_k\).

Define the finite rational principal part

\[
\boxed{
M_\Omega(z)
=
\sum_{j=1}^{r}\frac{a_j}{z-c_j}
+
\sum_{k=1}^{p}
\left(
\frac{b_k}{z-\rho_k}
+
\frac{\overline{b_k}}{z-\bar\rho_k}
\right).
}
\tag{2}
\]

Then \(M-M_\Omega\) is holomorphic on a neighbourhood of
\(\overline\Omega\). Since
\(U_{h_2}U_{h_1}^\#\) is holomorphic there as well, Cauchy's theorem gives

\[
\oint_{\partial\Omega}
(M-M_\Omega)
U_{h_2}U_{h_1}^\#\,dz
=0.
\]

Hence

\[
\boxed{
\mathcal A_H(h_1,h_2)
=
-\frac{1}{2\pi iL^2}
\oint_{\partial\Omega}
M_\Omega(z)
U_{h_2}(z)U_{h_1}^\#(z)\,dz.
}
\tag{3}
\]

This is an exact identity. No global Nevanlinna property of the full
\(H/H'\) is used.

---

## 3. Contour inertia of the principal part

For a real stationary point \(c_j\), the residue contribution of (3) is

\[
-\frac{a_j}{L^2}
U_{h_2}(c_j)\overline{U_{h_1}(c_j)}.
\]

Because \(H''(c_j)\in\mathbb R\setminus\{0\}\),

\[
-a_j|H''(c_j)|^2
=
-H(c_j)H''(c_j).
\]

Thus the real one-dimensional block is negative exactly when

\[
a_j>0
\quad\Longleftrightarrow\quad
H(c_j)H''(c_j)>0.
\]

For a conjugate pair \(\rho_k,\bar\rho_k\), in the evaluation coordinates

\[
x_1=U_h(\rho_k),
\qquad
x_2=U_h(\bar\rho_k),
\]

the Hermitian block is, up to the harmless positive factor \(L^{-2}\),

\[
\begin{pmatrix}
0&-\overline{b_k}\\
-b_k&0
\end{pmatrix},
\]

whose eigenvalues are

\[
\pm |b_k|.
\]

Therefore every nonreal conjugate stationary pair contributes exactly one
negative direction.

If

\[
B(H)
=
\#\{j:a_j>0\},
\qquad
P(H')=p,
\]

then, using the surjective packet evaluation map already proved in Section 02,

\[
\boxed{
n_-(A_H)=B(H)+P(H').
}
\tag{4}
\]

This is the manuscript's existing generic stationary-inertia identity, now
expressed through the residues of \(M_\Omega\).

---

## 4. Exact negative-square index of the Nevanlinna kernel

Define the scalar kernel on the domain of analyticity of \(M_\Omega\) in the
upper half-plane by

\[
K_{M_\Omega}(z,w)
:=
\frac{M_\Omega(z)-\overline{M_\Omega(w)}}
{z-\bar w}.
\tag{5}
\]

For a real pole \(c_j\),

\[
\frac{
a_j/(z-c_j)-a_j/(\bar w-c_j)
}{
z-\bar w
}
=
-\frac{a_j}{(z-c_j)(\bar w-c_j)}.
\tag{6}
\]

Thus its coefficient is the scalar \(-a_j\).

For one nonreal conjugate pair,

\[
m_k(z)
=
\frac{b_k}{z-\rho_k}
+
\frac{\overline{b_k}}{z-\bar\rho_k},
\]

one obtains

\[
\frac{
m_k(z)-\overline{m_k(w)}
}{
z-\bar w
}
=
-\frac{b_k}{(z-\rho_k)(\bar w-\rho_k)}
-\frac{\overline{b_k}}
{(z-\bar\rho_k)(\bar w-\bar\rho_k)}.
\tag{7}
\]

With the Cauchy-function basis

\[
f_{\rho_k}(z)=\frac1{z-\rho_k},
\qquad
f_{\bar\rho_k}(z)=\frac1{z-\bar\rho_k},
\]

the coefficient block in (7) is

\[
\begin{pmatrix}
0&-b_k\\
-\overline{b_k}&0
\end{pmatrix},
\tag{8}
\]

again with eigenvalues \(\pm|b_k|\).

Collect all Cauchy functions into a vector \(\Phi(z)\). Equations
(6)--(8) give an exact finite-rank factorization

\[
\boxed{
K_{M_\Omega}(z,w)
=
\Phi(z)\,\mathcal J_\Omega\,\Phi(w)^*,
}
\tag{9}
\]

where

\[
\mathcal J_\Omega
=
\bigoplus_{j=1}^{r}[-a_j]
\;\oplus\;
\bigoplus_{k=1}^{p}
\begin{pmatrix}
0&-b_k\\
-\overline{b_k}&0
\end{pmatrix}.
\tag{10}
\]

The Cauchy functions associated with distinct poles are linearly independent:
a linear relation on an open set would be a rational identity, and taking the
residue at each pole forces every coefficient to vanish.

Consequently one can choose finitely many upper-half-plane sample points for
which the Cauchy evaluation matrix has full column rank. For every sample the
Gram matrix of \(K_{M_\Omega}\) has no more negative eigenvalues than
\(\mathcal J_\Omega\), while a full-rank sample realizes the complete inertia
of \(\mathcal J_\Omega\).

Hence the kernel has exactly

\[
\boxed{
\kappa
=
B(H)+P(H')
}
\tag{11}
\]

negative squares.

By the standard definition of the scalar generalized Nevanlinna class,

\[
\boxed{
M_\Omega\in N_\kappa.
}
\tag{12}
\]

Combining (4) and (11),

\[
\boxed{
n_-(A_H)
=
\operatorname{sq}_-(K_{M_\Omega})
=
\kappa.
}
\tag{13}
\]

This step is elementary finite-dimensional algebra; no Krein--Langer theorem
is required yet.

---

## 5. Cayley transform preserves the negative-square index

Define

\[
S_\Omega(z)
:=
\frac{M_\Omega(z)-i}{M_\Omega(z)+i}.
\tag{14}
\]

At points where the quantities are defined,

\[
1-S_\Omega(z)\overline{S_\Omega(w)}
=
\frac{
-2i\left(
M_\Omega(z)-\overline{M_\Omega(w)}
\right)
}{
(M_\Omega(z)+i)
(\overline{M_\Omega(w)}-i)
}.
\]

Therefore the upper-half-plane Schur kernel

\[
K_{S_\Omega}(z,w)
:=
\frac{
1-S_\Omega(z)\overline{S_\Omega(w)}
}{
-i(z-\bar w)
}
\]

satisfies

\[
\boxed{
K_{S_\Omega}(z,w)
=
\frac{
2K_{M_\Omega}(z,w)
}{
(M_\Omega(z)+i)
(\overline{M_\Omega(w)}-i)
}.
}
\tag{15}
\]

For every finite set of points away from the poles of \(S_\Omega\), the Gram
matrix in (15) is obtained from the Gram matrix of \(K_{M_\Omega}\) by an
invertible diagonal congruence and multiplication by the positive scalar \(2\).

Thus

\[
\boxed{
\operatorname{sq}_-(K_{S_\Omega})
=
\operatorname{sq}_-(K_{M_\Omega})
=
\kappa.
}
\tag{16}
\]

After a conformal map from the upper half-plane to the disk, and if necessary
a disk automorphism choosing a regular base point, \(S_\Omega\) is therefore a
scalar generalized Schur function of index \(\kappa\).

---

## 6. Krein--Langer factorization

The only external structural theorem used in the chain is the scalar
Krein--Langer factorization for generalized Schur functions.

For a scalar generalized Schur function with exactly \(\kappa\) negative
squares, the Hilbert-space version of the Krein--Langer theorem gives a
coprime factorization

\[
\widehat S_\Omega
=
B_\Omega^{-1}S_0,
\tag{17}
\]

after mapping the upper half-plane to the unit disk, where

- \(S_0\) is an ordinary Schur function;
- \(B_\Omega\) is a finite Blaschke product;
- the denominator degree is exactly

\[
\boxed{
\deg B_\Omega=\kappa.
}
\tag{18}
\]

Equivalently, a scalar generalized Schur function of index \(\kappa\) has
exactly \(\kappa\) poles in the disk, counting multiplicity, after cancellation
has been removed in the coprime factorization.

A convenient modern reference is:

Lassi Lilleberg, *Generalized Schur--Nevanlinna functions and their
realizations*, Integral Equations and Operator Theory 92, 42 (2020),
DOI 10.1007/s00020-020-02600-w.

That paper states the generalized Schur and generalized Nevanlinna classes by
their negative-square kernels and records the Hilbert-space Krein--Langer
factorization with a Blaschke product of degree \(\kappa\).

Combining (13), (16), and (18) gives the exact generic equivalence

\[
\boxed{
n_-(A_H)
=
B(H)+P(H')
=
\operatorname{sq}_-(K_{M_\Omega})
=
\operatorname{sq}_-(K_{S_\Omega})
=
\deg B_\Omega.
}
\tag{19}
\]

---

## 7. Relation to the current off-axis zero count

The manuscript already proves, for the same generic perturbation \(H\),

\[
D(H)
=
B(H)+P(H')
+o(N_T),
\]

where \(D(H)\) is the number of nonreal conjugate zero pairs of \(H\) in the
good rectangle.

Therefore (19) immediately gives

\[
\boxed{
D(H)
=
\deg B_\Omega
+o(N_T).
}
\tag{20}
\]

This is a genuine reformulation of the generic stationary defect as a finite
Blaschke degree.

It is **not yet a new estimate**: \(M_\Omega\) was constructed from the
stationary poles themselves, so (20) does not by itself prove that the degree
is \(o(N_T)\).

---

## 8. Where the four-block matrix enters, and where exactness stops

The exact unperturbed identity remains

\[
A_F
=
A_T^{\rm true}
+L_T^{\rm geom}
+J_T^{\rm arch}
+R_T^{\rm exact}.
\tag{21}
\]

Section 14 then chooses \(H=F+\eta z+\varepsilon\) on the same fixed packet
space so that

\[
\left\|
(\mathfrak G_T^{\rm ret})^{-1/2}
(A_H-A_F)
(\mathfrak G_T^{\rm ret})^{-1/2}
\right\|_{\rm op}
<
\frac{\kappa_*\lambda_T}{8}.
\tag{22}
\]

Thus the manuscript transfers the right-edge estimates for the exact
four-block matrix \(A_F\) to the generic zero-side detector \(A_H\) by a small
operator perturbation.

One must **not** replace this by

\[
n_-(A_F)=\deg B_\Omega.
\]

That equality is not proved and can fail at a degenerate stationary zero.

The rigorously justified statement is:

1. \(A_F\) is exactly the four-block sum.
2. \(A_H\) is an arbitrarily small generic perturbation in the normalized
   operator metric used by the endgame.
3. \(A_H\) has the exact equivalent encodings in (19).

This is the correct interface between the four-block arithmetic side and the
negative-square language.

---

## 9. Why the full \(H/H'\) must not replace its principal part

The principal-part projection in (2) is essential.

For example, let

\[
H(z)=e^{z^2/2},
\qquad
\frac{H}{H'}=\frac1z.
\]

Choose a conjugation-symmetric rectangle that does not contain \(0\). There is
no stationary pole inside, so the corresponding closed-contour residue form is
zero.

However,

\[
K_{H/H'}(z,w)
=
-\frac1{z\bar w}
\]

has one negative square.

Thus, in general,

\[
n_-(A_H)
\neq
\operatorname{sq}_-\left(K_{H/H'}\right).
\]

The exact local object is \(M_\Omega\), obtained by discarding the holomorphic
background relative to the current contour.

For the same reason this note makes no identification with the zeros of
\(H+iH'\), with a global de Branges function, or with the previously considered
Levinson-type function
\(\zeta'+(f+1)\zeta\). Such an identification would require an additional
zeta-specific theorem controlling the holomorphic background.

---

## 10. Research consequence

The exact new target suggested by this encoding is

\[
\deg B_\Omega=o(N_T),
\]

but only if the Blaschke denominator can be accessed from the right-edge
arithmetic representation without first reconstructing all stationary poles.

If \(B_\Omega\) is built from the stationary poles and only then counted,
(19) is an exact but tautological re-encoding of the existing inertia identity.

Therefore the next nontrivial question is:

> Can the complete four-block right-edge data control the generalized-Schur
> denominator degree directly, without passing through individual stationary
> zeros?

Until such a mechanism is found, the negative-square route should be treated
as a rigorous structural reformulation rather than a completed density-one
proof.
