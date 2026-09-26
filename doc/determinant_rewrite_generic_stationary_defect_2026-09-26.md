# Determinant rewrite of the generic stationary defect (2026-09-26)

## Scope

This note isolates the current finite-dimensional rewrite of the **generic**
zero-side stationary defect.

It starts only after the Section 14 perturbation

\[
H(z)=F(z)+\eta z+\varepsilon
\]

has been chosen so that the zeros of \(H'\) in the good rectangle
\(\Omega=\Omega_T\) are simple, \(H\) and \(H'\) have no common zero, and
\(H'\) has no zero on \(\partial\Omega\).

The goal is not to prove a new zero-density estimate here.  The goal is to
rewrite the already-audited negative index as a concrete scalar rational
equation and then as a finite determinant / non-selfadjoint eigenvalue count.

The exact generic identity already available is

\[
\boxed{
n_-(A_H)
=
B(H)+P(H')
=
\operatorname{sq}_-(K_{M_\Omega})
=
\deg B_\Omega.
}
\]

The present note rewrites the same integer \(\kappa:=n_-(A_H)\).

---

## 1. Principal part of \(H/H'\)

Let the zeros of \(H'\) inside \(\Omega\) be

\[
\lambda_1,\dots,\lambda_m,
\]

listed with the conjugation symmetry.  Since the zeros are simple and
\(H(\lambda_j)\neq0\), define

\[
r_j
:=
\operatorname{Res}_{z=\lambda_j}\frac{H(z)}{H'(z)}
=
\frac{H(\lambda_j)}{H''(\lambda_j)}.
\]

The finite principal part is

\[
\boxed{
M_\Omega(z)
=
\sum_{j=1}^{m}\frac{r_j}{z-\lambda_j}.
}
\tag{1}
\]

Here the data satisfy

\[
\lambda_{\bar j}=\overline{\lambda_j},
\qquad
r_{\bar j}=\overline{r_j},
\]

and for a real stationary point \(c\),

\[
r_c\in\mathbb R.
\]

The holomorphic part of \(H/H'\) relative to the current contour contributes
zero to the closed contour form.  Hence \(M_\Omega\), not the full \(H/H'\),
is the correct finite object.

---

## 2. Rational form \(M_\Omega=P/Q\)

Set

\[
Q(z):=\prod_{j=1}^{m}(z-\lambda_j).
\]

Then

\[
M_\Omega(z)=\frac{P(z)}{Q(z)},
\]

where

\[
\boxed{
P(z)
=
\sum_{j=1}^{m}
r_j
\prod_{\ell\neq j}(z-\lambda_\ell).
}
\tag{2}
\]

Thus

\[
\deg Q=m,
\qquad
\deg P\le m-1.
\]

Because of the conjugation symmetry of the pole/residue data, both \(P\) and
\(Q\) can be chosen with real coefficients after collecting conjugate pairs.

The generalized-Schur Cayley transform is

\[
S_\Omega(z)
=
\frac{M_\Omega(z)-i}{M_\Omega(z)+i}
=
\boxed{
\frac{P(z)-iQ(z)}
     {P(z)+iQ(z)}.
}
\tag{3}
\]

After removal of common factors, the poles of \(S_\Omega\) in the upper
half-plane are therefore exactly the zeros of

\[
\boxed{
P(z)+iQ(z)=0
}
\tag{4}
\]

in the upper half-plane.

By the audited negative-square / Krein--Langer equivalence,

\[
\boxed{
\kappa
=
n_-(A_H)
=
N_{\mathbb C_+}(P+iQ),
}
\tag{5}
\]

where the zero count is with multiplicity and after cancellation in the
coprime generalized-Schur representation.

This is the scalar polynomial version of the stationary inertia problem.

---

## 3. Rank-one determinant representation

Introduce

\[
D:=\operatorname{diag}(\lambda_1,\dots,\lambda_m),
\qquad
r:=(r_1,\dots,r_m)^T,
\qquad
\mathbf 1:=(1,\dots,1)^T.
\]

Then

\[
M_\Omega(z)
=
\mathbf 1^T(zI-D)^{-1}r.
\tag{6}
\]

The matrix determinant lemma gives

\[
\det(A+uv^T)
=
\det(A)\bigl(1+v^TA^{-1}u\bigr).
\]

Applying it to

\[
A=zI-D,
\qquad
u=i\,r,
\qquad
v=\mathbf 1,
\]

gives

\[
\det\!\left(zI-D+i\,r\mathbf 1^T\right)
=
\det(zI-D)
\left(
1+i\,\mathbf 1^T(zI-D)^{-1}r
\right).
\]

Since

\[
M_\Omega(z)+i=0
\iff
1-iM_\Omega(z)=0,
\]

one may equivalently choose the sign convention

\[
\boxed{
\det\!\left(zI-D-i\,r\mathbf 1^T\right)=0
}
\tag{7}
\]

for the Cayley denominator equation, with the sign fixed consistently by the
chosen \(M_\Omega\) convention.

More invariantly, the only point needed below is that there is a rank-one
matrix \(R_\Omega\) such that

\[
\boxed{
P(z)+iQ(z)
=
C\,
\det(zI-D-R_\Omega)
}
\tag{8}
\]

for one nonzero constant \(C\).

Therefore

\[
\boxed{
\kappa
=
\#\{
\text{eigenvalues of }D+R_\Omega
\text{ in }\mathbb C_+
\},
}
\tag{9}
\]

counting algebraic multiplicity.

So the generic stationary defect can be represented as a half-plane
eigenvalue count for a diagonal matrix plus a rank-one non-selfadjoint
perturbation.

---

## 4. What this determinant rewrite does and does not solve

The determinant rewrite is exact, but it does not by itself prove

\[
\kappa=o(N_T).
\]

The dimension satisfies

\[
m\asymp N_T\asymp T\log T,
\]

so the polynomial/determinant in (4) or (8) already has degree of the same
order as the total zero count.

The target is therefore not to evaluate the determinant explicitly.  The
target is to prove that only \(o(N_T)\) of its zeros/eigenvalues enter the
wrong half-plane.

The main difficulty is that

\[
D=\operatorname{diag}(\lambda_j)
\]

is simple, but the rank-one perturbation is not known to be small:

\[
r_j=\frac{H(\lambda_j)}{H''(\lambda_j)}
\]

can vary strongly with \(j\).

A low-rank non-selfadjoint perturbation can move many eigenvalues.  Hence
"rank one" alone does not imply that only one or finitely many eigenvalues
change half-plane.

This is different from the Hermitian rank-one setting, where interlacing
provides strong spectral rigidity.

---

## 5. Herglotz-compatible pole/residue structure

For a real stationary point \(c\),

\[
r_c
=
\frac{H(c)}{H''(c)}.
\]

The bad-point condition is

\[
H(c)H''(c)>0
\iff
r_c>0.
\]

For the Pick kernel convention used in the negative-square audit, a real pole

\[
\frac{r_c}{z-c}
\]

contributes the rank-one kernel

\[
-\frac{r_c}
{(z-c)(\bar w-c)}.
\]

Thus

\[
r_c>0
\]

is exactly one negative square, while

\[
r_c<0
\]

is Herglotz-compatible for this sign convention.

Each nonreal conjugate stationary pair contributes one negative square
regardless of the magnitude of its residue.

Therefore, if one could delete only \(o(N_T)\) exceptional stationary poles
so that the remaining principal part has

1. only real poles;
2. the Herglotz-compatible residue signs;

then the remaining kernel would belong to \(N_0\), and all negative squares
would be confined to the deleted exceptional part.

This would immediately yield

\[
\boxed{
\kappa=o(N_T).
}
\tag{10}
\]

This formulation makes clear why the size of the negative eigenvalues is
irrelevant: the invariant is the number of sign-defective / nonreal
pole directions.

---

## 6. Equivalent scalar equation

The determinant equation can be written without matrices as

\[
\boxed{
M_\Omega(z)=-i,
}
\tag{11}
\]

or equivalently

\[
\boxed{
P(z)+iQ(z)=0.
}
\tag{12}
\]

Thus the Blaschke degree / negative index can also be viewed as the number of
upper-half-plane intersections of the rational principal part \(M_\Omega\)
with the level \(-i\).

If \(M_\Omega\) were an ordinary Herglotz/Nevanlinna function of the correct
orientation, the wrong-half-plane intersection would be forbidden.

Hence the negative index measures precisely the failure of the principal part
to have the ordinary Herglotz sign structure.

---

## 7. Current research target

The exact determinant reformulation is

\[
\boxed{
n_-(A_H)
=
N_{\mathbb C_+}(P+iQ)
=
\#\operatorname{spec}_{\mathbb C_+}(D+R_\Omega).
}
\tag{13}
\]

This is a useful finite-dimensional representation, but it is still a
re-encoding of the stationary pole data.

The nontrivial next question is not "how to expand the determinant?" but:

> Can the arithmetic/right-edge representation force the pole/residue data to
> be Herglotz-compatible outside only \(o(N_T)\) exceptional directions?

Equivalently:

> Can one show that after deleting \(o(N_T)\) stationary directions, the
> remaining principal part belongs to \(N_0\)?

A positive answer would prove

\[
\deg B_\Omega
=
n_-(A_H)
=
o(N_T)
\]

without any control on the magnitude of the negative eigenvalues.
