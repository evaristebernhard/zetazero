# Small Gap Closure: Direct-Carrier Square Bound on Polylogarithmic Exterior Range

Date: 2026-09-03

## Problem

The exterior packet-support argument requires direct one-\(\chi\) carrier coefficients beyond the original range \(x\le T\). For the lower exterior packet support,

\[
x_- = e^{-\Delta}L^{-C_{\rm pkt}/2},
\]

and a stationary point can occur only for

\[
\frac{T}{2\pi}\ll m\ll \frac{T}{x_-}
= e^{\Delta}T L^{C_{\rm pkt}/2}.
\]

Thus the original statement of Lemma `lem:direct-carrier-square`, which only asserted the coefficient square bound for \(x\le T\), did not literally cover the exterior stationary carrier range.

The needed extension is only polylogarithmic:

\[
x\le T L^{C_x}
\]

for fixed \(C_x\).

## Claim

For every fixed \(C_x\ge0\), the direct-carrier square bound remains valid uniformly for \(x\le T L^{C_x}\):

\[
\sum_{m\le x}\left|\partial_p^q c_m^{\rm dir}(p)\right|^2
\ll_{C_x} xL^{C_{\rm dir}},
\qquad 0\le q\le2.
\]

The same statement holds for the norm-summable HLP hierarchy, arbitrary subsets of levels, fixed coefficient translations, and support restrictions.

## Proof audit

The original proof uses the range \(x\le T\) only through logarithmic comparisons. If \(x\le T L^{C_x}\) with fixed \(C_x\), then

\[
\log(ex)
= \log T + O_{C_x}(\log L)
= L+O_{C_x}(\log L)
\asymp_{C_x}L.
\]

Hence every occurrence of \(\log(ex)\) in the factorial HLP majorant remains comparable with \(L\).

For the level-\(k\) coefficient \(f^{-k}\alpha_k(m)\), the existing factorial estimate gives

\[
\sum_{m\le x}\alpha_k(m)^2
\ll
\frac{A^k}{k!}
 x\, (\log(ex))^{2k+1},
\]

up to harmless absolute changes in the fixed constants. Since \(|f|\asymp L\) on the fixed absolute-convergence right edge,

\[
\left(
\sum_{m\le x}|f^{-k}\alpha_k(m)|^2
\right)^{1/2}
\ll_{C_x}
(xL)^{1/2}\frac{C^k}{\sqrt{k!}}.
\]

The support fact \(2^k\le x\) still gives \(k=O(\log x)=O(L)\), so the weighted-Chebyshev induction used in the factorial majorant remains in exactly the same uniform regime.

A fixed normalized physical-shift derivative produces factors

\[
\frac{\log m}{L}
\le
\frac{\log(TL^{C_x})}{L}
=1+O_{C_x}\!\left(\frac{\log L}{L}\right)
=O_{C_x}(1),
\]

and therefore does not alter factorial summability over \(k\).

Likewise, fixed translated coefficients satisfy

\[
m^{O(1/L)}
\le
\exp\!\left(
O\!\left(\frac{\log(TL^{C_x})}{L}\right)
\right)
=O_{C_x}(1).
\]

The ordinary \(k=0\) logarithmic-derivative term obeys

\[
\sum_{m\le x}\Lambda(m)^2
\le (\log x)\psi(x)
\ll_{C_x}xL.
\]

Finally, support restriction can only decrease the coefficient square sum.

Therefore the original proof extends without any new analytic input once its logarithmic dependence is written explicitly.

## Application to the exterior packet reserve

Choose fixed

\[
C_x>C_{\rm pkt}/2
\]

large enough to absorb the fixed transition-cap factor \(e^{\Delta}\). Since

\[
x_-^{-1}=e^{\Delta}L^{C_{\rm pkt}/2},
\]

every lower-exterior stationary carrier satisfies

\[
m\ll T L^{C_x}
\]

for all sufficiently large \(T\). Hence

\[
\sum_{m\ll T L^{C_x}}|c_m^{\rm dir}|^2
\ll T L^C,
\]

which is precisely the source coefficient input used in the exterior one-leaking-leg Hilbert--Schmidt lift.

The upper exterior range does not require a larger carrier cutoff: its nonstationary shell sum is controlled directly by integration by parts, while stationary/adjacent rows are already assigned to the low-rank exterior edge space.

## Status

This small gap is **closed in the working manuscript**.

Changes made:

- `sections/07_hlp_local_replacement.tex`: Lemma `lem:direct-carrier-square` now states and proves the bound for every fixed range \(x\le T L^{C_x}\).
- `sections/10_shell_edge.tex`: the exterior-support proof now invokes this uniform lemma directly instead of saying that the proof "extends verbatim".
- `main.tex` compiles successfully with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

## Consequence for the density-one gap audit

The former audit item "extension of direct-carrier square bounds into the exterior reserve" should no longer be treated as an open proof gap. The remaining exterior-support risk is instead the global source-ownership question: whether every reserve/cap/cross term has been assigned exactly once to the edge or relative-HS ledger.
