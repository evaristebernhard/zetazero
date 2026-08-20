# Candidate `main.tex` updates suggested by the Lean formalization

This file is a staging area for mathematical/expository improvements discovered
while formalizing the current proof.  It does **not** change the manuscript proof
route.  Items should be moved into `main.tex` only when the corresponding section
is being edited deliberately.

## M04: clarify the Fresnel/stationary-phase normalization

The stationary integral formalization now supports two useful clarifications for
Sections 03--04.

- The pure oscillatory Gaussian is handled through a genuine tail estimate and
  Abel damping, not by substituting an imaginary parameter into a Gaussian
  theorem whose hypotheses require positive real part.  The formal route proves
  the finite-tail estimate

  ```text
  || integral_R^S exp(i y^2/2) dy || <= 2/R
  ```

  and the symmetric Fresnel limit, with the quantitative window error `<= 4/R`.
  If the manuscript currently compresses this into “analytic continuation”, it
  should instead describe the Abel-damping argument explicitly.

- The stationary normalization is an exact scalar cancellation: saddle Stirling
  amplitude, Gaussian Hessian factor, and the external `1/(2*pi)` multiply to
  one.  This explains structurally why no pair-dependent Hessian weight survives
  in the principal arithmetic carrier.

- The finite-window replacement is quantitative in Lean.  The cubic real-phase
  remainder plus the unit-circle Lipschitz estimate gives

  ```text
  || exactKernel(eta,y) - exp(i y^2/2) ||
      <= (2/3) * |y|^3 / sqrt(t_*),
  ```

  and hence on `[-R,R]`

  ```text
  || integral (exactKernel - quadraticKernel) ||
      <= (4/3) * R^4 / sqrt(t_*).
  ```

  `StationaryMainTermError.lean` now goes one step further.  Since the exact
  kernel is Borel measurable and has norm one, it is automatically integrable on
  every finite interval; no separate continuity-at-log-zero argument is needed.
  Therefore Lean proves the actual finite-window stationary main term

  ```text
  || integral_{-R}^R exactKernel(eta,y) - sqrt(pi)*(1+i) ||
    <= (4/3) * R^4 / sqrt(t_*) + 4/R.
  ```

  A particularly clean window condition is

  ```text
  R^5 <= sqrt(t_*),
  ```

  under which the whole error is at most `16/(3R)`.  This is worth using in the
  manuscript instead of a generic `R -> infinity`, `R^4/sqrt(t_*) -> 0`
  sentence: it exhibits the exact balance between the cubic local error and the
  Fresnel tail, while still leaving freedom to choose any slowly growing `R`
  satisfying the packet-window constraints.


## M05: make the factorial-uniformity mechanism explicit

Lean suggests a cleaner presentation of Proposition `factorial-majorant` in
Section 07.

1. Work at the exponential cutoff `X = floor(exp y)`.  For every positive integer
   `d` in the summation range, the shortened cutoff is exactly

   ```text
   floor(exp y) / d = floor(exp (y - log d)).
   ```

   This removes an otherwise implicit floor/range comparison from the induction.

2. The weighted Chebyshev step can state the denominator explicitly:

   ```text
   sum_{d <= exp y} Lambda(d)/d * (1+y-log d)^m
     <= (1 + KM*B) * (1+y)^(m+1)/(m+1)
   ```

   under `m+1 <= B(1+y)`.  The `1/(m+1)` is the source of the factorial, rather
   than a later constant absorption.

3. The manuscript currently says the condition `m << log(ex)` is automatic from
   support.  Lean gives a concrete version.  If the level-`k` Mangoldt square sum
   at `floor(exp y)` is nonzero, then `2^k <= floor(exp y)`.  Since
   `log 2 > 1/2`, one obtains

   ```text
   2*k <= 4*(1+y).
   ```

   Thus `B=4` is already sufficient for the polynomial degree used in the
   induction.  This is worth stating because it removes a qualitative uniformity
   clause from the proof.

4. The formal induction actually produces a denominator `2k` at the natural
   `2k-1` exponent step.  Weakening `2k` to `k` gives the advertised `1/k!`.
   Mentioning this makes the factorial bookkeeping more transparent.

5. The exact coefficient identity is now also formalized:

   ```text
   (k+1) * alpha_{k+1}(n) = log(n) * Lambda_{k+1}(n).
   ```

   Lean proves it algebraically by observing that multiplication by `log n` is a
   derivation for Dirichlet convolution.  For exposition, this is cleaner than
   deriving the coefficient relation by differentiating an analytic Dirichlet
   series and then comparing coefficients.  The weaker already-proved inequality

   ```text
   alpha_{k+1}(n) <= log(n) * Lambda_{k+1}(n)
   ```

   remains useful as a division-free monotone comparison, but the exact identity
   gives a sharper square factor `1/(k+1)^2`.  Combining it with the Mangoldt
   factorial induction yields the natural-cutoff theorem

   ```text
   sum_{n<=X} alpha_{k+1}(n)^2
     <= KM * D^k/(k+1)! * X * (1+log X)^(2k+3),
   D = 1 + 4 KM.
   ```

   Thus the formal statement is slightly stronger than the manuscript's generic
   `C A^k/k!` form and does not require a separate analytic coefficient-comparison
   argument.

6. It is useful to separate **proof coordinates** from **calling coordinates**.
   The induction is cleanest at `X=floor(exp y)` because shortening by a divisor
   is exact there.  The final API should nevertheless be stated for an ordinary
   natural cutoff `X`, obtained by setting `y=log X`.  This keeps all floor
   bookkeeping out of the later stationary/direct-carrier lemmas.

7. The normalization used later in Sections 04 and 07 has now been formalized
   independently.  If `1+log X <= L`, then for level `k+1`

   ```text
   sum_{n<=X} |(C_H/L)^(k+1) alpha_{k+1}(n)|^2
     <= KM * D^k/(k+1)! * X * C_H^(2k+2) * (1+log X).
   ```

   The key scalar cancellation is

   ```text
   (C/L)^(2r) * a^(2r+1) <= C^(2r) * a,
   0 <= a <= L.
   ```

   So the large logarithmic power in the factorial majorant is not a final loss:
   the deterministic `L^{-k}` normalization absorbs all but one logarithm.  This
   is worth making explicit when `lem:direct-carrier-square` is next edited,
   because it explains why the completed carrier bound is uniform in the HLP
   level rather than merely summable after a crude polylogarithmic enlargement.

8. The level summation itself has a clean Hilbert-space formulation.  For any
   finite family of carrier levels, Lean now proves the exact finite-dimensional
   Minkowski interface

   ```text
   sqrt(sum_m |sum_k c_{k,m}|^2)
     <= sum_k sqrt(sum_m |c_{k,m}|^2).
   ```

   It is useful to keep this as a separate functional-analytic lemma.  The HLP
   arithmetic then only supplies one `ell^2` norm per level; no double-sum
   rearrangement belongs in the stationary-phase argument.  A support restriction
   is also automatically monotone because it only deletes nonnegative square
   coordinates.

9. The remaining one-dimensional level series now also has a Lean proof in
   `FactorialLevelSummability.lean`:

   ```text
   sum_k A^k / sqrt(k!) < infinity.
   ```

   Instead of a ratio test, the formal proof factors

   ```text
   A^k/sqrt(k!) = ((2|A|)^k/sqrt(k!)) * (1/2)^k.
   ```

   The squares of the two factors are respectively an exponential series and a
   geometric series, so Cauchy--Schwarz/Hölder gives summability immediately.
   Fixed derivative losses `(1+k)^q` require no new analysis: the elementary
   inequality `k+1 <= 2^k` absorbs them into a larger exponential parameter.
   This makes the sentence following `eq:direct-carrier-square` more transparent:
   polynomial-in-level derivative losses are harmless for a structural reason,
   not because of a delicate separate convergence estimate.

10. The direct-carrier formalization now suggests a three-layer presentation:

    ```text
    one-level factorial budget
      -> finite-level Minkowski assembly
      -> uniform finite-subset bound via the summable level weight.
    ```

    In particular, for every finite level set `K`, the normalized coefficient
    family satisfies a bound of the form

    ```text
    || sum_{k in K} (C/L)^(k+1) alpha_{k+1} ||_ell2
      <= sqrt(KM * X * (1+log X)) * C_HLP,
    ```

    where `C_HLP` is the same convergent level-series constant for every `K`.
    Thus the phrase “the same bound holds for any subset of levels” can be made
    literal: subset-uniformity comes from nonnegative summable level weights, not
    from cancellation between levels.  The same abstraction accepts a fixed
    polynomial factor `(k+1)^q`, which is exactly what the bounded `p`-derivatives
    produce.
