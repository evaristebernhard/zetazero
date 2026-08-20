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

