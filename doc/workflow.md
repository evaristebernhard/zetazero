# Node workflow and green-node policy

## Definition of green

A major node is **green** (fully formalized) only when all of the following are
true atomically on the main line:

1. every prerequisite major node is already green;
2. its Lean implementation builds with warnings treated as errors;
3. the project source contains no `sorry`, `admit`, or project-defined `axiom`;
4. every Blueprint `\lean{...}` name for the node resolves under
   `leanblueprint checkdecls`;
5. both the node statement and proof carry `\leanok`;
6. the Blueprint PDF, web output, and dependency graph build without dangling
   `\uses` references.

Green is reserved for this state.  Planned, ready-to-state, stated, and
partially proved nodes use non-green graph colors.

## Integration rule

- Complete one major node at a time.
- Develop unfinished work off the green main line; never use a placeholder to
  make it appear complete.
- A node turns green in one change containing its finished Lean declarations,
  valid `\lean` links, and statement/proof `\leanok` markers.
- Internal nodes may be split, merged, and renamed.  Major IDs M01--M10 and the
  facade modules listed in `roadmap.md` stay stable.
- Run `lake build`, `python3 scripts/check_lean_placeholders.py`, `leanblueprint all`,
  `leanblueprint checkdecls`, and `python3 -m pytest -q` before merging.

## Current integration status

M01 now has a complete Lean implementation through the physical-coordinate
rank-plus-Hilbert--Schmidt min--max theorem, but it remains non-green until the
Blueprint `\lean{...}` links and `\leanok` markers are added and checked.  The
remaining major nodes are non-green.

M02 has progressed beyond pointwise Hardy-gauge calculus: the symmetric-shift
curvature identity, packet polarization, Cauchy cancellation, zero-free boundary
integrability, exact packet-polarized same-form boundary equality, and the local
simple-zero logarithmic residue coefficient all build with warnings as errors.
Its unresolved core is now the global meromorphic residue/straightening step.
M03 independently contains reflection/counting infrastructure and the local
stationary residue plus conjugate-pair inertia algebra; it still awaits the
global residue sum, packet-evaluation surjectivity, and the `Z₁` good-height
estimates.

Shared infrastructure may be developed before a dependent major node turns
green when it is mathematically independent of that dependency.  This includes
not only `ZetaZero/Analytic/*`, but also stable algebraic interfaces for later
right-edge resolvents, HLP/HLZ coefficient hierarchies, positive Gram
factorizations, and rank/Hilbert--Schmidt transfer.  Such forward development is
allowed only when the lemma is independent of an unproved analytic assertion;
it must not be used to mark the dependent major node green prematurely.
