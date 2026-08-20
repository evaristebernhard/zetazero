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

- Work in complete theorem chains, normally 3--10 closely related declarations
  ending in one acceptance theorem; do not iterate or report lemma by lemma.
- Before starting, read `status.md`, `roadmap.md`, and the relevant manuscript
  paragraph, and identify the major node, paper label, dependencies, stable
  facade, and acceptance theorem.
- Develop unfinished work off the green main line; never use a placeholder to
  make it appear complete.
- A node turns green in one change containing its finished Lean declarations,
  valid `\lean` links, and statement/proof `\leanok` markers.
- Internal nodes may be split, merged, and renamed.  Major IDs M01--M10 and the
  facade modules listed in `roadmap.md` stay stable.
- During development build the target module, then its facade after integration.
  Run the relevant directed gate before each focused commit.  After every 2--4
  focused commits run `npm test -- lean-all` and all related directed gates.
- Commit implementation, facade import, directed test, and status/insight update
  atomically by theorem chain.  Keep broad manuscript-route edits in a separate
  documentation commit containing no new Lean proofs.
- Stage only the theorem chain being committed.  Do not commit build output,
  `.ai-bridge`, `route_b_density_one/`, Zone.Identifier files, raw research logs,
  or unrelated formatting.

## Commit subjects

Use scoped imperative subjects such as `feat(M04): ...`, `fix(M02-M03): ...`,
`docs(paper): ...`, and `chore(repo): ...`.

## Insight policy

Only record an insight when it strengthens a theorem, changes a proof interface,
identifies a manuscript gap, or materially simplifies later work.  Routine
tactic/compilation repairs are not recorded.  Reusable observations go in
`main_tex_formalization_notes.md` under date/node, observation, Lean evidence,
paper impact, and next interface.  Durable blockers go in
`analytic_frontier.md`; node state and dependencies go in `status.md` and
`roadmap.md` respectively.  Raw Route-B/contact/zero-lag notes stay in the local
ignored archive.

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
