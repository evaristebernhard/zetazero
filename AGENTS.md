# ZetaZero formalization policy

This policy applies to the whole repository.  The stable major-node facades are
M01--M10 as listed in `doc/roadmap.md`.

## Proof quality

- Do not add `sorry`, `admit`, project-defined `axiom`s, empty theorem shells,
  or artificially strong hypotheses that merely disguise an unfinished proof.
- Trust checked Lean declarations, not names or prose.  A theorem is complete
  only when its actual assumptions match the mathematical interface claimed by
  the paper.
- Develop a complete mathematical interface at a time: normally 3--10 tightly
  related declarations with one acceptance theorem.  Do not compile, commit,
  or report progress lemma by lemma.

## Starting and developing a theorem chain

Before editing, read `doc/status.md`, `doc/roadmap.md`, and the relevant paper
paragraph.  Record mentally (or in the work item) the major node, paper label,
dependencies, destination facade, and acceptance theorem.

During development, build only the target module.  Once the public declarations
are imported by their M01--M10 facade, build that facade too.  Temporary parallel
modules must name their eventual stable destination and must be removed when the
interface is integrated; do not maintain a second, duplicate API.

Combine every 2--4 focused commits into an integration tranche, then run
`npm test -- lean-all` and the relevant directed gates.

## Atomic commits

Commit vertically by theorem chain: implementation, stable facade import,
directed test, and the corresponding status/insight update belong together.
Large manuscript-route changes are separate documentation commits and contain
no new Lean proofs.

Use these subjects:

- `feat(M04): ...`
- `fix(M02-M03): ...`
- `docs(paper): ...`
- `chore(repo): ...`

Before committing, stage only files or hunks belonging to that theorem chain.
Never include generated output, `.ai-bridge` state, `route_b_density_one/`,
Zone.Identifier files, local research logs, or unrelated formatting.

## Documentation and insights

Document an insight only when it strengthens a theorem, changes a proof
interface, exposes a manuscript gap, or materially simplifies later work.
Routine tactic and compilation repairs are not insights.

Put reusable insights in `doc/main_tex_formalization_notes.md`, using:

1. date and major node;
2. observation;
3. Lean evidence (declarations/modules);
4. manuscript impact;
5. next interface.

Put durable blockers in `doc/analytic_frontier.md`.  Update node state in
`doc/status.md` and dependency changes in `doc/roadmap.md`.  Raw Route-B,
contact, and zero-lag research remains in the ignored
`route_b_density_one/` local archive; only reusable conclusions enter `doc/`.

## Verification and green nodes

Before a focused commit, run the target facade build, its directed pytest gate,
and `python3 scripts/check_lean_placeholders.py`.  Claims such as “verified”,
“pass”, and “green” must name commands executed in the current work, not stale
logs.

A major node is green only when all of the following pass together:

1. Lean implementation and stable facade build;
2. placeholder scan;
3. Blueprint declarations resolve with `leanblueprint checkdecls`;
4. the Blueprint statement and proof both carry `\leanok`;
5. `leanblueprint all` completes, including PDF, web output, and dependency
   graph.

Until then use the non-green states in `doc/status.md`, even if the Lean portion
is complete.
