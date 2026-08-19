# ZetaZero formalization

This directory records the formalization route and collaboration rules.  It is
deliberately separate from [`blueprint/`](../blueprint/), which is the
LeanBlueprint source and generated mathematical dependency graph.  The paper in
`main.tex` and `sections/` remains the canonical informal proof, while the Lean
library is now under active development and the documentation is kept in sync
with implemented major-node interfaces.

## Project goal

The project translates the proof into a Mathlib-backed Lean 4 library while
keeping a checkable correspondence between the paper, ten stable major nodes,
and Lean declarations.  M01 is Lean-complete through its physical-coordinate
min--max theorem.  M02 now reaches the packet-polarized same-form boundary
identity and local simple-zero coefficient; M03 contains the local stationary
residue/inertia theory.  Independent forward infrastructure has also started for
M04/M05/M07: exact right-edge source algebra, finite HLP resolvent expansion and
coefficient recurrence, and abstract positive-Gram pullbacks.  The package is
named `zetazero`; its public library and root namespace are `ZetaZero`.

See [roadmap.md](roadmap.md) for the major-node dependency graph and paper
mapping, [status.md](status.md) for the current node states, and
[workflow.md](workflow.md) for the definition of a green node and the
node-by-node integration policy.

## Local setup

```bash
lake exe cache get
lake build
python3 scripts/check_lean_placeholders.py

python3 -m venv blueprint/.venv
blueprint/.venv/bin/python -m pip install -r blueprint/requirements.txt
PATH="$PWD/blueprint/.venv/bin:$PATH" leanblueprint all

npm test -- lean
npm test -- lean-all
npm test -- blueprint-decls
python3 -m pytest -q
```

The checked-in toolchain and Lake manifest make Lean and package revisions
reproducible.  The `lean-all` gate is stricter than the default Lake target: it
builds every source module under `ZetaZero/`, including modules that have not yet
been imported by a public facade.
