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
node-by-node integration policy.  The implementation-facing stabilization and
density-one interface plan is in
[lean_formalization_plan.md](lean_formalization_plan.md).
`main.tex` 到 Lean 的分层映射、M01--M03 详译与 gap 记录见
[main_tex_to_lean_system.md](main_tex_to_lean_system.md)；全部 `ZetaZero/`
目录、文件和 facade 覆盖清单见
[lean_directory_inventory.md](lean_directory_inventory.md)。
下一轮选定的 gap 及执行顺序记录于
[lean_gap_closure_plan.md](lean_gap_closure_plan.md)。

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
python3 -m pytest
```

The checked-in toolchain and Lake manifest make Lean and package revisions
reproducible.  The `lean-all` gate is stricter than the default Lake target: it
builds every source module under `ZetaZero/`, including modules that have not yet
been imported by a public facade.
