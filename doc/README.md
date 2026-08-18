# ZetaZero formalization

This directory records the formalization route and collaboration rules.  It is
deliberately separate from [`blueprint/`](../blueprint/), which is the
LeanBlueprint source and generated mathematical dependency graph.  The
existing paper in `main.tex` and `sections/` remains the canonical informal
proof and is not modified by this initialization.

## Project goal

The project will translate the proof into a Mathlib-backed Lean 4 library while
keeping a checkable correspondence between the paper, ten stable major nodes,
and Lean declarations.  The package is named `zetazero`; its public library and
root namespace are `ZetaZero`.

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

python3 -m pytest -q
```

The checked-in toolchain and Lake manifest make Lean and package revisions
reproducible.  There is no Git remote at initialization time, so deployment and
GitHub Pages automation are intentionally not configured.
