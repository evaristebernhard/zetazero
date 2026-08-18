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

## Initialization status

All ten nodes are planned and non-green.  Their facade modules intentionally
contain documentation and namespaces only: there are no provisional theorem
statements, axioms, or placeholders.
