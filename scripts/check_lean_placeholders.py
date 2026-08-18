"""Reject placeholder proofs and project-defined axioms in Lean source."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom)\b")


def mask_comments_and_strings(source: str) -> str:
    """Preserve positions and newlines while masking Lean comments/strings."""
    out = list(source)
    i = 0
    block_depth = 0
    in_string = False
    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                block_depth += 1
                out[i : i + 2] = "  "
                i += 2
            elif source.startswith("-/", i):
                block_depth -= 1
                out[i : i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out[i : i + 2] = "  "
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            block_depth = 1
            out[i : i + 2] = "  "
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
            out[i:end] = " " * (end - i)
            i = end
        elif source[i] == '"':
            in_string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def main() -> int:
    paths = [ROOT / "ZetaZero.lean", *sorted((ROOT / "ZetaZero").rglob("*.lean"))]
    failures: list[str] = []
    for path in paths:
        source = mask_comments_and_strings(path.read_text())
        for match in FORBIDDEN.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(ROOT)}:{line}: {match.group()}")
    if failures:
        print("Forbidden Lean placeholder or axiom:")
        print("\n".join(failures))
        return 1
    print(f"PASS: scanned {len(paths)} Lean source files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

