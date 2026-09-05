#!/usr/bin/env python3
"""Verify (and with --fix, repair) the line numbers in THEOREMS.md.

Each row of the index names a Lean declaration and the file:line where it is
declared. Line numbers rot silently whenever documentation is inserted above
a declaration, so this script re-derives every location from the sources and
either reports drift (exit 1) or rewrites the index in place.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / "THEOREMS.md"

ROW = re.compile(
    r"^\| (?P<claim>[^|]*) \| `(?P<name>[^`]+)` \| "
    r"\[`(?P<file>[^:`]+):(?P<line>\d+)`\]\((?P=file)#L(?P=line)\) \|$"
)
DECL_KEYWORDS = r"(?:theorem|lemma|def|abbrev|inductive|structure|instance|noncomputable def|opaque|axiom|class|namespace)"


@dataclass(frozen=True)
class Row:
    claim: str
    name: str
    file: str
    line: int


def parse_rows(text: str) -> list[tuple[int, Row | None]]:
    rows: list[tuple[int, Row | None]] = []
    for i, raw in enumerate(text.splitlines()):
        m = ROW.match(raw)
        rows.append((i, Row(m["claim"], m["name"], m["file"], int(m["line"])) if m else None))
    return rows


def declaration_line(source_lines: list[str], qualified: str) -> int | None:
    parts = qualified.split(".")
    for k in range(1, len(parts) + 1):
        suffix = re.escape(".".join(parts[-k:]))
        pattern = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?{DECL_KEYWORDS}\s+{suffix}(?![\w.'])")
        hits = [n for n, line in enumerate(source_lines, 1) if pattern.match(line)]
        if len(hits) == 1:
            return hits[0]
        if len(hits) > 1:
            continue
    return None


def main(fix: bool) -> int:
    text = INDEX.read_text()
    lines = text.splitlines()
    drift: list[tuple[Row, int | None]] = []
    verified = 0
    for i, row in parse_rows(text):
        if row is None:
            continue
        src = (ROOT / row.file).read_text().splitlines()
        actual = declaration_line(src, row.name)
        if actual == row.line:
            verified += 1
            continue
        drift.append((row, actual))
        if fix and actual is not None:
            lines[i] = lines[i].replace(f"{row.file}:{row.line}", f"{row.file}:{actual}").replace(
                f"{row.file}#L{row.line}", f"{row.file}#L{actual}"
            )
    unresolved = [(r, a) for r, a in drift if a is None]
    for row, actual in drift:
        status = "UNRESOLVED" if actual is None else ("fixed" if fix else "stale")
        print(f"{status}: {row.name} {row.file}:{row.line} -> {actual}")
    if fix:
        INDEX.write_text("\n".join(lines) + "\n")
    print(f"{verified} verified, {len(drift) - len(unresolved)} drifted, {len(unresolved)} unresolved")
    if unresolved:
        return 1
    return 0 if (fix or not drift) else 1


if __name__ == "__main__":
    sys.exit(main(fix="--fix" in sys.argv[1:]))
