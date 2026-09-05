#!/usr/bin/env python3
"""Verify (and with --fix, repair) the line numbers in THEOREMS.md.

Each row of the index names a Lean declaration and the file:line where it is
declared. Line numbers rot silently whenever documentation is inserted above
a declaration, so this script re-derives every location from the sources and
either reports drift (exit 1) or rewrites the index in place.

It also checks that every declaration the index names is audited: that
`scripts/Audit.lean` prints its axioms. The README promises that audit for
every identifier the paper cites, and a promise the script does not check is
one that drifts.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / "THEOREMS.md"
AUDIT = ROOT / "scripts" / "Audit.lean"

ROW = re.compile(
    r"^\| (?P<claim>[^|]*) \| `(?P<name>[^`]+)` \| "
    r"\[`(?P<file>[^:`]+):(?P<line>\d+)`\]\((?P=file)#L(?P=line)\) \|$"
)
ROW_LIKE = re.compile(r"^\| [^|]* \| `")
DECL_KEYWORDS = r"(?:theorem|lemma|def|abbrev|inductive|structure|instance|noncomputable def|opaque|axiom|class|namespace)"
AUDIT_LINE = re.compile(r"^#print axioms (?P<name>\S+)\s*$")
# A namespace has no axioms to print; every other kind of declaration does.
UNAUDITABLE = {"namespace"}


@dataclass(frozen=True)
class Row:
    claim: str
    name: str
    file: str
    line: int


def parse_rows(text: str) -> tuple[list[tuple[int, Row | None]], list[int]]:
    """Rows of the index, and the line numbers of rows that look like index
    rows but do not parse (a malformed row would otherwise be skipped silently)."""
    rows: list[tuple[int, Row | None]] = []
    malformed: list[int] = []
    for i, raw in enumerate(text.splitlines()):
        m = ROW.match(raw)
        rows.append((i, Row(m["claim"], m["name"], m["file"], int(m["line"])) if m else None))
        if m is None and ROW_LIKE.match(raw):
            malformed.append(i + 1)
    return rows, malformed


@dataclass(frozen=True)
class Declaration:
    line: int
    keyword: str


def find_declaration(source_lines: list[str], qualified: str) -> Declaration | None:
    parts = qualified.split(".")
    for k in range(1, len(parts) + 1):
        suffix = re.escape(".".join(parts[-k:]))
        pattern = re.compile(
            rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?P<kw>{DECL_KEYWORDS})\s+{suffix}(?![\w.'])"
        )
        hits = [(n, m["kw"]) for n, line in enumerate(source_lines, 1) if (m := pattern.match(line))]
        if len(hits) == 1:
            return Declaration(*hits[0])
        if len(hits) > 1:
            continue
    return None


def audited_names() -> set[str]:
    return {m["name"] for line in AUDIT.read_text().splitlines() if (m := AUDIT_LINE.match(line))}


def main(fix: bool) -> int:
    text = INDEX.read_text()
    lines = text.splitlines()
    rows, malformed = parse_rows(text)
    audited = audited_names()
    drift: list[tuple[Row, int | None]] = []
    unaudited: list[Row] = []
    verified = 0
    for i, row in rows:
        if row is None:
            continue
        src = (ROOT / row.file).read_text().splitlines()
        decl = find_declaration(src, row.name)
        if decl is not None and decl.keyword not in UNAUDITABLE and row.name not in audited:
            unaudited.append(row)
        actual = decl.line if decl is not None else None
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
    for n in malformed:
        print(f"MALFORMED: THEOREMS.md:{n} looks like an index row but does not parse")
    for row in unaudited:
        print(f"UNAUDITED: {row.name} has no `#print axioms` line in {AUDIT.relative_to(ROOT)}")
    if fix:
        INDEX.write_text("\n".join(lines) + "\n")
    print(
        f"{verified} verified, {len(drift) - len(unresolved)} drifted, "
        f"{len(unresolved)} unresolved, {len(malformed)} malformed, {len(unaudited)} unaudited"
    )
    if unresolved or malformed or unaudited:
        return 1
    return 0 if (fix or not drift) else 1


if __name__ == "__main__":
    sys.exit(main(fix="--fix" in sys.argv[1:]))
