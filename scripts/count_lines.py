#!/usr/bin/env python3
"""Count the library's source lines, split into code, documentation, and blank.

The paper and README state the artifact's size, and a size stated without its
method drifts: `wc -l` counts the documentation the source files carry, which
is a third of them. This script is the method. Every line of `LambdaS/*.lean`
is classified as exactly one of

  code   a line with content outside every comment,
  doc    a line whose content lies entirely inside `/- ... -/` (nested blocks
         included) or after a `--` line comment,
  blank  a line with no content at all,

so the three counts sum to the file total and the classification is
reproducible from a checkout. Lean's block comments nest, and a `--` inside
a block comment is text, not a comment marker; both are handled. The script
also counts `theorem` and `lemma` declarations, on code lines only, so a
declaration quoted in documentation is not counted.

`--check` compares the README's status table against the counts (line
figures rounded to the nearest hundred, the theorem count exact) and exits 1
on drift; `--fix` rewrites the table in place. CI runs the check, so the
stated size cannot silently stop being the measured one.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "LambdaS"
README = ROOT / "README.md"
THEOREM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\b")


@dataclass(frozen=True)
class Counts:
    code: int
    doc: int
    blank: int
    theorems: int

    @property
    def total(self) -> int:
        return self.code + self.doc + self.blank

    def __add__(self, other: "Counts") -> "Counts":
        return Counts(
            self.code + other.code,
            self.doc + other.doc,
            self.blank + other.blank,
            self.theorems + other.theorems,
        )


def classify(source: str) -> Counts:
    """Classify each line of one file; comment depth carries across lines."""
    depth = 0
    code = doc = blank = theorems = 0
    for line in source.splitlines():
        has_code = False
        has_doc = False
        if depth == 0 and THEOREM.match(line):
            theorems += 1
        i = 0
        while i < len(line):
            two = line[i : i + 2]
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/" and depth > 0:
                depth -= 1
                i += 2
            elif two == "--" and depth == 0:
                if line[i:].strip():
                    has_doc = True
                break
            else:
                if not line[i].isspace():
                    if depth > 0:
                        has_doc = True
                    else:
                        has_code = True
                i += 1
        if has_code:
            code += 1
        elif has_doc:
            doc += 1
        else:
            blank += 1
    return Counts(code, doc, blank, theorems)


def round_hundreds(n: int) -> str:
    return f"{round(n, -2):,}"


def readme_rows(total: Counts) -> dict[str, str]:
    """The README status rows this script owns, keyed by their labels."""
    return {
        "lines of definitions and proofs": round_hundreds(total.code),
        "lines of documentation": round_hundreds(total.doc),
        "theorem and lemma declarations": str(total.theorems),
    }


ROW = re.compile(r"^\| (?P<label>[^|]+?) \| (?P<value>[^|]+?) \|$")


def reconcile_readme(total: Counts, fix: bool) -> int:
    """Compare (or rewrite) the README's owned rows; return the drift count."""
    expected = readme_rows(total)
    lines = README.read_text(encoding="utf-8").splitlines(keepends=True)
    drifted = 0
    seen: set[str] = set()
    for i, line in enumerate(lines):
        m = ROW.match(line.rstrip("\n"))
        if not m or m["label"] not in expected:
            continue
        seen.add(m["label"])
        want = expected[m["label"]]
        if m["value"] != want:
            drifted += 1
            print(f"README: {m['label']}: stated {m['value']}, measured {want}")
            lines[i] = f"| {m['label']} | {want} |\n"
    for label in expected.keys() - seen:
        drifted += 1
        print(f"README: no row for {label}")
    if fix and drifted:
        README.write_text("".join(lines), encoding="utf-8")
        print("README rewritten")
    return drifted


def main() -> int:
    files = sorted(LIBRARY.glob("*.lean"))
    if not files:
        print(f"no sources under {LIBRARY}", file=sys.stderr)
        return 1
    total = Counts(0, 0, 0, 0)
    for path in files:
        counts = classify(path.read_text(encoding="utf-8"))
        total = total + counts
        print(
            f"{path.name:22s} code {counts.code:5d}  doc {counts.doc:5d}"
            f"  blank {counts.blank:4d}  theorems {counts.theorems:3d}"
        )
    print(
        f"{'total':22s} code {total.code:5d}  doc {total.doc:5d}  blank {total.blank:4d}"
        f"  theorems {total.theorems:3d}  (lines {total.total})"
    )
    if "--check" in sys.argv or "--fix" in sys.argv:
        drifted = reconcile_readme(total, fix="--fix" in sys.argv)
        if drifted and "--fix" not in sys.argv:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
