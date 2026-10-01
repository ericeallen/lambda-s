#!/usr/bin/env python3
"""Check the output of `lake env lean scripts/Audit.lean` against the audit list.

Usage: check_axioms.py AXIOM_OUTPUT

Every `#print axioms` line in scripts/Audit.lean must yield exactly one report
in AXIOM_OUTPUT, and a report may name only `propext`, `Classical.choice`, and
`Quot.sound`; dependency lists that Lean wraps across lines are parsed whole.
A further axiom (including `sorryAx`), a missing or extra report, or any
unrecognized output exits 1; a usage error exits 2.
"""
from collections import Counter
from pathlib import Path
import re
import sys

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
    re.MULTILINE | re.DOTALL,
)


def validate(source: str, output: str) -> int:
    expected = Counter(re.findall(r"^#print axioms (\S+)", source, re.MULTILINE))
    if not expected:
        raise ValueError("audit source contains no declarations")
    reported: Counter[str] = Counter()
    for match in REPORT.finditer(output):
        name, dependencies = match.groups()
        reported[name] += 1
        if dependencies is not None:
            axioms = {item.strip() for item in dependencies.split(",")}
            unexpected = axioms - ALLOWED
            if unexpected:
                raise ValueError(f"{name}: forbidden axioms {sorted(unexpected)}")
    if REPORT.sub("", output).strip():
        raise ValueError("unrecognized output in axiom audit")
    if reported != expected:
        raise ValueError(f"audit declarations differ: missing={expected - reported}, extra={reported - expected}")
    return sum(reported.values())


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_axioms.py AXIOM_OUTPUT", file=sys.stderr)
        return 2
    try:
        count = validate(Path(__file__).with_name("Audit.lean").read_text(), Path(sys.argv[1]).read_text())
    except (OSError, ValueError) as error:
        print(f"axiom audit FAILED: {error}", file=sys.stderr)
        return 1
    print(f"{count} axiom reports verified; only standard Lean axioms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
