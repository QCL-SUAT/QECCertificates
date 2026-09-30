#!/usr/bin/env python3
"""Axiom audit: every `#print axioms` line that comes from this package must show
exactly the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Why this exists: "no custom axioms" is the kind of claim that is either machine-checked
or it is marketing.  Lean prints the axioms of a declaration on request; this script
reads that output out of a build log and refuses anything outside the standard three.
The audit region of the root module prints exactly the load-bearing declarations, so
covering the root module's own lines covers the claim.

Lean's output folds long axiom lists across lines; the reader joins continuation lines
until the closing bracket, because a folded list read line by line produces a bogus
axiom whose name ends in a comma.

Usage:  check_axioms.py <build.log>
Exit:   0 = at least one declaration audited, all of them exactly the standard three;
        1 = an axiom outside the standard three, or nothing audited at all (not
            "nothing to check" -- a fresh clone with no `#print axioms` output must
            not read as a pass).
"""
import io
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT_PREFIX = "info: QECCertificates.lean:"


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_axioms.py <build.log>", file=sys.stderr)
        return 2
    lines = io.open(sys.argv[1], encoding="utf-8", errors="replace").read().split("\n")

    audited, bad, i = 0, [], 0
    while i < len(lines):
        ln = lines[i]
        if ln.startswith("info:") and "depends on axioms:" in ln:
            buf = ln
            while "]" not in buf and i + 1 < len(lines):
                i += 1
                buf += " " + lines[i]
            if ln.startswith(ROOT_PREFIX):
                m = re.search(r"depends on axioms: \[(.*?)\]", buf)
                if m:
                    audited += 1
                    names = [x.strip() for x in m.group(1).split(",") if x.strip()]
                    extra = [x for x in names if x not in ALLOWED]
                    if extra:
                        bad.append((buf.strip()[:140], extra))
        i += 1

    print(f"audited {audited} declaration(s) printed in the root module's audit region")
    for ctx, extra in bad:
        print(f"FAIL outside the standard three: {extra}\n  {ctx}")
    if audited == 0:
        print("FAIL: nothing audited -- the build log carries no `#print axioms` "
              "output for this package (a cached build does not replay it; delete the "
              "root module's .olean or touch its source and rebuild)")
        return 1
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
