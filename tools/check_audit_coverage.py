#!/usr/bin/env python3
"""Audit-coverage gate: every non-private theorem and lemma is printed in the root
module's audit region.

Why this exists: the README claims "the audit region covers every non-private
theorem/lemma in the package", and the white paper claims the same.  A coverage
claim is exactly the kind that goes stale silently -- a new theorem lands, nobody
adds its `#print axioms` line, and every existing check still passes, because
`check_axioms.py` reads the lines that are there and never asks what is missing.
This gate asks what is missing.

A declaration is matched by its last dotted component, since the audit region
spells names through whatever namespace the module opened.  A last-component match
can accept a same-named declaration from another module, so the unmatched list is
read as well: a name reported here is checked by hand, not trusted as absent.  The
gate is deliberately one-sided -- it catches a theorem that lost its audit line,
which is the way this claim goes stale.

Usage:  check_audit_coverage.py [--root DIR] [--self-test]
Exit:   0 = every non-private theorem/lemma has an audit line, and the scan found
            declarations at all; 1 = one is missing, or nothing was scanned.
"""
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile

DECL = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
AUDITED = re.compile(r"^#print axioms\s+([A-Za-z0-9_.']+)", re.M)
ROOT_MODULE = "QECCertificates.lean"
MODULE_DIR = "QECCertificates"
COMMENT = ("--", "/-", "*")


def tracked(root, pattern):
    out = subprocess.run(["git", "ls-files", pattern], cwd=root,
                         capture_output=True, text=True)
    if out.returncode != 0:
        return []
    return [p for p in out.stdout.split("\n") if p.strip()]


def declarations(root):
    """(file, name) for every non-private theorem or lemma in the package."""
    # `git ls-files <dir>` lists the directory recursively; a glob like
    # `QECCertificates/**/*.lean` silently skips a module that sits directly in
    # that directory, which is exactly the file a coverage gate must not miss
    files = [p for p in tracked(root, MODULE_DIR) if p.endswith(".lean")]
    if os.path.isfile(os.path.join(root, ROOT_MODULE)):
        files.append(ROOT_MODULE)
    out = []
    for rel in files:
        text = io.open(os.path.join(root, rel), encoding="utf-8").read()
        # strip line comments: a `theorem ...` inside a docstring is prose, not a
        # declaration, and counting it would demand an audit line for a name that
        # does not exist
        body = "\n".join(ln for ln in text.split("\n")
                         if not ln.lstrip().startswith(COMMENT))
        out += [(rel, name) for _kw, name in DECL.findall(body)]
    return out


def findings(root):
    """Problem strings; empty means the audit region covers the package."""
    decls = declarations(root)
    root_path = os.path.join(root, ROOT_MODULE)
    if not os.path.isfile(root_path):
        return ["%s not found -- nothing to cover" % ROOT_MODULE]
    audited = set(AUDITED.findall(io.open(root_path, encoding="utf-8").read()))
    if not decls:
        return ["no non-private theorem/lemma found -- the scan looked at nothing"]
    if not audited:
        return ["the audit region carries no `#print axioms` line"]
    last = set(n.rsplit(".", 1)[-1] for n in audited)
    missing = [(rel, n) for rel, n in decls
               if n.rsplit(".", 1)[-1] not in last]
    out = []
    for rel, name in missing:
        out.append("%s: %s has no `#print axioms` line in %s"
                   % (rel, name, ROOT_MODULE))
    return out


def self_test():
    bad = 0
    tmp = tempfile.mkdtemp(prefix="audit_cov_")
    try:
        mod = os.path.join(tmp, MODULE_DIR)
        os.makedirs(mod)

        def put(rel, text):
            io.open(os.path.join(tmp, rel), "w", encoding="utf-8",
                    newline="\n").write(text)

        def seed(audit_line):
            subprocess.run(["git", "init", "-q"], cwd=tmp, check=True)
            # a primed name (the audit region spells it with the apostrophe), a
            # private declaration (exempt), and a `theorem` inside a docstring
            # (prose, must not be demanded)
            put(MODULE_DIR + "/A.lean", "namespace QECCertificates.A\n"
                "/-- The theorem ghost : no such declaration exists. -/\n"
                "theorem one : True := trivial\n"
                "lemma two' : True := trivial\n"
                "private theorem hidden : True := trivial\n"
                "end QECCertificates.A\n")
            put(ROOT_MODULE, audit_line)
            # the gate reads tracked files, so the fixture has to be tracked
            subprocess.run(["git", "add", "-A"], cwd=tmp, check=True,
                           capture_output=True)

        # control 1: covered (two lines, one of them with an apostrophe) -> pass
        seed("#print axioms QECCertificates.A.one\n"
             "#print axioms QECCertificates.A.two'\n")
        got = findings(tmp)
        if got:
            print("  x control 1: a covered package reported %s" % got, file=sys.stderr)
            bad = 1
        else:
            print("  ok control 1: a covered package passes")

        # control 2: one line dropped -> must report exactly that declaration
        seed("#print axioms QECCertificates.A.one\n")
        got = findings(tmp)
        if not any("two" in m for m in got) or any("one" in m for m in got):
            print("  x control 2: a dropped audit line was not named: %s" % got,
                  file=sys.stderr)
            bad = 1
        else:
            print("  ok control 2: a dropped audit line is named")

        # control 3: an empty audit region -> must fail rather than pass quietly
        seed("")
        got = findings(tmp)
        if not got:
            print("  x control 3: an empty audit region passed", file=sys.stderr)
            bad = 1
        else:
            print("  ok control 3: an empty audit region fails")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return bad


def main():
    argv = sys.argv[1:]
    if "--self-test" in argv:
        print("audit-coverage gate, self-test:")
        return self_test()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if "--root" in argv:
        root = argv[argv.index("--root") + 1]
    problems = findings(root)
    print("audit-coverage gate: does the audit region name every non-private "
          "theorem and lemma?")
    for m in problems:
        print("  x " + m)
    if problems:
        print("\nFAIL: %d declaration(s) outside the audit region." % len(problems))
        return 1
    print("  ok every non-private theorem/lemma carries a `#print axioms` line")
    return 0


if __name__ == "__main__":
    sys.exit(main())
