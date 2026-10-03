# Working in this repository

QECCertificates is a Lean 4 library: the certificate framework and the code instances
behind the two companion developments that import it. `README.md` says what the library
contains and what it guarantees, `CONTRIBUTING.md` says how a change is made, and this
file is the short version for a working session. Where the two of them already say
something, this file points at them rather than repeating it.

**Numerics default to Julia** (global rules, the "numerical tooling" section): new numerical work starts in Julia; falling back to Python needs a measured reason, not a hunch.

## The gates

Four static gates, each with a self-test, all of them part of a change:

    python tools/check_portability.py    --self-test
    python tools/check_readme_pair.py    --self-test
    python tools/check_audit_coverage.py --self-test
    python tools/ci_scope.py             --self-test --check

Run the self-test as well as the gate: a gate that has only ever printed PASS is an
assumption. None of the four needs the Lean toolchain, so all four are worth running
before a build.

`check_readme_pair.py` checks the two READMEs against each other, and each of them for
whitespace hygiene -- trailing spaces, tabs, odd spaces, CRLF, and, on the Chinese side,
a space between a Chinese character and the Latin or code beside it. `ci_scope.py --check`
checks them against the tree, which is a different question: the pair can be in step and
both wrong, and theirs are the counts a reader takes on trust. Its three numbers come
from the tree, so a reworded sentence that it can no longer read is a failure rather
than a pass.

## The build and the audit

    env -u LEAN_PATH lake build > build.log 2>&1
    python tools/check_axioms.py build.log

`env -u LEAN_PATH` matters: this checkout is wired to a shared mathlib by
`setup_links.sh`, and an inherited `LEAN_PATH` resolves against a stale layer.

The build is memory-heavy, by design: this is a library whose statements are meant to be
closed by kernel reduction, which is what makes the claims mean something. `tools/ci_scope.py`
holds the measured peak of every module and its docstring holds the recipe for measuring
a new one; that measurement is what decides whether continuous integration can afford to
build a module, and a module with no entry fails the gate. A full build needs a machine
of the class the README names, so the audit runs there and not in the runner.

`check_axioms.py` reads `#print axioms` output out of a build log, and a cached build does
not replay that output: after a warm rebuild, touch the root module or delete its `.olean`
before running the audit, or the gate will report that nothing was audited.

A build that is interrupted leaves the module it was compiling without its `.olean`,
while the module's `.trace` and `.olean.hash` stay behind, so the next compile of a
downstream module fails with `object file ... does not exist`. That is a hole to refill
with `lake build <module>`, not a broken cache. Do not kill a running `lake build` unless
the artifacts it will leave behind are a price worth paying.

## Adding a module

`CONTRIBUTING.md` carries the checklist. The two steps that get forgotten are the audit
region -- every non-private `theorem`/`lemma`, not only the load-bearing ones -- and the
measured peak in `tools/ci_scope.py`. Both are gated, so forgetting them fails in
continuous integration instead of in review.

## Dependencies

mathlib, Lean-QEC and QECLean are pinned by full 40-character revision in `lakefile.toml`
and `lake-manifest.json`, never by a tag or a short hash. Nothing is vendored.

## Session context

`.claude/settings.local.json` is untracked and excludes most of the user's rule files from
a session started here, to leave room in the harness's instruction budget. That affects
what is injected at startup only: the excluded files stay on disk, are read on demand, and
nothing about where a lesson is written down changes.
