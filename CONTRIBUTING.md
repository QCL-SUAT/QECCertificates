# Contributing

## Build

Lean `v4.34.0`, installed through `elan` and pinned in `lean-toolchain`. The dependencies
(mathlib, Lean-QEC, QECLean) are pinned by full revision hash in `lakefile.toml` and
fetched by `lake`; nothing is vendored.

```bash
env -u LEAN_PATH lake build
```

## The gates every change has to pass

The static gates cost seconds and need no toolchain, so they run first, in continuous
integration and on your machine alike:

```bash
python3 tools/check_portability.py      # machine-coupled paths, tracked build residue
python3 tools/check_readme_pair.py      # the two READMEs, section for section
python3 tools/check_audit_coverage.py   # every non-private theorem has an audit line
python3 tools/ci_scope.py --check       # every module has a measured memory peak
```

Each takes `--self-test` as well, and a gate that has only ever printed PASS is an
assumption, so run that too.

Then the build and the audit, on a machine with the memory for it:

```bash
env -u LEAN_PATH lake build > build.log 2>&1
python3 tools/check_axioms.py build.log
```

The build must be free of errors, and free of warnings from this package (warnings from a
dependency are not ours to fix). The gate then reads the audit region out of the build log
and refuses any declaration whose `#print axioms` line names an axiom beyond `propext`,
`Classical.choice` and `Quot.sound`. Declarations that depend on fewer, or on none at all,
are welcome.
`sorry`, `admit`, custom `axiom` declarations and `native_decide` are not.

A cached build does not replay `#print axioms` output, so the gate treats "nothing
audited" as a failure: after a warm rebuild, touch the root module or delete its `.olean`
before running it.

## Adding a module

1. put the file under `QECCertificates/<Layer>/`;
2. import it from the root module `QECCertificates.lean`;
3. append its `#print axioms` lines to the audit region at the end of that file, one
   commented section per module;
4. add a row for it to the module table in the root module's docstring;
5. measure it and record the peak in `tools/ci_scope.py`, because the scope of the
   continuous-integration build is computed from that table and a module with no entry
   fails the scope gate;
6. add a row to `README.md` if it opens a new layer; either way both READMEs now
   state the wrong number of modules, and `tools/ci_scope.py --check` fails until
   they are brought back in step, which is the point of that gate reading the prose;
7. rebuild.

Step 2 is not optional: the gate audits what the build printed, so a module that is never
compiled is never audited, and nothing else would notice.

## Style

* Module headers (`/-! ... -/`) and declaration docstrings (`/-- ... -/`) are written in
  English, for readers outside this project. Say what the module establishes, and say what
  it does not: a stated boundary is part of the result.
* A docstring's claims must be the claims of the declaration under it. If a statement is
  carried over from a dependency rather than proved here, say so.
* Mathematical notation goes in `$...$`, identifiers in backticks.
* LF line endings, no trailing whitespace.
* No machine-coupled paths anywhere: no absolute paths, no home directories, no `/tmp`.
  Anything a script reads or writes is relative to the script's own location.
* Dependencies are pinned by full 40-character revision hash, never by a tag or a short
  hash: a tag exists only in the checkout that created it.

## Licensing of contributions

Contributions are accepted under the license the project already carries: by opening a
pull request you agree that your contribution is licensed under Apache-2.0, as set out in
section 5 of `LICENSE`. No copyright assignment is requested or implied, so the copyright
of each contribution stays with whoever wrote it, and the project's own rights stay with
the copyright holder named in `LICENSE` and `NOTICE`.
