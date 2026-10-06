# QECCertificates

<div align="center">

![The QECCertificates logo: five qubits on a ring around a checkmark](assets/logo/qeccertificates-logo.svg)

</div>

[![build](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml/badge.svg)](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
![Lean](https://img.shields.io/badge/Lean-v4.34.0-blueviolet)

**English** | [简体中文](README.zh-CN.md)

A Lean 4 library of machine-checked distance certificates for quantum error correction.

## Overview

QECCertificates formalizes three things and the way they compose: the encoding of a
code-parameter search as a satisfiability problem; a certificate checker for the solver's
answer whose soundness is a theorem; and the translation between the operator-tree and
symplectic descriptions of a Pauli operator that the encoding rests on. Every load-bearing
declaration is printed in an audit region, so a reader can see which axioms it depends on
rather than having to trust the tool that printed a number.

Around that spine the library carries the layers in which a fault-tolerance statement is
read: the cochain complexes of a circuit with their mapping cones and Künneth formulas,
spacetime fault distance, the cosystolic distance, the auxiliary hypergraph that gauging
generalizes to, and the subcode layer between them. It also carries the abstract closure
theorem for syndrome-exhaustive check matrices, which is the dichotomy every weight-1
decoder lives in.

The library is developed alongside the two companion developments that import it. It is a
self-contained Lake package: its dependencies are fetched at pinned revisions, and none of
them is vendored.

## Motivation

Code parameters are found by search, and a search ends in a solver's verdict. The public
schema behind the qLDPC Challenge records what that costs: a distance that is not
certified is reported as an upper bound, for a non-CSS code because the Pauli-weight
certifier "is not available yet", for a circuit-level distance because an exact tier "is
deferred future work", and what exists in between is, in the schema's own words, evidence
but not a proof.

There are two ways out: trust the tool that printed the number, or make the number come
with something a third party can check. This library is the second way, on the formal
side: the encoding of the search problem, the soundness of the certificate checker, and
the composition of the two are theorems.

## Repository layout

| Layer | Contents |
|---|---|
| `QECCertificates/GF2/` | GF(2) linear algebra: trusted row reduction, kernel bases, rank certificates, dual witnesses, exact-distance bracketing, certificate sizes, hypergraph and lifted products, the Künneth formulas |
| `QECCertificates/Pauli/` | the operator-tree ↔ symplectic-representation translation |
| `QECCertificates/Reflect/` | the certificate framework: a kernel-checked LRAT/RUP checker with its soundness theorem, encoding faithfulness in both directions, where a model of the CNF **is** a light logical operator, symmetry breaking that preserves unsatisfiability, and the worked replays of the solver certificates used here |
| `QECCertificates/Codes/` | the code-theoretic layer: stabilizer, CSS and subsystem codes; gauging and measurement-protocol representations; the shared instance families (Bacon–Shor, BB, HGP, lifted product); the abstract closure theorem for syndrome-exhaustive check matrices |
| `QECCertificates/Homology/` | chain complexes over GF(2) and the distances they carry: the mapping cone and its snake formula, the four-term fault complex with its Künneth formulas, spacetime fault distance, the cosystolic distance, modular expansion, detector decomposition, port functions, the auxiliary hypergraph and the subcode layer |
| [`tools/check_axioms.py`](tools/check_axioms.py) | reads a build log and refuses any declaration whose `#print axioms` line names an axiom outside the three standard ones |

The package is **77 modules**, and the audit region covers **every** non-private
`theorem`/`lemma` in it.

## Guarantees

* zero `sorry`, zero custom axioms, zero `native_decide`;
* no audited declaration depends on an axiom outside `propext`, `Classical.choice` and
  `Quot.sound`; a declaration that needs fewer of them, or none, is equally acceptable;
* the certificate checker shares no code with any solver: an UNSAT verdict is re-derived
  from the formula and the proof file alone;
* portability is enforced by a gate: no machine-coupled paths, every dependency pinned by
  a full 40-character revision hash, LF line endings throughout.

## Requirements

Lean `v4.34.0`, pinned in `lean-toolchain`, and mathlib at the revision pinned in
`lakefile.toml`, both fetched by `lake`. A full build wants a machine with a large memory
budget, because the audit region alone elaborates every theorem in the library.

On a machine that already has a global Lean checkout, [`setup_links.sh`](setup_links.sh)
links the project to it. The script selects layers by the revisions in
`lake-manifest.json` rather than by directory names, and verifies the result, which saves
a download and a dependency build.

## Build

```bash
env -u LEAN_PATH lake build
```

Twelve of this package's own modules close their statements by kernel reduction over an
object large enough to need more memory than a runner can give one process. The budget is
ten gigabytes, which leaves a 16 GB runner room for the toolchain and the system, and the
largest module, the separation instances, peaks at **77 GiB**. Continuous integration
therefore builds **40 of the 77 modules**: every module whose measured peak fits the
budget, together with everything those modules import, since lake cannot build one without
the other. It builds them one at a time and in import order, because the budget is what one
process needs: with a module's imports already built, the call that builds it has nothing
else to schedule, and lake would otherwise keep as many modules in flight as the runner has
cores, which is how a job dies of memory with no error line of its own.
[`tools/ci_scope.py`](tools/ci_scope.py) holds the measured peak of every module, computes
that set, and fails when the tree and the table disagree, so a module has to be measured
before continuous integration will build it. The audit region is the root module, which
imports the whole library, so the axiom audit runs on a machine with the memory for a full
build, as under Verification below, and not in the runner; every run prints what it left
out.

## Verification

```bash
env -u LEAN_PATH lake build > build.log 2>&1
python3 tools/check_axioms.py build.log
```

The gate refuses any declaration outside the three standard axioms, and it treats "nothing
audited" as a failure rather than a pass. That last part matters on a fresh clone: a fully
cached build does not replay `#print axioms` output, so if the script reports zero
declarations, delete the root module's `.olean` or touch its source and build again.

## Citation

If you use this library in academic work, cite the archived release. [`CITATION.cff`](CITATION.cff)
carries the same information in machine-readable form.

```bibtex
@software{qeccertificates,
  title     = {{QECCertificates}: checkable distance certificates for quantum
              error correction},
  author    = {An, Shuoming},
  year      = {2026},
  doi       = {10.5281/zenodo.23056679},
  url       = {https://github.com/QCL-SUAT/QECCertificates}
}
```

## Contributing

How a change is made, and what a change has to pass, is in
[`CONTRIBUTING.md`](CONTRIBUTING.md). In short: the four static gates and their self-tests
run before a build, and a new module needs its audit-region entry and its measured peak.

## License

Apache-2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). The three dependencies
(mathlib, Lean-QEC, QECLean) are fetched by `lake` at the pinned revisions; none of them
is vendored here.

## Support

Questions and bug reports go to the [issue
tracker](https://github.com/QCL-SUAT/QECCertificates/issues). A report that carries the
pinned revisions and the tail of the build log gets a useful answer fastest. Support is
best effort: there is no service-level agreement, and the Build section above is the
first thing to try before opening an issue.
