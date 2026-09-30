# QECCertificates

[![build](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml/badge.svg)](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
![Lean](https://img.shields.io/badge/Lean-v4.34.0-blueviolet)

**English** | [简体中文](README.zh-CN.md)

**Certified code parameters and fault distances for quantum error correction.**
A Lean 4 library that replaces "trust the solver" with "check the certificate".

**Contents:** [Why this exists](#why-this-exists) ·
[What is here](#what-is-here) · [Guarantees](#guarantees) ·
[Build](#build) · [Verify](#verify) · [Citation](#citation) · [License](#license)

## Why this exists

Code parameters are found by search, and a search ends in a solver's verdict. The public
schema behind the qLDPC Challenge records what that costs: a distance that is not
certified is reported as an upper bound, for a non-CSS code because the Pauli-weight
certifier "is not available yet", for a circuit-level distance because an exact tier "is
deferred future work", and what exists in between is, in the schema's own words, evidence
but not a proof.

There are two ways out: trust the tool that printed the number, or make the number come
with something a third party can check. This library is the second way, on the formal
side. The encoding of the search problem, the soundness of the certificate checker, and
the composition of the two are theorems, and every load-bearing declaration is printed in
an audit region so that a reader can see which axioms it rests on.

## What is here

| Layer | Contents |
|---|---|
| `QECCertificates/GF2/` | GF(2) linear algebra: trusted row reduction, kernel bases, rank certificates, dual witnesses, exact-distance bracketing, certificate sizes, hypergraph and lifted products, the Künneth formulas |
| `QECCertificates/Pauli/` | the operator-tree ↔ symplectic-representation translation |
| `QECCertificates/Reflect/` | the certificate framework: a kernel-checked LRAT/RUP checker with its soundness theorem, encoding faithfulness in both directions, where a model of the CNF **is** a light logical operator, symmetry breaking that preserves unsatisfiability, and the worked replays of the solver certificates used here |
| `QECCertificates/Codes/` | the code-theoretic layer: stabilizer, CSS and subsystem codes; gauging and measurement-protocol representations; the shared instance families (Bacon–Shor, BB, HGP, lifted product) |
| [`tools/check_axioms.py`](tools/check_axioms.py) | reads a build log and refuses any declaration whose `#print axioms` line is not exactly the three standard axioms |

**55 modules**, and the audit region covers **every** non-private `theorem`/`lemma` in
the package. This repository has no un-audited corner.

## Guarantees

* zero `sorry`, zero custom axioms, zero `native_decide`;
* each audited declaration depends on exactly `propext`, `Classical.choice` and
  `Quot.sound`;
* the certificate checker shares no code with any solver: an UNSAT verdict is re-derived
  from the formula and the proof file alone;
* portability is a requirement, not an aspiration: no machine-coupled paths, every
  dependency pinned by a full 40-character revision hash, LF line endings everywhere.

## Build

Lean `v4.34.0` (pinned in `lean-toolchain`) and mathlib at the revision pinned in
`lakefile.toml` are fetched by `lake`:

```bash
env -u LEAN_PATH lake build
```

The pinned dependencies are heavy: a full build wants a machine with a large memory
budget, because the audit region alone elaborates every theorem in the library. On a
machine that already has a global Lean checkout, [`setup_links.sh`](setup_links.sh) links the project to
it. The script selects layers by the revisions in `lake-manifest.json` rather than by
directory names, and verifies the result, which saves a download and a dependency build.

## Verify

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
  title     = {{QECCertificates}: certified code parameters and fault distances},
  author    = {An, Shuoming},
  year      = {2026},
  doi       = {10.5281/zenodo.23056679},
  url       = {https://github.com/QCL-SUAT/QECCertificates}
}
```

Zenodo mints two numbers from one deposit: this concept DOI, which always resolves to
the newest version, and a DOI for each archived artifact in it (10.5281/zenodo.23056680
for the artifact deposited first). The machine-readable form is in [`CITATION.cff`](CITATION.cff).

## License

Apache-2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). The three dependencies
(mathlib, Lean-QEC, QECLean) are fetched by `lake` at the pinned revisions; none of them
is vendored here. How to contribute is in [`CONTRIBUTING.md`](CONTRIBUTING.md).
