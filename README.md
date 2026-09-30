# QECCertificates

[![build](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml/badge.svg)](https://github.com/QCL-SUAT/QECCertificates/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
![Lean](https://img.shields.io/badge/Lean-v4.34.0-blueviolet)

**Certified code parameters and fault distances for quantum error correction.**
A Lean 4 library that replaces "trust the solver" with "check the certificate".

Repository: <https://github.com/QCL-SUAT/QECCertificates> (Apache-2.0, anonymous clone).
Version 0.1.0 is tagged, and the two companion developments pin a full commit.

**Contents:** [Why this exists](#why-this-exists) ·
[What is here](#what-is-here) · [Guarantees](#guarantees) ·
[Build](#build) · [Verify](#verify) · [Roadmap](#roadmap) ·
[Paper](#paper) · [Provenance](#provenance) · [License and citation](#license-and-citation)

## Why this exists

Code parameters are found by search, and a search ends in a solver's verdict. The
public schema behind the qLDPC Challenge records what that costs: a distance that is
not certified is reported as an upper bound — for a non-CSS code because the
Pauli-weight certifier "is not available yet", for a circuit-level distance because an
exact tier "is deferred future work" — and what exists in between is, in the schema's
own words, evidence but not a proof.

There are two ways out: trust the tool that printed the number, or make the number
come with something a third party can check. This library is the second way, on the
formal side: the encoding of the search problem, the soundness of the certificate
checker, and the composition of the two are theorems, and every load-bearing
declaration is printed in an audit region so that a reader can see which axioms it
rests on.

## What is here

| Layer | Contents |
|---|---|
| `QECCertificates/GF2/` | GF(2) linear algebra: trusted row reduction, kernel bases, rank certificates, dual witnesses, exact-distance bracketing, certificate sizes, hypergraph and lifted products, the Künneth formulas |
| `QECCertificates/Pauli/` | the operator-tree ↔ symplectic-representation translation |
| `QECCertificates/Reflect/` | the certificate framework: a kernel-checked LRAT/RUP checker with its soundness theorem, encoding faithfulness in both directions — a model of the CNF **is** a light logical operator — symmetry breaking that preserves unsatisfiability, and the worked replays of the solver certificates used here |
| `QECCertificates/Codes/` | the code-theoretic layer: stabilizer, CSS and subsystem codes; gauging and measurement-protocol representations; the shared instance families (Bacon–Shor, BB, HGP, lifted product) |
| [`tools/check_axioms.py`](tools/check_axioms.py) | reads a build log and refuses any declaration whose `#print axioms` line is not exactly the three standard axioms |

**55 modules**, and the audit region covers **every** non-private `theorem`/`lemma` in
the package — this repository has no un-audited corner.

## Guarantees

* zero `sorry`, zero custom axioms, zero `native_decide`;
* each audited declaration depends on exactly `propext`, `Classical.choice` and
  `Quot.sound`;
* the certificate checker shares no code with any solver — an UNSAT verdict is
  re-derived from the formula and the proof file alone;
* portability is a requirement, not an aspiration: no machine-coupled paths, every
  dependency pinned by a full 40-character revision hash, LF line endings everywhere.

## Build

```bash
env -u LEAN_PATH lake build     # fetches mathlib, Lean-QEC and QECLean at the pinned revisions
```

The pinned dependencies are heavy; a full build wants a machine with a large memory
budget (the audit region alone elaborates every theorem in the library). On a machine
that already has a global Lean checkout, [`setup_links.sh`](setup_links.sh) links the project to it —
it selects layers by the revisions in `lake-manifest.json`, not by directory names,
and verifies the result — which saves a download and a dependency build.

## Verify

```bash
env -u LEAN_PATH lake build > build.log 2>&1
python3 tools/check_axioms.py build.log   # every audited declaration, three axioms only
```

A note for whoever runs this on a fresh clone: a fully cached build does **not** replay
`#print axioms` output, and the audit gate deliberately treats "nothing audited" as a
failure rather than a pass. If the script reports zero declarations, delete the root
module's `.olean` (or touch its source) and rebuild.

## Roadmap

v0.1 is the formal layer, and the two companion developments that share it now consume
it as a dependency: their GF(2), Pauli and shared code modules were deleted in favour of
imports pinned to a full revision, so the same statements build from one source. The
certificate toolchain next to the formal layer — the CNF encoder for distance lower
bounds with its known-value gate, the LRAT/RUP checkers in Python and C, and the
adapters that turn a check matrix into a certified bound — lands as `python/` in the
next version, followed by a white paper reporting its end-to-end results.

## Paper

[`paper/main.tex`](paper/main.tex) is the draft of that white paper: what the library contains, what is
machine-checked about it, how the two companion developments use it, and what it
deliberately does not do. It builds with `latexmk -pdf main.tex` and cites the
companion manuscripts, Lean-QEC and the qLDPC Challenge schema.

## Provenance

The shared core of this package was merged from two companion developments whose GF(2)
and Pauli layers had been duplicated, file by file, between them; the merge is recorded
in the two repositories' histories, and their two papers cite this package as the home
of that layer. Every statement moved without a single proof being rewritten — the
merge table shows, file by file, which side each module was taken from and what the
other side contributed into it.

## License and citation

Apache-2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). Citation metadata is in [`CITATION.cff`](CITATION.cff).
