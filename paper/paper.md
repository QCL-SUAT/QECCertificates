---
title: 'QECCertificates: checkable distance certificates for quantum error correction'
tags:
  - quantum error correction
  - formal verification
  - Lean
  - proof certificates
  - satisfiability solving
authors:
  - name: Shuoming An
    affiliation: "1, 2, 3"
    orcid: 0000-0002-9855-3812
affiliations:
  - index: 1
    name: Faculty of Computility Microelectronics, Shenzhen University of Advanced Technology, Shenzhen, China
  - index: 2
    name: Guangdong Provincial Key Laboratory of Computility Microelectronics, Shenzhen, China
  - index: 3
    name: Pengxin Quantum Technology (Shenzhen) Co., Ltd., Shenzhen, China
date: 3 October 2026
bibliography: paper.bib
---

# Summary

A quantum computer stores information in a quantum error-correcting code, and one number
measures how well the code protects it: the distance, the weight of the smallest error
the code cannot detect. Good codes are found by search -- enumerate candidates, compute a
distance for each -- and that computation is expensive enough that the public tables of
the field record many distances as upper bounds rather than proven facts, because
certifying a number costs more than finding it. QECCertificates [@qeccertificates] is a
Lean 4 library that makes a distance claim checkable without repeating the search. It
carries the linear algebra over the two-element field that such claims rest on, the
translation from quantum-mechanical Pauli operators to bit-vectors, an in-kernel checker
for the machine-readable format in which satisfiability solvers record their refutations,
and proofs that the encoding connecting codes to formulas is faithful in both directions.
A solver's verdict, once rendered as a certificate file, is then re-derived by the Lean
kernel itself. The library has 58 modules; every non-private theorem and lemma is printed
in an audit region together with the axioms it depends on, and no declaration rests on
any axiom beyond the three standard ones of Lean's logic.

# Statement of need

The need is stated in the field's own data. The public schema behind the qLDPC Challenge
[@qldpcchallenge] records what a search leaves open: a distance that is not certified is
reported there as an upper bound, for a non-CSS code because the Pauli-weight certifier
"is not available yet", and for a circuit-level distance because an exact tier "is
deferred future work"; what exists between an upper bound and a proof the schema itself
calls evidence. A reader of such a table has two options -- trust the program that
printed the number, or redo the search. This library is the second way out, on the formal
side: the encoding of the search problem, the soundness of the certificate checker, and
the composition of the two are theorems, so the search may be as fast, as heuristic and
as untrusted as its users like, because it is no longer part of the argument. The
intended users are the groups that search for and tabulate quantum low-density
parity-check codes [@breuckmann2021], the authors of code tables who want their numbers
to carry proofs,
and formal-methods researchers who need certified code parameters as hypotheses rather
than as trust.

# State of the field

The closest prior work is Lean-QEC [@leanqec], which turns the distance question into a
satisfiability question and replays the solver's proof inside a proof assistant; its
authors report a reach of 90 qubits and state that at 144 qubits the replay itself is the
wall. That architecture binds the check to the search: the proof travels with the solver
run. QECCertificates takes the other road, and the road was chosen deliberately. The
refutation format LRAT [@cade2017], the descendant of the clausal proofs that DRAT-trim
checks for the competitions [@wetzler2014], is the classical satisfiability community's
standard for checkable unsatisfiability proofs, so a checker for it -- proved sound, running in
the kernel, sharing no code with any solver -- accepts certificates from any solver that
emits the format, and the search stays outside the trusted base entirely. The library is
not a patch to Lean-QEC, whose end-to-end pipeline serves its own purpose; it is the
shared, solver-independent layer beneath it, built on mathlib [@mathlib] and Lean 4
[@lean4], extending that ecosystem rather than duplicating it. We are not aware of
another formal library in this area that separates the two roles in this way.

# Software design

The library is layered, and the layering is the design. At the bottom, GF(2) linear
algebra: row reduction with a proved pivot invariant, kernel bases, rank certificates,
dual witnesses, weight-limited enumeration with a covering theorem, and the hypergraph [@tillichzemor]
and lifted [@panteleev2022] products with the Künneth formulas that make their distances
computable in pieces. Above it a Pauli layer translating operator trees to the symplectic
bit-vector representation and back. Then the certificate framework: the LRAT/RUP checker
with its soundness theorem, the CNF encoding whose faithfulness is proved in both
directions -- a model of the encoded formula *is* a light logical operator -- and
symmetry breaking by lex-leader predicates whose reduction is proved rather than
assumed. On top, the code layer: stabilizer, CSS and subsystem codes, gauging and
measurement-protocol representations, and the shared instance families (Bacon-Shor
[@bacon2006], BB [@bravyi2024], hypergraph-product, lifted product).

Three trade-offs are worth naming. First, computation is kept in the kernel: statements
close by kernel reduction, so no checker outside the kernel is ever trusted. The price
is memory -- the largest module peaks at 77 GiB, so continuous integration builds the 25
of 58 modules whose measured peak fits a hosted runner, from a table of measured peaks
that fails the build when tree and table disagree, which is how a module comes to be
measured before it is built anywhere. Second, the proof format is standard rather than
bespoke: LRAT certificates are emitted by several solvers, which keeps the search
replaceable. Third, verification is architectural rather than incidental: an audit
region prints the axioms behind every non-private theorem and lemma, a script refuses
any axiom outside `propext`, `Classical.choice` and `Quot.sound`, and it treats "nothing
audited" as a failure, so a cached build that never replayed the audit lines cannot
pass as a pass. Four static gates -- portability, a bilingual README pair, audit
coverage, and CI scope -- run in seconds in every CI job before Lean is invoked at all.

# Research impact statement

The library is the shared formalization core of two companion developments, both of
which pin it by full commit hash. One builds an interface layer in which the row space
defined here is proved equal to the row space of Lean-QEC, the symplectic predicate is
proved equivalent to commutation of actual Pauli matrices, and a state on the logical
register is bounded by the logical dimension proved here. The other builds fault
complexes, the gauge-fixed instances, and a layer of conditions under which a logical
measurement succeeds, on the same core. The papers reporting those results are in
preparation and cite this library as the home of their shared statements, so a reader
can check the interface claims without reading either paper's repository. The instance
families carried here are the ones load-bearing for those developments.

# AI usage disclosure

The library, its documentation and the drafts of this paper were developed with the
Claude Code agent (DeepSeek-V4.1-Flash), working to the author's specification: the Lean
derivations, text polishing for this paper and for the module docstrings and the READMEs,
and the debugging of individual proof steps. The author reviewed, edited and validated all
AI-assisted output: every change compiled under the pinned toolchain and passed the
repository's four static gates, a full build and the axiom audit, and the problem framing,
the choice of what to prove, the layering of the library and what each gate enforces are
the author's decisions. The author remains responsible for the accuracy, originality,
licensing and ethical compliance of everything submitted.

# Acknowledgements

This work was supported by the National Natural Science Foundation of China under
Grant No. 12674609 and by the Guangdong Provincial Key Laboratory of Computility
Microelectronics under Grant No. 2024B1212010007.

# References
