# Submission letter -- JOSS

The paper (`paper.md`, `paper.bib`) is tracked on the default branch of the repository,
which is what the JOSS submission form's branch field names. This letter is the
free-text part of the form, or an email to the handling editor; the checklist below it
is the working list to clear before the form is filled in.

## BEFORE SUBMITTING -- checklist

Read against <https://joss.readthedocs.io/en/latest/submitting.html> on 3 October 2026;
the policy text cited below is from that page.

1. **Six months of public history (hard gate, "Must meet", item 1).** The repository
   was created public on 2026-09-30 and its commits span 2026-09-30 to 2026-10-02.
   JOSS runs automated checks on commit distribution and desk-rejects a repo that went
   public immediately before submission. Earliest realistic submission date is
   **2027-04-01**, and only if the interim shows continued public development: keep
   committing openly, tag further releases (v0.1.x), and let issues/PRs accumulate.
   A desk rejection now would burn the first impression; the gaps are fixable by
   waiting, not by writing.
2. **Demonstrated research impact (hard gate, item 2).** "Aspirational statements
   about future use are not sufficient." The evidence that exists today is the two
   companion developments pinning this library by commit. Land their papers or arXiv
   preprints (they cite this library as the home of the shared statements) **before**
   submitting, and cite them in the Research impact statement of `paper.md` as
   references rather than promises.
3. **AI usage disclosure (policy is strict).** The disclosure in `paper.md` follows
   the phase paper's acknowledgement style (tool and scope named plainly) and names
   DeepSeek-V4.1-Flash via the Claude Code agent for this repository's sessions. That
   name was checked against the record rather than assumed: every turn of this
   repository's sessions is logged with the model that served it, and all of them are
   the same DeepSeek flash model the phase paper's acknowledgement names. Re-read every
   sentence until each one is true of what actually happened; JOSS treats an
   incomplete or inaccurate disclosure as an ethical breach, and the January 2026
   policy explicitly looks for the human design decisions, which the section names.
4. **Acknowledgements.** Filled from the phase paper's funding: NSFC Grant
   No. 12674609 and Guangdong Provincial Key Laboratory of Computility
   Microelectronics Grant No. 2024B1212010007. Confirm both grants cover this
   software work before submitting.
5. **ORCID.** 0000-0002-9855-3812, already in `paper.md`'s author metadata; the
   submission form signs in with it, and the same identifier disambiguates the
   Google Scholar author profile.
6. **Paper and software together on the default branch.** `paper/paper.md` and
   `paper/paper.bib` are tracked in this repository, so the form's repository and
   branch fields are simply the repository URL and its default branch. Keep the paper
   in step with the repository: a number quoted in the paper (58 modules, 25-of-58 CI
   scope, 77 GiB peak, the audit-region length in `main.tex`) is a repository fact,
   and the same gates that pin it on `main` pin it in the paper.
7. **Colleague smoke test.** JOSS asks that "if your software is new, please be sure
   a colleague has tried it": have someone outside the machine that built it run
   `env -u LEAN_PATH lake build` on a fresh clone and the four gates, and say so in
   the review thread. The README's memory warning (77 GiB peak for a full build)
   must be told to the reviewers too, so nobody burns a runner on it.
8. **Compile the paper before submitting.** Whedon, the editorial bot, compiles
   `paper.md` itself from the branch named in the form; a dry run with the same
   pipeline avoids a broken preview in the review issue:
   `docker run --rm --volume $PWD/paper:/data --user $(id -u):$(id -g) --env
   JOURNAL=joss openjournals/inara`. Check the word count stays within 750-1750
   (1,176 as of 3 October 2026).
9. **Main subject of the paper.** "Logic and formal methods" (Track 7, CSISM --
   Computer science, Information Science, and Mathematics). The subject list lives in
   `lib/tracks.yml` of `openjournals/joss`; the closest precedent, the Agda standard
   library paper (JOSS 10.21105/joss.09241), is routed to the same track. The Physics
   and Engineering track has no quantum-information field, so the quantum side is
   carried by the paper's tags instead.
10. **At acceptance.** Make a tagged release, deposit it on Zenodo (the concept DOI
    10.5281/zenodo.23056679 already fronts all versions), and post the version number
    and DOI in the review thread; JOSS then deposits the paper's metadata with
    Crossref, which is what Google Scholar indexes.

## The letter

To the Editors,
Journal of Open Source Software

3 October 2026 (update the date when submitting)

Dear Editors,

Please consider "QECCertificates: checkable distance certificates for quantum error
correction" for publication in the Journal of Open Source Software.

QECCertificates is a Lean 4 library that makes a claim about a quantum error-correcting
code's distance checkable without repeating the search that produced it. Distances of
quantum low-density parity-check codes are found by search, and the field's public
tables record many of them as upper bounds precisely because certifying a number costs
more than finding it; a reader must either trust the search tool or redo the search.
The library replaces that trust with proof objects: an encoding of the distance
question as a satisfiability instance whose faithfulness is proved in both directions,
an in-kernel checker for the LRAT proof format with a proved soundness theorem that
shares no code with any solver, and kernel-checked code instances. An audit region
prints, for every non-private theorem and lemma in the package, the axioms it depends
on; no declaration goes beyond the three standard axioms of Lean's logic. The package
is a mathematical library in the sense of JOSS's definition of research software.

On scope and significance, per the criteria now in force:

- **Design thinking.** The load-bearing decision is the separation of search from
  check. The nearest prior work, Lean-QEC, replays a solver's proof inside a proof
  assistant and reports that the replay is what limits scale; our design keeps the
  untrusted search entirely outside the argument and checks a standard proof format,
  so the solver is exchangeable. The costs of the in-kernel design are paid openly:
  continuous integration builds only the modules whose measured memory peak fits a
  hosted runner, from a table the build fails without.
- **Open-source practice.** Apache-2.0; the repository is public, browsable and
  cloneable without registration, with an open issue tracker; four static gates and a
  scoped Lean build run on every push; releases are tagged (v0.1.0, v0.1.1) and
  archived (Zenodo concept DOI 10.5281/zenodo.23056679); documentation consists of a
  bilingual README pair, module-level docstrings and a CONTRIBUTING guide; portability
  is enforced by a gate that rejects machine-coupled paths and unpinned dependencies.
  The paper (`paper/paper.md`) is tracked beside the software it describes.
- **AI usage.** Development and drafting used the Claude Code agent (DeepSeek-V4.1-Flash)
  under my direction; the paper carries a full AI usage disclosure in the sense of the policy
  of January 2026, and the design decisions named above are mine, checked as described
  there. [Re-verify each sentence of the disclosure before submitting.]

Declarations, per JOSS policy:

- **Related publications** (co-publication policy): two companion papers, both in
  preparation, build on this library and cite it as the home of their shared
  statements; a further white paper on the Python side of the certificate chain is
  planned. I will keep the handling editor informed of their status during review.
- **Conflict of interest:** I am employed by Pengxin Quantum Technology (Shenzhen)
  Co., Ltd., one of the affiliations of this work. [Add or correct as applicable.]
- **Funding:** National Natural Science Foundation of China (Grant No. 12674609) and
  the Guangdong Provincial Key Laboratory of Computility Microelectronics (Grant
  No. 2024B1212010007).

The submitting author is the sole author of the paper and the major contributor of the
software. Questions and review are welcome in the public review thread; I can suggest
potential reviewers from the formal-verification and quantum-error-correction
communities on request.

Sincerely,

Shuoming An
Faculty of Computility Microelectronics,
Shenzhen University of Advanced Technology
anshuoming@suat-sz.edu.cn
