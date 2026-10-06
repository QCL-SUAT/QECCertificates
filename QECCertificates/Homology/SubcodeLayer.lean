/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.AuxComplex
import QECCertificates.GF2.LowerBound

open QECCertificates

/-!
# The subcode layer: [14] §6.2's gauging-subcode distance, read as a code distance

This module supplies the layer left open by item 1 of the "honest boundary" section of
`Homology/AuxComplex.lean`. What that section records is: **this library has no "subcode"
layer**, so "the subcode $A_\bullet$ has distance 1" from [14] §6.2 cannot be
machine-checked in that module; what is checked there is only the 1-cosystolic distance
of the **auxiliary complex**, $d_1^\bullet = 1$ (`gauging_cosystolicDistance_eq_one`).
This module reads "the subcode" as a **genuine CSS code object** (with X checks, Z
checks, CSS compatibility, and two distances), and machine-checks that sentence of §6.2
at this layer.

## 1. The source (the sole source of this module's definitions, transcribed verbatim)

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895.

**§6.2, p.35** (the sentence the main theorem of this module must land):

> **Gauging logical measurement [56] can be seen as an instance of hypergraph surgery
> where the subcode $A_\bullet$ has distance 1, and therefore requires $O(d)$ rounds of
> syndrome measurement to maintain fault-distance $d$.**

**§6.1, p.33** (the **only** gloss of "the distance of $A_\bullet$" in that paper):

> The distance of $A_\bullet$ is the minimum number of check errors on the auxiliary
> system which are required to cause an undetectable logical measurement error in a
> single round; this is not the same as the single-shot distance of the entire deformed
> code, because there can be checks in the bulk which have far less protection against
> measurement errors.

**Definition 2.5, p.11** (the definition of the word "subcode" in that paper):

> **Definition 2.5 (Subcode).** *Let a subcode of the CSS code defined by a chain complex
> $C_\bullet$ be a code defined by the chain complex $A_\bullet$ with an injective chain map
> $f_\bullet : A_\bullet \to C_\bullet$. We stipulate further that $f_\bullet$ must take each
> data qubit in $A_\bullet$ to a single data qubit in $C_\bullet$, and the same for any
> $Z$ or $X$ checks in $A_\bullet$.*
>
> The additional stipulation is made to maintain control over weights, as this is essential
> for our analysis; if $C_\bullet$ is LDPC, so is $A_\bullet$. Each matrix in the chain map
> $f_\bullet$ is therefore a permutation matrix, up to some all-zero rows.

**§1.2, p.3** (the auxiliary complex and the 1-cosystolic distance):

> Then $H^\bullet = \mathbb{F}_2^W \xleftarrow{\ \delta_2\ } \mathbb{F}_2^V
> \xleftarrow{\ \delta_1\ } \mathbb{F}_2^E \xleftarrow{\ \delta_0\ } \mathbb{F}_2^C$
> is a 4-term cochain complex, where the coboundary maps $\delta_i$ are specified by the
> inclusion relations of $W, V, E, C$. […] By including $W$, we can now consider the
> 1-cosystolic distance of $H^\bullet$, which is
> $d_1^\bullet = \min\{|u| : u \in \ker(\delta_2) \setminus \mathrm{im}(\delta_1)\}$.

**Theorem 6.5, p.34** (the immediate context of the sentence in §6.2):

> Each auxiliary complex $(A_\bullet)_1, (A_\bullet)_2, (A_\bullet)_3, \dots,
> (A_\bullet)_\Lambda$ has 1-cosystolic distance $d_i \geq \alpha_i^{-1} d$ for
> $i \in [\Lambda]$, with sparse cycle bases.

**Lemma 7.12, p.38** (the **only** joining of "subcode" and "auxiliary complex" there):

> Let $H$ be a hypergraph with modular expansion $\mathcal M_d(H) \ge 1/L$. Let $H$
> correspond to the **degree-shifted subcode $A_\bullet$** with distance at least $d$.

**Appendix D, p.90** (the **only** "explanation" of "degree-shifting"):

> These relabellings correspond precisely to the degree-shifting of a mapping cone to
> recover the original chain map $f_\bullet$.

**Remark on Proposition 9.3, p.50** (another place where a distance of "$A_\bullet$" appears):

> When $Q$ is CSS and the set $S$ forms a $Z$-type subcode $A_\bullet$, $w$ is the
> $X$-distance of $A_\bullet$.

## 2. The verdict: that sentence of §6.2 does **not** provide a machine-checkable object

**Conclusion (one sentence)**: [14] §6.2 makes a single assertion -- it neither gives the
construction of the gauging auxiliary complex / subcomplex, nor writes the
"degree-shifting" between "the subcode $A_\bullet$" and "the 1-cosystolic distance of
$H^\bullet$" as a definition. **The missing piece is exactly that one sentence**: "after
relabelling $\delta_1, \delta_2$ one obtains the subcomplex $A_\bullet \hookrightarrow
C_\bullet$ in the sense of Def 2.5, and $\mathbb F_2^V$ is $C_1$." Accordingly this module
**does not claim** to reproduce the construction of the source; it gives a **minimal
self-consistent** subcode layer and writes out the correspondence with the source item by
item (see §4).

**How far the source goes** (with the evidence given item by item):

1. **"Distance" is glossed but not defined.** The sentence in §6.1 is operational prose
   ("minimum number of check errors on the auxiliary system which are required to cause an
   undetectable logical measurement error in a single round"); it does not say which space
   each of "check error", "undetectable", "logical measurement error" acts on, and the
   clause that immediately follows only states that "this is **not**" the single-shot
   distance of the entire deformed code. What **can** be pinned down is a formula: the
   $d_1^\bullet = \min\{|u| : u \in \ker(\delta_2) \setminus \mathrm{im}(\delta_1)\}$ of
   §1.2, while Theorem 6.5 states that the "1-cosystolic distance" of the auxiliary
   complexes $(A_\bullet)_i$ is exactly $d_i$.
2. **The word "$A_\bullet$" is used in two different places in the source**: in Def 2.5 it
   is a **subcomplex of the memory-code complex $C_\bullet$** (with an injective,
   basis-preserving chain map $f_\bullet$); in §1.2 / Thm 6.5 it is also the **auxiliary
   complex** (vertices = Z checks, hyperedges = data bits together with X gauge checks,
   $W$ = a chosen family of components). Lemma 7.12 joins the two with the single phrase
   "degree-shifted subcode", but "degree-shifting" is mentioned only once in the whole
   paper and only as a side remark of the form "these relabellings correspond precisely
   to ...", **not written as a construction**.
3. **Def 2.5 itself** gives "subcode = subcomplex + injective basis-preserving chain map".
   The library's existing `IsPortFunction` (`Homology/PortFunction.lean`) is exactly the
   **data-bit half** of that (basis-preserving, injective), but the **complex half** (the
   checks of $A$ and the differentials of $A$) has no object at all in this library.

**Therefore**: this module takes the formula of §1.2, reads $A_\bullet$ as a CSS code, and
machine-checks that sentence of §6.2 as **the distance of that code**.

## 3. This module's "subcode layer": definition and conventions

**Definition (the $A_\bullet$ of this module).** Given an auxiliary hypergraph
$H = (\{1..k\}, E)$ ($k$ vertices, $m$ hyperedges) and a chosen family of components
`W : Fin I → Finset (Fin k)` ([14] §1.2 footnote 1, p.3: $W$ is "a set of our choice and is
often not a basis of all components of $H$"), this module reads the **subcode
$A_\bullet$** as the CSS code **with $\mathbb{F}_2^V$ as its qubit space**:

* **X checks** $= \delta_2$ (`subcodeXChecks W`): each row is the indicator vector of a
  chosen component;
* **Z checks** $= \delta_1^{\mathsf T}$ (`subcodeZChecks H`): each row is the indicator
  vector of a hyperedge.

Three reasons this reading is not an arbitrary choice:

1. **CSS compatibility is the complex condition.** $\delta_2\,(\delta_1^{\mathsf T})^{\mathsf T}
   = \delta_2\delta_1 = 0$ is exactly `surgeryD2_mul_surgeryD1_eq_zero` (half of the "is a
   4-term cochain complex" of [14] §1.2). Thus **the CSS compatibility of the subcode is
   not a new hypothesis, but the complex condition itself** (`subcode_css`).
2. **The Z distance is exactly the $d_1^\bullet$ of §1.2.** `subcodeDistanceZ` is defined as
   the minimum weight of $\ker\delta_2 \setminus \mathrm{rowSpace}(\delta_1^{\mathsf T})$,
   and $\mathrm{rowSpace}(\delta_1^{\mathsf T}) = \mathrm{im}(\delta_1)$
   (`range_toLin'_eq_transpose_rowSpace`). So it is the formula of §1.2 and also the
   precisification, on the side of "check errors on the auxiliary system" (elements live in
   $\mathbb F_2^V$), of the gloss of §6.1.
3. **It lands on the same element set as the existing 1-cosystolic distance**:
   `isCosystolic_iff_subcode` proves `IsCosystolic H W u` (the predicate of
   `Homology/AuxComplex.lean`) $\iff$ $u \in \ker\delta_2$ and
   $u \notin \mathrm{rowSpace}(\delta_1^{\mathsf T})$. The two predicates were written down
   independently, and the iff pins their witness sets to be the same -- this is the machine
   evidence that the "subcode layer" and the "auxiliary-complex layer" speak of one and the
   same thing.

**The machine check of §6.2** (`subcodeDistanceZ_eq_one`): on an even hypergraph (a
2-regular hypergraph / a graph is the minimal case), as long as the chosen family of
components `W` avoids some vertex `v`, **the Z distance of the subcode is exactly 1** --
the upper bound is a single-vertex cochain $\{v\}$ (**one check error**, exactly the object
counted in the gloss of §6.1), and the lower bound is given by "$\{v\} \notin
\mathrm{im}\,\delta_1$" (a parity argument on the even hypergraph).

## 4. Honest boundary (the paper's main text cites this paragraph)

**Verbatim from the source**: (i) the sentence of §6.2 itself; (ii) the 1-cosystolic
distance formula of §1.2 (this module's `subcodeDistanceZ`, after unfolding, is identical
term by term); (iii) the complex condition of §1.2 (this module's `subcode_css`); (iv)
Theorem 6.5's use of the distance of $A_\bullet$ (the same quantity, the same symbol).

**Merely "compatible with the source", not "verbatim"**:

1. **Reading $A_\bullet$ as "the CSS code with $\mathbb F_2^V$ as its qubit space" is this
   module's choice**, not the source's construction. The source's $A_\bullet$ is, in
   Def 2.5, a **subcomplex of the memory-code complex $C_\bullet$** (whose qubits are a
   subset of the memory code's data bits, injected through the basis-preserving chain map
   $f_\bullet$), and, in §1.2 / Thm 6.5, the auxiliary complex. **That phrase
   `degree-shifted subcode` between the two is left undefined**, and this module **does
   not** prove that identification; it only establishes "once read as a code, the sentence
   of §6.2 holds". Crossing that gap requires **the construction of the chain map
   $f_\bullet$ of Def 2.5** (and the relabelling, item by item, of that degree-shift),
   which is given by `Homology/SubcodeChainMap.lean`.

   **(That gap has now been closed by `Homology/SubcodeChainMap.lean`.)**
   That module gives the three components of the source's Def 2.5 chain map $f_\bullet$
   together with the two chain conditions (`SubcodeChainMap`), the item-by-item relabelling
   of the degree-shift (six `rfl`-level identities such as `auxChainD1_eq_transpose`, plus
   the two chain conditions `auxChainD1_mul_auxChainD2` / `auxChainD0_mul_auxChainD1`), and
   the **origin of the degree** in this module's §3 "reading $A_\bullet$ as a code" -- that
   $A_1 = \mathbb F_2^V$ is $C_1$, and this module's `subcodeDistanceZ` is exactly the
   **X distance** of the code read off the chain complex
   (`chainCode_distanceX_eq_subcodeDistanceZ`), with both matrix swaps and relabellings
   given by `rfl`-level theorems (`chainCodeX_eq_subcodeZChecks`,
   `chainCodeZ_eq_subcodeXChecks`). The main theorem of this module,
   `subcodeDistanceZ_eq_one`, has, on that **$A_\bullet$ constructed from the chain map**,
   the corresponding forms `gaugingSubcode_distanceZ_eq_one` /
   `chainCode_distanceX_eq_one`; and the half "why $G = H_X^{\mathsf T}$" is
   machine-checked by `incidence_unique` (the chain condition uniquely determines the
   incidence matrix) and `touching_of_chainCondition`.
2. **The gloss of §6.1 is only used in half.** The prose of §6.1 ("which are required to
   cause an undetectable logical measurement error") mentions both "undetectable" and
   "logical measurement error"; on the Z-distance side this module uses the **algebraic**
   criterion of §1.2 ($u \in \ker\delta_2 \setminus \mathrm{im}\,\delta_1$), not the
   "logical readout functional" criterion ($u$ pairs to 1 with some readout functional).
   The two **can differ** -- this library has recorded such a difference on Bacon–Shor
   (the docstring of `Codes/MeasurementProtocol.lean`: "it must be a logical functional
   rather than 'not in the row space'; the two differ on Bacon–Shor by $2$ versus $3$").
   This module **does not claim** that the two criteria give the same number.
3. **"Distance" has two sides, and the sentence of §6.2 does not say which.** The single
   matrix pair $(\delta_2,\ \delta_1^{\mathsf T})$, as a CSS code, has two sets of logical
   operators: the Z side
   $\ker\delta_2 \setminus \mathrm{rowSpace}(\delta_1^{\mathsf T})$ ($= 1$-cosystolic
   cochains) and the X side
   $\ker\delta_1^{\mathsf T} \setminus \mathrm{rowSpace}(\delta_2)$
   ($\ker\delta_1^{\mathsf T}$ = components, see
   `AuxComplex.isComponent_iff_mulVec_transpose`). This module defines and computes both
   sides: **the Z side is exactly 1** (the main theorem), while **the gauging instance of
   the X side is $k$ (the number of vertices, also the number of Z checks), not 1**
   (`subcodeDistanceX_graphOf_eq_card`) -- the two differ by a factor of $k$
   (`subcodeDistanceZ_ne_subcodeDistanceX_graphOf`). Hence the "distance 1" of §6.2 **can
   only be the Z side** (the 1-cosystolic distance of Thm 6.5), and cannot be the kind of X
   distance that the remark on Prop 9.3 speaks of. This **machine-checkable difference** is
   the quantitative evidence that "the single sentence of §6.2 does not pin down
   'distance'" (the two sides differ whenever $k \ge 2$).
4. **What is not done**: we do not construct the chain map $f_\bullet$ of Def 2.5, do not
   reproduce the mapping-cone relabelling of Appendix C/D, do not prove the equivalence
   between the "logical readout functional" of the §6.1 prose and the algebraic criterion,
   and do not touch the fault-distance theorems of [14] (the "$O(d)$ rounds" conclusions of
   Theorem 5.3 / 6.3 / 6.5 themselves).

## 5. Wiring (now in place; this module changed no existing file)

* The import section of the root module `QECCertificates.lean` carries
  `import QECCertificates.Homology.SubcodeLayer` (placed after `Homology.AuxComplex`);
* the audit region of the root module carries the following `#print axioms` lines (all
  measured to depend on exactly the three standard axioms):

```
-- The subcode layer: [14] §6.2's "the gauging subcode $A_\bullet$ has distance 1"
-- (Homology/SubcodeLayer.lean)
#print axioms QECCertificates.Homology.subcode_css
#print axioms QECCertificates.Homology.range_toLin'_eq_transpose_rowSpace
#print axioms QECCertificates.Homology.isCosystolic_iff_subcode
#print axioms QECCertificates.Homology.subcodeDistanceZ_eq_one
#print axioms QECCertificates.Homology.subcodeDistanceZ_graphOf_eq_one
#print axioms QECCertificates.Homology.subcodeDistanceZ_eq_one_empty
#print axioms QECCertificates.Homology.mem_ker_subcodeZChecks_graphOf_iff
#print axioms QECCertificates.Homology.subcodeDistanceX_graphOf_eq_card
#print axioms QECCertificates.Homology.subcodeDistanceZ_ne_subcodeDistanceX_graphOf
```

**Trust base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axiom; the `#print axioms` of the nine load-bearing theorems above are measured to
be exactly `propext`, `Classical.choice`, `Quot.sound` (the actual print-out appears in the
audit region of the root module `QECCertificates.lean`).
-/

namespace QECCertificates.Homology

open _root_.Matrix

open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. The subcode's two check matrices and CSS compatibility -/

/-- **The subcode's X checks**: the indicator vectors of the chosen family of components
`W` (the [14] footnote: $W$ is "a set of our choice and is often not a basis of all
components of $H$", so this module treats `W` as **an arbitrary family of components**). -/
abbrev subcodeXChecks {k : ℕ} {I : ℕ} (W : Fin I → Finset (Fin k)) : Matrix (Fin I) (Fin k) (ZMod 2) :=
  surgeryD2 W

/-- **The subcode's Z checks**: $\delta_1^{\mathsf T}$ -- each row is the indicator vector
of a hyperedge. -/
abbrev subcodeZChecks {k m : ℕ} (H : AuxHypergraph k m) : Matrix (Fin m) (Fin k) (ZMod 2) :=
  (surgeryD1 H).transpose

/-- **The subcode's CSS compatibility**:
$H_X H_Z^{\mathsf T} = \delta_2\,(\delta_1^{\mathsf T})^{\mathsf T} = \delta_2\delta_1 = 0$.

This is **not a new hypothesis** -- it is the complex condition of [14] §1.2 (the
$\delta_2\delta_1 = 0$ half of "is a 4-term cochain complex"), given directly by
`surgeryD2_mul_surgeryD1_eq_zero` in `Homology/AuxComplex.lean`. In other words: **the
subcode is a CSS code precisely because the auxiliary structure is a complex**. -/
theorem subcode_css {I : ℕ} (H : AuxHypergraph k m) (W : Fin I → Finset (Fin k))
    (hW : ∀ w, IsComponent H (W w)) :
    subcodeXChecks W * (subcodeZChecks H).transpose = 0 :=
  surgeryD2_mul_surgeryD1_eq_zero H W hW

/-! ## 2. Row space and the image of $\delta_1$

The $d_1^\bullet$ of [14] §1.2 is written on $\mathrm{im}(\delta_1)$, while this library's
distance carrier `min_weight_ker_not_mem_rowspace` is written on `rowSpace`. The two
coincide under transposition -- this section's bridge is the entire cost of writing the
"subcode layer" as **a code distance** (rather than only as a kernel-minus-image set
difference). -/

/-- **The image of $\delta_1$ = the row space of $\delta_1^{\mathsf T}$**:
$\mathrm{im}(\delta_1) = \mathrm{rowSpace}(\delta_1^{\mathsf T})$. -/
theorem range_toLin'_eq_transpose_rowSpace (M : Matrix (Fin k) (Fin m) (ZMod 2)) :
    LinearMap.range M.toLin' = M.transpose.rowSpace := by
  have hsingle : ∀ e : Fin m,
      M *ᵥ (fun e' => if e' = e then (1 : ZMod 2) else 0) = M.transpose e := by
    intro e
    funext i
    rw [Matrix.mulVec_apply, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_eq_single e]
    · rw [Matrix.row_apply, ite_eq_left rfl, mul_one]
    · intro b _ hb
      rw [Matrix.row_apply, ite_eq_right (fun h : b = e => hb h), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ e) h
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, hf⟩
    rw [← hf, Matrix.toLin'_apply]
    have hsum : M *ᵥ f = ∑ e : Fin m, f e • M.transpose e := by
      funext i
      rw [Matrix.mulVec_apply, dotProduct, Finset.sum_apply]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Matrix.row_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply]
      ring
    rw [hsum]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨e, rfl⟩
    refine ⟨(fun e' => if e' = e then (1 : ZMod 2) else 0), ?_⟩
    rw [Matrix.toLin'_apply]
    exact hsingle e

/-! ## 3. The subcode's two distances -/

/-- **The subcode's Z distance** (the 1-cosystolic distance of [14] §1.2, the "check
errors on the auxiliary system" side of the §6.1 gloss):
$\min\{|u| : u \in \ker(\delta_2) \setminus \mathrm{im}(\delta_1)\}$.

It is written using `min_weight_ker_not_mem_rowspace` so that the sentence of §6.2 lands on
**this library's uniform "code distance" interface** (the same shape as every distance
assertion in `Codes/CaseMatrix.lean`), rather than on another `sInf` formulation. The
equivalence of the two is given by `range_toLin'_eq_transpose_rowSpace`. -/
noncomputable def subcodeDistanceZ {I : ℕ} (H : AuxHypergraph k m)
    (W : Fin I → Finset (Fin k)) : ℕ :=
  min_weight_ker_not_mem_rowspace (subcodeXChecks W) (subcodeZChecks H)

/-- **The subcode's X distance** (the other side of the same CSS code):
$\min\{|\ell| : \ell \in \ker(\delta_1^{\mathsf T}) \setminus \mathrm{rowSpace}(\delta_2)\}$.
$\ker\delta_1^{\mathsf T}$ is exactly the **components** of $H$ (the
`isComponent_iff_mulVec_transpose` of `Homology/AuxComplex.lean`), so this is the side with
"components as logical operators and the chosen components as stabilizers". -/
noncomputable def subcodeDistanceX {I : ℕ} (H : AuxHypergraph k m)
    (W : Fin I → Finset (Fin k)) : ℕ :=
  min_weight_ker_not_mem_rowspace (subcodeZChecks H) (subcodeXChecks W)

/-- **The subcode distance and the existing 1-cosystolic criterion land on the same element
set**: `IsCosystolic` of `Homology/AuxComplex.lean` (expressing "not in the image" as
$\exists f,\ \delta_1 f = u$) is equivalent, item by item, to this module's "not in the row
space of $\delta_1^{\mathsf T}$". -/
theorem isCosystolic_iff_subcode {I : ℕ} (H : AuxHypergraph k m)
    (W : Fin I → Finset (Fin k)) (u : Vec k) :
    IsCosystolic H W u ↔
      u ∈ LinearMap.ker (subcodeXChecks W).toLin' ∧ u ∉ (subcodeZChecks H).rowSpace := by
  rw [IsCosystolic]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rwa [LinearMap.mem_ker, Matrix.toLin'_apply]
    · rw [← range_toLin'_eq_transpose_rowSpace (surgeryD1 H)]
      rintro ⟨f, hf⟩
      exact h2 ⟨f, by rw [← Matrix.toLin'_apply]; exact hf⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at h1
    · rw [← range_toLin'_eq_transpose_rowSpace (surgeryD1 H)] at h2
      intro hcontra
      obtain ⟨f, hf⟩ := hcontra
      exact h2 ⟨f, by rw [← Matrix.toLin'_apply] at hf; exact hf⟩

/-! ## 4. Main theorem: [14] §6.2's "the gauging subcode has distance 1"

The source sentence of §6.2 (p.35): *"Gauging logical measurement can be seen as an
instance of hypergraph surgery where the subcode $A_\bullet$ has distance 1, and therefore
requires $O(d)$ rounds of syndrome measurement to maintain fault-distance $d$."*

This module reads it as `subcodeDistanceZ H W = 1`: **the Z distance of the subcode is
exactly 1**. The upper bound is a **single-vertex cochain** $\{v\}$ (the "one check error"
of the §6.1 gloss), and the lower bound is given by "$\{v\} \notin \mathrm{im}\,\delta_1$". -/

/-- **Main theorem: the Z distance of the gauging subcode = 1** ([14] §6.2).

On an even hypergraph (every hyperedge has even cardinality; **a 2-regular hypergraph / a
graph is the minimal case**, i.e. the gauging auxiliary structure), as long as the chosen
family of components `W` avoids some vertex `v`, the Z distance of the subcode is exactly
`1`.

**Upper bound** (`minWeight_le_of_witness`): $u = \{v\}$ is an element of $\ker\delta_2$
(`surgeryD2_mulVec_indVec_singleton` + `ite_eq_right`), and is
$\notin \mathrm{rowSpace}(\delta_1^{\mathsf T}) = \mathrm{im}\,\delta_1$
(`not_mem_im_surgeryD1_indVec_singleton`: on an even hypergraph every element of
$\mathrm{im}\,\delta_1$ has even weight, while $\{v\}$ has weight 1). **Lower bound**: the
zero vector is always in the row space, so every candidate is nonzero and has weight
$\ge 1$. -/
theorem subcodeDistanceZ_eq_one {I : ℕ} (H : AuxHypergraph k m)
    (W : Fin I → Finset (Fin k)) (heven : IsEvenHyper H) (v : Fin k)
    (hv : ∀ w : Fin I, v ∉ W w) :
    subcodeDistanceZ H W = 1 := by
  have hk : 1 ≤ k := by have := v.isLt; omega
  have hker : indVec ({v} : Finset (Fin k)) ∈ LinearMap.ker (subcodeXChecks W).toLin' := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    funext w
    rw [surgeryD2_mulVec_indVec_singleton W v w]
    exact ite_eq_right (hv w)
  have hnot : indVec ({v} : Finset (Fin k)) ∉ (subcodeZChecks H).rowSpace := by
    rw [← range_toLin'_eq_transpose_rowSpace (surgeryD1 H)]
    rintro ⟨f, hf⟩
    exact not_mem_im_surgeryD1_indVec_singleton H heven v
      ⟨f, by rw [← Matrix.toLin'_apply]; exact hf⟩
  have hw : hammingNorm (indVec ({v} : Finset (Fin k))) = 1 := hammingNorm_indVec_singleton v
  unfold subcodeDistanceZ
  exact eq_minWeight_of_bounds (subcodeXChecks W) (subcodeZChecks H) hk hker hnot hw
    (fun F _ hFnot => one_le_hammingNorm_of_ne_zero fun h0 => hFnot (h0 ▸ Submodule.zero_mem _))

/-- **The 2-regular (graph) case**: the gauging auxiliary structure is a graph, so the Z
distance of the subcode is 1 -- the direct case that the sentence of §6.2 corresponds to. -/
theorem subcodeDistanceZ_graphOf_eq_one {I : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (W : Fin I → Finset (Fin k)) (v : Fin k)
    (hv : ∀ w : Fin I, v ∉ W w) :
    subcodeDistanceZ (graphOf ends) W = 1 :=
  subcodeDistanceZ_eq_one (graphOf ends) W (graphOf_isEven ends hloop) v hv

/-- **The degenerate case where `W` is the empty family** (the [14] footnote: $W$ is "a set
of our choice", and on a connected graph the only component of size $O(1)$ is
$\varnothing$) -- here the extra hypothesis of the main theorem holds automatically. -/
theorem subcodeDistanceZ_eq_one_empty (H : AuxHypergraph k m) (heven : IsEvenHyper H)
    (v : Fin k) :
    subcodeDistanceZ H (fun w : Fin 0 => w.elim0) = 1 :=
  subcodeDistanceZ_eq_one H _ heven v (fun w => w.elim0)

/-! ## 5. The other side is not 1: the "distance" of that §6.2 sentence is ambiguous

The single matrix pair $(\delta_2,\ \delta_1^{\mathsf T})$, as a CSS code, has **two** sets
of logical operators. §6.2 writes only "has distance 1" without saying which side. This
section computes the **other side** on the same gauging instance: it is $k$ (the number of
vertices = the number of Z checks), not 1.

**Why this deserves its own section**: the remark on Prop 9.3 (p.49) states "the distance
of a Z-type subcode is its X-distance", while §6.2 says gauging is an instance of "subcode
has distance 1" -- the two sentences together are consistent only if the latter refers to
the Z side (the 1-cosystolic distance of Thm 6.5). The theorems of this section quantify
that "which side" difference as the difference between $1$ and $k$. -/

/-- `indVec` on the support set is the original vector. -/
theorem indVec_support_eq {k : ℕ} (u : Vec k) : indVec (support u) = u := by
  funext i
  have hmem : (i ∈ support u) ↔ u i ≠ 0 := by
    rw [support, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  rw [indVec]
  by_cases h : u i ≠ 0
  · rw [ite_eq_left (hmem.mpr h), eq_one_of_ne_zero h]
  · rw [ite_eq_right (fun hc => h (hmem.mp hc)), not_not.mp h]

/-- The support of the zero vector is empty. -/
theorem support_zero (k : ℕ) : support (0 : Vec k) = ∅ := by
  rw [support, Finset.filter_eq_empty_iff]
  intro i _
  simp

/-- The support of the indicator vector of the whole set is the whole set. -/
theorem support_indVec_univ (k : ℕ) :
    support (indVec (Finset.univ : Finset (Fin k))) = Finset.univ := by
  rw [support]
  refine Finset.filter_true_of_mem fun i _ => ?_
  rw [indVec, ite_eq_left (Finset.mem_univ i)]
  exact one_ne_zero

/-- The weight of the indicator vector of the whole set = the number of vertices. -/
theorem hammingNorm_indVec_univ (k : ℕ) :
    hammingNorm (indVec (Finset.univ : Finset (Fin k))) = k := by
  have hfilter : (Finset.univ.filter
      (fun i : Fin k => indVec (Finset.univ : Finset (Fin k)) i ≠ 0)) = Finset.univ := by
    refine Finset.filter_true_of_mem fun i _ => ?_
    rw [indVec, ite_eq_left (Finset.mem_univ i)]
    exact one_ne_zero
  change (Finset.univ.filter
    (fun i : Fin k => indVec (Finset.univ : Finset (Fin k)) i ≠ 0)).card = k
  rw [hfilter, Finset.card_univ, Fintype.card_fin]

/-- **On a connected graph $\ker\delta_1^{\mathsf T}$ has only two elements**: zero and
all-ones. ($\ker\delta_1^{\mathsf T}$ = components, and the components of a connected graph
are exactly $\varnothing$ and $V$ -- the `graphOf_components_eq` of
`Homology/AuxComplex.lean`.) -/
theorem mem_ker_subcodeZChecks_graphOf_iff (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hconn : ∀ a b : Fin k, Reachable ends a b)
    (u : Vec k) :
    u ∈ LinearMap.ker (subcodeZChecks (graphOf ends)).toLin' ↔
      u = 0 ∨ u = indVec (Finset.univ : Finset (Fin k)) := by
  have hcomp : u ∈ LinearMap.ker (subcodeZChecks (graphOf ends)).toLin' ↔
      IsComponent (graphOf ends) (support u) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    have h1 := isComponent_iff_mulVec_transpose (graphOf ends) (support u)
    rw [indVec_support_eq] at h1
    exact h1.symm
  rw [hcomp, graphOf_components_eq ends hloop hconn (support u)]
  constructor
  · rintro (h0 | hu)
    · left
      funext i
      have hi : ¬ (u i ≠ 0) := by
        intro hc
        have hmem : i ∈ support u := by
          rw [support, Finset.mem_filter]
          exact ⟨Finset.mem_univ i, hc⟩
        rw [h0] at hmem
        exact Finset.notMem_empty i hmem
      exact not_not.mp hi
    · right
      calc u = indVec (support u) := (indVec_support_eq u).symm
        _ = indVec Finset.univ := by rw [hu]
  · rintro (rfl | rfl)
    · exact Or.inl (support_zero k)
    · exact Or.inr (support_indVec_univ k)

/-- **A matrix with zero rows has row space $\bot$** (when `W` is the empty family,
$\delta_2$ has no rows). -/
theorem rowSpace_subcodeXChecks_empty (W : Fin 0 → Finset (Fin k)) :
    (subcodeXChecks W).rowSpace = ⊥ := by
  rw [Matrix.rowSpace, Submodule.span_eq_bot]
  rintro x ⟨i, _⟩
  exact i.elim0

/-- **That §6.2 sentence is false on the "other side"**: the **X distance** of the same
gauging subcode is $k$ (the number of vertices = the number of Z checks), not 1.

The proof uses only two already-proved facts: $\ker\delta_1^{\mathsf T}$ has only
$\{0, \text{all-ones}\}$ (a connected graph has only two components), and when `W` is the
empty family the X-side "stabilizer space" is $\bot$; hence the candidate is exactly the
nonzero one of the two, of weight $k$. -/
theorem subcodeDistanceX_graphOf_eq_card (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hconn : ∀ a b : Fin k, Reachable ends a b)
    (hk : 1 ≤ k) :
    subcodeDistanceX (graphOf ends) (fun w : Fin 0 => w.elim0) = k := by
  have hker : indVec (Finset.univ : Finset (Fin k)) ∈
      LinearMap.ker (subcodeZChecks (graphOf ends)).toLin' :=
    (mem_ker_subcodeZChecks_graphOf_iff ends hloop hconn _).mpr (Or.inr rfl)
  have hne : indVec (Finset.univ : Finset (Fin k)) ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hk⟩
    rw [indVec, ite_eq_left (Finset.mem_univ (⟨0, hk⟩ : Fin k))] at this
    exact one_ne_zero this
  have hnot : indVec (Finset.univ : Finset (Fin k)) ∉
      (subcodeXChecks (fun w : Fin 0 => w.elim0)).rowSpace := by
    rw [rowSpace_subcodeXChecks_empty]
    intro hmem
    exact hne (by simpa using hmem)
  have hw : hammingNorm (indVec (Finset.univ : Finset (Fin k))) = k := hammingNorm_indVec_univ k
  unfold subcodeDistanceX
  refine eq_minWeight_of_bounds (subcodeZChecks (graphOf ends))
    (subcodeXChecks (fun w : Fin 0 => w.elim0)) (le_refl k) hker hnot hw ?_
  intro F hFker hFnot
  rcases (mem_ker_subcodeZChecks_graphOf_iff ends hloop hconn F).mp hFker with h0 | huniv
  · exact absurd (h0 ▸ Submodule.zero_mem _) hFnot
  · rw [huniv, hammingNorm_indVec_univ]

/-- **The ambiguity of [14] §6.2 is quantifiable on the gauging instance**: for $k \ge 2$,
the Z distance ($=1$, the side on which §6.2 holds) and the X distance ($=k$) of the same
subcode **are unequal**. -/
theorem subcodeDistanceZ_ne_subcodeDistanceX_graphOf (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hconn : ∀ a b : Fin k, Reachable ends a b)
    (v : Fin k) (hk : 2 ≤ k) :
    subcodeDistanceZ (graphOf ends) (fun w : Fin 0 => w.elim0) ≠
      subcodeDistanceX (graphOf ends) (fun w : Fin 0 => w.elim0) := by
  rw [subcodeDistanceZ_graphOf_eq_one ends hloop _ v (fun w => w.elim0),
    subcodeDistanceX_graphOf_eq_card ends hloop hconn (by omega)]
  omega

end QECCertificates.Homology
