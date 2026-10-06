/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.SubcodeLayer

open QECCertificates

/-!
# The Def 2.5 chain map $f_\bullet$: the subcode $A_\bullet$ constructed, not just read

Item 1 of the "honest boundary" section of `Homology/SubcodeLayer.lean` records the
largest gap in this library:

> **Reading $A_\bullet$ as "the CSS code with $\mathbb F_2^V$ as its qubit space" is this
> module's choice**, not the source's construction. The source's $A_\bullet$ is, in
> Def 2.5, a **subcomplex of the memory-code complex $C_\bullet$** (whose qubits are a
> subset of the memory code's data bits, injected through the basis-preserving chain map
> $f_\bullet$), and, in §1.2 / Thm 6.5, the auxiliary complex. **That phrase
> `degree-shifted subcode` between the two is left undefined** ... to cross that gap one
> must supply **the construction of the chain map $f_\bullet$ of Def 2.5** (and the
> item-by-item relabelling of that degree-shift), which this module **does not** construct.

This module **closes** that gap: it gives the three components of the Def 2.5 chain map
$f_\bullet$, the item-by-item relabelling of the degree-shift, the identification
$A_1 = \mathbb F_2^V = C_1$, and a construction in which **the code's own $X$-check matrix
induces an incidence matrix** -- the latter is precisely the assembly that [14] itself
gives (the $G = H_X^{\mathsf T}$ of p.18). The step "reading $A_\bullet$ as a code" in §3 of
`Homology/SubcodeLayer.lean` here becomes the result of **reading the chain differentials
of $A_\bullet$ under the degree convention** (`chainCodeX` / `chainCodeZ`), not a free
choice -- and the swap between the two labellings is likewise machine-checked as a theorem
(§4).

## 1. The source (transcribed verbatim, with page numbers)

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895
(`refs/Fast and fault-tolerant logical measurements - Auxiliary hypergraphs and
transversal surgery.pdf`).

**Definition 2.5 (Subcode), p. 11** (the structure this module implements):

> **Definition 2.5 (Subcode).** *Let a subcode of the CSS code defined by a chain complex
> $C_\bullet$ be a code defined by the chain complex $A_\bullet$ with an injective chain map
> $f_\bullet : A_\bullet \to C_\bullet$. We stipulate further that $f_\bullet$ must take each
> data qubit in $A_\bullet$ to a single data qubit in $C_\bullet$, and the same for any
> $Z$ or $X$ checks in $A_\bullet$.*
>
> The additional stipulation is made to maintain control over weights, as this is essential
> for our analysis; if $C_\bullet$ is LDPC, so is $A_\bullet$. Each matrix in the chain map
> $f_\bullet$ is therefore a permutation matrix, up to some all-zero rows.

**The chain condition above that definition (p. 11)**:

> $\dots$ i.e. $\partial^{D}_{i+1} f_{i+1} = f_i \partial^{C}_{i+1}\ \forall i \in \mathbb Z$.

(The `SubcodeChainMap.comm1` / `comm2` of this module are the $i = 1, 2$ cases, arranged in
the matrix-writing direction.)

**The mapping cone of Definition 4.1 (the display of p. 26)**: after stacking $A_\bullet$
with the memory-code complexes $C_\bullet, C'_\bullet, C''_\bullet$, the **degree-2
component** of the cone is $A_1 \oplus C_2 \oplus C'_2 \oplus \cdots$, the **degree-1
component** is $A_0 \oplus C_1 \oplus C'_1
\oplus \cdots$, and the **degree-0 component** is $C_0 \oplus C'_0 \oplus \cdots$; the two
slanted arrows in the figure are $f_1 : A_1 \to C_1$ and $f_0 : A_0 \to C_0$. The source
then states:

> Explicitly, $D_\bullet$ is the chain complex $\dots$ **Note that also $A_\bullet$
> generally possesses a nonzero $A_2$ component. This component corresponds to metachecks,
> so we ignore that term for now.**

**p. 27** (the reading below the same Tanner graph):

> Observe that the chain maps $f_\bullet, f'_\bullet, f''_\bullet$ determine the
> connectivity between the blocks and the auxiliary hypergraph, and that $\mathcal E = A_0$,
> $\mathcal V = A_1$.

**§5, p. 31** (the sentence about "degree-shift" on the mapping-cone side):

> The degree 1 of $A_\bullet$ is shifted by the mapping cone construction to be in
> $\mathrm{cone}(f)_2$, i.e. the set of vertices in the hypergraph is the set of basis
> elements of $A_1$.

**p. 17–18, equation (2)** (the **only** instance where the source gives an explicit
assembly -- the full block reading; bold as in the source):

> $\dots$ such that new data qubits are edges, new Z checks are vertices and $\mathcal H$
> has the edge-vertex incidence matrix $G \in \mathbb F_2^{\mathcal V \times \mathcal E}$.
> **$\mathcal H$ has 1-to-1 maps from edges to $X$ checks in $Q$ and to $X$ checks in $Q'$,
> and similar for vertices. Thus in order for the checks of the deformed code to commute,
> we have $G = H_X^{\mathsf T}$.**

**§6.2, p. 35** (the sentence that §6 of this module lands):

> Gauging logical measurement [56] can be seen as an instance of hypergraph surgery where
> the subcode $A_\bullet$ has distance 1, and therefore requires $O(d)$ rounds of syndrome
> measurement to maintain fault-distance $d$.

**Lemma 7.12, p. 38** and **Appendix D, p. 90** (the two occurrences of "degree-shifted" in
the paper): the former's "degree-shifted subcode $A_\bullet$", the latter's "These
relabellings correspond precisely to the degree-shifting of a mapping cone to recover the
original chain map $f_\bullet$", **are only side remarks** and are not written as a
construction -- the construction this module gives is that one.

## 2. What this module does (matched against the task item by item)

**(1) The chain map $f_\bullet$ of Def 2.5 -- §1, §2, §5.**
§1 cashes out "each basis element maps to **one** basis element" as the matrix `basisMap`,
and machine-checks all of its load-bearing properties: each column has exactly one `1`
(`basisMap_apply_self`, `basisMap_mulVec_single`), rows may be all zero
(`basisMap_row_eq_zero_iff`, "up to some all-zero rows"), an injective basis map implies an
injective linear map (`basisMap_mulVec_eq_zero`, the "injective chain map" of Def 2.5), and
the half that is the source's **reason** for the stipulation -- basis elements still map to
basis elements, with weight still $1$ (`hammingNorm_basisMap_mulVec_single`, "if
$C_\bullet$ is LDPC, so is $A_\bullet$"). §2 packages the three components $f_0, f_1, f_2$
and the two chain conditions into `SubcodeChainMap`, and gives its **chain-map content**:
cycles to cycles (`cycles_map`, `cycles2_map`), boundaries to boundaries (`boundaries_map`),
injectivity on cycles (`injective_on_cycles`, `injective_on_cycles0`).

**(2) The item-by-item relabelling of the degree-shift -- §3.**
It relabels the 4-term **cochain** complex of [14] §1.2,
$\mathbb F_2^W \xleftarrow{\delta_2} \mathbb F_2^V \xleftarrow{\delta_1} \mathbb F_2^E
\xleftarrow{\delta_0} \mathbb F_2^C$, into the **chain** complex
$A_2 \xrightarrow{\partial^A_2} A_1 \xrightarrow{\partial^A_1} A_0 \xrightarrow{\partial^A_0}
A_{-1}$: following the $\mathcal E = A_0$, $\mathcal V = A_1$ of p.27 and the "the set of
vertices $\dots$ is the set of basis elements of $A_1$" of p.31, it takes

$$A_2 := \mathbb F_2^W,\quad A_1 := \mathbb F_2^V,\quad A_0 := \mathbb F_2^E,\quad
A_{-1} := \mathbb F_2^C,\qquad \partial^A_i := \delta_i^{\mathsf T}.$$

The relabelling is checkable **item by item**: `auxChainD1_eq_transpose`,
`surgeryD1_eq_transpose_auxChainD1` ($\delta_1 = (\partial^A_1)^{\mathsf T}$: the same
linear map, with the degree reversed), and the same for $\delta_2, \delta_0$, six
`rfl`-level identities in all; plus the two chain conditions
`auxChainD1_mul_auxChainD2` ($\partial^A_1 \partial^A_2 = (\delta_2 \delta_1)^{\mathsf T}
= 0$) and `auxChainD0_mul_auxChainD1` -- **the relabelling produces no new complex
condition; it is the one that was already there**.

**(3) $\mathbb F_2^V$ is $C_1$, and the code read off $A_\bullet$ -- §4.**
$A_1 := \mathbb F_2^V$ is a definition-level fact (the type of `auxChainD1` is
`Matrix (Fin m) (Fin k)`: the **column** index of $\partial^A_1$ is exactly the vertex set
`Fin k`, see `auxChainD1_eq_transpose`); and for the CSS code read off $A_\bullet$ as a
chain complex, the qubit space is $A_1$ (the column indices of `chainCodeX` / `chainCodeZ`
are both exactly `Fin k` = the vertex set), with Z checks = $A_2$ and X checks = $A_0$.
**The labels are exactly swapped relative to `Homology/SubcodeLayer.lean`** (which calls
$\delta_1^{\mathsf T}$ the Z checks and $\delta_2$ the X checks), and both swaps are
`rfl`-level theorems (`chainCodeX_eq_subcodeZChecks`, `chainCodeZ_eq_subcodeXChecks`), so
that **`SubcodeLayer.subcodeDistanceZ` ($= d_1^\bullet$) is the X distance of the code of
this module** (`chainCode_distanceX_eq_subcodeDistanceZ`). In the all-1-to-1 case it
collapses to `basisMap_id : basisMap id = 1` -- $f_1$ is the identity, and
$\mathbb F_2^V$ **is** $C_1$.

**(4) Where that code comes from: the chain condition uniquely determines the incidence
matrix -- §5.**
The source's p.18 says "Thus in order for the checks of the deformed code to commute, we
have $G = H_X^{\mathsf T}$". This module makes it into two halves: `incidence_unique` (any
incidence matrix satisfying the chain condition **equals** the induced incidence on every
selected edge -- the uniqueness of "$G = H_X^{\mathsf T}$") and `touching_of_chainCondition`
(the chain condition **conversely** forces "only $X$ checks intersecting a port bit may
enter the hypergraph"). And the induced incidence itself (`inducedHyper`, whose
`surgeryD1_inducedHyper` gives it as the restricted form of $H_X^{\mathsf T}$)
**automatically** satisfies the chain condition (`inducedSubcode_comm1`) -- this is the
`inducedSubcodeChainMap` of §5.

**(5) The "distance 1" of §6.2 on the **constructed** $A_\bullet$ -- §6.**
`gaugingSubcode_distanceZ_eq_one`, `chainCode_distanceX_eq_one`: the $A_\bullet$
constructed from the port data has code distance exactly $1$. **Hence the prefix of the
main theorem `subcodeDistanceZ_eq_one` of `Homology/SubcodeLayer.lean` is no longer "this
library's self-built CSS-code reading", but "the $A_\bullet$ constructed from the chain map
$f_\bullet$ of Def 2.5"**.

## 3. Honest boundary (the paper's main text cites this paragraph)

1. **The source does not give the gauging subcode construction; this module gives a
   generalization of its only explicit assembly.**
   [14] §6.2 has only one sentence (quoted above), and the only place in the paper that
   writes out an explicit assembly is equation (2) of p.17–18 (the full block reading):
   "1-to-1 maps from edges to $X$ checks in $Q$ ... Thus ... $G = H_X^{\mathsf T}$". This
   module's `inducedHyper` is the formalization of that sentence (replacing the bijections
   there by two injections $\iota, \varepsilon$), and it proves that it automatically
   satisfies the chain condition. **This is "compatible with the source, and turning the
   source's only explicit assembly into a construction", not "the construction that the
   sentence of §6.2 itself already writes down".**

2. **The even hypothesis is load-bearing: it is a hypothesis of this library's existing
   model, not a new one.**
   The distance conclusion of §6 (via `subcodeDistanceZ_eq_one_empty` of
   `Homology/SubcodeLayer.lean`) needs an even hypergraph (every hyperedge has even
   cardinality). Under the induced incidence, $|{\rm edge}_e|$ is the weight of the selected
   $X$ check $\varepsilon e$ on the port bits (`inducedHyper_edge_card`,
   `inducedHyper_isEven_iff`), so the exact meaning of the even hypothesis is **"every
   selected $X$ check has even weight on the port bits"**. It holds automatically in two
   cases: (i) the graph (2-regular) model -- $|{\rm edge}_e| = 2$, exactly the shape of the
   gauging auxiliary structure and the model of this library's `graphOf` series; (ii) in the
   full block reading, codes whose $X$ checks have even weight (such as toric / surface
   codes).

3. **What is not done**: we do not prove the equivalence between the chain condition and
   the cochain condition (this module only uses the complex condition of the cochain
   complex, $\delta$, to derive the complex condition of the chain complex -- one
   direction, which suffices); we do not construct the **induced** instance with
   $W \ne \emptyset$ ($f_2$ would need $\partial^C_2 f_2 = f_1 \partial^A_2$, i.e. **every
   component $W w$ must be exactly the support of some $Z$ check of the code**; the
   source's p.26 states "so we ignore that term for now", so the induced side takes
   $W = \emptyset$, where $A_2 = 0$ and $f_2$ is trivial, making `comm2` hold
   **unconditionally**).
   **But the structure itself does not exclude $A_2 \ne 0$**: this module additionally
   gives a `selfChainMap` -- the target complex is taken to be itself and the three
   components are the identity, so that $A_2$ is nonempty while the two chain conditions
   degenerate to $1\cdot\partial = \partial\cdot 1$; `selfChainMap_phi2_apply` is the
   witness of its non-triviality ($\varphi_2$ is defined on a nonempty index set).
   So this item is of the same kind as Case 2 of §16: what is missing is **an object the
   source does not give** (the metacheck layer on the target-code side), not work; it does
   not touch the fault-distance theorems of [14] (Thm 5.3 / 6.3 / 6.5 themselves), does not
   do the module expansion of §7, and does not touch the `the gauged-measurement companion development's `DistancePreservation` module`
   side.

**Trust base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axiom; the `#print axioms` of the load-bearing theorems appears at the end of the
root module `QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open _root_.Matrix

open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. The "basis-preserving" layer of Def 2.5: one basis element to a **single** one -/

/-- **The matrix of a basis map** (the "must take each data qubit in $A_\bullet$ to a single
data qubit in $C_\bullet$, and the same for any $Z$ or $X$ checks" of Def 2.5): `φ` is a map
between basis sets, and the matrix is its graph.

The convention agrees with `Homology/AuxComplex.lean`: `M : Matrix ρ σ` acting on column
vectors represents $\mathbb F_2^\sigma \to \mathbb F_2^\rho$, so
`basisMap φ : Matrix (Fin c) (Fin a)` is the map $A \to C$, with the **column** index the
basis of $A$ and the **row** index the basis of $C$. -/
def basisMap {a c : ℕ} (φ : Fin a → Fin c) : Matrix (Fin c) (Fin a) (ZMod 2) :=
  fun j i => if φ i = j then 1 else 0

/-- On `ZMod 2`, anything other than 1 is 0. -/
theorem eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x
  · rfl
  · exact absurd rfl h

/-- The value of the basis map (definition level). -/
theorem basisMap_apply {a c : ℕ} (φ : Fin a → Fin c) (j : Fin c) (i : Fin a) :
    basisMap φ j i = if φ i = j then 1 else 0 := rfl

/-- **The `i`-th column is 1 at `φ i`**: each $A$-basis element maps to exactly **one**
$C$-basis element. -/
theorem basisMap_apply_self {a c : ℕ} (φ : Fin a → Fin c) (i : Fin a) :
    basisMap φ (φ i) i = 1 := by
  rw [basisMap_apply, ite_eq_left rfl]

/-- **The column is zero elsewhere.** -/
theorem basisMap_apply_eq_zero {a c : ℕ} (φ : Fin a → Fin c) {j : Fin c} {i : Fin a}
    (h : φ i ≠ j) : basisMap φ j i = 0 := by
  rw [basisMap_apply, ite_eq_right (fun hc : φ i = j => h hc)]

/-- **A row may be all zero, and it is exactly a row of $C$ into which no $A$-basis element
falls** -- the "a permutation matrix, up to some all-zero rows" of Def 2.5. -/
theorem basisMap_row_eq_zero_iff {a c : ℕ} (φ : Fin a → Fin c) (j : Fin c) :
    (∀ i : Fin a, basisMap φ j i = 0) ↔ ∀ i : Fin a, φ i ≠ j := by
  constructor
  · intro h i hij
    have := h i
    rw [basisMap_apply, ite_eq_left hij] at this
    exact one_ne_zero this
  · intro h i
    exact basisMap_apply_eq_zero φ (h i)

/-- **The action of the basis map on a basis vector**: the `i`-th basis vector maps to the
`φ i`-th basis vector -- exactly the use of the "basis-preserving" stipulation of Def 2.5
(the weight control of $A$ is inherited from $C$). -/
theorem basisMap_mulVec_single {a c : ℕ} (φ : Fin a → Fin c) (i : Fin a) :
    basisMap φ *ᵥ (fun i' : Fin a => if i' = i then 1 else 0) =
      fun j : Fin c => if φ i = j then 1 else 0 := by
  funext j
  rw [Matrix.mulVec_apply, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.row_apply, basisMap_apply, ite_eq_left rfl, mul_one]
  · intro b _ hb
    rw [Matrix.row_apply, ite_eq_right (fun h : b = i => hb h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Reading the original coordinate at `φ i`**: `(basisMap φ *ᵥ x) (φ i) = x i` (this
uses the injectivity of `φ`). -/
theorem basisMap_mulVec_apply_self {a c : ℕ} {φ : Fin a → Fin c} (hφ : Function.Injective φ)
    (x : Fin a → ZMod 2) (i : Fin a) : (basisMap φ *ᵥ x) (φ i) = x i := by
  rw [Matrix.mulVec_apply, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.row_apply, basisMap_apply, ite_eq_left rfl, one_mul]
  · intro b _ hb
    rw [Matrix.row_apply, basisMap_apply,
      ite_eq_right (fun h : φ b = φ i => hb (hφ h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **An injective basis map implies an injective linear map** -- the linear-algebra
content of the "injective chain map" of Def 2.5. -/
theorem basisMap_mulVec_eq_zero {a c : ℕ} {φ : Fin a → Fin c} (hφ : Function.Injective φ)
    {x : Fin a → ZMod 2} (hx : basisMap φ *ᵥ x = 0) : x = 0 := by
  funext i
  have h := basisMap_mulVec_apply_self hφ x i
  rw [hx] at h
  simpa using h.symm

/-- **An injective basis map is injective on the kernel.** -/
theorem basisMap_ker_eq_bot {a c : ℕ} {φ : Fin a → Fin c} (hφ : Function.Injective φ) :
    LinearMap.ker (basisMap φ).toLin' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
  exact basisMap_mulVec_eq_zero hφ hx

/-- **The weight of a basis element is still 1**: the machine-checkable content of the
Def 2.5 sentence "The additional stipulation is made to maintain control over weights
$\dots$ if $C_\bullet$ is LDPC, so is $A_\bullet$" -- the image of each basis vector of $A$
under $f$ is still **one** basis vector (weight 1). -/
theorem hammingNorm_basisMap_mulVec_single {a c : ℕ} (φ : Fin a → Fin c) (i : Fin a) :
    hammingNorm (basisMap φ *ᵥ (fun i' : Fin a => if i' = i then 1 else 0)) = 1 := by
  rw [basisMap_mulVec_single]
  have hsupp : (Finset.univ.filter (fun j : Fin c => (if φ i = j then (1 : ZMod 2) else 0) ≠ 0))
      = {φ i} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hj⟩
      by_contra hne
      rw [ite_eq_right (fun h : φ i = j => hne h.symm)] at hj
      exact hj rfl
    · intro h
      subst h
      exact ⟨Finset.mem_univ (φ i), by rw [ite_eq_left rfl]; exact one_ne_zero⟩
  change (Finset.univ.filter
    (fun j : Fin c => (if φ i = j then (1 : ZMod 2) else 0) ≠ 0)).card = 1
  rw [hsupp, Finset.card_singleton]

/-- **When the map is 1-to-1 everywhere the basis map is the identity matrix**: the
definition-level form of "$A_1 = \mathbb F_2^V$ **is** $C_1$" (the "and similar for
vertices" of the source's p.18 is a bijection in the full block reading). -/
theorem basisMap_id (n : ℕ) : basisMap (id : Fin n → Fin n) = 1 := by
  ext j i
  rw [basisMap_apply, Matrix.one_apply]
  simp only [id_eq]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right (fun hc : i = j => h hc), ite_eq_right (fun hc : j = i => h hc.symm)]

/-! ## 2. The chain map of Def 2.5: three components plus two chain conditions -/

/-- **The chain map $f_\bullet : A_\bullet \to C_\bullet$ of Def 2.5** (Definition 2.5 of
[14] p.11).

The three components $f_0, f_1, f_2$ are each given by an **injection between basis sets**
(`basisMap`, the source's "take each $\dots$ to a single $\dots$"), the three `inj` fields
are the source's "injective chain map", and the two `comm` fields are the chain condition
$\partial^{C}_{i+1} f_{i+1} = f_i \partial^{C}_{i+1}$ of p.11 equation (1) in the cases
$i = 1, 2$.

Matrix index convention (agreeing with `Homology/AuxComplex.lean`):
`dA1 : Matrix (Fin a₀) (Fin a₁)` denotes $\partial^A_1 : A_1 \to A_0$, i.e. the **row** index
is $A_0$ and the **column** index is $A_1$. Hence `basisMap phi0 * dA1 :
Matrix (Fin c₀) (Fin a₁)` is $f_0 \partial^A_1$, and `dC1 * basisMap phi1` is
$\partial^C_1 f_1$; their equality is the chain condition for $i = 1$. -/
structure SubcodeChainMap (a₀ a₁ a₂ c₀ c₁ c₂ : ℕ)
    (dA1 : Matrix (Fin a₀) (Fin a₁) (ZMod 2)) (dA2 : Matrix (Fin a₁) (Fin a₂) (ZMod 2))
    (dC1 : Matrix (Fin c₀) (Fin c₁) (ZMod 2)) (dC2 : Matrix (Fin c₁) (Fin c₂) (ZMod 2)) where
  /-- The component $f_0 : A_0 \to C_0$ (the slanted arrow from $A_0$ to $C_0$ in the
  figure of the source's p.26). -/
  phi0 : Fin a₀ → Fin c₀
  /-- The component $f_1 : A_1 \to C_1$ (the source's p.27: $f_1$ sends the vertices of
  the auxiliary hypergraph to the data bits of the code). -/
  phi1 : Fin a₁ → Fin c₁
  /-- The component $f_2 : A_2 \to C_2$ ($A_2$ is the metacheck term; the source's p.26
  "This component corresponds to metachecks, so we ignore that term for now"). -/
  phi2 : Fin a₂ → Fin c₂
  /-- The source's "injective chain map" (at the level of bases). -/
  inj0 : Function.Injective phi0
  /-- The source's "injective chain map" (at the level of bases). -/
  inj1 : Function.Injective phi1
  /-- The source's "injective chain map" (at the level of bases). -/
  inj2 : Function.Injective phi2
  /-- Chain condition $\partial^C_1 f_1 = f_0 \partial^A_1$ ([14] p.11 equation (1),
  $i = 1$). -/
  comm1 : basisMap phi0 * dA1 = dC1 * basisMap phi1
  /-- Chain condition $\partial^C_2 f_2 = f_1 \partial^A_2$ ([14] p.11 equation (1),
  $i = 2$). -/
  comm2 : basisMap phi1 * dA2 = dC2 * basisMap phi2

variable {a₀ a₁ a₂ c₀ c₁ c₂ : ℕ}
variable {dA1 : Matrix (Fin a₀) (Fin a₁) (ZMod 2)} {dA2 : Matrix (Fin a₁) (Fin a₂) (ZMod 2)}
variable {dC1 : Matrix (Fin c₀) (Fin c₁) (ZMod 2)} {dC2 : Matrix (Fin c₁) (Fin c₂) (ZMod 2)}

/-- **The chain map sends cycles to cycles** (the $A_1$ case):
$x \in \ker \partial^A_1 \Rightarrow f_1 x \in \ker \partial^C_1$.

This is what the phrase "chain map" means: it is not an arbitrary homomorphism, but the one
that connects the **differentials** (the source's p.17 "in order for the checks of the
deformed code to commute"). -/
theorem SubcodeChainMap.cycles_map (F : SubcodeChainMap a₀ a₁ a₂ c₀ c₁ c₂ dA1 dA2 dC1 dC2)
    {x : Fin a₁ → ZMod 2} (hx : dA1 *ᵥ x = 0) : dC1 *ᵥ (basisMap F.phi1 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, ← F.comm1, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- **The chain map sends cycles to cycles** (the $A_2$ case, i.e. the metacheck term). -/
theorem SubcodeChainMap.cycles2_map (F : SubcodeChainMap a₀ a₁ a₂ c₀ c₁ c₂ dA1 dA2 dC1 dC2)
    {z : Fin a₂ → ZMod 2} (hz : dA2 *ᵥ z = 0) : dC2 *ᵥ (basisMap F.phi2 *ᵥ z) = 0 := by
  rw [Matrix.mulVec_mulVec, ← F.comm2, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]

/-- **The chain map sends boundaries to boundaries**: $f_1(\operatorname{im}\partial^A_2)
\subseteq \operatorname{im}\partial^C_2$ (term-by-term equality, stronger than inclusion). -/
theorem SubcodeChainMap.boundaries_map (F : SubcodeChainMap a₀ a₁ a₂ c₀ c₁ c₂ dA1 dA2 dC1 dC2)
    (y : Fin a₂ → ZMod 2) :
    basisMap F.phi1 *ᵥ (dA2 *ᵥ y) = dC2 *ᵥ (basisMap F.phi2 *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, F.comm2, ← Matrix.mulVec_mulVec]

/-- **Injectivity on cycles**: $f_1$ is injective on $A_1$, so $A_\bullet$ is **genuinely**
a subcomplex that embeds in (not a quotient, and not only at the level of homology). -/
theorem SubcodeChainMap.injective_on_cycles (F : SubcodeChainMap a₀ a₁ a₂ c₀ c₁ c₂ dA1 dA2 dC1 dC2)
    {x : Fin a₁ → ZMod 2} (hx : basisMap F.phi1 *ᵥ x = 0) : x = 0 :=
  basisMap_mulVec_eq_zero F.inj1 hx

/-- **Injectivity on cycles ($A_0$ side).** -/
theorem SubcodeChainMap.injective_on_cycles0 (F : SubcodeChainMap a₀ a₁ a₂ c₀ c₁ c₂ dA1 dA2 dC1 dC2)
    {w : Fin a₀ → ZMod 2} (hw : basisMap F.phi0 *ᵥ w = 0) : w = 0 :=
  basisMap_mulVec_eq_zero F.inj0 hw

/-! ## 3. degree-shift: the §1.2 cochain complex relabelled as a chain complex $A_\bullet$

[14] §1.2 gives the cochain complex
$\mathbb F_2^W \xleftarrow{\delta_2} \mathbb F_2^V \xleftarrow{\delta_1} \mathbb F_2^E
\xleftarrow{\delta_0} \mathbb F_2^C$ (all three arrows point left), whereas the
$A_\bullet$ of Def 2.5 is a **chain** complex and the mapping cone of Def 4.1 needs
$\partial^A_i : A_i \to A_{i-1}$. This section connects the two **item by item**:

$$A_2 := \mathbb F_2^W,\quad A_1 := \mathbb F_2^V,\quad A_0 := \mathbb F_2^E,\quad
A_{-1} := \mathbb F_2^C,\qquad \partial^A_i := \delta_i^{\mathsf T}.$$

The degrees are pinned down by the "$\mathcal E = A_0$, $\mathcal V = A_1$" of the source's
p.27 and the "the set of vertices in the hypergraph is the set of basis elements of $A_1$"
of p.31: vertices in **degree one**, hyperedges in **degree zero**, components in **degree
two**, and cycles in **degree minus one**. -/

/-- **The chain differential of the degree-shift, $\partial^A_1 : A_1 \to A_0$** -- the
transpose of the $\delta_1$ of [14] §1.2. Row index = $A_0 = \mathbb F_2^E$ (hyperedges),
column index = $A_1 = \mathbb F_2^V$ (vertices). -/
def auxChainD1 (H : AuxHypergraph k m) : Matrix (Fin m) (Fin k) (ZMod 2) :=
  (surgeryD1 H).transpose

/-- **The chain differential of the degree-shift, $\partial^A_2 : A_2 \to A_1$** -- the
transpose of $\delta_2$. Row index = $A_1 = \mathbb F_2^V$ (vertices), column index =
$A_2 = \mathbb F_2^W$ (components, i.e. metachecks). -/
def auxChainD2 {ι : Type*} (W : ι → Finset (Fin k)) : Matrix (Fin k) ι (ZMod 2) :=
  (surgeryD2 W).transpose

/-- **The chain differential of the degree-shift, $\partial^A_0 : A_0 \to A_{-1}$** -- the
transpose of $\delta_0$. Row index = $A_{-1} = \mathbb F_2^C$ (cycles), column index =
$A_0 = \mathbb F_2^E$ (hyperedges). -/
def auxChainD0 {κ : Type*} (H : AuxHypergraph k m) (C : κ → Finset (Fin m)) :
    Matrix κ (Fin m) (ZMod 2) :=
  (surgeryD0 H C).transpose

/-- **Relabelling (the $\delta_1$ item)**: $\partial^A_1 = \delta_1^{\mathsf T}$
(definition level). -/
theorem auxChainD1_eq_transpose (H : AuxHypergraph k m) :
    auxChainD1 H = (surgeryD1 H).transpose := rfl

/-- **Relabelling (the $\delta_1$ item, read backwards)**:
$\delta_1 = (\partial^A_1)^{\mathsf T}$ -- **the same linear map, with the degree
reversed**. This is all that "degree-shifting" amounts to in this library. -/
theorem surgeryD1_eq_transpose_auxChainD1 (H : AuxHypergraph k m) :
    surgeryD1 H = (auxChainD1 H).transpose := by
  rw [auxChainD1, Matrix.transpose_transpose]

/-- **Relabelling (the $\delta_2$ item)**: $\partial^A_2 = \delta_2^{\mathsf T}$
(definition level). -/
theorem auxChainD2_eq_transpose {ι : Type*} (W : ι → Finset (Fin k)) :
    auxChainD2 W = (surgeryD2 W).transpose := rfl

/-- **Relabelling (the $\delta_2$ item, read backwards)**:
$\delta_2 = (\partial^A_2)^{\mathsf T}$. -/
theorem surgeryD2_eq_transpose_auxChainD2 {ι : Type*} (W : ι → Finset (Fin k)) :
    surgeryD2 W = (auxChainD2 W).transpose := by
  rw [auxChainD2, Matrix.transpose_transpose]

/-- **Relabelling (the $\delta_0$ item)**: $\partial^A_0 = \delta_0^{\mathsf T}$
(definition level). -/
theorem auxChainD0_eq_transpose {κ : Type*} (H : AuxHypergraph k m)
    (C : κ → Finset (Fin m)) :
    auxChainD0 H C = (surgeryD0 H C).transpose := rfl

/-- **Relabelling (the $\delta_0$ item, read backwards)**:
$\delta_0 = (\partial^A_0)^{\mathsf T}$. -/
theorem surgeryD0_eq_transpose_auxChainD0 {κ : Type*} (H : AuxHypergraph k m)
    (C : κ → Finset (Fin m)) :
    surgeryD0 H C = (auxChainD0 H C).transpose := by
  rw [auxChainD0, Matrix.transpose_transpose]

/-- **$A_\bullet$ is a chain complex (first composite)**:
$\partial^A_1 \partial^A_2 = 0$. Obtained by transposing $\delta_2 \delta_1 = 0$ (the
complex condition of `Homology/AuxComplex.lean`) -- that is, **the relabelling produces no
new complex condition**; it is the one that was already there. -/
theorem auxChainD1_mul_auxChainD2 {ι : Type*} [Fintype ι] (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (hW : ∀ w, IsComponent H (W w)) :
    auxChainD1 H * auxChainD2 W = 0 := by
  rw [auxChainD1, auxChainD2, ← Matrix.transpose_mul,
    surgeryD2_mul_surgeryD1_eq_zero H W hW, Matrix.transpose_zero]

/-- **$A_\bullet$ is a chain complex (second composite)**:
$\partial^A_0 \partial^A_1 = 0$. -/
theorem auxChainD0_mul_auxChainD1 {κ : Type*} (H : AuxHypergraph k m)
    (C : κ → Finset (Fin m)) (hC : ∀ c, IsCycleSet H (C c)) :
    auxChainD0 H C * auxChainD1 H = 0 := by
  rw [auxChainD0, auxChainD1, ← Matrix.transpose_mul,
    surgeryD1_mul_surgeryD0_eq_zero H C hC, Matrix.transpose_zero]

/-! ## 4. The CSS code read off $A_\bullet$: $\mathbb F_2^V$ is $C_1$

Def 2.5 says the subcode is "a code **defined by the chain complex** $A_\bullet$". This
module reads that sentence under the degree convention (**no longer a free choice**): qubit
space = $A_1$, Z checks = $A_2$, X checks = $A_0$, so the two check matrices are exactly

$$H_X = \partial^A_1 : A_1 \to A_0,\qquad H_Z = (\partial^A_2)^{\mathsf T} : A_1 \to A_2 .$$

They are **exactly swapped in labelling** relative to the two matrices of
`Homology/SubcodeLayer.lean` (which calls $\delta_1^{\mathsf T}$ the Z checks and $\delta_2$
the X checks) -- because that file reads from the **cochain** complex directly, whereas this
one reads from the chain complex **after the degree-shift**, and each relabelling swaps the
X/Z names once. The two are **the same two-matrix object**, and this module machine-checks
that fact as two `rfl`-level theorems (`chainCodeX_eq_subcodeZChecks`,
`chainCodeZ_eq_subcodeXChecks`). -/

/-- **The X-check matrix of the code read off $A_\bullet$**: the chain differential
$\partial^A_1$ itself. -/
abbrev chainCodeX (H : AuxHypergraph k m) : Matrix (Fin m) (Fin k) (ZMod 2) := auxChainD1 H

/-- **The Z-check matrix of the code read off $A_\bullet$**: the transpose of
$\partial^A_2$, with row index = $A_2$. -/
abbrev chainCodeZ {ι : Type*} (W : ι → Finset (Fin k)) : Matrix ι (Fin k) (ZMod 2) :=
  (auxChainD2 W).transpose

/-- **★ The labelling swap (the X half)**: the X checks read off the chain complex are the
Z checks of `Homology/SubcodeLayer.lean` (both are $\delta_1^{\mathsf T}$). -/
theorem chainCodeX_eq_subcodeZChecks (H : AuxHypergraph k m) :
    chainCodeX H = subcodeZChecks H := rfl

/-- **★ The labelling swap (the Z half)**: the Z checks read off the chain complex
($\delta_2$) are the X checks of `Homology/SubcodeLayer.lean`. -/
theorem chainCodeZ_eq_subcodeXChecks {I : ℕ} (W : Fin I → Finset (Fin k)) :
    chainCodeZ W = subcodeXChecks W := by
  rw [chainCodeZ, auxChainD2, subcodeXChecks, Matrix.transpose_transpose]

/-- **★ The arithmetic form of the gap**: the **X distance** of the code read off
$A_\bullet$ is exactly `SubcodeLayer.subcodeDistanceZ` -- that is, the $d_1^\bullet$ of
[14] §1.2. (X distance = $\min\{|x| : H_Z x = 0,\ x \notin \operatorname{rowSpace} H_X\}$;
substituting $H_Z = \delta_2$, $H_X = \delta_1^{\mathsf T}$ gives $d_1^\bullet$.) -/
theorem chainCode_distanceX_eq_subcodeDistanceZ {I : ℕ} (H : AuxHypergraph k m)
    (W : Fin I → Finset (Fin k)) :
    min_weight_ker_not_mem_rowspace (chainCodeZ W) (chainCodeX H) = subcodeDistanceZ H W := by
  rw [chainCodeZ_eq_subcodeXChecks, chainCodeX_eq_subcodeZChecks]
  rfl

/-- **★ $\mathbb F_2^V$ **is** $C_1$ (the precise form of the full block reading)**:
taking $\iota = \varepsilon = \mathrm{id}$ (vertices are all data bits, hyperedges are all
$X$ checks), both components of the chain map are **identity matrices** (`basisMap_id`), so
the chain condition $\partial^C_1 f_1 = f_0 \partial^A_1$ collapses to
$\partial^A_1 = H_X$: the incidence matrix of the auxiliary complex **equals** the $X$-check
matrix of the code term by term -- exactly the source's p.18 "Thus in order for the checks
of the deformed code to commute, we have $G = H_X^{\mathsf T}$". -/
theorem fullBlock_chainCondition_iff (n : ℕ) (Hx dA1 : Matrix (Fin n) (Fin n) (ZMod 2)) :
    basisMap (id : Fin n → Fin n) * dA1 = Hx * basisMap (id : Fin n → Fin n) ↔ dA1 = Hx := by
  rw [basisMap_id, Matrix.one_mul, Matrix.mul_one]

/-! ## 5. Where $A_\bullet$ comes from: the incidence induced by the code's $X$ checks

The source's p.18: "$\mathcal H$ has 1-to-1 maps from edges to $X$ checks in $Q$ and to $X$
checks in $Q'$, and similar for vertices. **Thus in order for the checks of the deformed code
to commute, we have $G = H_X^{\mathsf T}$.**"

The reading of this section: the "injection from hyperedges to $X$ checks" of $\mathcal H$
is $\varepsilon$ (hyperedge $e$ corresponds to the $\varepsilon e$-th $X$ check of the code),
and the "injection from vertices to data bits" is $\iota$ (vertex $v$ corresponds to the
$\iota v$-th data bit of the code). The incidence matrix therefore **has no freedom**:
$G(v,e) = H_X(\varepsilon e, \iota v)$. This section turns that into four theorems:

* `surgeryD1_inducedHyper_apply` / `surgeryD1_inducedHyper`: the induced incidence equals,
  term by term, the restricted form of $H_X^{\mathsf T}$ (the **construction**);
* `inducedSubcode_comm1`: it **automatically** satisfies the chain condition -- so
  $A_\bullet$ really embeds into $C_\bullet$ through $f_\bullet$, rather than "just one
  commuting square short";
* `incidence_unique`: **conversely, any** incidence matrix satisfying the chain condition
  is uniquely determined to be of this shape on every selected hyperedge -- this is the
  "forced" half of the source's "Thus $\dots$ we have $G = H_X^{\mathsf T}$";
* `touching_of_chainCondition`: the chain condition further forces "a hyperedge may connect
  only to an $X$ check intersecting a port bit" (the source's "construct the measurement
  hypergraph $\mathcal H$ to connect only to a subcode"). -/

/-- **The auxiliary hypergraph induced by the port data** (the $G = H_X^{\mathsf T}$ of
[14] p.18): vertices = selected data bits ($\iota$), hyperedges = selected $X$ checks
($\varepsilon$); vertex $v$ lies in hyperedge $e$ iff bit $\iota v$ is in the support of
the $\varepsilon e$-th $X$ check. -/
def inducedHyper {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) : AuxHypergraph k m where
  edge e := Finset.univ.filter (fun v => Hx (ε e) (ι v) = 1)

/-- **The induced incidence equals $H_X$ entry by entry**:
`surgeryD1 (inducedHyper Hx ι ε) v e = Hx (ε e) (ι v)`. -/
theorem surgeryD1_inducedHyper_apply {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) (v : Fin k) (e : Fin m) :
    surgeryD1 (inducedHyper Hx ι ε) v e = Hx (ε e) (ι v) := by
  have hedge : (inducedHyper Hx ι ε).edge e =
      Finset.univ.filter (fun u : Fin k => Hx (ε e) (ι u) = 1) := rfl
  have hmem : (v ∈ (inducedHyper Hx ι ε).edge e) ↔ Hx (ε e) (ι v) = 1 := by
    rw [hedge, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩
  show (if v ∈ (inducedHyper Hx ι ε).edge e then (1 : ZMod 2) else 0) = Hx (ε e) (ι v)
  by_cases h : Hx (ε e) (ι v) = 1
  · rw [ite_eq_left (hmem.mpr h), h]
  · rw [ite_eq_right (fun hc => h (hmem.mp hc)), eq_zero_of_ne_one h]

/-- **The induced incidence matrix is the restricted transpose of $H_X$** (matrix form):
restrict $H_X$ to rows $\varepsilon$ and columns $\iota$, then transpose (that is, the
source's $G = H_X^{\mathsf T}$). -/
theorem surgeryD1_inducedHyper {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) :
    surgeryD1 (inducedHyper Hx ι ε) = (Hx.submatrix ε id).transpose.submatrix ι id := by
  ext v e
  rw [surgeryD1_inducedHyper_apply]
  rfl

/-- **The weight of a selected $X$ check on the port bits.** -/
def xWeightOn {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2)) (ι : Fin k → Fin n)
    (c : Fin a) : ℕ := hammingNorm (fun v : Fin k => Hx c (ι v))

/-- **The cardinality of a hyperedge of the induced hypergraph = the weight of the selected
$X$ check on the port bits.** -/
theorem inducedHyper_edge_card {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) (e : Fin m) :
    ((inducedHyper Hx ι ε).edge e).card = xWeightOn Hx ι (ε e) := by
  have hfilter : (Finset.univ.filter (fun v : Fin k => Hx (ε e) (ι v) = 1)) =
      (Finset.univ.filter (fun v : Fin k => Hx (ε e) (ι v) ≠ 0)) := by
    refine Finset.filter_congr fun v _ => ?_
    exact ⟨fun h => by rw [h]; exact one_ne_zero, fun h => eq_one_of_ne_zero h⟩
  change (Finset.univ.filter (fun v : Fin k => Hx (ε e) (ι v) = 1)).card =
    xWeightOn Hx ι (ε e)
  rw [hfilter]
  rfl

/-- **★ The exact meaning of the induced hypergraph being "even"**: even iff **every
selected $X$ check has even weight on the port bits**. So the even hypothesis in the
main theorem of `Homology/SubcodeLayer.lean` is, under this construction, not an
abstract condition but a checkable property on the code side. -/
theorem inducedHyper_isEven_iff {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) :
    IsEvenHyper (inducedHyper Hx ι ε) ↔ ∀ e : Fin m, Even (xWeightOn Hx ι (ε e)) := by
  exact ⟨fun h e => by simpa [inducedHyper_edge_card] using h e,
    fun h e => by simpa [inducedHyper_edge_card] using h e⟩

/-- **★ The induced incidence automatically satisfies the chain condition (the $i = 1$
half)**: $f_0 \partial^A_1 = \partial^C_1 f_1$, i.e.
$\varepsilon_\bullet \cdot (\delta_1^{\mathsf T}) = H_X \cdot \iota_\bullet$.

`htouch` is the **only** extra condition needed for this to hold, and its content matches
the source's p.26 "construct the measurement hypergraph $\mathcal H$ to connect only to a
*subcode* of each": **an $X$ check intersecting a port bit must not be left out** (if it is,
it lies outside the image of $\varepsilon$ and the two sides fail to match;
`touching_of_chainCondition` proves that it is also **necessary**). In the full block
reading ($\varepsilon$ is a bijection) it holds automatically -- that is the source's p.18
"1-to-1 maps from edges to $X$ checks". -/
theorem inducedSubcode_comm1 {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) (hε : Function.Injective ε)
    (htouch : ∀ c : Fin a, (∃ v : Fin k, Hx c (ι v) = 1) → c ∈ Set.range ε) :
    basisMap ε * auxChainD1 (inducedHyper Hx ι ε) = Hx * basisMap ι := by
  have key : ∀ (c : Fin a) (v : Fin k),
      (∑ q : Fin n, Hx c q * basisMap ι q v) = Hx c (ι v) := by
    intro c v
    rw [Finset.sum_eq_single (ι v)]
    · rw [basisMap_apply_self, mul_one]
    · intro q _ hq
      rw [basisMap_apply, ite_eq_right (fun h : ι v = q => hq h.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (ι v)) h
  ext c v
  rw [Matrix.mul_apply, Matrix.mul_apply, key c v]
  by_cases hc : c ∈ Set.range ε
  · obtain ⟨e₀, he₀⟩ := hc
    rw [Finset.sum_eq_single e₀]
    · rw [← he₀, basisMap_apply_self, one_mul, auxChainD1, Matrix.transpose_apply,
        surgeryD1_inducedHyper_apply]
    · intro b _ hb
      have hne : ε b ≠ c := fun hbc => hb (hε (by rw [hbc, he₀]))
      rw [basisMap_apply_eq_zero ε hne, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ e₀) h
  · have hzero : Hx c (ι v) = 0 :=
      eq_zero_of_ne_one fun hone => hc (htouch c ⟨v, hone⟩)
    rw [Finset.sum_eq_zero (fun e _ => ?_), hzero]
    rw [basisMap_apply_eq_zero ε (fun h : ε e = c => hc ⟨e, h⟩), zero_mul]

/-- **★ The chain condition uniquely determines the incidence matrix** (the [14] p.18 "Thus
in order for the checks of the deformed code to commute, we have $G = H_X^{\mathsf T}$"):
let $\varepsilon$ be injective and let $G$ be **any** incidence matrix making the checks of
the deformed code commute (i.e. satisfying the chain condition
$\varepsilon_\bullet G = H_X \iota_\bullet$); then on every selected hyperedge $G$
**equals** the induced incidence -- the induced incidence is the **unique** such incidence. -/
theorem incidence_unique {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) (hε : Function.Injective ε)
    (G : Matrix (Fin m) (Fin k) (ZMod 2)) (hG : basisMap ε * G = Hx * basisMap ι)
    (e : Fin m) : G e = auxChainD1 (inducedHyper Hx ι ε) e := by
  funext v
  have hentry := congrFun (congrFun hG (ε e)) v
  rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
  have hL : (∑ b : Fin m, basisMap ε (ε e) b * G b v) = G e v := by
    rw [Finset.sum_eq_single e]
    · rw [basisMap_apply_self, one_mul]
    · intro b _ hb
      rw [basisMap_apply, ite_eq_right (fun h : ε b = ε e => hb (hε h)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ e) h
  have hR : (∑ q : Fin n, Hx (ε e) q * basisMap ι q v) = Hx (ε e) (ι v) := by
    rw [Finset.sum_eq_single (ι v)]
    · rw [basisMap_apply_self, mul_one]
    · intro q _ hq
      rw [basisMap_apply, ite_eq_right (fun h : ι v = q => hq h.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (ι v)) h
  rw [hL, hR] at hentry
  rw [auxChainD1, Matrix.transpose_apply, surgeryD1_inducedHyper_apply]
  exact hentry

/-- **★ The chain condition further forces "connect only to a subcode"** (the source's p.16
"connect only to a subcode"): if $G$ satisfies the chain condition, then **every $X$ check
intersecting some port bit** must lie in the image of $\varepsilon$ (otherwise it does not
appear in the hypergraph, yet it does intersect a port bit -- the chain condition forbids
this kind of "omission"). -/
theorem touching_of_chainCondition {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a) (_hε : Function.Injective ε)
    (G : Matrix (Fin m) (Fin k) (ZMod 2)) (hG : basisMap ε * G = Hx * basisMap ι)
    (c : Fin a) (hc : ∃ v : Fin k, Hx c (ι v) = 1) : c ∈ Set.range ε := by
  by_contra hnot
  obtain ⟨v, hv⟩ := hc
  have hentry := congrFun (congrFun hG c) v
  rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
  have hL : (∑ b : Fin m, basisMap ε c b * G b v) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [basisMap_apply_eq_zero ε (fun h : ε b = c => hnot ⟨b, h⟩), zero_mul]
  have hR : (∑ q : Fin n, Hx c q * basisMap ι q v) = Hx c (ι v) := by
    rw [Finset.sum_eq_single (ι v)]
    · rw [basisMap_apply_self, mul_one]
    · intro q _ hq
      rw [basisMap_apply, ite_eq_right (fun h : ι v = q => hq h.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (ι v)) h
  rw [hL, hR, hv] at hentry
  exact absurd hentry.symm (by decide)

/-- **★ The chain map of Def 2.5, gauging case**: take $W = \emptyset$ (the source's p.26
"This component corresponds to metachecks, so we ignore that term for now"; the gauging
auxiliary complex of §6.2 is "a graph", with no metacheck term). Then $A_2 = 0$ and
$f_2 = \mathrm{elim}_0$ are trivial, $f_0 = \varepsilon_\bullet$, $f_1 = \iota_\bullet$;
of the two chain conditions, the $i = 1$ one holds automatically by the induced incidence
(`inducedSubcode_comm1`), and the $i = 2$ one holds **unconditionally** (both sides are
matrices with zero columns).

`Hz` is just the $Z$-check matrix of the memory code; when $A_2 = 0$ the chain condition
does not consume it (it is taken as it is, so that the half "$C_2 =$ the $Z$ checks of the
memory code" is visible in the type). -/
def inducedSubcodeChainMap {a b n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin b) (Fin n) (ZMod 2)) (ι : Fin k → Fin n) (ε : Fin m → Fin a)
    (hι : Function.Injective ι) (hε : Function.Injective ε)
    (htouch : ∀ c : Fin a, (∃ v : Fin k, Hx c (ι v) = 1) → c ∈ Set.range ε) :
    SubcodeChainMap m k 0 a n b (auxChainD1 (inducedHyper Hx ι ε))
      (auxChainD2 (fun w : Fin 0 => w.elim0)) Hx Hz.transpose where
  phi0 := ε
  phi1 := ι
  phi2 := fun w : Fin 0 => w.elim0
  inj0 := hε
  inj1 := hι
  inj2 := fun x _ _ => x.elim0
  comm1 := inducedSubcode_comm1 Hx ι ε hε htouch
  comm2 := by
    ext i j
    exact j.elim0

/-- **★ A non-degenerate chain map: an instance with $A_2 \ne 0$** ($W \ne \emptyset$).

`inducedSubcodeChainMap` takes $\iota = \mathrm{Fin}\ 0$, i.e. **no metacheck** -- exactly
the choice of [14] p.26: *"Note that also $A_\bullet$ generally possesses a nonzero $A_2$
component. This component corresponds to metachecks, so we ignore that term for now."*

**That choice is not a limitation of the chain-map structure**: `phi2` and `comm2` are just
fields of `SubcodeChainMap`. This definition gives an instance with $A_2$ **nonempty** -- the
target complex is taken to be itself and all three components are the identity, so that the
two chain conditions degenerate to $1\cdot\partial = \partial\cdot 1$.

**Boundary (stated)**: what the library lacks is the **induced** instance in which "the
target-code side also carries a metacheck layer" -- that layer is exactly the term the
source says to ignore. So this item is of the same kind as Case 2 of §16: what is missing is
**an object the source does not give**, not work. -/
def selfChainMap {k m a₂ : ℕ} (H : AuxHypergraph k m) (W : Fin a₂ → Finset (Fin k)) :
    SubcodeChainMap m k a₂ m k a₂ (auxChainD1 H) (auxChainD2 W)
      (auxChainD1 H) (auxChainD2 W) where
  phi0 := id
  phi1 := id
  phi2 := id
  inj0 := Function.injective_id
  inj1 := Function.injective_id
  inj2 := Function.injective_id
  comm1 := by simp [basisMap_id]
  comm2 := by simp [basisMap_id]

/-- **It indeed carries a non-trivial $A_2$ component**: the third component sends some
element of $A_2$ to itself -- that is, $\varphi_2$ is defined on a **nonempty** index set,
not on the empty type as in `inducedSubcodeChainMap`. -/
theorem selfChainMap_phi2_apply {a₂ : ℕ} (H : AuxHypergraph k m)
    (W : Fin (a₂ + 1) → Finset (Fin k)) :
    (selfChainMap H W).phi2 ⟨0, Nat.succ_pos a₂⟩ = ⟨0, Nat.succ_pos a₂⟩ := rfl

/-! ## 6. [14] §6.2's "gauging subcode has distance 1", on the constructed $A_\bullet$

The source's §6.2 (p.35):

> Gauging logical measurement [56] can be seen as an instance of hypergraph surgery where
> the subcode $A_\bullet$ has distance 1, and therefore requires $O(d)$ rounds of syndrome
> measurement to maintain fault-distance $d$.

`Homology/SubcodeLayer.lean` machine-checks this sentence as `subcodeDistanceZ_eq_one`, but
the $A_\bullet$ there is "this library's self-built reading". This section moves **the same
conclusion** onto the $A_\bullet$ **constructed from the chain map of Def 2.5**
(`inducedHyper` + `inducedSubcodeChainMap`). -/

/-- **★ The machine check of §6.2 (construction side)**: the auxiliary hypergraph induced
by the port data (that is, $G = H_X^{\mathsf T}$) has, in the **even** case, subcode Z
distance exactly 1. -/
theorem gaugingSubcode_distanceZ_eq_one {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a)
    (heven : IsEvenHyper (inducedHyper Hx ι ε)) (v : Fin k) :
    subcodeDistanceZ (inducedHyper Hx ι ε) (fun w : Fin 0 => w.elim0) = 1 :=
  subcodeDistanceZ_eq_one_empty _ heven v

/-- **★ The same conclusion in the "code read off $A_\bullet$" convention**: the **X
distance** of this code is 1, and it is the $d_1^\bullet$ of §1.2
(`chainCode_distanceX_eq_subcodeDistanceZ`). -/
theorem chainCode_distanceX_eq_one {a n : ℕ} (Hx : Matrix (Fin a) (Fin n) (ZMod 2))
    (ι : Fin k → Fin n) (ε : Fin m → Fin a)
    (heven : IsEvenHyper (inducedHyper Hx ι ε)) (v : Fin k) :
    min_weight_ker_not_mem_rowspace (chainCodeZ (fun w : Fin 0 => w.elim0))
      (chainCodeX (inducedHyper Hx ι ε)) = 1 := by
  rw [chainCode_distanceX_eq_subcodeDistanceZ]
  exact gaugingSubcode_distanceZ_eq_one Hx ι ε heven v

/-- **The full block reading case** (the source's p.18 "1-to-1 maps"):
$\iota = \varepsilon = \mathrm{id}$, and the induced hypergraph is the code's $X$-Tanner
graph. -/
theorem fullBlock_distanceZ_eq_one (n : ℕ) (Hx : Matrix (Fin n) (Fin n) (ZMod 2))
    (heven : IsEvenHyper (inducedHyper Hx (id : Fin n → Fin n) (id : Fin n → Fin n)))
    (v : Fin n) :
    subcodeDistanceZ (inducedHyper Hx (id : Fin n → Fin n) (id : Fin n → Fin n))
      (fun w : Fin 0 => w.elim0) = 1 :=
  subcodeDistanceZ_eq_one_empty _ heven v

/-- **The meaning on the code side of the full block reading's even condition**: under the
identity ports, `Even (xWeightOn Hx id c)` is "the $c$-th $X$ check has even weight". -/
theorem xWeightOn_id (n : ℕ) (Hx : Matrix (Fin n) (Fin n) (ZMod 2)) (c : Fin n) :
    xWeightOn Hx (id : Fin n → Fin n) c = hammingNorm (fun q : Fin n => Hx c q) := rfl

/-- **The even condition of the full block reading** (together with `xWeightOn_id`, this is
"$X$ checks have even weight"). -/
theorem fullBlock_isEven_iff (n : ℕ) (Hx : Matrix (Fin n) (Fin n) (ZMod 2)) :
    IsEvenHyper (inducedHyper Hx (id : Fin n → Fin n) (id : Fin n → Fin n)) ↔
      ∀ c : Fin n, Even (hammingNorm (fun q : Fin n => Hx c q)) := by
  rw [inducedHyper_isEven_iff]
  constructor
  · intro h c
    simpa only [xWeightOn, id_eq] using h c
  · intro h c
    simpa only [xWeightOn, id_eq] using h c

end QECCertificates.Homology
