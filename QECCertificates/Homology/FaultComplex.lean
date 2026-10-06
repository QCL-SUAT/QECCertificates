/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.MappingCone
import QECCertificates.Codes.TimeLikeInstance
import QECCertificates.Codes.CaseMatrix

open QECCertificates

/-!
# The fault complex: the four-term chain complex of [14] Appendix A.1

The honest boundary in §5 item 1 of `the gauged-measurement companion development's `SurgerySchedule` module` records verbatim that
**the fault complex of [14] Appendix A.1 is not formalized in this library**, while the
proofs of [14] Theorem 6.5 / 6.3 go through the homology classification on it.
`Homology/MappingCone.lean` supplied the mapping cone (the cone's complex condition, the
short exact sequence, the connecting homomorphism, the dimension identities), and
`Homology/AuxComplex.lean` supplied the four-term **auxiliary** complex of [14] §1.2 and the
$1$-cosystolic distance -- but neither of those **is** the fault complex of A.1 itself.
What this module supplies **is** that complex.

## 1. The text of [14] Appendix A.1, verbatim (this module's only source of definitions)

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895.

**p.61** (the four terms of the complex and the labelling of the six blocks):

> A.1 Fault complexes
>
> A fault complex is defined as a chain complex with 4 terms,
>
> $$F_\bullet = F_3 \longrightarrow F_2 \longrightarrow F_1 \longrightarrow F_0$$
>
> where by convention the $F_3$ and $F_0$ components correspond to $Z$ and $X$ detectors
> respectively. In fault-tolerant measurement-based quantum computing (MBQC), $F_2$ corresponds
> to a set of $X$ fault locations, i.e. locations in spacetime which can experience only
> $X$-type faults, while $F_1$ corresponds to a set of $Z$-type fault locations. The fault
> complex is therefore in bijection with a graph state.
>
> When the graph state corresponds to a foliated CSS code, this can be reinterpreted in the
> circuit model, undergoing phenomenological noise. Now, $F_2$ corresponds to a combined
> set of spacetime locations at which data qubits can experience $X$ Pauli faults and also $Z$
> checks, which can experience measurement errors. $F_1$ is the same but for $Z$ Pauli faults
> and $X$ checks. In this case, we can expand out a fault complex to have the following diagram:

**p.62** (the square diagram of the six blocks, and the **total-complex** reading of
"taking direct sums vertically"):

> where components in the overall fault complex are given by taking direct sums vertically
> in the diagram, so we have
>
> $$F_{1,2} \longrightarrow F_{1,1} \oplus F_{0,2} \longrightarrow F_{1,0} \oplus F_{0,1}
>   \longrightarrow F_{0,0}$$
>
> Throughout this section every diagram drawn in the above form is assumed to have direct
> sums vertically in the diagram.¹⁵
>
> [footnote 15] This is essentially passing to the "total complex" [90].

The six labels on the same page, verbatim:

> * $F_{0,0}$ corresponds to $X$ detectors.
> * $F_{0,1}$ corresponds to locations for $Z$ Pauli faults on data qubits.
> * $F_{1,0}$ corresponds to locations for $X$ check faults.
> * $F_{0,2}$ corresponds to locations for $Z$ check faults.
> * $F_{1,1}$ corresponds to locations for $X$ Pauli faults on data qubits.
> * $F_{1,2}$ corresponds to $Z$ detectors.

**p.63** (the explicit shape under a foliated CSS code; the basis for the §4/§5
instances of this module):

> The standard way to foliate a CSS code $C_\bullet$ from the fault complex perspective is to
> take $(\mathcal R \otimes C)_\bullet$, where $\mathcal R_\bullet : \mathcal R_1 \to
> \mathcal R_0$ has the differential $R$ being either the full-rank parity-check matrix for
> the repetition code or its dual. In the former, the code is initialised in the $|0\rangle$
> state and measured out in the $Z$ basis; in the latter, the code is initialised in the
> $|+\rangle$ state and measured out in the $X$ basis. Hence the code "idles" for $l$ rounds,
> where $l$ is the blocklength of the repetition code.
>
> If we do this, the fault complex has the explicit form:
>
> $$\mathcal R_1 \otimes C_2 \longrightarrow \mathcal R_1 \otimes C_1 \oplus
>   \mathcal R_0 \otimes C_2 \longrightarrow \mathcal R_1 \otimes C_0 \oplus
>   \mathcal R_0 \otimes C_1 \longrightarrow \mathcal R_0 \otimes C_0 \qquad (5)$$
>
> Note that $\mathcal R_1 \otimes C_1$ and $\mathcal R_0 \otimes C_1$ correspond to the same
> data qubits but at different points in time; in the circuit model this is purely convention,
> and any given data qubit can still undergo either type of error, $Z$ or $X$.
>
> It is easy to compute the homologies using the Künneth formula. Then elements of $H_1(F)$
> correspond to equivalence classes of logical $\overline Z$ faults in spacetime, composed of
> $Z$ Pauli errors and $X$ check errors, and elements of $H^2(F)$ to logical $\overline X$
> faults, composed of $X$ Pauli errors and $Z$ check errors.

## 2. What A.1 gives and what it does not (this module's choices, honestly marked)

**The text states explicitly**: the names and directions of the four terms, the pairwise
correspondence of the six blocks, that the four terms are formed from the six blocks by
**taking direct sums vertically** (the $F_{1,2} \longrightarrow F_{1,1} \oplus F_{0,2}
\longrightarrow F_{1,0} \oplus F_{0,1} \longrightarrow F_{0,0}$ of p.62), the shape of
$(\mathcal R \otimes C)_\bullet$ in the foliated CSS case (Eq. (5) of p.63), and the
physical meaning of $H_1$ / $H^2$.

**What the text does not print**: **the matrices of the three differentials
$\partial_0,\partial_1,\partial_2$ themselves**. p.62 only **draws** the seven arrows
($F_{1,2}\to F_{1,1}$, $F_{1,2}\to F_{0,2}$, $F_{1,1}\to F_{1,0}$, $F_{1,1}\to F_{0,1}$,
$F_{0,2}\to F_{0,1}$, $F_{1,0}\to F_{0,0}$, $F_{0,1}\to F_{0,0}$) and gives no matrix
formula for the individual blocks. This module therefore gives **two** things and keeps
them strictly apart:

1. `FaultComplex` (§2) takes the **seven blocks as data**: the complex condition then
   splits into four **block equations** (`d11_10 * d12_11 = 0` and so on), and this
   module proves "these four block equations hold ⟹ the assembled four terms form a
   complex" -- **this is the whole proof obligation of "it is a complex", and no
   particular matrices are presupposed**.
2. `koszulFaultComplex` (§3) gives **one concrete set of blocks**: footnote 15 says that
   taking direct sums vertically is the **total complex**, and the differential of the
   total complex is fixed by the Koszul formula
   $\partial(x \otimes y) = \partial_{\mathcal R} x \otimes y + x \otimes \partial_C y$.
   This module **proves** that this set of blocks satisfies those four block equations,
   and that the only nontrivial input is the **CSS condition**
   $\partial_1 \partial_2 = 0$. What this passage claims to be is "**the total-complex
   reading really is a complex**", not "A.1 printed this formula".

## 3. What this module does

* **§1 the four-term chain complex**: `FaultComplex` -- the types of the six blocks, the
  four terms (vertical direct sums), the three differentials `fd2` / `fd1` / `fd0` (block
  matrices, padded at both ends with `Fin 0` into one and the same block shape, the same
  device as `coneD2` in `Homology/MappingCone.lean`).
* **§2 the complex condition**: `FaultComplex.comp_d1_d2` / `comp_d0_d1` (**it is a
  complex**), and the assembly criterion that **splits the complex condition into four
  block equations**: `fd0_mul_fd1_of` / `fd1_mul_fd2_of` / `faultComplexOf`.
* **§3 the total complex (Koszul)**: the three Kronecker gadgets `kron_mul` /
  `kron_zero_left` / `add_self_matrix`, and `koszulFaultComplex` -- **the CSS condition
  $\partial_1\partial_2 = 0$ makes the fault complex a complex**, which is the algebraic
  content of A.1's "is a chain complex with 4 terms".
* **§4 instance one (timelike, `Codes/TimeLikeInstance.lean`)**: a trivial complex on the
  code side and the $l = 4$ repetition code on the timelike side; it proves that the
  instance's diagonal block ($F_{1,1} \to F_{0,1}$) **is** `timeLike34H` (under the
  relabelling `finProdFinEquiv`) -- that is, the matrix "12 (check, round) positions → 9
  (check, adjacent round) positions" in `Codes/TimeLikeInstance.lean` **is** the
  differential of the fault complex. Homology reading: $\dim H^2 = 3$
  (`timeLikeFaultComplex_cycles_finrank`), and the least weight of a nonzero element is
  $= 4 = T$ (`timeLikeFaultComplex_minWeight`, cross-checked against `timeLike34_d`).
* **§5 instance two (the Shor code $[[9,1,3]]$, non-degenerate)**: a four-term complex
  that is **nonzero at both ends** ($24 \to 54 \to 35 \to 6$), with the four block
  equations re-checked independently by `by decide` on the **explicit matrices** (without
  reusing the general proof of §3).
* **§6 relation to the mapping cone**: `FaultComplex.toCochain4` feeds a fault complex
  into the `Cochain4` of `Homology/MappingCone.lean`, so that module's cone, short exact
  sequence, connecting homomorphism and dimension identities are **directly available**
  for a fault complex. **A.1 does not print which surgery map $F$ is taken** (p.61 only
  says "In our case we will take mapping cones on spacetime volumes"), so this module does
  **not** state "some fault complex = the cone of the idling fault complex" -- see §7
  item 2.

## 4. Honest boundary (cited by the paper text)

**Not done, and not claimed**:

1. **The three differentials are a "total-complex reading", not a formula printed in
   A.1**. A.1 gives only the shape and the seven arrows; the `koszulFaultComplex` of §3
   is a **reading** of "vertical direct sums = total complex" (footnote 15) together with
   the Koszul formula. A.1 does not write this formula, and this library cannot decide
   from A.1 that it is the one the authors of [14] used. The `FaultComplex` of §2 takes
   the seven blocks as data precisely so that this choice is **exposed to the user**.
2. **"Taking the mapping cone on the idling complex gives the surgery complex" is not
   formalized**. A.1 mentions cones (p.61, "we will take mapping cones on spacetime
   volumes") and the dimension formula of Eq. (4), but **does not give the map $F$ that
   is coned** ($F$ is defined in the surgery construction of [14] §6). Without $F$ there
   is no statement, and this module hands over only the bridge "fault complex =
   `Cochain4`" (`toCochain4`), making the cone machinery of `Homology/MappingCone.lean`
   usable; §5 item 1 of `SurgerySchedule.lean` (the gap is in the **combination** of the
   fault complex itself with the mapping cone) **is still not closed**.
3. **A.1 content this module does not reproduce**: (a) the sentence on p.62, "The fault
   complex is therefore in bijection with a graph state" (graph states ↔ fault
   complexes), **is not formalized** -- this library has no graph-state / stabilizer-graph
   representation layer; (b) the Künneth formula of p.63
   $H_1(\mathcal R \otimes C) = H_1(\mathcal R) \otimes H_0(C) \oplus H_0(\mathcal R)
   \otimes H_1(C)$ and the dual formula for $H^2$ are not in this module, having been
   machine-checked in `Codes/FaultComplexKunneth` (all four degrees over a general $R$,
   instantiated at the two repetition-code foliations that p.63 uses); (c) $H_1(F)$ /
   $H^4(F)$ of footnote 16 ("impossible detector triggers") is not formalized; (d) the
   bodies of [14] Thm 6.5 / 6.3 (phenomenological fault distance) are not formalized.
4. **This library's code distance is the static distance of the
   `min_weight_ker_not_mem_rowspace` family, and the $1$-cosystolic distance of [14] is a
   different quantity; mixing the two gives wrong answers.** (The warning of §5 item 2 of
   `the gauged-measurement companion development's `SurgerySchedule` module`, copied here.) The instance of §4 identifies the
   differential of the fault complex with `timeLike34H`, and so **for that instance** the
   $H^2$ reading is **the same** `min_weight_ker_not_mem_rowspace` number as
   `timeLike34_d` -- this is because the instance's remaining two terms are
   $F_3 = F_0 = 0$ (see the discussion in §4), and it is **not** an identification in
   general, still less "static distance = $1$-cosystolic distance".
5. **The Shor instance of §5 does only "it is a complex"**: it computes neither the
   $H_1$ / $H^2$ dimensions nor any conclusion of the form "fault distance $= 3$" or
   "distance $\ge d$".
6. **Things read off the diagram alone, not landed in a Lean statement**: the existence
   of the **diagonal arrow** $F_{1,1} \to F_{0,1}$ in the square diagram of p.62 is read
   off the rendered diagram (the A.1 text does not enumerate the arrows); the seven blocks
   of §2 and the Koszul blocks of §3 are nonzero or zero **at this position** consistently
   with the diagram, but "the authors of A.1 did draw this diagonal arrow" is not
   something this library can machine-check.
7. **Only the sufficient direction is done**: the `fd1_mul_fd2_of` / `fd0_mul_fd1_of` of
   §2 give "four block equations ⟹ complex"; the converse direction needs a
   block-vanishing criterion for `Matrix.fromBlocks`, which this module does not touch.

**Trusted base**: this module uses no `sorry` / `admit` / `native_decide` and introduces
no custom axioms; the `#print axioms` of the load-bearing theorems are printed at the end
of the root module `QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open scoped BigOperators

open _root_.Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. The four-term chain complex: six blocks and four terms

Orientation convention: `A : Matrix m n (ZMod 2)` acting on **column vectors** denotes a
map $\mathbb F_2^n \to \mathbb F_2^m$; the complex of [14] runs $F_3 \to F_2 \to F_1 \to
F_0$. A block's name reads as **`dXY_ZW` $=$ the block mapping $F_{X,Y}$ to $F_{Z,W}$**
(source first, target second). -/

variable {F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂ : Type*}
variable [Fintype F₀₀] [Fintype F₀₁] [Fintype F₀₂]
variable [Fintype F₁₀] [Fintype F₁₁] [Fintype F₁₂]

/-- The third term of the fault complex ([14] p.62: $F_3 = F_{1,2}$, the $Z$-type
detectors).

The `Fin 0` appended at the end gives the three differentials **one and the same block
shape** ($2 \times 2$), so that the complex condition can always be expanded mechanically
with `Matrix.fromBlocks_multiply` -- the same device as `coneD2` in
`Homology/MappingCone.lean`. `Fin 0` is an empty index and changes nothing. -/
abbrev FaultTerm3 (F₁₂ : Type*) := F₁₂ ⊕ Fin 0

/-- The second term of the fault complex: $F_2 = F_{1,1} \oplus F_{0,2}$
($X$ Pauli fault locations $\oplus$ $Z$ check fault locations). -/
abbrev FaultTerm2 (F₁₁ F₀₂ : Type*) := F₁₁ ⊕ F₀₂

/-- The first term of the fault complex: $F_1 = F_{1,0} \oplus F_{0,1}$
($X$ check fault locations $\oplus$ $Z$ Pauli fault locations). -/
abbrev FaultTerm1 (F₁₀ F₀₁ : Type*) := F₁₀ ⊕ F₀₁

/-- The zeroth term of the fault complex ([14] p.62: $F_0 = F_{0,0}$, the $X$-type
detectors). -/
abbrev FaultTerm0 (F₀₀ : Type*) := F₀₀ ⊕ Fin 0

/-- **$\partial_2 : F_2 \to F_3$** (the two arrows $F_{1,2}\to F_{1,1}$ and
$F_{1,2}\to F_{0,2}$ in the diagram).

Rows split as $F_{1,1} \oplus F_{0,2}$, columns as $F_{1,2} \oplus \varnothing$; the
bottom-right block is $0$. -/
def fd2 {F₁₁ F₀₂ F₁₂ : Type*} [Fintype F₁₁] [Fintype F₀₂] [Fintype F₁₂]
    (d12_11 : Matrix F₁₁ F₁₂ (ZMod 2)) (d12_02 : Matrix F₀₂ F₁₂ (ZMod 2)) :
    Matrix (FaultTerm2 F₁₁ F₀₂) (FaultTerm3 F₁₂) (ZMod 2) :=
  Matrix.fromBlocks d12_11 0 d12_02 0

/-- **$\partial_1 : F_1 \to F_2$** (the three arrows $F_{1,1}\to F_{1,0}$,
$F_{1,1}\to F_{0,1}$ (**the diagonal arrow**) and $F_{0,2}\to F_{0,1}$ in the diagram;
the arrow $F_{0,2} \to F_{1,0}$ is not in the diagram and is taken to be $0$).

Rows split as $F_{1,0} \oplus F_{0,1}$, columns as $F_{1,1} \oplus F_{0,2}$; the
top-right block is $0$. -/
def fd1 {F₁₀ F₀₁ F₁₁ F₀₂ : Type*} [Fintype F₁₀] [Fintype F₀₁] [Fintype F₁₁] [Fintype F₀₂]
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) :
    Matrix (FaultTerm1 F₁₀ F₀₁) (FaultTerm2 F₁₁ F₀₂) (ZMod 2) :=
  Matrix.fromBlocks d11_10 0 d11_01 d02_01

/-- **$\partial_0 : F_0 \to F_1$** (the two arrows $F_{1,0}\to F_{0,0}$ and
$F_{0,1}\to F_{0,0}$ in the diagram).

Rows split as $F_{0,0} \oplus \varnothing$, columns as $F_{1,0} \oplus F_{0,1}$; the
bottom-left and bottom-right blocks are $0$. -/
def fd0 {F₀₀ F₁₀ F₀₁ : Type*} [Fintype F₀₀] [Fintype F₁₀] [Fintype F₀₁]
    (d10_00 : Matrix F₀₀ F₁₀ (ZMod 2)) (d01_00 : Matrix F₀₀ F₀₁ (ZMod 2)) :
    Matrix (FaultTerm0 F₀₀) (FaultTerm1 F₁₀ F₀₁) (ZMod 2) :=
  Matrix.fromBlocks d10_00 d01_00 0 0

/-! ## 2. The complex condition: the seven blocks as data, and when they form a complex -/

/-- **The fault complex** ([14] p.61: `a chain complex with 4 terms`
$F_3 \to F_2 \to F_1 \to F_0$).

The seven blocks are **data**: $F_{1,2}\to F_{1,1}$ and $F_{1,2}\to F_{0,2}$ (the two
blocks of $\partial_2$), $F_{1,1}\to F_{1,0}$, $F_{1,1}\to F_{0,1}$ (the diagonal arrow)
and $F_{0,2}\to F_{0,1}$ (the three blocks of $\partial_1$), $F_{1,0}\to F_{0,0}$ and
$F_{0,1}\to F_{0,0}$ (the two blocks of $\partial_0$). The two fields are the **complex
conditions** $\partial_1\partial_2 = 0$ and $\partial_0\partial_1 = 0$ -- in the
orientation of [14] ($F_3 \to F_2 \to F_1 \to F_0$). The $\delta_0/\delta_1/\delta_2$ of
`Homology/AuxComplex.lean` form **another** complex (the auxiliary complex of [14] §1.2),
not the same object as this structure. -/
structure FaultComplex (F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂ : Type*)
    [Fintype F₀₀] [Fintype F₀₁] [Fintype F₀₂]
    [Fintype F₁₀] [Fintype F₁₁] [Fintype F₁₂] where
  /-- The block $F_{1,2} \to F_{1,1}$ ($Z$ detectors $\to$ $X$ Pauli faults). -/
  d12_11 : Matrix F₁₁ F₁₂ (ZMod 2)
  /-- The block $F_{1,2} \to F_{0,2}$ ($Z$ detectors $\to$ $Z$ check faults). -/
  d12_02 : Matrix F₀₂ F₁₂ (ZMod 2)
  /-- The block $F_{1,1} \to F_{1,0}$ ($X$ Pauli faults $\to$ $X$ check faults). -/
  d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)
  /-- The block $F_{1,1} \to F_{0,1}$ (**the diagonal arrow in the diagram**:
  $X$ Pauli faults $\to$ $Z$ Pauli faults). -/
  d11_01 : Matrix F₀₁ F₁₁ (ZMod 2)
  /-- The block $F_{0,2} \to F_{0,1}$ ($Z$ check faults $\to$ $Z$ Pauli faults). -/
  d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)
  /-- The block $F_{1,0} \to F_{0,0}$ ($X$ check faults $\to$ $X$ detectors). -/
  d10_00 : Matrix F₀₀ F₁₀ (ZMod 2)
  /-- The block $F_{0,1} \to F_{0,0}$ ($Z$ Pauli faults $\to$ $X$ detectors). -/
  d01_00 : Matrix F₀₀ F₀₁ (ZMod 2)
  /-- The complex condition $\partial_1 \partial_2 = 0$. -/
  comp_d1_d2 : fd1 d11_10 d11_01 d02_01 * fd2 d12_11 d12_02 = 0
  /-- The complex condition $\partial_0 \partial_1 = 0$. -/
  comp_d0_d1 : fd0 d10_00 d01_00 * fd1 d11_10 d11_01 d02_01 = 0

/-- **Block decomposition of the complex condition (the second composite)**:
$\partial_1\partial_2 = 0$ is given by two **block equations**

$$F_{1,1}\colon\ d_{1,1\to 1,0}\, d_{1,2\to 1,1} = 0, \qquad
  F_{0,1}\colon\ d_{1,1\to 0,1}\, d_{1,2\to 1,1} + d_{0,2\to 0,1}\, d_{1,2\to 0,2} = 0.$$

(The **sufficient** direction, the one §3 of this module actually uses; the converse
needs a block-vanishing criterion for `Matrix.fromBlocks` and is not touched here, see
§4 item 7 of the module header.) -/
theorem fd1_mul_fd2_of {F₁₀ F₀₁ F₁₁ F₀₂ F₁₂ : Type*}
    [Fintype F₁₀] [Fintype F₀₁] [Fintype F₁₁] [Fintype F₀₂] [Fintype F₁₂]
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) (d12_11 : Matrix F₁₁ F₁₂ (ZMod 2))
    (d12_02 : Matrix F₀₂ F₁₂ (ZMod 2))
    (h1 : d11_10 * d12_11 = 0)
    (h2 : d11_01 * d12_11 + d02_01 * d12_02 = 0) :
    fd1 d11_10 d11_01 d02_01 * fd2 d12_11 d12_02 = 0 := by
  have hc1 : fd1 d11_10 d11_01 d02_01
      = Matrix.fromBlocks d11_10 (0 : Matrix F₁₀ F₀₂ (ZMod 2)) d11_01 d02_01 := rfl
  have hc2 : fd2 d12_11 d12_02
      = Matrix.fromBlocks d12_11 (0 : Matrix F₁₁ (Fin 0) (ZMod 2)) d12_02
          (0 : Matrix F₀₂ (Fin 0) (ZMod 2)) := rfl
  have h00 : d11_10 * d12_11 + (0 : Matrix F₁₀ F₀₂ (ZMod 2)) * d12_02 = 0 := by
    rw [Matrix.zero_mul, add_zero]; exact h1
  have h01 : d11_10 * (0 : Matrix F₁₁ (Fin 0) (ZMod 2))
      + (0 : Matrix F₁₀ F₀₂ (ZMod 2)) * (0 : Matrix F₀₂ (Fin 0) (ZMod 2)) = 0 := by
    rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have h10 : d11_01 * d12_11 + d02_01 * d12_02 = 0 := h2
  have h11 : d11_01 * (0 : Matrix F₁₁ (Fin 0) (ZMod 2))
      + d02_01 * (0 : Matrix F₀₂ (Fin 0) (ZMod 2)) = 0 := by
    rw [Matrix.mul_zero, Matrix.mul_zero, add_zero]
  rw [hc1, hc2, Matrix.fromBlocks_multiply, h00, h01, h10, h11]
  exact Matrix.fromBlocks_zero

/-- **Block decomposition of the complex condition (the first composite)**:
$\partial_0\partial_1 = 0$ is given by two **block equations**

$$F_{1,1}\colon\ d_{1,0\to 0,0}\, d_{1,1\to 1,0} + d_{0,1\to 0,0}\, d_{1,1\to 0,1} = 0,
  \qquad F_{0,2}\colon\ d_{0,1\to 0,0}\, d_{0,2\to 0,1} = 0.$$

(As in `fd1_mul_fd2_of`, the sufficient direction is given.) -/
theorem fd0_mul_fd1_of {F₀₀ F₁₀ F₀₁ F₁₁ F₀₂ : Type*}
    [Fintype F₀₀] [Fintype F₁₀] [Fintype F₀₁] [Fintype F₁₁] [Fintype F₀₂]
    (d10_00 : Matrix F₀₀ F₁₀ (ZMod 2)) (d01_00 : Matrix F₀₀ F₀₁ (ZMod 2))
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2))
    (h1 : d10_00 * d11_10 + d01_00 * d11_01 = 0) (h2 : d01_00 * d02_01 = 0) :
    fd0 d10_00 d01_00 * fd1 d11_10 d11_01 d02_01 = 0 := by
  have hc0 : fd0 d10_00 d01_00
      = Matrix.fromBlocks d10_00 d01_00 (0 : Matrix (Fin 0) F₁₀ (ZMod 2))
          (0 : Matrix (Fin 0) F₀₁ (ZMod 2)) := rfl
  have hc1 : fd1 d11_10 d11_01 d02_01
      = Matrix.fromBlocks d11_10 (0 : Matrix F₁₀ F₀₂ (ZMod 2)) d11_01 d02_01 := rfl
  have h00 : d10_00 * d11_10 + d01_00 * d11_01 = 0 := h1
  have h01 : d10_00 * (0 : Matrix F₁₀ F₀₂ (ZMod 2)) + d01_00 * d02_01 = 0 := by
    rw [Matrix.mul_zero, zero_add]; exact h2
  have h10 : (0 : Matrix (Fin 0) F₁₀ (ZMod 2)) * d11_10
      + (0 : Matrix (Fin 0) F₀₁ (ZMod 2)) * d11_01 = 0 := by
    rw [Matrix.zero_mul, Matrix.zero_mul, add_zero]
  have h11 : (0 : Matrix (Fin 0) F₁₀ (ZMod 2)) * (0 : Matrix F₁₀ F₀₂ (ZMod 2))
      + (0 : Matrix (Fin 0) F₀₁ (ZMod 2)) * d02_01 = 0 := by
    rw [Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [hc0, hc1, Matrix.fromBlocks_multiply, h00, h01, h10, h11]
  exact Matrix.fromBlocks_zero

/-- **Assembling a fault complex from the four block equations**: as soon as the four
block equations hold, the assembled four-term complex **is** a complex. This lays out
explicitly the **whole proof obligation** of the sentence "it is a complex". -/
def faultComplexOf {F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂ : Type*}
    [Fintype F₀₀] [Fintype F₀₁] [Fintype F₀₂]
    [Fintype F₁₀] [Fintype F₁₁] [Fintype F₁₂]
    (d12_11 : Matrix F₁₁ F₁₂ (ZMod 2)) (d12_02 : Matrix F₀₂ F₁₂ (ZMod 2))
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) (d10_00 : Matrix F₀₀ F₁₀ (ZMod 2))
    (d01_00 : Matrix F₀₀ F₀₁ (ZMod 2))
    (h1 : d11_10 * d12_11 = 0) (h2 : d11_01 * d12_11 + d02_01 * d12_02 = 0)
    (h3 : d10_00 * d11_10 + d01_00 * d11_01 = 0) (h4 : d01_00 * d02_01 = 0) :
    FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂ where
  d12_11 := d12_11
  d12_02 := d12_02
  d11_10 := d11_10
  d11_01 := d11_01
  d02_01 := d02_01
  d10_00 := d10_00
  d01_00 := d01_00
  comp_d1_d2 := fd1_mul_fd2_of d11_10 d11_01 d02_01 d12_11 d12_02 h1 h2
  comp_d0_d1 := fd0_mul_fd1_of d10_00 d01_00 d11_10 d11_01 d02_01 h3 h4

/-! ## 3. The total complex (Koszul): the CSS condition $\partial_1\partial_2 = 0$ makes
the fault complex a complex -/

variable {R₀ R₁ C₀ C₁ C₂ : Type*}
variable [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂]
variable [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]

/-- The multiplicative law for Kronecker products (the direction of
`Matrix.mul_kronecker_mul` turned into "merge first, split after", with the conversion
between `Matrix.kronecker` and its `kroneckerMap` body written out explicitly). -/
lemma kron_mul {l m n l' m' n' : Type*} [Fintype m] [Fintype m']
    (A : Matrix l m (ZMod 2)) (B : Matrix m n (ZMod 2))
    (A' : Matrix l' m' (ZMod 2)) (B' : Matrix m' n' (ZMod 2)) :
    Matrix.kronecker A A' * Matrix.kronecker B B' = Matrix.kronecker (A * B) (A' * B') := by
  change Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A A'
      * Matrix.kroneckerMap (fun x1 x2 => x1 * x2) B B'
    = Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (A * B) (A' * B')
  exact (Matrix.mul_kronecker_mul A B A' B').symm

/-- A Kronecker product with a zero left factor is zero. -/
lemma kron_zero_left {l m n p : Type*} (B : Matrix n p (ZMod 2)) :
    Matrix.kronecker (0 : Matrix l m (ZMod 2)) B
      = (0 : Matrix (l × n) (m × p) (ZMod 2)) := by
  change Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (0 : Matrix l m (ZMod 2)) B = 0
  exact Matrix.zero_kronecker B

/-- Over GF(2) a matrix added to itself is zero: the shared `add_self_fun` of
`GF2/Basic.lean`, applied to the rows. -/
lemma add_self_matrix {l m : Type*} (M : Matrix l m (ZMod 2)) : M + M = 0 := by
  funext i
  exact add_self_fun (M i)

/-- **The fault complex given by the total-complex (Koszul) differential**: given a
timelike differential $R : \mathcal R_1 \to \mathcal R_0$ (`timeLikeRepR` of
`Codes/TimeLikeInstance.lean` is one value of it) and a code-side CSS complex
$\partial_1 : C_1 \to C_0$, $\partial_2 : C_2 \to C_1$ (**the CSS condition
$\partial_1\partial_2 = 0$ is the only nontrivial input**), the
$(\mathcal R \otimes C)_\bullet$ of [14] p.63 is a fault complex.

The seven blocks are expanded by the Koszul formula
$\partial(x\otimes y) = \partial_{\mathcal R}x \otimes y + x \otimes \partial_C y$ (the
signs are trivial over $\mathbb F_2$); the indices are taken as
$F_{i,j} = C_j \times \mathcal R_i$ (**the code index first** -- this is only the order in
which the tensor factors are written, the same tensor product as the
$\mathcal R_i \otimes C_j$ of [14]).

The origin of the four block equations (the `fd1_mul_fd2_of` / `fd0_mul_fd1_of` of §2):

* $d_{1,1\to 1,0}\, d_{1,2\to 1,1}
  = (\mathrm{id}\otimes\partial_1)(\mathrm{id}\otimes\partial_2)
  = \mathrm{id}\otimes(\partial_1\partial_2) = 0$: **the CSS condition**;
* $d_{1,1\to 0,1}\,d_{1,2\to 1,1} = d_{0,2\to 0,1}\,d_{1,2\to 0,2}
  = \partial_{\mathcal R}\otimes\partial_2$: the two routes are equal, and over
  characteristic $2$ they sum to zero (cancellation of Koszul signs);
* $d_{1,0\to 0,0}\,d_{1,1\to 1,0} = d_{0,1\to 0,0}\,d_{1,1\to 0,1}
  = \partial_{\mathcal R}\otimes\partial_1$: as above;
* $d_{0,1\to 0,0}\,d_{0,2\to 0,1} = \mathrm{id}\otimes(\partial_1\partial_2) = 0$:
  **the CSS condition**. -/
def koszulFaultComplex (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    FaultComplex (C₀ × R₀) (C₁ × R₀) (C₂ × R₀) (C₀ × R₁) (C₁ × R₁) (C₂ × R₁) :=
  faultComplexOf
    (Matrix.kronecker dC2 (1 : Matrix R₁ R₁ (ZMod 2)))
    (Matrix.kronecker (1 : Matrix C₂ C₂ (ZMod 2)) R)
    (Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
    (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R)
    (Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)))
    (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R)
    (Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
    (by rw [kron_mul, hC, Matrix.mul_one, kron_zero_left])
    (by rw [kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul,
          add_self_matrix])
    (by rw [kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul,
          add_self_matrix])
    (by rw [kron_mul, hC, Matrix.mul_one, kron_zero_left])

/-- **$(\mathcal R \otimes C)_\bullet$ is a complex**: the two complex conditions of
`koszulFaultComplex` read off verbatim -- the two fields of the `FaultComplex` structure
just are "it is a complex". -/
theorem koszul_is_complex (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (fd1 (koszulFaultComplex R dC1 dC2 hC).d11_10 (koszulFaultComplex R dC1 dC2 hC).d11_01
        (koszulFaultComplex R dC1 dC2 hC).d02_01
      * fd2 (koszulFaultComplex R dC1 dC2 hC).d12_11
          (koszulFaultComplex R dC1 dC2 hC).d12_02 = 0)
    ∧ (fd0 (koszulFaultComplex R dC1 dC2 hC).d10_00 (koszulFaultComplex R dC1 dC2 hC).d01_00
      * fd1 (koszulFaultComplex R dC1 dC2 hC).d11_10 (koszulFaultComplex R dC1 dC2 hC).d11_01
        (koszulFaultComplex R dC1 dC2 hC).d02_01 = 0) :=
  ⟨(koszulFaultComplex R dC1 dC2 hC).comp_d1_d2,
    (koszulFaultComplex R dC1 dC2 hC).comp_d0_d1⟩

/-- The block $F_{1,2}\to F_{1,1}$ is $\mathrm{id} \otimes \partial_2$ (definitional
unfolding). -/
theorem koszulFaultComplex_d12_11 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d12_11
      = Matrix.kronecker dC2 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl

/-- The block $F_{1,2}\to F_{0,2}$ is $\partial_{\mathcal R} \otimes \mathrm{id}$. -/
theorem koszulFaultComplex_d12_02 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d12_02
      = Matrix.kronecker (1 : Matrix C₂ C₂ (ZMod 2)) R := rfl

/-- The block $F_{1,0}\to F_{1,1}$ is $\mathrm{id} \otimes \partial_1$. -/
theorem koszulFaultComplex_d11_10 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d11_10
      = Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl

/-- **The diagonal block** ($F_{1,1} \to F_{0,1}$): $\partial_{\mathcal R} \otimes
\mathrm{id}$. -/
theorem koszulFaultComplex_d11_01 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d11_01
      = Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R := rfl

/-- The block $F_{0,2} \to F_{0,1}$ is $\mathrm{id} \otimes \partial_2$. -/
theorem koszulFaultComplex_d02_01 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d02_01
      = Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl

/-- The block $F_{1,0} \to F_{0,0}$ is $\partial_{\mathcal R} \otimes \mathrm{id}$. -/
theorem koszulFaultComplex_d10_00 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d10_00
      = Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R := rfl

/-- The block $F_{0,1} \to F_{0,0}$ is $\mathrm{id} \otimes \partial_1$. -/
theorem koszulFaultComplex_d01_00 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    (koszulFaultComplex R dC1 dC2 hC).d01_00
      = Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl

/-! ## 4. Instance one: a timelike detector code ($m = 3$ checks, $T = 4$ rounds)

On the code side take the **trivial complex** ($C_0 = C_2 = 0$,
$C_1 = \mathbb F_2^3$: three "check" sites and no check operators); on the timelike side
take the check matrix `timeLikeRepR` of the $l = 4$ repetition code. Then the four terms
of $(\mathcal R \otimes C)_\bullet$ are $F_3 = 0$, $F_2 = \mathbb F_2^{12}$,
$F_1 = \mathbb F_2^{9}$, $F_0 = 0$, and the only nontrivial differential is the diagonal
block $s = 1 \otimes R$ -- **it is the `timeLike34H` of
`Codes/TimeLikeInstance.lean`** ($9 \times 12$); see `timeLikeFaultComplex_d11_01` and
`timeLike34H_eq_reindex`.

**Note that the target of the block is not a detector**: the side with $9$ entries is
$F_{0,1} = C_1 \times \mathcal R_0$ ([14] p.62: $Z$ Pauli fault locations), not $F_0$.
The timelike component reads the **kernel** -- $\ker\partial_1$ is exactly the family of
vectors "some check wrong throughout $T$ consecutive rounds" ($H^2$); see the two reading
theorems below. -/

/-- The timelike differential $R$: the **check matrix** of the $l = 4$ repetition code
($3$ adjacent-round checks), i.e. "the full-rank parity-check matrix for the repetition
code" of [14] p.63 (the former case, $|0\rangle$ preparation / $Z$-basis measurement). -/
def timeLikeRepR : Matrix (Fin 3) (Fin 4) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 2 + e 3]

/-- **`timeLike34H` is the 4-round repetition-code check matrix of each of the 3
checks**: it agrees entrywise under the relabellings
`finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9` (rows: `(check, adjacent round)`) and
`finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin 12` (columns: `(check, round)`). -/
theorem timeLike34H_eq_reindex :
    timeLike34H
      = (Matrix.kronecker (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) timeLikeRepR).reindex
          finProdFinEquiv finProdFinEquiv := by
  decide

/-- **The fault complex of the timelike instance** (the
$(\mathcal R \otimes C)_\bullet$ of [14] p.63, with a trivial code side and the
$l = 4$ repetition code on the timelike side). -/
def timeLikeFaultComplex : FaultComplex (Fin 0 × Fin 3) (Fin 3 × Fin 3) (Fin 0 × Fin 3)
    (Fin 0 × Fin 4) (Fin 3 × Fin 4) (Fin 0 × Fin 4) :=
  koszulFaultComplex timeLikeRepR 0 0 (by simp)

/-- **The diagonal block is `timeLike34H`**: the $F_{1,1} \to F_{0,1}$ block of
$(\mathcal R \otimes C)$ is $= 1 \otimes R$; with `timeLike34H_eq_reindex`, the
$9 \times 12$ matrix of `Codes/TimeLikeInstance.lean` is this one differential block of
the fault complex. -/
theorem timeLikeFaultComplex_d11_01 :
    timeLikeFaultComplex.d11_01
      = Matrix.kronecker (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) timeLikeRepR := rfl

/-- **Both ends of the timelike instance are degenerate**: the two blocks of $\partial_2$
and the two blocks of $\partial_0$ are all zero ($F_3 = F_0 = 0$; this piece keeps only
"faults in the time direction" and has no detectors).

So the two complex conditions are **vacuous** here -- which both explains why the homology
reading below connects straight to `timeLike34_d` and shows that this instance **cannot**
be used to exhibit "the CSS condition implies a complex" (that one is on the Shor
instance of §5). -/
theorem timeLikeFaultComplex_degenerate :
    timeLikeFaultComplex.d12_11 = 0 ∧ timeLikeFaultComplex.d12_02 = 0
      ∧ timeLikeFaultComplex.d10_00 = 0 ∧ timeLikeFaultComplex.d01_00 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Homology reading (dimension)**: $\ker\partial_1$ has dimension $3$ -- each of the
three checks has one free direction "wrong throughout four consecutive rounds". (Here
$H^2 = \ker\partial_1/\mathrm{im}\,\partial_2$ and $\mathrm{im}\,\partial_2 = 0$ (the
previous item), so what is computed here is the dimension of $H^2$; the next item gives
its minimum-weight reading.) -/
theorem timeLikeFaultComplex_cycles_finrank :
    Module.finrank (ZMod 2) ↥(LinearMap.ker timeLike34H.mulVecLin) = 3 := by
  have hrank : timeLike34H.rank = 9 := by
    rw [Matrix.rank_eq_length_rowReduce]
    decide
  have hrn := LinearMap.finrank_range_add_finrank_ker timeLike34H.mulVecLin
  have hrange : Module.finrank (ZMod 2) ↥(LinearMap.range timeLike34H.mulVecLin) = 9 := hrank
  have hdim : Module.finrank (ZMod 2) (Fin 12 → ZMod 2) = 12 := by simp
  omega

/-- **Homology reading (minimum weight), cross-checked against the existing distance
conclusion**: the least weight of a nonzero element of $H^2$ of the timelike fault complex
is exactly $4 = T$ (the number of rounds) -- this **is** the number computed by
`timeLike34_d` of `Codes/TimeLikeInstance.lean`: for this instance both ends are
degenerate (`timeLikeFaultComplex_degenerate`), so
$H^2 = \ker\partial_1 \setminus \{0\}$, and `timeLike34_d` computes exactly
`min_weight_ker_not_mem_rowspace timeLike34H (zeroRows 12)` (the row space of `zeroRows`
is $\bot$, so that set is "the nonzero vectors in the kernel"). This theorem takes it over
unchanged; its purpose is to **point out that the two readings coincide on this instance**,
adding no computation. -/
theorem timeLikeFaultComplex_minWeight :
    min_weight_ker_not_mem_rowspace timeLike34H (zeroRows 12) = 4 := timeLike34_d

/-! ## 5. Instance two: the foliated fault complex of the Shor code $[[9,1,3]]$
(**non-degenerate**)

On the code side take the CSS complex of the Shor code ($C_2 = \mathbb F_2^6$ $Z$ checks,
$C_1 = \mathbb F_2^9$ data qubits, $C_0 = \mathbb F_2^2$ $X$ checks); on the timelike side
again the $l = 4$ repetition code. The four terms therefore **are nonzero at both ends**:
$F_3 = 24$, $F_2 = 36 + 18 = 54$, $F_1 = 8 + 27 = 35$, $F_0 = 6$. The four block
equations are re-checked independently by `by decide` on the **explicit matrices**
(without reusing the general proof of §3). -/

/-- The code-side differential $\partial_1 : C_1 \to C_0$ (data qubits $\to$ $X$ checks). -/
def shorD1 : Matrix (Fin 2) (Fin 9) (ZMod 2) := shorHx

/-- The code-side differential $\partial_2 : C_2 \to C_1$ ($Z$ checks $\to$ the data
qubits in their support). -/
def shorD2 : Matrix (Fin 9) (Fin 6) (ZMod 2) := shorHz.transpose

/-- **The CSS condition of the Shor code** $\partial_1\partial_2 = 0$ (that is,
$H_X H_Z^{\mathsf T} = 0$): the only input the general theorem of §3 needs, re-checked
independently on this instance. -/
theorem shorD1_mul_shorD2 : shorD1 * shorD2 = 0 := by decide

/-- **The fault complex of the Shor instance** (non-degenerate: nonzero at both ends). -/
def shorFaultComplex : FaultComplex
    (Fin 2 × Fin 3) (Fin 9 × Fin 3) (Fin 6 × Fin 3) (Fin 2 × Fin 4) (Fin 9 × Fin 4)
    (Fin 6 × Fin 4) :=
  koszulFaultComplex timeLikeRepR shorD1 shorD2 shorD1_mul_shorD2

/-- **The dimensions of the four terms** ($F_3 = 24$, $F_2 = 54$, $F_1 = 35$, $F_0 = 6$). -/
theorem shorFaultComplex_term_dims :
    Fintype.card (FaultTerm3 (Fin 6 × Fin 4)) = 24
      ∧ Fintype.card (FaultTerm2 (Fin 9 × Fin 4) (Fin 6 × Fin 3)) = 54
      ∧ Fintype.card (FaultTerm1 (Fin 2 × Fin 4) (Fin 9 × Fin 3)) = 35
      ∧ Fintype.card (FaultTerm0 (Fin 2 × Fin 3)) = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [FaultTerm3, FaultTerm2, FaultTerm1, FaultTerm0]

/-- **The seven blocks are explicit matrices**: each block is the Kronecker product of
two **explicit small matrices** ($\partial_1$ = `shorHx`, $\partial_2$ = `shorHzᵀ`,
$\partial_{\mathcal R}$ = `timeLikeRepR`). -/
theorem shorFaultComplex_blocks :
    shorFaultComplex.d12_11 = Matrix.kronecker shorD2 (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
      ∧ shorFaultComplex.d12_02
          = Matrix.kronecker (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) timeLikeRepR
      ∧ shorFaultComplex.d11_10 = Matrix.kronecker shorD1 (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
      ∧ shorFaultComplex.d11_01
          = Matrix.kronecker (1 : Matrix (Fin 9) (Fin 9) (ZMod 2)) timeLikeRepR
      ∧ shorFaultComplex.d02_01 = Matrix.kronecker shorD2 (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))
      ∧ shorFaultComplex.d10_00
          = Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) timeLikeRepR
      ∧ shorFaultComplex.d01_00 = Matrix.kronecker shorD1 (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The four block equations hold independently on the explicit matrices** (`by
decide`, without going through the general proof of §3).

These four are exactly the "whole proof obligation of the complex condition" laid out in
§2: the first two give $\partial_1\partial_2 = 0$, the last two give
$\partial_0\partial_1 = 0$. Of these, $d_{1,1\to 1,0}d_{1,2\to 1,1} = 0$ and
$d_{0,1\to 0,0}d_{0,2\to 0,1} = 0$ **are** the CSS condition of the Shor code; the other
two are the Koszul two-route cancellation (characteristic $2$). -/
theorem shorFaultComplex_block_equations :
    (shorFaultComplex.d11_10 * shorFaultComplex.d12_11 = 0)
      ∧ (shorFaultComplex.d11_01 * shorFaultComplex.d12_11
          + shorFaultComplex.d02_01 * shorFaultComplex.d12_02 = 0)
      ∧ (shorFaultComplex.d10_00 * shorFaultComplex.d11_10
          + shorFaultComplex.d01_00 * shorFaultComplex.d11_01 = 0)
      ∧ (shorFaultComplex.d01_00 * shorFaultComplex.d02_01 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## 6. Relation to the mapping cone: `FaultComplex` is a `Cochain4` -/

/-- **Packing a fault complex as a `Cochain4` of `Homology/MappingCone.lean`**: reordering
the terms as $(F_3, F_2, F_1, F_0)$ gives the cochain complex
$(C_0,C_1,C_2,C_3) = (F_3,F_2,F_1,F_0)$ with differentials $d^C_0 = \partial_2$,
$d^C_1 = \partial_1$, $d^C_2 = \partial_0$.

The cone, the short exact sequence, the connecting homomorphism and the dimension
identities of `Homology/MappingCone.lean` are then available directly for **any** fault
complex (both sides of a `CochainMap` can be filled with fault complexes).
**A.1 does not print the map that is coned** (see §4 item 2 of the module header), so
this module does not state "some fault complex = the cone of the idling fault complex". -/
def FaultComplex.toCochain4 (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) :
    Cochain4 (FaultTerm3 F₁₂) (FaultTerm2 F₁₁ F₀₂) (FaultTerm1 F₁₀ F₀₁) (FaultTerm0 F₀₀) where
  d0 := fd2 F.d12_11 F.d12_02
  d1 := fd1 F.d11_10 F.d11_01 F.d02_01
  d2 := fd0 F.d10_00 F.d01_00
  comp_d1_d0 := F.comp_d1_d2
  comp_d2_d1 := F.comp_d0_d1

/-! ## 3, continued: **fix one check and take the parity along the time axis**
(the machine form of the weight-preservation mechanism of [56] Theorem 5)

In the proof of Theorem 5 of [56] (Williamson–Yoder, *Low-overhead fault-tolerant quantum
computation by gauging logical operators*, arXiv:2410.02213), the weight-preservation
mechanism has a verbatim sentence:

> Undoing the spacetime stabilizer equivalence that cleaned the spacetime logical into a
> spacelike logical **cannot reduce the distance** … This is because each such stabilizer
> **preserves the parity of the space and initialization faults along the timeline at a fixed
> position**.

The theorems of this section are the form of that sentence on the Koszul fault complex.
**Fix one code-side check `r` and one pair of adjacent rounds `i`**; the functional

$$\varphi_{r,i}(x)=\sum_{t\,:\,R_i^t=1}x_{1,0}(r,t)+\sum_{c\,:\,dC_1(r,c)=1}x_{0,1}(c,i)$$

takes its left term on $F_{1,0}=C_0\times R_1$ and its right term on
$F_{0,1}=C_1\times R_0$ -- **the two time axes are offset by one**. The theorem says that
$\varphi_{r,i}$ is **identically zero** on $\mathrm{im}\,\partial_1$.

**The proof uses only two things**: the Koszul two-route cancellation (the same double sum
appears twice and sums to zero over characteristic $2$), and the code-side **CSS
condition** $dC_1dC_2=0$. So the parity conservation "along the time axis, at a fixed
position" **is a consequence of the complex condition itself**, not an extra hypothesis --
which is precisely why the weight-preservation argument of [56] can be machine-checked.

**How it is written**: the three blocks are **written out in `Matrix.of` form** (explicit
`if`s on `x.1`/`x.2`), without invoking the `kron` alias -- the entrywise lemmas for
`kron` only fire when `Matrix.kronecker` is visible in the goal, and unfolding a
semireducible definition triggers "target expression is not type-correct under implicit
transparency". The equivalence of the two `kron` blocks is recorded separately as
`koszulBlock_*_eq_kronecker`. -/

/-- The $F_{1,0}\leftarrow F_{1,1}$ block (the explicit spelling of
$=dC_1\otimes\mathrm{id}$). -/
theorem koszulBlock11_eq_kronecker {C₀ C₁ R₁ : Type*} [DecidableEq R₁]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    (Matrix.of fun (x : C₀ × R₁) (y : C₁ × R₁) =>
        dC1 x.1 y.1 * (if x.2 = y.2 then (1 : ZMod 2) else 0))
      = Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)) := by
  ext x y
  rfl

/-- The $F_{0,1}\leftarrow F_{1,1}$ block (the explicit spelling of
$=\mathrm{id}\otimes R$). -/
theorem koszulBlock01_eq_kronecker {C₁ R₀ R₁ : Type*} [DecidableEq C₁]
    (R : Matrix R₀ R₁ (ZMod 2)) :
    (Matrix.of fun (x : C₁ × R₀) (y : C₁ × R₁) =>
        (if x.1 = y.1 then (1 : ZMod 2) else 0) * R x.2 y.2)
      = Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R := by
  ext x y
  rfl

/-- The $F_{0,1}\leftarrow F_{0,2}$ block (the explicit spelling of
$=dC_2\otimes\mathrm{id}$). -/
theorem koszulBlock02_eq_kronecker {C₁ C₂ R₀ : Type*} [DecidableEq R₀]
    (dC2 : Matrix C₁ C₂ (ZMod 2)) :
    (Matrix.of fun (x : C₁ × R₀) (y : C₂ × R₀) =>
        dC2 x.1 y.1 * (if x.2 = y.2 then (1 : ZMod 2) else 0))
      = Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)) := by
  ext x y
  rfl

/-! **Remark**: the three items above match the `Matrix.of` spelling of the three blocks
with the `kron` spelling. -/

/-! ## 3, continued, part two: the conservation theorem

The three blocks are written as `Matrix.of` (without the `kron` alias, for the reason
above), and $\partial_1$ is assembled by `fd1`: **fix one code-side check `r` and one pair
of adjacent rounds `i`; the functional is identically zero on
$\mathrm{im}\,\partial_1$** (`conserved_parity`).

The proof has three parts: **the same double sum appears twice** (the first and second
parts both reduce to the same normal form and sum to zero over characteristic $2$), and
the third part is killed by the **CSS condition** $dC_1dC_2=0$. **Two sum rearrangements
are used**: `Finset.mul_sum` to push a scalar into a sum, `Finset.sum_comm` to swap the
order, and `Finset.sum_eq_single` with an `if` on the index to collapse the sum to a
single term. -/

/-- Over $\mathbb Z_2$ the indicator spelling and the multiplication spelling agree. -/
lemma zmod2_ind (a v : ZMod 2) : (if a = 1 then v else 0) = a * v := by
  split_ifs with h
  · rw [h, one_mul]
  · have h0 : a = 0 := by
      fin_cases a
      · rfl
      · exact absurd rfl h
    rw [h0, zero_mul]

/-- The block $F_{1,1}\to F_{1,0}$: $dC_1\otimes\mathrm{id}$. -/
def parBlock11 {C₀ C₁ R₁ : Type*} [DecidableEq R₁] (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    Matrix (C₀ × R₁) (C₁ × R₁) (ZMod 2) :=
  Matrix.of fun x y => dC1 x.1 y.1 * (if x.2 = y.2 then (1 : ZMod 2) else 0)

/-- The block $F_{1,1}\to F_{0,1}$ (the diagonal arrow in the diagram):
$\mathrm{id}\otimes R$. -/
def parBlock01 {C₁ R₀ R₁ : Type*} [DecidableEq C₁] (Rm : Matrix R₀ R₁ (ZMod 2)) :
    Matrix (C₁ × R₀) (C₁ × R₁) (ZMod 2) :=
  Matrix.of fun x y => (if x.1 = y.1 then (1 : ZMod 2) else 0) * Rm x.2 y.2

/-- The block $F_{0,2}\to F_{0,1}$: $dC_2\otimes\mathrm{id}$. -/
def parBlock02 {C₁ C₂ R₀ : Type*} [DecidableEq R₀] (dC2 : Matrix C₁ C₂ (ZMod 2)) :
    Matrix (C₁ × R₀) (C₂ × R₀) (ZMod 2) :=
  Matrix.of fun x y => dC2 x.1 y.1 * (if x.2 = y.2 then (1 : ZMod 2) else 0)

variable {C₀ C₁ C₂ R₀ R₁ : Type*}
variable [Fintype C₀] [Fintype C₁] [Fintype C₂] [Fintype R₀] [Fintype R₁]
variable [DecidableEq C₁] [DecidableEq R₀] [DecidableEq R₁]

/-- The coordinatewise reading of $\partial_1$ in the $F_{1,0}$ row. -/
lemma fd1_par_apply_inl (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (Rm : Matrix R₀ R₁ (ZMod 2)) (y11 : C₁ × R₁ → ZMod 2) (y02 : C₂ × R₀ → ZMod 2)
    (r : C₀) (t : R₁) :
    ((fd1 (parBlock11 dC1) (parBlock01 Rm) (parBlock02 dC2)) *ᵥ
        (Sum.elim y11 y02)) (Sum.inl (r, t))
      = ∑ y : C₁ × R₁, dC1 r y.1 * (if t = y.2 then (1 : ZMod 2) else 0) * y11 y := by
  simp only [fd1, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Sum.elim_inl]
  exact Finset.sum_congr rfl fun y _ => by
    rw [parBlock11, Matrix.of_apply]

/-- The coordinatewise reading of $\partial_1$ in the $F_{0,1}$ row (the sum of the two
blocks). -/
lemma fd1_par_apply_inr (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (Rm : Matrix R₀ R₁ (ZMod 2)) (y11 : C₁ × R₁ → ZMod 2) (y02 : C₂ × R₀ → ZMod 2)
    (c : C₁) (i : R₀) :
    ((fd1 (parBlock11 dC1) (parBlock01 Rm) (parBlock02 dC2)) *ᵥ
        (Sum.elim y11 y02)) (Sum.inr (c, i))
      = (∑ y : C₁ × R₁, (if c = y.1 then (1 : ZMod 2) else 0) * Rm i y.2 * y11 y)
        + (∑ z : C₂ × R₀, dC2 c z.1 * (if i = z.2 then (1 : ZMod 2) else 0) * y02 z) := by
  simp only [fd1, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, parBlock01, parBlock02, Matrix.of_apply]

/-- **The conservation theorem**: fix one code-side check $r$ and one pair of adjacent
rounds $i$; the functional is identically zero on $\mathrm{im}\,\partial_1$ -- only the
CSS condition $dC_1dC_2=0$ is needed. -/
theorem conserved_parity (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (Rm : Matrix R₀ R₁ (ZMod 2)) (hCSS : dC1 * dC2 = 0) (r : C₀) (i : R₀)
    (y11 : C₁ × R₁ → ZMod 2) (y02 : C₂ × R₀ → ZMod 2) :
    (∑ t : R₁, (if Rm i t = 1 then
        ((fd1 (parBlock11 dC1) (parBlock01 Rm) (parBlock02 dC2)) *ᵥ
          (Sum.elim y11 y02)) (Sum.inl (r, t)) else 0))
      + (∑ c : C₁, (if dC1 r c = 1 then
        ((fd1 (parBlock11 dC1) (parBlock01 Rm) (parBlock02 dC2)) *ᵥ
          (Sum.elim y11 y02)) (Sum.inr (c, i)) else 0)) = 0 := by
  have hsum1 : (∑ t : R₁, (if Rm i t = 1 then
        ((fd1 (parBlock11 dC1) (parBlock01 Rm) (parBlock02 dC2)) *ᵥ
          (Sum.elim y11 y02)) (Sum.inl (r, t)) else 0))
      = ∑ t : R₁, Rm i t *
          ∑ y : C₁ × R₁, dC1 r y.1 * (if t = y.2 then (1 : ZMod 2) else 0) * y11 y :=
    Finset.sum_congr rfl fun t _ => by rw [zmod2_ind, fd1_par_apply_inl]
  have hsum2 : (∑ c : C₁, (if dC1 r c = 1 then
        ((fd1 (parBlock11 dC1) (parBlock01 Rm) (parBlock02 dC2)) *ᵥ
          (Sum.elim y11 y02)) (Sum.inr (c, i)) else 0))
      = ∑ c : C₁, dC1 r c *
          ((∑ y : C₁ × R₁, (if c = y.1 then (1 : ZMod 2) else 0) * Rm i y.2 * y11 y)
            + (∑ z : C₂ × R₀,
                dC2 c z.1 * (if i = z.2 then (1 : ZMod 2) else 0) * y02 z)) :=
    Finset.sum_congr rfl fun c _ => by rw [zmod2_ind, fd1_par_apply_inr]
  rw [hsum1, hsum2]
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ t : R₁, Rm i t *
        ∑ y : C₁ × R₁, dC1 r y.1 * (if t = y.2 then (1 : ZMod 2) else 0) * y11 y)
      = ∑ y : C₁ × R₁, dC1 r y.1 * Rm i y.2 * y11 y := by
    rw [Finset.sum_congr rfl (fun t _ => Finset.mul_sum ..)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => by
      rw [Finset.sum_eq_single y.2]
      · simp only [ite_true, mul_one]
        ring
      · intro t _ ht
        simp [ht]
      · intro h
        exact absurd (Finset.mem_univ y.2) h
  have h2 : (∑ c : C₁, dC1 r c *
        ∑ y : C₁ × R₁, (if c = y.1 then (1 : ZMod 2) else 0) * Rm i y.2 * y11 y)
      = ∑ y : C₁ × R₁, dC1 r y.1 * Rm i y.2 * y11 y := by
    rw [Finset.sum_congr rfl (fun c _ => Finset.mul_sum ..)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => by
      rw [Finset.sum_eq_single y.1]
      · simp only [ite_true]
        ring
      · intro c _ hc
        simp [hc]
      · intro h
        exact absurd (Finset.mem_univ y.1) h
  have h3 : (∑ c : C₁, dC1 r c *
        ∑ z : C₂ × R₀, dC2 c z.1 * (if i = z.2 then (1 : ZMod 2) else 0) * y02 z) = 0 := by
    rw [Finset.sum_congr rfl (fun c _ => Finset.mul_sum ..)]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hcs : ∑ c : C₁, dC1 r c * dC2 c z.1 = 0 := by
      simpa [Matrix.mul_apply] using congrFun (congrFun hCSS r) z.1
    calc ∑ c : C₁, dC1 r c * (dC2 c z.1 * (if i = z.2 then (1 : ZMod 2) else 0) * y02 z)
        = ∑ c : C₁, (dC1 r c * dC2 c z.1) *
            ((if i = z.2 then (1 : ZMod 2) else 0) * y02 z) :=
          Finset.sum_congr rfl fun c _ => by ring
      _ = (∑ c : C₁, dC1 r c * dC2 c z.1) *
            ((if i = z.2 then (1 : ZMod 2) else 0) * y02 z) := by rw [Finset.sum_mul]
      _ = 0 := by rw [hcs, zero_mul]
  rw [h1, h2, h3, add_zero]
  exact CharTwo.add_self_eq_zero _

end QECCertificates.Homology
