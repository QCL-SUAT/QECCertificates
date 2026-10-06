/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.Duality
import QECCertificates.Homology.FaultComplex
import QECCertificates.Homology.MappingConeSnake

open QECCertificates

/-!
# [14] p.63 Künneth (foliated CSS): verbatim reading, hypotheses, the checked half

## 1. The source (verbatim, page numbers as printed in the PDF)

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895 (the `refs/` corpus
as in the module header of `Homology/FaultComplex.lean`).

**p.63** (§A.1, foliated CSS case; the only source of this module):

> The standard way to foliate a CSS code $C_\bullet$ from the fault complex perspective is to
> take $(\mathcal R \otimes C)_\bullet$, where $\mathcal R_\bullet : \mathcal R_1 \to
> \mathcal R_0$ has the differential $R$ being either the full-rank parity-check matrix for
> the repetition code or its dual. […]
>
> If we do this, the fault complex has the explicit form:
>
> $$\mathcal R_1 \otimes C_2 \longrightarrow \mathcal R_1 \otimes C_1 \oplus
>   \mathcal R_0 \otimes C_2 \longrightarrow \mathcal R_1 \otimes C_0 \oplus
>   \mathcal R_0 \otimes C_1 \longrightarrow \mathcal R_0 \otimes C_0 \qquad (5)$$
>
> […]
>
> It is easy to compute the homologies using the Künneth formula. Then elements of $H_1(F)$
> correspond to equivalence classes of logical $\overline Z$ faults in spacetime, composed of
> $Z$ Pauli errors and $X$ check errors, and elements of $H^2(F)$ to logical $\overline X$
> faults, composed of $X$ Pauli errors and $Z$ check errors.¹⁶
>
> For completeness, we have,
>
> * $H_1(\mathcal R \otimes C) = H_1(\mathcal R) \otimes H_0(C) \oplus
>   H_0(\mathcal R) \otimes H_1(C)$.
> * $H_2(\mathcal R \otimes C) = H_1(\mathcal R) \otimes H_1(C) \oplus
>   H_0(\mathcal R) \otimes H_2(C)$.
>
> When $\mathcal R_\bullet$ is the repetition code, we have
>
> $$H_1(\mathcal R \otimes C) = H_1(\mathcal R) \otimes H_0(C) = \{0, \mathbf 1\} \otimes
>   C_0/\mathrm{im}H_X$$
> $$H_2(\mathcal R \otimes C) = H_1(\mathcal R) \otimes H_1(C) = \{0, (1, 0, 0, \ldots, 0)\}
>   \otimes H_1(C),$$
>
> where $\mathbf 0$ and $\mathbf 1$ are the all-zero and all-one vectors […]. When
> $\mathcal R_\bullet$ is dual to the repetition code we instead have
>
> $$H_1(\mathcal R \otimes C) = H_0(\mathcal R) \otimes H_1(C) = \{0, (1, 0, 0, \ldots, 0)\}
>   \otimes H_1(C)$$
> $$H_2(\mathcal R \otimes C) = H_0(\mathcal R) \otimes H_2(C) = \{0, \mathbf 1\} \otimes
>   H_2(C).$$

**p.60** (the introduction to the same appendix, Künneth's "same-page sibling", the Snake
dimension formula, already machine-checked by `Homology/MappingConeSnake.lean`):

> The Snake Lemma [90, Lem. 1.3.2] and rank-nullity together imply that for a mapping cone
> $\mathrm{cone}(f^\bullet)$ defined by a chain map $f^\bullet : A^\bullet \to C^\bullet$,
> we have $|H_i(\mathrm{cone}(f^\bullet))| = |H_i(C^\bullet)| + |H_{i-1}(A^\bullet)|
> - |\mathrm{im}\,H_i(f^\bullet)| - |\mathrm{im}\,H_{i-1}(f^\bullet)|$, where $|V|$ is
> shorthand for $\dim V$ when $V$ is a vector space.

## 1 (continued). The same formula is also the machine form of the [56] decoupling lemma

[14] §3.1 refers its fault-distance conclusion to **[56]** (Williamson–Yoder, the copy in
this repository's `refs/`, `williamson2026gauging` in `refs.bib`), and the proof of the
spacetime fault-distance theorem of [56] (**numbered Theorem 5 in arXiv v2**, whose
supplementary material numbers the same statement Supplementary Theorem 1) **has three
steps**, of which the second is **Lemma 7 (Decoupling of space and time faults)**:

> Any spacetime logical fault **is equivalent to the product of a space logical fault and a
> time logical fault**, up to multiplication with spacetime stabilizers.

By p.63's own correspondence ($H_1(F)$ = equivalence classes of logical $\overline Z$
faults), this sentence is the decomposition of $H_1(\mathcal R\otimes C)$, and
**`kunneth_H1` of this module is exactly its dimension half**:
$\dim H_1 = \dim\ker R\cdot h_0(C) + \mathrm{coker}R\cdot h_1(C)$, where the $\ker R$
term is the **time direction** and the $\mathrm{coker}R$ term the **space direction**,
each tensored with one logical space of $C$.

**Honest qualification (not to be omitted)**: this module gives a **dimension equality**,
whereas Lemma 7 is an **element-level** statement; dimension equality is the **counting**
half of decoupling, and **the element-level decomposition is not in the library**.
The machine forms of the other two of [56]'s three steps are also not in this module:
step 1 is the timelike bookkeeping (`padded_timelike_ge` of
`the gauged-measurement companion development's `SurgerySchedule` module` and `timeFault_const` of `Homology/FaultComplex.lean`),
step 3 is weight preservation (`conserved_parity` of the same module). The reconciliation
with [56] is recorded item by item in the statements of the sections.

## 2. Verbatim reading of the formula and its hypotheses (this module's basis)

**Shape of the formula**: the two statements of p.63 are homology formulas for the
**tensor-product complex (total complex)**, whose degrees correspond one-to-one with the
four terms of Eq. (5): $T_3 = \mathcal R_1\otimes C_2$,
$T_2 = \mathcal R_1\otimes C_1\oplus \mathcal R_0\otimes C_2$,
$T_1 = \mathcal R_1\otimes C_0\oplus\mathcal R_0\otimes C_1$,
$T_0 = \mathcal R_0\otimes C_0$, with the Koszul differential
$\partial(x\otimes y) = \partial_{\mathcal R}x\otimes y + x\otimes\partial_C y$
(`koszulFaultComplex` of §3 of `Homology/FaultComplex.lean` is exactly its seven-block
form, and it has been machine-checked to be a complex).

**Hypotheses needed for it to hold (three read verbatim plus two implicit ones)**:

1. **Coefficient field**: $\mathbb F_2$ is a **field**, so the Künneth formula **has no Tor
   term** and is an isomorphism rather than a spectral sequence.
   This is the only reason p.63's formula is an **equality** (rather than "degenerating to
   the $E^2$ page"); this library works over `ZMod 2` throughout.
2. **Lengths of the complexes**: $\mathcal R_\bullet$ is **2-term**
   ($\mathcal R_1\to\mathcal R_0$, so $H_m(\mathcal R) = 0$ for $m\ge 2$), and
   $C_\bullet$ is **3-term** ($C_2\to C_1\to C_0$).
   Hence the general shape of Künneth
   $H_n(\mathcal R\otimes C) = \bigoplus_{i+j=n} H_i(\mathcal R)\otimes H_j(C)$
   **degenerates exactly** at $n = 1, 2$ to the two lines printed by p.63:
   * $H_1$: the terms with $i+j=1$ are $(1,0)$ and $(0,1)$, which is the first line;
   * $H_2$: the terms with $i+j=2$ are $(1,1)$, $(0,2)$ and $(2,0)$, and since
     $H_2(\mathcal R) = 0$ (a 2-term complex), only $(1,1)$ and $(0,2)$ remain, which is
     the second line.
   It also gives the other two lines p.63 does **not** print:
   $H_0 = H_0(\mathcal R)\otimes H_0(C)$ and $H_3 = H_1(\mathcal R)\otimes H_2(C)$.
   This module states all four and marks which two are printed.
3. **Reading of the total complex**: the four terms of Eq. (5) are the direct sum graded by
   "total degree" (footnote 15 of the source: "This is essentially passing to the 'total
   complex'"), and `koszulFaultComplex` of this library uses exactly this differential
   (see the module header of §3 of `Homology/FaultComplex.lean`).

**The two implicit hypotheses (the focus of this module's machine checking)**: the two
"for completeness" bullets of p.63 are a **specialisation**: "When $\mathcal R_\bullet$ is
the repetition code, we have $H_1(\mathcal R\otimes C) = H_1(\mathcal R)\otimes H_0(C)$",
i.e. it **drops the whole term** $H_0(\mathcal R)\otimes H_1(C)$ of the general formula;
the dual case likewise drops $H_1(\mathcal R)\otimes H_2(C)$. The legitimacy of the drop
comes from:

* **repetition code**: $R$ is the **full-rank parity-check matrix** ($l-1$ rows, $l$
  columns, full row rank) → $R$ is **surjective** → $\mathrm{coker}R = 0$ →
  $H_0(\mathcal R) = 0$;
* **its dual**: $R$ is the **transpose** ($l$ rows, $l-1$ columns, full column rank) →
  $R$ is **injective** → $\ker R = 0$ → $H_1(\mathcal R) = 0$.

Both are machine-checked in this module (§2), **for any number of rounds** (§2.2:
surjectivity `repR_surjective`, dual injectivity `repR_transpose_injective`, whose
consumers give $H_0(\mathcal R) = 0$ and the dual-side $H_1 = 0$), and the source's own
instance is `timeLikeRepR` of `Homology/FaultComplex.lean` (the $3\times 4$ parity-check
matrix of the $l = 4$ round repetition code, i.e. §2.2 with $l = 3$, see
`timeLikeRepR_eq_repR`): $H_0 = 0$, $H_1 = \{0,\mathbf 1\}$ ($\dim H_1 = 1$ and the
all-ones vector lies in the kernel; the general-$\ell$ version is `repR_twoTermH1` and
`repR_ker_eq_span_allOnes`), which is exactly the $\{0,\mathbf 1\}$ printed by p.63.

## 3. What this module does

* **§2 hypotheses**: `matRank` (the dimension of the image), the $H_0/H_1$ dimensions of
  a 2-term complex (`twoTermH0` / `twoTermH1`) and rank-nullity (`twoTermH1_add_matRank`
  and the like), the two vanishing criteria from surjectivity/injectivity
  (`twoTermH0_eq_zero_of_surjective` / `twoTermH1_eq_zero_of_injective`), the homology
  dimensions of both sides of p.63's formula (`threeTermH0/H1/H2`, `faultH0/H1/H2/H3`);
  §2.2 pushes the two hypotheses to a **general $\ell$** (surjectivity of `repR l` and
  injectivity of its transpose, $H_0 = 0$, the dual-side $H_1 = 0$, $\dim H_1(\mathcal R)
  = 1$ with the kernel spanned exactly by the all-ones vector), and the instance on
  `timeLikeRepR` (surjectivity, $H_0 = 0$, the all-ones vector in the kernel,
  $\dim H_1 = 1$) is its specialisation at $l = 3$ (`timeLikeRepR_eq_repR`).
* **§3 the engine of Künneth**: `kroneckerMap_one_mulVec_apply` (the component formula for
  the Kronecker $\otimes\,\mathrm{id}$, which is the bridge between Eq. (5) of p.63 and
  `koszulFaultComplex` of this library), `kerKroneckerOneEquiv`,
  `finrank_ker_kronecker_one`, `matRank_kronecker_one`
  ($\dim\ker(A\otimes\mathrm{id}_\iota) = |\iota|\cdot\dim\ker A$, and likewise for the
  rank), and `finrank_const_pi`. This is the source of the factor $|\mathcal R_i|$ in the
  Künneth formula, and the exact content of "homology commutes with multiplying by a
  coordinate space".
* **§4 all four degrees of the Künneth formula machine-checked** (all on the degenerate
  family $R = 0$): $m = 3$ uses the block shape `fromBlocks A 0 0 0`
  (`finrank_ker_fromBlocks_fin0` for the kernel, `kunneth_H3_R_zero` for the formula);
  §4.1 adds the kernel/image dimension lemmas for the two shapes **block-diagonal** and
  **block-row**, and §4.2 uses them to give the three degrees $m = 2,1,0$
  (`kunneth_H2_R_zero` / `kunneth_H1_R_zero` / `kunneth_H0_R_zero`), each using once the
  rank bound `matRank_le_finrank_ker_of_mul_eq_zero` supplied by the CSS condition.
* **§4.3–11 the ingredients for general $R$**: the kernel and image of the two block
  shapes block-row/block-column (§4.3, §4.4), the inclusion "a cycle $\otimes$ a cycle
  lands in $\ker\partial_2$" (§4.5), the general-module Π engine (§4.6–8: the kernel and
  the **image** dimensions of `piMulVec`), the currying interface (§4.9, giving
  `kunneth_H3` for general $R$), the mirror engine $\mathrm{id}\otimes A$ (§4.10), and the
  two lemmas on the dimension of a preimage and the rank of a quotient (§4.11).
* **§4.12 the intersection of images**: the last piece needed for the two-step
  decomposition of $\ker\partial_2$, namely
  $\dim(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}B)
  = \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R$, is machine-checked
  (`finrank_inf_range_koszul_data`). The method is "intersecting with an image equals the
  image of a quotient" (`finrank_inf_range_ker_sub`) coupled with taking quotients
  coordinatewise (`piMapQ`); both sides fall back to the Π engine.
* **§4.13 the matrix-world form of the intersection of images**: `currySwap` (the swap of
  tensor factor order) moves the tuple form of §4.12 to the block-matrix side, giving
  `finrank_inf_range_koszul` (the $\partial_2$ side) and `finrank_inf_range_koszul_row`
  (the $\partial_1$ side), exactly the two terms the two-step bookkeeping needs. The four
  transport lemmas hold for any two families of matrices of the same shape.
* **§4.14 the kernel of a general $2\times2$ block**: the kernel of the shape of `fd1`
  when $R \ne 0$, $\binom{A\ \ 0}{C\ \ D}$, is $= \dim\ker D + \dim(\ker A\cap\ker C)
  + \dim(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}D)$ (`finrank_ker_fromBlocks_row_col`),
  the three terms exactly the three pieces prepared in §4.12–13; the two explicit
  isomorphisms `kerProjSecondEquiv` / `rangeProjSecondEquiv` make the two-step bookkeeping
  "solve $y$ first, then $x$" concrete.
* **§4.16–17 the general-$R$ version of $H_2$**: the bookkeeping lemma `arith_H2_gen`
  (9 variables, 4 hypotheses, first moved to $\mathbb Z$ and closed by `ring`, then
  brought back) plus substitution gives `kunneth_H2` (the second bullet printed by p.63,
  $\dim H_2 = \dim\ker R\cdot h_1(C) + \mathrm{coker}R\cdot h_2(C)$).
* **§4.18–19 the general-$R$ version of $H_1$**: the bookkeeping lemma `arith_H1_gen`
  plus substitution gives `kunneth_H1` (the first bullet printed by p.63,
  $\dim H_1 = \dim\ker R\cdot h_0(C) + \mathrm{coker}R\cdot h_1(C)$); the two bounds come
  from linear algebra (`Submodule.finrank_le` and `Submodule.finrank_mono`).
* **§4.20 the general-$R$ version of $H_0$**: `kunneth_H0` ($\dim H_0
  = \mathrm{coker}R\cdot h_0(C)$), the quotient dimension via
  `finrank_quotient_range_eq` and $\mathrm{rank}\,\partial_0$ via the new lemma
  `matRank_eq_card_sub_finrank_ker` together with `finrank_ker_fd0`.
  **All four degrees are now machine-checked.**
* **§4.21 the four degrees for the two standard foliations**: substituting the four
  general formulas above into the two kinds of $\mathcal R$ used on p.63 (the repetition
  code $R$ and its dual $R^{\mathsf T}$) gives the two bullets read directly off the
  source: on the repetition side $H_1 = h_0(C)$, $H_2 = h_1(C)$, on the dual side
  $H_1 = h_1(C)$, $H_2 = h_2(C)$ (`kunneth_H0_repR` … `kunneth_H3_repR_transpose`, for
  any number of rounds $\ell$); the missing piece is the dual-side $H_0(\mathcal R)$,
  supplied by `repR_transpose_twoTermH0`.
* **§1 (continued) the relation to [56]**: the same $H_1$ formula is the **dimension
  half** of the **decoupling lemma** of [56] (Lemma 7 / Lemma 4 of its supplementary
  material): the $\ker R$ term is the time direction, the $\mathrm{coker}R$ term the
  space direction; the element-level decomposition is unrelated to this module, see the
  honest qualification of that section.
* **§5 honest boundary**: all four degrees over general $R$ are machine-checked (see item
  1 of that section); the remaining boundaries are stated one by one.

-/

namespace QECCertificates.Homology

open scoped BigOperators

open _root_.Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 2. Hypotheses: 2-term complexes, vanishing criteria, the `timeLikeRepR` instance

The homology of the 2-term complex $\mathcal R_1 \xrightarrow{R} \mathcal R_0$ ($R$ is
`Matrix R₀ R₁`, acting on column vectors): $H_1(\mathcal R) = \ker R$,
$H_0(\mathcal R) = \mathrm{coker}R$. -/

variable {R₀ R₁ C₀ C₁ C₂ : Type*}
variable [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂]

/-- The **rank** of a matrix: the dimension of its image.  This is `Matrix.rank` under a
local name -- the two unfold to the same `finrank` of `LinearMap.range A.mulVecLin` -- so
any lemma stated about one applies to the other by `show` or `change`.  The module uses the
rank only for rank-nullity. -/
noncomputable def matRank {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix β α (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin)

/-- The dimension of $H_1$: $\dim\ker R$. -/
noncomputable def twoTermH1 (R : Matrix R₀ R₁ (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)

/-- The dimension of $H_0$: $\dim\mathrm{coker}R = \dim\bigl(\mathbb F_2^{\mathcal R_0}/
  \mathrm{im}R\bigr)$. -/
noncomputable def twoTermH0 (R : Matrix R₀ R₁ (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ((R₀ → ZMod 2) ⧸ LinearMap.range R.mulVecLin)

/-- **Rank-nullity (kernel side)**: $\dim\ker R + \mathrm{rank}\,R = |\mathcal R_1|$. -/
theorem twoTermH1_add_matRank (R : Matrix R₀ R₁ (ZMod 2)) :
    twoTermH1 R + matRank R = Fintype.card R₁ := by
  have h := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  have hdim : Module.finrank (ZMod 2) (R₁ → ZMod 2) = Fintype.card R₁ :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  simp only [twoTermH1, matRank, hdim] at *
  omega

/-- **Rank-nullity (cokernel side)**: $\dim\mathrm{coker}R + \mathrm{rank}\,R = |\mathcal R_0|$. -/
theorem twoTermH0_add_matRank (R : Matrix R₀ R₁ (ZMod 2)) :
    twoTermH0 R + matRank R = Fintype.card R₀ := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range R.mulVecLin)
  have hdim : Module.finrank (ZMod 2) (R₀ → ZMod 2) = Fintype.card R₀ :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  simp only [twoTermH0, matRank, hdim] at *
  omega

/-! ### 2.0.1 The homology dimensions on both sides of p.63's formula (computable form)

Over a **field**, both $H_j(C)$ of [14] p.63 (the CSS complex
$C_2 \xrightarrow{\partial_2} C_1 \xrightarrow{\partial_1} C_0$) and $H_m(F)$ (the fault
complex $F_3 \xrightarrow{\partial_2} F_2 \xrightarrow{\partial_1} F_1
\xrightarrow{\partial_0} F_0$, the seven blocks of `Homology/FaultComplex.lean`) are
"kernel dimension minus image dimension", and this subsection writes them as computable
dimensions for use on both sides of the formula. (This is also the exact meaning of
"compute" in "It is easy to compute the homologies" on p.63.) -/

omit [Fintype R₀] [Fintype R₁] [Fintype C₂] in
/-- The $H_0$ dimension of the CSS complex: $\dim\bigl(C_0/\mathrm{im}\,\partial_1\bigr)$. -/
noncomputable def threeTermH0 (dC1 : Matrix C₀ C₁ (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin)

omit [Fintype R₀] [Fintype R₁] in
/-- The $H_1$ dimension of the CSS complex: $\dim\ker\partial_1 - \dim\mathrm{im}\,\partial_2$. -/
noncomputable def threeTermH1 (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin) - matRank dC2

omit [Fintype R₀] [Fintype R₁] [Fintype C₀] in
/-- The $H_2$ dimension of the CSS complex: $\dim\ker\partial_2$. -/
noncomputable def threeTermH2 (dC2 : Matrix C₁ C₂ (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)

variable {F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂ : Type*}
variable [Fintype F₀₀] [Fintype F₀₁] [Fintype F₀₂]
variable [Fintype F₁₀] [Fintype F₁₁] [Fintype F₁₂]

omit [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂] in
/-- The $H_3$ dimension of the fault complex: $\dim\ker\partial_2$ (nothing maps in at the top). -/
noncomputable def faultH3 (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker (fd2 F.d12_11 F.d12_02).mulVecLin)

omit [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂] in
/-- The $H_2$ dimension of the fault complex: $\dim\ker\partial_1 - \dim\mathrm{im}\,\partial_2$. -/
noncomputable def faultH2 (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker (fd1 F.d11_10 F.d11_01 F.d02_01).mulVecLin)
    - Module.finrank (ZMod 2) ↥(LinearMap.range (fd2 F.d12_11 F.d12_02).mulVecLin)

omit [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂] in
/-- The $H_1$ dimension of the fault complex: $\dim\ker\partial_0 - \dim\mathrm{im}\,\partial_1$.
(It is this that $H_1(F)$ and $H^2(F)$ of p.63 refer to; §8 of this module gives the
element-level form on the timelike side.) -/
noncomputable def faultH1 (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.ker (fd0 F.d10_00 F.d01_00).mulVecLin)
    - Module.finrank (ZMod 2) ↥(LinearMap.range (fd1 F.d11_10 F.d11_01 F.d02_01).mulVecLin)

omit [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂] in
/-- The $H_0$ dimension of the fault complex: $\dim\bigl(F_0/\mathrm{im}\,\partial_0\bigr)$. -/
noncomputable def faultH0 (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) : ℕ :=
  Module.finrank (ZMod 2) ((FaultTerm0 F₀₀ → ZMod 2) ⧸
    LinearMap.range (fd0 F.d10_00 F.d01_00).mulVecLin)

/-- **$R$ surjective implies $H_0(\mathcal R) = 0$** (the repetition-code case of [14]
p.63: "the full-rank parity-check matrix for the repetition code"). -/
theorem twoTermH0_eq_zero_of_surjective (R : Matrix R₀ R₁ (ZMod 2))
    (hR : Function.Surjective R.mulVecLin) : twoTermH0 R = 0 := by
  have h := twoTermH0_add_matRank R
  have hrank : matRank R = Fintype.card R₀ := by
    rw [matRank, LinearMap.range_eq_top.mpr hR]
    exact (Submodule.topEquiv (R := ZMod 2) (M := (R₀ → ZMod 2))).finrank_eq.trans
      (Module.finrank_fintype_fun_eq_card (ZMod 2))
  omega

omit [Fintype R₀] in
/-- **$R$ injective implies $H_1(\mathcal R) = 0$** (the dual case of [14] p.63: "its dual"). -/
theorem twoTermH1_eq_zero_of_injective (R : Matrix R₀ R₁ (ZMod 2))
    (hR : Function.Injective R.mulVecLin) : twoTermH1 R = 0 := by
  rw [twoTermH1, LinearMap.ker_eq_bot.mpr hR]
  exact Submodule.finrank_eq_zero.mpr rfl

/-! ### 2.1 Instance: `timeLikeRepR` of `Homology/FaultComplex.lean` (4 rounds)

`timeLikeRepR : Matrix (Fin 3) (Fin 4)` is the $3\times4$ **full-rank parity-check
matrix** (the "full-rank parity-check matrix for the repetition code" of [14] p.63, §4 of
`Homology/FaultComplex.lean`). This subsection machine-checks three of its properties:
surjectivity ($\Rightarrow H_0 = 0$), the all-ones vector in the kernel, and
$\dim H_1 = 1$ (so $H_1(\mathcal R) = \{0,\mathbf 1\}$, exactly the 1-dimensional space
printed by p.63). -/

/-- The image of `timeLikeRepR` contains the three standard basis vectors (computed entry
by entry from the definition of `timeLikeRepR`). -/
theorem timeLikeRepR_surjective : Function.Surjective timeLikeRepR.mulVecLin := by
  decide

theorem timeLikeRepR_allOnes_mem_ker : timeLikeRepR.mulVecLin 1 = 0 := by
  decide

theorem timeLikeRepR_twoTermH1 : twoTermH1 timeLikeRepR = 1 := by
  have h := twoTermH1_add_matRank timeLikeRepR
  have hrank : matRank timeLikeRepR = 3 := by
    rw [matRank, LinearMap.range_eq_top.mpr timeLikeRepR_surjective]
    exact ((Submodule.topEquiv (R := ZMod 2) (M := (Fin 3 → ZMod 2))).finrank_eq.trans
      (Module.finrank_fin_fun (ZMod 2)))
  simp only [hrank, Fintype.card_fin] at h
  omega


/-! ### 2.2 General $\ell$: the two "drop one term" hypotheses hold for **every** round count

§2.1 machine-checks the two hypotheses of p.63 only on the source's own $l = 4$ instance
(`timeLikeRepR`), whereas p.63 says "when $\mathcal R_\bullet$ is the repetition code /
its dual", for **any** number of rounds. This subsection carries the hypotheses over to a
general $\ell$: the parity-check matrix of the repetition code is surjective and its dual
injective, each of the two for every $\ell$.

* `repR l` is the parity-check matrix of the $\ell$-round repetition code,
  $(\partial x)_i = x_i + x_{i+1}$; it agrees with `timeLikeRepR` of
  `Homology/FaultComplex.lean` at $l = 3$ (`timeLikeRepR_eq_repR`), so the properties
  verified in §2.1 at $l = 4$ are specialisations of these.
* **Surjectivity** (`repR_surjective`): given explicitly by the recursive preimage
  $x_\ell = 0$, $x_i = x_{i+1} + y_i$ (`repPreimage`), whose equation lemma
  `repPreimage_castSucc` cancels entry by entry.
* **Dual-side injectivity** (`repR_transpose_injective`): transposition preserves the rank
  (`matRank_transpose`), so $\mathrm{rank}(R^{\mathsf T}) = \ell$, exactly the dimension
  of the domain, and rank-nullity gives kernel dimension $0$.
* The consumers of the two criteria, `repR_twoTermH0` / `repR_transpose_twoTermH1`, are
  $H_0(\mathcal R) = 0$ and the dual-side $H_1(\mathcal R) = 0$ for general $\ell$.
* Also the general version of $H_1(\mathcal R) = \{0,\mathbf 1\}$: the all-ones vector in
  the kernel (`repR_allOnes_mem_ker`) and $\dim H_1 = 1$ (`repR_twoTermH1`), which
  together say the kernel is **exactly** the one-dimensional space it spans
  (`repR_ker_eq_span_allOnes`), that is, the line printed by p.63. -/

/-- The parity-check matrix of the general $\ell$-round repetition code:
$(\partial x)_i = x_i + x_{i+1}$, for $i < \ell$ and $x$ of length $\ell + 1$.
`timeLikeRepR` of `Homology/FaultComplex.lean` is the specialisation at $\ell = 3$
(`timeLikeRepR_eq_repR`). -/
def repR (l : ℕ) : Matrix (Fin l) (Fin (l + 1)) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/-- The entrywise action of `repR l`: $(\partial x)_i = x_i + x_{i+1}$. -/
theorem repR_mulVec_apply (l : ℕ) (x : Fin (l + 1) → ZMod 2) (i : Fin l) :
    (repR l *ᵥ x) i = x (Fin.castSucc i) + x i.succ := by
  simp only [repR, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hstep : ∀ j : Fin (l + 1),
      (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = (i : ℕ) + 1 then (1 : ZMod 2) else 0) * x j
        = (if j = Fin.castSucc i then x j else 0) + (if j = i.succ then x j else 0) := by
    intro j
    by_cases h1 : j = Fin.castSucc i
    · subst h1
      have hne : ¬ ((Fin.castSucc i : Fin (l + 1)) = Fin.succ i) :=
        ne_of_lt (Fin.castSucc_lt_succ (i := i))
      simp [hne]
    · by_cases h2 : j = Fin.succ i
      · subst h2
        have hne : ¬ ((Fin.succ i : Fin (l + 1)) = Fin.castSucc i) := h1
        simp [hne]
      · have hne1 : ¬ ((j : ℕ) = (i : ℕ)) := fun h => h1 (Fin.ext h)
        have hne2 : ¬ ((j : ℕ) = (i : ℕ) + 1) := fun h => h2 (Fin.ext h)
        simp [hne1, hne2, h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (Fin.castSucc i) x, Finset.sum_ite_eq' Finset.univ i.succ x]
  simp

/-- The recursive preimage: $x_\ell = 0$, $x_i = x_{i+1} + y_i$ (accumulated backwards
from the end). -/
def repPreimage (l : ℕ) (y : Fin l → ZMod 2) : Fin (l + 1) → ZMod 2 :=
  Fin.reverseInduction (motive := fun _ => ZMod 2) 0 fun i xs => xs + y i

/-- The equation lemma for the recursive preimage: $x_i = x_{i+1} + y_i$. -/
theorem repPreimage_castSucc (l : ℕ) (y : Fin l → ZMod 2) (i : Fin l) :
    repPreimage l y (Fin.castSucc i) = repPreimage l y i.succ + y i :=
  Fin.reverseInduction_castSucc i

/-- **The recursive preimage really is a preimage**: $\partial\,(\text{repPreimage } y) = y$. -/
theorem repR_mulVec_repPreimage (l : ℕ) (y : Fin l → ZMod 2) :
    repR l *ᵥ repPreimage l y = y := by
  funext i
  rw [repR_mulVec_apply, repPreimage_castSucc]
  rw [add_assoc, add_comm (y i) (repPreimage l y i.succ), ← add_assoc,
    CharTwo.add_self_eq_zero, zero_add]

/-- **Surjectivity for general $\ell$**: the "full-rank parity-check matrix for the
repetition code" of p.63 holds for **any** number of rounds (§2.1 verified $l = 4$ only). -/
theorem repR_surjective (l : ℕ) : Function.Surjective (repR l).mulVecLin :=
  fun y => ⟨repPreimage l y, repR_mulVec_repPreimage l y⟩

/-- The rank of `repR l` equals the number of rows (full row rank). -/
theorem repR_matRank (l : ℕ) : matRank (repR l) = l := by
  rw [matRank, LinearMap.range_eq_top.mpr (repR_surjective l)]
  exact (Submodule.topEquiv (R := ZMod 2) (M := (Fin l → ZMod 2))).finrank_eq.trans
    (Module.finrank_fin_fun (ZMod 2))

/-- Transposition preserves the rank (`matRank` is the form of `Matrix.rank`, see its
definition in §2 of this module). -/
theorem matRank_transpose {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix β α (ZMod 2)) : matRank A.transpose = matRank A :=
  Matrix.rank_transpose A

/-- **Dual-side injectivity for general $\ell$**: the "its dual" of p.63 holds for **any**
number of rounds. -/
theorem repR_transpose_injective (l : ℕ) :
    Function.Injective (repR l).transpose.mulVecLin := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.finrank_eq_zero.mp
  have h := LinearMap.finrank_range_add_finrank_ker ((repR l).transpose).mulVecLin
  have hdom : Module.finrank (ZMod 2) (Fin l → ZMod 2) = l := Module.finrank_fin_fun (ZMod 2)
  have hran : Module.finrank (ZMod 2) ↥(LinearMap.range ((repR l).transpose).mulVecLin) = l := by
    have h1 : matRank ((repR l).transpose) = l := by
      rw [matRank_transpose (repR l), repR_matRank]
    exact h1
  simp only [hdom] at h
  omega

/-- **Consumer of the hypothesis (repetition side)**: the $\ell$-round repetition code of
this document satisfies $H_0(\mathcal R) = 0$, so the whole term
$H_0(\mathcal R)\otimes H_1(C)$ of the first bullet of p.63 can be dropped. -/
theorem repR_twoTermH0 (l : ℕ) : twoTermH0 (repR l) = 0 :=
  twoTermH0_eq_zero_of_surjective (repR l) (repR_surjective l)

/-- **Consumer of the hypothesis (dual side)**: the dual $\ell$-round complex satisfies
$H_1 = 0$, so the whole term $H_1(\mathcal R)\otimes H_2(C)$ can be dropped. -/
theorem repR_transpose_twoTermH1 (l : ℕ) : twoTermH1 (repR l).transpose = 0 :=
  twoTermH1_eq_zero_of_injective (repR l).transpose (repR_transpose_injective l)

/-- The all-ones vector lies in the kernel ($\mathbf 1$ is a kernel element of
$\partial$, $H_1(\mathcal R)\ni\mathbf 1$). -/
theorem repR_allOnes_mem_ker (l : ℕ) :
    (1 : Fin (l + 1) → ZMod 2) ∈ LinearMap.ker (repR l).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext i
  rw [repR_mulVec_apply]
  simp only [Pi.one_apply]
  exact CharTwo.add_self_eq_zero 1

/-- $\dim H_1(\mathcal R) = 1$: full row rank plus rank-nullity. -/
theorem repR_twoTermH1 (l : ℕ) : twoTermH1 (repR l) = 1 := by
  have h := twoTermH1_add_matRank (repR l)
  rw [repR_matRank, Fintype.card_fin] at h
  omega

/-- **$H_1(\mathcal R) = \{0,\mathbf 1\}$, general $\ell$**: the kernel is spanned exactly
by the all-ones vector (the line printed by p.63; the `timeLikeRepR` version of §2.1 is
the specialisation at $\ell = 3$). -/
theorem repR_ker_eq_span_allOnes (l : ℕ) :
    LinearMap.ker (repR l).mulVecLin
      = Submodule.span (ZMod 2) ({1} : Set (Fin (l + 1) → ZMod 2)) := by
  have h1ne : (1 : Fin (l + 1) → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, Nat.succ_pos l⟩
    simp at this
  have hle : Submodule.span (ZMod 2) ({1} : Set (Fin (l + 1) → ZMod 2))
      ≤ LinearMap.ker (repR l).mulVecLin := by
    rw [Submodule.span_le]
    rintro x rfl
    exact repR_allOnes_mem_ker l
  have hfin : Module.finrank (ZMod 2)
        ↥(Submodule.span (ZMod 2) ({1} : Set (Fin (l + 1) → ZMod 2)))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (repR l).mulVecLin) := by
    rw [finrank_span_singleton h1ne]
    exact (repR_twoTermH1 l).symm
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

/-- **The bridge to the $l = 4$ instance of this library**: `timeLikeRepR` of
`Homology/FaultComplex.lean` is `repR` at $\ell = 3$, so the properties verified in §2.1
on that instance are all specialisations of §2.2. -/
theorem timeLikeRepR_eq_repR : timeLikeRepR = repR 3 := by decide


/-! ## 3. The engine of Künneth: "homology commutes with multiplying by a coordinate space"

In the two bullets of p.63 the argument $\mathcal R_i$ enters the right-hand side through
$\otimes$ (as in $H_1(\mathcal R)\otimes H_0(C)$), which in **dimension** is a factor
$|\mathcal R_i|$. This step ("tensor a complex with a coordinate space; the homology
dimensions multiply term by term by the dimension of that space") is the core machinery
of Künneth, and this module machine-checks it. Technically it is the kernel/image
dimension formula for the Kronecker product $A\otimes \mathrm{id}_\iota$. -/

/-- **The component formula for the Kronecker $\otimes\,\mathrm{id}$** (the pivot of this
module; it is also the bridge between Eq. (5) of p.63 and `koszulFaultComplex` of §3 of
`Homology/FaultComplex.lean`):

$$\bigl((A\otimes \mathrm{id}_\iota)\cdot x\bigr)_{(i,i')} = \sum_j A_{ij}\,x_{(j,i')}.$$ -/
theorem kroneckerMap_one_mulVec_apply {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : Matrix α β (ZMod 2)) (x : β × ι → ZMod 2) (i : α) (i' : ι) :
    ((Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix ι ι (ZMod 2))) *ᵥ x) (i, i')
      = ∑ j, A i j * x (j, i') := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single i']
  · rw [Matrix.one_apply_eq, mul_one]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i') h

/-- The isomorphism (currying) between $\ker(A\otimes \mathrm{id}_\iota)$ and
$\iota \to \ker A$: the first component is the **slotwise** kernel. -/
def kerKroneckerOneEquiv {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : Matrix α β (ZMod 2)) :
    ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
        (1 : Matrix ι ι (ZMod 2))).mulVecLin) ≃ₗ[ZMod 2]
      (ι → ↥(LinearMap.ker A.mulVecLin)) where
  toFun x := fun i' =>
    ⟨fun j => (x : β × ι → ZMod 2) (j, i'), by
      funext i
      have hx : (Matrix.kroneckerMap (fun a b => a * b) A
          (1 : Matrix ι ι (ZMod 2))) *ᵥ (x : β × ι → ZMod 2) = 0 := x.2
      have hxy := congrFun hx (i, i')
      rw [kroneckerMap_one_mulVec_apply] at hxy
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] using hxy⟩
  invFun y :=
    ⟨fun p => (y p.2 : β → ZMod 2) p.1, by
      funext p
      obtain ⟨i, i'⟩ := p
      have hxy := congrFun (y i').2 i
      rw [Matrix.mulVecLin_apply] at hxy
      rw [Matrix.mulVecLin_apply, kroneckerMap_one_mulVec_apply]
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] using hxy⟩
  map_add' x y := by
    funext i'
    exact Subtype.ext (funext fun j => rfl)
  map_smul' c x := by
    funext i'
    exact Subtype.ext (funext fun j => rfl)
  left_inv x := by
    ext p
    rcases p with ⟨j, i'⟩
    rfl
  right_inv y := by
    funext i'
    exact Subtype.ext (funext fun j => rfl)

/-- The dimension of a constant-family Pi space: $\dim(\iota \to M) = |\iota|\cdot\dim M$. -/
theorem finrank_const_pi {ι M : Type*} [Fintype ι] [AddCommMonoid M] [Module (ZMod 2) M]
    [Module.Free (ZMod 2) M] [Module.Finite (ZMod 2) M] :
    Module.finrank (ZMod 2) (ι → M) = Fintype.card ι * Module.finrank (ZMod 2) M := by
  have h1 : Module.finrank (ZMod 2) (ι → M) = ∑ _i : ι, Module.finrank (ZMod 2) M :=
    Module.finrank_pi_fintype (ZMod 2) (M := fun _ : ι => M)
  have h2 : (∑ _i : ι, Module.finrank (ZMod 2) M)
      = Fintype.card ι * Module.finrank (ZMod 2) M := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [h1, h2]

/-- **Kernel dimension**: $\dim\ker(A\otimes \mathrm{id}_\iota) = |\iota|\cdot\dim\ker A$. -/
theorem finrank_ker_kronecker_one {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : Matrix α β (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
        (1 : Matrix ι ι (ZMod 2))).mulVecLin)
      = Fintype.card ι * Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) := by
  rw [(kerKroneckerOneEquiv A).finrank_eq,
    finrank_const_pi (ι := ι) (M := ↥(LinearMap.ker A.mulVecLin))]

/-- **Rank**: $\mathrm{rank}(A\otimes \mathrm{id}_\iota) = |\iota|\cdot\mathrm{rank}\,A$
(rank-nullity plus the previous lemma). -/
theorem matRank_kronecker_one {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (A : Matrix α β (ZMod 2)) :
    matRank (Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix ι ι (ZMod 2)))
      = Fintype.card ι * matRank A := by
  have hker := finrank_ker_kronecker_one (α := α) (β := β) (ι := ι) A
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix ι ι (ZMod 2))).mulVecLin
  have hrnA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdom : Module.finrank (ZMod 2) (β × ι → ZMod 2) = Fintype.card β * Fintype.card ι := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod]
  have hdomA : Module.finrank (ZMod 2) (β → ZMod 2) = Fintype.card β :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have key : matRank (Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix ι ι (ZMod 2)))
      + Fintype.card ι * Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
      = Fintype.card β * Fintype.card ι := by
    rw [hker, hdom] at hrn
    rw [matRank]
    exact hrn
  have keyA : matRank A + Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
      = Fintype.card β := by
    rw [hdomA] at hrnA
    rw [matRank]
    exact hrnA
  rw [Nat.mul_comm (Fintype.card β) (Fintype.card ι)] at key
  have hmain : matRank (Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix ι ι (ZMod 2)))
      = Fintype.card ι * (Fintype.card β
        - Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)) := by
    rw [Nat.mul_sub]
    omega
  rw [hmain]
  congr 1
  omega

/-! ## 4. One **degree** of the Künneth formula ($m = 3$): the degenerate family $R = 0$

Take $R = 0$ (the differential of the 2-term complex is zero): then the **cross terms of
the Koszul total complex, which contain $R$, vanish**, the three differentials reduce to
the $\partial\otimes\mathrm{id}$ blocks, and the engine of §3 gives the homology
dimensions directly. This subsection machine-checks the formula at **one degree of that
degenerate family** ($m = 3$, the cleanest one):

$$\dim H_3(\mathcal R\otimes C) = |\mathcal R_1|\cdot\dim H_2(C)
  \qquad(\text{general shape } H_3 = H_1(\mathcal R)\otimes H_2(C),
  \text{while for } R = 0,\ H_1(\mathcal R) = \mathbb F_2^{\mathcal R_1}).$$

The other three degrees ($m = 0,1,2$) are computed in the same way and need only two
block-matrix lemmas (the kernel and image of block-diagonal / block-row shapes):
**the ingredients are in §4.1 and the four formulas in §4.2**. -/

/-- **The component formula for the block matrix $\binom{A\ 0}{0\ 0}$ (the `inl` row)**
(the second column block has the empty index `Fin 0`):

$$\Bigl(\binom{A\ 0}{0\ 0}\cdot x\Bigr)_{(\mathrm{inl}\,p)}
  = \bigl(A \cdot (x \circ \mathrm{inl})\bigr)_p.$$ -/
theorem fromBlocks_fin0_mulVec_apply_inl {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q] (A : Matrix P₁ Q (ZMod 2)) (x : (Q ⊕ Fin 0) → ZMod 2) (p : P₁) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2))
        (0 : Matrix P₂ Q (ZMod 2)) (0 : Matrix P₂ (Fin 0) (ZMod 2))) *ᵥ x) (Sum.inl p)
      = (A *ᵥ (fun q => x (Sum.inl q))) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- As above, the `inr` row is identically zero. -/
theorem fromBlocks_fin0_mulVec_apply_inr {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q] (A : Matrix P₁ Q (ZMod 2)) (x : (Q ⊕ Fin 0) → ZMod 2) (p : P₂) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2))
        (0 : Matrix P₂ Q (ZMod 2)) (0 : Matrix P₂ (Fin 0) (ZMod 2))) *ᵥ x) (Sum.inr p) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- **The kernel of the block matrix $\binom{A\ 0}{0\ 0}$** (the second column block has
the empty index `Fin 0`): isomorphic to the kernel of $A$.

(A vector over $Q \oplus \mathrm{Fin}\ 0$ is fully determined by its half over $Q$; the
other half lives over the empty type.) -/
def kerFromBlocksFin0Equiv {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q]
    (A : Matrix P₁ Q (ZMod 2)) :
    ↥(LinearMap.ker (Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2))
        (0 : Matrix P₂ Q (ZMod 2)) (0 : Matrix P₂ (Fin 0) (ZMod 2))).mulVecLin)
      ≃ₗ[ZMod 2] ↥(LinearMap.ker A.mulVecLin) where
  toFun x :=
    ⟨fun q => (x : (Q ⊕ Fin 0) → ZMod 2) (Sum.inl q), by
      funext p
      have hx : (Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2))
          (0 : Matrix P₂ Q (ZMod 2)) (0 : Matrix P₂ (Fin 0) (ZMod 2))) *ᵥ
            (x : (Q ⊕ Fin 0) → ZMod 2) = 0 := LinearMap.mem_ker.mp x.2
      have hxy := congrFun hx (Sum.inl p)
      rw [fromBlocks_fin0_mulVec_apply_inl] at hxy
      simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using hxy⟩
  invFun z :=
    ⟨fun p => match p with
      | Sum.inl q => (z : Q → ZMod 2) q
      | Sum.inr e => Fin.elim0 e, by
      funext p
      cases p with
      | inl q =>
        rw [Matrix.mulVecLin_apply, fromBlocks_fin0_mulVec_apply_inl]
        have hz : A *ᵥ (z : Q → ZMod 2) = 0 := LinearMap.mem_ker.mp z.2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hz q
      | inr e =>
        rw [Matrix.mulVecLin_apply, fromBlocks_fin0_mulVec_apply_inr, Pi.zero_apply]⟩
  map_add' x y := Subtype.ext (funext fun q => rfl)
  map_smul' c x := Subtype.ext (funext fun q => rfl)
  left_inv x := by
    ext p
    cases p with
    | inl q => rfl
    | inr e => exact Fin.elim0 e
  right_inv z := Subtype.ext (funext fun q => rfl)

/-- **Kernel dimension**: $\dim\ker\binom{A\ 0}{0\ 0} = \dim\ker A$ (the empty-index half
contributes no dimension). -/
theorem finrank_ker_fromBlocks_fin0 {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q]
    (A : Matrix P₁ Q (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks A
        (0 : Matrix P₁ (Fin 0) (ZMod 2)) (0 : Matrix P₂ Q (ZMod 2))
        (0 : Matrix P₂ (Fin 0) (ZMod 2))).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) :=
  (kerFromBlocksFin0Equiv A).finrank_eq

/-- **The $m = 3$ degree of the Künneth formula on the degenerate family $R = 0$**
(machine-checked): $$\dim H_3(\mathcal R\otimes C) = |\mathcal R_1|\cdot\dim H_2(C).$$

$|\mathcal R_1|$ is exactly $\dim H_1(\mathcal R)$ (for $R = 0$,
$H_1(\mathcal R) = \mathbb F_2^{\mathcal R_1}$), consistent with the general shape
$H_3 = H_1(\mathcal R)\otimes H_2(C)$ of p.63; the dimension factor is given by
`finrank_ker_kronecker_one` of §3, and the block-matrix step by
`finrank_ker_fromBlocks_fin0`. -/
theorem kunneth_H3_R_zero [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH3 (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC)
      = Fintype.card R₁ * threeTermH2 dC2 := by
  have h11 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d12_11
      = Matrix.kronecker dC2 (1 : Matrix R₁ R₁ (ZMod 2)) :=
    koszulFaultComplex_d12_11 _ _ _ _
  have h02 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d12_02
      = (0 : Matrix (C₂ × R₀) (C₂ × R₁) (ZMod 2)) := by
    rw [koszulFaultComplex_d12_02]
    exact Matrix.kronecker_zero _
  rw [faultH3, h11, h02, threeTermH2]
  simp only [fd2]
  -- Unify `↥(M.mulVecLin.ker)` with `↥(LinearMap.ker M.mulVecLin)`, and expand
  -- `Matrix.kronecker` into `kroneckerMap` (the form of the engine lemmas)
  change Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₁ R₁ (ZMod 2)))
      (0 : Matrix (C₁ × R₁) (Fin 0) (ZMod 2)) (0 : Matrix (C₂ × R₀) (C₂ × R₁) (ZMod 2))
      (0 : Matrix (C₂ × R₀) (Fin 0) (ZMod 2))).mulVecLin)
    = Fintype.card R₁ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
  have hkb := finrank_ker_fromBlocks_fin0 (P₁ := C₁ × R₁) (P₂ := C₂ × R₀) (Q := C₂ × R₁)
    (A := Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₁ R₁ (ZMod 2)))
  rw [hkb]
  exact finrank_ker_kronecker_one (α := C₁) (β := C₂) (ι := R₁) dC2

/-! ## 4.1 Two block shapes: block-diagonal and block-row (ingredients for $m=0,1,2$)

The $m=3$ case of §4 needs only one block shape $\binom{A\ 0}{0\ 0}$
(`finrank_ker_fromBlocks_fin0`, the second column block having the empty index). The other
three degrees need two more, supplied here by the **same method**: build an explicit `≃ₗ`
linear equivalence, then read the dimension off `.finrank_eq`, with no determinant
computation and no lemma from outside the library.

* **Block-diagonal** $\binom{A\ 0}{0\ B}$ (needed for $m=1,2$): both the kernel and the
  image split block by block, and the dimensions add;
* **Block-row (first column block zero)** $\binom{0\ B}{0\ 0}$ (needed for $m=0,1$): the
  second row block has the empty index `Fin 0`, exactly the row-block shape of `fd0`, and
  its image has the same dimension as the image of $B$.

This yields three block-shape dimension lemmas (`finrank_ker_fromBlocks_diag`,
`matRank_fromBlocks_diag`, `matRank_fromBlocks_zeroLeft`), together with three small
lemmas independent of the block shape (`matRank_zero`,
`finrank_ker_eq_card_sub_matRank`, `finrank_quotient_range_eq`), and one **rank bound
supplied by the CSS condition** `matRank_le_finrank_ker_of_mul_eq_zero`
($\mathrm{im}\,\partial_2 \subseteq \ker\partial_1$, the entire content of the word
"homology", and the only input needed by the arithmetic of the two cases $m=1,2$ below).

**§4.3 adds the general block-row** $\binom{A\ B}{0\ 0}$ (for $R \ne 0$ the top-left block
of `fd0` is no longer zero): it is the small subsection just before the three arithmetic
lemmas below.

The last three are pure $\mathbb N$ arithmetic (one used by each of $m=0,1,2$), listed
separately so as not to be mixed in with the dimension derivations. -/

/-- The component formula for the block-diagonal matrix $\binom{A\ 0}{0\ B}$ (the `inl`
row): the second column block is zero, so only the first term remains. -/
theorem fromBlocks_diag_mulVec_apply_inl {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₂ Q₂ (ZMod 2))
    (x : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₁) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2)) B) *ᵥ x)
        (Sum.inl p) = (A *ᵥ fun q => x (Sum.inl q)) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- The component formula for the block-diagonal matrix $\binom{A\ 0}{0\ B}$ (the `inr`
row): the first column block is zero, so only the second term remains. -/
theorem fromBlocks_diag_mulVec_apply_inr {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₂ Q₂ (ZMod 2))
    (x : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₂) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2)) B) *ᵥ x)
        (Sum.inr p) = (B *ᵥ fun q => x (Sum.inr q)) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

/-- **The kernel of a block-diagonal matrix**:
$\ker\binom{A\ 0}{0\ B} \cong \ker A \times \ker B$ (each of the two components satisfies
its own kernel condition). -/
noncomputable def kerFromBlocksDiagEquiv {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₂ Q₂ (ZMod 2)) :
    ↥(LinearMap.ker (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2))
        (0 : Matrix P₂ Q₁ (ZMod 2)) B).mulVecLin)
      ≃ₗ[ZMod 2] (↥(LinearMap.ker A.mulVecLin) × ↥(LinearMap.ker B.mulVecLin)) where
  toFun x :=
    (⟨fun q => (x : (Q₁ ⊕ Q₂) → ZMod 2) (Sum.inl q), by
      funext p
      have hx : (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2))
          B) *ᵥ (x : (Q₁ ⊕ Q₂) → ZMod 2) = 0 := LinearMap.mem_ker.mp x.2
      have hxy := congrFun hx (Sum.inl p)
      rw [fromBlocks_diag_mulVec_apply_inl] at hxy
      simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using hxy⟩,
     ⟨fun q => (x : (Q₁ ⊕ Q₂) → ZMod 2) (Sum.inr q), by
      funext p
      have hx : (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2))
          B) *ᵥ (x : (Q₁ ⊕ Q₂) → ZMod 2) = 0 := LinearMap.mem_ker.mp x.2
      have hxy := congrFun hx (Sum.inr p)
      rw [fromBlocks_diag_mulVec_apply_inr] at hxy
      simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using hxy⟩)
  invFun y :=
    ⟨fun p => match p with
      | Sum.inl q => (y.1 : Q₁ → ZMod 2) q
      | Sum.inr q => (y.2 : Q₂ → ZMod 2) q, by
      funext p
      cases p with
      | inl q =>
        rw [Matrix.mulVecLin_apply, fromBlocks_diag_mulVec_apply_inl]
        have hy : A *ᵥ (y.1 : Q₁ → ZMod 2) = 0 := LinearMap.mem_ker.mp y.1.2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hy q
      | inr q =>
        rw [Matrix.mulVecLin_apply, fromBlocks_diag_mulVec_apply_inr]
        have hy : B *ᵥ (y.2 : Q₂ → ZMod 2) = 0 := LinearMap.mem_ker.mp y.2.2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hy q⟩
  map_add' x y := by
    refine Prod.ext ?_ ?_ <;> exact Subtype.ext (funext fun _ => rfl)
  map_smul' c x := by
    refine Prod.ext ?_ ?_ <;> exact Subtype.ext (funext fun _ => rfl)
  left_inv x := by
    refine Subtype.ext (funext fun p => ?_)
    cases p <;> rfl
  right_inv y := by
    refine Prod.ext ?_ ?_ <;> exact Subtype.ext (funext fun _ => rfl)

/-- **Kernel dimension of a block-diagonal matrix**:
$\dim\ker\binom{A\ 0}{0\ B} = \dim\ker A + \dim\ker B$. -/
theorem finrank_ker_fromBlocks_diag {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₂ Q₂ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks A
        (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2)) B).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
        + Module.finrank (ZMod 2) ↥(LinearMap.ker B.mulVecLin) := by
  rw [(kerFromBlocksDiagEquiv A B).finrank_eq]
  exact Module.finrank_prod

/-- **Rank of a block-diagonal matrix**:
$\mathrm{rank}\binom{A\ 0}{0\ B} = \mathrm{rank}\,A + \mathrm{rank}\,B$
(rank-nullity plus `finrank_ker_fromBlocks_diag`). -/
theorem matRank_fromBlocks_diag {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₂ Q₂ (ZMod 2)) :
    matRank (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2)) B)
      = matRank A + matRank B := by
  have hk := finrank_ker_fromBlocks_diag A B
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.fromBlocks A
    (0 : Matrix P₁ Q₂ (ZMod 2)) (0 : Matrix P₂ Q₁ (ZMod 2)) B).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h3 := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hd : Module.finrank (ZMod 2) ((Q₁ ⊕ Q₂) → ZMod 2)
      = Fintype.card Q₁ + Fintype.card Q₂ := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have hd1 : Module.finrank (ZMod 2) (Q₁ → ZMod 2) = Fintype.card Q₁ :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hd2 : Module.finrank (ZMod 2) (Q₂ → ZMod 2) = Fintype.card Q₂ :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  simp only [matRank, hk, hd, hd1, hd2] at *
  omega

/-- The component formula for the block matrix $\binom{0\ B}{0\ 0}$ (the `inl` row): the
first column block is zero, so only the $B$ term remains. -/
theorem fromBlocks_zeroLeft_mulVec_apply_inl {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (B : Matrix P₁ Q₂ (ZMod 2)) (x : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₁) :
    ((Matrix.fromBlocks (0 : Matrix P₁ Q₁ (ZMod 2)) B (0 : Matrix P₂ Q₁ (ZMod 2))
        (0 : Matrix P₂ Q₂ (ZMod 2))) *ᵥ x) (Sum.inl p) = (B *ᵥ fun q => x (Sum.inr q)) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

/-- As above, the `inr` row is identically zero (the second row block is $0$). -/
theorem fromBlocks_zeroLeft_mulVec_apply_inr {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (B : Matrix P₁ Q₂ (ZMod 2)) (x : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₂) :
    ((Matrix.fromBlocks (0 : Matrix P₁ Q₁ (ZMod 2)) B (0 : Matrix P₂ Q₁ (ZMod 2))
        (0 : Matrix P₂ Q₂ (ZMod 2))) *ᵥ x) (Sum.inr p) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- **The image of a block-row (first column block zero)**:
$\mathrm{im}\binom{0\ B}{0\ 0} \cong \mathrm{im}\,B$ (the forward map takes the first
coordinate, the inverse pads an element of the image of $B$ with zero in the second). -/
noncomputable def rangeFromBlocksZeroLeftEquiv {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (B : Matrix P₁ Q₂ (ZMod 2)) :
    ↥(LinearMap.range (Matrix.fromBlocks (0 : Matrix P₁ Q₁ (ZMod 2)) B
        (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))).mulVecLin)
      ≃ₗ[ZMod 2] ↥(LinearMap.range B.mulVecLin) where
  toFun y :=
    ⟨fun p => (y : (P₁ ⊕ P₂) → ZMod 2) (Sum.inl p), by
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      refine LinearMap.mem_range.mpr ⟨fun q => x (Sum.inr q), ?_⟩
      funext p
      have h := congrFun hx (Sum.inl p)
      rw [Matrix.mulVecLin_apply, fromBlocks_zeroLeft_mulVec_apply_inl] at h
      simpa only [Matrix.mulVecLin_apply] using h⟩
  invFun z :=
    ⟨Sum.elim (fun p => (z : P₁ → ZMod 2) p) (fun _ => 0), by
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp z.2
      refine LinearMap.mem_range.mpr ⟨Sum.elim (fun _ : Q₁ => 0) x, ?_⟩
      funext p
      cases p with
      | inl p₁ =>
        rw [Matrix.mulVecLin_apply, fromBlocks_zeroLeft_mulVec_apply_inl]
        have hw : (fun q => (Sum.elim (fun _ : Q₁ => 0) x) (Sum.inr q)) = x := by
          funext q
          rw [Sum.elim_inr]
        rw [hw]
        have h := congrFun hx p₁
        rw [Matrix.mulVecLin_apply] at h
        simpa only [Sum.elim_inl] using h
      | inr p₂ =>
        rw [Matrix.mulVecLin_apply, fromBlocks_zeroLeft_mulVec_apply_inr]
        rfl⟩
  map_add' y z := by
    refine Subtype.ext (funext fun p => ?_)
    simp
  map_smul' c y := by
    refine Subtype.ext (funext fun p => ?_)
    simp
  left_inv y := by
    refine Subtype.ext (funext fun p => ?_)
    cases p with
    | inl p₁ => rfl
    | inr p₂ =>
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      have h := congrFun hx (Sum.inr p₂)
      rw [Matrix.mulVecLin_apply, fromBlocks_zeroLeft_mulVec_apply_inr] at h
      exact h
  right_inv z := by
    refine Subtype.ext (funext fun p₁ => ?_)
    rfl

/-- **The rank of a block-row (first column block zero)**:
$\mathrm{rank}\binom{0\ B}{0\ 0} = \mathrm{rank}\,B$ (an immediate consequence of the
image isomorphism above). -/
theorem matRank_fromBlocks_zeroLeft {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (B : Matrix P₁ Q₂ (ZMod 2)) :
    matRank (Matrix.fromBlocks (0 : Matrix P₁ Q₁ (ZMod 2)) B
        (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))) = matRank B :=
  (rangeFromBlocksZeroLeftEquiv B).finrank_eq

/-- The rank of the zero matrix is zero. -/
theorem matRank_zero {P Q : Type*} [Fintype P] [Fintype Q] :
    matRank (0 : Matrix P Q (ZMod 2)) = 0 := by
  rw [matRank, Matrix.mulVecLin_zero]
  simp

/-- **Kernel dimension = source-space dimension minus rank** (rank-nullity, written on
the "subtraction" side). -/
theorem finrank_ker_eq_card_sub_matRank {P Q : Type*} [Fintype P] [Fintype Q]
    (M : Matrix P Q (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker M.mulVecLin) = Fintype.card Q - matRank M := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hd : Module.finrank (ZMod 2) (Q → ZMod 2) = Fintype.card Q :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  simp only [matRank, hd] at h ⊢
  omega

/-- **Cokernel dimension = target-space dimension minus rank** (as above, on the quotient
side; the reading of `faultH0`). -/
theorem finrank_quotient_range_eq {P Q : Type*} [Fintype P] [Fintype Q]
    (M : Matrix P Q (ZMod 2)) :
    Module.finrank (ZMod 2) ((P → ZMod 2) ⧸ LinearMap.range M.mulVecLin)
      = Fintype.card P - matRank M := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range M.mulVecLin)
  have hd : Module.finrank (ZMod 2) (P → ZMod 2) = Fintype.card P :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  simp only [matRank, hd] at h ⊢
  omega

omit [Fintype C₀] in
/-- **The rank bound supplied by the CSS condition**: when $\partial_1\partial_2 = 0$ we
have $\mathrm{im}\,\partial_2 \subseteq \ker\partial_1$, hence
$\mathrm{rank}\,\partial_2 \le \dim\ker\partial_1$. (The entire content of the word
"homology", and the only input needed by the arithmetic of the two cases $m=1,2$.) -/
theorem matRank_le_finrank_ker_of_mul_eq_zero (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    matRank dC2 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin) := by
  have hle : LinearMap.range dC2.mulVecLin ≤ LinearMap.ker dC1.mulVecLin := by
    intro x hx
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    rw [← hy, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hC, Matrix.zero_mulVec]
  calc matRank dC2 = Module.finrank (ZMod 2) ↥(LinearMap.range dC2.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin) := Submodule.finrank_mono hle

/-! ### 4.3 The general block-row $\binom{A\ B}{0\ 0}$: the extra block when $R \ne 0$

Among the three block shapes of §4.1, **block-row** was done only for the case where the
first column block is zero (`matRank_fromBlocks_zeroLeft`), which is exactly the shape of
`fd0` when $R = 0$. For $R \ne 0$ the top-left block of `fd0` is no longer zero, and what
is needed is the image and kernel of the **general block-row** $\binom{A\ B}{0\ 0}$. This
subsection supplies it, by the same method as §4.1: build an explicit `≃ₗ` and read the
dimension off `.finrank_eq`.

Unlike the block-diagonal case, the images of the two blocks of a general block-row
**can intersect** (the top-left and top-right blocks of `fd0` are exactly such a pair),
and the dimension bookkeeping differs by precisely this term. Applying
`Submodule.finrank_sup_add_finrank_inf_eq` to the two images and then matching "the sum of
the two images" against "the image of the general block-row" via `rangeFromBlocksRowEquiv`
yields three conclusions: the rank identity in additive form
(`matRank_fromBlocks_row_add`, avoiding truncated subtraction on $\mathbb N$), its
subtraction form (`finrank_inf_range_eq`), and the kernel of the general block-row
(`finrank_ker_fromBlocks_row`): what the kernel has in excess of the sum of the two
kernels is exactly the intersection of the images. -/

/-- The component formula for the general block-row $\binom{A\ B}{0\ 0}$ (the `inl` row):
each of the two blocks contributes one term. -/
theorem fromBlocks_row_mulVec_apply_inl {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₁ Q₂ (ZMod 2))
    (x : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₁) :
    ((Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))) *ᵥ x)
        (Sum.inl p) = (A *ᵥ fun q => x (Sum.inl q)) p + (B *ᵥ fun q => x (Sum.inr q)) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂]

/-- The component formula for the general block-row $\binom{A\ B}{0\ 0}$ (the `inr` row):
identically zero (the second row block is the empty index). -/
theorem fromBlocks_row_mulVec_apply_inr {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₁ Q₂ (ZMod 2))
    (x : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₂) :
    ((Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))) *ᵥ x)
        (Sum.inr p) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul]
  simp

/-- **The image of a general block-row $\cong$ the sum of the two images**:
$\mathrm{im}\binom{A\ B}{0\ 0} \cong \mathrm{im}A \sqcup \mathrm{im}B$ (the component on
the second row block is zero, so the image lies in the `inl` half). -/
noncomputable def rangeFromBlocksRowEquiv {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₁ Q₂ (ZMod 2)) :
    ↥(LinearMap.range (Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2))
        (0 : Matrix P₂ Q₂ (ZMod 2))).mulVecLin)
      ≃ₗ[ZMod 2] ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) where
  toFun y :=
    ⟨fun p => (y : (P₁ ⊕ P₂) → ZMod 2) (Sum.inl p), by
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      have hpt : (fun p => (y : (P₁ ⊕ P₂) → ZMod 2) (Sum.inl p))
          = A *ᵥ (fun q : Q₁ => x (Sum.inl q)) + B *ᵥ (fun q : Q₂ => x (Sum.inr q)) := by
        funext p
        have h := congrFun hx (Sum.inl p)
        rw [Matrix.mulVecLin_apply, fromBlocks_row_mulVec_apply_inl] at h
        simpa only [Pi.add_apply] using h.symm
      rw [hpt]
      exact Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨_, rfl⟩)
        (LinearMap.mem_range.mpr ⟨_, rfl⟩)⟩
  invFun z :=
    ⟨Sum.elim (fun p => (z : P₁ → ZMod 2) p) (fun _ => 0), by
      rcases Submodule.mem_sup.mp z.2 with ⟨a, ha, b, hb, hab⟩
      obtain ⟨xa, hxa⟩ := LinearMap.mem_range.mp ha
      obtain ⟨xb, hxb⟩ := LinearMap.mem_range.mp hb
      refine LinearMap.mem_range.mpr ⟨Sum.elim xa xb, ?_⟩
      funext p
      cases p with
      | inl p₁ =>
        rw [Matrix.mulVecLin_apply, fromBlocks_row_mulVec_apply_inl]
        have h1 : (fun q => (Sum.elim xa xb : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q)) = xa := by
          funext q; rw [Sum.elim_inl]
        have h2 : (fun q => (Sum.elim xa xb : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q)) = xb := by
          funext q; rw [Sum.elim_inr]
        rw [h1, h2, Sum.elim_inl, ← hab, Pi.add_apply, ← hxa, ← hxb]
        simp only [Matrix.mulVecLin_apply]
      | inr p₂ =>
        rw [Matrix.mulVecLin_apply, fromBlocks_row_mulVec_apply_inr, Sum.elim_inr]⟩
  map_add' y z := by
    refine Subtype.ext (funext fun p => ?_)
    simp only [Submodule.coe_add, Pi.add_apply]
  map_smul' c y := by
    refine Subtype.ext (funext fun p => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv y := by
    refine Subtype.ext (funext fun p => ?_)
    cases p with
    | inl p₁ => rfl
    | inr p₂ =>
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      have h := congrFun hx (Sum.inr p₂)
      rw [Matrix.mulVecLin_apply, fromBlocks_row_mulVec_apply_inr] at h
      simpa only [Sum.elim_inr] using h
  right_inv z := by
    refine Subtype.ext (funext fun p => ?_)
    rfl

/-- **The rank of a general block-row (additive form)**:
$\mathrm{rank}\binom{A\ B}{0\ 0} + \dim(\mathrm{im}A\cap\mathrm{im}B)
= \mathrm{rank}A + \mathrm{rank}B$. The additive form avoids truncated subtraction on
$\mathbb N$; the reasoning uses only inclusion-exclusion for ranks and the image
correspondence above. -/
theorem matRank_fromBlocks_row_add {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₁ Q₂ (ZMod 2)) :
    matRank (Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2)))
      + Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin)
      = matRank A + matRank B := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin)
    (LinearMap.range B.mulVecLin)
  have hsup : Module.finrank (ZMod 2)
      ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)
      = matRank (Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2))
          (0 : Matrix P₂ Q₂ (ZMod 2))) :=
    (rangeFromBlocksRowEquiv (P₂ := P₂) (Q₁ := Q₁) A B).finrank_eq.symm
  simp only [matRank] at h hsup ⊢
  omega

/-- **The dimension of the intersection of the two images of a general block-row**:
$\dim(\mathrm{im}A\cap\mathrm{im}B) = \mathrm{rank}A + \mathrm{rank}B
- \mathrm{rank}\binom{A\ B}{0\ 0}$, the term by which the kernel of the block-row exceeds
the sum of the two kernels when $R \ne 0$. -/
theorem finrank_inf_range_eq {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₁ Q₂ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin)
      = matRank A + matRank B
        - matRank (Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2))
            (0 : Matrix P₂ Q₂ (ZMod 2))) := by
  have h := matRank_fromBlocks_row_add (P₂ := P₂) A B
  have hle : matRank (Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2))
      (0 : Matrix P₂ Q₂ (ZMod 2))) ≤ matRank A + matRank B := by omega
  omega

/-- **The kernel of a general block-row**: $\dim\ker\binom{A\ B}{0\ 0} = \dim\ker A +
\dim\ker B + \dim(\mathrm{im}A\cap\mathrm{im}B)$; beyond the two kernels separately, the
excess is exactly the intersection of the two images. -/
theorem finrank_ker_fromBlocks_row {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (B : Matrix P₁ Q₂ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks A B
        (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
        + Module.finrank (ZMod 2) ↥(LinearMap.ker B.mulVecLin)
        + Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin) := by
  have hleA : matRank A ≤ Fintype.card Q₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [matRank]
    have hd : Module.finrank (ZMod 2) (Q₁ → ZMod 2) = Fintype.card Q₁ :=
      Module.finrank_fintype_fun_eq_card (ZMod 2)
    omega
  have hleB : matRank B ≤ Fintype.card Q₂ := by
    have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [matRank]
    have hd : Module.finrank (ZMod 2) (Q₂ → ZMod 2) = Fintype.card Q₂ :=
      Module.finrank_fintype_fun_eq_card (ZMod 2)
    omega
  have hA : Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) + matRank A
      = Fintype.card Q₁ := by
    rw [finrank_ker_eq_card_sub_matRank (M := A)]; exact Nat.sub_add_cancel hleA
  have hB : Module.finrank (ZMod 2) ↥(LinearMap.ker B.mulVecLin) + matRank B
      = Fintype.card Q₂ := by
    rw [finrank_ker_eq_card_sub_matRank (M := B)]; exact Nat.sub_add_cancel hleB
  have hR : Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks A B
        (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))).mulVecLin)
      + matRank (Matrix.fromBlocks A B (0 : Matrix P₂ Q₁ (ZMod 2))
          (0 : Matrix P₂ Q₂ (ZMod 2))) = Fintype.card (Q₁ ⊕ Q₂) := by
    rw [finrank_ker_eq_card_sub_matRank]
    refine Nat.sub_add_cancel ?_
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.fromBlocks A B
      (0 : Matrix P₂ Q₁ (ZMod 2)) (0 : Matrix P₂ Q₂ (ZMod 2))).mulVecLin
    rw [matRank]
    have hd : Module.finrank (ZMod 2) ((Q₁ ⊕ Q₂) → ZMod 2) = Fintype.card (Q₁ ⊕ Q₂) :=
      Module.finrank_fintype_fun_eq_card (ZMod 2)
    omega
  have hadd := matRank_fromBlocks_row_add (P₂ := P₂) A B
  simp only [Fintype.card_sum] at hR
  omega

/-- Arithmetic ($m = 0$): factor out $|\mathcal R_0|$ (the term $|\mathcal R_0|h_0(C)$).
`h` is the natural hypothesis for it (under truncated subtraction on $\mathbb N$ it in
fact holds for all parameters). -/
theorem arith_H0 (b d r₁ : ℕ) (_h : r₁ ≤ b) : b * d - d * r₁ = d * (b - r₁) := by
  rw [Nat.mul_comm b d, Nat.mul_sub_left_distrib]

/-- Arithmetic ($m = 2$): each of the two subtrahends matches one term. -/
theorem arith_H2 (a b k₁ k₂ r₂ : ℕ) (h : r₂ ≤ k₁) :
    a * k₁ + b * k₂ - a * r₂ = a * (k₁ - r₂) + b * k₂ := by
  have h4 : a * r₂ ≤ a * k₁ := Nat.mul_le_mul_left a h
  rw [Nat.mul_sub_left_distrib]
  omega

/-- Arithmetic ($m = 1$): using $c = r_1 + k_1$ (rank-nullity) to hook the $|\mathcal R_1|$
term up with the two halves $h_0, h_1$. -/
theorem arith_H1 (a b c d k₁ r₁ r₂ : ℕ)
    (h1 : r₁ ≤ b) (h2 : r₂ ≤ k₁) (h3 : r₁ + k₁ = c) :
    (b * a + c * d - d * r₁) - (a * r₁ + d * r₂) = a * (b - r₁) + d * (k₁ - r₂) := by
  rw [← h3, Nat.add_mul, Nat.mul_comm r₁ d, Nat.mul_comm k₁ d, Nat.mul_comm b a,
    Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
  have h4 : a * r₁ ≤ a * b := Nat.mul_le_mul_left a h1
  have h5 : d * r₂ ≤ d * k₁ := Nat.mul_le_mul_left d h2
  omega

/-! ## 4.2 The Künneth dimension formula at the other three degrees ($m = 0,1,2$)

Still with $R = 0$ ($H_0(\mathcal R) = \mathbb F_2^{\mathcal R_0}$ and
$H_1(\mathcal R) = \mathbb F_2^{\mathcal R_1}$ maximal, arbitrary differential on $C$),
the differential of the Koszul total complex reduces to the "$\partial \otimes
\mathrm{id}$" blocks, and the four degrees are read off block by block (the shapes of the
seven blocks of `koszulFaultComplex` when $R = 0$):

* $\partial_2 = \binom{M_3\ 0}{0\ 0}$ ($M_3 = \mathrm{id}\otimes\partial_2$); the $m=3$
  case of §4 uses its kernel;
* $\partial_1 = \binom{M_1\ 0}{0\ M_2}$ (**block-diagonal**:
  $M_1 = \mathrm{id}\otimes\partial_1$, $M_2 = \mathrm{id}\otimes\partial_2$);
* $\partial_0 = \binom{0\ N}{0\ 0}$ (**block-row**: $N = \mathrm{id}\otimes\partial_1$).

Thus the two block-shape lemmas of §4.1 and the engine of §3 give all four degrees; the
arithmetic for $m=1,2$ uses "$\mathrm{im}\,\partial_2 \subseteq \ker\partial_1$" (that is,
the CSS condition) once each. -/

/-- **The $m = 2$ degree of the Künneth formula on the degenerate family $R = 0$**
(machine-checked): $$\dim H_2(\mathcal R\otimes C) = |\mathcal R_1|\cdot\dim H_1(C)
  + |\mathcal R_0|\cdot\dim H_2(C).$$

Consistent with the general shape
$H_2 = H_1(\mathcal R)\otimes H_1(C)\oplus H_0(\mathcal R)\otimes H_2(C)$ of p.63 (both
factors are maximal when $R = 0$). -/
theorem kunneth_H2_R_zero [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH2 (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC)
      = Fintype.card R₁ * threeTermH1 dC1 dC2 + Fintype.card R₀ * threeTermH2 dC2 := by
  have h11 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d11_10
      = Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl
  have h01 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d11_01 = 0 := by
    rw [koszulFaultComplex_d11_01]
    exact Matrix.kronecker_zero _
  have h02 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d02_01
      = Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  have h12 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d12_11
      = Matrix.kronecker dC2 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl
  have h20 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d12_02 = 0 := by
    rw [koszulFaultComplex_d12_02]
    exact Matrix.kronecker_zero _
  rw [faultH2, h11, h01, h02, h12, h20]
  -- Replace the **instance path** of `fd1` / `fd2` by the `fromBlocks` form (the shape of
  -- the block dimension lemmas of §4.1): a direct `simp only [fd1]` unfolds only the main
  -- term, not the instance arguments of `Module.finrank`, so rw stops at "the same
  -- expression with a different instance".
  change Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
      (0 : Matrix (C₀ × R₁) (C₂ × R₀) (ZMod 2))
      (0 : Matrix (C₁ × R₀) (C₁ × R₁) (ZMod 2))
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
    - matRank (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₁ R₁ (ZMod 2)))
      (0 : Matrix (C₁ × R₁) (Fin 0) (ZMod 2))
      (0 : Matrix (C₂ × R₀) (C₂ × R₁) (ZMod 2))
      (0 : Matrix (C₂ × R₀) (Fin 0) (ZMod 2)))
    = Fintype.card R₁ * threeTermH1 dC1 dC2 + Fintype.card R₀ * threeTermH2 dC2
  simp only [finrank_ker_fromBlocks_diag, matRank_fromBlocks_diag, matRank_zero, add_zero,
    finrank_ker_kronecker_one, matRank_kronecker_one, threeTermH1, threeTermH2]
  exact arith_H2 (Fintype.card R₁) (Fintype.card R₀)
    (Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin))
    (Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)) (matRank dC2)
    (matRank_le_finrank_ker_of_mul_eq_zero dC1 dC2 hC)

/-- **The $m = 1$ degree of the Künneth formula on the degenerate family $R = 0$**
(machine-checked): $$\dim H_1(\mathcal R\otimes C) = |\mathcal R_1|\cdot\dim H_0(C)
  + |\mathcal R_0|\cdot\dim H_1(C).$$

The two bullets printed by p.63 are exactly what this becomes after dropping one whole
factor via $H_0(\mathcal R) = 0$ (repetition case) or $H_1(\mathcal R) = 0$ (dual case);
that specialisation is not made here, so both terms are present. -/
theorem kunneth_H1_R_zero [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH1 (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC)
      = Fintype.card R₁ * threeTermH0 dC1 + Fintype.card R₀ * threeTermH1 dC1 dC2 := by
  have h10 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d10_00 = 0 := by
    rw [koszulFaultComplex_d10_00]
    exact Matrix.kronecker_zero _
  have h12 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d11_01 = 0 := by
    rw [koszulFaultComplex_d11_01]
    exact Matrix.kronecker_zero _
  have h01 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d01_00
      = Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  have h11 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d11_10
      = Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl
  have h02 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d02_01
      = Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  rw [faultH1, h10, h01, h11, h12, h02]
  -- As in `kunneth_H2_R_zero`: first replace the instance path of `fd0` / `fd1` by the
  -- `fromBlocks` form
  change Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks
      (0 : Matrix (C₀ × R₀) (C₀ × R₁) (ZMod 2))
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
      (0 : Matrix (Fin 0) (C₀ × R₁) (ZMod 2))
      (0 : Matrix (Fin 0) (C₁ × R₀) (ZMod 2))).mulVecLin)
    - matRank (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
      (0 : Matrix (C₀ × R₁) (C₂ × R₀) (ZMod 2))
      (0 : Matrix (C₁ × R₀) (C₁ × R₁) (ZMod 2))
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2))))
    = Fintype.card R₁ * threeTermH0 dC1 + Fintype.card R₀ * threeTermH1 dC1 dC2
  rw [finrank_ker_eq_card_sub_matRank, matRank_fromBlocks_zeroLeft]
  simp only [matRank_fromBlocks_diag, matRank_kronecker_one]
  have hcardT1 : Fintype.card (FaultTerm1 (C₀ × R₁) (C₁ × R₀))
      = Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀ := by
    simp [FaultTerm1, Fintype.card_prod]
  have hH0 : threeTermH0 dC1 = Fintype.card C₀ - matRank dC1 := by
    have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range dC1.mulVecLin)
    have hd : Module.finrank (ZMod 2) (C₀ → ZMod 2) = Fintype.card C₀ :=
      Module.finrank_fintype_fun_eq_card (ZMod 2)
    simp only [threeTermH0, matRank, hd] at hq ⊢
    omega
  have hle : matRank dC1 ≤ Fintype.card C₀ := by
    have h := twoTermH0_add_matRank dC1
    simp only [twoTermH0] at h
    omega
  have hrn : matRank dC1 + Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
      = Fintype.card C₁ := by
    have h := twoTermH1_add_matRank dC1
    simp only [twoTermH1] at h
    omega
  rw [hcardT1, threeTermH1, hH0]
  exact arith_H1 (Fintype.card R₁) (Fintype.card C₀) (Fintype.card C₁) (Fintype.card R₀)
    (Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)) (matRank dC1) (matRank dC2)
    hle (matRank_le_finrank_ker_of_mul_eq_zero dC1 dC2 hC) hrn

/-- **The $m = 0$ degree of the Künneth formula on the degenerate family $R = 0$**
(machine-checked): $$\dim H_0(\mathcal R\otimes C) = |\mathcal R_0|\cdot\dim H_0(C).$$

Consistent with the general shape $H_0 = H_0(\mathcal R)\otimes H_0(C)$ (for $R = 0$,
$H_0(\mathcal R) = \mathbb F_2^{\mathcal R_0}$); this one p.63 does not print. -/
theorem kunneth_H0_R_zero [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH0 (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC)
      = Fintype.card R₀ * threeTermH0 dC1 := by
  have h10 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d10_00 = 0 := by
    rw [koszulFaultComplex_d10_00]
    exact Matrix.kronecker_zero _
  have h01 : (koszulFaultComplex (0 : Matrix R₀ R₁ (ZMod 2)) dC1 dC2 hC).d01_00
      = Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  rw [faultH0, h10, h01]
  -- As in `kunneth_H2_R_zero`: first replace the instance path of `fd0` by the
  -- `fromBlocks` form
  change Module.finrank (ZMod 2) ((FaultTerm0 (C₀ × R₀) → ZMod 2) ⧸
      LinearMap.range (Matrix.fromBlocks
        (0 : Matrix (C₀ × R₀) (C₀ × R₁) (ZMod 2))
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
        (0 : Matrix (Fin 0) (C₀ × R₁) (ZMod 2))
        (0 : Matrix (Fin 0) (C₁ × R₀) (ZMod 2))).mulVecLin)
    = Fintype.card R₀ * threeTermH0 dC1
  rw [finrank_quotient_range_eq, matRank_fromBlocks_zeroLeft, matRank_kronecker_one]
  have hcard : Fintype.card (FaultTerm0 (C₀ × R₀)) = Fintype.card C₀ * Fintype.card R₀ := by
    simp [FaultTerm0, Fintype.card_prod]
  have hH0 : threeTermH0 dC1 = Fintype.card C₀ - matRank dC1 := by
    have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range dC1.mulVecLin)
    have hd : Module.finrank (ZMod 2) (C₀ → ZMod 2) = Fintype.card C₀ :=
      Module.finrank_fintype_fun_eq_card (ZMod 2)
    simp only [threeTermH0, matRank, hd] at hq ⊢
    omega
  have hle : matRank dC1 ≤ Fintype.card C₀ := by
    have h := twoTermH0_add_matRank dC1
    simp only [twoTermH0] at h
    omega
  rw [hcard, hH0]
  exact arith_H0 (Fintype.card C₀) (Fintype.card R₀) (matRank dC1) hle

/-! ### 4.4 The block-column $\binom{A\ 0}{B\ 0}$: the shape of `fd2` when $R \ne 0$

For $R = 0$ the second block `d12_02` of `fd2` is a zero block
(`Matrix.kronecker_zero`), and the two "only the top-left block is nonzero" shapes of §4
suffice; for $R \ne 0$ it is $\mathrm{id}\otimes R$, so `fd2` becomes the **block-column**
$\binom{\mathrm{id}\otimes\partial_2}{1\otimes R}$: the two blocks have the **same column
index** (both $F_{1,2}$), and the kernel is the **intersection** of the two kernels rather
than their sum. This section supplies the dimension lemma for that shape, again by the
method of §4.1 (an explicit $\simeq_\ell$, then read the dimension). -/

/-- **The component formula for the block-column $\binom{A\ 0}{B\ 0}$ (the `inl` row)**
(the second column block has the empty index `Fin 0`):

$$\Bigl(\binom{A\ 0}{B\ 0}\cdot x\Bigr)_{(\mathrm{inl}\,p)}
  = \bigl(A \cdot (x \circ \mathrm{inl})\bigr)_p.$$ -/
theorem fromBlocks_col_mulVec_apply_inl {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q] (A : Matrix P₁ Q (ZMod 2)) (B : Matrix P₂ Q (ZMod 2))
    (x : (Q ⊕ Fin 0) → ZMod 2) (p : P₁) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2)) B
        (0 : Matrix P₂ (Fin 0) (ZMod 2))) *ᵥ x) (Sum.inl p)
      = (A *ᵥ (fun q => x (Sum.inl q))) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- As above, the `inr` row gives the $B$ block (one of the two differences from
`fromBlocks_fin0` of §4). -/
theorem fromBlocks_col_mulVec_apply_inr {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q] (A : Matrix P₁ Q (ZMod 2)) (B : Matrix P₂ Q (ZMod 2))
    (x : (Q ⊕ Fin 0) → ZMod 2) (p : P₂) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2)) B
        (0 : Matrix P₂ (Fin 0) (ZMod 2))) *ᵥ x) (Sum.inr p)
      = (B *ᵥ (fun q => x (Sum.inl q))) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- **The kernel of the block-column $\binom{A\ 0}{B\ 0}$** (the second column block has
the empty index `Fin 0`): isomorphic to $\ker A \cap \ker B$.

(A vector over $Q \oplus \mathrm{Fin}\ 0$ is fully determined by its half over $Q$, so the
kernel condition is "the two kernels hold simultaneously", exactly the constraint imposed
by the extra block of `fd2` when $R \ne 0$.) -/
def kerFromBlocksColEquiv {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q]
    (A : Matrix P₁ Q (ZMod 2)) (B : Matrix P₂ Q (ZMod 2)) :
    ↥(LinearMap.ker (Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2))
        B (0 : Matrix P₂ (Fin 0) (ZMod 2))).mulVecLin)
      ≃ₗ[ZMod 2] ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) where
  toFun x :=
    ⟨fun q => (x : (Q ⊕ Fin 0) → ZMod 2) (Sum.inl q), by
      have hx : (Matrix.fromBlocks A (0 : Matrix P₁ (Fin 0) (ZMod 2)) B
          (0 : Matrix P₂ (Fin 0) (ZMod 2))) *ᵥ (x : (Q ⊕ Fin 0) → ZMod 2) = 0 :=
        LinearMap.mem_ker.mp x.2
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · funext p
        have hxy := congrFun hx (Sum.inl p)
        rw [fromBlocks_col_mulVec_apply_inl] at hxy
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using hxy
      · funext p
        have hxy := congrFun hx (Sum.inr p)
        rw [fromBlocks_col_mulVec_apply_inr] at hxy
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using hxy⟩
  invFun z :=
    ⟨fun p => match p with
      | Sum.inl q => (z : Q → ZMod 2) q
      | Sum.inr e => Fin.elim0 e, by
      funext p
      cases p with
      | inl q =>
        rw [Matrix.mulVecLin_apply, fromBlocks_col_mulVec_apply_inl]
        have hz : A *ᵥ (z : Q → ZMod 2) = 0 :=
          LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hz q
      | inr e =>
        rw [Matrix.mulVecLin_apply, fromBlocks_col_mulVec_apply_inr]
        have hz : B *ᵥ (z : Q → ZMod 2) = 0 :=
          LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hz e⟩
  map_add' x y := Subtype.ext (funext fun q => rfl)
  map_smul' c x := Subtype.ext (funext fun q => rfl)
  left_inv x := by
    ext p
    cases p with
    | inl q => rfl
    | inr e => exact Fin.elim0 e
  right_inv z := Subtype.ext (funext fun q => rfl)

/-- **The kernel dimension of a block-column**:
$\dim\ker\binom{A\ 0}{B\ 0} = \dim(\ker A \cap \ker B)$.

This is the lemma missing for the shape of `fd2` when $R \ne 0$. -/
theorem finrank_ker_fromBlocks_col {P₁ P₂ Q : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q]
    (A : Matrix P₁ Q (ZMod 2)) (B : Matrix P₂ Q (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks A
        (0 : Matrix P₁ (Fin 0) (ZMod 2)) B (0 : Matrix P₂ (Fin 0) (ZMod 2))).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) :=
  (kerFromBlocksColEquiv A B).finrank_eq

/-! ### 4.5 A cycle $\otimes$ a cycle lands in $\ker\partial_2$ when $R \ne 0$

Over general $R$, the step "$\dim H_3 = \dim H_1(\mathcal R)\cdot\dim H_2(C)$" is
mathematically the conclusion of the Künneth theorem for tensor products of complexes. Its
**inclusion direction** needs no general theory of tensor products: an element can be
written directly as the coordinatewise product `tensorVec c r`. This section machine-checks
that direction:

* the first block of $\partial_2$ acts only on the indices of the $C$ side, the second only
  on the indices of the $\mathcal R$ side;
* hence when $c$ is a cycle of $C$ and $r$ a cycle of $\mathcal R$, `tensorVec c r` is
  killed by both blocks, i.e. lies in $\ker\partial_2$.

The **converse direction** of this inclusion (that it is surjective, i.e. the dimension
count) is machine-checked in §4.9, giving
$\dim H_3 = \dim H_1(\mathcal R)\cdot\dim H_2(C)$. -/

/-- **The component formula for the Kronecker $\mathrm{id}\otimes A$** (the mirror of the
one in §3, with `1` on the left):

$$\bigl((\mathrm{id}_\alpha\otimes A)\cdot x\bigr)_{(i,i')} = \sum_j A_{i'j}\,x_{(i,j)}.$$ -/
theorem kroneckerMap_one_left_mulVec_apply {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq α] (A : Matrix ι κ (ZMod 2)) (x : α × κ → ZMod 2) (i : α) (i' : ι) :
    ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) A) *ᵥ x) (i, i')
      = ∑ j, A i' j * x (i, j) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro a _ ha
    simp only [Matrix.one_apply_ne (Ne.symm ha), zero_mul, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The tensor of two vectors** (coordinatewise product):
$\mathtt{tensorVec}\ c\ r\ (a,b) = c_a\,r_b$.

It turns "a cycle of $\mathcal R$ $\times$ a cycle of $C$" into a concrete vector of
$\mathcal R\otimes C$, so the inclusion direction needs no tensor-product space built
first. -/
def tensorVec {β ι : Type*} (c : β → ZMod 2) (r : ι → ZMod 2) : β × ι → ZMod 2 :=
  fun p => c p.1 * r p.2

/-- **A tensor of cycles lies in the kernel of $A\otimes\mathrm{id}$**: when $c$ is a
cycle of $A$, $(A\otimes\mathrm{id})\cdot(c\otimes r) = 0$ (independently of $r$). -/
theorem tensorVec_mulVec_kronecker_one_eq_zero {α β ι : Type*} [Fintype α] [Fintype β]
    [Fintype ι] [DecidableEq ι] (A : Matrix α β (ZMod 2)) {c : β → ZMod 2}
    {r : ι → ZMod 2} (hc : A *ᵥ c = 0) (i : α) (i' : ι) :
    ((Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix ι ι (ZMod 2))) *ᵥ tensorVec c r)
        (i, i') = 0 := by
  rw [kroneckerMap_one_mulVec_apply]
  have hcol : (A *ᵥ c) i = ∑ j, A i j * c j := rfl
  calc ∑ j, A i j * (c j * r i') = ∑ j, (A i j * c j) * r i' := by
        refine Finset.sum_congr rfl (fun j _ => by ring)
    _ = (∑ j, A i j * c j) * r i' := by rw [Finset.sum_mul]
    _ = (A *ᵥ c) i * r i' := by rw [hcol]
    _ = 0 := by rw [hc]; simp

/-- **A tensor of cycles lies in the kernel of $\mathrm{id}\otimes R$**: when $r$ is a
cycle of $R$, $(\mathrm{id}\otimes R)\cdot(c\otimes r) = 0$ (independently of $c$). -/
theorem tensorVec_mulVec_kronecker_one_left_eq_zero {α ι κ : Type*} [Fintype α] [Fintype ι]
    [Fintype κ] [DecidableEq α] (R : Matrix ι κ (ZMod 2)) {c : α → ZMod 2}
    {r : κ → ZMod 2} (hr : R *ᵥ r = 0) (i : α) (i' : ι) :
    ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) R) *ᵥ tensorVec c r)
        (i, i') = 0 := by
  rw [kroneckerMap_one_left_mulVec_apply]
  have hrow : (R *ᵥ r) i' = ∑ j, R i' j * r j := rfl
  calc ∑ j, R i' j * (c i * r j) = c i * (∑ j, R i' j * r j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => by ring)
    _ = c i * (R *ᵥ r) i' := by rw [hrow]
    _ = 0 := by rw [hr]; simp

/-- **A cycle $\otimes$ a cycle lies in $\ker\partial_2$ when $R \ne 0$** (the Künneth
inclusion direction):

When $c$ is a second-order cycle of $C$ and $r$ a cycle of $\mathcal R$ (the same block
$R$), `tensorVec c r` (padded with the empty fourth-term index) is killed by `fd2`. -/
theorem koszulTensorVec_fd2_eq_zero {C₀ C₁ C₂ R₀ R₁ : Type*} [Fintype C₀] [Fintype C₁]
    [Fintype C₂] [Fintype R₀] [Fintype R₁] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂] [DecidableEq R₀] [DecidableEq R₁]
    (R : Matrix R₀ R₁ (ZMod 2)) {dC1 : Matrix C₀ C₁ (ZMod 2)} {dC2 : Matrix C₁ C₂ (ZMod 2)}
    {hC : dC1 * dC2 = 0} {c : C₂ → ZMod 2} {r : R₁ → ZMod 2}
    (hc : dC2 *ᵥ c = 0) (hr : R *ᵥ r = 0) :
    fd2 (koszulFaultComplex R dC1 dC2 hC).d12_11 (koszulFaultComplex R dC1 dC2 hC).d12_02
        *ᵥ (fun p => match p with
          | Sum.inl q => tensorVec c r q
          | Sum.inr e => Fin.elim0 e) = 0 := by
  rw [koszulFaultComplex_d12_11, koszulFaultComplex_d12_02]
  funext p
  cases p with
  | inl p =>
    rw [fd2, fromBlocks_col_mulVec_apply_inl]
    exact tensorVec_mulVec_kronecker_one_eq_zero dC2 hc p.1 p.2
  | inr p =>
    rw [fd2, fromBlocks_col_mulVec_apply_inr]
    exact tensorVec_mulVec_kronecker_one_left_eq_zero R hr p.1 p.2

/-! ### 4.6 Scaffolding for the last step: moving "act along one index" to module-valued tuples

The **last step** of $\dim H_3 = \dim H_1(\mathcal R)\cdot\dim H_2(C)$ over general $R$
is a dimension count. The shape it needs is: under currying,
$\ker(\mathrm{id}\otimes\partial_2)\cap\ker(1\otimes R)$ becomes
$$\{v : \mathcal R_1 \to \ker\partial_2 : \text{acting along $\mathcal R_1$ by $R$ is zero}\},$$
whose dimension is $\dim\ker\partial_2 \cdot \dim\ker R$ (the tensor product of the kernel
of $R$ with "tuples of values in $\ker\partial_2$"). This section sets up the objects that
shape needs and machine-checks half of it:

* `piMulVec` writes "act along one index" as a linear map with **values in an arbitrary
  $\mathbb F_2$-module** (for $M = \ker\partial_2$ it is the shape of
  $R\otimes\mathrm{id}_M$);
* its kernel **contains at least "a cycle $\otimes$ an arbitrary element"**
  (`tupleTensor_mem_ker_piMulVec`, for any $M$).

**The dimension count itself is still not done** (see §5): it is an equality rather than
an inclusion, and needs the kernel to be spanned exactly by those elements. -/

/-- **Acting along $\iota$**: $(\mathtt{piMulVec}\ R\ v)_k = \sum_j R_{kj}\,v_j$.

When $M$ is a subspace type (such as $\ker\partial_2$), this is the shape of
$R\otimes\mathrm{id}_M$ on tuple space. -/
def piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*} [AddCommMonoid M]
    [Module (ZMod 2) M] (R : Matrix κ ι (ZMod 2)) : (ι → M) →ₗ[ZMod 2] (κ → M) where
  toFun v := fun k => ∑ j, R k j • v j
  map_add' v w := by
    funext k
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext k
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm])

/-- The evaluation formula for acting along $\iota$ (the definitional unfolding). -/
theorem piMulVec_apply {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*} [AddCommMonoid M]
    [Module (ZMod 2) M] (R : Matrix κ ι (ZMod 2)) (v : ι → M) (k : κ) :
    piMulVec R v k = ∑ j, R k j • v j := rfl

/-- **The outer product of a vector and an element**:
$\mathtt{tupleTensor}\ a\ m\ j = a_j \bullet m$.

When $a$ is a cycle and $M = \ker\partial_2$, it is the tuple obtained by multiplying an
element of $H_2(C)$ with an element of $H_1(\mathcal R)$, that is, the concrete vector the
inclusion direction needs. -/
def tupleTensor {ι : Type*} (a : ι → ZMod 2) {M : Type*} [SMul (ZMod 2) M] (m : M) : ι → M :=
  fun j => a j • m

/-- **The outer product of a cycle and an arbitrary element lies in the kernel of acting
along $\iota$** (for any $M$): when $R\cdot a = 0$,
$\mathtt{piMulVec}\ R\ (\mathtt{tupleTensor}\ a\ m) = 0$. -/
theorem tupleTensor_mem_ker_piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommMonoid M] [Module (ZMod 2) M] (R : Matrix κ ι (ZMod 2)) {a : ι → ZMod 2}
    (ha : R *ᵥ a = 0) (m : M) :
    piMulVec R (tupleTensor a m) = 0 := by
  funext k
  rw [piMulVec_apply, Pi.zero_apply]
  have hk : (R *ᵥ a) k = ∑ j, R k j * a j := rfl
  calc ∑ j, R k j • (a j • m) = ∑ j, (R k j * a j) • m := by
        refine Finset.sum_congr rfl (fun j _ => by rw [smul_smul])
    _ = (∑ j, R k j * a j) • m := by rw [Finset.sum_smul]
    _ = (R *ᵥ a) k • m := by rw [hk]
    _ = 0 := by rw [ha]; simp

/-! ### 4.7 The Π-type engine: the coordinate case

§4.6 set up `piMulVec` (with arbitrary module values). This section computes its **kernel
dimension** when $M$ is a coordinate space ($M = \alpha \to \mathbb F_2$):
$|\alpha| \cdot \dim\ker R$. The method is to **rearrange** tuple space into
$(\iota \times \alpha \to \mathbb F_2)$; after the rearrangement `piMulVec R` **is** the
shape $R\otimes\mathrm{id}_\alpha$ of the existing engine
(`finrank_ker_kronecker_one` of §3), so the dimension is read off directly.

For a general module $M$ (such as $\ker\partial_2$) **one more step follows**: move tuple
space to coordinate space along a basis of $M$ (an equivalence that commutes with
`piMulVec R` coordinatewise). That move is still not done, see §5. -/

/-- **The Π-type rearrangement**: $(\iota \to \alpha \to M) \simeq_\ell
(\iota \times \alpha \to M)$ (both directions move coordinates individually, so every law
is `rfl`). -/
def piCurry (ι α : Type*) (M : Type*) [AddCommMonoid M] [Module (ZMod 2) M] :
    (ι → α → M) ≃ₗ[ZMod 2] (ι × α → M) where
  toFun f := fun p => f p.1 p.2
  invFun g := fun i a => g (i, a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The evaluation formula for the rearrangement (the definitional unfolding). -/
@[simp] theorem piCurry_apply {ι α : Type*} {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (f : ι → α → M) (i : ι) (a : α) : piCurry ι α M f (i, a) = f i a := rfl

/-- **After the rearrangement, `piMulVec` is $R \otimes \mathrm{id}_\alpha$** (the
coordinate case):

$$\mathrm{piCurry}\ (\mathrm{piMulVec}\ R\ v) = (R\otimes\mathrm{id}_\alpha)\cdot
\mathrm{piCurry}\ v.$$ -/
theorem piCurry_piMulVec {κ ι α : Type*} [Fintype κ] [Fintype ι] [Fintype α]
    [DecidableEq α] (R : Matrix κ ι (ZMod 2)) (v : ι → α → ZMod 2) :
    piCurry κ α (ZMod 2) (piMulVec (M := α → ZMod 2) R v)
      = (Matrix.kroneckerMap (fun a b => a * b) R (1 : Matrix α α (ZMod 2))) *ᵥ
          piCurry ι α (ZMod 2) v := by
  funext p
  obtain ⟨k, a⟩ := p
  rw [kroneckerMap_one_mulVec_apply, piCurry_apply, piMulVec_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, piCurry_apply]

/-- **The Π-type rearrangement matches the two kernels**: transported along `piCurry`, the
kernel of `piMulVec R` is isomorphic to the kernel of $R\otimes\mathrm{id}_\alpha$. -/
def kerPiMulVecEquiv {κ ι α : Type*} [Fintype κ] [Fintype ι] [Fintype α] [DecidableEq α]
    (R : Matrix κ ι (ZMod 2)) :
    ↥(LinearMap.ker (piMulVec (M := α → ZMod 2) R))
      ≃ₗ[ZMod 2] ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) R
          (1 : Matrix α α (ZMod 2))).mulVecLin) where
  toFun v :=
    ⟨piCurry ι α (ZMod 2) v.1, by
      have hv : (piMulVec (M := α → ZMod 2) R) v.1 = 0 := (LinearMap.mem_ker).mp v.2
      have h := piCurry_piMulVec R (v.1 : ι → α → ZMod 2)
      rw [hv, map_zero] at h
      simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using h.symm⟩
  invFun w :=
    ⟨(piCurry ι α (ZMod 2)).symm w.1, by
      have hw : (Matrix.kroneckerMap (fun a b => a * b) R
          (1 : Matrix α α (ZMod 2))) *ᵥ w.1 = 0 := by
        simpa only [Matrix.mulVecLin_apply] using (LinearMap.mem_ker).mp w.2
      have h := piCurry_piMulVec R ((piCurry ι α (ZMod 2)).symm w.1)
      rw [LinearEquiv.apply_symm_apply, hw] at h
      exact (piCurry κ α (ZMod 2)).injective (by rw [h, map_zero])⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)
  left_inv v := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

/-- **The Π engine in the coordinate case**: $\dim\ker(\mathrm{piMulVec}\ R)$
(with $M = \alpha \to \mathbb F_2$) $= |\alpha| \cdot \dim\ker R$. -/
theorem finrank_ker_piMulVec_coord {κ ι α : Type*} [Fintype κ] [Fintype ι] [Fintype α]
    [DecidableEq α] (R : Matrix κ ι (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (piMulVec (M := α → ZMod 2) R))
      = Fintype.card α * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) :=
  (kerPiMulVecEquiv R).finrank_eq.trans (finrank_ker_kronecker_one (α := κ) (β := ι) (ι := α) R)

/-! ### 4.8 General module: moving values to coordinates along a basis

§4.7 computed the kernel dimension in the coordinate case. This section reduces the case
of an **arbitrary** finite-dimensional $M$ to it: a basis of $M$ (`Module.finBasis`) gives
$M \simeq_\ell \mathbb F_2^{r}$, acting componentwise on tuple space, and this transport
**commutes with `piMulVec R`** (`piMapEquiv_piMulVec`), so the kernel dimension is
unchanged and the general formula is read off from the coordinate case. -/

/-- **Moving values to coordinates**: the tuple-space equivalence induced componentwise by
$M \simeq_\ell \mathbb F_2^r$. -/
def piMapEquiv {ι : Type*} {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M] (r : ℕ)
    (e : M ≃ₗ[ZMod 2] (Fin r → ZMod 2)) : (ι → M) ≃ₗ[ZMod 2] (ι → Fin r → ZMod 2) :=
  LinearEquiv.piCongrRight fun _ => e

/-- **The transport commutes with `piMulVec`**: taking coordinates componentwise does not
change the result of "acting along an index". -/
theorem piMapEquiv_piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommMonoid M] [Module (ZMod 2) M] (r : ℕ) (e : M ≃ₗ[ZMod 2] (Fin r → ZMod 2))
    (R : Matrix κ ι (ZMod 2)) (v : ι → M) :
    piMapEquiv r e (piMulVec (M := M) R v)
      = piMulVec (M := Fin r → ZMod 2) R (piMapEquiv r e v) := by
  funext k a
  simp only [piMapEquiv, LinearEquiv.piCongrRight_apply, piMulVec_apply, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The transport to coordinates matches the two kernels. -/
def kerPiMulVecCongr {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*} [AddCommMonoid M]
    [Module (ZMod 2) M] (r : ℕ) (e : M ≃ₗ[ZMod 2] (Fin r → ZMod 2))
    (R : Matrix κ ι (ZMod 2)) :
    ↥(LinearMap.ker (piMulVec (M := M) R))
      ≃ₗ[ZMod 2] ↥(LinearMap.ker (piMulVec (M := Fin r → ZMod 2) R)) where
  toFun v :=
    ⟨piMapEquiv r e v.1, by
      have hv : (piMulVec (M := M) R) v.1 = 0 := (LinearMap.mem_ker).mp v.2
      have h := piMapEquiv_piMulVec r e R v.1
      rw [hv, map_zero] at h
      simpa only [LinearMap.mem_ker] using h.symm⟩
  invFun w :=
    ⟨(piMapEquiv r e).symm w.1, by
      have hw : (piMulVec (M := Fin r → ZMod 2) R) w.1 = 0 := (LinearMap.mem_ker).mp w.2
      have h := piMapEquiv_piMulVec r e R ((piMapEquiv r e).symm w.1)
      rw [LinearEquiv.apply_symm_apply, hw] at h
      exact (piMapEquiv r e).injective (by rw [h, map_zero])⟩
  map_add' v w := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)
  left_inv v := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

/-- **The Π engine for a general module**: $\dim\ker(\mathrm{piMulVec}\ R)
= \dim M \cdot \dim\ker R$ (for any finite-dimensional $M$); move to coordinates along a
basis of $M$, then use §4.7. -/
theorem finrank_ker_piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    (R : Matrix κ ι (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (piMulVec (M := M) R))
      = Module.finrank (ZMod 2) M * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) := by
  have h := (kerPiMulVecCongr (Module.finrank (ZMod 2) M)
    (Module.finBasis (ZMod 2) M).equivFun R).finrank_eq
  rw [h, finrank_ker_piMulVec_coord R, Fintype.card_fin]

/-- **The rank version of the Π engine**:
$\dim\mathrm{im}(\mathrm{piMulVec}\ R) = \dim M\cdot\mathrm{rank}\,R$ (the dual of the
previous lemma, via rank-nullity; it is needed for the "intersection of images" term at
the remaining three degrees). -/
theorem finrank_range_piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    (R : Matrix κ ι (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (piMulVec (M := M) R))
      = Module.finrank (ZMod 2) M * matRank R := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (piMulVec (M := M) R)
  have hker := finrank_ker_piMulVec (M := M) R
  have hdom : Module.finrank (ZMod 2) (ι → M) = Fintype.card ι * Module.finrank (ZMod 2) M :=
    finrank_const_pi (ι := ι) (M := M)
  have hrnA := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  have hdomA : Module.finrank (ZMod 2) (ι → ZMod 2) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have key : Module.finrank (ZMod 2) ↥(LinearMap.range (piMulVec (M := M) R))
      + Module.finrank (ZMod 2) M
        * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
      = Fintype.card ι * Module.finrank (ZMod 2) M := by
    rw [hker, hdom] at hrn
    exact hrn
  have keyA : Module.finrank (ZMod 2) ↥(LinearMap.range R.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) = Fintype.card ι := by
    rw [hdomA] at hrnA
    exact hrnA
  have hmain : Module.finrank (ZMod 2) ↥(LinearMap.range (piMulVec (M := M) R))
      = Module.finrank (ZMod 2) M
        * (Fintype.card ι - Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)) := by
    rw [Nat.mul_comm (Fintype.card ι) (Module.finrank (ZMod 2) M)] at key
    rw [Nat.mul_sub]
    omega
  rw [hmain]
  congr 1
  rw [matRank]
  omega

/-! ### 4.9 The interface: under currying the intersection is the tuple kernel (general $R$)

The last step. `kerKroneckerOneEquiv` of §3 identifies
$\ker(A\otimes\mathrm{id}_\iota)$ with $(\iota \to \ker A)$; under this identification,
"$(1\otimes R)$ is zero" **is** "the tuple is killed by `piMulVec R`" (immediate by
expanding coordinatewise). Hence

$$\dim\Bigl(\ker(A\otimes\mathrm{id})\cap\ker(1\otimes R)\Bigr)
  = \dim\ker\bigl(\mathrm{piMulVec}\ R\ \text{on}\ \iota \to \ker A\bigr)
  = \dim\ker A \cdot \dim\ker R$$

(the last step is §4.8). Attaching this chain to the block-column shape of `fd2` and the
two blocks of `fd1` gives the $H_3$ of p.63 over **general $R$**:
$\dim H_3 = \dim H_1(\mathcal R)\cdot\dim H_2(C)$ (`kunneth_H3`). -/

/-- **The pointwise form of the interface**: the value of $(1\otimes R)\cdot x$ at
$(j,k)$ equals the value at $j$ of the $k$-th component of `piMulVec R` after currying. -/
theorem kronecker_one_mulVec_eq_piMulVec {α β ι κ : Type*} [Fintype α] [Fintype β]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq β] (A : Matrix α β (ZMod 2))
    (R : Matrix κ ι (ZMod 2))
    (x : ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
        (1 : Matrix ι ι (ZMod 2))).mulVecLin)) :
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix β β (ZMod 2)) R) *ᵥ
        (x : β × ι → ZMod 2)
      = fun p => ((piMulVec (M := ↥(LinearMap.ker A.mulVecLin)) R
          (kerKroneckerOneEquiv A x)) p.2 : β → ZMod 2) p.1 := by
  funext p
  obtain ⟨j, k⟩ := p
  rw [kroneckerMap_one_left_mulVec_apply, piMulVec_apply]
  have hcoe : ((∑ l, R k l • (kerKroneckerOneEquiv A x) l :
        ↥(LinearMap.ker A.mulVecLin)) : β → ZMod 2)
      = ∑ l, R k l • ((kerKroneckerOneEquiv A x) l : β → ZMod 2) := by
    simpa only [Submodule.subtype_apply, map_smul] using
      (map_sum (Submodule.subtype (LinearMap.ker A.mulVecLin))
        (fun l => R k l • (kerKroneckerOneEquiv A x) l) Finset.univ)
  rw [hcoe, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul]
  rfl

/-- **$(1\otimes R)$ is zero $\iff$ the tuple is killed by `piMulVec R`** (on
$\ker(A\otimes\mathrm{id})$). -/
theorem kronecker_one_eq_zero_iff {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq β] (A : Matrix α β (ZMod 2)) (R : Matrix κ ι (ZMod 2))
    (x : ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
        (1 : Matrix ι ι (ZMod 2))).mulVecLin)) :
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix β β (ZMod 2)) R) *ᵥ
        (x : β × ι → ZMod 2) = 0
      ↔ piMulVec (M := ↥(LinearMap.ker A.mulVecLin)) R (kerKroneckerOneEquiv A x) = 0 := by
  rw [kronecker_one_mulVec_eq_piMulVec A R x]
  constructor
  · intro h
    funext k
    refine Subtype.ext (funext fun j => ?_)
    exact congrFun h (j, k)
  · intro h
    funext p
    obtain ⟨j, k⟩ := p
    exact congrArg (fun w : ↥(LinearMap.ker A.mulVecLin) => (w : β → ZMod 2) j)
      (congrFun h k)

/-- The intersection and the tuple kernel have equal dimension (via the currying interface). -/
theorem finrank_inf_ker_kronecker {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq β] (A : Matrix α β (ZMod 2)) (R : Matrix κ ι (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
          (1 : Matrix ι ι (ZMod 2))).mulVecLin
        ⊓ LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b)
          (1 : Matrix β β (ZMod 2)) R).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (piMulVec (M := ↥(LinearMap.ker A.mulVecLin))
          R)) := by
  refine LinearEquiv.finrank_eq ?_
  refine
    { toFun := fun x => ⟨kerKroneckerOneEquiv A ⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun v => ⟨(kerKroneckerOneEquiv A).symm v.1, ?_⟩
      map_add' := fun x y => Subtype.ext
        (map_add (kerKroneckerOneEquiv A) ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩)
      map_smul' := fun c x => Subtype.ext
        (map_smul (kerKroneckerOneEquiv A) c ⟨x.1, x.2.1⟩)
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  · have hiff := kronecker_one_eq_zero_iff A R ⟨x.1, x.2.1⟩
    have hx : (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix β β (ZMod 2)) R) *ᵥ
        (x.1 : β × ι → ZMod 2) = 0 := by
      simpa only [Matrix.mulVecLin_apply] using (LinearMap.mem_ker).mp x.2.2
    simpa only [LinearMap.mem_ker] using hiff.mp hx
  · have hv : piMulVec (M := ↥(LinearMap.ker A.mulVecLin)) R v.1 = 0 :=
      (LinearMap.mem_ker).mp v.2
    refine Submodule.mem_inf.mpr ⟨((kerKroneckerOneEquiv A).symm v.1).2, ?_⟩
    have hiff := kronecker_one_eq_zero_iff A R ((kerKroneckerOneEquiv A).symm v.1)
    rw [LinearEquiv.apply_symm_apply] at hiff
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hiff.mpr hv

/-- **The $H_3$ of p.63 over general $R$**: $\dim H_3(\mathcal R\otimes C) =
\dim H_1(\mathcal R)\cdot\dim H_2(C)$. -/
theorem kunneth_H3 [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀] [DecidableEq C₁]
    [DecidableEq C₂] (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH3 (koszulFaultComplex R dC1 dC2 hC) = twoTermH1 R * threeTermH2 dC2 := by
  simp only [faultH3, twoTermH1, threeTermH2]
  rw [fd2, koszulFaultComplex_d12_11, koszulFaultComplex_d12_02, finrank_ker_fromBlocks_col]
  have h := finrank_inf_ker_kronecker (A := dC2) (R := R)
  have h2 := finrank_ker_piMulVec (M := ↥(LinearMap.ker dC2.mulVecLin)) R
  exact (h.trans h2).trans (Nat.mul_comm _ _)

/-! ### 4.10 The mirror engine: kernel and rank on the $\mathrm{id}_\alpha\otimes A$ side

The three items of §3 (the component formula, the currying isomorphism of the kernel, the
dimension formula) are all written for $A\otimes\mathrm{id}_\iota$. At the three degrees
remaining over general $R$, what appears in $\partial_0$ and $\partial_1$ is the
**mirror** $\mathrm{id}\otimes A$ (blocks `d11_01`, `d10_00`, `d12_02`), so this engine is
transported over first. There is nothing technically new: the component formula was already
machine-checked in §4.5 (`kroneckerMap_one_left_mulVec_apply`), and this subsection
completes its currying isomorphism and two dimension formulas, mirroring §3 item by item. -/

/-- The isomorphism (currying) between $\ker(\mathrm{id}_\alpha\otimes A)$ and
$\alpha \to \ker A$: the tuple index is the **factor on the left**. -/
def kerOneKroneckerEquiv {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq α] (A : Matrix ι κ (ZMod 2)) :
    ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2))
        A).mulVecLin) ≃ₗ[ZMod 2]
      (α → ↥(LinearMap.ker A.mulVecLin)) where
  toFun x := fun a =>
    ⟨fun j => (x : α × κ → ZMod 2) (a, j), by
      funext i'
      have hx : (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) A) *ᵥ
          (x : α × κ → ZMod 2) = 0 := x.2
      have hxy := congrFun hx (a, i')
      rw [kroneckerMap_one_left_mulVec_apply] at hxy
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] using hxy⟩
  invFun y :=
    ⟨fun p => (y p.1 : κ → ZMod 2) p.2, by
      funext p
      obtain ⟨i, i'⟩ := p
      have hxy := congrFun (y i).2 i'
      rw [Matrix.mulVecLin_apply] at hxy
      rw [Matrix.mulVecLin_apply, kroneckerMap_one_left_mulVec_apply]
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] using hxy⟩
  map_add' x y := by
    funext i'
    exact Subtype.ext (funext fun j => rfl)
  map_smul' c x := by
    funext i'
    exact Subtype.ext (funext fun j => rfl)
  left_inv x := by
    ext p
    rcases p with ⟨j, i'⟩
    rfl
  right_inv y := by
    funext i'
    exact Subtype.ext (funext fun j => rfl)

/-- **Kernel dimension (mirror)**:
$\dim\ker(\mathrm{id}_\alpha\otimes A) = |\alpha|\cdot\dim\ker A$. -/
theorem finrank_ker_one_kronecker {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq α] (A : Matrix ι κ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix α α (ZMod 2)) A).mulVecLin)
      = Fintype.card α * Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) := by
  rw [(kerOneKroneckerEquiv A).finrank_eq,
    finrank_const_pi (ι := α) (M := ↥(LinearMap.ker A.mulVecLin))]

/-- **Rank (mirror)**: $\mathrm{rank}(\mathrm{id}_\alpha\otimes A) = |\alpha|\cdot\mathrm{rank}\,A$
(rank-nullity plus the previous lemma). -/
theorem matRank_one_kronecker {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    [DecidableEq α] (A : Matrix ι κ (ZMod 2)) :
    matRank (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) A)
      = Fintype.card α * matRank A := by
  have hker := finrank_ker_one_kronecker (α := α) A
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) A).mulVecLin
  have hrnA := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdom : Module.finrank (ZMod 2) (α × κ → ZMod 2) = Fintype.card α * Fintype.card κ := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod]
  have hdomA : Module.finrank (ZMod 2) (κ → ZMod 2) = Fintype.card κ :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have key : matRank (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) A)
      + Fintype.card α * Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
      = Fintype.card α * Fintype.card κ := by
    rw [hker, hdom] at hrn
    rw [matRank]
    exact hrn
  have keyA : matRank A + Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
      = Fintype.card κ := by
    rw [hdomA] at hrnA
    rw [matRank]
    exact hrnA
  have hmain : matRank (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) A)
      = Fintype.card α * (Fintype.card κ
        - Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)) := by
    rw [Nat.mul_sub]
    omega
  rw [hmain]
  congr 1
  omega

/-! ### 4.11 The dimension of a preimage (the common lemma of the remaining three degrees)

$\dim f^{-1}(U) = \dim\ker f + \dim(\mathrm{im}\,f\cap U)$, obtained by applying
rank-nullity to the restriction of $f$ to $f^{-1}(U)$. It is precisely what the
"intersection of images" term at the remaining three degrees needs. -/

/-- **The dimension of a preimage**: $\dim f^{-1}(U) = \dim\ker f + \dim(\mathrm{im}\,f\cap U)$. -/
theorem finrank_comap_add {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) V]
    [Module.Finite (ZMod 2) W] (f : V →ₗ[ZMod 2] W) (U : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) ↥(Submodule.comap f U)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker f)
        + Module.finrank (ZMod 2) ↥(LinearMap.range f ⊓ U) := by
  -- The restriction map: `f` takes values on `f⁻¹(U)`, with target `im f ⊓ U`
  let g : ↥(Submodule.comap f U) →ₗ[ZMod 2] ↥(LinearMap.range f ⊓ U) :=
    { toFun := fun x => ⟨f x.1, ⟨⟨x.1, rfl⟩, x.2⟩⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  -- Kernel: `g x = 0 ⟺ f x = 0`
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker g)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker f) := by
    refine LinearEquiv.finrank_eq ?_
    exact
      { toFun := fun x =>
          ⟨x.1.1, congrArg (fun z : ↥(LinearMap.range f ⊓ U) => (z : W)) x.2⟩
        invFun := fun y =>
          ⟨⟨y.1, by rw [Submodule.mem_comap, y.2]; exact U.zero_mem⟩, Subtype.ext y.2⟩
        map_add' := fun x y => Subtype.ext rfl
        map_smul' := fun c x => Subtype.ext rfl
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  -- Image: `g` is surjective
  have hrange : Module.finrank (ZMod 2) ↥(LinearMap.range g)
      = Module.finrank (ZMod 2) ↥(LinearMap.range f ⊓ U) := by
    have htop : LinearMap.range g = ⊤ := by
      rw [LinearMap.range_eq_top]
      rintro ⟨w, hw, hwU⟩
      obtain ⟨v, hv⟩ := hw
      exact ⟨⟨v, by rw [Submodule.mem_comap, hv]; exact hwU⟩, Subtype.ext hv⟩
    rw [htop]
    exact LinearEquiv.finrank_eq Submodule.topEquiv
  omega

/-- **The intersection of an image with a subspace**: $\dim(\mathrm{im} f\cap U)
+ \mathrm{rank}(\pi_U\circ f) = \mathrm{rank}\,f$, where $\pi_U$ is the quotient map to
$W/U$.

Used together with the previous lemma: that one splits "preimage" into a kernel and an
intersection of images, this one turns the intersection of images into the **rank of the
quotient map** (the kernel of $\pi_U\circ f$ is exactly $f^{-1}(U)$, so subtracting the
two equations gives the result). -/
theorem finrank_inf_range_add_finrank_range_mkQ {V W : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) V]
    [Module.Finite (ZMod 2) W] (f : V →ₗ[ZMod 2] W) (U : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) ↥(LinearMap.range f ⊓ U)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (U.mkQ.comp f))
      = Module.finrank (ZMod 2) ↥(LinearMap.range f) := by
  have hcomap : LinearMap.ker (U.mkQ.comp f) = Submodule.comap f U := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mem_comap, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
  have hpre := finrank_comap_add f U
  have h2 := LinearMap.finrank_range_add_finrank_ker (U.mkQ.comp f)
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  rw [hcomap, hpre] at h2
  omega

/-! ### 4.12 The "intersection of images" term: the intersection of two images

Layer the kernel of
$\partial_2 = \binom{d_{1,1\to1,0}\ \ 0}{d_{1,1\to0,1}\ \ d_{0,2\to0,1}}$ as "first solve
$x$, then solve $y$": the fibre over $x$ is $\ker B$, and the $x$ in the image are exactly
those with $Cx\in\mathrm{im}B$. Hence

$$\dim\ker\partial_2 = \dim\{x\in\ker A : Cx\in\mathrm{im}B\} + \dim\ker B,$$

and `finrank_comap_add` (§4.11) splits the first term into a kernel and an intersection of
images:

$$\dim\{x\in\ker A : Cx\in\mathrm{im}B\} = \dim\ker A
  + \dim\bigl(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}B\bigr).$$

The first term $\dim\ker A$ and the third $\dim\ker B$ are direct instances of the
$\otimes\mathrm{id}$ engine of §3; what remains is **the middle term**, the
**intersection** of two images. It is not the kernel or image of any single matrix, and no
ready-made engine covers it (numerically it equals
$\mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R$, checked term by term by an independent probe).
This section computes it.

**Route**: replace "intersecting with an image" by "**the image after taking a quotient**":

$$\dim(\mathrm{im}f\cap\ker g) = \dim\mathrm{im}f - \dim\mathrm{im}(g\circ f),$$

(`finrank_inf_range_ker_sub`: both terms on the right are rank-nullity, so subtracting
gives it), and then take $g$ to be the map `piMapQ` that **takes quotients coordinatewise**.
Its kernel is exactly the block "every component lies in $S$", which is what
$\mathrm{im}B$ looks like on the "coordinatewise values" side. Both terms on the right then
fall back to the existing Π engine: $\dim\mathrm{im}f = \dim M\cdot\mathrm{rank}\,R$
(§4.8) and $\dim\mathrm{im}(g\circ f) = \dim(M/S)\cdot\mathrm{rank}\,R$, whose difference is
$\dim S\cdot\mathrm{rank}\,R$. This piece of middleware, "taking quotients coordinatewise",
commutes with "acting along an index" (`piMapQ_comp_piMulVec`), so the rank on the quotient
side returns to the same engine (`finrank_range_piMapQ_comp_piMulVec`). -/

/-- **The rank form of the quotient map**: $\dim(\mathrm{im}\,f\cap\ker g)
= \dim\mathrm{im}\,f - \dim\mathrm{im}(g\circ f)$.

An equivalent way to write "intersecting with $\ker g$" is "the quotient by $g$": both
quantities are written as rank-nullity, then `finrank_comap_add` connects
$\ker(g\circ f)=f^{-1}(\ker g)$, and subtracting gives the result. -/
theorem finrank_inf_range_ker_sub {V W W' : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup W'] [Module (ZMod 2) W']
    [Module.Finite (ZMod 2) V] [Module.Finite (ZMod 2) W]
    (f : V →ₗ[ZMod 2] W) (g : W →ₗ[ZMod 2] W') :
    Module.finrank (ZMod 2) ↥(LinearMap.range f ⊓ LinearMap.ker g)
      = Module.finrank (ZMod 2) ↥(LinearMap.range f)
        - Module.finrank (ZMod 2) ↥(LinearMap.range (g.comp f)) := by
  have hpre := finrank_comap_add f (LinearMap.ker g)
  have hker : LinearMap.ker (g.comp f) = Submodule.comap f (LinearMap.ker g) := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mem_comap]
  have h1 := LinearMap.finrank_range_add_finrank_ker (g.comp f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at h1
  omega

/-- **The coordinatewise quotient map**: $(w_j)_j \mapsto ([w_j])_j$, sending each
component into the quotient $M/S$.

It carries the reading "$\mathrm{im}B$ is exactly coordinatewise inside
$\mathrm{im}\,\partial_2$": taking $S = \mathrm{im}\,dC_2$, its kernel is exactly the block
"every component lies in $S$" from the start of §4.12. -/
def piMapQ {κ : Type*} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (S : Submodule (ZMod 2) M) : (κ → M) →ₗ[ZMod 2] (κ → M ⧸ S) where
  toFun w := fun j => S.mkQ (w j)
  map_add' w w' := by funext j; simp
  map_smul' c w := by funext j; simp

/-- The kernel of the coordinatewise quotient map = "the tuples every component of which
lies in $S$". -/
theorem ker_piMapQ {κ : Type*} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (S : Submodule (ZMod 2) M) :
    LinearMap.ker (piMapQ (κ := κ) S) = Submodule.pi Set.univ (fun _ : κ => S) := by
  ext w
  simp only [LinearMap.mem_ker, piMapQ, LinearMap.coe_mk, AddHom.coe_mk, funext_iff,
    Pi.zero_apply, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- The coordinatewise quotient map is surjective (pick one representative per component). -/
theorem range_piMapQ {κ : Type*} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (S : Submodule (ZMod 2) M) : LinearMap.range (piMapQ (κ := κ) S) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro w
  choose v hv using fun j => Submodule.mkQ_surjective S (w j)
  exact ⟨v, funext hv⟩

/-- **Coordinatewise quotienting commutes with "acting along an index"**: taking
quotients componentwise and then acting along $\iota$ equals acting first and then taking
quotients componentwise. -/
theorem piMapQ_comp_piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] (S : Submodule (ZMod 2) M)
    (R : Matrix κ ι (ZMod 2)) :
    (piMapQ (κ := κ) S).comp (piMulVec (M := M) R)
      = (piMulVec (M := M ⧸ S) R).comp (piMapQ (κ := ι) S) := by
  ext v k
  simp only [LinearMap.comp_apply, piMapQ, LinearMap.coe_mk, AddHom.coe_mk, piMulVec_apply,
    map_sum, map_smul]

/-- **The rank on the quotient side**:
$\dim\mathrm{im}\bigl(\text{coordinatewise quotient}\circ\text{piMulVec }R\bigr)
= \dim(M/S)\cdot\mathrm{rank}\,R$.

This is the engine of the "right-hand term" in the route of §4.12: coordinatewise
quotienting is surjective, so the image is the image of the same Π engine over $M/S$. -/
theorem finrank_range_piMapQ_comp_piMulVec {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    (S : Submodule (ZMod 2) M) (R : Matrix κ ι (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.range ((piMapQ (κ := κ) S).comp (piMulVec (M := M) R)))
      = Module.finrank (ZMod 2) (M ⧸ S) * matRank R := by
  rw [piMapQ_comp_piMulVec, LinearMap.range_comp, range_piMapQ, Submodule.map_top,
    finrank_range_piMulVec (M := M ⧸ S) R]

/-- **The intersection of images (tuple form)**:
$\dim\bigl(\mathrm{im}(\text{piMulVec }R)\cap \{v : \text{every component lies in }
S\}\bigr) = \dim S\cdot\mathrm{rank}\,R$.

This is the **only new piece of work** in §4.12 (the existing engines cover only kernels
and images, whereas here the **intersection** of two images is needed):

* left minus right is given by `finrank_inf_range_ker_sub` (take $g=$ `piMapQ S`, whose
  kernel is exactly the block "every component lies in $S$"),
* the two terms are given by the Π engine of §4.8 ($\dim M\cdot\mathrm{rank}\,R$) and its
  quotient version ($\dim(M/S)\cdot\mathrm{rank}\,R$),
* the difference $= \dim S\cdot\mathrm{rank}\,R$ is closed by
  $\dim(M/S) = \dim M - \dim S$. -/
theorem finrank_inf_range_piMulVec_pi {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    (S : Submodule (ZMod 2) M) (R : Matrix κ ι (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (piMulVec (M := M) R)
        ⊓ Submodule.pi Set.univ (fun _ : κ => S))
      = Module.finrank (ZMod 2) ↥S * matRank R := by
  have h := finrank_inf_range_ker_sub (piMulVec (M := M) R) (piMapQ (κ := κ) S)
  rw [ker_piMapQ, finrank_range_piMulVec (M := M) R,
    finrank_range_piMapQ_comp_piMulVec (S := S) (R := R), Submodule.finrank_quotient S] at h
  rw [h, Nat.sub_mul, Nat.sub_sub_self (Nat.mul_le_mul_right _ (Submodule.finrank_le S))]

/-- Pulling a submodule $S \le K$ back along the subtype embedding preserves its dimension
(the pullback only views the same subspace in a different ambient space). -/
theorem finrank_comap_subtype_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {K S : Submodule (ZMod 2) V} (h : S ≤ K) :
    Module.finrank (ZMod 2) ↥(Submodule.comap (Submodule.subtype K) S)
      = Module.finrank (ZMod 2) ↥S := by
  refine (LinearEquiv.finrank_eq ?_).symm
  exact
    { toFun := fun s => ⟨⟨s.1, h s.2⟩, s.2⟩
      invFun := fun t => ⟨t.1.1, t.2⟩
      map_add' := fun a b => Subtype.ext rfl
      map_smul' := fun c a => Subtype.ext rfl
      left_inv := fun s => Subtype.ext rfl
      right_inv := fun t => Subtype.ext rfl }

/-- The image-kernel form of the CSS condition $dC_1\,dC_2 = 0$:
$\mathrm{im}\,\partial_2 \subseteq \ker\partial_1$ (between the 2-term complex
$\mathcal C R$ and the 3-term complex $C$ of §2; this is the inclusion used in §4.9). -/
theorem range_mulVecLin_le_ker_mulVecLin {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
    {M : Matrix Q R (ZMod 2)} {N : Matrix P Q (ZMod 2)} (h : N * M = 0) :
    LinearMap.range M.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
  intro v hv
  obtain ⟨w, rfl⟩ := hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

/-- **The intersection of images, in the form on Koszul data**: for
$M = \ker\partial_1$, $S = \mathrm{im}\,\partial_2$,
$$\dim\bigl(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}B\bigr)
  = \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R.$$

The left-hand side is the intersection of the two images of `fd1` (that is, $\partial_2$):
the image of $C = \mathrm{id}\otimes R$ restricted to $\ker A$
($A = \mathrm{id}\otimes\partial_1$), and the image of $B = \partial_2\otimes\mathrm{id}$.
All three interfaces are already in place: $\ker A\cong(\mathcal R_1\to\ker\partial_1)$
comes from the currying isomorphism of §3, "$Cx$ equals the value of `piMulVec R`
pointwise" from `kronecker_one_mulVec_eq_piMulVec` of §4.9, and $\mathrm{im}B$ is exactly
the block "every component lies in $\mathrm{im}\,\partial_2$". -/
theorem finrank_inf_range_koszul_data {C₀ C₁ C₂ R₀ R₁ : Type*} [Fintype C₀] [Fintype C₁]
    [Fintype C₂] [Fintype R₀] [Fintype R₁] (R : Matrix R₀ R₁ (ZMod 2))
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (piMulVec (M := ↥(LinearMap.ker dC1.mulVecLin)) R)
        ⊓ Submodule.pi Set.univ (fun _ : R₀ =>
            Submodule.comap (Submodule.subtype (LinearMap.ker dC1.mulVecLin))
              (LinearMap.range dC2.mulVecLin)))
      = matRank dC2 * matRank R := by
  rw [finrank_inf_range_piMulVec_pi (S := Submodule.comap
        (Submodule.subtype (LinearMap.ker dC1.mulVecLin)) (LinearMap.range dC2.mulVecLin))
      (R := R),
    finrank_comap_subtype_of_le (h := range_mulVecLin_le_ker_mulVecLin hC)]
  simp only [matRank]

/-! ### 4.13 The matrix-world form of the intersection of images (the currying identification)

§4.12 proved that term in **tuple form** (`finrank_inf_range_koszul_data`: the value side
with $M = \ker\partial_1$, $S = \mathrm{im}\,\partial_2$). What the two-step bookkeeping
(`finrank_comap_add` and the block kernel formula) actually needs is that term in the
**matrix world**:

$$\dim\bigl(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}B\bigr)
  = \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R,\qquad
  C = \mathrm{id}\otimes R,\ A = \mathrm{id}\otimes\partial_1,\ B = \partial_2\otimes\mathrm{id},$$

and the same on the $\partial_1$ side (the two blocks being $\mathrm{id}\otimes R$ and
$\partial_1\otimes\mathrm{id}$). The bridge between the two worlds is the **swap of tensor
factor order** `currySwap`: a vector over $F_{0,1} = C_1\times\mathcal R_0$ is read with
$C_1$ first and $\mathcal R_0$ second as $(\mathcal R_0 \to C_1 \to \mathbb F_2)$, on which
side $(\mathrm{id}\otimes R)x$ **is pointwise** the value of `piMulVec R`
(`kronecker_one_mulVec_eq_piMulVec` of §4.9), and
$\mathrm{im}(\partial_2\otimes\mathrm{id})$ **is** the block "every component lies in
$\mathrm{im}\,\partial_2$" (`map_currySwap_range_kronecker_one`, checked componentwise with
`kroneckerMap_one_mulVec_apply`). After the move it is §4.12; moving back uses only
`Submodule.map_inf` and "an injective map preserves the dimension of a submodule"
(`finrank_map_eq_of_injective`).

The four transport lemmas of this section (`map_currySwap_range_domRestrict`,
`map_currySwap_range_kronecker_one`, `map_currySwap_range_one_kronecker`,
`map_piSubtypeIncl_inf_pi`) are **general**: they hold for any two families of matrices of
the same shape, independently of this complex. -/

/-- **The swap of tensor factor order**: $(C \times \kappa \to M) \simeq_\ell
(\kappa \to C \to M)$. Both directions move coordinates individually, so every law is
`rfl`. -/
def currySwap (C κ M : Type*) [AddCommMonoid M] [Module (ZMod 2) M] :
    (C × κ → M) ≃ₗ[ZMod 2] (κ → C → M) where
  toFun w := fun j c => w (c, j)
  invFun v := fun p => v p.2 p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The coordinatewise embedding**: $(\kappa \to \mathord{\uparrow}K) \to (\kappa \to V)$
(each component embedded by the subtype embedding). -/
def piSubtypeIncl {κ V : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
    (K : Submodule (ZMod 2) V) : (κ → ↥K) →ₗ[ZMod 2] (κ → V) where
  toFun w := fun j => (w j : V)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem piSubtypeIncl_injective {κ V : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
    (K : Submodule (ZMod 2) V) : Function.Injective (piSubtypeIncl (κ := κ) K) := by
  intro w w' h
  funext j
  exact Subtype.ext (congrFun h j)

/-- **An injective linear map transports the dimension of a submodule unchanged**:
$\dim(f(P)) = \dim P$ (for $f$ injective). -/
theorem finrank_map_eq_of_injective {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) V]
    (f : V →ₗ[ZMod 2] W) (hf : Function.Injective f) (p : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) ↥(Submodule.map f p) = Module.finrank (ZMod 2) ↥p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  have hker : LinearMap.ker (f.domRestrict p) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    refine Subtype.ext (hf ?_)
    simpa only [LinearMap.domRestrict_apply] using hxy
  rw [LinearMap.range_domRestrict, hker, finrank_bot, add_zero] at h
  exact h

/-- **The dimension of the Π of a submodule**:
$\dim\{w : \text{every component lies in } S\} = |\kappa|\cdot\dim S$. -/
theorem finrank_pi_submodule {κ V : Type*} [Fintype κ] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (S : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) ↥(Submodule.pi Set.univ (fun _ : κ => S))
      = Fintype.card κ * Module.finrank (ZMod 2) ↥S := by
  have e : ↥(Submodule.pi Set.univ (fun _ : κ => S)) ≃ₗ[ZMod 2] (κ → ↥S) :=
    { toFun := fun w => fun j => ⟨w.1 j, (Submodule.mem_pi.mp w.2) j (Set.mem_univ j)⟩
      invFun := fun v => ⟨fun j => (v j : V), Submodule.mem_pi.mpr fun j _ => (v j).2⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl
      left_inv := fun w => rfl
      right_inv := fun v => rfl }
  rw [LinearEquiv.finrank_eq e, finrank_const_pi]

/-- **Transport of the image (the $\partial_2\otimes\mathrm{id}$ side)**: under
`currySwap`, the image of $(A\otimes 1_\kappa)$ equals the block "every component lies in
$\mathrm{im}\,A$". -/
theorem map_currySwap_range_kronecker_one {β γ κ : Type*} [Fintype β] [Fintype γ] [Fintype κ]
    [DecidableEq κ] (A : Matrix β γ (ZMod 2)) :
    Submodule.map (currySwap β κ (ZMod 2)).toLinearMap
        (LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) A (1 : Matrix κ κ (ZMod 2))).mulVecLin)
      = Submodule.pi Set.univ (fun _ : κ => LinearMap.range A.mulVecLin) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
    refine Submodule.mem_pi.mpr fun j _ => LinearMap.mem_range.mpr ⟨fun i => z (i, j), ?_⟩
    funext c
    show (A *ᵥ fun i => z (i, j)) c
      = ((Matrix.kroneckerMap (fun a b => a * b) A 1).mulVecLin z) (c, j)
    rw [Matrix.mulVecLin_apply, kroneckerMap_one_mulVec_apply]
    rfl
  · rw [LinearEquiv.finrank_map_eq, finrank_pi_submodule, ← matRank, ← matRank,
      matRank_kronecker_one]

/-- **Interchange for the intersection of images**: pull the "coordinatewise embedding"
outside the intersection (the embedding is injective, so both sides have the same
dimension). -/
theorem map_piSubtypeIncl_inf_pi {κ V : Type*} [Fintype κ] [AddCommGroup V] [Module (ZMod 2) V]
    (S K : Submodule (ZMod 2) V) (P : Submodule (ZMod 2) (κ → ↥K)) :
    Submodule.map (piSubtypeIncl (κ := κ) K) P ⊓ Submodule.pi Set.univ (fun _ : κ => S)
      = Submodule.map (piSubtypeIncl (κ := κ) K)
          (P ⊓ Submodule.pi Set.univ (fun _ : κ => Submodule.comap (Submodule.subtype K) S)) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨hwP, hwS⟩ := Submodule.mem_inf.mp hw
    obtain ⟨v, hvP, rfl⟩ := Submodule.mem_map.mp hwP
    refine Submodule.mem_map.mpr ⟨v, Submodule.mem_inf.mpr ⟨hvP, ?_⟩, rfl⟩
    rw [Submodule.mem_pi] at hwS
    exact Submodule.mem_pi.mpr fun j _ => (Submodule.mem_pi.mp hwS j (Set.mem_univ j))
  · refine le_inf (Submodule.map_mono inf_le_left) ?_
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    have hv' : ∀ j, (v j : V) ∈ S := fun j =>
      Submodule.mem_comap.mp (Submodule.mem_pi.mp (Submodule.mem_inf.mp hv).2 j (Set.mem_univ j))
    exact Submodule.mem_pi.mpr fun j _ => hv' j

/-- **Transport of the image ($\mathrm{id}\otimes R$ restricted to the $\ker$)**: under
`currySwap`, the image of $(\mathrm{id}_\beta\otimes R)$ restricted to
$\ker(A\otimes\mathrm{id}_\iota)$ equals the image of `piMulVec R` on "tuples with values
in $\ker A$", transported back by the coordinatewise embedding. -/
theorem map_currySwap_range_domRestrict {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq β] (A : Matrix α β (ZMod 2)) (R : Matrix κ ι (ZMod 2)) :
    Submodule.map (currySwap β κ (ZMod 2)).toLinearMap
        (LinearMap.range
          ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix β β (ZMod 2)) R).mulVecLin.domRestrict
            (LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
              (1 : Matrix ι ι (ZMod 2))).mulVecLin)))
      = Submodule.map (piSubtypeIncl (κ := κ) (LinearMap.ker A.mulVecLin))
          (LinearMap.range (piMulVec (M := ↥(LinearMap.ker A.mulVecLin)) R)) := by
  have hcomp : (currySwap β κ (ZMod 2)).toLinearMap.comp
        ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix β β (ZMod 2)) R).mulVecLin.domRestrict
          (LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) A
            (1 : Matrix ι ι (ZMod 2))).mulVecLin))
      = (piSubtypeIncl (κ := κ) (LinearMap.ker A.mulVecLin)).comp
          ((piMulVec (M := ↥(LinearMap.ker A.mulVecLin)) R).comp
            (kerKroneckerOneEquiv A).toLinearMap) := by
    ext x j c
    change (((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix β β (ZMod 2)) R) *ᵥ
        (x : β × ι → ZMod 2))) (c, j)
      = (Submodule.subtype (LinearMap.ker A.mulVecLin)
          ((piMulVec (M := ↥(LinearMap.ker A.mulVecLin)) R) (kerKroneckerOneEquiv A x) j)) c
    exact congrFun (kronecker_one_mulVec_eq_piMulVec A R x) (c, j)
  rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (kerKroneckerOneEquiv A).surjective, Submodule.map_top]

/-- **Transport of the image (the $\mathrm{id}_\alpha\otimes R$ side)**: under `currySwap`,
the image of $(\mathrm{id}_\alpha\otimes R)$ is the image of `piMulVec R` on "tuples with
values in $\mathbb F_2^\alpha$". -/
theorem map_currySwap_range_one_kronecker {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq α] [DecidableEq κ] (R : Matrix κ ι (ZMod 2)) :
    Submodule.map (currySwap α κ (ZMod 2)).toLinearMap
        (LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) R).mulVecLin)
      = LinearMap.range (piMulVec (M := α → ZMod 2) R) := by
  have hcomp : (currySwap α κ (ZMod 2)).toLinearMap.comp
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) R).mulVecLin
      = (piMulVec (M := α → ZMod 2) R).comp (currySwap α ι (ZMod 2)).toLinearMap := by
    ext x j c
    show ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix α α (ZMod 2)) R).mulVecLin x) (c, j) = _
    rw [Matrix.mulVecLin_apply, kroneckerMap_one_left_mulVec_apply, LinearMap.comp_apply,
      piMulVec_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    rfl
  rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (currySwap α ι (ZMod 2)).surjective, Submodule.map_top]

/-- **The intersection of images (the $\partial_2$ side, matrix world)**: on Koszul data,
$$\dim\bigl(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}B\bigr)
  = \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R\quad
  (C = \mathrm{id}\otimes R,\ A = \mathrm{id}\otimes\partial_1,
  \ B = \partial_2\otimes\mathrm{id}).$$
`currySwap` moves the three objects together to the tuple side, then it falls back to
`finrank_inf_range_koszul_data` of §4.12. -/
theorem finrank_inf_range_koszul {C₀ C₁ C₂ R₀ R₁ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
    [Fintype R₀] [Fintype R₁] [DecidableEq C₁] [DecidableEq R₀] [DecidableEq R₁]
    (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    Module.finrank (ZMod 2) ↥(LinearMap.range
          ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R).mulVecLin.domRestrict
            (LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) dC1
              (1 : Matrix R₁ R₁ (ZMod 2))).mulVecLin))
        ⊓ LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) dC2
            (1 : Matrix R₀ R₀ (ZMod 2))).mulVecLin)
      = matRank dC2 * matRank R := by
  have hkey : Submodule.map (currySwap C₁ R₀ (ZMod 2)).toLinearMap
        (LinearMap.range
            ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R).mulVecLin.domRestrict
              (LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) dC1
                (1 : Matrix R₁ R₁ (ZMod 2))).mulVecLin))
          ⊓ LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) dC2
              (1 : Matrix R₀ R₀ (ZMod 2))).mulVecLin)
      = Submodule.map (piSubtypeIncl (κ := R₀) (LinearMap.ker dC1.mulVecLin))
          (LinearMap.range (piMulVec (M := ↥(LinearMap.ker dC1.mulVecLin)) R)
            ⊓ Submodule.pi Set.univ (fun _ : R₀ =>
                Submodule.comap (Submodule.subtype (LinearMap.ker dC1.mulVecLin))
                  (LinearMap.range dC2.mulVecLin))) := by
    rw [Submodule.map_inf _ (currySwap C₁ R₀ (ZMod 2)).injective,
      map_currySwap_range_domRestrict dC1 R, map_currySwap_range_kronecker_one (A := dC2),
      map_piSubtypeIncl_inf_pi]
  rw [← LinearEquiv.finrank_map_eq (currySwap C₁ R₀ (ZMod 2))
      (LinearMap.range
          ((Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R).mulVecLin.domRestrict
            (LinearMap.ker (Matrix.kroneckerMap (fun a b => a * b) dC1
              (1 : Matrix R₁ R₁ (ZMod 2))).mulVecLin))
        ⊓ LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) dC2
            (1 : Matrix R₀ R₀ (ZMod 2))).mulVecLin),
    hkey, finrank_map_eq_of_injective _ (piSubtypeIncl_injective _),
    finrank_inf_range_koszul_data R dC1 dC2 hC]

/-- **The intersection of images (the $\partial_1$ side, matrix world)**:
$\dim\bigl(\mathrm{im}(\mathrm{id}\otimes R)\cap\mathrm{im}(\partial_1\otimes\mathrm{id})\bigr)
= \mathrm{rank}(dC_1)\cdot\mathrm{rank}\,R$, an instance of the lemma of §4.12 in the
**full ambient space**. -/
theorem finrank_inf_range_koszul_row {C₀ C₁ C₂ R₀ R₁ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
    [Fintype R₀] [Fintype R₁] [DecidableEq C₀] [DecidableEq R₀] [DecidableEq R₁]
    (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.range
          (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R).mulVecLin
        ⊓ LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) dC1
            (1 : Matrix R₀ R₀ (ZMod 2))).mulVecLin)
      = matRank dC1 * matRank R := by
  have hkey : Submodule.map (currySwap C₀ R₀ (ZMod 2)).toLinearMap
        (LinearMap.range
            (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R).mulVecLin
          ⊓ LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) dC1
              (1 : Matrix R₀ R₀ (ZMod 2))).mulVecLin)
      = LinearMap.range (piMulVec (M := C₀ → ZMod 2) R)
        ⊓ Submodule.pi Set.univ (fun _ : R₀ => LinearMap.range dC1.mulVecLin) := by
    rw [Submodule.map_inf _ (currySwap C₀ R₀ (ZMod 2)).injective,
      map_currySwap_range_one_kronecker R, map_currySwap_range_kronecker_one (A := dC1)]
  rw [← LinearEquiv.finrank_map_eq (currySwap C₀ R₀ (ZMod 2))
      (LinearMap.range
          (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R).mulVecLin
        ⊓ LinearMap.range (Matrix.kroneckerMap (fun a b => a * b) dC1
            (1 : Matrix R₀ R₀ (ZMod 2))).mulVecLin),
    hkey, finrank_inf_range_piMulVec_pi (S := LinearMap.range dC1.mulVecLin) (R := R)]
  simp only [matRank]

/-! ### 4.14 The kernel of a general $2\times2$ block (top-right block zero): the shape of
`fd1` when $R \ne 0$

For $R \ne 0$, $\partial_2 = $`fd1` is
$\binom{d_{1,1\to1,0}\ \ 0}{d_{1,1\to0,1}\ \ d_{0,2\to0,1}}$, a general block matrix rather
than one of the three "only one block nonzero" shapes of §4.1–4. This section gives a
kernel dimension formula for it:

$$\dim\ker\binom{A\ \ 0}{C\ \ D} = \dim\ker D + \dim(\ker A\cap\ker C)
  + \dim\bigl(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}D\bigr),$$

whose three terms are exactly the three pieces prepared in §4.12–13: the
$\otimes\mathrm{id}$ engine, the intersection of kernels, and the intersection of images.
The method is the two-step bookkeeping "first solve $y$, then solve $x$": the fibre over
$y$ is exactly $\ker A\cap\ker C$ (the top-right block is zero, so the `inl` row sees only
$A$; the two explicit isomorphisms `kerProjSecondEquiv`), the $y$ in the image are those
with $D\,y\in\mathrm{im}(C|_{\ker A})$ (`rangeProjSecondEquiv`), and `finrank_comap_add` of
§4.11 splits the latter into $\dim\ker D$ and the intersection of the two images. -/

/-- **The component formula for the block matrix $\binom{A\ \ 0}{C\ \ D}$ (the `inl` row)**
(the top-right block is zero, so only $A$ is seen). -/
theorem fromBlocks_zeroRight_mulVec_apply_inl {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (C : Matrix P₂ Q₁ (ZMod 2))
    (D : Matrix P₂ Q₂ (ZMod 2)) (z : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₁) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) C D) *ᵥ z) (Sum.inl p)
      = (A *ᵥ (fun q => z (Sum.inl q))) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- As above, the `inr` row gives the two blocks $C\,x + D\,y$. -/
theorem fromBlocks_zeroRight_mulVec_apply_inr {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (C : Matrix P₂ Q₁ (ZMod 2))
    (D : Matrix P₂ Q₂ (ZMod 2)) (z : (Q₁ ⊕ Q₂) → ZMod 2) (p : P₂) :
    ((Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) C D) *ᵥ z) (Sum.inr p)
      = (C *ᵥ (fun q => z (Sum.inl q)) + D *ᵥ (fun q₂ => z (Sum.inr q₂))) p := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Pi.add_apply]

/-- **The projection to the second block (the $y$ half)**: the family of linear functionals
on $\ker\binom{A\ 0}{C\ D}$. -/
def projSecond {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q₁] [Fintype Q₂]
    (A : Matrix P₁ Q₁ (ZMod 2)) (C : Matrix P₂ Q₁ (ZMod 2)) (D : Matrix P₂ Q₂ (ZMod 2)) :
    ↥(LinearMap.ker (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) C D).mulVecLin)
      →ₗ[ZMod 2] (Q₂ → ZMod 2) where
  toFun z := fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)
  map_add' _ _ := by funext q₂; rfl
  map_smul' _ _ := by funext q₂; rfl

/-- **The kernel of the projection to $y$**: isomorphic to $\ker A\cap\ker C$; when
$y = 0$ the top-right block is zero, so the `inl` row reduces to $Ax = 0$ and the `inr`
row to $Cx = 0$. -/
def kerProjSecondEquiv {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q₁]
    [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (C : Matrix P₂ Q₁ (ZMod 2))
    (D : Matrix P₂ Q₂ (ZMod 2)) :
    ↥(LinearMap.ker (projSecond A C D))
      ≃ₗ[ZMod 2] ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker C.mulVecLin) where
  toFun z :=
    ⟨fun q => (z.1 : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q), by
      have h1 : (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) C D) *ᵥ
          (z.1 : Q₁ ⊕ Q₂ → ZMod 2) = 0 := LinearMap.mem_ker.mp z.1.2
      have h3 : (fun q₂ => (z.1 : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) = 0 := z.2
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · funext p
        have h2 := congrFun h1 (Sum.inl p)
        rw [fromBlocks_zeroRight_mulVec_apply_inl] at h2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using h2
      · funext p
        have h2 := congrFun h1 (Sum.inr p)
        rw [fromBlocks_zeroRight_mulVec_apply_inr, Pi.add_apply, Pi.zero_apply] at h2
        have h4 : (D *ᵥ (fun q₂ => (z.1 : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂))) p = 0 := by
          rw [h3, Matrix.mulVec_zero, Pi.zero_apply]
        rw [h4, add_zero] at h2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using h2⟩
  invFun x :=
    ⟨⟨fun p => match p with
        | Sum.inl q => (x : Q₁ → ZMod 2) q
        | Sum.inr _ => 0, by
      have hxA : A *ᵥ (x : Q₁ → ZMod 2) = 0 :=
        LinearMap.mem_ker.mp (Submodule.mem_inf.mp x.2).1
      have hxC : C *ᵥ (x : Q₁ → ZMod 2) = 0 :=
        LinearMap.mem_ker.mp (Submodule.mem_inf.mp x.2).2
      funext p
      rw [Matrix.mulVecLin_apply]
      cases p with
      | inl p =>
        rw [fromBlocks_zeroRight_mulVec_apply_inl]
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hxA p
      | inr p =>
        rw [fromBlocks_zeroRight_mulVec_apply_inr]
        have hzero : (fun q₂ => (match (Sum.inr q₂ : Q₁ ⊕ Q₂) with
            | Sum.inl q => (x : Q₁ → ZMod 2) q
            | Sum.inr _ => 0)) = (0 : Q₂ → ZMod 2) := rfl
        rw [hzero, Matrix.mulVec_zero, add_zero]
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hxC p⟩, by
      funext q₂
      rfl⟩
  map_add' x y := Subtype.ext (funext fun q => rfl)
  map_smul' c x := Subtype.ext (funext fun q => rfl)
  left_inv z := Subtype.ext (by
    apply Subtype.ext
    funext p
    cases p with
    | inl q => rfl
    | inr q₂ =>
      exact (congrFun z.2 q₂).symm)
  right_inv x := Subtype.ext rfl

/-- **The image of the projection to $y$**: isomorphic to the block
"$D\,y \in \mathrm{im}(C|_{\ker A})$"; with the top-right block zero, the kernel condition
is exactly $Ax = 0$ together with $Cx = Dy$. -/
def rangeProjSecondEquiv {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂] [Fintype Q₁]
    [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (C : Matrix P₂ Q₁ (ZMod 2))
    (D : Matrix P₂ Q₂ (ZMod 2)) :
    ↥(LinearMap.range (projSecond A C D))
      ≃ₗ[ZMod 2] ↥(Submodule.comap D.mulVecLin
          (LinearMap.range (C.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)))) where
  toFun y :=
    ⟨(y : Q₂ → ZMod 2), by
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp y.2
      have h1 : (Matrix.fromBlocks A (0 : Matrix P₁ Q₂ (ZMod 2)) C D) *ᵥ
          (z : Q₁ ⊕ Q₂ → ZMod 2) = 0 := LinearMap.mem_ker.mp z.2
      have hAx : A *ᵥ (fun q => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q)) = 0 := by
        funext p
        have h2 := congrFun h1 (Sum.inl p)
        rw [fromBlocks_zeroRight_mulVec_apply_inl, Pi.zero_apply] at h2
        simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using h2
      have hCD : C *ᵥ (fun q => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q))
          = D *ᵥ (fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) := by
        funext p
        have h2 := congrFun h1 (Sum.inr p)
        rw [fromBlocks_zeroRight_mulVec_apply_inr, Pi.add_apply, Pi.zero_apply] at h2
        calc (C *ᵥ fun q => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q)) p
            = ((C *ᵥ fun q => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q)) p
                + ((D *ᵥ fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) p
                  + (D *ᵥ fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) p)) := by
              rw [CharTwo.add_self_eq_zero, add_zero]
          _ = (((C *ᵥ fun q => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q)) p
                + (D *ᵥ fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) p)
              + (D *ᵥ fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) p) := by
              rw [add_assoc]
          _ = (D *ᵥ fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) p := by
              rw [h2, zero_add]
      refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨⟨fun q => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inl q), hAx⟩, ?_⟩)
      -- $C x = D y$: replace the `inr` part of $z$ by $y$ (via $hz$)
      have hzy : (fun q₂ => (z : Q₁ ⊕ Q₂ → ZMod 2) (Sum.inr q₂)) = (y : Q₂ → ZMod 2) := hz
      rw [← hzy]
      exact hCD⟩
  invFun y :=
    ⟨(y : Q₂ → ZMod 2), by
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp y.2)
      have hxA : A *ᵥ (x : Q₁ → ZMod 2) = 0 := by
        simpa only [Matrix.mulVecLin_apply] using LinearMap.mem_ker.mp x.2
      have hxCD : C *ᵥ (x : Q₁ → ZMod 2) = D *ᵥ (y : Q₂ → ZMod 2) := by
        simpa only [LinearMap.domRestrict_apply, Matrix.mulVecLin_apply] using hx
      refine LinearMap.mem_range.mpr ⟨⟨fun p => match p with
          | Sum.inl q => (x : Q₁ → ZMod 2) q
          | Sum.inr q₂ => (y : Q₂ → ZMod 2) q₂, ?_⟩, ?_⟩
      · funext p
        rw [Matrix.mulVecLin_apply]
        cases p with
        | inl p =>
          rw [fromBlocks_zeroRight_mulVec_apply_inl, Pi.zero_apply]
          simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun hxA p
        | inr p =>
          rw [fromBlocks_zeroRight_mulVec_apply_inr, Pi.add_apply, Pi.zero_apply]
          change (C *ᵥ (x : Q₁ → ZMod 2)) p + (D *ᵥ (y : Q₂ → ZMod 2)) p = 0
          rw [hxCD, CharTwo.add_self_eq_zero]
      · funext q₂
        rfl⟩
  map_add' a b := Subtype.ext rfl
  map_smul' c a := Subtype.ext rfl
  left_inv y := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

/-- **The kernel of a general $2\times2$ block (top-right block zero)**:
$$\dim\ker\binom{A\ \ 0}{C\ \ D} = \dim\ker D + \dim(\ker A\cap\ker C)
  + \dim\bigl(\mathrm{im}(C|_{\ker A})\cap\mathrm{im}D\bigr).$$

Layered as "first solve $y$, then solve $x$": the fibre over $y$ is exactly
$\ker A\cap\ker C$ (the first isomorphism), the $y$ in the image satisfy
$Dy\in\mathrm{im}(C|_{\ker A})$ (the second isomorphism), and then `finrank_comap_add`
splits the latter into $\dim\ker D$ and the intersection of the two images. When
$R \ne 0$, `fd1` has exactly this shape, so the three terms of $\dim\ker\partial_2$ fall
into place. -/
theorem finrank_ker_fromBlocks_row_col {P₁ P₂ Q₁ Q₂ : Type*} [Fintype P₁] [Fintype P₂]
    [Fintype Q₁] [Fintype Q₂] (A : Matrix P₁ Q₁ (ZMod 2)) (C : Matrix P₂ Q₁ (ZMod 2))
    (D : Matrix P₂ Q₂ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks A
        (0 : Matrix P₁ Q₂ (ZMod 2)) C D).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker D.mulVecLin)
        + Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker C.mulVecLin)
        + Module.finrank (ZMod 2) ↥(LinearMap.range
            (C.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)) ⊓ LinearMap.range D.mulVecLin) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (projSecond A C D)
  have h1 : Module.finrank (ZMod 2) ↥(LinearMap.ker (projSecond A C D))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker C.mulVecLin) :=
    (kerProjSecondEquiv A C D).finrank_eq
  have h2 : Module.finrank (ZMod 2) ↥(LinearMap.range (projSecond A C D))
      = Module.finrank (ZMod 2) ↥(Submodule.comap D.mulVecLin
          (LinearMap.range (C.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)))) :=
    (rangeProjSecondEquiv A C D).finrank_eq
  have h3 := finrank_comap_add D.mulVecLin
    (LinearMap.range (C.mulVecLin.domRestrict (LinearMap.ker A.mulVecLin)))
  rw [inf_comm] at h3
  rw [h1, h2] at hrn
  omega

/-! ### 4.15 Closed forms of the two intermediate kernels over general $R$

The remaining three degrees reduce in the end to just $\dim\ker\partial_2$ and
$\dim\ker\partial_1$ (see item 1 of §5). Once §4.12–14 have prepared the blocks, these two
are a **substitution**: for $\partial_2 = $`fd1` use the general $2\times2$ block kernel
formula of §4.14, and for $\partial_1 = $`fd0` the block-row formula of §4.3,
substituting the engine values term by term.

$$\dim\ker\partial_2 = \dim\ker dC_1\cdot\dim\ker R
  + \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R + |\mathcal R_0|\cdot\dim\ker dC_2,$$
$$\dim\ker\partial_1 = |C_0|\cdot\dim\ker R
  + |\mathcal R_0|\cdot\dim\ker dC_1 + \mathrm{rank}(dC_1)\cdot\mathrm{rank}\,R.$$

Both agree verbatim with the closed forms measured by `tools/probe_kunneth_general.jl`
(that probe: 136 random $(C_\bullet,R)$ and 0 mismatches). -/

/-- **The closed form of $\dim\ker\partial_2$ over general $R$**:
$$\dim\ker\partial_2 = \dim\ker dC_1\cdot\dim\ker R
  + \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R + |\mathcal R_0|\cdot\dim\ker dC_2.$$

That is, the block kernel formula of §4.14 together with the three engines:
$\ker(dC_2\otimes1)$ via §3, the intersection of kernels via §4.9 and the Π engine, the
intersection of images via §4.13. -/
theorem finrank_ker_fd1 {R₀ R₁ C₀ C₁ C₂ : Type*} [Fintype R₀] [Fintype R₁] [Fintype C₀]
    [Fintype C₁] [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq R₀] [DecidableEq R₁]
    (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (fd1
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
          * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + matRank dC2 * matRank R
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin) := by
  change Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
      (0 : Matrix (C₀ × R₁) (C₂ × R₀) (ZMod 2))
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin) = _
  rw [finrank_ker_fromBlocks_row_col,
    finrank_ker_kronecker_one dC2,
    finrank_inf_ker_kronecker (A := dC1) (R := R),
    finrank_ker_piMulVec (M := ↥(LinearMap.ker dC1.mulVecLin)) R,
    finrank_inf_range_koszul R dC1 dC2 hC]
  omega

/-- **The closed form of $\dim\ker\partial_1$ over general $R$**:
$$\dim\ker\partial_1 = |C_0|\cdot\dim\ker R + |\mathcal R_0|\cdot\dim\ker dC_1
  + \mathrm{rank}(dC_1)\cdot\mathrm{rank}\,R.$$

$\partial_1 = $`fd0` is a **block-row** $(1\otimes R\ \ dC_1\otimes1)$, so the block-row
kernel formula of §4.3 applies directly, the three blocks being the mirror engine of §4.10,
the engine of §3, and the $\partial_1$-side intersection of images of §4.13. -/
theorem finrank_ker_fd0 {R₀ R₁ C₀ C₁ C₂ : Type*} [Fintype R₀] [Fintype R₁] [Fintype C₀]
    [Fintype C₁] [Fintype C₂] [DecidableEq C₀] [DecidableEq R₀] [DecidableEq R₁]
    (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (fd0
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
      = Fintype.card C₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        + matRank dC1 * matRank R := by
  change Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
      (0 : Matrix (Fin 0) (C₀ × R₁) (ZMod 2))
      (0 : Matrix (Fin 0) (C₁ × R₀) (ZMod 2))).mulVecLin) = _
  rw [finrank_ker_fromBlocks_row,
    finrank_ker_one_kronecker (ι := R₀) (κ := R₁) (α := C₀) (A := R),
    finrank_ker_kronecker_one (α := C₀) (β := C₁) (ι := R₀) dC1,
    finrank_inf_range_koszul_row (C₂ := C₂) (R := R) (dC1 := dC1)]

/-! ### 4.16 The bookkeeping lemmas for three degrees (the $H_2$ and $H_1$ cases)

Once the closed forms of $\dim\ker\partial_2$ and $\dim\ker\partial_1$ (§4.15) are in
hand, what remains is a **rank subtraction**:
$H_2 = \dim\ker\partial_2 - \mathrm{rank}\,\partial_3$ (and likewise for $H_1$, $H_0$). The
difficulty here is the bookkeeping of truncated subtraction on $\mathbb N$: the first term
of $\dim\ker\partial_2$ and the $|C_2||\mathcal R_1|$ in $\mathrm{rank}\,\partial_3$ cancel
each other, via the two rank-nullity identities
$\mathrm{rk}dC_2 + \dim\ker dC_2 = |C_2|$ and
$\mathrm{rk}R + \dim\ker R = |\mathcal R_1|$; over $\mathbb N$ one must say at every step
that "no truncation occurs" (here via the CSS-condition bounds
$\mathrm{rk}dC_2\le\dim\ker dC_1$ and $\mathrm{rk}R\le|\mathcal R_0|$).

This section machine-checks them **as pure arithmetic lemmas** (the $H_2$ one: 9 variables,
four hypotheses; the $H_1$ one: 11 variables, eight hypotheses); neither involves matrices;
they only answer "given the rank-nullity identities and two bounds, does this $\mathbb N$
equality hold". The proof follows the convention of this repository: move to $\mathbb Z$
and close by `ring` (a polynomial identity), then fall back to $\mathbb N$ with
`Nat.cast_injective` and the bounds of `Nat.cast_sub`. -/



theorem arith_H2_gen (kC1 kC2 rC2 kR rR ℓ m n₂ : ℕ)
    (h2 : rC2 + kC2 = n₂) (hR : rR + kR = ℓ) (hle : rC2 ≤ kC1) (hleR : rR ≤ m)
    (hb : kR * kC2 ≤ n₂ * ℓ)
    (hout : n₂ * ℓ - kR * kC2 ≤ kC1 * kR + rC2 * rR + m * kC2) :
    kC1 * kR + rC2 * rR + m * kC2 - (n₂ * ℓ - kR * kC2)
      = kR * (kC1 - rC2) + (m - rR) * kC2 := by
  have h2' : ((rC2 + kC2 : ℕ) : ℤ) = (n₂ : ℤ) := by exact_mod_cast h2
  have hR' : ((rR + kR : ℕ) : ℤ) = (ℓ : ℤ) := by exact_mod_cast hR
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hout, Nat.cast_sub hb]
  push_cast
  rw [← h2', ← hR', Nat.cast_sub hle, Nat.cast_sub hleR]
  push_cast
  ring

/-! ### 4.17 The dimension of $H_2$ over general $R$: the second bullet printed by p.63

$$H_2(\mathcal R\otimes C) = H_1(\mathcal R)\otimes H_1(C)
  \oplus H_0(\mathcal R)\otimes H_2(C)$$

in dimension is $\dim H_2 = \dim H_1(\mathcal R)\cdot\dim H_1(C)
+ \dim H_0(\mathcal R)\cdot\dim H_2(C)$
($\ker R\cdot h_1(C) + \mathrm{coker}R\cdot h_2(C)$). Assembly:
$H_2 = \ker\partial_2/\mathrm{im}\,\partial_3$, so
$\dim H_2 = \dim\ker\partial_2 - \mathrm{rank}\,\partial_3$; the first term is
`finrank_ker_fd1` of §4.15, the second is given by rank-nullity
($\mathrm{rank} = |F_3| - \dim\ker\partial_3$, $|F_3| = |C_2||\mathcal R_1|$) together with
`kunneth_H3` of §4.9; the $\mathbb N$ bookkeeping of the subtraction is `arith_H2_gen` of
§4.16. The $\partial_3$ side is kept in the **complex-field form**
(`fd2 F.d12_11 F.d12_02`) to avoid the syntactic difference between the two notations
`Matrix.kronecker` and `kroneckerMap`. -/

theorem kunneth_H2 {R₀ R₁ C₀ C₁ C₂ : Type*} [Fintype R₀] [Fintype R₁] [Fintype C₀]
    [Fintype C₁] [Fintype C₂] [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (R : Matrix R₀ R₁ (ZMod 2))
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH2 (koszulFaultComplex R dC1 dC2 hC)
      = twoTermH1 R * threeTermH1 dC1 dC2 + twoTermH0 R * threeTermH2 dC2 := by
  have h11 : (koszulFaultComplex R dC1 dC2 hC).d11_10
      = Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl
  have h01 : (koszulFaultComplex R dC1 dC2 hC).d11_01
      = Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R := rfl
  have h02 : (koszulFaultComplex R dC1 dC2 hC).d02_01
      = Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  have h12 : (koszulFaultComplex R dC1 dC2 hC).d12_11
      = Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl
  have h20 : (koszulFaultComplex R dC1 dC2 hC).d12_02
      = Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₂ C₂ (ZMod 2)) R := rfl
  -- The ∂₃ side: keep the **complex-field form** (`fd2 F.d12_11 F.d12_02`), so that the
  -- two notations of kronecker do not clash
  have hker3 : Module.finrank (ZMod 2) ↥(LinearMap.ker (fd2
      (koszulFaultComplex R dC1 dC2 hC).d12_11
      (koszulFaultComplex R dC1 dC2 hC).d12_02).mulVecLin)
      = twoTermH1 R * threeTermH2 dC2 := by
    simpa only [faultH3] using kunneth_H3 R dC1 dC2 hC
  have hmat3 : Module.finrank (ZMod 2) ↥(LinearMap.range (fd2
      (koszulFaultComplex R dC1 dC2 hC).d12_11
      (koszulFaultComplex R dC1 dC2 hC).d12_02).mulVecLin)
      = Fintype.card C₂ * Fintype.card R₁ - twoTermH1 R * threeTermH2 dC2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (fd2
      (koszulFaultComplex R dC1 dC2 hC).d12_11
      (koszulFaultComplex R dC1 dC2 hC).d12_02).mulVecLin
    have hcard : Fintype.card ((C₂ × R₁) ⊕ Fin 0) = Fintype.card C₂ * Fintype.card R₁ := by
      rw [Fintype.card_sum, Fintype.card_fin, add_zero, Fintype.card_prod]
    have hdom : Module.finrank (ZMod 2) ((C₂ × R₁) ⊕ Fin 0 → ZMod 2)
        = Fintype.card C₂ * Fintype.card R₁ := by
      rw [Module.finrank_fintype_fun_eq_card, hcard]
    rw [hdom, hker3] at hrn
    omega
  rw [faultH2, h11, h01, h02, finrank_ker_fd1 R dC1 dC2 hC, hmat3]
  have hcoker : twoTermH0 R = Fintype.card R₀ - matRank R := by
    have := twoTermH0_add_matRank R
    omega
  rw [hcoker]
  simp only [twoTermH1, threeTermH1, threeTermH2]
  -- The arithmetic part of the bookkeeping: prepare the six hypotheses first (including
  -- the two rank-nullity identities and the CSS bound)
  have h2 : matRank dC2 + Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      = Fintype.card C₂ := by
    change Module.finrank (ZMod 2) ↥(LinearMap.range dC2.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin) = Fintype.card C₂
    have hr := LinearMap.finrank_range_add_finrank_ker dC2.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at hr
    exact hr
  have hR : matRank R + Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
      = Fintype.card R₁ := by
    have := twoTermH1_add_matRank R
    simp only [twoTermH1] at this
    omega
  have hb : Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      ≤ Fintype.card C₂ * Fintype.card R₁ := by
    have hkR : Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) ≤ Fintype.card R₁ := by
      have h := twoTermH1_add_matRank R
      simp only [twoTermH1] at h
      omega
    have hkC : Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin) ≤ Fintype.card C₂ := by
      have h := finrank_ker_eq_card_sub_matRank dC2
      omega
    calc Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
          * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
        ≤ Fintype.card R₁ * Fintype.card C₂ := Nat.mul_le_mul hkR hkC
      _ = Fintype.card C₂ * Fintype.card R₁ := Nat.mul_comm _ _
  have hadd : Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
      + matRank dC2 * matRank R + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) * matRank dC2
      + matRank R * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
          * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
        + Fintype.card C₂ * Fintype.card R₁ := by
    rw [← h2, ← hR]
    ring
  have hout : Fintype.card C₂ * Fintype.card R₁
        - Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
          * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
          * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + matRank dC2 * matRank R
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin) := by
    have hmono1 : Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin) * matRank dC2
        ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
          * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin) :=
      Nat.mul_le_mul_left _ (matRank_le_finrank_ker_of_mul_eq_zero dC1 dC2 hC)
    have hmono2 : matRank R * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
        ≤ Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin) :=
      Nat.mul_le_mul_right _ (by have := twoTermH0_add_matRank R; omega)
    omega
  exact arith_H2_gen _ _ _ _ _ _ _ _ h2 hR
    (matRank_le_finrank_ker_of_mul_eq_zero dC1 dC2 hC)
    (by have := twoTermH0_add_matRank R; omega) hb hout


/-! ### 4.18 The bookkeeping lemma for $H_1$ (same method as $H_2$)

The same two things: first turn the $\mathbb N$ equality into an additive identity
(verified by `ring` over $\mathbb Z$), then fall back to $\mathbb N$ with
`Nat.cast_injective` and the bounds of `Nat.cast_sub`; the two bounds have the same source
as in $H_2$, with `hin` being $\dim\ker\partial_2\le|F_2|$ (three product bounds) and
`hout` being $\mathrm{rank}\,\partial_2\le\dim\ker\partial_1$ (the additive identity plus
three monotonicities). -/

/-- **The bookkeeping for $H_1$ (general $R$, pure arithmetic)**:
$$\Bigl(|C_0|\dim\ker R + |\mathcal R_0|\dim\ker dC_1 + \mathrm{rk}dC_1\,\mathrm{rk}R\Bigr)
  - \Bigl(|C_1||\mathcal R_1| + |C_2||\mathcal R_0| - \dim\ker\partial_2\Bigr)
  = \dim\ker R\cdot h_0(C) + \mathrm{coker}R\cdot h_1(C),$$
where $\dim\ker\partial_2 = \dim\ker dC_1\dim\ker R + \mathrm{rk}dC_2\,\mathrm{rk}R
+ |\mathcal R_0|\dim\ker dC_2$ (§4.15). -/
theorem arith_H1_gen (n₀ kC1 kC2 rC1 rC2 kR rR ℓ m n₁ n₂ : ℕ)
    (hC1 : rC1 + kC1 = n₁) (h2 : rC2 + kC2 = n₂) (hR : rR + kR = ℓ)
    (hle1 : rC1 ≤ n₀) (hle2 : rC2 ≤ kC1) (hleR : rR ≤ m)
    (hin : kC1 * kR + rC2 * rR + m * kC2 ≤ n₁ * ℓ + n₂ * m)
    (hout : n₁ * ℓ + n₂ * m - (kC1 * kR + rC2 * rR + m * kC2)
      ≤ n₀ * kR + m * kC1 + rC1 * rR) :
    n₀ * kR + m * kC1 + rC1 * rR
        - (n₁ * ℓ + n₂ * m - (kC1 * kR + rC2 * rR + m * kC2))
      = kR * (n₀ - rC1) + (m - rR) * (kC1 - rC2) := by
  have hC1' : ((rC1 + kC1 : ℕ) : ℤ) = (n₁ : ℤ) := by exact_mod_cast hC1
  have h2' : ((rC2 + kC2 : ℕ) : ℤ) = (n₂ : ℤ) := by exact_mod_cast h2
  have hR' : ((rR + kR : ℕ) : ℤ) = (ℓ : ℤ) := by exact_mod_cast hR
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hout, Nat.cast_sub hin]
  push_cast
  rw [← hC1', ← h2', ← hR', Nat.cast_sub hle1, Nat.cast_sub hle2, Nat.cast_sub hleR]
  push_cast
  ring


/-! ### 4.19 The dimension of $H_1$ over general $R$: the first bullet printed by p.63

$$H_1(\mathcal R\otimes C) = H_1(\mathcal R)\otimes H_0(C)
  \oplus H_0(\mathcal R)\otimes H_1(C)$$

in dimension is $\dim H_1 = \dim\ker R\cdot h_0(C) + \mathrm{coker}R\cdot h_1(C)$. The
assembly has the same shape as §4.17: $H_1 = \ker\partial_1/\mathrm{im}\,\partial_2$, the
first term uses `finrank_ker_fd0` of §4.15, the second is given by rank-nullity
($\mathrm{rank}\,\partial_2 = |F_2| - \dim\ker\partial_2$) together with
`finrank_ker_fd1`, and the joint is `arith_H1_gen` of §4.18.

Both bounds come directly from linear algebra:
$\dim\ker\partial_2\le|F_2|$ is "the kernel lies in the domain"
(`Submodule.finrank_le`), and $\mathrm{rank}\,\partial_2\le\dim\ker\partial_1$ is the
complex condition $\mathrm{im}\,\partial_2\subseteq\ker\partial_1$
(`Submodule.finrank_mono` together with `range_mulVecLin_le_ker_mulVecLin` of §4.12); the
two are two lines each and are independent of `omega`'s atom ordering. -/

/-- **The dimension of $H_1$ over general $R$**: $\dim H_1 = \dim\ker R\cdot h_0(C)
+ \mathrm{coker}R\cdot h_1(C)$, the general-$R$ version of the first bullet printed by
p.63. -/
theorem kunneth_H1 {R₀ R₁ C₀ C₁ C₂ : Type*} [Fintype R₀] [Fintype R₁] [Fintype C₀]
    [Fintype C₁] [Fintype C₂] [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (R : Matrix R₀ R₁ (ZMod 2))
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH1 (koszulFaultComplex R dC1 dC2 hC)
      = twoTermH1 R * threeTermH0 dC1 + twoTermH0 R * threeTermH1 dC1 dC2 := by
  have h10 : (koszulFaultComplex R dC1 dC2 hC).d10_00
      = Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R := rfl
  have h01 : (koszulFaultComplex R dC1 dC2 hC).d01_00
      = Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  have h11 : (koszulFaultComplex R dC1 dC2 hC).d11_10
      = Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)) := rfl
  have h101 : (koszulFaultComplex R dC1 dC2 hC).d11_01
      = Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R := rfl
  have h02 : (koszulFaultComplex R dC1 dC2 hC).d02_01
      = Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  -- $\mathrm{rank}\,\partial_2 = |F_2| - \dim\ker\partial_2$
  have hmat2 : Module.finrank (ZMod 2) ↥(LinearMap.range (fd1
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
      = (Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀)
        - (Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
              * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
            + matRank dC2 * matRank R
            + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (fd1
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin
    have hcard : Fintype.card (FaultTerm2 (C₁ × R₁) (C₂ × R₀))
        = Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀ := by
      change Fintype.card ((C₁ × R₁) ⊕ (C₂ × R₀))
        = Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod]
    have hdom : Module.finrank (ZMod 2) ((C₁ × R₁) ⊕ (C₂ × R₀) → ZMod 2)
        = Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀ := by
      rw [Module.finrank_fintype_fun_eq_card, hcard]
    rw [hdom, finrank_ker_fd1 R dC1 dC2 hC] at hrn
    omega
  rw [faultH1, h10, h01, h11, h101, h02, finrank_ker_fd0 (C₂ := C₂) R dC1, hmat2]
  have hcoker : twoTermH0 R = Fintype.card R₀ - matRank R := by
    have := twoTermH0_add_matRank R
    omega
  have hquot : threeTermH0 dC1 = Fintype.card C₀ - matRank dC1 := finrank_quotient_range_eq dC1
  rw [hcoker, hquot]
  simp only [twoTermH1, threeTermH1]
  -- The arithmetic part of the bookkeeping: two rank-nullity identities, three
  -- comparisons and two bounds
  have hC1eq : matRank dC1 + Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
      = Fintype.card C₁ := by
    change Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin) = Fintype.card C₁
    have hr := LinearMap.finrank_range_add_finrank_ker dC1.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at hr
    exact hr
  have h2eq : matRank dC2 + Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      = Fintype.card C₂ := by
    change Module.finrank (ZMod 2) ↥(LinearMap.range dC2.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin) = Fintype.card C₂
    have hr := LinearMap.finrank_range_add_finrank_ker dC2.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at hr
    exact hr
  have hReq : matRank R + Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
      = Fintype.card R₁ := by
    have h := twoTermH1_add_matRank R
    simp only [twoTermH1] at h
    omega
  have hle1 : matRank dC1 ≤ Fintype.card C₀ := by
    change Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin) ≤ Fintype.card C₀
    calc Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin)
        ≤ Module.finrank (ZMod 2) (C₀ → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card C₀ := Module.finrank_fintype_fun_eq_card (ZMod 2)
  -- `hin`: dim ker ∂₂ ≤ |F₂|, likewise a consequence of linear algebra (the kernel lies in
  -- the domain), so no term-by-term arithmetic is needed
  have hdomF2 : Module.finrank (ZMod 2) (FaultTerm2 (C₁ × R₁) (C₂ × R₀) → ZMod 2)
      = Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀ := by
    change Module.finrank (ZMod 2) ((C₁ × R₁) ⊕ (C₂ × R₀) → ZMod 2)
      = Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_prod]
  have hin : Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
      + matRank dC2 * matRank R
      + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin)
      ≤ Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀ := by
    have hraw2 : Module.finrank (ZMod 2) ↥(LinearMap.ker (fd1
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
        ≤ Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀ := by
      calc Module.finrank (ZMod 2) ↥(LinearMap.ker (fd1
            (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
            (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
            (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
          ≤ Module.finrank (ZMod 2) (FaultTerm2 (C₁ × R₁) (C₂ × R₀) → ZMod 2) :=
            Submodule.finrank_le _
        _ = Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀ := hdomF2
    rw [finrank_ker_fd1 R dC1 dC2 hC] at hraw2
    exact hraw2
  -- `hout`: rank ∂₂ ≤ dim ker ∂₁ needs no arithmetic; it **is** the dimension consequence
  -- of the complex condition (im ∂₂ ⊆ ker ∂₁)
  have hraw : Module.finrank (ZMod 2) ↥(LinearMap.range (fd1
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₁ C₁ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC2 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
      ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker (fd0
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin) :=
    Submodule.finrank_mono (range_mulVecLin_le_ker_mulVecLin
      (koszulFaultComplex R dC1 dC2 hC).comp_d0_d1)
  have hout : Fintype.card C₁ * Fintype.card R₁ + Fintype.card C₂ * Fintype.card R₀
        - (Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
              * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
            + matRank dC2 * matRank R
            + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC2.mulVecLin))
      ≤ Fintype.card C₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        + matRank dC1 * matRank R := by
    rw [hmat2, finrank_ker_fd0 (C₂ := C₂) R dC1] at hraw
    exact hraw
  exact arith_H1_gen _ _ _ _ _ _ _ _ _ _ _ hC1eq h2eq hReq hle1
    (matRank_le_finrank_ker_of_mul_eq_zero dC1 dC2 hC)
    (by have := twoTermH0_add_matRank R; omega) hin hout


/-! ### 4.20 $H_0$: the last of the four degrees

$\dim H_0 = \mathrm{coker}R\cdot h_0(C)$ (not printed by p.63, but given by the general
shape of Künneth). Since $H_0 = \mathrm{coker}\,\partial_0$ is itself a **quotient**
dimension, the assembly differs slightly from the previous three: quotient dimension
$= |F_0| - \mathrm{rank}\,\partial_0$ (`finrank_quotient_range_eq`), and
$\mathrm{rank}\,\partial_0 = |F_1| - \dim\ker\partial_0$ (the new lemma
`matRank_eq_card_sub_finrank_ker` together with `finrank_ker_fd0` of §4.15); the two
bounds come, as in §4.19, from **linear algebra** (the kernel lies in the domain, the image
in the ambient space), and the bookkeeping is `arith_H0_gen` of §4.20 (same method).

**All four degrees over general $R$ are now machine-checked**: $H_3$ (§4.9), $H_2$ (§4.17),
$H_1$ (§4.19), $H_0$ (this section), the two bullets printed by p.63 and the other two
given by the general shape of Künneth. -/

/-- **The bookkeeping for $H_0$ (general $R$, pure arithmetic)**:
$$\Bigl(|C_0||\mathcal R_0|\Bigr)
  - \Bigl(|C_0||\mathcal R_1| + |C_1||\mathcal R_0| - \dim\ker\partial_0\Bigr)
  = \mathrm{coker}R\cdot h_0(C),$$
where $\dim\ker\partial_0 = |C_0|\dim\ker R + |\mathcal R_0|\dim\ker dC_1
+ \mathrm{rk}dC_1\,\mathrm{rk}R$ (§4.15). -/
theorem arith_H0_gen (n₀ kC1 rC1 kR rR ℓ m n₁ : ℕ)
    (hC1 : rC1 + kC1 = n₁) (hR : rR + kR = ℓ)
    (hle1 : rC1 ≤ n₀) (hleR : rR ≤ m)
    (hin : n₀ * kR + m * kC1 + rC1 * rR ≤ n₀ * ℓ + n₁ * m)
    (hout : n₀ * ℓ + n₁ * m - (n₀ * kR + m * kC1 + rC1 * rR) ≤ n₀ * m) :
    n₀ * m - (n₀ * ℓ + n₁ * m - (n₀ * kR + m * kC1 + rC1 * rR))
      = (m - rR) * (n₀ - rC1) := by
  have hC1' : ((rC1 + kC1 : ℕ) : ℤ) = (n₁ : ℤ) := by exact_mod_cast hC1
  have hR' : ((rR + kR : ℕ) : ℤ) = (ℓ : ℤ) := by exact_mod_cast hR
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hout, Nat.cast_sub hin]
  push_cast
  rw [← hC1', ← hR', Nat.cast_sub hle1, Nat.cast_sub hleR]
  push_cast
  ring

/-- "Rank = number of domain columns minus kernel dimension" (the reverse form of
`finrank_ker_eq_card_sub_matRank`, needed for the quotient-dimension bookkeeping of
$H_0$). -/
theorem matRank_eq_card_sub_finrank_ker {P Q : Type*} [Fintype P] [Fintype Q]
    (M : Matrix P Q (ZMod 2)) :
    matRank M = Fintype.card Q - Module.finrank (ZMod 2) ↥(LinearMap.ker M.mulVecLin) := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hd : Module.finrank (ZMod 2) (Q → ZMod 2) = Fintype.card Q :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  change Module.finrank (ZMod 2) ↥(LinearMap.range M.mulVecLin)
    = Fintype.card Q - Module.finrank (ZMod 2) ↥(LinearMap.ker M.mulVecLin)
  omega


/-- **The dimension of $H_0$ over general $R$**: $\dim H_0 = \mathrm{coker}R\cdot h_0(C)$,
the fourth degree, not printed by p.63 but given by the general shape of Künneth. -/
theorem kunneth_H0 {R₀ R₁ C₀ C₁ C₂ : Type*} [Fintype R₀] [Fintype R₁] [Fintype C₀]
    [Fintype C₁] [Fintype C₂] [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀]
    [DecidableEq C₁] [DecidableEq C₂] (R : Matrix R₀ R₁ (ZMod 2))
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH0 (koszulFaultComplex R dC1 dC2 hC) = twoTermH0 R * threeTermH0 dC1 := by
  have h10 : (koszulFaultComplex R dC1 dC2 hC).d10_00
      = Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R := rfl
  have h01 : (koszulFaultComplex R dC1 dC2 hC).d01_00
      = Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)) := rfl
  have hcard0 : Fintype.card (FaultTerm0 (C₀ × R₀)) = Fintype.card C₀ * Fintype.card R₀ := by
    change Fintype.card ((C₀ × R₀) ⊕ Fin 0) = Fintype.card C₀ * Fintype.card R₀
    rw [Fintype.card_sum, Fintype.card_fin, add_zero, Fintype.card_prod]
  have hcard1 : Fintype.card (FaultTerm1 (C₀ × R₁) (C₁ × R₀))
      = Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀ := by
    change Fintype.card ((C₀ × R₁) ⊕ (C₁ × R₀))
      = Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod]
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker (fd0
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
      = Fintype.card C₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        + matRank dC1 * matRank R := finrank_ker_fd0 (C₂ := C₂) R dC1
  -- Both bounds come from linear algebra (the method of §4.19): the kernel lies in the
  -- domain, the image in the ambient space
  have hin : Fintype.card C₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        + matRank dC1 * matRank R
      ≤ Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀ := by
    have hraw : Module.finrank (ZMod 2) ↥(LinearMap.ker (fd0
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
        ≤ Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀ := by
      calc Module.finrank (ZMod 2) ↥(LinearMap.ker (fd0
            (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
            (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
          ≤ Module.finrank (ZMod 2) (FaultTerm1 (C₀ × R₁) (C₁ × R₀) → ZMod 2) :=
            Submodule.finrank_le _
        _ = Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀ := by
            rw [Module.finrank_fintype_fun_eq_card, hcard1]
    rw [hker] at hraw
    exact hraw
  have hout : Fintype.card C₀ * Fintype.card R₁ + Fintype.card C₁ * Fintype.card R₀
        - (Fintype.card C₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
          + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
          + matRank dC1 * matRank R)
      ≤ Fintype.card C₀ * Fintype.card R₀ := by
    have hraw : Module.finrank (ZMod 2) ↥(LinearMap.range (fd0
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
        ≤ Fintype.card C₀ * Fintype.card R₀ := by
      calc Module.finrank (ZMod 2) ↥(LinearMap.range (fd0
            (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
            (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))).mulVecLin)
          ≤ Module.finrank (ZMod 2) (FaultTerm0 (C₀ × R₀) → ZMod 2) := Submodule.finrank_le _
        _ = Fintype.card C₀ * Fintype.card R₀ := by
            rw [Module.finrank_fintype_fun_eq_card, hcard0]
    have hraw' : matRank (fd0
        (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2))))
        ≤ Fintype.card C₀ * Fintype.card R₀ := hraw
    rw [matRank_eq_card_sub_finrank_ker, hcard1, hker] at hraw'
    exact hraw'
  rw [faultH0, h10, h01]
  change Module.finrank (ZMod 2) ((FaultTerm0 (C₀ × R₀) → ZMod 2) ⧸ LinearMap.range
      (Matrix.fromBlocks (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
        (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
        (0 : Matrix (Fin 0) (C₀ × R₁) (ZMod 2))
        (0 : Matrix (Fin 0) (C₁ × R₀) (ZMod 2))).mulVecLin)
    = twoTermH0 R * threeTermH0 dC1
  have hkerB : Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.fromBlocks
      (Matrix.kroneckerMap (fun a b => a * b) (1 : Matrix C₀ C₀ (ZMod 2)) R)
      (Matrix.kroneckerMap (fun a b => a * b) dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
      (0 : Matrix (Fin 0) (C₀ × R₁) (ZMod 2))
      (0 : Matrix (Fin 0) (C₁ × R₀) (ZMod 2))).mulVecLin)
      = Fintype.card C₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
        + Fintype.card R₀ * Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
        + matRank dC1 * matRank R := hker
  rw [finrank_quotient_range_eq, hcard0, matRank_eq_card_sub_finrank_ker, hcard1, hkerB]
  simp only [twoTermH0, threeTermH0]
  rw [finrank_quotient_range_eq R, finrank_quotient_range_eq dC1]
  have hC1eq : matRank dC1 + Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin)
      = Fintype.card C₁ := by
    change Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin)
      + Module.finrank (ZMod 2) ↥(LinearMap.ker dC1.mulVecLin) = Fintype.card C₁
    have hr := LinearMap.finrank_range_add_finrank_ker dC1.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at hr
    exact hr
  have hReq : matRank R + Module.finrank (ZMod 2) ↥(LinearMap.ker R.mulVecLin)
      = Fintype.card R₁ := by
    have h := twoTermH1_add_matRank R
    simp only [twoTermH1] at h
    omega
  have hle1 : matRank dC1 ≤ Fintype.card C₀ := by
    change Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin) ≤ Fintype.card C₀
    calc Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin)
        ≤ Module.finrank (ZMod 2) (C₀ → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card C₀ := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hleR : matRank R ≤ Fintype.card R₀ := by
    have h := twoTermH0_add_matRank R
    omega
  exact arith_H0_gen _ _ _ _ _ _ _ _ hC1eq hReq hle1 hleR hin hout

/-! ### 4.21 The four degrees on the two standard foliations: the landing of p.63 bullets

The formula of p.63 is read **directly off the source** for two kinds of $\mathcal R$:
"When $\mathcal R_\bullet$ is the repetition code, we have
$H_1(\mathcal R\otimes C) = H_1(\mathcal R)\otimes H_0(C)
= \{0,\mathbf 1\}\otimes C_0/\mathrm{im}H_X$ and $H_2(\mathcal R\otimes C)
= H_1(\mathcal R)\otimes H_1(C) = \{0,(1,0,\ldots,0)\}\otimes H_1(C)$", and the two are
interchanged on taking the dual.

The **entire mathematical content** of these two readings is the two-term homology of
$\mathcal R$: the full-rank parity-check matrix of the repetition code is surjective
($H_0(\mathcal R) = 0$, `repR_twoTermH0` of §4.8), and its kernel is spanned by the
all-ones vector ($H_1(\mathcal R)$ one-dimensional, `repR_twoTermH1`); on the dual side
$H_1(\mathcal R) = 0$ (`repR_transpose_twoTermH1`) and $H_0(\mathcal R)$ is one-dimensional
(`repR_transpose_twoTermH0`, added in this section). Substituting these into the four
general formulas of §4.17–20, the two bullets of the source are **four substitutions**, for
any number of rounds $\ell$.

The result is a **symmetric table** (dimensions; $h_j(C)$ is `threeTermH0/H1/H2` of §2.0.1):

| | $H_0(F)$ | $H_1(F)$ | $H_2(F)$ | $H_3(F)$ |
|---|---|---|---|---|
| repetition code $\mathcal R$ | $0$ | $h_0(C)$ | $h_1(C)$ | $h_2(C)$ |
| dual | $h_0(C)$ | $h_1(C)$ | $h_2(C)$ | $0$ |

Changing $\mathcal R$ only shifts the four entries one place in the table: on the
repetition side $H_2(F)$ is counted by $h_1(C)$ and $H_1(F)$ by $h_0(C)$; on the dual side
$H_1(F)$ is counted by $h_1(C)$ and $H_2(F)$ by $h_2(C)$.

**Physical reading** (the quantitative form of that sentence of p.63; the
**element-level** correspondence is still the source's, and this section does dimensions
only). By p.63, the elements of $H_1(F)$ are spacetime equivalence classes of logical
$\overline Z$ faults and those of $H_2(F)$ of logical $\overline X$ faults. The table says
that **the foliation decides which of the two fault types is counted by the logical space
of the code**: on the repetition side it is the $\overline X$ side
($\dim H_2(F) = h_1(C)$, exactly the "$\{0,(1,0,\ldots,0)\}\otimes H_1(C)$" written by
p.63), and on the dual side it switches to the $\overline Z$ side
($\dim H_1(F) = h_1(C)$); the other type is counted by $h_0(C)$ or $h_2(C)$ of the code
complex. The timelike instance of this library, `timeLikeRepR` ($= $`repR 3`, four rounds),
falls on the **repetition** side. -/

/-- **The dual-side $H_0(\mathcal R)$**: $\dim\mathrm{coker}R^{\mathsf T} = 1$, which
together with `repR_transpose_twoTermH1` ($H_1 = 0$) makes the two two-term homologies on
the dual side $(H_0, H_1) = (1, 0)$, the mirror of $(0, 1)$ on the repetition side. -/
theorem repR_transpose_twoTermH0 (l : ℕ) : twoTermH0 (repR l).transpose = 1 := by
  have h := twoTermH0_add_matRank (repR l).transpose
  have h1 : matRank (repR l).transpose = l := by
    rw [matRank_transpose (repR l), repR_matRank]
  rw [h1, Fintype.card_fin] at h
  omega

/-- **Repetition-side $H_0(F)$**: surjectivity of $R$ makes the whole term zero. -/
theorem kunneth_H0_repR (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
    [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH0 (koszulFaultComplex (repR l) dC1 dC2 hC) = 0 := by
  rw [kunneth_H0 (repR l) dC1 dC2 hC, repR_twoTermH0]
  ring

/-- **Repetition-side $H_1(F)$**: $\dim H_1(F) = h_0(C)$, the
"$H_1(\mathcal R)\otimes H_0(C) = \{0,\mathbf 1\}\otimes C_0/\mathrm{im}H_X$" of the first
bullet of p.63. -/
theorem kunneth_H1_repR (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
    [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH1 (koszulFaultComplex (repR l) dC1 dC2 hC) = threeTermH0 dC1 := by
  rw [kunneth_H1 (repR l) dC1 dC2 hC, repR_twoTermH1, repR_twoTermH0]
  ring

/-- **Repetition-side $H_2(F)$**: $\dim H_2(F) = h_1(C)$, the
"$H_1(\mathcal R)\otimes H_1(C) = \{0,(1,0,\ldots,0)\}\otimes H_1(C)$" of the second
bullet of p.63, i.e. the equivalence classes of $\overline X$ faults are counted by the
logical space of the code. -/
theorem kunneth_H2_repR (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
    [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH2 (koszulFaultComplex (repR l) dC1 dC2 hC) = threeTermH1 dC1 dC2 := by
  rw [kunneth_H2 (repR l) dC1 dC2 hC, repR_twoTermH1, repR_twoTermH0]
  ring

/-- **Repetition-side $H_3(F)$**: $\dim H_3(F) = h_2(C)$. -/
theorem kunneth_H3_repR (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
    [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH3 (koszulFaultComplex (repR l) dC1 dC2 hC) = threeTermH2 dC2 := by
  rw [kunneth_H3 (repR l) dC1 dC2 hC, repR_twoTermH1]
  ring

/-- **Dual-side $H_0(F)$**: $\dim H_0(F) = h_0(C)$. -/
theorem kunneth_H0_repR_transpose (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁]
    [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH0 (koszulFaultComplex (repR l).transpose dC1 dC2 hC) = threeTermH0 dC1 := by
  rw [kunneth_H0 (repR l).transpose dC1 dC2 hC, repR_transpose_twoTermH0]
  ring

/-- **Dual-side $H_1(F)$**: $\dim H_1(F) = h_1(C)$, the
"$H_0(\mathcal R)\otimes H_1(C) = \{0,(1,0,\ldots,0)\}\otimes H_1(C)$" of the dual line of
p.63, i.e. after passing to the dual it is the $\overline Z$ faults that are counted by
the logical space of the code. -/
theorem kunneth_H1_repR_transpose (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁]
    [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH1 (koszulFaultComplex (repR l).transpose dC1 dC2 hC) = threeTermH1 dC1 dC2 := by
  rw [kunneth_H1 (repR l).transpose dC1 dC2 hC, repR_transpose_twoTermH1,
    repR_transpose_twoTermH0]
  ring

/-- **Dual-side $H_2(F)$**: $\dim H_2(F) = h_2(C)$, the
"$H_0(\mathcal R)\otimes H_2(C) = \{0,\mathbf 1\}\otimes H_2(C)$" of the dual line of
p.63. -/
theorem kunneth_H2_repR_transpose (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁]
    [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH2 (koszulFaultComplex (repR l).transpose dC1 dC2 hC) = threeTermH2 dC2 := by
  rw [kunneth_H2 (repR l).transpose dC1 dC2 hC, repR_transpose_twoTermH1,
    repR_transpose_twoTermH0]
  ring

/-- **Dual-side $H_3(F)$**: injectivity of $R^{\mathsf T}$ makes the whole term zero. -/
theorem kunneth_H3_repR_transpose (l : ℕ) {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁]
    [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultH3 (koszulFaultComplex (repR l).transpose dC1 dC2 hC) = 0 := by
  rw [kunneth_H3 (repR l).transpose dC1 dC2 hC, repR_transpose_twoTermH1]
  ring

/-! ## 5. Honest boundary (the paper's main text cites this section)

**Machine-checked** (details in §4): **all four degrees over general $R$**
(`kunneth_H2` / `kunneth_H1` / `kunneth_H0` / `kunneth_H3` of §4.17/19/20/9), that is the
four $n$ of $\dim H_n = \sum_{i+j=n}\dim H_i(\mathcal R)\cdot\dim H_j(C)$; the four degrees
on the degenerate family $R = 0$ (`kunneth_H0_R_zero` … `kunneth_H3_R_zero`); the four
degrees on the two standard foliations, repetition code and its dual (of §4.21,
`kunneth_H0_repR` … `kunneth_H3_repR_transpose`), that is the landing of the two bullets
printed by p.63; and the block shapes needed for general $R$ (§4.3–4) together with the
inclusion direction (§4.5).

**The assembly of the four degrees over general $R$, and what is not done and not claimed**:

1. **$H_0/H_1/H_2$ over general $R$ are machine-checked** (landed item by item from §4.12,
   whose assembly this section records). The closed forms of these three (shaped by the
   numerical probe: $\dim H_0 = \mathrm{coker}R\cdot h_0(C)$,
   $\dim H_1 = \ker R\cdot h_0(C) + \mathrm{coker}R\cdot h_1(C)$,
   $\dim H_2 = \ker R\cdot h_1(C) + \mathrm{coker}R\cdot h_2(C)$, with 0 mismatches over
   136 random instances) reduce to the two intermediate kernels $\dim\ker\partial_2$ and
   $\dim\ker\partial_1$; and **every block** needed for the "fibre + rank" two-step
   decomposition of these two kernels now has an engine: $\dim\ker A$ and $\dim\ker B$ are
   the $\otimes\mathrm{id}$ engine of §3, $\dim\ker(C|_{\ker A})$ is the intersection of
   kernels of §4.9 (the same `finrank_inf_ker_kronecker`), and on the $\dim\ker\partial_1$
   side $\dim(\mathrm{im}(\mathrm{id}\otimes R)\cap\mathrm{im}(\partial_1\otimes\mathrm{id}))
   = \mathrm{rank}(dC_1)\cdot\mathrm{rank}\,R$ is an instance of the same lemma in the
   **full ambient space** (the two matrix-world terms are already machine-checked by
   `finrank_inf_range_koszul` and `_row` of §4.13) ($M = \mathbb F_2^{C_0}$, with no
   $\ker$ restriction; the matrix-world form is `finrank_inf_range_koszul_row` of §4.13),
   while the intersection of images on the $\dim\ker\partial_2$ side is
   `finrank_inf_range_koszul_data` (its matrix-world form is `finrank_inf_range_koszul` of
   §4.13). The general $2\times2$ block kernel formula of §4.14 is then applied to
   $\partial_2$ and to (block-row) $\partial_1$. The two closed forms are machine-checked
   in §4.15 (`finrank_ker_fd1` $= \dim\ker dC_1\cdot\dim\ker R
   + \mathrm{rank}(dC_2)\cdot\mathrm{rank}\,R + |\mathcal R_0|\cdot\dim\ker dC_2$, and
   `finrank_ker_fd0` $= |C_0|\cdot\dim\ker R + |\mathcal R_0|\cdot\dim\ker dC_1
   + \mathrm{rank}(dC_1)\cdot\mathrm{rank}\,R$, verbatim matching the probe's measurements).
   **$H_2$ is in the library (§4.16–17)**: $\dim H_2 = \dim\ker R\cdot h_1(C)
   + \mathrm{coker}R\cdot h_2(C)$ (`kunneth_H2`), i.e. the **second bullet** printed by
   p.63 holds over general $R$. Assembly: $\dim\ker\partial_2$ (§4.15) minus
   $\mathrm{rank}\,\partial_3$ (rank-nullity together with `kunneth_H3` of §4.9), the
   $\mathbb N$ bookkeeping of the subtraction being the pure arithmetic lemma
   `arith_H2_gen` of §4.16 (depending only on `propext` and `Quot.sound`).
   **$H_1$ is also in the library (§4.18–19)**: $\dim H_1 = \dim\ker R\cdot h_0(C)
   + \mathrm{coker}R\cdot h_1(C)$ (`kunneth_H1`), the **first bullet** printed by p.63.
   The assembly has the same shape, and the two bounds come from **linear algebra** (the
   kernel lies in the domain; the complex condition
   $\mathrm{im}\,\partial_2\subseteq\ker\partial_1$), so no term-by-term $\mathbb N$
   arithmetic is needed.
   **$H_0$ is also in the library (§4.20)**: $\dim H_0 = \mathrm{coker}R\cdot h_0(C)$
   (`kunneth_H0`).
   **Hence all four degrees over general $R$ are machine-checked**:
   $\dim H_n = \sum_{i+j=n}\dim H_i(\mathcal R)\cdot\dim H_j(C)$, the two bullets printed
   by p.63 ($H_1$, $H_2$) and the other two given by the general shape of Künneth ($H_0$,
   $H_3$). The four on the degenerate family $R = 0$ are as follows: there
   $H_0(\mathcal R) = \mathbb F_2^{\mathcal R_0}$ and
   $H_1(\mathcal R) = \mathbb F_2^{\mathcal R_1}$ are maximal, the differential of the
   Koszul total complex reduces to the "$\partial\otimes\mathrm{id}$" blocks with the cross
   terms, which contain $R$, vanishing, so any nondegenerate differential on $C$ gives
   $\dim H_0 = |\mathcal R_0|\,h_0(C)$,
   $\dim H_1 = |\mathcal R_1|\,h_0(C) + |\mathcal R_0|\,h_1(C)$,
   $\dim H_2 = |\mathcal R_1|\,h_1(C) + |\mathcal R_0|\,h_2(C)$,
   $\dim H_3 = |\mathcal R_1|\,h_2(C)$, where $h_j(C)$ is `threeTermH0/H1/H2`.
   The method is to write the four differentials for $R = 0$ as **block matrices** (the
   blocks of $T_0 \leftarrow T_1 \leftarrow T_2 \leftarrow T_3$) and add the kernel and
   image dimensions block by block: $m = 3$ uses the kernel of `fromBlocks A 0 0 0`
   (`finrank_ker_fromBlocks_fin0`), $m = 1,2$ use the **block-diagonal**
   $\binom{A\ 0}{0\ B}$ (`finrank_ker_fromBlocks_diag` / `matRank_fromBlocks_diag`), and
   $m = 0,1$ use the **block-row** $\binom{0\ B}{0\ 0}$
   (`matRank_fromBlocks_zeroLeft`), each of the three using once the rank bound
   `matRank_le_finrank_ker_of_mul_eq_zero` supplied by the CSS condition.
2. **What general $R$ gives is a dimension equality, not an isomorphism of homology**:
   $\dim H_3(\mathcal R\otimes C) = \dim H_1(\mathcal R)\cdot\dim H_2(C)$ comes from a
   dimension count. The block-column shape of `fd2` when $R\ne0$ gives the intersection of
   the two kernels, which under currying is the kernel of `piMulVec R` on tuple space
   $(\mathcal R_1 \to \ker\partial_2)$, then falls to the Π engine of a general module;
   this module does not construct the isomorphism $H_3 \cong H_2(C)\otimes H_1(\mathcal R)$
   itself.
3. **Not treated by this module**: the **element-level** interpretation of the physical
   reading of p.63 ($H_1(F)$ ↔ logical $\overline Z$ faults, $H^2(F)$ ↔ logical
   $\overline X$ faults); this module does dimensions only. The dimension half lands in
   §4.21: the closed forms of the four degrees on the two foliations say which degree of
   the code counts each of the two fault types; the **element level** (which class
   corresponds to which logical operator) is still the source's and is not in this library.
4. **Not treated by this module**: the boundary in item 2 of §4 of
   `Homology/FaultComplex.lean` (A.1 does not print the cone map $F$) and the Shor-instance
   homology reading of its §5; the Künneth formula is independent of the mapping cone.

**Trust base**: this module uses no `sorry` / `admit` / `native_decide` (the three concrete
instances of §2 use the kernel `decide`), and introduces no custom axiom; the
`#print axioms` of the load-bearing theorems is at the end of the root module
`QECCertificates.lean`.
-/


/-! ## 8. The **element level** of Künneth: the "spanning" half of decoupling

Everything above (§2 to §4) gives **dimensions**. This section gives one **element-level**
statement: making Lemma 7 of [56] (Decoupling of space and time faults) into a theorem
about **vectors** on the **timelike side of the repetition-code foliation**, that is, the
$H_1(F)$ term of [14] p.63, raised from "counting" to "what each cycle looks like".

**Object**: the **timelike embedding** `timelikeEmb` on
`F_1 = (C_0 × R_1) ⊕ (C_1 × R_0)`, sending $y : C_0 \to \mathbb F_2$ to the
$\mathrm{inl}$ block, **constant along the time index**, with the $\mathrm{inr}$ block
zero. It is the $y$ factor in the $H_1(\mathcal R)\otimes H_0(C)$ term.

**Three components**:

1. **Lands in the kernel** (`timelikeEmb_mem_ker`): when the **row sums of $R$ are even**
   ($R\cdot\mathbf 1 = 0$), a timelike vector is killed by $\partial_0$;
2. **The image of $\mathrm{im}\,\partial_C$ is a boundary** (`timelikeEmb_dC1_eq`):
   $\Phi(\partial_C z) = \partial_1(\text{a } z \text{ constant along time})$;
3. **The converse** (`mem_range_dC1_of_timelikeEmb_mem`): if $\Phi y$ is a boundary then
   $y\in\mathrm{im}\,\partial_C$, obtained by reading **any one time slice** of the
   $\mathrm{inl}$ block.

**Main theorem `ker_koszulD0_eq_sup`**: when the row sums are even and the dimension of
$H_1(F)$ equals $h_0(C)$,

$$\ker\partial_0 \;=\; \Phi(C_0) \;+\; \mathrm{im}\,\partial_1 .$$

The proof is a **dimension count** ($\Phi$ injective,
$T\sqcap\mathrm{im}\,\partial_1 = \Phi(\mathrm{im}\,\partial_C)$, both sides of dimension
$h_0(C)+\dim\mathrm{im}\,\partial_1$), **not a homology chase**.
**Instance `ker_koszulD0_repR_eq_sup`**: for $R=$ `repR l` the two hypotheses hold
automatically (even row sums by `repR_allOnes_mem_ker`, the count by `kunneth_H1_repR`).

**Boundary (must be stated alongside)**: this item covers only the **timelike side of the
repetition-code foliation** ($R$ surjective $\Rightarrow$ $\mathrm{coker}R=0$), i.e. the
$H_1 = H_1(\mathcal R)\otimes H_0(C)$ term; **the dual-foliation side**
($H_0(\mathcal R)\otimes H_1(C)$) is §9, and the case where **the two terms coexist over
general $R$** is §11. -/


/-! ### The timelike embedding (fully general, no topological hypothesis) -/

/-- The timelike embedding: $y \mapsto$ onto the $\mathrm{inl}$ block of `F_1`, constant
along the time index, with the $\mathrm{inr}$ block zero. -/
noncomputable def timelikeEmb (C R S : Type*) :
    (C → ZMod 2) →ₗ[ZMod 2] ((C × R) ⊕ S → ZMod 2) where
  toFun y := Sum.elim (fun p : C × R => y p.1) (0 : S → ZMod 2)
  map_add' y y' := by
    funext p
    rcases p with p | p <;> simp [Pi.add_apply]
  map_smul' c y := by
    funext p
    rcases p with p | p <;> simp

theorem timelikeEmb_apply_inl {C R S : Type*} (y : C → ZMod 2) (p : C × R) :
    timelikeEmb C R S y (Sum.inl p) = y p.1 := rfl

theorem timelikeEmb_apply_inr {C R S : Type*} (y : C → ZMod 2) (p : S) :
    timelikeEmb C R S y (Sum.inr p) = 0 := rfl

theorem timelikeEmb_injective {C R S : Type*} [Nonempty R] :
    Function.Injective (timelikeEmb C R S) := by
  intro y y' h
  funext c
  let t : R := Classical.arbitrary R
  have h1 := congrFun h (Sum.inl (c, t))
  simpa [timelikeEmb] using h1

theorem ker_timelikeEmb {C R S : Type*} [Nonempty R] :
    LinearMap.ker (timelikeEmb C R S) = ⊥ :=
  LinearMap.ker_eq_bot.mpr timelikeEmb_injective

/-! ### Component formulas for the block matrices -/

theorem fd0_mulVec_apply_inl {F₀₀ F₀₁ F₁₀ : Type*} [Fintype F₀₀] [Fintype F₀₁] [Fintype F₁₀]
    (d10 : Matrix F₀₀ F₁₀ (ZMod 2)) (d01 : Matrix F₀₀ F₀₁ (ZMod 2))
    (x : F₁₀ → ZMod 2) (p : F₀₀) :
    ((fd0 d10 d01) *ᵥ (Sum.elim x 0)) (Sum.inl p) = (d10 *ᵥ x) p := by
  simp only [fd0, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  simp

/-- The $\mathrm{inl}$ row of $\partial_1$ sees only the $\mathrm{inl}$ part of the input. -/
theorem fd1_mulVec_inl {F₁₀ F₀₁ F₁₁ F₀₂ : Type*} [Fintype F₁₀] [Fintype F₀₁]
    [Fintype F₁₁] [Fintype F₀₂]
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) (g : F₁₁ ⊕ F₀₂ → ZMod 2) (p : F₁₀) :
    ((fd1 d11_10 d11_01 d02_01) *ᵥ g) (Sum.inl p)
      = (d11_10 *ᵥ (fun q => g (Sum.inl q))) p := by
  simp only [fd1, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

/-- The $\mathrm{inr}$ row of $\partial_1$ sees both blocks. -/
theorem fd1_mulVec_inr {F₁₀ F₀₁ F₁₁ F₀₂ : Type*} [Fintype F₁₀] [Fintype F₀₁]
    [Fintype F₁₁] [Fintype F₀₂]
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) (g : F₁₁ ⊕ F₀₂ → ZMod 2) (p : F₀₁) :
    ((fd1 d11_10 d11_01 d02_01) *ᵥ g) (Sum.inr p)
      = (d11_01 *ᵥ (fun q => g (Sum.inl q))) p
        + (d02_01 *ᵥ (fun q => g (Sum.inr q))) p := by
  simp only [fd1, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem fd1_mulVec_sumElim_inl {F₁₀ F₀₁ F₁₁ F₀₂ : Type*} [Fintype F₁₀] [Fintype F₀₁]
    [Fintype F₁₁] [Fintype F₀₂]
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) (x : F₁₁ → ZMod 2) (p : F₁₀) :
    ((fd1 d11_10 d11_01 d02_01) *ᵥ (Sum.elim x 0)) (Sum.inl p) = (d11_10 *ᵥ x) p := by
  rw [fd1_mulVec_inl]
  rfl

theorem fd1_mulVec_sumElim_inr {F₁₀ F₀₁ F₁₁ F₀₂ : Type*} [Fintype F₁₀] [Fintype F₀₁]
    [Fintype F₁₁] [Fintype F₀₂]
    (d11_10 : Matrix F₁₀ F₁₁ (ZMod 2)) (d11_01 : Matrix F₀₁ F₁₁ (ZMod 2))
    (d02_01 : Matrix F₀₁ F₀₂ (ZMod 2)) (x : F₁₁ → ZMod 2) (p : F₀₁) :
    ((fd1 d11_10 d11_01 d02_01) *ᵥ (Sum.elim x 0)) (Sum.inr p) = (d11_01 *ᵥ x) p := by
  rw [fd1_mulVec_inr]
  have h1 : (fun q : F₀₂ => (Sum.elim x (0 : F₀₂ → ZMod 2)) (Sum.inr q))
      = (0 : F₀₂ → ZMod 2) := by
    funext q
    rfl
  rw [h1, Matrix.mulVec_zero, Pi.zero_apply, add_zero]
  have h2 : (fun q : F₁₁ => (Sum.elim x (0 : F₀₂ → ZMod 2)) (Sum.inl q)) = x := by
    funext q
    rfl
  rw [h2]

/-! ### The two Koszul differentials (written as bare blocks) -/

section Blocks

variable {R₀ R₁ C₀ C₁ C₂ : Type*}
variable [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂]
variable [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]

/-- The Koszul differential $F_1 \to F_0$. -/
abbrev koszulD0 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    Matrix (FaultTerm0 (C₀ × R₀)) (FaultTerm1 (C₀ × R₁) (C₁ × R₀)) (ZMod 2) :=
  fd0 (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R)
    (Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)))

/-- The Koszul differential $F_2 \to F_1$. -/
abbrev koszulD1 (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) :
    Matrix (FaultTerm1 (C₀ × R₁) (C₁ × R₀)) (FaultTerm2 (C₁ × R₁) (C₂ × R₀)) (ZMod 2) :=
  fd1 (Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
    (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R)
    (Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)))

omit [DecidableEq C₀] [DecidableEq C₁] in
theorem kron_one_mulVec_c (dC : Matrix C₀ C₁ (ZMod 2)) (w : C₁ × R₁ → ZMod 2)
    (c : C₀) (t : R₁) :
    ((Matrix.kronecker dC (1 : Matrix R₁ R₁ (ZMod 2))) *ᵥ w) (c, t)
      = (dC *ᵥ (fun c' => w (c', t))) c := by
  simpa [Matrix.kronecker, Matrix.mulVec, dotProduct] using
    kroneckerMap_one_mulVec_apply (A := dC) (x := w) c t

omit [DecidableEq R₀] [DecidableEq R₁] in
theorem kron_one_left_mulVec_c (R : Matrix R₀ R₁ (ZMod 2)) (w : C₁ × R₁ → ZMod 2)
    (c : C₁) (r : R₀) :
    ((Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ w) (c, r)
      = (R *ᵥ (fun t => w (c, t))) r := by
  simpa [Matrix.kronecker, Matrix.mulVec, dotProduct] using
    kroneckerMap_one_left_mulVec_apply (A := R) (x := w) c r

omit [DecidableEq R₀] [DecidableEq R₁] in
theorem kron_one_left_mulVec_c0 (R : Matrix R₀ R₁ (ZMod 2)) (w : C₀ × R₁ → ZMod 2)
    (c : C₀) (r : R₀) :
    ((Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) *ᵥ w) (c, r)
      = (R *ᵥ (fun t => w (c, t))) r := by
  simpa [Matrix.kronecker, Matrix.mulVec, dotProduct] using
    kroneckerMap_one_left_mulVec_apply (A := R) (x := w) c r

omit [DecidableEq R₀] [DecidableEq R₁] in
/-- When the row sums vanish, a vector constant along time is killed by
$\mathrm{id}\otimes R$ (the $C_0$ side). -/
theorem kron_one_left_mulVec_constC0 (R : Matrix R₀ R₁ (ZMod 2))
    (hRow : R *ᵥ (1 : R₁ → ZMod 2) = 0) (y : C₀ → ZMod 2) (c : C₀) (r : R₀) :
    ((Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) *ᵥ (fun p : C₀ × R₁ => y p.1))
      (c, r) = 0 := by
  rw [kron_one_left_mulVec_c0]
  show (R *ᵥ (fun _ : R₁ => y c)) r = 0
  have hconst : (fun _ : R₁ => y c) = y c • (1 : R₁ → ZMod 2) := by
    funext t
    simp
  rw [hconst, Matrix.mulVec_smul, hRow, smul_zero]
  rfl

omit [DecidableEq R₀] [DecidableEq R₁] in
/-- As above, the $C_1$ side. -/
theorem kron_one_left_mulVec_constC1 (R : Matrix R₀ R₁ (ZMod 2))
    (hRow : R *ᵥ (1 : R₁ → ZMod 2) = 0) (z : C₁ → ZMod 2) (c : C₁) (r : R₀) :
    ((Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ (fun p : C₁ × R₁ => z p.1))
      (c, r) = 0 := by
  rw [kron_one_left_mulVec_c]
  show (R *ᵥ (fun _ : R₁ => z c)) r = 0
  have hconst : (fun _ : R₁ => z c) = z c • (1 : R₁ → ZMod 2) := by
    funext t
    simp
  rw [hconst, Matrix.mulVec_smul, hRow, smul_zero]
  rfl

/-! ### The three components -/

variable (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))

omit [DecidableEq R₁] [DecidableEq C₁] in
/-- **Component 1**: when the row sums are even, a timelike vector lands in
$\ker\partial_0$. -/
theorem timelikeEmb_mem_ker (hRow : R *ᵥ (1 : R₁ → ZMod 2) = 0) (y : C₀ → ZMod 2) :
    timelikeEmb C₀ R₁ (C₁ × R₀) y ∈ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext p
  rcases p with p | e
  · simp only [Pi.zero_apply]
    show ((fd0 (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R)
          (Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)))) *ᵥ
          (Sum.elim (fun q : C₀ × R₁ => y q.1) 0)) (Sum.inl p) = (0 : ZMod 2)
    rw [fd0_mulVec_apply_inl]
    exact kron_one_left_mulVec_constC0 R hRow y p.1 p.2
  · exact Fin.elim0 e

omit [DecidableEq C₀] [DecidableEq C₂] in
/-- **Component 2**: $\Phi(\partial_C z)$ is a boundary. -/
theorem timelikeEmb_dC1_eq (hRow : R *ᵥ (1 : R₁ → ZMod 2) = 0) (z : C₁ → ZMod 2) :
    timelikeEmb C₀ R₁ (C₁ × R₀) (dC1 *ᵥ z)
      = (koszulD1 R dC1 dC2).mulVecLin (Sum.elim (fun p : C₁ × R₁ => z p.1) 0) := by
  funext p
  rcases p with p | p
  · show (timelikeEmb C₀ R₁ (C₁ × R₀) (dC1 *ᵥ z)) (Sum.inl p)
      = ((fd1 (Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
          (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R)
          (Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)))) *ᵥ
          (Sum.elim (fun q : C₁ × R₁ => z q.1) 0)) (Sum.inl p)
    rw [fd1_mulVec_sumElim_inl, kron_one_mulVec_c, timelikeEmb_apply_inl]
  · show (timelikeEmb C₀ R₁ (C₁ × R₀) (dC1 *ᵥ z)) (Sum.inr p)
      = ((fd1 (Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2)))
          (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R)
          (Matrix.kronecker dC2 (1 : Matrix R₀ R₀ (ZMod 2)))) *ᵥ
          (Sum.elim (fun q : C₁ × R₁ => z q.1) 0)) (Sum.inr p)
    rw [fd1_mulVec_sumElim_inr, timelikeEmb_apply_inr]
    exact (kron_one_left_mulVec_constC1 R hRow z p.1 p.2).symm

omit [DecidableEq C₀] [DecidableEq C₂] in
/-- **Component 3**: if $\Phi y$ is a boundary then $y \in \mathrm{im}\,\partial_C$. -/
theorem mem_range_dC1_of_timelikeEmb_mem [Nonempty R₁] {y : C₀ → ZMod 2}
    (hy : timelikeEmb C₀ R₁ (C₁ × R₀) y
      ∈ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin) :
    y ∈ LinearMap.range dC1.mulVecLin := by
  obtain ⟨g, hg⟩ := hy
  refine ⟨fun c' => g (Sum.inl (c', Classical.arbitrary R₁)), ?_⟩
  rw [Matrix.mulVecLin_apply]
  funext c
  have h1 := congrFun hg (Sum.inl (c, Classical.arbitrary R₁))
  rw [Matrix.mulVecLin_apply] at h1
  rw [fd1_mulVec_inl, kron_one_mulVec_c, timelikeEmb_apply_inl] at h1
  exact h1

/-! ### The spanning theorem -/

omit [DecidableEq C₂] in
/-- **The "spanning" half of decoupling** (the timelike side of the repetition-code
foliation): when the row sums are even and the dimension of $H_1(F)$ equals $h_0(C)$,
**every cycle is a timelike vector modulo a boundary**:
$\ker\partial_0 = \Phi(C_0) + \mathrm{im}\,\partial_1$. -/
theorem ker_koszulD0_eq_sup [Nonempty R₁]
    (hRow : R *ᵥ (1 : R₁ → ZMod 2) = 0)
    (hComplex : koszulD0 R dC1 * koszulD1 R dC1 dC2 = 0)
    (hCount : Module.finrank (ZMod 2) ↥(LinearMap.ker (koszulD0 R dC1).mulVecLin)
        - Module.finrank (ZMod 2) ↥(LinearMap.range (koszulD1 R dC1 dC2).mulVecLin)
      = threeTermH0 dC1) :
    LinearMap.ker (koszulD0 R dC1).mulVecLin
      = LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀))
        ⊔ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin := by
  have hTK : LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀))
      ≤ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
    rintro _ ⟨y, rfl⟩
    exact timelikeEmb_mem_ker R dC1 hRow y
  have hSK : LinearMap.range (koszulD1 R dC1 dC2).mulVecLin
      ≤ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec g (koszulD0 R dC1) (koszulD1 R dC1 dC2), hComplex]
    exact Matrix.zero_mulVec g
  refine (Submodule.eq_of_le_of_finrank_eq (sup_le hTK hSK) ?_).symm
  have hTfin : Module.finrank (ZMod 2) ↥(LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀)))
      = Fintype.card C₀ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (timelikeEmb C₀ R₁ (C₁ × R₀))
    rw [ker_timelikeEmb] at h1
    simp only [finrank_bot, add_zero] at h1
    rw [h1, Module.finrank_fintype_fun_eq_card]
  have hInffin : Module.finrank (ZMod 2)
        ↥(LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀))
          ⊓ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin)
      = matRank dC1 := by
    have hInf : LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀))
          ⊓ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin
        = Submodule.map (timelikeEmb C₀ R₁ (C₁ × R₀)) (LinearMap.range dC1.mulVecLin) := by
      ext x
      constructor
      · rintro ⟨⟨y, rfl⟩, hx⟩
        exact ⟨y, mem_range_dC1_of_timelikeEmb_mem R dC1 dC2 hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, rfl⟩ := hy
        exact ⟨⟨_, rfl⟩, ⟨_, (timelikeEmb_dC1_eq R dC1 dC2 hRow z).symm⟩⟩
    rw [hInf]
    have hcomp : Submodule.map (timelikeEmb C₀ R₁ (C₁ × R₀)) (LinearMap.range dC1.mulVecLin)
        = LinearMap.range ((timelikeEmb C₀ R₁ (C₁ × R₀)).comp
            (LinearMap.range dC1.mulVecLin).subtype) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨⟨y, hy⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [hcomp]
    have hinj : Function.Injective ((timelikeEmb C₀ R₁ (C₁ × R₀)).comp
        (LinearMap.range dC1.mulVecLin).subtype) :=
      timelikeEmb_injective.comp (fun (x y : ↥(LinearMap.range dC1.mulVecLin))
        (hxy : (x : C₀ → ZMod 2) = (y : C₀ → ZMod 2)) => Subtype.ext hxy)
    rw [LinearMap.finrank_range_of_inj hinj]
    rfl
  have hthree : threeTermH0 dC1 = Fintype.card C₀ - matRank dC1 := finrank_quotient_range_eq dC1
  have hrank : matRank dC1 ≤ Fintype.card C₀ := by
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.range dC1.mulVecLin) ≤ Fintype.card C₀ := by
      rw [← Module.finrank_fintype_fun_eq_card (ZMod 2)]
      exact Submodule.finrank_le _
    simpa [matRank] using h1
  have hKfin : Module.finrank (ZMod 2) ↥(LinearMap.ker (koszulD0 R dC1).mulVecLin)
      = threeTermH0 dC1
        + Module.finrank (ZMod 2) ↥(LinearMap.range (koszulD1 R dC1 dC2).mulVecLin) := by
    have hle : Module.finrank (ZMod 2) ↥(LinearMap.range (koszulD1 R dC1 dC2).mulVecLin)
        ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker (koszulD0 R dC1).mulVecLin) :=
      Submodule.finrank_mono hSK
    omega
  have hsup : Module.finrank (ZMod 2)
        ↥(LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀))
          ⊔ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin)
      = Fintype.card C₀
        + Module.finrank (ZMod 2) ↥(LinearMap.range (koszulD1 R dC1 dC2).mulVecLin)
        - matRank dC1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (timelikeEmb C₀ R₁ (C₁ × R₀)))
      (LinearMap.range (koszulD1 R dC1 dC2).mulVecLin)
    rw [hTfin, hInffin] at h
    exact Nat.eq_sub_of_add_eq h
  rw [hsup, hKfin, hthree]
  omega

end Blocks

/-! ### The instance on the repetition-code foliation -/

section RepR

variable {C₀ C₁ C₂ : Type*}
variable [Fintype C₀] [Fintype C₁] [Fintype C₂]
variable [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]

/-- **The spanning theorem on the repetition-code foliation**: for $R =$ `repR l` the two
hypotheses hold automatically (the count given by `repR_surjective` is supplied by
`kunneth_H1_repR`, and even row sums by `repR_allOnes_mem_ker`), so **every cycle is a
timelike vector modulo a boundary**. -/
theorem ker_koszulD0_repR_eq_sup (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    LinearMap.ker (koszulD0 (repR l) dC1).mulVecLin
      = LinearMap.range (timelikeEmb C₀ (Fin (l + 1)) (C₁ × Fin l))
        ⊔ LinearMap.range (koszulD1 (repR l) dC1 dC2).mulVecLin := by
  refine ker_koszulD0_eq_sup (repR l) dC1 dC2 ?_ ?_ ?_
  · rw [← Matrix.mulVecLin_apply]
    exact repR_allOnes_mem_ker l
  · exact (koszulFaultComplex (repR l) dC1 dC2 hC).comp_d0_d1
  · exact kunneth_H1_repR l dC1 dC2 hC

end RepR

/-! ## 9. The **element level** of Künneth (dual side): the $H_0(\mathcal R)\otimes H_1(C)$ half

§8 did the **timelike side** ($R$ surjective, $H_1 = H_1(\mathcal R)\otimes H_0(C)$); this
item does the **dual side**: when $R$ is injective ($\ker R = 0$), $\mathrm{coker}\,R$ is
one-dimensional, $H_1 = H_0(\mathcal R)\otimes H_1(C)$, and what carries the weight is the
spacelike $C_1$ term.

**Main theorem** (`ker_koszulD0_eq_sup_of_injective`): for $\ker R = 0$ and
$\partial_0\partial_1 = 0$,

$$\ker\partial_0 \;=\; S \;+\; \mathrm{im}\,\partial_1,\qquad
  S = \{\,f : f|_{\mathrm{inl}} = 0,\ \forall r,\ dC_1\,(f|_{\mathrm{inr}})_r = 0\,\}.$$

**The difference from §8 (the valuable difference)**: §8 needs the two hypotheses "even row
sums + the dimension of $H_1(F)$ $= h_0(C)$", the second of which is a **counting input**;
this item needs **only that $R$ is injective**, with no counting at all. The condition
$\ker R = 0$ makes the readings of the `inl` block uniquely solvable, so the whole equality
reduces to an **element-level** proposition (the `inl` block lands in
$\mathrm{im}(dC_1\otimes1)$), and that half is given by **dot-product duality**:
`mem_range_mulVecLin_iff_forall_dot_eq_zero` says the **column space $=$ the orthogonal
complement of the left kernel** (the direction $\Rightarrow$ is one line of
`dotProduct_mulVec`; the direction $\Leftarrow$ goes through
`Subspace.dualAnnihilator_dualCoannihilator_eq` together with the dot-product equivalence
`dotProductEquiv`).

**Three steps of the proof**: (1) the reading of $\partial_0$ on the `inl` row is the sum
of two blocks, and a cycle gives $(1\otimes R)\,a = (dC_1\otimes1)\,h$; (2) summing with
weights $\mu\in\ker dC_1^{\mathsf T}$, injectivity of $R$ annihilates
$\sum_c \mu_c\,a_c$, so the `inl` reading of every time slice is orthogonal to
$\ker dC_1^{\mathsf T}$; (3) hence $a\in\mathrm{im}(dC_1\otimes1_{R_1})$, and after taking
a preimage $g$ the two blocks of $f-\partial_1 g$ each fall into place.

**Boundary (must be stated alongside)**: this item covers only the **dual foliation**
($\ker R = 0$), i.e. the $H_1 = H_0(\mathcal R)\otimes H_1(C)$ term; the case where **the
two terms coexist over general $R$** is §11.
-/

section DualFoliage

variable {R₀ R₁ C₀ C₁ C₂ : Type*}
variable [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂]
variable [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]

/-! ### Dot-product duality: the orthogonal-complement characterisation of `range` -/

section DotDual

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **The orthogonal-complement characterisation of `range`**: the column space $=$ the
"orthogonal complement" of the left kernel.  This is the same statement as
`QECCertificates.mem_range_mulVecLin_iff_forall_dot_eq_zero`, re-exported under this
module's namespace; the proof is that lemma. -/
theorem mem_range_mulVecLin_iff_forall_dot_eq_zero {M : Matrix α β (ZMod 2)}
    (v : α → ZMod 2) :
    v ∈ LinearMap.range M.mulVecLin
      ↔ ∀ μ : α → ZMod 2, Mᵀ *ᵥ μ = 0 → μ ⬝ᵥ v = 0 :=
  QECCertificates.mem_range_mulVecLin_iff_forall_dot_eq_zero v

end DotDual

/-! ### The spacelike embedding and the slice kernel -/

/-- **The spacelike embedding**: sends $g$ to the `inr` block, with the `inl` block zero. -/
def spacelikeEmb (A B : Type*) [Fintype A] [Fintype B] :
    (B → ZMod 2) →ₗ[ZMod 2] (A ⊕ B → ZMod 2) where
  toFun g := Sum.elim 0 g
  map_add' g g' := by funext i; rcases i with a | b <;> rfl
  map_smul' c g := by funext i; rcases i with a | b <;> rfl

theorem spacelikeEmb_apply_inl {A B : Type*} [Fintype A] [Fintype B]
    (g : B → ZMod 2) (a : A) : spacelikeEmb A B g (Sum.inl a) = 0 := rfl

theorem spacelikeEmb_apply_inr {A B : Type*} [Fintype A] [Fintype B]
    (g : B → ZMod 2) (b : B) : spacelikeEmb A B g (Sum.inr b) = g b := rfl

theorem spacelikeEmb_injective {A B : Type*} [Fintype A] [Fintype B] :
    Function.Injective (spacelikeEmb A B) := by
  intro g g' h
  funext b
  have h1 := congrFun h (Sum.inr b)
  simpa [spacelikeEmb] using h1

theorem ker_spacelikeEmb {A B : Type*} [Fintype A] [Fintype B] :
    LinearMap.ker (spacelikeEmb A B) = ⊥ :=
  LinearMap.ker_eq_bot.mpr spacelikeEmb_injective

/-- **The slice kernel**: the vectors whose `inr` block lies in $\ker dC_1$ at every
$R_0$-slice. -/
def sliceKer (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    Submodule (ZMod 2) (C₁ × R₀ → ZMod 2) where
  carrier := {g | ∀ r, dC1 *ᵥ (fun c => g (c, r)) = 0}
  zero_mem' := by
    intro r
    rw [show (fun c => (0 : C₁ × R₀ → ZMod 2) (c, r)) = 0 from rfl, Matrix.mulVec_zero]
  add_mem' := by
    intro x y hx hy r
    rw [show (fun c => (x + y) (c, r)) = (fun c => x (c, r)) + (fun c => y (c, r)) from rfl,
      Matrix.mulVec_add, hx r, hy r, add_zero]
  smul_mem' := by
    intro a x hx r
    rw [show (fun c => (a • x) (c, r)) = a • (fun c => x (c, r)) from rfl,
      Matrix.mulVec_smul, hx r, smul_zero]

omit [Fintype R₀] [Fintype C₀] [DecidableEq R₀] [DecidableEq C₀] [DecidableEq C₁] in
theorem mem_sliceKer {dC1 : Matrix C₀ C₁ (ZMod 2)} {g : C₁ × R₀ → ZMod 2} :
    g ∈ sliceKer (R₀ := R₀) dC1 ↔ ∀ r, dC1 *ᵥ (fun c => g (c, r)) = 0 := Iff.rfl

/-- **The spacelike subspace $S$**: the `inl` block is zero and the `inr` block lies in
the slice kernel. -/
noncomputable def spacelikeSub (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    Submodule (ZMod 2) ((C₀ × R₁) ⊕ (C₁ × R₀) → ZMod 2) :=
  Submodule.map (spacelikeEmb (C₀ × R₁) (C₁ × R₀)) (sliceKer (R₀ := R₀) dC1)

omit [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀] [DecidableEq C₁] in
theorem mem_spacelikeSub {dC1 : Matrix C₀ C₁ (ZMod 2)}
    {f : (C₀ × R₁) ⊕ (C₁ × R₀) → ZMod 2} :
    f ∈ spacelikeSub (R₀ := R₀) (R₁ := R₁) dC1 ↔
      (∀ p : C₀ × R₁, f (Sum.inl p) = 0)
        ∧ (∀ r, dC1 *ᵥ (fun c => f (Sum.inr (c, r))) = 0) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨fun p => rfl, fun r => by simpa [spacelikeEmb] using hg r⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun p : C₁ × R₀ => f (Sum.inr p), fun r => by simpa [spacelikeEmb] using h2 r, ?_⟩
    funext q
    rcases q with q | q
    · simpa [spacelikeEmb] using (h1 q).symm
    · rfl

/-! ### The block readings of $\partial_0$ -/

/-- The reading of $\partial_0$ (block-row $(A\ \ B)$) on the `inl` row: each of the two
blocks contributes once. -/
theorem fd0_mulVec_apply_inl_add {F₀₀ F₀₁ F₁₀ : Type*} [Fintype F₀₀] [Fintype F₀₁]
    [Fintype F₁₀] (A : Matrix F₀₀ F₁₀ (ZMod 2)) (B : Matrix F₀₀ F₀₁ (ZMod 2))
    (x : F₁₀ ⊕ F₀₁ → ZMod 2) (p : F₀₀) :
    ((fd0 A B) *ᵥ x) (Sum.inl p)
      = (A *ᵥ (fun q => x (Sum.inl q))) p + (B *ᵥ (fun q => x (Sum.inr q))) p := by
  simp only [fd0, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]

/-! ### The two inclusions -/

omit [DecidableEq R₁] [DecidableEq C₁] in
/-- **$S\le\ker\partial_0$** (no hypothesis on $R$ is needed: on the `inl` row,
$\partial_0$ sees only the `inl` block). -/
theorem spacelikeSub_le_ker (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    spacelikeSub (R₀ := R₀) (R₁ := R₁) dC1
      ≤ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
  intro f hf
  obtain ⟨h1, h2⟩ := mem_spacelikeSub.mp hf
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext p
  rw [Pi.zero_apply]
  rcases p with p | e
  · rw [fd0_mulVec_apply_inl_add]
    rw [show (fun q : C₀ × R₁ => f (Sum.inl q)) = 0 from funext h1]
    rw [Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    rw [kron_one_mulVec_c]
    exact congrFun (h2 p.2) p.1
  · exact Fin.elim0 e

omit [DecidableEq C₂] in
/-- **$S\sqcup\mathrm{im}\,\partial_1\le\ker\partial_0$**: the latter is exactly the
complex condition $\partial_0\partial_1=0$. -/
theorem spacelike_sup_le_ker (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hComplex : koszulD0 R dC1 * koszulD1 R dC1 dC2 = 0) :
    spacelikeSub (R₀ := R₀) (R₁ := R₁) dC1
        ⊔ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin
      ≤ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
  refine sup_le (spacelikeSub_le_ker R dC1) ?_
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec x (koszulD0 R dC1) (koszulD1 R dC1 dC2),
    hComplex, Matrix.zero_mulVec]

/-! ### The main theorem -/

/-- Over `ZMod 2`, $a+b=0$ gives $a=b$. -/
theorem eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have hw : b + b = (0 : ZMod 2) := CharTwo.add_self_eq_zero b
  calc a = a + 0 := (add_zero a).symm
    _ = a + (b + b) := by rw [hw, add_zero]
    _ = a + b + b := (add_assoc a b b).symm
    _ = 0 + b := by rw [h]
    _ = b := zero_add b

omit [DecidableEq C₂] in
/-- **The spanning theorem on the dual foliation** (the dual side of §8): when
$\ker R=0$, $\ker\partial_0 = S + \mathrm{im}\,\partial_1$.

**The difference from §8**: §8 needs the two hypotheses "even row sums + the dimension of
$H_1(F)$ $=h_0(C)$"; this item needs **only that $R$ is injective**, with no counting
hypothesis. The condition `ker R = 0` makes the readings of the `inl` block solvable, and
the half "the solution lies in $\mathrm{im}(dC_1\otimes1)$" is given by dot-product
duality. -/
theorem ker_koszulD0_eq_sup_of_injective (R : Matrix R₀ R₁ (ZMod 2))
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hInj : Function.Injective R.mulVecLin)
    (hComplex : koszulD0 R dC1 * koszulD1 R dC1 dC2 = 0) :
    LinearMap.ker (koszulD0 R dC1).mulVecLin
      = spacelikeSub (R₀ := R₀) (R₁ := R₁) dC1
        ⊔ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin := by
  refine le_antisymm ?_ (spacelike_sup_le_ker R dC1 dC2 hComplex)
  intro f hf
  have hf0 : koszulD0 R dC1 *ᵥ f = 0 := by
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hf
  -- The reading at each `(c,r)`: the two contributions of the two blocks are equal
  have hkey : ∀ (c : C₀) (r : R₀),
      (R *ᵥ (fun t => f (Sum.inl (c, t)))) r
        = (dC1 *ᵥ (fun c' => f (Sum.inr (c', r)))) c := by
    intro c r
    have h1 := congrFun hf0 (Sum.inl (c, r))
    rw [Pi.zero_apply, fd0_mulVec_apply_inl_add, kron_one_left_mulVec_c0,
      kron_one_mulVec_c] at h1
    exact eq_of_add_eq_zero h1
  -- The dot-product step: `μ ∈ ker dC₁ᵀ` ⟹ the reading of every time slice is orthogonal
  have hz : ∀ μ : C₀ → ZMod 2, dC1ᵀ *ᵥ μ = 0 →
      ∀ t : R₁, μ ⬝ᵥ (fun c => f (Sum.inl (c, t))) = 0 := by
    intro μ hμ t
    have hker : R *ᵥ (fun t' : R₁ => ∑ c, μ c * f (Sum.inl (c, t'))) = 0 := by
      funext r
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.zero_apply]
      rw [Finset.sum_comm]
      have h2 : ∀ c : C₀, (∑ t', R r t' * (μ c * f (Sum.inl (c, t'))))
          = μ c * (R *ᵥ (fun t' => f (Sum.inl (c, t')))) r := by
        intro c
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t' _ => by ring
      simp only [h2, hkey]
      rw [show (∑ c, μ c * (dC1 *ᵥ (fun c' => f (Sum.inr (c', r)))) c)
          = μ ⬝ᵥ (dC1 *ᵥ (fun c' => f (Sum.inr (c', r)))) from rfl,
        dot_mulVec_transpose, hμ, zero_dotProduct]
    have hzero : (fun t' : R₁ => ∑ c, μ c * f (Sum.inl (c, t'))) = 0 :=
      hInj (by rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hker, Matrix.mulVec_zero])
    have hfin := congrFun hzero t
    simpa [dotProduct] using hfin
  -- Every time slice lies in the column space of `dC₁`
  have hmem : ∀ t : R₁, ∃ w : C₁ → ZMod 2, dC1 *ᵥ w = fun c => f (Sum.inl (c, t)) := by
    intro t
    have h1 : (fun c => f (Sum.inl (c, t))) ∈ LinearMap.range dC1.mulVecLin :=
      (mem_range_mulVecLin_iff_forall_dot_eq_zero (M := dC1) _).mpr fun μ hμ => hz μ hμ t
    rw [LinearMap.mem_range] at h1
    simpa only [Matrix.mulVecLin_apply] using h1
  choose g hg using hmem
  set gs : (C₁ × R₁) ⊕ (C₂ × R₀) → ZMod 2 :=
    Sum.elim (fun p : C₁ × R₁ => g p.2 p.1) 0 with hgs
  have hinl_eq : ∀ p : C₀ × R₁, ((koszulD1 R dC1 dC2) *ᵥ gs) (Sum.inl p)
      = f (Sum.inl p) := by
    intro p
    rw [hgs, fd1_mulVec_sumElim_inl, kron_one_mulVec_c]
    exact congrFun (hg p.2) p.1
  refine Submodule.mem_sup.mpr
    ⟨f - (koszulD1 R dC1 dC2) *ᵥ gs, ?_, (koszulD1 R dC1 dC2) *ᵥ gs, ⟨gs, rfl⟩,
      sub_add_cancel _ _⟩
  rw [mem_spacelikeSub]
  have hker : (f - (koszulD1 R dC1 dC2) *ᵥ gs)
      ∈ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub,
      show (koszulD0 R dC1) *ᵥ ((koszulD1 R dC1 dC2) *ᵥ gs) = 0 from by
        rw [Matrix.mulVec_mulVec, hComplex, Matrix.zero_mulVec],
      hf0, sub_zero]
  refine ⟨fun p => ?_, fun r => ?_⟩
  · rw [Pi.sub_apply, hinl_eq p, sub_self]
  · funext c
    have h2' : (koszulD0 R dC1) *ᵥ (f - (koszulD1 R dC1 dC2) *ᵥ gs) = 0 :=
      hker
    have h2 := congrFun h2' (Sum.inl (c, r))
    rw [Pi.zero_apply, fd0_mulVec_apply_inl_add] at h2
    rw [show (fun q : C₀ × R₁ => (f - (koszulD1 R dC1 dC2) *ᵥ gs) (Sum.inl q)) = 0 from
        funext fun q => by rw [Pi.sub_apply, hinl_eq q, sub_self, Pi.zero_apply],
      Matrix.mulVec_zero, Pi.zero_apply, zero_add] at h2
    rw [kron_one_mulVec_c] at h2
    exact h2

end DualFoliage


-- The arguments of the two `simp only` calls of this section are **deliberately kept the
-- same set** (`add_zero`/`zero_add` are needed by one and redundant but harmless in the
-- other). The linter is turned off here so that the two writings are not made
-- inconsistent just to silence one warning.
set_option linter.unusedSimpArgs false

/-! ## 11. Decoupling spanning over general $R$: $\ker\partial_0 = S + \mathrm{im}\,\partial_1 + T$

§8 and §9 are the two **degenerate endpoints** of this item ($1\in\ker R$ and
$\ker R=0$). Over general $R$ the missing piece is **not** "constant along time" (the
probe `tools/probe_decoupling_mixed.jl` ruled that form out) but a larger $T$: **every
$C_0$-fibre lies in $\ker R$**.

**Method of proof** (no homology chase, no dimension count): split the `inl` part $u$ of
$f$ along `projMat dC1` into $u_1$ (landing in $\mathrm{im}(dC_1\otimes1)$) and $u-u_1$;
the latter is killed by $\mathrm{id}\otimes R$, because the projection **commutes** with
$\mathrm{id}\otimes R$ and **is the identity** on $\mathrm{im}\,dC_1$, so $u-u_1\in T$; the
remaining $(0,\cdot)$ lies in the kernel, hence in $S$. -/

section GeneralR

variable {R₀ R₁ C₀ C₁ C₂ : Type*}
variable [Fintype R₀] [Fintype R₁] [Fintype C₀] [Fintype C₁] [Fintype C₂]
variable [DecidableEq R₀] [DecidableEq R₁] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]

/-! ### The timelike subspace `T` -/

/-- **The timelike subspace $T$**: on the `inl` block every $C_0$-fibre
`t ↦ f (inl (c,t))` lies in $\ker R$, and the `inr` block is zero (i.e. the image of
$C_0\otimes\ker R$). It generalises the "constant along time" branch. -/
def timelikeSub (R : Matrix R₀ R₁ (ZMod 2)) :
    Submodule (ZMod 2) (FaultTerm1 (C₀ × R₁) (C₁ × R₀) → ZMod 2) where
  carrier := {f | (∀ e : C₁ × R₀, f (Sum.inr e) = 0)
    ∧ ∀ c : C₀, R *ᵥ (fun t : R₁ => f (Sum.inl (c, t))) = 0}
  zero_mem' := ⟨fun e => rfl, fun c => by
    rw [show (fun t : R₁ => (0 : FaultTerm1 (C₀ × R₁) (C₁ × R₀) → ZMod 2) (Sum.inl (c, t)))
        = 0 from rfl, Matrix.mulVec_zero]⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun e => ?_, fun c => ?_⟩
    · simp only [Pi.add_apply, hx1 e, hy1 e, add_zero]
    · rw [show (fun t : R₁ => (x + y) (Sum.inl (c, t)))
          = (fun t => x (Sum.inl (c, t))) + (fun t => y (Sum.inl (c, t))) from rfl,
        Matrix.mulVec_add, hx2 c, hy2 c, add_zero]
  smul_mem' := by
    rintro a x ⟨hx1, hx2⟩
    refine ⟨fun e => ?_, fun c => ?_⟩
    · simp only [Pi.smul_apply, hx1 e, smul_zero]
    · rw [show (fun t : R₁ => (a • x) (Sum.inl (c, t)))
          = a • (fun t => x (Sum.inl (c, t))) from rfl,
        Matrix.mulVec_smul, hx2 c, smul_zero]

omit [Fintype R₀] [Fintype C₀] [Fintype C₁] [DecidableEq R₀] [DecidableEq R₁]
  [DecidableEq C₀] [DecidableEq C₁] in
theorem mem_timelikeSub {R : Matrix R₀ R₁ (ZMod 2)}
    {f : FaultTerm1 (C₀ × R₁) (C₁ × R₀) → ZMod 2} :
    f ∈ timelikeSub (R₀ := R₀) (R₁ := R₁) (C₀ := C₀) (C₁ := C₁) R
      ↔ (∀ e : C₁ × R₀, f (Sum.inr e) = 0)
        ∧ ∀ c : C₀, R *ᵥ (fun t : R₁ => f (Sum.inl (c, t))) = 0 := Iff.rfl

omit [DecidableEq R₁] [DecidableEq C₁] in
/-- **$T\le\ker\partial_0$**, with no hypothesis on $R, dC_1$. -/
theorem timelikeSub_le_ker (R : Matrix R₀ R₁ (ZMod 2)) (dC1 : Matrix C₀ C₁ (ZMod 2)) :
    timelikeSub (R₀ := R₀) (R₁ := R₁) (C₀ := C₀) (C₁ := C₁) R
      ≤ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
  intro f hf
  obtain ⟨h1, h2⟩ := mem_timelikeSub.mp hf
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext p
  rw [Pi.zero_apply]
  rcases p with p | e
  · have hz : (fun q : C₁ × R₀ => f (Sum.inr q)) = 0 := funext h1
    rw [fd0_mulVec_apply_inl_add, kron_one_left_mulVec_c0, h2 p.1, hz, Matrix.mulVec_zero]
    simp
  · exact Fin.elim0 e

/-! ### The projection onto `im dC1` -/

noncomputable def projLift (M : Matrix C₀ C₁ (ZMod 2)) :
    (C₀ → ZMod 2) →ₗ[ZMod 2] ↥(LinearMap.range M.mulVecLin) :=
  ((LinearMap.range M.mulVecLin).subtype.exists_leftInverse_of_injective
    (LinearMap.range M.mulVecLin).ker_subtype).choose

/-- **The projection onto `im dC1`**: the only external tool this theorem needs. -/
noncomputable def projToRange (M : Matrix C₀ C₁ (ZMod 2)) :
    (C₀ → ZMod 2) →ₗ[ZMod 2] (C₀ → ZMod 2) :=
  (LinearMap.range M.mulVecLin).subtype.comp (projLift M)

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] in
theorem projLift_comp (M : Matrix C₀ C₁ (ZMod 2)) :
    (projLift M).comp (LinearMap.range M.mulVecLin).subtype = LinearMap.id :=
  ((LinearMap.range M.mulVecLin).subtype.exists_leftInverse_of_injective
    (LinearMap.range M.mulVecLin).ker_subtype).choose_spec

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] in
theorem projLift_apply (M : Matrix C₀ C₁ (ZMod 2)) (y : ↥(LinearMap.range M.mulVecLin)) :
    projLift M (y : C₀ → ZMod 2) = y :=
  LinearMap.congr_fun (projLift_comp M) y

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] in
theorem projToRange_mem (M : Matrix C₀ C₁ (ZMod 2)) (x : C₀ → ZMod 2) :
    projToRange M x ∈ LinearMap.range M.mulVecLin :=
  (projLift M x).2

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] in
theorem projToRange_eq_self (M : Matrix C₀ C₁ (ZMod 2)) {y : C₀ → ZMod 2}
    (hy : y ∈ LinearMap.range M.mulVecLin) : projToRange M y = y :=
  congrArg Subtype.val (projLift_apply M ⟨y, hy⟩)

noncomputable def projMat (M : Matrix C₀ C₁ (ZMod 2)) : Matrix C₀ C₀ (ZMod 2) :=
  LinearMap.toMatrix' (projToRange M)

omit [DecidableEq C₁] in
theorem projMat_mulVec (M : Matrix C₀ C₁ (ZMod 2)) (x : C₀ → ZMod 2) :
    projMat M *ᵥ x = projToRange M x :=
  LinearMap.toMatrix'_mulVec (projToRange M) x

/-- `projMat` is the identity on `im M`: `P * M = M`. -/
theorem projMat_mul (M : Matrix C₀ C₁ (ZMod 2)) : projMat M * M = M := by
  have h : ∀ y : C₁ → ZMod 2, (projMat M * M) *ᵥ y = M *ᵥ y := by
    intro y
    rw [← Matrix.mulVec_mulVec, projMat_mulVec]
    exact projToRange_eq_self M (LinearMap.mem_range.mpr ⟨y, rfl⟩)
  ext c c'
  have h1 := congrFun (h (Pi.single c' 1)) c
  simpa [Matrix.mulVec, dotProduct_single_one] using h1

omit [DecidableEq C₀] in
/-- **The component formula for `kron A 1`** (the mirror of
`kroneckerMap_one_left_mulVec_apply`, with `1` on the right). -/
theorem kron_right_one_mulVec {A : Matrix C₀ C₀ (ZMod 2)} (w : C₀ × R₁ → ZMod 2)
    (c : C₀) (t : R₁) :
    ((Matrix.kronecker A (1 : Matrix R₁ R₁ (ZMod 2))) *ᵥ w) (c, t)
      = (A *ᵥ (fun c' => w (c', t))) c := by
  simp only [Matrix.kronecker, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single t]
  · simp [Matrix.one_apply_eq]
  · intro y _ hy
    simp [Matrix.one_apply_ne (Ne.symm hy)]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-! ### The main theorem -/

omit [DecidableEq C₂] in
/-- **Decoupling "spanning" over general $R$**:
$\ker\partial_0 \le S + \mathrm{im}\,\partial_1 + T$. -/
theorem ker_koszulD0_le_sup_general (R : Matrix R₀ R₁ (ZMod 2))
    (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hComplex : koszulD0 R dC1 * koszulD1 R dC1 dC2 = 0) :
    LinearMap.ker (koszulD0 R dC1).mulVecLin
      ≤ spacelikeSub (R₀ := R₀) (R₁ := R₁) dC1
        ⊔ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin
        ⊔ timelikeSub (R₀ := R₀) (R₁ := R₁) (C₀ := C₀) (C₁ := C₁) R := by
  intro f hf
  have hzero : (koszulD0 R dC1) *ᵥ f = 0 := by
    have h := hf
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
  have hrel : (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R)
        *ᵥ (fun p : C₀ × R₁ => f (Sum.inl p))
      = (Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2)))
        *ᵥ (fun e : C₁ × R₀ => f (Sum.inr e)) := by
    funext p
    have h1 := congrFun hzero (Sum.inl p)
    rw [Pi.zero_apply, fd0_mulVec_apply_inl_add] at h1
    exact eq_of_add_eq_zero h1
  set u : C₀ × R₁ → ZMod 2 := fun p => f (Sum.inl p) with hu
  set v : C₁ × R₀ → ZMod 2 := fun e => f (Sum.inr e) with hv
  have hrel : (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) *ᵥ u
      = (Matrix.kronecker dC1 (1 : Matrix R₀ R₀ (ZMod 2))) *ᵥ v := by
    funext p
    have h1 := congrFun hzero (Sum.inl p)
    rw [Pi.zero_apply, fd0_mulVec_apply_inl_add, ← hu, ← hv] at h1
    exact eq_of_add_eq_zero h1
  set U₁ : C₀ × R₁ → ZMod 2 :=
    (Matrix.kronecker (projMat dC1) (1 : Matrix R₁ R₁ (ZMod 2))) *ᵥ u with hU₁
  -- ★ The projection commutes with (1⊗R) and is the identity on im dC1, so the projection
  -- does not change the reading of (1⊗R)
  have hcomm : (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) *ᵥ U₁
      = (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) *ᵥ u := by
    rw [hU₁, Matrix.mulVec_mulVec]
    have hkr : (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R)
          * (Matrix.kronecker (projMat dC1) (1 : Matrix R₁ R₁ (ZMod 2)))
        = (Matrix.kronecker (projMat dC1) (1 : Matrix R₀ R₀ (ZMod 2)))
          * (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) := by
      rw [kron_mul, kron_mul]
      simp
    rw [hkr, ← Matrix.mulVec_mulVec, hrel, Matrix.mulVec_mulVec, kron_mul, projMat_mul]
    simp
  -- `U₁` lies in `im(kron dC1 1)`
  have hmem : U₁ ∈ LinearMap.range
      (Matrix.kronecker dC1 (1 : Matrix R₁ R₁ (ZMod 2))).mulVecLin := by
    rw [hU₁]
    choose w hw using fun t : R₁ => projToRange_mem dC1 (fun c : C₀ => f (Sum.inl (c, t)))
    refine LinearMap.mem_range.mpr ⟨fun e : C₁ × R₁ => w e.2 e.1, ?_⟩
    rw [Matrix.mulVecLin_apply]
    funext p
    rw [kron_one_mulVec_c, kron_right_one_mulVec, projMat_mulVec]
    exact congrFun (hw p.2) p.1
  obtain ⟨g, hg⟩ := hmem
  rw [Matrix.mulVecLin_apply] at hg
  -- ★ Key: `u + U₁` is killed by `(1⊗R)`
  have hkill : (Matrix.kronecker (1 : Matrix C₀ C₀ (ZMod 2)) R) *ᵥ (u + U₁) = 0 := by
    rw [Matrix.mulVec_add, hcomm]
    funext p
    exact CharTwo.add_self_eq_zero _
  -- The three terms lie in the three subspaces respectively
  have h1mem : (koszulD1 R dC1 dC2) *ᵥ (Sum.elim g 0
      : FaultTerm2 (C₁ × R₁) (C₂ × R₀) → ZMod 2)
      ∈ LinearMap.range (koszulD1 R dC1 dC2).mulVecLin :=
    LinearMap.mem_range.mpr ⟨Sum.elim g 0, rfl⟩
  have h2mem : Sum.elim (u + U₁) (0 : C₁ × R₀ → ZMod 2)
      ∈ timelikeSub (R₀ := R₀) (R₁ := R₁) (C₀ := C₀) (C₁ := C₁) R := by
    refine mem_timelikeSub.mpr ⟨fun e => rfl, fun c => ?_⟩
    funext r
    have h := congrFun hkill (c, r)
    rw [Pi.zero_apply, kron_one_left_mulVec_c0] at h
    simpa only [Sum.elim_inl, Pi.zero_apply] using h
  have hxK : Sum.elim (0 : C₀ × R₁ → ZMod 2)
        (v + (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ g)
      ∈ LinearMap.ker (koszulD0 R dC1).mulVecLin := by
    have hx : Sum.elim (0 : C₀ × R₁ → ZMod 2)
          (v + (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ g)
        = f + (koszulD1 R dC1 dC2) *ᵥ (Sum.elim g 0
            : FaultTerm2 (C₁ × R₁) (C₂ × R₀) → ZMod 2)
          + Sum.elim (u + U₁) (0 : C₁ × R₀ → ZMod 2) := by
      funext p
      rcases p with p | e
      · simp only [Pi.add_apply, Sum.elim_inl]
        rw [fd1_mulVec_inl]
        have hgg : (fun q : C₁ × R₁ => (Sum.elim g (0 : C₂ × R₀ → ZMod 2)) (Sum.inl q)) = g := rfl
        have hup : f (Sum.inl p) = u p := (congrFun hu p).symm
        rw [hgg, hg]
        simp only [Pi.zero_apply, hup, add_zero, zero_add]
        exact (CharTwo.add_self_eq_zero (u p + U₁ p)).symm
      · simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr]
        rw [fd1_mulVec_inr]
        have hgg : (fun q : C₁ × R₁ => (Sum.elim g (0 : C₂ × R₀ → ZMod 2)) (Sum.inl q)) = g := rfl
        have hz2 : (fun q : C₂ × R₀ => (Sum.elim g (0 : C₂ × R₀ → ZMod 2)) (Sum.inr q)) = 0 := rfl
        have hvp : f (Sum.inr e) = v e := (congrFun hv e).symm
        rw [hgg, hz2, Matrix.mulVec_zero]
        simp only [Pi.zero_apply, hvp, add_zero, zero_add]
    rw [hx]
    refine Submodule.add_mem _ (Submodule.add_mem _ hf ?_) ?_
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hComplex,
        Matrix.zero_mulVec]
    · exact (timelikeSub_le_ker R dC1) h2mem
  have h3mem : Sum.elim (0 : C₀ × R₁ → ZMod 2)
        (v + (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ g)
      ∈ spacelikeSub (R₀ := R₀) (R₁ := R₁) dC1 := by
    refine mem_spacelikeSub.mpr ⟨fun p => rfl, fun r => ?_⟩
    funext c
    have hker := hxK
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    have h := congrFun hker (Sum.inl (c, r))
    have hz0 : (fun q : C₀ × R₁ => (Sum.elim (0 : C₀ × R₁ → ZMod 2)
    (v + (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ g)) (Sum.inl q)) = 0 := rfl
    have hz1 : (fun q : C₀ × R₁ => (0 : ZMod 2)) = 0 := rfl
    simp only [Pi.zero_apply, fd0_mulVec_apply_inl_add, Sum.elim_inl, Sum.elim_inr,
      hz0, hz1, Matrix.mulVec_zero, zero_add, kron_one_mulVec_c] at h
    simpa only [Sum.elim_inr, Pi.zero_apply] using h
  have hsum : (koszulD1 R dC1 dC2) *ᵥ (Sum.elim g 0
        : FaultTerm2 (C₁ × R₁) (C₂ × R₀) → ZMod 2)
      + Sum.elim (u + U₁) (0 : C₁ × R₀ → ZMod 2)
      + Sum.elim (0 : C₀ × R₁ → ZMod 2)
          (v + (Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ g) = f := by
    funext p
    rcases p with p | e
    · simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr]
      rw [fd1_mulVec_inl]
      have hgg : (fun q : C₁ × R₁ => (Sum.elim g (0 : C₂ × R₀ → ZMod 2)) (Sum.inl q)) = g := rfl
      have hup : f (Sum.inl p) = u p := (congrFun hu p).symm
      rw [hgg, hg]
      simp only [Pi.zero_apply, hup, add_zero, zero_add]
      rw [add_comm (u p) (U₁ p), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr]
      rw [fd1_mulVec_inr]
      have hgg : (fun q : C₁ × R₁ => (Sum.elim g (0 : C₂ × R₀ → ZMod 2)) (Sum.inl q)) = g := rfl
      have hz2 : (fun q : C₂ × R₀ => (Sum.elim g (0 : C₂ × R₀ → ZMod 2)) (Sum.inr q)) = 0 := rfl
      have hvp : f (Sum.inr e) = v e := (congrFun hv e).symm
      rw [hgg, hz2, Matrix.mulVec_zero]
      simp only [Pi.zero_apply, hvp, add_zero, zero_add]
      rw [add_comm (v e) (((Matrix.kronecker (1 : Matrix C₁ C₁ (ZMod 2)) R) *ᵥ g) e),
        ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [← hsum]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_right h1mem))
      (Submodule.mem_sup_right h2mem))
    (Submodule.mem_sup_left (Submodule.mem_sup_left h3mem))

end GeneralR

end QECCertificates.Homology
