/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.HypergraphSurgery

open QECCertificates

/-!
# The auxiliary-complex layer: hypergraph surgery, the 1-cosystolic distance, gauging

Section 2 ("Certifiable metrics") item 8 of the proposal requires that **homomorphic
measurement** (a surgery whose auxiliary structure is given by a hypergraph, the $O(d)$
rounds of [14]) be brought into the same reduce-solve-verify chain, and notes that *gauging
is the special case whose subcode distance is 1*. `Homology/HypergraphSurgery.lean` delivers
the **representation layer** of that item (the auxiliary hypergraph, its components, the
product identity for the Gauss laws, the timelike component), and states explicitly in its
Section 6 ("Honest boundaries") that **the four-term complex and the 1-cosystolic distance
are not reproduced**, and that `IsComponent` is only "the coordinatewise spelling of
$\ker \delta$". This module supplies that layer.

## 1. The text of [14] (the sole source of this module's definitions, transcribed)

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895.

**§1.2, p.3** (the four-term complex, components, the 1-cosystolic distance):

> In this work, we augment the above formulation by associating a 4-term chain complex
> with the hypergraph $H = (V, E)$. Specifically, let $C$ be a basis of cycles of $H$, where a
> cycle is a collections of hyperedges which include every vertex in $V$ an even number of
> times. Let $W$ be a set of $O(1)$-sized components of $H$, where a component is a collection
> of vertices which intersect every hyperedge on an even number of vertices.¹ Then
>
> $$H^\bullet = \mathbb{F}_2^W \xleftarrow{\ \delta_2\ } \mathbb{F}_2^V
>   \xleftarrow{\ \delta_1\ } \mathbb{F}_2^E \xleftarrow{\ \delta_0\ } \mathbb{F}_2^C$$
>
> is a 4-term cochain complex, where the coboundary maps $\delta_i$ are specified by the inclusion
> relations of $W, V, E, C$. Note that when $H$ is a simple connected graph (i.e., every hyper-
> edge is a regular edge), the only component is the set of all vertices $V$. Typically when
> treating cell complexes the above coboundary maps would instead be boundary maps: we
> flip this convention to suit our conventions in the main body.
>
> […] By including $W$, we can now consider the 1-cosystolic distance of $H^\bullet$, which is
>
> $$d_1^\bullet = \min\{|u| : u \in \ker(\delta_2) \setminus \mathrm{im}(\delta_1)\}.$$

(Footnote 1: **"Note here that $W$ is a set of our choice and is often not a basis of all
components of $H$."**)

**The direction of the arrows**: all three arrows of the source point **left**, that is,
$\delta_2 : \mathbb F_2^V \to \mathbb F_2^W$, $\delta_1 : \mathbb F_2^E \to \mathbb F_2^V$,
$\delta_0 : \mathbb F_2^C \to \mathbb F_2^E$. Then $\ker(\delta_2) \subseteq \mathbb F_2^V$
and $\mathrm{im}(\delta_1) \subseteq \mathbb F_2^V$ live in the same space, which is what
makes the formula for $d_1^\bullet$ hold (read the arrows the other way and the two sides
are no longer in one space). The matrix convention of this module: `surgeryD1 H :
Matrix (Fin k) (Fin m)` acts on column vectors, that is, $\delta_1 : \mathbb F_2^E \to
\mathbb F_2^V$, where `Fin k` = $V$ (vertices) and `Fin m` = $E$ (hyperedges).

**§5, p.32** (the meaning of the vertex space):

> The degree 1 of $A_\bullet$ is shifted by the mapping cone construction to be in
> $\mathrm{cone}(f)_2$, i.e. **the set of vertices in the hypergraph is the set of basis
> elements of $A_1$.**

> In the mapping cone that describes the surgery operation, the 1-cosystolic distance
> captures the metacheck distance.

**§6.2, p.35** (the sentence this module's main theorem is to land):

> **Gauging logical measurement [56] can be seen as an instance of hypergraph surgery
> where the subcode $A_\bullet$ has distance 1, and therefore requires $O(d)$ rounds of
> syndrome measurement to maintain fault-distance $d$.**

The context of the same section (the opening of p.33, and §6.1 of p.33):

> We can consider (a) block reading with a distance $d$ subcode and (b) conventional LDPC
> code surgery, which uses a distance 1 subcode, to each sit at opposite ends of an axis
> determining the time cost of logical measurements.

> The distance of $A_\bullet$ is the minimum number of check errors on the auxiliary system
> which are required to cause an undetectable logical measurement error in a single round;
> this is not the same as the single-shot distance of the entire deformed code.

**§7, p.35–37** (modular expansion and thickening; **not reproduced** here, transcribed only
for reference):

> **Definition 7.2 (Modular expansion).** *Let $\mathcal H(\mathcal V, \mathcal E)$ be a hypergraph
> with incidence matrix $G : \mathbb F_2\mathcal E \to \mathbb F_2\mathcal V$ and specified subspace
> $W \subset \mathbb F_2\mathcal V$ containing elements $\kappa_\lambda$. Let $t \in \mathbb R_+$ be
> a positive real number. The modular expansion $\mathcal M_t$ of $\mathcal H$ is the largest real
> number such that, for all $v \subseteq \mathcal V$,
> $|G^{\mathsf T}v| \geq \mathcal M_t \min(t, |\kappa_\lambda| - |v \cap \kappa_\lambda| +
> |v \cap \mathcal U \setminus \kappa_\lambda| : \kappa_\lambda \in W)$.*

> **Theorem 7.8 (Thickening).** *Let $\mathcal H(\mathcal V, \mathcal E)$ be a hypergraph with
> modular expansion $\mathcal M_t(\mathcal H)$. Let $\mathcal J_L$ be the path graph with length
> $L \geq \frac{1}{\mathcal M_t(\mathcal H)}$, i.e. $L$ vertices and $L-1$ edges. Let
> $\mathcal H_L := \mathcal H \square \mathcal J_L$ be the hypergraph of $\mathcal H$ thickened $L$
> times. Then $\mathcal H_L$ has modular expansion $\mathcal M_t(\mathcal H_L) \geq 1$ for
> $\mathcal U^\ell = \bigcup_i V_i^\ell$ at any level $\ell \in \{1, 2, \cdots, L\}$, where
> $V_i^\ell$ is the copy of $V_i$ in the $\ell$th level of the thickened hypergraph.*

(Definition 7.1 defines $W \subseteq \mathbb F_2^{\mathcal V}$ as spanned by the images of the
port function, $V_i = \mathrm{supp}(v_i)$, and $\mathcal U = \bigcup_i V_i$; Theorem 7.7 gives
$\mathcal M_d(\mathcal H) \geq 1 \Rightarrow$ the deformed code has distance $\geq d$. This
"modular expansion" route is **not** formalized in this module.)

## 2. What this module does

**§2, the four-term complex** (`IsCycleSet` / `surgeryD0` / `surgeryD1` / `surgeryD2`):
the maps $\delta_0, \delta_1, \delta_2$ of [14] §1.2 are written as GF(2) matrices, and the
**complex conditions** $\delta_1 \circ \delta_0 = 0$ and $\delta_2 \circ \delta_1 = 0$ are
machine-checked:

* `surgeryD1_mul_surgeryD0_eq_zero`: $\delta_1\delta_0 = 0$ when every cycle covers each of
  its vertices an even number of times (exactly [14]'s definition of a *cycle*);
* `surgeryD2_mul_surgeryD1_eq_zero`: $\delta_2\delta_1 = 0$ when every member of $W$ is a
  **component** (exactly [14]'s definition of a *component*);
* together the two are [14]'s "is a 4-term cochain complex" (`surgery_four_term_complex`).

**§3, the two kernels** (`isComponent_iff_mulVec_transpose` /
`isCycleSet_iff_mulVec_surgeryD1`): $\ker(\delta_1^{\mathsf T}) = \{$components$\}$ and
$\ker(\delta_1) = \{$cycles$\}$, closing the gap left by item 1 of Section 6 of
`Homology/HypergraphSurgery.lean` (which states that `IsComponent` is "the coordinatewise
spelling of $\ker \delta$" but does **not** reproduce the complex).

**§4, the component structure in the graph case** (`isComponent_eq_empty_or_univ_of_reachable`
and others): [14] §1.2 says "when $H$ is a simple connected graph …, the only component is
the set of all vertices $V$". The previous module proved only the **half** "$V$ is a
component"; this module supplies the half "**only**": on a connected graph the components
are exactly $\varnothing$ and $V$ (`graphOf_components_eq`, both directions).

**§5, the 1-cosystolic distance and the "distance 1" of gauging** (the main theorem of this
module): define $d_1^\bullet = \min\{|u| : u \in \ker(\delta_2)\setminus\mathrm{im}(\delta_1)\}$
(`cosystolicDistance`); then:

* `gauging_cosystolicDistance_eq_one`: on an **even hypergraph** (every hyperedge of even
  cardinality; a 2-regular hypergraph, i.e. a graph, is the minimal case) with a chosen
  component family $W$ that misses some vertex $v$ ($v \notin \bigcup W$), $d_1^\bullet = 1$:
  the upper bound is the single-vertex cocycle $\{v\}$, the lower bound is
  $\{v\} \notin \mathrm{im}(\delta_1)$;
* `graphOf_cosystolicDistance_eq_one`: the corollary in the **2-regular (graph) case** —
  which is exactly the auxiliary structure of gauging;
* `graphOf_not_high_cosystolic`: hence on a 2-regular auxiliary complex whose component
  family `W` misses some vertex, the hypothesis "1-cosystolic distance $\ge d$" ($d \ge 2$)
  of [14] Theorem 5.3 **cannot hold** — the machine-side counterpart of "therefore requires
  $O(d)$ rounds" in the sentence of §6.2;
* `high_cosystolic_requires_cover` (the contrapositive of the main theorem, the strongest
  statement of this section): if the weight lower bound $d \ge 2$ really holds, then either
  `W` covers every vertex or the hypergraph has an **odd-cardinality** hyperedge — that is,
  "$d_1 \ge 2$" is impossible on a 2-regular auxiliary structure.

**§6, the interface with `Codes/Gauging.lean` and `HypergraphSurgery.lean`**: the entries of
$\delta_1$ are the **auxiliary-bit block** of the Gauss-law check matrix `gaussLawMat`
(`gaussLawMat H = [I \mid \delta_1]`, `gaussLawMat_apply_inr`), in the graph case each entry
equals `gaussOp` (`surgeryD1_graphOf_eq_gaussOp`), and in the 2-regular case every column of
$\delta_1$ has exactly two nonzero entries (`graphOf_surgeryD1_col_card`) — that is, "the
auxiliary structure degenerates to the incidence matrix of a graph".

## 3. Honest boundaries (the paper cites this section)

**What is formalized**: (i) the four-term complex of [14] §1.2 and its complex conditions;
(ii) components and cycles are the kernels of $\delta_1^{\mathsf T}$ and $\delta_1$
respectively; (iii) the full two-directional statement that on a connected graph the only
components are $\varnothing$ and $V$; (iv) the definition of the $1$-cosystolic distance and
the fact that **it equals 1 in the gauging case (2-regular, even hypergraph)**, with an
explicit witness (the single-vertex cocycle) and a lower bound, together with the resulting
statement that a 2-regular auxiliary complex does not satisfy $d_1 \ge d$ ($d \ge 2$) and
its contrapositive `high_cosystolic_requires_cover`.

**What is not formalized** (the scope of this module; **no claim is made**):

1. **The half "the subcode $A_\bullet$ has distance 1".** The wording of [14] §6.2 is that
   the **subcode $A_\bullet$ of gauging has distance 1**; **this module** does not build the
   subcode layer, so "the subcode distance $=1$" is not machine-checked here. What this
   module does is its counterpart on the **auxiliary-complex** side: the $1$-cosystolic
   distance $d_1^\bullet = 1$. (The subcode layer itself is `Homology/SubcodeLayer.lean`,
   which reads "subcode" as a genuine CSS code object (X checks, Z checks, CSS compatibility,
   two distances) and machine-checks that sentence of §6.2; the chain map and the
   degree-shift are in `Homology/SubcodeChainMap.lean`. The boundary described above is the
   scope of **this module**, not the current state of the whole library.)
   [14] §6.1 describes "the distance of $A_\bullet$" as *"the minimum number of check errors
   on the auxiliary system which are required to cause an undetectable logical measurement
   error in a single round"* — this is a convention of the same order as
   $d_1^\bullet = \min\{|u| : u \in \ker \delta_2 \setminus \mathrm{im}\,\delta_1\}$
   (vertex = check, hyperedge = data bit, see the convention of Theorem 7.7 in §7), but
   **this module makes no equivalence claim that the two are equal** — that would first
   require formalizing the subcode layer.
2. **The fault-tolerance distance theorem of [14] itself** (Theorem 5.3 / 6.3 / 6.5). In
   "$d_1 = 1$, hence $O(d)$ rounds are required", the phrase "$O(d)$ rounds" is the
   **conclusion of that theorem**, whose proof uses a combined argument over the deformed
   code, the compacted code, soundness and the fault distance; this module machine-checks
   only that its **hypothesis side degenerates in the gauging case** ($d_1 = 1$ makes
   $d_1 \ge d$ impossible), together with the round arithmetic written down in [14] itself
   (`rounds_ge_of_cosystolic_one`, pure ℕ arithmetic, **not** a fault-tolerance argument).
3. **The modular expansion / thickening of §7** (Definition 7.2, Theorem 7.8): not
   formalized, and neither is $\mathcal M_t$ over $\mathbb R$ or the port function.
4. **The choice of $W$.** [14] says $W$ is "a set of $O(1)$-sized components" (the footnote
   adds "a set of our choice and is often not a basis of all components"). This module
   treats $W$ as **an arbitrary family of components**, and the extra hypothesis the main
   theorem needs is "some vertex misses $\bigcup W$" — on a connected graph the only
   $O(1)$-sized component is $\varnothing$, so this hypothesis holds automatically in the
   gauging setting of [14] (`gauging_cosystolicDistance_eq_one_empty`).

**Trusted base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axiom; the `#print axioms` output for the load-bearing theorems is in the audit region
at the end of the root module `QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open scoped BigOperators

open _root_.Matrix

variable {k m : ℕ}

/-! ## 1. Indicator vectors, cycles and components -/

/-- The indicator vector of a subset (the vector spelling of "this set" over GF(2)). -/
def indVec {n : ℕ} (S : Finset (Fin n)) : Vec n := fun i => if i ∈ S then 1 else 0

/-- **A cycle** ([14] §1.2): a family of hyperedges such that every vertex is covered by an
**even** number of them — the source's "a collection of hyperedges which include every
vertex in V an even number of times". -/
def IsCycleSet (H : AuxHypergraph k m) (c : Finset (Fin m)) : Prop :=
  ∀ v : Fin k, Even ((c.filter (fun e => v ∈ H.edge e)).card)

/-- A natural number is zero in `ZMod 2` iff it is even (the bridge carrying parity into
GF(2)). -/
theorem even_iff_natCast_zmod_two_eq_zero (n : ℕ) : Even n ↔ ((n : ZMod 2) = 0) := by
  rw [even_iff_two_dvd, CharP.cast_eq_zero_iff (ZMod 2) 2 n]

/-! ## 2. The four-term complex ([14] §1.2) -/

/-- $\delta_0 : \mathbb F_2^C \to \mathbb F_2^E$ — sends a cycle to the set of hyperedges it
contains (what [14] calls "specified by the inclusion relations of $W, V, E, C$"). -/
def surgeryD0 {k m : ℕ} {κ : Type*} (_H : AuxHypergraph k m) (C : κ → Finset (Fin m)) :
    Matrix (Fin m) κ (ZMod 2) :=
  fun e c => if e ∈ C c then 1 else 0

/-- $\delta_1 : \mathbb F_2^E \to \mathbb F_2^V$ — sends a hyperedge to its vertex set, i.e.
$G$ (the transpose of the incidence matrix $G : \mathbb F_2\mathcal E \to \mathbb F_2\mathcal V$
of [14] §7). -/
def surgeryD1 (H : AuxHypergraph k m) : Matrix (Fin k) (Fin m) (ZMod 2) :=
  fun v e => if v ∈ H.edge e then 1 else 0

/-- $\delta_2 : \mathbb F_2^V \to \mathbb F_2^W$ — sends a vertex set to its coordinates on
the chosen component family `W`. -/
def surgeryD2 {k : ℕ} {ι : Type*} (W : ι → Finset (Fin k)) : Matrix ι (Fin k) (ZMod 2) :=
  fun w v => if v ∈ W w then 1 else 0

/-- **$\delta_1 \circ \delta_0 = 0$**: the composite vanishes when every member of `C` is a
**cycle** — that is, a cycle covers every vertex an even number of times. -/
theorem surgeryD1_mul_surgeryD0_eq_zero {k m : ℕ} {κ : Type*} (H : AuxHypergraph k m)
    (C : κ → Finset (Fin m)) (hC : ∀ c, IsCycleSet H (C c)) :
    surgeryD1 H * surgeryD0 H C = 0 := by
  ext v c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  have hprod : ∀ e : Fin m, surgeryD1 H v e * surgeryD0 H C e c
      = (if v ∈ H.edge e ∧ e ∈ C c then (1 : ZMod 2) else 0) := by
    intro e
    have h1 : surgeryD1 H v e = (if v ∈ H.edge e then (1 : ZMod 2) else 0) := rfl
    have h2 : surgeryD0 H C e c = (if e ∈ C c then (1 : ZMod 2) else 0) := rfl
    rw [h1, h2]
    by_cases hv : v ∈ H.edge e <;> by_cases hc : e ∈ C c <;> simp [hv, hc]
  rw [Finset.sum_congr rfl fun e _ => hprod e, Finset.sum_boole]
  have hset : {e ∈ (Finset.univ : Finset (Fin m)) | v ∈ H.edge e ∧ e ∈ C c}
      = (C c).filter (fun e => v ∈ H.edge e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hset]
  obtain ⟨t, ht⟩ := hC c v
  rw [ht, Nat.cast_add, CharTwo.add_self_eq_zero (t : ZMod 2)]

/-- **$\delta_2 \circ \delta_1 = 0$**: the composite vanishes when every member of $W$ is a
**component** — that is, every hyperedge meets every component in an even number of
vertices. -/
theorem surgeryD2_mul_surgeryD1_eq_zero {k m : ℕ} {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (hW : ∀ w, IsComponent H (W w)) :
    surgeryD2 W * surgeryD1 H = 0 := by
  ext w e
  rw [Matrix.mul_apply, Matrix.zero_apply]
  have hprod : ∀ v : Fin k, surgeryD2 W w v * surgeryD1 H v e
      = (if v ∈ W w ∧ v ∈ H.edge e then (1 : ZMod 2) else 0) := by
    intro v
    have h1 : surgeryD2 W w v = (if v ∈ W w then (1 : ZMod 2) else 0) := rfl
    have h2 : surgeryD1 H v e = (if v ∈ H.edge e then (1 : ZMod 2) else 0) := rfl
    rw [h1, h2]
    by_cases hw : v ∈ W w <;> by_cases he : v ∈ H.edge e <;> simp [hw, he]
  rw [Finset.sum_congr rfl fun v _ => hprod v, Finset.sum_boole]
  have hset : {v ∈ (Finset.univ : Finset (Fin k)) | v ∈ W w ∧ v ∈ H.edge e}
      = W w ∩ H.edge e := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  rw [hset]
  obtain ⟨t, ht⟩ := hW w e
  rw [ht, Nat.cast_add, CharTwo.add_self_eq_zero (t : ZMod 2)]

/-- **[14] §1.2's "is a 4-term cochain complex"**:
$\mathbb F_2^W \xleftarrow{\delta_2} \mathbb F_2^V \xleftarrow{\delta_1} \mathbb F_2^E
\xleftarrow{\delta_0} \mathbb F_2^C$ really is a (co)chain complex — that the members of $C$
are cycles and those of $W$ are components implies both composites vanish. -/
theorem surgery_four_term_complex {k m : ℕ} {κ ι : Type*} (H : AuxHypergraph k m)
    (C : κ → Finset (Fin m)) (W : ι → Finset (Fin k))
    (hC : ∀ c, IsCycleSet H (C c)) (hW : ∀ w, IsComponent H (W w)) :
    surgeryD1 H * surgeryD0 H C = 0 ∧ surgeryD2 W * surgeryD1 H = 0 :=
  ⟨surgeryD1_mul_surgeryD0_eq_zero H C hC, surgeryD2_mul_surgeryD1_eq_zero H W hW⟩

/-! ## 3. The two kernels: components = ker δ₁ᵀ, cycles = ker δ₁ -/

/-- **The component of (δ₁ᵀ ·ᵥ S) at the hyperedge `e`** is the cardinality of the
intersection of `S` with `e` (mod 2). -/
theorem transpose_surgeryD1_mulVec_indVec_apply (H : AuxHypergraph k m)
    (S : Finset (Fin k)) (e : Fin m) :
    ((surgeryD1 H).transpose *ᵥ indVec S) e = (((S ∩ H.edge e).card : ℕ) : ZMod 2) := by
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply, Matrix.transpose_apply]
  have hprod : ∀ v : Fin k, surgeryD1 H v e * indVec S v
      = (if v ∈ H.edge e ∧ v ∈ S then (1 : ZMod 2) else 0) := by
    intro v
    have h1 : surgeryD1 H v e = (if v ∈ H.edge e then (1 : ZMod 2) else 0) := rfl
    have h2 : indVec S v = (if v ∈ S then (1 : ZMod 2) else 0) := rfl
    rw [h1, h2]
    by_cases hv : v ∈ H.edge e <;> by_cases hs : v ∈ S <;> simp [hv, hs]
  rw [Finset.sum_congr rfl fun v _ => hprod v, Finset.sum_boole]
  have hset : {v ∈ (Finset.univ : Finset (Fin k)) | v ∈ H.edge e ∧ v ∈ S}
      = H.edge e ∩ S := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  rw [hset, Finset.inter_comm]

/-- **Components are `ker δ₁ᵀ`**: the definition of a *component* in [14] §1.2 ("a collection
of vertices which intersect every hyperedge on an even number of vertices") is exactly
$\delta_1^{\mathsf T} S = 0$ — the gap left by item 1 of Section 6 of
`HypergraphSurgery.lean`. -/
theorem isComponent_iff_mulVec_transpose (H : AuxHypergraph k m) (S : Finset (Fin k)) :
    IsComponent H S ↔ (surgeryD1 H).transpose *ᵥ indVec S = 0 := by
  have hzero : ((surgeryD1 H).transpose *ᵥ indVec S = 0)
      ↔ ∀ e : Fin m, (((S ∩ H.edge e).card : ℕ) : ZMod 2) = 0 := by
    constructor
    · intro h e
      rw [← transpose_surgeryD1_mulVec_indVec_apply H S e, h]
      rfl
    · intro h
      funext e
      rw [transpose_surgeryD1_mulVec_indVec_apply H S e, h e]
      rfl
  rw [hzero]
  exact ⟨fun h e => (even_iff_natCast_zmod_two_eq_zero _).mp (h e),
    fun h e => (even_iff_natCast_zmod_two_eq_zero _).mpr (h e)⟩

/-- **The component of (δ₁ ·ᵥ c) at the vertex `v`** is the number of hyperedges of `c`
covering `v` (mod 2). -/
theorem surgeryD1_mulVec_indVec_apply (H : AuxHypergraph k m) (c : Finset (Fin m)) (v : Fin k) :
    (surgeryD1 H *ᵥ indVec c) v
      = (((c.filter (fun e => v ∈ H.edge e)).card : ℕ) : ZMod 2) := by
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply]
  have hprod : ∀ e : Fin m, surgeryD1 H v e * indVec c e
      = (if v ∈ H.edge e ∧ e ∈ c then (1 : ZMod 2) else 0) := by
    intro e
    have h1 : surgeryD1 H v e = (if v ∈ H.edge e then (1 : ZMod 2) else 0) := rfl
    have h2 : indVec c e = (if e ∈ c then (1 : ZMod 2) else 0) := rfl
    rw [h1, h2]
    by_cases hv : v ∈ H.edge e <;> by_cases hc : e ∈ c <;> simp [hv, hc]
  rw [Finset.sum_congr rfl fun e _ => hprod e, Finset.sum_boole]
  have hset : {e ∈ (Finset.univ : Finset (Fin m)) | v ∈ H.edge e ∧ e ∈ c}
      = c.filter (fun e => v ∈ H.edge e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hset]

/-- **Cycles are `ker δ₁`**: a *cycle* in [14] §1.2 ("a collection of hyperedges which
include every vertex an even number of times") is exactly $\delta_1 c = 0$. -/
theorem isCycleSet_iff_mulVec_surgeryD1 (H : AuxHypergraph k m) (c : Finset (Fin m)) :
    IsCycleSet H c ↔ surgeryD1 H *ᵥ indVec c = 0 := by
  have hzero : (surgeryD1 H *ᵥ indVec c = 0)
      ↔ ∀ v : Fin k, (((c.filter (fun e => v ∈ H.edge e)).card : ℕ) : ZMod 2) = 0 := by
    constructor
    · intro h v
      rw [← surgeryD1_mulVec_indVec_apply H c v, h]
      rfl
    · intro h
      funext v
      rw [surgeryD1_mulVec_indVec_apply H c v, h v]
      rfl
  rw [hzero]
  exact ⟨fun h v => (even_iff_natCast_zmod_two_eq_zero _).mp (h v),
    fun h v => (even_iff_natCast_zmod_two_eq_zero _).mpr (h v)⟩

/-! ## 4. The component structure in the graph case ([14] §1.2's "the only component") -/

/-- The cardinality of the two-element intersection `S ∩ {a, b}` is the sum of the two
indicator values (`a ≠ b`). -/
theorem card_inter_pair {α : Type*} [DecidableEq α] (S : Finset α) {a b : α} (hab : a ≠ b) :
    (S ∩ ({a, b} : Finset α)).card
      = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · have hset : S ∩ ({a, b} : Finset α) = {a, b} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h.elim (fun hx => hx ▸ ha) (fun hx => hx ▸ hb), h⟩
    rw [hset, Finset.card_pair hab, ite_eq_left ha, ite_eq_left hb]
  · have hset : S ∩ ({a, b} : Finset α) = {a} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxS, hxa | hxb⟩
        · exact hxa
        · exact absurd (hxb ▸ hxS) hb
      · intro hx
        exact ⟨hx ▸ ha, Or.inl hx⟩
    rw [hset, Finset.card_singleton, ite_eq_left ha, ite_eq_right hb]
  · have hset : S ∩ ({a, b} : Finset α) = {b} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxS, hxa | hxb⟩
        · exact absurd (hxa ▸ hxS) ha
        · exact hxb
      · intro hx
        exact ⟨hx ▸ hb, Or.inr hx⟩
    rw [hset, Finset.card_singleton, ite_eq_right ha, ite_eq_left hb]
  · have hset : S ∩ ({a, b} : Finset α) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with ⟨hxS, hxa | hxb⟩
      · exact ha (hxa ▸ hxS)
      · exact hb (hxb ▸ hxS)
    rw [hset, Finset.card_empty, ite_eq_right ha, ite_eq_right hb]

/-- The parity of an indicator value is the negation of the proposition:
`Even (if p then 1 else 0) ↔ ¬p`. -/
theorem even_indicator_iff {α : Type*} [DecidableEq α] (S : Finset α) (a : α) :
    Even (if a ∈ S then 1 else 0) ↔ ¬ (a ∈ S) := by
  by_cases h : a ∈ S <;> simp [h]

/-- **Components of a graph = "closed" sets**: on a 2-regular hypergraph, "`S` meets every
hyperedge in an even number of vertices" is equivalent to no hyperedge "crossing" `S` (both
endpoints of each hyperedge lie in `S` or neither does). -/
theorem isComponent_graphOf_iff_closed {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (S : Finset (Fin k)) :
    IsComponent (graphOf ends) S ↔ ∀ e : Fin m, ((ends e).1 ∈ S ↔ (ends e).2 ∈ S) := by
  constructor
  · intro h e
    have he := h e
    rw [graphOf_edge, card_inter_pair S (hloop e), Nat.even_add,
      even_indicator_iff S (ends e).1, even_indicator_iff S (ends e).2] at he
    tauto
  · intro h e
    rw [graphOf_edge, card_inter_pair S (hloop e), Nat.even_add,
      even_indicator_iff S (ends e).1, even_indicator_iff S (ends e).2]
    refine ⟨fun h1 h2 => h1 ((h e).mpr h2), fun h2 h1 => h2 ((h e).mp h1)⟩

/-- **Adjacency** of the graph given by the endpoint function: `a` and `b` are joined by
some hyperedge. -/
def Adj {k m : ℕ} (ends : Fin m → Fin k × Fin k) (a b : Fin k) : Prop :=
  ∃ e : Fin m, ((ends e).1 = a ∧ (ends e).2 = b) ∨ ((ends e).1 = b ∧ (ends e).2 = a)

/-- **The reachability closure**: walking along hyperedges. -/
inductive Reachable {k m : ℕ} (ends : Fin m → Fin k × Fin k) : Fin k → Fin k → Prop where
  /-- Reachable in zero steps. -/
  | refl (a : Fin k) : Reachable ends a a
  /-- Cross one hyperedge to a neighbour. -/
  | step {a b c : Fin k} : Reachable ends a b → Adj ends b c → Reachable ends a c

/-- **Closed sets propagate along reachability**: if `S` is a component and `a ∈ S`, then
every vertex reachable from `a` lies in `S`. -/
theorem reachable_mem_of_isComponent {k m : ℕ} {ends : Fin m → Fin k × Fin k}
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) {S : Finset (Fin k)}
    (hS : IsComponent (graphOf ends) S) {a b : Fin k} (ha : a ∈ S)
    (hab : Reachable ends a b) : b ∈ S := by
  induction hab with
  | refl => exact ha
  | step hab hbc ih =>
    obtain ⟨e, h | h⟩ := hbc
    · obtain ⟨h1, h2⟩ := h
      have he := (isComponent_graphOf_iff_closed ends hloop S).mp hS e
      rw [h1, h2] at he
      exact he.mp ih
    · obtain ⟨h1, h2⟩ := h
      have he := (isComponent_graphOf_iff_closed ends hloop S).mp hS e
      rw [h1, h2] at he
      exact he.mpr ih

/-- **[14] §1.2's "the only component" (the "only" half)**: on a connected graph the only
components are $\varnothing$ and the full vertex set $V$. The previous module proved only
that "$V$ is a component"; this theorem supplies the "only". -/
theorem isComponent_eq_empty_or_univ_of_reachable {k m : ℕ} {ends : Fin m → Fin k × Fin k}
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hconn : ∀ a b : Fin k, Reachable ends a b)
    {S : Finset (Fin k)} (hS : IsComponent (graphOf ends) S) :
    S = ∅ ∨ S = Finset.univ := by
  by_cases hne : S.Nonempty
  · right
    obtain ⟨a, ha⟩ := hne
    exact Finset.eq_univ_of_forall fun b =>
      reachable_mem_of_isComponent hloop hS ha (hconn a b)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

/-- **The components of a connected graph are exactly $\varnothing$ and $V$** (both
directions): the full machine form of the sentence "when $H$ is a simple connected graph …,
the only component is the set of all vertices $V$" of [14] §1.2. -/
theorem graphOf_components_eq {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (hconn : ∀ a b : Fin k, Reachable ends a b)
    (S : Finset (Fin k)) :
    IsComponent (graphOf ends) S ↔ S = ∅ ∨ S = Finset.univ := by
  constructor
  · exact isComponent_eq_empty_or_univ_of_reachable hloop hconn
  · rintro (rfl | rfl)
    · intro e
      rw [Finset.empty_inter, Finset.card_empty]
      exact ⟨0, rfl⟩
    · exact component_univ_of_graph (graphOf_card_two ends hloop)

/-! ## 5. The 1-cosystolic distance ([14] §1.2) -/

/-- **A $1$-cosystolic cocycle**: a member of $\ker(\delta_2) \setminus \mathrm{im}(\delta_1)$
— a cocycle sent to zero by $\delta_2$ that is **not** a physical fault (an image of
$\delta_1$). -/
def IsCosystolic {k m : ℕ} {ι : Type*} (H : AuxHypergraph k m) (W : ι → Finset (Fin k))
    (u : Vec k) : Prop :=
  surgeryD2 W *ᵥ u = 0 ∧ ¬ ∃ f : Vec m, surgeryD1 H *ᵥ f = u

/-- **The $1$-cosystolic distance** ([14] §1.2): $d_1^\bullet = \min\{|u| : u \in
\ker(\delta_2) \setminus \mathrm{im}(\delta_1)\}$. -/
noncomputable def cosystolicDistance {k m : ℕ} {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) : ℕ :=
  sInf {w : ℕ | ∃ u : Vec k, IsCosystolic H W u ∧ hammingNorm u = w}

/-- A vector of weight zero is the zero vector. -/
theorem eq_zero_of_hammingNorm_eq_zero {n : ℕ} {u : Vec n} (h : hammingNorm u = 0) : u = 0 := by
  funext i
  by_contra hi
  have hmem : i ∈ Finset.univ.filter (fun j : Fin n => u j ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have h0 : (Finset.univ.filter (fun j : Fin n => u j ≠ 0)) = ∅ :=
    Finset.card_eq_zero.mp (by
      rw [← show hammingNorm u
          = (Finset.univ.filter (fun j : Fin n => u j ≠ 0)).card from rfl]
      exact h)
  rw [h0] at hmem
  exact absurd hmem (Finset.notMem_empty i)

/-- A nonzero vector has weight at least 1. -/
theorem one_le_hammingNorm_of_ne_zero {n : ℕ} {u : Vec n} (h : u ≠ 0) :
    1 ≤ hammingNorm u := by
  by_contra hlt
  exact h (eq_zero_of_hammingNorm_eq_zero (by omega))

/-- `hammingNorm` is just the sum of the coordinates in GF(2) (the parity of the weight
equals the parity of the coordinate sum). -/
theorem sum_eq_natCast_hammingNorm (u : Vec k) :
    (∑ i : Fin k, u i) = (((hammingNorm u : ℕ)) : ZMod 2) := by
  have hterm : ∀ i : Fin k, u i = (if u i ≠ 0 then (1 : ZMod 2) else 0) := by
    intro i
    by_cases hi : u i = 0
    · rw [ite_eq_right (by simpa using hi), hi]
    · rw [ite_eq_left hi, eq_one_of_ne_zero hi]
  have hbool : (∑ i : Fin k, (if u i ≠ 0 then (1 : ZMod 2) else 0))
      = (((Finset.univ.filter (fun i : Fin k => u i ≠ 0)).card : ℕ) : ZMod 2) :=
    Finset.sum_boole (fun i : Fin k => u i ≠ 0) Finset.univ
  have hnorm : hammingNorm u = (Finset.univ.filter (fun i : Fin k => u i ≠ 0)).card := rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i, hbool, hnorm]

/-- The weight is even iff the coordinate sum is zero (GF(2)). -/
theorem even_hammingNorm_iff_sum_eq_zero (u : Vec k) :
    Even (hammingNorm u) ↔ ∑ i : Fin k, u i = 0 := by
  have hcast : (((hammingNorm u : ℕ)) : ZMod 2) = ∑ i : Fin k, u i :=
    (sum_eq_natCast_hammingNorm u).symm
  rw [← hcast]
  exact (even_iff_natCast_zmod_two_eq_zero (hammingNorm u))

/-- **In the image of $\delta_1$ of an even hypergraph the weight is always even** — when
every hyperedge has even cardinality, every physical fault's syndrome (an image of
$\delta_1$) has an even number of nonzero coordinates. -/
theorem even_hammingNorm_of_mulVec_surgeryD1 (H : AuxHypergraph k m) (heven : IsEvenHyper H)
    (f : Vec m) : Even (hammingNorm (surgeryD1 H *ᵥ f)) := by
  rw [even_hammingNorm_iff_sum_eq_zero]
  have hpt : ∀ v : Fin k, (surgeryD1 H *ᵥ f) v = ∑ e : Fin m, surgeryD1 H v e * f e := by
    intro v
    rw [Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row_apply]
  rw [Finset.sum_congr rfl fun v _ => hpt v, Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hstep : (∑ v : Fin k, surgeryD1 H v e * f e)
      = (∑ v : Fin k, surgeryD1 H v e) * f e :=
    (Finset.sum_mul Finset.univ (fun v : Fin k => surgeryD1 H v e) (f e)).symm
  rw [hstep]
  have hcol : (∑ v : Fin k, surgeryD1 H v e) = (((H.edge e).card : ℕ) : ZMod 2) := by
    have hterm : ∀ v : Fin k, surgeryD1 H v e = (if v ∈ H.edge e then (1 : ZMod 2) else 0) :=
      fun v => rfl
    have hfilter : {v ∈ (Finset.univ : Finset (Fin k)) | v ∈ H.edge e} = H.edge e := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_boole, hfilter]
  rw [hcol]
  obtain ⟨t, ht⟩ := heven e
  rw [ht, Nat.cast_add, CharTwo.add_self_eq_zero (t : ZMod 2), zero_mul]

/-- The indicator vector of a singleton has weight 1. -/
theorem hammingNorm_indVec_singleton (v : Fin k) :
    hammingNorm (indVec ({v} : Finset (Fin k))) = 1 := by
  have hset : (Finset.univ.filter (fun i : Fin k => indVec ({v} : Finset (Fin k)) i ≠ 0))
      = {v} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hi⟩
      by_contra hne
      rw [indVec, ite_eq_right (by simpa [Finset.mem_singleton] using hne)] at hi
      exact hi rfl
    · intro hi
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [indVec, ite_eq_left (by simpa using hi)]
      exact one_ne_zero
  rw [show hammingNorm (indVec ({v} : Finset (Fin k)))
      = (Finset.univ.filter (fun i : Fin k => indVec ({v} : Finset (Fin k)) i ≠ 0)).card
      from rfl,
    hset, Finset.card_singleton]

/-- $\delta_2$ acting on a single-vertex vector: the value at coordinate `w` is `[v ∈ w]`. -/
theorem surgeryD2_mulVec_indVec_singleton {k : ℕ} {ι : Type*} (W : ι → Finset (Fin k))
    (v : Fin k) (w : ι) :
    (surgeryD2 W *ᵥ indVec ({v} : Finset (Fin k))) w
      = (if v ∈ W w then (1 : ZMod 2) else 0) := by
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply]
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun b : Fin k => surgeryD2 W w b * indVec ({v} : Finset (Fin k)) b) v
    (fun b _ hb => by
      rw [indVec, ite_eq_right (by simpa [Finset.mem_singleton] using hb), mul_zero])
    (fun hnot => absurd (Finset.mem_univ v) hnot)
  rw [hsingle]
  have hdv : surgeryD2 W w v = (if v ∈ W w then (1 : ZMod 2) else 0) := rfl
  have hv_self : indVec ({v} : Finset (Fin k)) v = 1 := by
    rw [indVec, ite_eq_left (Finset.mem_singleton_self v)]
  rw [hdv, hv_self, mul_one]

/-- **A single-vertex vector is never in the image of $\delta_1$** (even hypergraph) — this
is exactly where $d_1^\bullet \ge 1$ comes from. -/
theorem not_mem_im_surgeryD1_indVec_singleton {k m : ℕ} (H : AuxHypergraph k m)
    (heven : IsEvenHyper H) (v : Fin k) :
    ¬ ∃ f : Vec m, surgeryD1 H *ᵥ f = indVec ({v} : Finset (Fin k)) := by
  rintro ⟨f, hf⟩
  have hev := even_hammingNorm_of_mulVec_surgeryD1 H heven f
  rw [hf, hammingNorm_indVec_singleton] at hev
  exact (Nat.not_even_iff_odd.mpr ⟨0, by norm_num⟩) hev

/-- **A single-vertex vector is a $1$-cosystolic cocycle**: even hypergraph, plus every
component missing that vertex. -/
theorem isCosystolic_indVec_singleton {k m : ℕ} {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (heven : IsEvenHyper H) {v : Fin k} (hv : ∀ w : ι, v ∉ W w) :
    IsCosystolic H W (indVec ({v} : Finset (Fin k))) := by
  constructor
  · funext w
    rw [surgeryD2_mulVec_indVec_singleton W v w]
    exact ite_eq_right (hv w)
  · exact not_mem_im_surgeryD1_indVec_singleton H heven v

/-- **A $1$-cosystolic cocycle is necessarily nonzero** (the zero vector is in the image of
$\delta_1$). -/
theorem isCosystolic_ne_zero {k m : ℕ} {ι : Type*} {H : AuxHypergraph k m}
    {W : ι → Finset (Fin k)} {u : Vec k} (h : IsCosystolic H W u) : u ≠ 0 := by
  intro h0
  refine h.2 ⟨0, ?_⟩
  rw [h0, Matrix.mulVec_zero]

/-- **Main theorem: the $1$-cosystolic distance of a gauging-type auxiliary structure is
1.**

On an even hypergraph (every hyperedge of even cardinality; a **2-regular hypergraph, i.e. a
graph, is the minimal case**, the auxiliary structure of gauging), as soon as the chosen
component family `W` misses some vertex `v`, the $1$-cosystolic distance is exactly `1`: the
upper bound is the single-vertex cocycle `{v}`, the lower bound is
"$\{v\} \notin \mathrm{im}(\delta_1)$". -/
theorem gauging_cosystolicDistance_eq_one {k m : ℕ} {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (heven : IsEvenHyper H) (v : Fin k) (hv : ∀ w : ι, v ∉ W w) :
    cosystolicDistance H W = 1 := by
  have hmem : IsCosystolic H W (indVec ({v} : Finset (Fin k))) :=
    isCosystolic_indVec_singleton H W heven hv
  have hw : hammingNorm (indVec ({v} : Finset (Fin k))) = 1 := hammingNorm_indVec_singleton v
  have hset : (1 : ℕ) ∈ {w : ℕ | ∃ u : Vec k, IsCosystolic H W u ∧ hammingNorm u = w} :=
    ⟨indVec ({v} : Finset (Fin k)), hmem, hw⟩
  refine le_antisymm (csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hset) ?_
  refine le_csInf ⟨1, hset⟩ ?_
  rintro b ⟨u, hu, rfl⟩
  exact one_le_hammingNorm_of_ne_zero (isCosystolic_ne_zero hu)

/-- **The 2-regular (graph) case**: the auxiliary structure of gauging is a graph (the case
the sentence of [14] §6.2 corresponds to), so the $1$-cosystolic distance is 1. -/
theorem graphOf_cosystolicDistance_eq_one {k m : ℕ} {ι : Type*}
    (ends : Fin m → Fin k × Fin k) (hloop : ∀ e, (ends e).1 ≠ (ends e).2)
    (W : ι → Finset (Fin k)) (v : Fin k) (hv : ∀ w : ι, v ∉ W w) :
    cosystolicDistance (graphOf ends) W = 1 :=
  gauging_cosystolicDistance_eq_one (graphOf ends) W (graphOf_isEven ends hloop) v hv

/-- The degenerate case where `W` is the empty family (the footnote of [14]: $W$ is "a set
of our choice", and on a connected graph the only $O(1)$-sized component is $\varnothing$) —
here the extra hypothesis of the main theorem holds automatically and the $1$-cosystolic
distance is still 1. -/
theorem gauging_cosystolicDistance_eq_one_empty {k m : ℕ} (H : AuxHypergraph k m)
    (heven : IsEvenHyper H) (v : Fin k) :
    cosystolicDistance H (fun w : Empty => w.elim) = 1 :=
  gauging_cosystolicDistance_eq_one H _ heven v (fun w => w.elim)

/-- **A 2-regular auxiliary complex whose component family misses some vertex does not
satisfy the distance hypothesis of [14] Theorem 5.3** ($d \ge 2$): the graph has a weight-1
$1$-cosystolic cocycle, so "1-cosystolic distance $\ge d$" cannot hold — this is the
machine counterpart, on the hypothesis side, of "therefore requires $O(d)$ rounds" in
[14] §6.2. -/
theorem graphOf_not_high_cosystolic {k m : ℕ} {ι : Type*} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (W : ι → Finset (Fin k)) (v : Fin k)
    (hv : ∀ w : ι, v ∉ W w) {d : ℕ} (hd : 2 ≤ d) :
    ¬ (∀ u : Vec k, IsCosystolic (graphOf ends) W u → d ≤ hammingNorm u) := by
  intro h
  have hmem := isCosystolic_indVec_singleton (graphOf ends) W (graphOf_isEven ends hloop) hv
  have hle := h _ hmem
  rw [hammingNorm_indVec_singleton] at hle
  omega

/-- **The price of a high cosystolic distance** (the contrapositive of the main theorem):
if some cocycle weight lower bound `d ≥ 2` holds on an even hypergraph, then the chosen
component family `W` must **cover every vertex** — otherwise
`gauging_cosystolicDistance_eq_one` immediately gives a counterexample of weight 1. For the
auxiliary structure of gauging (a graph), "cover every vertex" can only be achieved by taking
`W ∋ V`, whereas [14] §1.2 requires `W` to consist of $O(1)$-sized components. This is the
strongest reading of the sentence "the subcode $A_\bullet$ has distance 1, and therefore
requires $O(d)$ rounds" of §6.2 on the **auxiliary-complex** side: the $1$-cosystolic
distance of a graph can only be 1. -/
theorem high_cosystolic_requires_cover {k m : ℕ} {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) {d : ℕ} (hd : 2 ≤ d)
    (h : ∀ u : Vec k, IsCosystolic H W u → d ≤ hammingNorm u) :
    (∀ v : Fin k, ∃ w : ι, v ∈ W w) ∨ ∃ e : Fin m, Odd (H.edge e).card := by
  by_contra hc
  push Not at hc
  obtain ⟨hcover, hodd⟩ := hc
  obtain ⟨v, hv⟩ := hcover
  have heven : IsEvenHyper H := fun e => Nat.not_odd_iff_even.mp (hodd e)
  have hmem := isCosystolic_indVec_singleton H W heven hv
  have hle := h _ hmem
  rw [hammingNorm_indVec_singleton] at hle
  omega

/-- The **round arithmetic** of [14] Theorem 6.5: the condition "1-cosystolic distance
$d_i \ge \alpha_i^{-1}d$" is written $\alpha_i d_i \ge d$; taking $d_i = 1$ yields
$\alpha_i \ge d$, which is the "therefore requires $O(d)$ rounds" of the sentence in §6.2.

**Note**: this is the pure ℕ arithmetic in the statement of [14], **not** the
fault-tolerance argument itself (this module formalizes no fault-distance theorem; see
Section 3 of the module documentation). -/
theorem rounds_ge_of_cosystolic_one {d α : ℕ} (h : d ≤ α * 1) : d ≤ α := by
  simpa using h

/-! ## 6. The interface with `Codes/Gauging.lean` and `HypergraphSurgery.lean` -/

/-- **The representation-layer shadow of [14] §5**: "the set of vertices in the hypergraph is
the set of basis elements of $A_1$" — the vertex space `Fin k` of the complex is exactly the
index space of the Gauss laws `starOp H v`, and the entries of $\delta_1$ are precisely the
**auxiliary-bit block** of the Gauss-law check matrix: `gaussLawMat H = [I | δ₁]`. -/
theorem gaussLawMat_apply_inr (H : AuxHypergraph k m) (v : Fin k) (e : Fin m) :
    gaussLawMat H v (Sum.inr e) = surgeryD1 H v e := by
  have h : gaussLawMat H v (Sum.inr e) = starOp H v (Sum.inr e) := rfl
  rw [h, starOp_apply_inr]
  rfl

/-- The vertex-bit block of the same partition is the identity matrix. -/
theorem gaussLawMat_apply_inl (H : AuxHypergraph k m) (v w : Fin k) :
    gaussLawMat H v (Sum.inl w) = (if w = v then 1 else 0) :=
  starOp_apply_inl H v w

/-- The rows of $\delta_1^{\mathsf T}$ are the components of the Gauss laws on the auxiliary
bits. -/
theorem transpose_surgeryD1_apply_eq_starOp (H : AuxHypergraph k m) (e : Fin m) (v : Fin k) :
    (surgeryD1 H).transpose e v = starOp H v (Sum.inr e) := by
  rw [Matrix.transpose_apply, starOp_apply_inr]
  rfl

/-- The graph case: $\delta_1$ equals the existing `gaussOp` entry by entry (a bridge between
two independent definitions). -/
theorem surgeryD1_graphOf_eq_gaussOp {k m : ℕ} (ends : Fin m → Fin k × Fin k) (v : Fin k)
    (e : Fin m) : surgeryD1 (graphOf ends) v e = gaussOp ends v (Sum.inr e) := by
  have h := congrFun (starOp_graphOf ends v) (Sum.inr e)
  rwa [starOp_apply_inr] at h

/-- **In the 2-regular case every column of $\delta_1$ has exactly two nonzero entries** —
the check matrix of the auxiliary structure is the incidence matrix of a graph (the machine
criterion for "the auxiliary structure degenerates to a graph", the same fact as
`graphOf_ancCol_card`). -/
theorem graphOf_surgeryD1_col_card {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (e : Fin m) :
    (Finset.univ.filter (fun v : Fin k => surgeryD1 (graphOf ends) v e = 1)).card = 2 := by
  have hset : (Finset.univ.filter (fun v : Fin k => surgeryD1 (graphOf ends) v e = 1))
      = (Finset.univ.filter
          (fun v : Fin k => gaussLawMat (graphOf ends) v (Sum.inr e) = 1)) := by
    ext v
    simp only [Finset.mem_filter, gaussLawMat_apply_inr]
  rw [hset]
  exact graphOf_ancCol_card ends hloop e

end QECCertificates.Homology
