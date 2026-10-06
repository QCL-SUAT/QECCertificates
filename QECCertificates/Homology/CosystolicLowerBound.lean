/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.Duality
import QECCertificates.Homology.AuxComplex

open QECCertificates

/-!
# Lower-bound tools for the $1$-cosystolic distance, and an unbounded $d_1^\bullet=k-1$ family

`Homology/AuxComplex.lean` gave the definition of the $1$-cosystolic distance
(`cosystolicDistance`, [14] §1.2), and machine-checked the **gauging case $d_1^\bullet = 1$**
(`gauging_cosystolicDistance_eq_one`) as well as the **negative result**
`graphOf_not_high_cosystolic` (2-regular + a family of components avoiding some vertex ⟹
$d_1^\bullet = 1$). This module supplies **the other direction**: **lower-bound** tools for
$d_1^\bullet$, and a machine-checkable family with **unbounded** $d_1^\bullet$ — that is,
hypothesis 1 of [14] Theorem 5.3, "auxiliary complex has 1-cosystolic distance
$\ge d/\alpha$", **can genuinely be instantiated under this library's conventions** (this
module gives two families of examples with $d_i>1$).

## 1. Which source sentence → which library definition → which theorem of this module

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895
(`refs/Fast and fault-tolerant logical measurements - Auxiliary hypergraphs and
transversal surgery.pdf`).

**(1) §1.2 (p.3)** defines the $1$-cosystolic distance and a *component*:

> By including $W$, we can now consider the 1-cosystolic distance of $H^\bullet$, which is
> $$d_1^\bullet = \min\{|u| : u \in \ker(\delta_2)\setminus\mathrm{im}(\delta_1)\}.$$

> …a component is a collection of vertices which intersect every hyperedge on an even
> number of vertices.

→ this library's `cosystolicDistance` / `IsCosystolic` / `IsComponent` (all in
`Homology/AuxComplex.lean`). **Every distance theorem** of this module is stated directly on
this definition, without introducing a second notion of "distance".

**(2) hypothesis 1 of Theorem 5.3 (p.32, proof in Appendix A.5, p.82)**:

> *Each auxiliary complex $(A_\bullet)_1,(A_\bullet)_2,\dots$ has 1-cosystolic distance
> $d_i \ge \frac{1}{\alpha_i}d$ … with sparse cycle bases.* (The constant-round version of
> Thm 5.3 is $d_i \ge d$.)

In Appendix A.5 the **sentence that uses this hypothesis** reads, verbatim:

> *Because each auxiliary complex $(A_\bullet)_1,(A_\bullet)_2,\dots$ has 1-cosystolic
> distance $d$, the weight of a logical fault on checks in the auxiliary system must be at
> least $d$.*

→ that is, "**every $1$-cosystolic cochain has weight $\ge d$**". This module machine-checks
it as the **lower-bound half** of `cosystolicDistance_pair_eq` (`cosystolicDistance_pair_ge`),
and gives an explicit witness (`pairWitness_iscosystolic`) making the equality hold.

**(3) the comparison sentence of §6.2 (p.35)**:

> Gauging logical measurement can be seen as an instance of hypergraph surgery where the
> subcode $A_\bullet$ has distance 1, and therefore requires $O(d)$ rounds of syndrome
> measurement to maintain fault-distance $d$.

→ `Homology/AuxComplex.lean` has machine-checked that its hypothesis side degenerates on
gauging (a 2-regular auxiliary structure) to $d_1^\bullet = 1$; this module gives **the other
end**: as long as the family of components $W$ **covers** every vertex, $d_1^\bullet$ can be
arbitrarily large — exactly the situation in which the necessary condition pointed out by
`high_cosystolic_requires_cover` (already in this library) is satisfied.

## 2. What this module contains

**§1 General mechanism: a component is a zero functional on $\mathrm{im}\,\delta_1$.**

* `surgeryD1_col_sum`: $\sum_{v\in S}\delta_1(v,e) = |S\cap\text{edge}_e|$ (the GF(2) reading);
* `sum_mulVec_surgeryD1_eq_zero_of_isComponent`: `IsComponent H S` ⟹
  $\sum_{v\in S}(\delta_1 f)(v)=0$ — this is the "evaluated" version of
  `isComponent_iff_mulVec_transpose` (a component $=\ker\delta_1^{\mathsf T}$);
* `notMem_image_surgeryD1_of_component_odd` / `isCosystolic_of_component_odd`:
  the coordinate sum of $u$ on some component is $1$ ⟹ $u\notin\mathrm{im}\,\delta_1$,
  and adding $\delta_2u=0$ gives a $1$-cosystolic cochain.

This mechanism is the tool for **upper bounds**: to exhibit a $1$-cosystolic cochain it
suffices to point to an "odd component" witness.
`gauging_cosystolicDistance_eq_one` in `Homology/AuxComplex.lean` is exactly its special case
$S=\{v\}$.

**§2 A general lower bound: the complete classification at weight $1$ ⟹ $d_1^\bullet\ge 2$
under a cover.**

* `isCosystolic_indVec_singleton_iff`: on an **even hypergraph**,
  `IsCosystolic H W (indVec {v}) ↔ ∀ w, v ∉ W w` — both directions are given (the existing
  module has only the half "$v\notin\bigcup W$"; this module supplies the **reverse**
  direction, so the weight-$1$ case is classified **completely**);
* `two_le_hammingNorm_of_isCosystolic`: hence as soon as $W$ covers every vertex, **every**
  $1$-cosystolic cochain has weight $\ge 2$ — this is the precise meaning of
  "$d_1^\bullet\ge 2$" under this library's conventions (the zero vector does not count in the
  definition, see `isCosystolic_ne_zero`, so the lower bound is stated for the weight of a
  cosystolic cochain);
* `eq_indVec_support`: turns a vector into the indicator vector of its own support (an
  intermediate step, itself a reusable tool).

**§3 A structured family: $d_1^\bullet = k-1$, unbounded.** Take

* the vertices $V=\mathrm{Fin}\,k$, with two distinct points $a\ne b$ designated
  (`pairEdgeHyper`);
* a **single hyperedge** $\text{edge}_0=\{a,b\}$ ($m=1$; this is a 2-regular hypergraph);
* the family of components $W=\{\{a,b,t\}:t\in T\}$, where $T$ is **every vertex other than
  $a,b$** (`pairTripleW`).

Every member of $W$ is a component (it meets the unique hyperedge in $2$ vertices), and $W$
**covers** $V$. Hence

$$d_1^\bullet = |T|+1 = k-1 \qquad(\texttt{cosystolicDistance\_pair\_eq},\ \texttt{\_\_compl}).$$

$k$ is arbitrary ($k\ge2$), so $d_1^\bullet$ is unbounded above: taking $d=k-1$ and
$\alpha_i=1$ yields infinitely many machine-checkable instances of hypothesis 1 of [14]
Thm 5.3.

**Why does this 2-regular family escape the negative result `graphOf_not_high_cosystolic`?**
The hypothesis of that negative result is "there is a vertex not in $\bigcup W$"; the $W$ of
this family **covers** $V$, so the hypothesis fails. On a **connected** graph the only
components are $\varnothing$ and $V$ (`graphOf_components_eq`), so covering $V$ with
components of size $O(1)$ forces $W\ni V$; this family uses a **disconnected** 2-regular
hypergraph (the vertices other than $a,b$ are isolated), so each $\{a,b,t\}$ is a component of
size $O(1)$. This is the **entire** reason for the escape, recorded faithfully in the honest
boundary.

**§4 One instance that is connected ($d_1^\bullet=2$)**: $V=\mathrm{Fin}\,5$, hyperedges
$\{0,1\}$ and $\{0,2,3,4\}$ (they share the vertex $0$ and together cover every vertex, hence
the incidence graph is **connected**), and the family of components $\{\{0,1,2\},\{3,4\}\}$.
Then `cosystolicDistance_connExample_eq_two` gives $d_1^\bullet=2$ — so $d_1^\bullet>1$ **is**
attainable on a **connected** auxiliary structure, and the "disconnectedness" of the family
above is a property of **that family**, not a necessary condition for $d_1^\bullet\ge2$.

**§5 The $W$ equivalence classes and the complete classification at weight $2$.** Introduce the
$W$ equivalence

$$a \sim_W b \iff \forall w,\ a \in W_w \leftrightarrow b \in W_w ,$$

so that the two halves in the definition of $d_1^\bullet$ are each **completely
characterized** (the definition is `WSame`, the conclusions are the four items below):

* `surgeryD2_mulVec_indVec_pair_eq_zero_iff`: $\delta_2$ sends $\{a,b\}$ to zero if and only
  if $a\sim_W b$ — the kernel half;
* `exists_surgeryD1_eq_iff_forall_component` (the technical core of this section, the duality
  on a **general hypergraph**): $u\in\mathrm{im}\,\delta_1$ if and only if $u$ is orthogonal to
  **every component**. §1 machine-checks the half "component $\Rightarrow$ zero functional";
  here the reverse direction is supplied, so $\mathrm{im}\,\delta_1$ is **completely
  characterized** by the components;
* `mem_image_surgeryD1_indVec_pair_iff`: $\{a,b\}\in\mathrm{im}\,\delta_1$ if and only if
  **no** component separates $a$ from $b$ — the image half;
* `isCosystolic_indVec_pair_iff` / `isCosystolic_indVec_pair_iff_component`: the
  **necessary-and-sufficient classification** — $\{a,b\}$ is a $1$-cosystolic cochain if and
  only if "$a\sim_W b$" and "some component separates $a$ from $b$", both factors entirely
  **decidable**.

**§6 A family with connected incidence graph and unbounded $d_1^\bullet$.** First formalize
"the incidence graph is connected" itself as `IncidenceConnected`, then take the vertex set
$V=\mathrm{Fin}\,k$ ($k$ even), a **single hyperedge** $=V$, and the family of components given
by the (distinct) point pairs within $Q$ and within $Q^{\mathsf c}$ (`splitPairW`, each member
having exactly $2$ vertices). Then the incidence graph of $H$ is **connected**
(`univEdgeHyper_incidenceConnected`), every hyperedge has even cardinality, $W$ covers $V$, and
$\ker\delta_2$ is exactly the vectors that are "constant on $Q$ and constant on
$Q^{\mathsf c}$" (`mulVec_surgeryD2_splitPairW_eq_zero_iff` — it has **no** kernel element of
weight $2$), so

$$d_1^\bullet=\min(|Q|,|Q^{\mathsf c}|)
\qquad(\texttt{cosystolicDistance\_univEdge\_splitPairW\_eq}),$$

and taking $|Q|=k/2$ gives $d_1^\bullet=k/2$
(`cosystolicDistance_univEdge_splitPairW_half`).
`exists_incidenceConnected_cosystolicDistance_ge` packages it as: for every $d$ there is an
instance with **connected incidence graph**, $W$ covering, components of size $O(1)$, and
$d_1^\bullet\ge d$ — that is, the **disconnectedness of the family of §3 is not a necessary
condition**.

## 3. Honest boundary (the paper text cites this paragraph)

**Already machine-checked**:

1. **General mechanism**: a component gives a zero functional on $\mathrm{im}\,\delta_1$
   (the three items of §1);
2. **General lower bound (weight one)**: the **necessary-and-sufficient** characterization of
   the weight-$1$ $1$-cosystolic cochains on an even hypergraph, and "$W$ covers $V$ ⟹ every
   $1$-cosystolic cochain has weight $\ge 2$" (the three items of §2);
3. **Structured family**: the unbounded family with $d_1^\bullet=k-1$, where the upper and
   the lower bound are **both** theorems (`cosystolicDistance_pair_le` and
   `cosystolicDistance_pair_ge`);
4. **One connected instance**: the example of §4 with two hyperedges and two components,
   $d_1^\bullet=2$ decided vector by vector (`cosystolicDistance_connExample_eq_two`).
5. **The complete classification at weight $2$** (§5, **general hypergraph**, not just some
   family): the $W$ equivalence (`WSame`) and the pair of **necessary-and-sufficient**
   conditions "component separation" (`isCosystolic_indVec_pair_iff` /
   `isCosystolic_indVec_pair_iff_component`), together with the duality they use,
   `exists_surgeryD1_eq_iff_forall_component` ($\mathrm{im}\,\delta_1$ completely
   characterized by the components).
6. **A family with connected incidence graph and unbounded $d_1^\bullet$** (§6): on
   `univEdgeHyper` + `splitPairW`, $d_1^\bullet=\min(|Q|,|Q^{\mathsf c}|)$, with upper and
   lower bound **both** theorems (`cosystolicDistance_univEdge_splitPairW_eq`), equal to
   $k/2$ when $|Q|=k/2$; connectedness itself is formalized as `IncidenceConnected`
   (`exists_incidenceConnected_cosystolicDistance_ge`).

**Not formalized** (**not claimed**):

1. **A lower bound $d_1^\bullet\ge 3$ (indeed any $d$) on a general hypergraph**.
   $d_1^\bullet$ is "the minimum weight of an element of $\ker\delta_2$ lying **outside**
   $\mathrm{im}\,\delta_1$", i.e. in classical coding theory the **minimum weight of the
   quotient space $\ker\delta_2/\mathrm{im}\,\delta_1$** — in general there is no combinatorial
   formula, and it is of the same difficulty as the code-distance lower bound of a classical
   code. What this module gives is: the mechanism (§1), the complete classification at weight
   $1$ **and weight $2$** (§2, §5), and **two families** (§3, §6) — the $W$ equivalence needed
   for the weight-$2$ classification is `WSame`.
   **What remains open is a uniform treatment by weight**: the classification at weight $3$
   and above is not done, and the weight-$2$ classification gives a criterion for **that one
   weight** only (deciding "whether a given pair is a cosystolic cochain" is a finite,
   decidable linear-algebra check), not a general lower bound for $d_1^\bullet$.
2. **The second half of [14] hypothesis 1, "with sparse cycle bases"**. This library has no
   layer of "cycle bases" (`Homology/AuxComplex.lean` only reads $\ker\delta_1$ as the
   coordinatewise form of a "cycle set"), so this module **does not touch** the LDPC property.
3. **The fault-tolerance conclusion of [14] Theorem 5.3 itself**. This module only
   machine-checks that its **hypothesis** holds for one family; it makes no fault-distance
   argument — that is the boundary of `Homology/FaultComplex*.lean` and
   `the gauged-measurement companion development's `SurgeryProtocol` module`, which this module does not modify.
4. **Connectedness and unboundedness of the families**: the unbounded family of §3 is **not a
   connected graph** (the vertices other than $a,b$ are isolated), and this is exactly why it
   can cover $V$ with components of size $O(1)$ (on a **connected** graph the only components
   are $\varnothing$ and $V$, see `graphOf_components_eq`, so covering $V$ with $O(1)$
   components forces $W\ni V$). **"Disconnected" is not a necessary condition**: §4 gives an
   instance with **connected incidence graph** ($d_1^\bullet=2$), and §6 goes further and gives
   a **connected and unbounded** family (`univEdgeHyper` + `splitPairW`, $d_1^\bullet=k/2$,
   $k$ any even number). **The price of this family must be stated clearly**: it has only
   **one** hyperedge, and that hyperedge is the whole of $V$, so the second half of [14]
   hypothesis 1, "with sparse cycle bases" (the LDPC property), **fails** for this family — it
   instantiates the first half of hypothesis 1 ($d_i\ge d/\alpha_i$, components of size
   $O(1)$), consistent with item 2 above. Also: the hypothesis of the existing negative result
   `graphOf_not_high_cosystolic` is "there is a vertex not in $\bigcup W$", and the three
   instances of this module all **cover** $V$, so none of them conflicts with it.

**Trust base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axioms.
-/

namespace QECCertificates.Homology

open scoped BigOperators

open _root_.Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {k m : ℕ}

/-! ## 1. General mechanism: a component is a zero functional on `im δ₁` -/

/-- The support of an indicator vector is the set itself. -/
theorem support_indVec (S : Finset (Fin k)) : support (indVec S) = S := by
  ext i
  rw [mem_support, indVec]
  constructor
  · intro h
    by_contra hi
    rw [ite_eq_right (by simpa using hi)] at h
    exact h rfl
  · intro hi
    rw [ite_eq_left hi]
    exact one_ne_zero

/-- The weight of an indicator vector equals its cardinality (the "weight = set size"
reading of `indVec`). -/
theorem hammingNorm_indVec (S : Finset (Fin k)) : hammingNorm (indVec S) = S.card := by
  rw [← weight_eq_hammingNorm, support_indVec]

/-- Every vector is the indicator vector of its own support (over GF(2) the values are only
$0$ and $1$). -/
theorem eq_indVec_support (u : Vec k) : u = indVec (support u) := by
  funext x
  rw [indVec]
  by_cases h : u x = 0
  · rw [ite_eq_right (by simpa [mem_support] using h), h]
  · rw [ite_eq_left (by simpa [mem_support] using h), eq_one_of_ne_zero h]

/-- **The coordinatewise expansion of $\delta_2$**: the value at the `w`-th component is the
coordinate sum of `u` over `W w`. -/
theorem surgeryD2_mulVec_sum {ι : Type*} (W : ι → Finset (Fin k)) (u : Vec k) (w : ι) :
    (surgeryD2 W *ᵥ u) w = ∑ v ∈ W w, u v := by
  have key : ∀ v : Fin k, surgeryD2 W w v * u v = (if v ∈ W w then u v else 0) := by
    intro v
    rw [surgeryD2]
    by_cases h : v ∈ W w <;> simp [h]
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply]
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  rw [← Finset.sum_filter]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The column sum of $\delta_1$**: the sum of the values of $S$ on the hyperedge $e$ is
$=|S\cap\text{edge}_e|$ (the GF(2) writing). -/
theorem surgeryD1_col_sum (H : AuxHypergraph k m) (S : Finset (Fin k)) (e : Fin m) :
    ∑ v ∈ S, surgeryD1 H v e = (((S ∩ H.edge e).card : ℕ) : ZMod 2) := by
  have key : ∀ v : Fin k, surgeryD1 H v e = (if v ∈ H.edge e then (1 : ZMod 2) else 0) := by
    intro v; rw [surgeryD1]
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- **A component is a zero functional on $\mathrm{im}\,\delta_1$**: $S$ is a component ⟹
$\sum_{v\in S}(\delta_1 f)(v)=0$. This is the "evaluated" version of
`isComponent_iff_mulVec_transpose` (a component $=\ker\delta_1^{\mathsf T}$), and the
starting point of every mechanism in this module. -/
theorem sum_mulVec_surgeryD1_eq_zero_of_isComponent (H : AuxHypergraph k m)
    {S : Finset (Fin k)} (hS : IsComponent H S) (f : Vec m) :
    ∑ v ∈ S, (surgeryD1 H *ᵥ f) v = 0 := by
  have hpt : ∀ v : Fin k, (surgeryD1 H *ᵥ f) v = ∑ e : Fin m, surgeryD1 H v e * f e := by
    intro v
    rw [Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row_apply]
  calc ∑ v ∈ S, (surgeryD1 H *ᵥ f) v
      = ∑ v ∈ S, ∑ e : Fin m, surgeryD1 H v e * f e :=
        Finset.sum_congr rfl (fun v _ => hpt v)
    _ = ∑ e : Fin m, ∑ v ∈ S, surgeryD1 H v e * f e := Finset.sum_comm
    _ = ∑ e : Fin m, (∑ v ∈ S, surgeryD1 H v e) * f e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        exact (Finset.sum_mul S (fun v => surgeryD1 H v e) (f e)).symm
    _ = 0 := by
        refine Finset.sum_eq_zero (fun e _ => ?_)
        rw [surgeryD1_col_sum H S e]
        obtain ⟨t, ht⟩ := hS e
        rw [ht, Nat.cast_add, CharTwo.add_self_eq_zero (t : ZMod 2), zero_mul]

/-- **The odd-component certificate**: if the coordinate sum of `u` on some **component** is
$1$, then `u` is not in the image of $\delta_1$. -/
theorem notMem_image_surgeryD1_of_component_odd (H : AuxHypergraph k m)
    {S : Finset (Fin k)} (hS : IsComponent H S) {u : Vec k}
    (h : ∑ v ∈ S, u v = 1) : ¬ ∃ f : Vec m, surgeryD1 H *ᵥ f = u := by
  rintro ⟨f, rfl⟩
  rw [sum_mulVec_surgeryD1_eq_zero_of_isComponent H hS f] at h
  exact one_ne_zero h.symm

/-- **The odd-component certificate (composite form)**: $\delta_2u=0$ and the coordinate of
`u` on some component is $1$ ⟹ `u` is a $1$-cosystolic cochain.
`gauging_cosystolicDistance_eq_one` is its special case $S=\{v\}$. -/
theorem isCosystolic_of_component_odd {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) {S : Finset (Fin k)} (hS : IsComponent H S) {u : Vec k}
    (hker : surgeryD2 W *ᵥ u = 0) (h : ∑ v ∈ S, u v = 1) : IsCosystolic H W u :=
  ⟨hker, notMem_image_surgeryD1_of_component_odd H hS h⟩

/-! ## 2. A general lower bound: complete classification at weight one, and "cover ⟹ weight ≥ 2" -/

/-- **A necessary-and-sufficient characterization of the weight-$1$ $1$-cosystolic cochains**
(an even hypergraph): a single-point cochain is cosystolic if and only if that vertex avoids
all components. The existing module gives the "$\Leftarrow$"; here the "$\Rightarrow$" is
supplied, so weight $1$ is fully classified. -/
theorem isCosystolic_indVec_singleton_iff {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (heven : IsEvenHyper H) (v : Fin k) :
    IsCosystolic H W (indVec ({v} : Finset (Fin k))) ↔ ∀ w : ι, v ∉ W w := by
  constructor
  · intro h w hmem
    have hz := congrFun h.1 w
    rw [surgeryD2_mulVec_indVec_singleton W v w, ite_eq_left hmem, Pi.zero_apply] at hz
    exact one_ne_zero hz
  · exact fun hv => isCosystolic_indVec_singleton H W heven hv

/-- **A cover ⟹ no cosystolic cochain of weight $1$**: if `W` covers every vertex, then every
$1$-cosystolic cochain has weight at least $2$. This is the precise meaning of
$d_1^\bullet\ge2$ (the zero vector does not count in the definition of $d_1^\bullet$, see
`isCosystolic_ne_zero`, so the lower bound is stated for the weight of a cosystolic
cochain). -/
theorem two_le_hammingNorm_of_isCosystolic {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (heven : IsEvenHyper H)
    (hcover : ∀ v : Fin k, ∃ w : ι, v ∈ W w) {u : Vec k} (hu : IsCosystolic H W u) :
    2 ≤ hammingNorm u := by
  by_contra hlt
  have h1 : hammingNorm u = 1 := by
    have := one_le_hammingNorm_of_ne_zero (isCosystolic_ne_zero hu)
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (by rw [weight_eq_hammingNorm]; exact h1)
  have hueq : u = indVec ({v} : Finset (Fin k)) := by
    rw [eq_indVec_support u, hv]
  have hcos : IsCosystolic H W (indVec ({v} : Finset (Fin k))) := by
    rw [← hueq]; exact hu
  obtain ⟨w, hw⟩ := hcover v
  exact ((isCosystolic_indVec_singleton_iff H W heven v).mp hcos w) hw

/-! ## 3. A structured family: the single hyperedge `{a,b}` and a covering component family -/

/-- **The single-hyperedge auxiliary hypergraph** ($m=1$): the only hyperedge is `{a,b}`. -/
def pairEdgeHyper (a b : Fin k) : AuxHypergraph k 1 where
  edge _ := {a, b}

/-- **The covering component family**: each `t ∈ T` gives the component `{a,b,t}`. -/
def pairTripleW (a b : Fin k) (T : Finset (Fin k)) : ↑T → Finset (Fin k) :=
  fun t => insert t.1 ({a, b} : Finset (Fin k))

theorem pairEdgeHyper_isEven {a b : Fin k} (hab : a ≠ b) :
    IsEvenHyper (pairEdgeHyper a b) := by
  intro e
  simp only [pairEdgeHyper]
  rw [Finset.card_pair hab]
  exact ⟨1, rfl⟩

theorem pairTripleW_isComponent {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (t : ↑T) : IsComponent (pairEdgeHyper a b) (pairTripleW a b T t) := by
  have hset : insert t.1 ({a, b} : Finset (Fin k)) ∩ ({a, b} : Finset (Fin k)) = {a, b} :=
    Finset.inter_eq_right.mpr (Finset.subset_insert _ _)
  intro e
  simp only [pairEdgeHyper, pairTripleW]
  rw [hset, Finset.card_pair hab]
  exact ⟨1, rfl⟩

/-- Every `t` in `T` avoids `{a,b}`. -/
theorem pairTripleW_notMem {a b : Fin k} {T : Finset (Fin k)} (haT : a ∉ T) (hbT : b ∉ T)
    (t : ↑T) : t.1 ∉ ({a, b} : Finset (Fin k)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun h => haT (h ▸ t.2), fun h => hbT (h ▸ t.2)⟩

/-- **The component constraint of $\delta_2$**: the equation of the `t`-th component is
$u_t + (u_a+u_b) = 0$ — splitting the sum over a three-element set by `insert`. -/
theorem mulVec_surgeryD2_pairTripleW {a b : Fin k} {T : Finset (Fin k)}
    (haT : a ∉ T) (hbT : b ∉ T) (u : Vec k) (t : ↑T) :
    (surgeryD2 (pairTripleW a b T) *ᵥ u) t
      = u t.1 + ∑ v ∈ ({a, b} : Finset (Fin k)), u v := by
  rw [surgeryD2_mulVec_sum, pairTripleW,
    Finset.sum_insert (pairTripleW_notMem haT hbT t)]

/-- **The kernel characterization**: $\ker\delta_2$ is exactly the vectors whose coordinates
on `T` all equal $u_a+u_b$. -/
theorem ker_pairTripleW {a b : Fin k} {T : Finset (Fin k)} (haT : a ∉ T) (hbT : b ∉ T)
    (u : Vec k) :
    (surgeryD2 (pairTripleW a b T) *ᵥ u = 0)
      ↔ ∀ t : ↑T, u t.1 = ∑ v ∈ ({a, b} : Finset (Fin k)), u v := by
  constructor
  · intro h t
    have ht := congrFun h t
    rw [mulVec_surgeryD2_pairTripleW haT hbT u t, Pi.zero_apply] at ht
    exact (add_eq_zero_iff_eq _ _).mp ht
  · intro h
    funext t
    rw [mulVec_surgeryD2_pairTripleW haT hbT u t, Pi.zero_apply, h t]
    exact CharTwo.add_self_eq_zero _

/-- **The image of $\delta_1$ on the single hyperedge**: $f\mapsto f_0\cdot\{a,b\}$. -/
theorem mulVec_surgeryD1_pairEdgeHyper (a b : Fin k) (f : Vec 1) :
    (surgeryD1 (pairEdgeHyper a b) *ᵥ f) = (f 0) • indVec ({a, b} : Finset (Fin k)) := by
  funext v
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
  rw [surgeryD1, indVec, pairEdgeHyper]
  by_cases h : v ∈ ({a, b} : Finset (Fin k)) <;> simp [h, mul_comm]

/-- **Membership in the image**: $\mathrm{im}\,\delta_1=\{0,\ \{a,b\}\}$. -/
theorem mem_image_pairEdgeHyper (a b : Fin k) (u : Vec k) :
    (∃ f : Vec 1, surgeryD1 (pairEdgeHyper a b) *ᵥ f = u)
      ↔ (u = 0 ∨ u = indVec ({a, b} : Finset (Fin k))) := by
  constructor
  · rintro ⟨f, hf⟩
    rw [mulVec_surgeryD1_pairEdgeHyper] at hf
    rw [← hf]
    by_cases h : f 0 = 0
    · left; rw [h, zero_smul]
    · right; rw [eq_one_of_ne_zero h, one_smul]
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [Matrix.mulVec_zero]⟩
    · refine ⟨fun _ => 1, ?_⟩
      rw [mulVec_surgeryD1_pairEdgeHyper, one_smul]

/-- **A vector supported in `{a,b}` whose two entries are equal lies in $\mathrm{im}\,\delta_1$**
— this is the closing step of the lower-bound proof of §3: a $\ker\delta_2$ element with $c=0$
is automatically in the image of $\delta_1$, hence is not a cosystolic cochain. -/
theorem mem_image_of_pair_support {a b : Fin k} {u : Vec k}
    (hout : ∀ v, v ≠ a → v ≠ b → u v = 0) (heq : u a = u b) :
    ∃ f : Vec 1, surgeryD1 (pairEdgeHyper a b) *ᵥ f = u := by
  rw [mem_image_pairEdgeHyper]
  have hkey : u = (u a) • indVec ({a, b} : Finset (Fin k)) := by
    funext v
    rw [Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne v a with hva | hva
    · rw [hva]
      simp [indVec]
    · rcases eq_or_ne v b with hvb | hvb
      · rw [hvb]
        rw [indVec, ite_eq_left (by simp : b ∈ ({a, b} : Finset (Fin k))), mul_one]
        exact heq.symm
      · have hnot : ¬ (v ∈ ({a, b} : Finset (Fin k))) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hva, hvb⟩
        rw [hout v hva hvb, indVec, ite_eq_right hnot, mul_zero]
  by_cases ha : u a = 0
  · left; rw [hkey, ha, zero_smul]
  · right; rw [hkey, eq_one_of_ne_zero ha, one_smul]

/-- The witness vector `indVec (insert a T)` is sent to zero by $\delta_2$. -/
theorem pairWitness_ker {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (haT : a ∉ T) (hbT : b ∉ T) :
    surgeryD2 (pairTripleW a b T) *ᵥ indVec (insert a T) = 0 := by
  rw [ker_pairTripleW haT hbT]
  intro t
  have h1 : indVec (insert a T) t.1 = 1 := by
    rw [indVec, ite_eq_left (Finset.mem_insert_of_mem t.2)]
  have h2 : indVec (insert a T) a = 1 := by
    rw [indVec, ite_eq_left (Finset.mem_insert_self a T)]
  have hbn : ¬ (b ∈ insert a T) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hba => hab hba.symm, hbT⟩
  have h3 : indVec (insert a T) b = 0 := by rw [indVec, ite_eq_right hbn]
  rw [h1, Finset.sum_pair hab, h2, h3]
  norm_num

/-- The witness vector is not in the image of $\delta_1$ (its weight is $|T|+1\ge2$, whereas
the image contains only $0$ and `indVec {a,b}`). -/
theorem pairWitness_notMem_image {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (hbT : b ∉ T) :
    ¬ ∃ f : Vec 1, surgeryD1 (pairEdgeHyper a b) *ᵥ f = indVec (insert a T) := by
  intro h
  rw [mem_image_pairEdgeHyper] at h
  have ha : indVec (insert a T) a = 1 := by
    rw [indVec, ite_eq_left (Finset.mem_insert_self a T)]
  have hbn : ¬ (b ∈ insert a T) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hba => hab hba.symm, hbT⟩
  have hb : indVec (insert a T) b = 0 := by rw [indVec, ite_eq_right hbn]
  rcases h with h | h
  · have hc := congrFun h a
    rw [ha, Pi.zero_apply] at hc
    exact one_ne_zero hc
  · have hc := congrFun h b
    rw [hb, indVec, ite_eq_left (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))] at hc
    exact one_ne_zero hc.symm

/-- **The witness**: `indVec (insert a T)` is a $1$-cosystolic cochain of weight exactly
$|T|+1$. -/
theorem pairWitness_iscosystolic {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (haT : a ∉ T) (hbT : b ∉ T) :
    IsCosystolic (pairEdgeHyper a b) (pairTripleW a b T) (indVec (insert a T)) :=
  ⟨pairWitness_ker hab haT hbT, pairWitness_notMem_image hab hbT⟩

/-- **Upper bound: $d_1^\bullet \le |T|+1$** (given by the explicit witness). -/
theorem cosystolicDistance_pair_le {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (haT : a ∉ T) (hbT : b ∉ T) :
    cosystolicDistance (pairEdgeHyper a b) (pairTripleW a b T) ≤ T.card + 1 := by
  have hmem := pairWitness_iscosystolic hab haT hbT
  have hw : hammingNorm (indVec (insert a T)) = T.card + 1 := by
    rw [hammingNorm_indVec, Finset.card_insert_of_notMem haT]
  have hset : (T.card + 1) ∈ {w : ℕ | ∃ u : Vec k,
      IsCosystolic (pairEdgeHyper a b) (pairTripleW a b T) u ∧ hammingNorm u = w} :=
    ⟨indVec (insert a T), hmem, hw⟩
  exact csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hset

/-- **Lower bound: $d_1^\bullet \ge |T|+1$** — the machine counterpart, on this family, of the
sentence of [14] Appendix A.5, "the weight of a logical fault on checks in the auxiliary
system must be at least $d$". -/
theorem cosystolicDistance_pair_ge {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (haT : a ∉ T) (hbT : b ∉ T) (hcover : ∀ v, v ≠ a → v ≠ b → v ∈ T)
    {u : Vec k} (hu : IsCosystolic (pairEdgeHyper a b) (pairTripleW a b T) u) :
    T.card + 1 ≤ hammingNorm u := by
  have hker := (ker_pairTripleW haT hbT u).mp hu.1
  have hpair : ∑ v ∈ ({a, b} : Finset (Fin k)), u v = u a + u b := Finset.sum_pair hab
  by_cases hc : ∑ v ∈ ({a, b} : Finset (Fin k)), u v = 0
  · exfalso
    have hout : ∀ v, v ≠ a → v ≠ b → u v = 0 := by
      intro v hva hvb
      have h := hker ⟨v, hcover v hva hvb⟩
      rw [hc] at h
      exact h
    have heq : u a = u b := by
      have h := hc
      rw [hpair] at h
      exact (add_eq_zero_iff_eq _ _).mp h
    exact hu.2 (mem_image_of_pair_support hout heq)
  · have hc1 : ∑ v ∈ ({a, b} : Finset (Fin k)), u v = 1 := eq_one_of_ne_zero hc
    have hall : ∀ t : ↑T, u t.1 = 1 := fun t => by rw [hker t, hc1]
    have hsum1 : u a + u b = 1 := by rw [← hpair]; exact hc1
    have hTsub : T ⊆ support u := by
      intro v hv
      rw [mem_support]
      have hv1 := hall ⟨v, hv⟩
      rw [hv1]
      exact one_ne_zero
    have hw : ∀ w : Fin k, w ∉ T → u w = 1 → T.card + 1 ≤ hammingNorm u := by
      intro w hwT hw1
      have hsub : insert w T ⊆ support u := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · rw [mem_support, hw1]; exact one_ne_zero
        · exact hTsub hv
      calc T.card + 1 = (insert w T).card := (Finset.card_insert_of_notMem hwT).symm
        _ ≤ (support u).card := Finset.card_le_card hsub
        _ = hammingNorm u := weight_eq_hammingNorm u
    by_cases ha : u a = 0
    · exact hw b hbT (by rw [ha, zero_add] at hsum1; exact hsum1)
    · exact hw a haT (eq_one_of_ne_zero ha)

/-- **The main theorem: $d_1^\bullet=|T|+1$** (the upper bound from the explicit witness, the
lower bound from the previous item). -/
theorem cosystolicDistance_pair_eq {a b : Fin k} (hab : a ≠ b) {T : Finset (Fin k)}
    (haT : a ∉ T) (hbT : b ∉ T) (hcover : ∀ v, v ≠ a → v ≠ b → v ∈ T) :
    cosystolicDistance (pairEdgeHyper a b) (pairTripleW a b T) = T.card + 1 := by
  refine le_antisymm (cosystolicDistance_pair_le hab haT hbT) ?_
  refine le_csInf ⟨T.card + 1, ?_⟩ ?_
  · exact ⟨indVec (insert a T), pairWitness_iscosystolic hab haT hbT,
      by rw [hammingNorm_indVec, Finset.card_insert_of_notMem haT]⟩
  · rintro n ⟨u, hu, rfl⟩
    exact cosystolicDistance_pair_ge hab haT hbT hcover hu

/-- **$T$ taken as "every vertex other than `{a,b}`"**: a direct instance of the main
theorem. -/
theorem cosystolicDistance_pair_compl {a b : Fin k} (hab : a ≠ b) :
    cosystolicDistance (pairEdgeHyper a b) (pairTripleW a b (Finset.univ \ {a, b}))
      = (Finset.univ \ ({a, b} : Finset (Fin k))).card + 1 := by
  refine cosystolicDistance_pair_eq hab (by simp) (by simp) ?_
  intro v hva hvb
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hva, hvb⟩

/-- **$d_1^\bullet = k-1$**: on `Fin k`, with the single hyperedge `{a,b}` and the component
family given by all the remaining vertices, the $1$-cosystolic distance is exactly $k-1$. $k$
is arbitrary, so $d_1^\bullet$ is **unbounded** — taking $d=k-1$ and $\alpha_i=1$ in
hypothesis $d_i\ge d/\alpha_i$ of [14] Thm 5.3 gives endlessly many instantiations. -/
theorem cosystolicDistance_pair_eq_card_sub_one {a b : Fin k} (hab : a ≠ b) :
    cosystolicDistance (pairEdgeHyper a b) (pairTripleW a b (Finset.univ \ {a, b}))
      = k - 1 := by
  rw [cosystolicDistance_pair_compl hab]
  have hcard : (Finset.univ \ ({a, b} : Finset (Fin k))).card = k - 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hab]
  have hk : 2 ≤ k := by
    have h := Finset.card_le_univ ({a, b} : Finset (Fin k))
    rw [Finset.card_pair hab, Fintype.card_fin] at h
    exact h
  rw [hcard]
  omega

/-! ## 4. One instance that is connected ($d_1^\bullet=2$)

The family of §3 is **disconnected** (the vertices other than $a,b$ are isolated). To answer
"is disconnectedness necessary", here is another instance with **connected incidence graph**:
$V=\mathrm{Fin}\,5$, hyperedges $\{0,1\}$ and $\{0,2,3,4\}$ (the two edges share the vertex
$0$ and together cover every vertex, so the incidence graph is connected; both edges have even
cardinality), with the family of components $\{\{0,1,2\},\{3,4\}\}$ (covering $V$). Hence
$d_1^\bullet=2$ — attaining $d_1^\bullet>1$ on a **connected** auxiliary structure **is**
possible.

(The family that is "connected and with unbounded $d_1^\bullet$" is in the next section, §6 —
this section only answers the question "is disconnectedness necessary".)
-/

/-- **The hypergraph of the connected instance**: the two even-cardinality hyperedges `{0,1}`
and `{0,2,3,4}`, sharing the vertex `0` and covering every vertex. -/
def connHyper : AuxHypergraph 5 2 where
  edge e := if e = (0 : Fin 2) then {0, 1} else {0, 2, 3, 4}

/-- **The component family of the connected instance**: `{0,1,2}` and `{3,4}`, covering every
vertex. -/
def connW : Fin 2 → Finset (Fin 5) := fun e => if e = (0 : Fin 2) then {0, 1, 2} else {3, 4}

theorem connHyper_edge_zero : connHyper.edge 0 = ({0, 1} : Finset (Fin 5)) := rfl

theorem connHyper_edge_one : connHyper.edge 1 = ({0, 2, 3, 4} : Finset (Fin 5)) := rfl

theorem connHyper_isEven : IsEvenHyper connHyper := by
  intro e
  fin_cases e <;> decide

theorem connW_isComponent : ∀ e : Fin 2, IsComponent connHyper (connW e) := by
  intro e
  fin_cases e <;> intro e' <;> fin_cases e' <;> decide

theorem connW_covers : ∀ v : Fin 5, ∃ e : Fin 2, v ∈ connW e := by decide

theorem connExample_witness : IsCosystolic connHyper connW (indVec ({3, 4} : Finset (Fin 5))) := by
  unfold IsCosystolic
  decide

theorem connExample_ge : ∀ u : Vec 5, IsCosystolic connHyper connW u → 2 ≤ hammingNorm u := by
  unfold IsCosystolic
  decide

/-- **The $1$-cosystolic distance of the connected instance is $2$**: the witness `{3,4}`
gives the upper bound, and a vector-by-vector decision gives the lower bound ($5$ vertices,
enumerating all $2^5$ vectors). -/
theorem cosystolicDistance_connExample_eq_two : cosystolicDistance connHyper connW = 2 := by
  have hmem := connExample_witness
  have hw : hammingNorm (indVec ({3, 4} : Finset (Fin 5))) = 2 := by
    rw [hammingNorm_indVec, Finset.card_pair (by decide : (3 : Fin 5) ≠ 4)]
  have hset : (2 : ℕ) ∈ {w : ℕ | ∃ u : Vec 5,
      IsCosystolic connHyper connW u ∧ hammingNorm u = w} :=
    ⟨indVec ({3, 4} : Finset (Fin 5)), hmem, hw⟩
  refine le_antisymm (csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hset) ?_
  refine le_csInf ⟨2, hset⟩ ?_
  rintro n ⟨u, hu, rfl⟩
  exact connExample_ge u hu

/-! ## 5. The `W` equivalence classes and the complete classification at weight 2 -/

/-- **The `W` equivalence**: two vertices lie in **exactly the same** members of the
components. -/
def WSame {k : ℕ} {ι : Type*} (W : ι → Finset (Fin k)) (a b : Fin k) : Prop :=
  ∀ w : ι, (a ∈ W w ↔ b ∈ W w)

theorem wsame_refl {ι : Type*} (W : ι → Finset (Fin k)) (a : Fin k) : WSame W a a :=
  fun _ => Iff.rfl

theorem wsame_symm {ι : Type*} {W : ι → Finset (Fin k)} {a b : Fin k} (h : WSame W a b) :
    WSame W b a :=
  fun w => (h w).symm

theorem wsame_trans {ι : Type*} {W : ι → Finset (Fin k)} {a b c : Fin k}
    (hab : WSame W a b) (hbc : WSame W b c) : WSame W a c :=
  fun w => (hab w).trans (hbc w)

/-- The two-point indicator vector split point by point (`a ≠ b`). -/
theorem indVec_pair_eq_add {k : ℕ} (a b : Fin k) (hab : a ≠ b) :
    indVec ({a, b} : Finset (Fin k))
      = indVec ({a} : Finset (Fin k)) + indVec ({b} : Finset (Fin k)) := by
  funext v
  rw [Pi.add_apply, indVec, indVec, indVec]
  by_cases hva : v = a
  · rw [hva]
    rw [ite_eq_left (by simp : a ∈ ({a, b} : Finset (Fin k))),
      ite_eq_left (by simp : a ∈ ({a} : Finset (Fin k))),
      ite_eq_right (by simpa [Finset.mem_singleton] using hab : ¬ (a ∈ ({b} : Finset (Fin k))))]
    norm_num
  · by_cases hvb : v = b
    · rw [hvb]
      rw [ite_eq_left (by simp : b ∈ ({a, b} : Finset (Fin k))),
        ite_eq_right (by simpa [Finset.mem_singleton] using hab.symm :
          ¬ (b ∈ ({a} : Finset (Fin k)))),
        ite_eq_left (by simp : b ∈ ({b} : Finset (Fin k)))]
      norm_num
    · rw [ite_eq_right (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hva, hvb⟩ : ¬ (v ∈ ({a, b} : Finset (Fin k)))),
        ite_eq_right (by simpa [Finset.mem_singleton] using hva : ¬ (v ∈ ({a} : Finset (Fin k)))),
        ite_eq_right (by simpa [Finset.mem_singleton] using hvb : ¬ (v ∈ ({b} : Finset (Fin k))))]
      norm_num

/-- `δ₂` applied to a two-point indicator vector, split point by point. -/
theorem surgeryD2_mulVec_indVec_pair {ι : Type*} (W : ι → Finset (Fin k)) {a b : Fin k}
    (hab : a ≠ b) :
    surgeryD2 W *ᵥ indVec ({a, b} : Finset (Fin k))
      = surgeryD2 W *ᵥ indVec ({a} : Finset (Fin k))
        + surgeryD2 W *ᵥ indVec ({b} : Finset (Fin k)) := by
  rw [indVec_pair_eq_add a b hab, Matrix.mulVec_add]

/-- The coordinates of `δ₂` applied to a two-point indicator vector. -/
theorem surgeryD2_mulVec_indVec_pair_apply {ι : Type*} (W : ι → Finset (Fin k)) {a b : Fin k}
    (hab : a ≠ b) (w : ι) :
    (surgeryD2 W *ᵥ indVec ({a, b} : Finset (Fin k))) w
      = (if a ∈ W w then (1 : ZMod 2) else 0) + (if b ∈ W w then (1 : ZMod 2) else 0) := by
  rw [surgeryD2_mulVec_indVec_pair W hab, Pi.add_apply, surgeryD2_mulVec_indVec_singleton W a w,
    surgeryD2_mulVec_indVec_singleton W b w]

/-- **The kernel condition at weight 2 is exactly `W` equivalence**. -/
theorem surgeryD2_mulVec_indVec_pair_eq_zero_iff {ι : Type*} (W : ι → Finset (Fin k))
    {a b : Fin k} (hab : a ≠ b) :
    surgeryD2 W *ᵥ indVec ({a, b} : Finset (Fin k)) = 0 ↔ WSame W a b := by
  constructor
  · intro h w
    have hw := congrFun h w
    rw [surgeryD2_mulVec_indVec_pair_apply W hab w, Pi.zero_apply] at hw
    have hw' : (if a ∈ W w then (1 : ZMod 2) else 0)
        = (if b ∈ W w then (1 : ZMod 2) else 0) := (add_eq_zero_iff_eq _ _).mp hw
    constructor
    · intro ha
      by_contra hb
      rw [ite_eq_left ha, ite_eq_right hb] at hw'
      exact one_ne_zero hw'
    · intro hb
      by_contra ha
      rw [ite_eq_right ha, ite_eq_left hb] at hw'
      exact one_ne_zero hw'.symm
  · intro h
    funext w
    rw [surgeryD2_mulVec_indVec_pair_apply W hab w, Pi.zero_apply]
    by_cases ha : a ∈ W w
    · rw [ite_eq_left ha, ite_eq_left ((h w).mp ha)]
      exact CharTwo.add_self_eq_zero (1 : ZMod 2)
    · rw [ite_eq_right ha, ite_eq_right (fun hb => ha ((h w).mpr hb))]
      exact CharTwo.add_self_eq_zero (0 : ZMod 2)

/-! ### Duality: `im δ₁` is completely characterized by the components -/

/-- **General duality**: `u` lies in the column space of `M` if and only if `u` is orthogonal
to `ker Mᵀ` (under the standard dot product).  Proved from the single home of this statement,
`QECCertificates.mem_range_mulVecLin_iff_forall_dot_eq_zero`. -/
theorem exists_mulVec_eq_iff_forall_dot_eq_zero (M : Matrix (Fin k) (Fin m) (ZMod 2))
    (u : Vec k) :
    (∃ f : Vec m, M *ᵥ f = u) ↔ ∀ y : Vec k, Mᵀ *ᵥ y = 0 → u ⬝ᵥ y = 0 := by
  have hrange : (∃ f : Vec m, M *ᵥ f = u) ↔ u ∈ LinearMap.range M.mulVecLin := by
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  rw [hrange]
  constructor
  · intro hmem y hy
    exact (dotProduct_comm u y).trans
      ((mem_range_mulVecLin_iff_forall_dot_eq_zero (M := M) u).mp hmem y hy)
  · intro h
    exact (mem_range_mulVecLin_iff_forall_dot_eq_zero (M := M) u).mpr
      (fun y hy => (dotProduct_comm u y).symm.trans (h y hy))

/-- `u ⬝ᵥ indVec S` is the coordinate sum of `u` over `S`. -/
theorem dotProduct_indVec (u : Vec k) (S : Finset (Fin k)) :
    u ⬝ᵥ indVec S = ∑ v ∈ S, u v := by
  have key : ∀ v : Fin k, u v * indVec S v = (if v ∈ S then u v else 0) := by
    intro v
    rw [indVec]
    by_cases hv : v ∈ S <;> simp [hv]
  rw [dotProduct, Finset.sum_congr rfl (fun v _ => key v), ← Finset.sum_filter]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **`im δ₁` completely characterized by the components** (the technical core of §5 of this
module): `u` is the syndrome of a physical fault if and only if `u` is orthogonal to **every
component**. §1 machine-checks only the half "component ⟹ zero functional". -/
theorem exists_surgeryD1_eq_iff_forall_component (H : AuxHypergraph k m) (u : Vec k) :
    (∃ f : Vec m, surgeryD1 H *ᵥ f = u)
      ↔ ∀ S : Finset (Fin k), IsComponent H S → ∑ v ∈ S, u v = 0 := by
  rw [exists_mulVec_eq_iff_forall_dot_eq_zero]
  constructor
  · intro h S hS
    have hy : (surgeryD1 H)ᵀ *ᵥ indVec S = 0 := (isComponent_iff_mulVec_transpose H S).mp hS
    have hz := h (indVec S) hy
    rwa [dotProduct_indVec] at hz
  · intro h y hy
    have hsupp : IsComponent H (support y) := by
      rw [isComponent_iff_mulVec_transpose]
      rw [← eq_indVec_support y]
      exact hy
    have hz : u ⬝ᵥ y = ∑ v ∈ support y, u v :=
      (congrArg (fun z : Vec k => u ⬝ᵥ z) (eq_indVec_support y)).trans
        (dotProduct_indVec u (support y))
    rw [hz]
    exact h (support y) hsupp

/-- The coordinate sum of a two-point indicator vector over `S`. -/
theorem sum_indVec_pair (S : Finset (Fin k)) {a b : Fin k} (hab : a ≠ b) :
    ∑ v ∈ S, indVec ({a, b} : Finset (Fin k)) v
      = (if a ∈ S then (1 : ZMod 2) else 0) + (if b ∈ S then (1 : ZMod 2) else 0) := by
  have key : ∀ v : Fin k, indVec ({a, b} : Finset (Fin k)) v
      = (if v ∈ ({a, b} : Finset (Fin k)) then (1 : ZMod 2) else 0) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_boole, Finset.filter_mem_eq_inter,
    card_inter_pair S hab]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> norm_num [ha, hb]

/-- **The image condition at weight 2**: $\{a,b\}$ is a physical fault (a member of
$\mathrm{im}\,\delta_1$) if and only if **no component separates `a` from `b`**. -/
theorem mem_image_surgeryD1_indVec_pair_iff (H : AuxHypergraph k m) {a b : Fin k}
    (hab : a ≠ b) :
    (∃ f : Vec m, surgeryD1 H *ᵥ f = indVec ({a, b} : Finset (Fin k)))
      ↔ ∀ S : Finset (Fin k), IsComponent H S → (a ∈ S ↔ b ∈ S) := by
  rw [exists_surgeryD1_eq_iff_forall_component]
  constructor
  · intro h S hS
    have hz := h S hS
    rw [sum_indVec_pair S hab] at hz
    have hz' : (if a ∈ S then (1 : ZMod 2) else 0)
        = (if b ∈ S then (1 : ZMod 2) else 0) := (add_eq_zero_iff_eq _ _).mp hz
    constructor
    · intro ha
      by_contra hb
      rw [ite_eq_left ha, ite_eq_right hb] at hz'
      exact one_ne_zero hz'
    · intro hb
      by_contra ha
      rw [ite_eq_right ha, ite_eq_left hb] at hz'
      exact one_ne_zero hz'.symm
  · intro h S hS
    rw [sum_indVec_pair S hab]
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha, ite_eq_left ((h S hS).mp ha)]
      exact CharTwo.add_self_eq_zero (1 : ZMod 2)
    · rw [ite_eq_right ha, ite_eq_right (fun hb => ha ((h S hS).mpr hb))]
      exact CharTwo.add_self_eq_zero (0 : ZMod 2)

/-- **The complete classification at weight 2**: $\{a,b\}$ is a $1$-cosystolic cochain if and
only if "$a \sim_W b$" and "$\{a,b\}$ is not a physical fault". -/
theorem isCosystolic_indVec_pair_iff {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) {a b : Fin k} (hab : a ≠ b) :
    IsCosystolic H W (indVec ({a, b} : Finset (Fin k)))
      ↔ WSame W a b
        ∧ ¬ ∃ f : Vec m, surgeryD1 H *ᵥ f = indVec ({a, b} : Finset (Fin k)) :=
  ⟨fun h => ⟨(surgeryD2_mulVec_indVec_pair_eq_zero_iff W hab).mp h.1, h.2⟩,
    fun h => ⟨(surgeryD2_mulVec_indVec_pair_eq_zero_iff W hab).mpr h.1, h.2⟩⟩

theorem iff_of_not_not_iff {p q : Prop} (h : ¬ (p ↔ ¬ q)) : p ↔ q := by
  constructor
  · intro hp
    by_contra hq
    exact h ⟨fun _ => hq, fun _ => hp⟩
  · intro hq
    by_contra hp
    exact h ⟨fun hp' => absurd hp' hp, fun hnq => absurd hq hnq⟩

theorem not_not_iff_of_iff {p q : Prop} (h : p ↔ q) : ¬ (p ↔ ¬ q) := by
  intro hc
  by_cases hq : q
  · exact (hc.mp (h.mpr hq)) hq
  · exact hq (h.mp (hc.mpr hq))

/-- **The complete classification at weight 2 (component form, closed)**: $\{a,b\}$ is a
$1$-cosystolic cochain if and only if "$a \sim_W b$" and "some component separates `a` from
`b`" — the two factors cover the $\ker\delta_2$ half and the $\mathrm{im}\,\delta_1$ half. -/
theorem isCosystolic_indVec_pair_iff_component {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) {a b : Fin k} (hab : a ≠ b) :
    IsCosystolic H W (indVec ({a, b} : Finset (Fin k)))
      ↔ WSame W a b ∧ ∃ S : Finset (Fin k), IsComponent H S ∧ (a ∈ S ↔ b ∉ S) := by
  rw [isCosystolic_indVec_pair_iff H W hab]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hc
    exact h.2 ((mem_image_surgeryD1_indVec_pair_iff H hab).mpr fun S hS =>
      iff_of_not_not_iff fun hss => hc ⟨S, hS, hss⟩)
  · rintro ⟨h1, S, hS, hsep⟩
    refine ⟨h1, fun hc => ?_⟩
    exact not_not_iff_of_iff ((mem_image_surgeryD1_indVec_pair_iff H hab).mp hc S hS) hsep

/-! ## 6. A family with connected incidence graph and unbounded $d_1^\bullet$ -/

/-- **Incidence adjacency**: two vertices lie in a common hyperedge. -/
def IncidenceAdj {k m : ℕ} (H : AuxHypergraph k m) (v w : Fin k) : Prop :=
  ∃ e : Fin m, v ∈ H.edge e ∧ w ∈ H.edge e

/-- **The incidence graph is connected**: any two vertices are joined by a chain of "shared
hyperedge". -/
def IncidenceConnected {k m : ℕ} (H : AuxHypergraph k m) : Prop :=
  ∀ v w : Fin k, Relation.ReflTransGen (IncidenceAdj H) v w

/-- **The single-hyperedge "full" hypergraph**: the only hyperedge is the whole vertex set `V`. -/
def univEdgeHyper (k : ℕ) : AuxHypergraph k 1 where
  edge _ := Finset.univ

theorem univEdgeHyper_edge (k : ℕ) (e : Fin 1) : (univEdgeHyper k).edge e = Finset.univ := rfl

theorem univEdgeHyper_isEven {k : ℕ} (hk : Even k) : IsEvenHyper (univEdgeHyper k) := by
  intro e
  rw [univEdgeHyper_edge, Finset.card_univ, Fintype.card_fin]
  exact hk

theorem univEdgeHyper_incidenceConnected (k : ℕ) : IncidenceConnected (univEdgeHyper k) :=
  fun v w => Relation.ReflTransGen.single ⟨0, Finset.mem_univ v, Finset.mem_univ w⟩

theorem mulVec_surgeryD1_univEdgeHyper (k : ℕ) (f : Vec 1) :
    surgeryD1 (univEdgeHyper k) *ᵥ f = (f 0) • indVec (Finset.univ : Finset (Fin k)) := by
  funext v
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
  rw [surgeryD1, univEdgeHyper, indVec]
  simp [mul_comm]

/-- The $\mathrm{im}\,\delta_1$ of the full hypergraph has only two elements: $0$ and the
all-ones vector. -/
theorem mem_image_univEdgeHyper (k : ℕ) (u : Vec k) :
    (∃ f : Vec 1, surgeryD1 (univEdgeHyper k) *ᵥ f = u)
      ↔ (u = 0 ∨ u = indVec (Finset.univ : Finset (Fin k))) := by
  constructor
  · rintro ⟨f, hf⟩
    have hf' : u = (f 0) • indVec (Finset.univ : Finset (Fin k)) := by
      rw [← hf, mulVec_surgeryD1_univEdgeHyper]
    rw [hf']
    by_cases h : f 0 = 0
    · left; rw [h, zero_smul]
    · right; rw [eq_one_of_ne_zero h, one_smul]
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [Matrix.mulVec_zero]⟩
    · exact ⟨fun _ => 1, by rw [mulVec_surgeryD1_univEdgeHyper]; simp⟩

/-- **The "same-side pair" component family**: the (distinct) point pairs within `Q` and
within `Qᶜ`, and the empty set in the other cases (the empty set is also a component, and the
constraint it gives is empty). -/
def splitPairW (Q : Finset (Fin k)) (p : Fin k × Fin k) : Finset (Fin k) :=
  if p.1 ≠ p.2 ∧ (p.1 ∈ Q ↔ p.2 ∈ Q) then {p.1, p.2} else ∅

theorem splitPairW_isComponent (Q : Finset (Fin k)) (p : Fin k × Fin k) :
    IsComponent (univEdgeHyper k) (splitPairW Q p) := by
  intro e
  rw [univEdgeHyper_edge, Finset.inter_univ]
  unfold splitPairW
  by_cases h : p.1 ≠ p.2 ∧ (p.1 ∈ Q ↔ p.2 ∈ Q)
  · rw [ite_eq_left h, Finset.card_pair h.1]
    exact ⟨1, rfl⟩
  · rw [ite_eq_right h, Finset.card_empty]
    exact ⟨0, rfl⟩

/-- `W` covers every vertex (the necessary condition pointed to by
`high_cosystolic_requires_cover` of §2). -/
theorem splitPairW_covers {Q : Finset (Fin k)} (hQ : 2 ≤ Q.card) (hQc : 2 ≤ (Qᶜ).card) :
    ∀ v : Fin k, ∃ p : Fin k × Fin k, v ∈ splitPairW Q p := by
  intro v
  have htwo : ∀ S : Finset (Fin k), 2 ≤ S.card → ∃ w ∈ S, w ≠ v := by
    intro S hS
    by_contra h
    push Not at h
    have hsub : S ⊆ ({v} : Finset (Fin k)) := fun w hw => by
      rw [Finset.mem_singleton]; exact h w hw
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    omega
  by_cases hv : v ∈ Q
  · obtain ⟨w, hw, hwv⟩ := htwo Q hQ
    refine ⟨(v, w), ?_⟩
    have hcond : (v, w).1 ≠ (v, w).2 ∧ ((v, w).1 ∈ Q ↔ (v, w).2 ∈ Q) :=
      ⟨hwv.symm, Iff.intro (fun _ => hw) (fun _ => hv)⟩
    rw [splitPairW, ite_eq_left hcond]
    exact Finset.mem_insert_self v {w}
  · obtain ⟨w, hw, hwv⟩ := htwo Qᶜ hQc
    have hw' : w ∉ Q := by rwa [Finset.mem_compl] at hw
    refine ⟨(v, w), ?_⟩
    have hcond : (v, w).1 ≠ (v, w).2 ∧ ((v, w).1 ∈ Q ↔ (v, w).2 ∈ Q) :=
      ⟨hwv.symm, Iff.intro (fun h => absurd h hv) (fun h => absurd h hw')⟩
    rw [splitPairW, ite_eq_left hcond]
    exact Finset.mem_insert_self v {w}

/-- **The characterization of $\ker\delta_2$**: the kernel of `splitPairW Q` is exactly the
vectors that are "constant on `Q` and constant on `Qᶜ`" — with **no** kernel element of weight
$2$ (exactly what the family of §3 cannot achieve). -/
theorem mulVec_surgeryD2_splitPairW_eq_zero_iff (Q : Finset (Fin k)) (u : Vec k) :
    surgeryD2 (splitPairW Q) *ᵥ u = 0
      ↔ (∀ x ∈ Q, ∀ y ∈ Q, u x = u y) ∧ (∀ x, x ∉ Q → ∀ y, y ∉ Q → u x = u y) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      by_cases hxy : x = y
      · rw [hxy]
      · have hcond : (x, y).1 ≠ (x, y).2 ∧ ((x, y).1 ∈ Q ↔ (x, y).2 ∈ Q) :=
          ⟨hxy, Iff.intro (fun _ => hy) (fun _ => hx)⟩
        have hp : splitPairW Q (x, y) = ({(x, y).1, (x, y).2} : Finset (Fin k)) :=
          ite_eq_left hcond
        have hz := congrFun h (x, y)
        rw [surgeryD2_mulVec_sum, hp, Finset.sum_pair (show (x, y).1 ≠ (x, y).2 from hxy),
          Pi.zero_apply] at hz
        exact (add_eq_zero_iff_eq _ _).mp hz
    · intro x hx y hy
      by_cases hxy : x = y
      · rw [hxy]
      · have hcond : (x, y).1 ≠ (x, y).2 ∧ ((x, y).1 ∈ Q ↔ (x, y).2 ∈ Q) :=
          ⟨hxy, Iff.intro (fun h => absurd h hx) (fun h => absurd h hy)⟩
        have hp : splitPairW Q (x, y) = ({(x, y).1, (x, y).2} : Finset (Fin k)) :=
          ite_eq_left hcond
        have hz := congrFun h (x, y)
        rw [surgeryD2_mulVec_sum, hp, Finset.sum_pair (show (x, y).1 ≠ (x, y).2 from hxy),
          Pi.zero_apply] at hz
        exact (add_eq_zero_iff_eq _ _).mp hz
  · intro h
    funext p
    rw [surgeryD2_mulVec_sum, Pi.zero_apply]
    unfold splitPairW
    by_cases hc : p.1 ≠ p.2 ∧ (p.1 ∈ Q ↔ p.2 ∈ Q)
    · rw [ite_eq_left hc, Finset.sum_pair hc.1]
      by_cases hp : p.1 ∈ Q
      · rw [h.1 p.1 hp p.2 (hc.2.mp hp), CharTwo.add_self_eq_zero]
      · rw [h.2 p.1 hp p.2 (fun h2 => hp (hc.2.mpr h2)), CharTwo.add_self_eq_zero]
    · rw [ite_eq_right hc, Finset.sum_empty]

/-- The constancy on the kernel gives an explicit form: `u` depends only on "whether or not it
is in `Q`". -/
theorem eq_smul_indVec_split {Q : Finset (Fin k)} {u : Vec k}
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, u x = u y) (hQc : ∀ x, x ∉ Q → ∀ y, y ∉ Q → u x = u y)
    {x₀ : Fin k} (hx₀ : x₀ ∈ Q) {y₀ : Fin k} (hy₀ : y₀ ∉ Q) :
    u = (u x₀) • indVec Q + (u y₀) • indVec (Qᶜ) := by
  funext v
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hv : v ∈ Q
  · have h1 : u v = u x₀ := hQ v hv x₀ hx₀
    have h2 : indVec Q v = 1 := by rw [indVec, ite_eq_left hv]
    have h3 : indVec (Qᶜ) v = 0 := by
      rw [indVec, ite_eq_right (by rw [Finset.mem_compl]; exact fun h => h hv)]
    rw [h1, h2, h3]
    ring
  · have h1 : u v = u y₀ := hQc v hv y₀ hy₀
    have h2 : indVec Q v = 0 := by rw [indVec, ite_eq_right hv]
    have h3 : indVec (Qᶜ) v = 1 := by
      rw [indVec, ite_eq_left (by rw [Finset.mem_compl]; exact hv)]
    rw [h1, h2, h3]
    ring

-- A local copy within this file: `Homology/PortFunction.lean` already has a public theorem of
-- the same name and shape, and its module is not on the import branch of this file. Lean does
-- accept two same-named declarations once both enter the closure of the root module (measured:
-- a full build with 0 errors), but that makes the `#print axioms` lines of the root module
-- ambiguous, and editing one of them silently shadows the other. So it is demoted to
-- `private` here, removing the ambiguity and the shadowing.
private theorem indVec_ne_zero_of_nonempty {S : Finset (Fin k)} (h : S.Nonempty) : indVec S ≠ 0 := by
  obtain ⟨v, hv⟩ := h
  intro h0
  have h1 : indVec S v = 1 := by rw [indVec, ite_eq_left hv]
  rw [h0, Pi.zero_apply] at h1
  exact one_ne_zero h1.symm

theorem indVec_ne_indVec_univ {S : Finset (Fin k)} (h : (Sᶜ).Nonempty) :
    indVec S ≠ indVec (Finset.univ : Finset (Fin k)) := by
  obtain ⟨v, hv⟩ := h
  have hv' : v ∉ S := by rwa [Finset.mem_compl] at hv
  intro h0
  have h1 : indVec S v = 0 := by rw [indVec, ite_eq_right hv']
  have h2 : indVec (Finset.univ : Finset (Fin k)) v = 1 := by
    rw [indVec, ite_eq_left (Finset.mem_univ v)]
  rw [h0, h2] at h1
  exact one_ne_zero h1

/-- The equivalence between `x ∉ Q` and `x ∈ Qᶜ` (a `¬¬` elimination, to avoid going back and
forth in `rw` lists). -/
theorem mem_compl_iff_notMem {Q : Finset (Fin k)} {x : Fin k} : x ∈ Qᶜ ↔ x ∉ Q :=
  Finset.mem_compl

theorem splitPairW_kernel (Q : Finset (Fin k)) {S : Finset (Fin k)}
    (hS : S = Q ∨ S = Qᶜ) : surgeryD2 (splitPairW Q) *ᵥ indVec S = 0 := by
  rw [mulVec_surgeryD2_splitPairW_eq_zero_iff]
  rcases hS with hSQ | hSQc
  · rw [hSQ]
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      have h1 : indVec Q x = 1 := by rw [indVec, ite_eq_left hx]
      have h2 : indVec Q y = 1 := by rw [indVec, ite_eq_left hy]
      rw [h1, h2]
    · intro x hx y hy
      have h1 : indVec Q x = 0 := by rw [indVec, ite_eq_right hx]
      have h2 : indVec Q y = 0 := by rw [indVec, ite_eq_right hy]
      rw [h1, h2]
  · rw [hSQc]
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      have hx' : x ∉ Qᶜ := fun hc => (mem_compl_iff_notMem.mp hc) hx
      have hy' : y ∉ Qᶜ := fun hc => (mem_compl_iff_notMem.mp hc) hy
      have h1 : indVec (Qᶜ) x = 0 := by rw [indVec, ite_eq_right hx']
      have h2 : indVec (Qᶜ) y = 0 := by rw [indVec, ite_eq_right hy']
      rw [h1, h2]
    · intro x hx y hy
      have h1 : indVec (Qᶜ) x = 1 := by rw [indVec, ite_eq_left (mem_compl_iff_notMem.mpr hx)]
      have h2 : indVec (Qᶜ) y = 1 := by rw [indVec, ite_eq_left (mem_compl_iff_notMem.mpr hy)]
      rw [h1, h2]

theorem splitPairW_notMem_image (Q : Finset (Fin k)) (hQne : Q.Nonempty)
    (hQcne : (Qᶜ).Nonempty) {S : Finset (Fin k)} (hS : S = Q ∨ S = Qᶜ) :
    ¬ ∃ f : Vec 1, surgeryD1 (univEdgeHyper k) *ᵥ f = indVec S := by
  intro hcon
  have h := (mem_image_univEdgeHyper k (indVec S)).mp hcon
  have hne0 : indVec S ≠ 0 := by
    rcases hS with hSQ | hSQc
    · rw [hSQ]; exact indVec_ne_zero_of_nonempty hQne
    · rw [hSQc]; exact indVec_ne_zero_of_nonempty hQcne
  have hne1 : indVec S ≠ indVec (Finset.univ : Finset (Fin k)) := by
    rcases hS with hSQ | hSQc
    · rw [hSQ]; exact indVec_ne_indVec_univ hQcne
    · rw [hSQc]; exact indVec_ne_indVec_univ (by simpa using hQne)
  exact h.elim hne0 hne1

/-- **The main theorem: the $1$-cosystolic distance on the full hypergraph = $\min(|Q|,|Q^c|)$**
(the upper bound from the two explicit witnesses `indVec Q` and `indVec Qᶜ`, the lower bound
from the constancy characterization of $\ker\delta_2$). -/
theorem cosystolicDistance_univEdge_splitPairW_eq {Q : Finset (Fin k)}
    (hQ : 2 ≤ Q.card) (hQc : 2 ≤ (Qᶜ).card) :
    cosystolicDistance (univEdgeHyper k) (splitPairW Q) = min Q.card (k - Q.card) := by
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hQcne : (Qᶜ).Nonempty := Finset.card_pos.mp (by omega)
  have hwit : ∀ S : Finset (Fin k), (S = Q ∨ S = Qᶜ) →
      IsCosystolic (univEdgeHyper k) (splitPairW Q) (indVec S) :=
    fun S hS => ⟨splitPairW_kernel Q hS, splitPairW_notMem_image Q hQne hQcne hS⟩
  refine le_antisymm ?_ ?_
  · have hleQ : cosystolicDistance (univEdgeHyper k) (splitPairW Q) ≤ Q.card :=
      csInf_le ⟨0, fun b _ => Nat.zero_le b⟩
        ⟨indVec Q, hwit Q (Or.inl rfl), hammingNorm_indVec Q⟩
    have hleQc : cosystolicDistance (univEdgeHyper k) (splitPairW Q) ≤ (Qᶜ).card :=
      csInf_le ⟨0, fun b _ => Nat.zero_le b⟩
        ⟨indVec (Qᶜ), hwit (Qᶜ) (Or.inr rfl), hammingNorm_indVec (Qᶜ)⟩
    rw [Finset.card_compl, Fintype.card_fin] at hleQc
    exact le_min hleQ hleQc
  · refine le_csInf ⟨Q.card, ⟨indVec Q, hwit Q (Or.inl rfl), hammingNorm_indVec Q⟩⟩ ?_
    rintro n ⟨u, hu, rfl⟩
    have hker := (mulVec_surgeryD2_splitPairW_eq_zero_iff Q u).mp hu.1
    obtain ⟨x₀, hx₀⟩ := hQne
    obtain ⟨y₀, hy₀c⟩ := hQcne
    have hy₀ : y₀ ∉ Q := by rwa [Finset.mem_compl] at hy₀c
    have hsplit : u = (u x₀) • indVec Q + (u y₀) • indVec (Qᶜ) :=
      eq_smul_indVec_split hker.1 hker.2 hx₀ hy₀
    by_cases hcx : u x₀ = 0
    · by_cases hcy : u y₀ = 0
      · rw [hcx, hcy, zero_smul, zero_smul, add_zero] at hsplit
        exact absurd hsplit (isCosystolic_ne_zero hu)
      · have hy1 : u y₀ = 1 := eq_one_of_ne_zero hcy
        rw [hcx, zero_smul, hy1, one_smul, zero_add] at hsplit
        rw [hsplit, hammingNorm_indVec, Finset.card_compl, Fintype.card_fin]
        exact min_le_right _ _
    · by_cases hcy : u y₀ = 0
      · have hx1 : u x₀ = 1 := eq_one_of_ne_zero hcx
        rw [hx1, one_smul, hcy, zero_smul, add_zero] at hsplit
        rw [hsplit, hammingNorm_indVec]
        exact min_le_left _ _
      · have hx1 : u x₀ = 1 := eq_one_of_ne_zero hcx
        have hy1 : u y₀ = 1 := eq_one_of_ne_zero hcy
        rw [hx1, hy1, one_smul, one_smul] at hsplit
        refine absurd ?_ hu.2
        rw [hsplit]
        refine ⟨fun _ => 1, ?_⟩
        rw [mulVec_surgeryD1_univEdgeHyper]
        funext v
        rw [one_smul, Pi.add_apply]
        by_cases hv : v ∈ Q
        · have h1 : indVec (Finset.univ : Finset (Fin k)) v = 1 := by
            rw [indVec, ite_eq_left (Finset.mem_univ v)]
          have h2 : indVec Q v = 1 := by rw [indVec, ite_eq_left hv]
          have h3 : indVec (Qᶜ) v = 0 :=
            by rw [indVec, ite_eq_right (fun hc => (mem_compl_iff_notMem.mp hc) hv)]
          rw [h1, h2, h3]
          ring
        · have h1 : indVec (Finset.univ : Finset (Fin k)) v = 1 := by
            rw [indVec, ite_eq_left (Finset.mem_univ v)]
          have h2 : indVec Q v = 0 := by rw [indVec, ite_eq_right hv]
          have h3 : indVec (Qᶜ) v = 1 := by rw [indVec, ite_eq_left (mem_compl_iff_notMem.mpr hv)]
          rw [h1, h2, h3]
          ring

/-- The family with `Q` taken as the first half: $d_1^\bullet=d$, for arbitrary $d$ —
**unbounded**. -/
def halfSet (d : ℕ) : Finset (Fin (2 * d)) :=
  (Finset.univ : Finset (Fin d)).map (Fin.castLEEmb (by omega))

theorem halfSet_card (d : ℕ) : (halfSet d).card = d := by
  rw [halfSet, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem cosystolicDistance_univEdge_splitPairW_half {d : ℕ} (hd : 2 ≤ d) :
    cosystolicDistance (univEdgeHyper (2 * d)) (splitPairW (halfSet d)) = d := by
  rw [cosystolicDistance_univEdge_splitPairW_eq
    (by rw [halfSet_card]; omega)
    (by rw [Finset.card_compl, halfSet_card, Fintype.card_fin]; omega), halfSet_card]
  have h : 2 * d - d = d := by omega
  rw [h, min_self]

/-- **A family with connected incidence graph and unbounded $d_1^\bullet$**: for every `d`
there is an auxiliary hypergraph $H=(V,E)$ and a family $W$ of components of size $O(1)$ such
that the incidence graph of $H$ is connected, every hyperedge has even cardinality, $W$ covers
$V$, and $d \le d_1^\bullet$. -/
theorem exists_incidenceConnected_cosystolicDistance_ge (d : ℕ) :
    ∃ (k : ℕ) (H : AuxHypergraph k 1) (W : Fin k × Fin k → Finset (Fin k)),
      IncidenceConnected H ∧ IsEvenHyper H ∧ (∀ p, IsComponent H (W p)) ∧
        (∀ v, ∃ p, v ∈ W p) ∧ d ≤ cosystolicDistance H W := by
  refine ⟨2 * (d + 2), univEdgeHyper (2 * (d + 2)), splitPairW (halfSet (d + 2)),
    univEdgeHyper_incidenceConnected _, univEdgeHyper_isEven ⟨d + 2, by ring⟩,
    fun p => splitPairW_isComponent _ p,
    splitPairW_covers (by rw [halfSet_card]; omega)
      (by rw [Finset.card_compl, halfSet_card, Fintype.card_fin]; omega), ?_⟩
  rw [cosystolicDistance_univEdge_splitPairW_half (d := d + 2) (by omega)]
  omega

end QECCertificates.Homology
