/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.Gauging

open QECCertificates

/-!
# The auxiliary-structure layer of hypergraph surgery (homomorphic measurement)

Item 8 of §2 of the proposal ("Quantifiable targets") asks that **homomorphic
measurement** — the class of "homomorphic" logical measurements that the guideline names,
that is, surgery whose auxiliary structure is given by a hypergraph rather than a graph, in
the $O(d)$-round formulation of [14] — be brought into the same reduce/solve/verify chain,
and notes that *gauging is the special case whose subcode has distance 1* ([14] §6.2). This
module supplies the **representation layer** of that item: it generalises the auxiliary
structure from a "graph" to an **auxiliary hypergraph**, and machine-checks its relation to
the construction already in `Codes/Gauging.lean`.

## 1. The formulation of [14] (the source of this module's definitions)

[14] (Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895), §1.2 and §6.2:

* §1.2: the auxiliary system is specified by a **hypergraph** $H = (V, E)$, with which is
  associated a four-term cochain complex $F_2 W \to F_2 V \to F_2 E \to F_2 C$, where $W$
  is a set of **components** — "a collection of vertices which intersect every hyperedge on
  an **even** number of vertices".
* The sentence immediately following in §1.2 (this module turns it into a theorem in §2):
  "Note that when $H$ is a simple connected graph (i.e., every hyperedge is a regular edge),
  the only component is the set of all vertices $V$."
* A sentence after Theorem 6.5 in §6.2: **"Gauging logical measurement [56] can be seen as
  an instance of hypergraph surgery where the subcode $A_\bullet$ has distance 1, and
  therefore requires $O(d)$ rounds of syndrome measurement to maintain fault-distance
  $d$."** — note that the source says **the subcode has distance 1** (as against the
  "distance-$d$ subcode" of block reading, see the opening of §6, "conventional LDPC code
  surgery, which uses a distance 1 subcode"), not that "the auxiliary hypergraph degenerates
  to a graph". This module therefore places the machine-checkable part on the
  **auxiliary-structure** side (§4 below explains why it stays on that side only; the
  subcode layer is in `Homology/SubcodeLayer.lean`).

## 2. Components and parity (the machine form of the §1.2 sentence)

`IsComponent H S`: the vertex set `S` meets every hyperedge in an even number of vertices —
this is the definition of [14], and within its four-term complex it is equivalent to "$S$ is
sent to zero by the incidence map" (this module does not reproduce that complex, so it is
not written as $S \in \ker \delta_i$, to avoid misattribution).

* `component_univ_iff_even`: **the whole vertex set `V` is a component ⟺ every hyperedge
  has even cardinality**;
* `component_univ_of_graph`: for a 2-regular hypergraph (that is, a "graph") `V` is
  necessarily a component — the §1.2 sentence of [14];
* `not_component_univ_of_odd`: a single hyperedge of odd cardinality makes `V` fail to be a
  component — parity is **necessary and sufficient**, not merely sufficient.

## 3. The Gauss-law product = the vertex-operator product (the W–Y lifting, generalised)

`starOp H v = X_v · ∏_{e ∋ v} X_e` (the star of the vertex $v$) is the Gauss law of [14].
`Codes/Gauging.lean` already proves the lifting identity $L = \prod_v A_v = \prod_v X_v$ on a
**graph** (`gauss_prod_eq_vertex_prod`). This module generalises it and **characterises** it:

* `starOp_sum_apply_inr`: the component of $\bigl(\sum_v A_v\bigr)$ on the auxiliary bit $e$
  is exactly $|e| \bmod 2$ (the hyperedge cardinality);
* `starOp_sum_eq_vertexOp_sum_iff`: **$\sum_v A_v = \sum_v X_v$ ⟺ every hyperedge has even
  cardinality**. Thus "the lifting identity holds" and "$V$ is a component" are the same
  statement, and parity is necessary and sufficient;
* `starOp_sum_eq_vertexOp_sum`: on an even hypergraph $\sum_v A_v = \sum_v X_v$ — the
  generalisation of the existing `gauss_prod_eq_vertex_prod` to an **arbitrary even
  hypergraph**;
* `starOp_sum_apply_inr_eq_one_of_odd`: with a single hyperedge of odd cardinality the
  auxiliary component becomes $1$ — the identity **fails**. (This is why [14] introduces
  the $W$ components and the four-term complex rather than the three-term graph complex.)

## 4. The 2-regular case recovers the existing gauging construction (reduction)

* `graphOf_card_two` / `graphOf_isEven`: a hypergraph given by a self-loop-free endpoint
  function is 2-regular, hence even;
* `starOp_graphOf`: **the Gauss law of the hypergraph equals, entry by entry, the `gaussOp`
  of `Gauging.lean`** — a bridge between two **independently written** definitions (the
  hyperedge is a `Finset`, `gaussOp` uses endpoint pairs), whose proof must get through the
  `Finset` membership fact "$v \in \{(a,b).1, (a,b).2\} \iff a = v \vee b = v$";
* `gaussLawMat` / `gaussLawMat_graphOf`: the **check matrix** of the auxiliary structure
  (rows = Gauss laws, columns = vertex bits and auxiliary bits);
* `graphOf_ancCol_card`: in the 2-regular case each auxiliary column has exactly **2**
  nonzero entries — the check matrix is the incidence matrix of a graph, which is the
  machine criterion for "the auxiliary structure degenerates to a graph";
* `gauss_prod_eq_vertex_prod_of_hypergraph`: a theorem whose statement is **word-for-word**
  `Gauging.gauss_prod_eq_vertex_prod`, but derived through the hypergraph theorem — that is,
  the existing theorem is the main theorem evaluated in the 2-regular case;
* `starOp_linearIndependent`: the $k$ Gauss laws are always linearly independent (the vertex
  block is the identity matrix), independently of the hyperedge structure;
* `hypergraphSurgery_k`: the operator lifted to a stabilizer (the component of the product
  of the Gauss laws on the vertex bits, `promotedOp`) is **independent of the auxiliary
  hypergraph** (`promotedOp_eq_allOnes`), so `deformX_k` applies verbatim and the number of
  logical qubits drops by exactly one — the same conclusion as for gauging.

## 5. The timelike component is independent of the auxiliary structure

The protocol layer of `MeasurementProtocol.lean` computes the timelike component as
"the number of rounds $\times$ the depth of one round". This module gives the timelike chain
of the hypergraph surgery protocol (bits indexed by "Gauss-law index $\times$ round", the
checks being the comparison of the same law across adjacent rounds):

* `timeFault_const`: orthogonality to every timelike check ⟹ each Gauss law is constant
  along the time axis (directly reusing `Gauging.timeLike_eq_of_repCheck` — each
  column is **sliced** and the family-level theorem is then applied);
* `timeFault_weight_ge` / `timeWit_*`: nonzero ⟹ at least one law has a nonzero
  time axis ⟹ weight $\ge$ the number of rounds; and "set the whole time axis of one
  law to one" gives exactly the attainable witness of weight $=$ the number of rounds;
* `timeComponent_aux_independent`: for **any** auxiliary hypergraph `H` (a 2-regular graph
  or a proper hypergraph) the minimal undetectable timelike weight is `S + 1` — `H` enters
  the **definition** of the timelike chain (the Gauss-law index comes from the vertex set)
  yet does not appear in the **conclusion**. This is the machine-side basis for "the two
  families fit into the same chain": changing the auxiliary structure does not change the
  timelike component.

## 6. Honest boundaries (the paper cites this section)

**Formalized**: (i) the definition of the auxiliary hypergraph, the component predicate and
the parity characterisation; (ii) the Gauss laws and the product identity on an **arbitrary
even hypergraph**, together with its **necessity and sufficiency**; (iii) the recovery, entry
by entry in the 2-regular case, of the existing construction of `Gauging.lean` (equal Gauss
laws, the check matrix being the incidence matrix of a graph, the same dimension law);
(iv) the timelike component depends only on the number of rounds, independently of the
auxiliary graph or hypergraph.

**Not formalized** (beyond this module's scope; **no claim** is made):

1. **The spacelike fault distance of [14]**. The main theorems of the paper (Thm 5.3 / 6.5)
   need the deformed code and the compacted code to have distance $\ge d$, a sufficient
   condition for which is the **modular expansion** of §7 and the $1$-**cosystolic distance**
   (1-cosystolic distance $d_1 = \min\{|u| : u \in \ker \delta_2 \setminus
   \mathrm{im}\,\delta_1\}$, as the source has it; this module does **not** reproduce that
   complex, see item 1). The `IsComponent` this module provides is the **underlying object**
   of the 1-cosystolic chain (the coordinatewise form of $\ker \delta_0$), but it does
   **not** define the four-term complex, $\delta_1$ or the quotient, and it proves no
   distance bound. The "distance" of the auxiliary structure (the 1-cosystolic distance) and
   the code distances already in this library are **two different quantities**, and mixing
   them leads to errors.
2. **The "subcode has distance 1" half**. The §6.2 sentence of [14] says the **subcode
   $A_\bullet$ of gauging has distance 1**, not that "the auxiliary hypergraph degenerates
   to a graph". **This module** does not contain the subcode layer (the spacelike component
   of `Codes/Gauging.lean` is the `deformX` that lifts a logical operator to a stabilizer),
   so that item is not machine-checked here; what this module does is **one machine-checkable
   necessary-condition side** of it: when the auxiliary structure falls back to 2-regular
   (a graph), the Gauss laws, the check matrix and the dimension law coincide entry by entry
   with the existing gauging construction. (The subcode layer is in
   `Homology/SubcodeLayer.lean` — it reads "subcode" as an actual CSS code object and
   machine-checks the §6.2 sentence; the chain map and the degree shift are in
   `Homology/SubcodeChainMap.lean`.)
3. **The full $O(d)$-round surgery construction for hyperedges of size $> 2$**. For a proper
   hypergraph this module proves only two things: that "the product of the Gauss laws still
   satisfies a lifting identity" (even hyperedges) and that "the timelike component is
   unchanged"; the expansion, thickening, generalized flux and scheduling of §7 of [14] are
   not done. For a hyperedge of odd cardinality the identity **fails**
   (`starOp_sum_apply_inr_eq_one_of_odd`), which is exactly where the $W$ components are
   needed, and this module does **not** supply $W$.

**Trust base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axioms; the `#print axioms` of the load-bearing theorems is in the root module
`QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open scoped BigOperators

/-! ## 1. The auxiliary hypergraph -/

/-- **The auxiliary hypergraph**: `k` vertices and `m` hyperedges. A hyperedge is given as a
vertex set, and its cardinality **may differ from $2$** — which is exactly what makes
hypergraph surgery more general than gauging (the auxiliary structure of gauging is a graph,
whose hyperedges are all 2-element).

The qubit indexing convention agrees with `Codes/Gauging.lean`: `Sum.inl v` = vertex bit,
`Sum.inr e` = hyperedge auxiliary bit. -/
structure AuxHypergraph (k m : ℕ) where
  /-- The vertex set of the `e`th hyperedge. -/
  edge : Fin m → Finset (Fin k)

/-- **An even hypergraph**: every hyperedge has even cardinality. A 2-regular hypergraph
(a graph) is the smallest case. -/
def IsEvenHyper {k m : ℕ} (H : AuxHypergraph k m) : Prop := ∀ e, Even (H.edge e).card

/-- **A 2-regular hypergraph**: every hyperedge contains exactly 2 vertices, which is the
"graph" of [14]. -/
def IsGraphHyper {k m : ℕ} (H : AuxHypergraph k m) : Prop := ∀ e, (H.edge e).card = 2

/-- The 2-regular hypergraph given by an endpoint function (a hyperedge = an endpoint pair). -/
def graphOf {k m : ℕ} (ends : Fin m → Fin k × Fin k) : AuxHypergraph k m where
  edge e := {(ends e).1, (ends e).2}

/-- **A component** ([14] §1.2): a vertex set meeting every hyperedge in an even number of
vertices — the coordinatewise form of "$S$ is sent to zero by the incidence map". -/
def IsComponent {k m : ℕ} (H : AuxHypergraph k m) (S : Finset (Fin k)) : Prop :=
  ∀ e, Even ((S ∩ H.edge e).card)

/-- **The whole vertex set is a component ⟺ every hyperedge has even cardinality** — the
necessary-and-sufficient form of the parity condition of [14] §1.2. -/
theorem component_univ_iff_even {k m : ℕ} (H : AuxHypergraph k m) :
    IsComponent H Finset.univ ↔ IsEvenHyper H := by
  constructor
  · intro h e
    have he := h e
    rwa [Finset.univ_inter] at he
  · intro h e
    rw [Finset.univ_inter]
    exact h e

/-- On a 2-regular hypergraph (a graph) the whole vertex set is a component — the
machine-checkable half of the §1.2 sentence of [14], "when H is a simple connected graph,
the only component is the set of all vertices V". -/
theorem component_univ_of_graph {k m : ℕ} {H : AuxHypergraph k m} (h : IsGraphHyper H) :
    IsComponent H Finset.univ := by
  rw [component_univ_iff_even]
  intro e
  rw [h e]
  exact ⟨1, rfl⟩

/-- A single hyperedge of odd cardinality makes the whole vertex set **fail** to be a
component — so parity is necessary and sufficient, not merely sufficient. -/
theorem not_component_univ_of_odd {k m : ℕ} {H : AuxHypergraph k m}
    (h : ∃ e, Odd (H.edge e).card) : ¬ IsComponent H Finset.univ := by
  intro hc
  obtain ⟨e, he⟩ := h
  exact Nat.not_even_iff_odd.mpr he ((component_univ_iff_even H).mp hc e)

/-- The hyperedge given by an endpoint pair. -/
theorem graphOf_edge {k m : ℕ} (ends : Fin m → Fin k × Fin k) (e : Fin m) :
    (graphOf ends).edge e = {(ends e).1, (ends e).2} := rfl

/-- Without self-loops an endpoint pair is exactly a 2-element set: `graphOf` is 2-regular. -/
theorem graphOf_card_two {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (e : Fin m) :
    ((graphOf ends).edge e).card = 2 := by
  rw [graphOf_edge]
  exact Finset.card_pair (hloop e)

/-- `graphOf` is an even hypergraph (2 is even). -/
theorem graphOf_isEven {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) : IsEvenHyper (graphOf ends) := by
  intro e
  rw [graphOf_card_two ends hloop e]
  exact ⟨1, rfl⟩

/-! ## 2. The Gauss laws (star operators) -/

/-- The auxiliary-bit operator `X_e` (acting only on the `e`th hyperedge). -/
def ancOp {k m : ℕ} (e : Fin m) : (Fin k ⊕ Fin m) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun e' => if e' = e then 1 else 0)

@[simp] theorem ancOp_apply_inl {k m : ℕ} (e : Fin m) (w : Fin k) :
    ancOp (k := k) e (Sum.inl w) = 0 := rfl

@[simp] theorem ancOp_apply_inr {k m : ℕ} (e e' : Fin m) :
    ancOp (k := k) e (Sum.inr e') = if e' = e then 1 else 0 := rfl

@[simp] theorem vertexOp_apply_inl {k m : ℕ} (v w : Fin k) :
    vertexOp (k := k) (m := m) v (Sum.inl w) = if w = v then 1 else 0 := rfl

@[simp] theorem vertexOp_apply_inr {k m : ℕ} (v : Fin k) (e : Fin m) :
    vertexOp (k := k) (m := m) v (Sum.inr e) = 0 := rfl

/-- **The Gauss law (star operator)**: $A_v = X_v \cdot \prod_{e \ni v} X_e$ — the star of
the vertex `v`, acting on the vertex bit $v$ and on the auxiliary bits of all hyperedges
containing $v$. -/
def starOp {k m : ℕ} (H : AuxHypergraph k m) (v : Fin k) : (Fin k ⊕ Fin m) → ZMod 2 :=
  vertexOp v + ∑ e : Fin m, if v ∈ H.edge e then ancOp e else 0

/-- The component of a Gauss law on a vertex bit: `A_v` takes `[w = v]` at `Sum.inl w`. -/
theorem starOp_apply_inl {k m : ℕ} (H : AuxHypergraph k m) (v w : Fin k) :
    starOp H v (Sum.inl w) = if w = v then 1 else 0 := by
  have hsum : (∑ e : Fin m, (if v ∈ H.edge e then ancOp e else 0) :
      (Fin k ⊕ Fin m) → ZMod 2) (Sum.inl w) = 0 := by
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases hv : v ∈ H.edge e
    · rw [ite_eq_left hv]
      rfl
    · rw [ite_eq_right hv]
      rfl
  rw [starOp, Pi.add_apply, hsum, add_zero]
  rfl

/-- The component of a Gauss law on an auxiliary bit: `A_v` takes `[v ∈ e]` at `Sum.inr e`. -/
theorem starOp_apply_inr {k m : ℕ} (H : AuxHypergraph k m) (v : Fin k) (e : Fin m) :
    starOp H v (Sum.inr e) = if v ∈ H.edge e then 1 else 0 := by
  have hv : vertexOp (k := k) (m := m) v (Sum.inr e) = 0 := rfl
  have hsum : (∑ e' : Fin m, (if v ∈ H.edge e' then ancOp (k := k) e' else 0)) (Sum.inr e)
      = if v ∈ H.edge e then 1 else 0 := by
    rw [Finset.sum_apply]
    have hsingle := Finset.sum_eq_single (s := Finset.univ)
      (f := fun e' : Fin m =>
        (if v ∈ H.edge e' then ancOp (k := k) e' else 0) (Sum.inr e)) e
      (fun b _ hb => by
        by_cases hvb : v ∈ H.edge b
        · rw [ite_eq_left hvb, ancOp_apply_inr (k := k) b e]
          rw [ite_eq_right (fun h : e = b => hb h.symm)]
        · rw [ite_eq_right hvb]
          rfl)
      (fun hnot => absurd (Finset.mem_univ e) hnot)
    rw [hsingle]
    by_cases hve : v ∈ H.edge e
    · rw [ite_eq_left hve, ancOp_apply_inr (k := k) e e, ite_eq_left rfl, ite_eq_left hve]
    · rw [ite_eq_right hve, ite_eq_right hve]
      simp only [Pi.zero_apply]
  rw [starOp, Pi.add_apply, hv, zero_add]
  exact hsum

/-! ## 3. The Gauss-law product: the W–Y lifting, generalised, and its necessity -/

/-- **The engine of the main theorem**: the component of the product of the Gauss laws on
the auxiliary bit `e` is exactly the hyperedge cardinality $|e| \bmod 2$.

Thus "the auxiliary component vanishes" and "the hyperedge has even cardinality" are the
same statement. -/
theorem starOp_sum_apply_inr {k m : ℕ} (H : AuxHypergraph k m) (e : Fin m) :
    (∑ v : Fin k, starOp H v) (Sum.inr e) = ((H.edge e).card : ZMod 2) := by
  rw [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun v _ => starOp_apply_inr H v e]
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The component of the product of the Gauss laws on a vertex bit is always 1 (the vertex
block is the row sum of the identity matrix). -/
theorem starOp_sum_apply_inl {k m : ℕ} (H : AuxHypergraph k m) (w : Fin k) :
    (∑ v : Fin k, starOp H v) (Sum.inl w) = 1 := by
  rw [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun v _ => starOp_apply_inl H v w]
  rw [Finset.sum_eq_single w]
  · rw [ite_eq_left rfl]
  · intro b _ hb
    rw [ite_eq_right (fun h : w = b => hb h.symm)]
  · intro hnot
    exact absurd (Finset.mem_univ w) hnot

/-- **The W–Y lifting, generalised**: on an even hypergraph the product of the Gauss laws =
the product of the vertex operators (`Codes/Gauging.lean`'s `gauss_prod_eq_vertex_prod` on
an arbitrary even hypergraph). -/
theorem starOp_sum_eq_vertexOp_sum {k m : ℕ} (H : AuxHypergraph k m) (hH : IsEvenHyper H) :
    (∑ v : Fin k, starOp H v) = ∑ v : Fin k, vertexOp (k := k) (m := m) v := by
  funext q
  rcases q with w | e
  · rw [starOp_sum_apply_inl, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun v _ => vertexOp_apply_inl v w]
    rw [Finset.sum_eq_single w]
    · rw [ite_eq_left rfl]
    · intro b _ hb
      rw [ite_eq_right (fun h : w = b => hb h.symm)]
    · intro hnot
      exact absurd (Finset.mem_univ w) hnot
  · rw [starOp_sum_apply_inr, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun v _ => vertexOp_apply_inr v e]
    rw [Finset.sum_const_zero]
    obtain ⟨t, ht⟩ := hH e
    rw [ht, Nat.cast_add]
    exact CharTwo.add_self_eq_zero (t : ZMod 2)

/-- With a single hyperedge of odd cardinality the auxiliary component of the product of
the Gauss laws becomes $1$ — the identity **fails**. This is exactly why [14] introduces
the $W$ components and the four-term complex rather than the three-term graph complex. -/
theorem starOp_sum_apply_inr_eq_one_of_odd {k m : ℕ} (H : AuxHypergraph k m) (e : Fin m)
    (he : Odd (H.edge e).card) : (∑ v : Fin k, starOp H v) (Sum.inr e) = 1 := by
  rw [starOp_sum_apply_inr]
  obtain ⟨t, ht⟩ := he
  rw [ht, Nat.cast_add, Nat.cast_mul]
  have htwo : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul, zero_add, Nat.cast_one]

/-- **The necessary and sufficient condition for the lifting identity**: $\sum_v A_v =
\sum_v X_v$ ⟺ every hyperedge has even cardinality. ("$\Leftarrow$" is
`starOp_sum_eq_vertexOp_sum`; "$\Rightarrow$" is a counterexample from an odd hyperedge.) -/
theorem starOp_sum_eq_vertexOp_sum_iff {k m : ℕ} (H : AuxHypergraph k m) :
    (∑ v : Fin k, starOp H v) = ∑ v : Fin k, vertexOp (k := k) (m := m) v
      ↔ IsEvenHyper H := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨e, he⟩ := not_forall.mp hne
    have hodd : Odd (H.edge e).card := Nat.not_even_iff_odd.mp he
    have h1 := starOp_sum_apply_inr_eq_one_of_odd H e hodd
    have h2 : (∑ v : Fin k, vertexOp (k := k) (m := m) v) (Sum.inr e) = 0 := by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun v _ => vertexOp_apply_inr v e
    have hcong := congrFun h (Sum.inr e)
    rw [h1, h2] at hcong
    exact one_ne_zero hcong
  · exact starOp_sum_eq_vertexOp_sum H

/-! ## 4. The 2-regular case recovers the existing gauging construction -/

/-- **The reduction bridge**: the Gauss law of the hypergraph equals, entry by entry, the
`gaussOp` of `Codes/Gauging.lean`.

The two definitions are **independently** written (the hyperedge is a `Finset`, `gaussOp`
uses endpoint pairs), and the equality must get through the membership fact
"$v \in \{(a,b).1,(a,b).2\} \iff a = v \vee b = v$". -/
theorem starOp_graphOf {k m : ℕ} (ends : Fin m → Fin k × Fin k) (v : Fin k) :
    starOp (graphOf ends) v = gaussOp ends v := by
  have hiff : ∀ e : Fin m,
      (v ∈ (graphOf ends).edge e) ↔ ((ends e).1 = v ∨ (ends e).2 = v) := by
    intro e
    rw [graphOf_edge, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  funext q
  rcases q with w | e
  · rw [starOp_apply_inl]
    rfl
  · have hg : gaussOp ends v (Sum.inr e)
        = (if (ends e).1 = v ∨ (ends e).2 = v then 1 else 0) := rfl
    rw [starOp_apply_inr, hg]
    by_cases hv : v ∈ (graphOf ends).edge e
    · rw [ite_eq_left hv, ite_eq_left ((hiff e).mp hv)]
    · rw [ite_eq_right hv, ite_eq_right (fun h => hv ((hiff e).mpr h))]

/-- **The check matrix of the auxiliary structure**: rows = Gauss laws (vertices),
columns = vertex bits and hyperedge auxiliary bits. -/
def gaussLawMat {k m : ℕ} (H : AuxHypergraph k m) : Matrix (Fin k) (Fin k ⊕ Fin m) (ZMod 2) :=
  fun v q => starOp H v q

/-- In the 2-regular case the check matrix equals the existing `gaussOp` row by row. -/
theorem gaussLawMat_graphOf {k m : ℕ} (ends : Fin m → Fin k × Fin k) (v : Fin k) :
    gaussLawMat (graphOf ends) v = gaussOp ends v :=
  starOp_graphOf ends v

/-- **In the 2-regular case the check matrix is the incidence matrix of a graph**: every
auxiliary column has exactly 2 nonzero entries.

This is the machine criterion for "the auxiliary structure degenerates to a graph" (the
construction of `Codes/Gauging.lean` is exactly this case). -/
theorem graphOf_ancCol_card {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (e : Fin m) :
    (Finset.univ.filter (fun v : Fin k => gaussLawMat (graphOf ends) v (Sum.inr e) = 1)).card = 2 := by
  have hiff : ∀ v : Fin k,
      (v ∈ (graphOf ends).edge e) ↔ (v = (ends e).1 ∨ v = (ends e).2) := by
    intro v
    rw [graphOf_edge, Finset.mem_insert, Finset.mem_singleton]
  have hval : ∀ v : Fin k, gaussLawMat (graphOf ends) v (Sum.inr e)
      = (if v ∈ (graphOf ends).edge e then 1 else 0) :=
    fun v => starOp_apply_inr (graphOf ends) v e
  have hset : (Finset.univ.filter
        (fun v : Fin k => gaussLawMat (graphOf ends) v (Sum.inr e) = 1))
      = {(ends e).1, (ends e).2} := by
    ext v
    rw [Finset.mem_filter, hval v, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hp⟩
      by_contra h
      have hnot : ¬(v ∈ (graphOf ends).edge e) := fun hc => h ((hiff v).mp hc)
      rw [ite_eq_right hnot] at hp
      exact one_ne_zero hp.symm
    · rintro (h | h)
      · exact ⟨Finset.mem_univ _, ite_eq_left ((hiff v).mpr (Or.inl h))⟩
      · exact ⟨Finset.mem_univ _, ite_eq_left ((hiff v).mpr (Or.inr h))⟩
  rw [hset, Finset.card_pair (hloop e)]

/-- **The existing theorem is the main theorem evaluated in the 2-regular case**: a theorem
whose statement is word-for-word `Gauging.gauss_prod_eq_vertex_prod`, but derived through
the hypergraph theorem `starOp_sum_eq_vertexOp_sum`.

This is the machine evidence for "hypergraph surgery, restricted to a 2-regular hypergraph
= the existing gauging construction". -/
theorem gauss_prod_eq_vertex_prod_of_hypergraph {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) :
    (∑ v : Fin k, gaussOp ends v) = ∑ v : Fin k, vertexOp (k := k) (m := m) v := by
  have h := starOp_sum_eq_vertexOp_sum (graphOf ends) (graphOf_isEven ends hloop)
  rwa [Finset.sum_congr rfl fun v _ => starOp_graphOf ends v] at h

/-- **The $k$ Gauss laws are always linearly independent** (the vertex block is the
identity matrix), independently of the hyperedge structure. -/
theorem starOp_linearIndependent {k m : ℕ} (H : AuxHypergraph k m) :
    LinearIndependent (ZMod 2) (fun v : Fin k => starOp H v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrFun hg (Sum.inl v)
  rw [Finset.sum_apply] at hv
  have hcong : (∑ w : Fin k, (g w • starOp H w) (Sum.inl v))
      = ∑ w : Fin k, g w • (if v = w then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Pi.smul_apply, starOp_apply_inl]
  rw [hcong] at hv
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun w : Fin k => g w • (if v = w then (1 : ZMod 2) else 0)) v
    (fun b _ hb => by rw [ite_eq_right (fun h : v = b => hb h.symm), smul_zero])
    (fun hnot => absurd (Finset.mem_univ v) hnot)
  rw [hsingle, ite_eq_left rfl, smul_eq_mul, mul_one] at hv
  simpa using hv

/-! ### The dimension law: the promoted operator is independent of the auxiliary structure -/

/-- The all-ones vector: the operator lifted to a stabilizer (all-ones support on the
vertex bits). -/
def allOnes (k : ℕ) : Vec k := fun _ => 1

/-- **The operator promoted by hypergraph surgery**: the component of the product of the
Gauss laws on the vertex bits — the operator that is repeatedly measured. -/
def promotedOp {k m : ℕ} (H : AuxHypergraph k m) : Vec k :=
  fun w => (∑ v : Fin k, starOp H v) (Sum.inl w)

/-- The promoted operator is **independent of the auxiliary hypergraph**: whether a
2-regular graph or a proper hypergraph, it is the all-ones operator on the vertices. -/
theorem promotedOp_eq_allOnes {k m : ℕ} (H : AuxHypergraph k m) :
    promotedOp H = allOnes k := by
  funext w
  rw [promotedOp, starOp_sum_apply_inl]
  rfl

/-- Any two auxiliary hypergraphs (2-regular graph / proper hypergraph, even with
different hyperedge sets and sizes) promote **the same** operator. -/
theorem promotedOp_aux_independent {k m₁ m₂ : ℕ} (H₁ : AuxHypergraph k m₁)
    (H₂ : AuxHypergraph k m₂) : promotedOp H₁ = promotedOp H₂ := by
  rw [promotedOp_eq_allOnes, promotedOp_eq_allOnes]

/-- On an even hypergraph the product of the Gauss laws **does not touch the auxiliary
bits at all** (the auxiliary component is always zero). -/
theorem liftedOp_anc_eq_zero {k m : ℕ} (H : AuxHypergraph k m) (hH : IsEvenHyper H) (e : Fin m) :
    (∑ v : Fin k, starOp H v) (Sum.inr e) = 0 := by
  rw [starOp_sum_apply_inr]
  obtain ⟨t, ht⟩ := hH e
  rw [ht, Nat.cast_add]
  exact CharTwo.add_self_eq_zero (t : ZMod 2)

/-- **The dimension law of hypergraph surgery (the same conclusion as `deformX_k` for
gauging)**: lifting the promoted operator of `H` to a stabilizer drops the number of
logical qubits by exactly one.

Since the promoted operator is independent of the auxiliary hypergraph
(`promotedOp_eq_allOnes`), this holds for **any** even hypergraph (including a 2-regular
graph), and the proof is just the existing `deformX_k` — the hypergraph side introduces no
new distance cost. -/
theorem hypergraphSurgery_k {k m : ℕ} (H : AuxHypergraph k m) (Hx Lz : List (Vec k))
    (h : promotedOp H ∉ spanL Hx) :
    k - (rowReduce (Hx ++ [promotedOp H])).length - (rowReduce Lz).length
      = (k - (rowReduce Hx).length - (rowReduce Lz).length) - 1 := by
  rw [promotedOp_eq_allOnes] at h ⊢
  exact deformX_k (n := k) h

/-! ## 5. The timelike component is independent of the auxiliary structure -/

/-- The bit index of the timelike chain of the protocol: `(Gauss-law index, round)`. -/
abbrev TimeFault (k S : ℕ) := Fin k × Fin (S + 1) → ZMod 2

/-- **The timelike check of the protocol**: the comparison of the same Gauss law across two
adjacent rounds.

The Gauss-law index comes from the vertex set of the auxiliary hypergraph `H`, so `H` enters
the **definition** of this chain; but `H.edge` (which law acts on which auxiliary bits) does
**not** — the auxiliary hypergraph changes only the **content** of each law, not **which
laws are repeatedly measured**. This is the structural reason the two families fit into the
same chain. -/
def protocolTimeCheck {k m : ℕ} (_H : AuxHypergraph k m) (S : ℕ) (v : Fin k) (i : Fin S) :
    TimeFault k S → ZMod 2 :=
  fun x => x (v, Fin.castSucc i) + x (v, i.succ)

/-- **A timelike fault pattern**: orthogonal to every timelike check (each Gauss law reads
the same in adjacent rounds). -/
def IsTimeLikeFault {k m : ℕ} (H : AuxHypergraph k m) (S : ℕ) (x : TimeFault k S) : Prop :=
  ∀ (v : Fin k) (i : Fin S), protocolTimeCheck H S v i x = 0

/-- **Each Gauss law is constant along the time axis** — each column is **sliced** and then
the existing family-level theorem `timeLike_eq_of_repCheck` of `Codes/Gauging.lean` is
applied directly. -/
theorem timeFault_const {k m S : ℕ} {H : AuxHypergraph k m} {x : TimeFault k S}
    (hf : IsTimeLikeFault H S x) (v : Fin k) :
    ∀ i j : Fin (S + 1), x (v, i) = x (v, j) := by
  have hslice : ∀ i : Fin S, repCheck S i ⬝ᵥ (fun t : Fin (S + 1) => x (v, t)) = 0 := by
    intro i
    rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot]
    exact hf v i
  exact timeLike_eq_of_repCheck hslice

/-- **A lower bound on the timelike component**: a nonzero timelike fault has at least one
Gauss law whose time axis is entirely nonzero, so its weight is at least the number of
rounds. -/
theorem timeFault_weight_ge {k m S : ℕ} {H : AuxHypergraph k m} {x : TimeFault k S}
    (hf : IsTimeLikeFault H S x) (hx : x ≠ 0) : S + 1 ≤ hammingNorm x := by
  have hex : ∃ v : Fin k, ∃ t : Fin (S + 1), x (v, t) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun p => by
      obtain ⟨v, t⟩ := p
      exact hc v t)
  obtain ⟨v, t₀, ht₀⟩ := hex
  have hall : ∀ t : Fin (S + 1), x (v, t) = 1 := by
    intro t
    refine eq_one_of_ne_zero ?_
    rw [timeFault_const hf v t t₀]
    exact ht₀
  have hsub : ({v} : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin (S + 1)))
      ⊆ Finset.univ.filter (fun p : Fin k × Fin (S + 1) => x p ≠ 0) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_singleton] at hp
    obtain ⟨h1, _⟩ := hp
    have hpv : p = (v, p.2) := Prod.ext h1 rfl
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hpv, hall p.2]
    exact one_ne_zero
  have hle := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ,
    Fintype.card_fin] at hle
  change S + 1 ≤ (Finset.univ.filter (fun p : Fin k × Fin (S + 1) => x p ≠ 0)).card
  exact hle

/-- **An attainable witness**: set the whole time axis of one Gauss law to one — the weight
is exactly the number of rounds, and it escapes every timelike check. -/
def timeWit {k S : ℕ} (v₀ : Fin k) : TimeFault k S := fun p => if p.1 = v₀ then 1 else 0

theorem timeWit_apply {k S : ℕ} (v₀ : Fin k) (p : Fin k × Fin (S + 1)) :
    timeWit (S := S) v₀ p = if p.1 = v₀ then 1 else 0 := rfl

theorem timeWit_apply_pair {k S : ℕ} (v₀ v : Fin k) (i : Fin (S + 1)) :
    timeWit (S := S) v₀ (v, i) = if v = v₀ then 1 else 0 := rfl

theorem timeWit_isFault {k m S : ℕ} (H : AuxHypergraph k m) (v₀ : Fin k) :
    IsTimeLikeFault H S (timeWit (S := S) v₀) := by
  intro v i
  change (timeWit (S := S) v₀) (v, Fin.castSucc i)
      + (timeWit (S := S) v₀) (v, i.succ) = 0
  rw [timeWit_apply_pair (S := S) v₀ v (Fin.castSucc i),
    timeWit_apply_pair (S := S) v₀ v i.succ]
  by_cases hv : v = v₀
  · rw [ite_eq_left hv]
    exact CharTwo.add_self_eq_zero 1
  · rw [ite_eq_right hv]
    exact CharTwo.add_self_eq_zero 0

theorem timeWit_ne_zero {k S : ℕ} (v₀ : Fin k) : timeWit (S := S) v₀ ≠ 0 := by
  intro h
  have h1 : (timeWit (S := S) v₀) (v₀, (0 : Fin (S + 1))) = 0 := by
    simpa using congrFun h (v₀, (0 : Fin (S + 1)))
  rw [timeWit_apply_pair (S := S) v₀ v₀ (0 : Fin (S + 1)), ite_eq_left rfl] at h1
  exact one_ne_zero h1

theorem timeWit_weight {k S : ℕ} (v₀ : Fin k) :
    hammingNorm (timeWit (S := S) v₀) = S + 1 := by
  change (Finset.univ.filter (fun p : Fin k × Fin (S + 1) => timeWit (S := S) v₀ p ≠ 0)).card
    = S + 1
  have hset : (Finset.univ.filter (fun p : Fin k × Fin (S + 1) => timeWit (S := S) v₀ p ≠ 0))
      = ({v₀} : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin (S + 1))) := by
    ext p
    rw [Finset.mem_filter, timeWit_apply, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hp⟩
      refine ⟨?_, Finset.mem_univ _⟩
      by_contra h
      rw [ite_eq_right h] at hp
      exact hp rfl
    · rintro ⟨h1, _⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ite_eq_left h1]
      exact one_ne_zero
  rw [hset, Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ,
    Fintype.card_fin]

/-- **The timelike component = the number of rounds**: the minimal undetectable timelike
weight of the hypergraph surgery protocol is exactly `S + 1`.

The lower bound is `timeFault_weight_ge` and attainability is `timeWit_*` (a two-sided
squeeze), and it **does not depend on the hyperedge structure**. -/
theorem protocolTime_minWeight {k m : ℕ} (H : AuxHypergraph k m) (v₀ : Fin k) (S : ℕ) :
    IsLeast {w : ℕ | ∃ x : TimeFault k S, x ≠ 0 ∧ IsTimeLikeFault H S x ∧ hammingNorm x = w}
      (S + 1) := by
  constructor
  · exact ⟨timeWit (S := S) v₀, timeWit_ne_zero v₀, timeWit_isFault H v₀, timeWit_weight v₀⟩
  · rintro w ⟨x, hx, hf, rfl⟩
    exact timeFault_weight_ge hf hx

/-- **The timelike component is independent of the auxiliary structure**: for **any**
auxiliary hypergraph `H` (a 2-regular graph or a proper hypergraph) the minimal undetectable
timelike weight is `S + 1`.

The auxiliary hypergraph enters the **definition** of the timelike chain (the `H` of
`IsTimeLikeFault H S x`) yet does not appear in the **conclusion** — this is the machine-side
basis for "gauging and hypergraph surgery fit into the same chain". -/
theorem timeComponent_aux_independent {k m : ℕ} (H : AuxHypergraph k m) (v₀ : Fin k) (S : ℕ) :
    IsLeast {w : ℕ | ∃ x : TimeFault k S, x ≠ 0 ∧ IsTimeLikeFault H S x ∧ hammingNorm x = w}
      (S + 1) :=
  protocolTime_minWeight H v₀ S

end QECCertificates.Homology
