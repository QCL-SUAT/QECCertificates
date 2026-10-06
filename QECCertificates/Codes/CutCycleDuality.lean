/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.Separation
import QECCertificates.Homology.CosystolicLowerBound

/-!
# The first step of W–Y Lemma 2: an edge support is a cut (the cut space is the
orthogonal complement of the even-subgraph space)

The counting core `space_fault_weight_ge_of_expansion` of `Codes/ToricFamilySpatial.lean`
splits the proof of [12] Methods Lemma 2 into three pieces, of which **the third** (the
Cheeger count) is a theorem, while **the first** (the X-type support of a logical operator
on the edges is the cut of some vertex set) and **the second** (cleaning) are written into
the statement as hypotheses. This module turns **the first piece** into a theorem.

## Contents

Following the library's existing encoding, the ancilla graph is an edge list
`edges : List (Fin k × Fin k)` (`Codes/Separation.lean`'s `cutSize` and `HasExpansionOne`
are stated on it), and this module attaches to it the **incidence matrix**
`incidMat edges : Matrix (Fin edges.length) (Fin k) (ZMod 2)` -- one row per edge (parallel
edges each take a row), one column per vertex, with a $1$ at an edge and each of its two
endpoints. The two spaces mentioned by the first piece of Lemma 2 thus acquire names in
this library:

* **the cut space** `(incidMat edges).mulVecLin.range`: taking `f` to be the indicator
  vector `indVec T` of a vertex set $T$, `incidMat edges *ᵥ indVec T` is exactly the
  indicator vector of the cut $\partial T$ (`support_mulVec_indVec`), whose weight is the
  number of cut edges (`hammingNorm_mulVec_indVec_eq_cutSize`, matching the existing
  `cutSize` verbatim); conversely $\mathbb{Z}_2$ has only the two elements $0/1$, so every
  `f : Vec k` is the indicator vector of some $T$, and this image is "all cuts".
* **the even-subgraph space**, the kernel of `((incidMat edges)ᵀ *ᵥ ·)`:
  `((incidMat edges)ᵀ *ᵥ n) u` is "the number of selected edges incident at vertex `u`"
  (`incidMatOf_transpose_mulVec_apply`), so its vanishing is exactly "every vertex has even
  selected degree", that is an even subgraph -- the standard algebraic definition of the
  cycle space (each edge is a column, the kernel of $\partial_1$).

**The main theorem** `cut_iff_forall_dot_evenSubgraph`: `M` lies in the cut space if and
only if `M` is orthogonal to every even subgraph. It is the general duality
`exists_mulVec_eq_iff_forall_dot_eq_zero` of `Codes/CosystolicLowerBound.lean` instantiated
on the incidence matrix; what this module adds are the two facts missing from reading that
abstract statement **as a graph-theoretic sentence** (image = cuts, kernel = even
subgraphs) together with the **weight reading** of a cut.

## Honest boundary

* The cycle space is taken here in its **algebraic definition** `ker ((incidMat edges)ᵀ)`
  (even subgraphs), and §6 machine-checks its **classical description** as well: the cycle
  space is spanned by **cycles** (minimal nonempty even subgraphs),
  `evenSubgraphSpace_eq_span_minCycle`. Hence the right-hand side of the §3 main theorem,
  "orthogonal to every even subgraph", and "orthogonal to every cycle" are the same
  sentence.
* The incidence matrix is given **row by row** on the edge list, parallel edges each taking
  a row, matching `cutSize`'s convention of counting by list entries.
* The two readings of a cut (`support_mulVec_indVec`, `hammingNorm_mulVec_indVec_eq_cutSize`)
  are stated under the **loop-free** hypothesis (`LoopFree`) -- the ancilla graph is simple,
  and a loop means different things in the two readings (`cutSize` does not count loops).
  **The main theorem needs no loop-free hypothesis**: it is purely linear.
-/

namespace QECCertificates

open QECCertificates.Homology

open _root_.Matrix

open scoped BigOperators

variable {k : ℕ}

/-! ## 1. Edge lists, loop-freeness, the incidence matrix -/

/-- An edge list is **loop-free**: the two endpoints of every edge are distinct. -/
def LoopFree {m : ℕ} (e : Fin m → Fin k × Fin k) : Prop := ∀ i, (e i).1 ≠ (e i).2

/-- **The incidence matrix** (given row by row against the edge index): edge $i$ is a row,
vertex a column, with a $1$ at an edge and each of its two endpoints.

The row index is `Fin m` (the edge list numbered by position); taking
`e := fun i => edges.get i` on an edge list gives `incidMat edges`. -/
def incidMatOf {m : ℕ} (e : Fin m → Fin k × Fin k) : Matrix (Fin m) (Fin k) (ZMod 2) :=
  fun i v => if (e i).1 = v ∨ (e i).2 = v then 1 else 0

theorem incidMatOf_apply {m : ℕ} (e : Fin m → Fin k × Fin k) (i : Fin m) (v : Fin k) :
    incidMatOf e i v = if (e i).1 = v ∨ (e i).2 = v then 1 else 0 := rfl

/-! ## 2. Two action formulas: matrix-vector action and transpose action -/

/-- **The incidence matrix acting on a vector**: the $i$-th component is the sum of the
vector's values at the two endpoints. Under loop-freeness this is the $i$-th component of
the cut $\partial T$ (see `support_mulVec_indVec`). -/
theorem incidMatOf_mulVec_apply {m : ℕ} (e : Fin m → Fin k × Fin k) (hfree : LoopFree e)
    (v : Vec k) (i : Fin m) :
    (incidMatOf e *ᵥ v) i = v (e i).1 + v (e i).2 := by
  have hne : (e i).1 ≠ (e i).2 := hfree i
  have hterm : ∀ j : Fin k, incidMatOf e i j * v j
      = (if j = (e i).1 then v j else 0) + (if j = (e i).2 then v j else 0) := by
    intro j
    rw [incidMatOf_apply]
    by_cases h1 : j = (e i).1
    · rw [ite_eq_left (Or.inl h1.symm), ite_eq_left h1,
        ite_eq_right (fun h => hne (h1.symm.trans h))]
      simp
    · by_cases h2 : j = (e i).2
      · rw [ite_eq_left (Or.inr h2.symm), ite_eq_right h1, ite_eq_left h2]
        simp
      · rw [ite_eq_right (fun h => h.elim (fun ha => h1 ha.symm) (fun hb => h2 hb.symm)),
          ite_eq_right h1, ite_eq_right h2]
        simp
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (e i).1, Finset.sum_ite_eq' Finset.univ (e i).2]
  simp

/-- **The transpose of the incidence matrix acting on a vector**: the $u$-th component is
the sum of the weights of the selected edges "incident at `u`", that is the degree of `n`
at `u` (in `ZMod 2`). Hence `((incidMat edges)ᵀ *ᵥ n) u = 0` for every `u` is exactly
"every vertex has even degree" -- an even subgraph (the algebraic definition of the cycle
space). -/
theorem incidMatOf_transpose_mulVec_apply {m : ℕ} (e : Fin m → Fin k × Fin k)
    (n : Vec m) (u : Fin k) :
    ((incidMatOf e)ᵀ *ᵥ n) u
      = (Finset.univ.filter (fun i => (e i).1 = u ∨ (e i).2 = u)).sum n := by
  rw [Matrix.mulVec, dotProduct]
  have hterm : ∀ i : Fin m, (incidMatOf e)ᵀ u i * n i
      = (if (e i).1 = u ∨ (e i).2 = u then n i else 0) := by
    intro i
    rw [Matrix.transpose_apply, incidMatOf_apply]
    by_cases h : (e i).1 = u ∨ (e i).2 = u <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_filter]

/-! ## 3. The main theorem: `M` is a cut $\iff$ `M` is orthogonal to every even subgraph -/

/-- **The cut space is the orthogonal complement of the even-subgraph space** (the first
piece of W–Y Lemma 2).

The left-hand side is "the cut of some vertex set": when `f : Vec k` is the indicator
vector of a vertex set $T$, `incidMat edges *ᵥ f` is the cut $\partial T$, and in `ZMod 2`
every `f` is the indicator vector of some $T$; the right-hand side is "orthogonal to every
even subgraph".

It is the general duality `exists_mulVec_eq_iff_forall_dot_eq_zero` of
`Codes/CosystolicLowerBound.lean` instantiated (this module adds only the two
graph-theoretic readings, so the proof here is one line). -/
theorem cut_iff_forall_dot_evenSubgraph {m : ℕ} (e : Fin m → Fin k × Fin k) (M : Vec m) :
    (∃ f : Vec k, incidMatOf e *ᵥ f = M)
      ↔ ∀ n : Vec m, (incidMatOf e)ᵀ *ᵥ n = 0 → M ⬝ᵥ n = 0 :=
  exists_mulVec_eq_iff_forall_dot_eq_zero (incidMatOf e) M

/-! ## 4. The two readings of a cut: support and weight -/

/-- **The support of a cut vector**: `incidMatOf e *ᵥ indVec T` is nonzero in the $i$-th
position if and only if exactly one endpoint of the $i$-th edge lies in `T` -- that is, it
is the indicator vector of the cut $\partial T$. -/
theorem support_mulVec_indVec {m : ℕ} (e : Fin m → Fin k × Fin k) (hfree : LoopFree e)
    (T : Finset (Fin k)) :
    support (incidMatOf e *ᵥ indVec T)
      = Finset.univ.filter
          (fun i => decide ((e i).1 ∈ T) != decide ((e i).2 ∈ T)) := by
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [incidMatOf_mulVec_apply e hfree]
  by_cases h1 : (e i).1 ∈ T <;> by_cases h2 : (e i).2 ∈ T <;>
    simp [indVec, h1, h2, CharTwo.add_self_eq_zero]

/-! ## 5. The bridge between edge lists and `cutSize` (the library's existing convention) -/

/-- The incidence matrix (edge-list version): the row index is `Fin edges.length` and the
$i$-th row is the $i$-th edge. -/
abbrev incidMat (edges : List (Fin k × Fin k)) :
    Matrix (Fin edges.length) (Fin k) (ZMod 2) :=
  incidMatOf (fun i => edges.get i)

theorem incidMat_apply (edges : List (Fin k × Fin k)) (i : Fin edges.length) (v : Fin k) :
    incidMat edges i v = if (edges.get i).1 = v ∨ (edges.get i).2 = v then 1 else 0 := rfl

/-- An edge list is **loop-free** (read off edge by edge). -/
def LoopFreeEdges (edges : List (Fin k × Fin k)) : Prop :=
  ∀ i : Fin edges.length, (edges.get i).1 ≠ (edges.get i).2

/-- **The by-position counting bridge**: the indicator count over `Fin l.length` equals the
length of `List.filter` (both sides count list entries with multiplicity). -/
theorem card_filter_get_eq_length_filter {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin l.length => p (l.get i) = true)).card
      = (l.filter p).length := by
  rw [Finset.card_filter, ← List.countP_eq_length_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    change (∑ i : Fin (l.length + 1), (if p ((a :: l).get i) = true then 1 else 0))
      = List.countP p (a :: l)
    rw [Fin.sum_univ_succ, List.get_cons_zero]
    have hs : ∀ i : Fin l.length, List.get (a :: l) i.succ = List.get l i :=
      fun i => List.get_cons_succ' (i := i)
    simp only [hs, List.countP_cons]
    by_cases hp : p a = true
    · rw [ite_eq_left hp, ih]
      omega
    · rw [ite_eq_right hp, ih]
      omega

/-- **The weight of a cut is the number of cut edges**:
`hammingNorm (incidMat edges *ᵥ indVec T) = cutSize edges T`.

The left-hand side is the weight of the cut vector given by the incidence matrix, the
right-hand side is `Codes/Separation.lean`'s `cutSize` (the quantity `HasExpansionOne`
uses) -- the two conventions are aligned here, so the $|\partial T|$ of the counting core
and the cut-vector weight here are the same number. -/
theorem hammingNorm_mulVec_indVec_eq_cutSize (edges : List (Fin k × Fin k))
    (hfree : LoopFreeEdges edges) (T : Finset (Fin k)) :
    hammingNorm (incidMat edges *ᵥ indVec T) = cutSize edges T := by
  rw [← weight_eq_hammingNorm,
    support_mulVec_indVec (k := k) (fun i : Fin edges.length => edges.get i) hfree T, cutSize]
  exact card_filter_get_eq_length_filter edges
    (fun e => decide (e.1 ∈ T) != decide (e.2 ∈ T))

/-! ## 6. The even-subgraph space is spanned by cycles (the classical description of the
cycle space)

Section 2 took the cycle space in its **algebraic form**: the kernel of the transpose
incidence matrix, that is the edge sets with even degree at every vertex (even subgraphs).
This section supplies its **classical description** -- the cycle space is spanned by
**cycles**, so "orthogonal to every cycle" and "orthogonal to every even subgraph" are the
same thing, and the right-hand side of the main theorem `cut_iff_forall_dot_evenSubgraph`
need no longer be named after "even subgraphs".

A **cycle** here is a **minimal nonempty even subgraph**. It is the simple cycle of graph
theory: minimality keeps it from containing a smaller cycle, and its degree at every
vertex can only be $0$ or $2$ (a degree $\ge 4$ would yield a smaller even subgraph by
walking around along two distinct edges); a double edge given by a parallel edge also falls
under the definition. The definition does not need to write a "cycle" as a closed walk, so
no walk machinery is introduced.

**The proof** (strong induction on the size of the edge set): a nonempty even subgraph `S`
that is minimal is itself a generator; otherwise there is a nonempty proper subset
`T ⊊ S` that is still an even subgraph. In characteristic $2$ the difference set is still
an even subgraph (the two incidence counts of `S \ T` subtract), and both `|T|` and
`|S \ T|` are smaller than `|S|`, while `indVec S = indVec T + indVec (S \ T)`, so the
induction hypothesis applies to two smaller even subgraphs. -/

/-- The **even-subgraph space** on an edge list (the algebraic form of the cycle space):
the kernel of the transpose incidence matrix.

Here `n` lives on the **edges**, and `((incidMatOf e)ᵀ *ᵥ n) u` is the sum of the selected
edges at vertex `u`, so this vanishing is exactly "every vertex has even selected
degree". -/
abbrev evenSubgraphSpace {k m : ℕ} (e : Fin m → Fin k × Fin k) : Submodule (ZMod 2) (Vec m) :=
  LinearMap.ker ((incidMatOf e)ᵀ).mulVecLin

/-- A **cycle**: a minimal nonempty even subgraph. -/
def IsMinEvenSubgraph {k m : ℕ} (e : Fin m → Fin k × Fin k) (S : Finset (Fin m)) : Prop :=
  S.Nonempty ∧ indVec S ∈ evenSubgraphSpace e ∧
    ∀ T : Finset (Fin m), T ⊂ S → T.Nonempty → indVec T ∉ evenSubgraphSpace e

/-- The generating set: the indicator vectors of the cycles (minimal even subgraphs). -/
def minCycleVecs {k m : ℕ} (e : Fin m → Fin k × Fin k) : Set (Vec m) :=
  {v | ∃ S : Finset (Fin m), IsMinEvenSubgraph e S ∧ indVec S = v}

/-- **The indicator vector of a difference set is the sum of the two** (`T ⊆ S`,
characteristic $2$): `indVec (S \ T) = indVec S + indVec T`. -/
theorem indVec_sdiff_eq_add {n : ℕ} {S T : Finset (Fin n)} (h : T ⊆ S) :
    indVec (S \ T) = indVec S + indVec T := by
  funext i
  simp only [indVec, Pi.add_apply]
  by_cases hiT : i ∈ T
  · have hiS : i ∈ S := h hiT
    have hni : i ∉ S \ T := fun hh => (Finset.mem_sdiff.mp hh).2 hiT
    rw [ite_eq_right hni, ite_eq_left hiS, ite_eq_left hiT]
    simp [CharTwo.add_self_eq_zero]
  · by_cases hiS : i ∈ S
    · have hi : i ∈ S \ T := Finset.mem_sdiff.mpr ⟨hiS, hiT⟩
      rw [ite_eq_left hi, ite_eq_left hiS, ite_eq_right hiT]
      simp
    · have hni : i ∉ S \ T := fun hh => hiS (Finset.mem_sdiff.mp hh).1
      rw [ite_eq_right hni, ite_eq_right hiS, ite_eq_right hiT]
      simp

/-- **The even-subgraph space is spanned by cycles** (the classical description of the
cycle space): every even subgraph is a linear combination of cycles (minimal even
subgraphs).

Together with `cut_iff_forall_dot_evenSubgraph`, "orthogonal to every even subgraph" and
"orthogonal to every cycle" are therefore the same sentence, which is exactly how the
first step of the counting lemma reads in the classical literature. -/
theorem evenSubgraphSpace_eq_span_minCycle {k m : ℕ} (e : Fin m → Fin k × Fin k) :
    evenSubgraphSpace e = Submodule.span (ZMod 2) (minCycleVecs e) := by
  refine le_antisymm ?_ ?_
  · have key : ∀ n, ∀ S : Finset (Fin m), S.card ≤ n → indVec S ∈ evenSubgraphSpace e →
        indVec S ∈ Submodule.span (ZMod 2) (minCycleVecs e) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro S hle hS
        by_cases hne : S.Nonempty
        · by_cases hmin : IsMinEvenSubgraph e S
          · exact Submodule.subset_span ⟨S, hmin, rfl⟩
          · have hex : ∃ T : Finset (Fin m),
                T ⊂ S ∧ T.Nonempty ∧ indVec T ∈ evenSubgraphSpace e := by
              by_contra hcon
              apply hmin
              exact ⟨hne, hS, fun T hT1 hT2 hT3 => hcon ⟨T, hT1, hT2, hT3⟩⟩
            obtain ⟨T, hTssub, hTne, hTcyc⟩ := hex
            have hTsub : T ⊆ S := hTssub.subset
            have hssub : S \ T ⊂ S := by
              refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
              intro hEq
              obtain ⟨t, htT⟩ := hTne
              have hnt : ¬ (t ∈ S \ T) := fun hh => (Finset.mem_sdiff.mp hh).2 htT
              rw [hEq] at hnt
              exact hnt (hTsub htT)
            have hTlt : T.card < n :=
              Nat.lt_of_lt_of_le (Finset.card_lt_card hTssub) hle
            have hDlt : (S \ T).card < n :=
              Nat.lt_of_lt_of_le (Finset.card_lt_card hssub) hle
            have hDcyc : indVec (S \ T) ∈ evenSubgraphSpace e := by
              rw [indVec_sdiff_eq_add hTsub]
              exact (evenSubgraphSpace e).add_mem hS hTcyc
            have hspanT := ih T.card hTlt T le_rfl hTcyc
            have hspanD := ih (S \ T).card hDlt (S \ T) le_rfl hDcyc
            have hrecon : indVec S = indVec T + indVec (S \ T) := by
              rw [indVec_sdiff_eq_add hTsub, add_comm (indVec T), add_assoc,
                add_self, add_zero]
            rw [hrecon]
            exact (Submodule.span (ZMod 2) (minCycleVecs e)).add_mem hspanT hspanD
        · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          rw [hS0]
          have hz : indVec (∅ : Finset (Fin m)) = 0 := by
            funext i; simp [indVec]
          rw [hz]
          exact Submodule.zero_mem _
    intro v hv
    rw [eq_indVec_support v] at hv ⊢
    exact key (support v).card (support v) le_rfl hv
  · refine Submodule.span_le.mpr ?_
    intro v hv
    obtain ⟨S, hS, hveq⟩ := hv
    rw [← hveq]
    exact hS.2.1

end QECCertificates
