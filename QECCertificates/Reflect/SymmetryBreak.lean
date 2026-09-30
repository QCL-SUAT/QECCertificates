/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB144Symmetry

/-!
# Faithfulness of symmetry breaking: the broken formula is unsatisfiable only if the original is

The external encoder adds "lexicographic orbit representative" constraints to a CNF and then hands
it to the solver. The direction that route needs is

    the CNF after breaking is unsatisfiable  ⟹  the original CNF is unsatisfiable

This module proves its **semantic core** and instantiates that core at the translation group of BB
$[[144,12,12]]$.

## Core: the orbit lifting lemma

Let `G` be a family of permutations of `α` (**only required to be finite and to contain the
identity**; it need not be a subgroup), let `≤` be a total order on `α` and let `P` be a predicate
**invariant** under `G`. Define the broken predicate

    OrbitMin G P a  :=  P a ∧ ∀ g ∈ G, a ≤ g a

Then **`∃ a, OrbitMin G P a` ⟺ `∃ a, P a`** (`orbitMin_iff_exists`). The two directions are:

* `⟸`: take `a` with `P`, and take the `≤`-least element `m` of **its orbit**. Then `m` is some
  `g a`, so `P m` holds by invariance; and for any `h ∈ G`, `h m` again lies in the same orbit, so
  `m ≤ h m`. Hence `m` satisfies the broken predicate.
* `⟹`: the broken predicate already implies `P`.

**This is the direction the route needs**: taking the contrapositive of `⟹` gives "no broken
solution implies no original solution". The `⟸` half (every orbit retains a representative) is
exactly where the **too tight** failure mode lives: if the broken encoding cuts away too much, it
is this half that fails. Both directions are therefore proved.

**Why "contains the identity" is needed**: `⟸` uses that the `a` with `P a` really does lie in its
own orbit.

## Relation to the CNF layer (the step this module does **not** take, marked as such)

What this module states is the **semantics**: `P` is a `Prop` and `OrbitMin` is its constrained
form. Connecting the **CNF** produced by the external encoder still requires

    SatFormula τ (CNF after breaking)  ⟹  ∃ a, OrbitMin G P a

that is, "a satisfying assignment of the CNF, projected through `x`/`w`, gives a broken semantic
solution". This is assembled from the `buildPair_sat` family of `Reflect/Encode.lean` (the
soundness of the Tseitin chains, product blocks and sequential counters) together with the
soundness of the lexicographic-comparator clauses. **That step is not in this module**: what is
delivered here is its semantic premise and the orbit lemma, which the next module of the
faithfulness family in `Reflect/` takes up.
-/

namespace QECCertificates

open scoped BigOperators

-- `GrossGroup`（`= ZMod 12 × ZMod 6`）在上游 QEC 的命名空间里
open Quantum.Stabilizer.Homological.BB

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **orbit** of `a` under `G`: the finite set of all `g a` with `g ∈ G`.

`Finset.univ.filter` is used rather than `G.image` because the former describes exactly the fact
that an orbit is a finite subset of `α`, and it needs no `DecidableEq` on `Equiv.Perm α`. -/
def orbitOf (G : Finset (Equiv.Perm α)) (a : α) : Finset α :=
  Finset.univ.filter (fun b => ∃ g ∈ G, g a = b)

theorem mem_orbitOf {G : Finset (Equiv.Perm α)} {a b : α} :
    b ∈ orbitOf G a ↔ ∃ g ∈ G, g a = b := by
  simp [orbitOf]

/-- When the identity is in `G`, `a` lies in its own orbit; this is what the `⟸` half rests on. -/
theorem self_mem_orbitOf (G : Finset (Equiv.Perm α)) (h1 : 1 ∈ G) (a : α) :
    a ∈ orbitOf G a :=
  mem_orbitOf.mpr ⟨1, h1, rfl⟩

/-- **Orbit lifting lemma**: a finite orbit has a least element.

The proof uses only that the orbit is finite and nonempty. It does not need `G` to be a subgroup,
nor to contain the identity (nonemptiness is supplied by the caller). This is the only place in the
module where `LinearOrder` is used. -/
theorem exists_min_orbitOf [LinearOrder α] (G : Finset (Equiv.Perm α)) {a : α}
    (hne : (orbitOf G a).Nonempty) :
    ∃ m ∈ orbitOf G a, ∀ b ∈ orbitOf G a, m ≤ b :=
  let ⟨m, hm, hmin⟩ := Finset.exists_min_image (orbitOf G a) id hne
  ⟨m, hm, fun b hb => hmin b hb⟩

/-- `P` is invariant under `G`. -/
def IsInvariant (G : Finset (Equiv.Perm α)) (P : α → Prop) : Prop :=
  ∀ g ∈ G, ∀ a, P (g a) ↔ P a

/-- **The broken predicate**: `P` holds and `a` is `≤`-least within its own orbit.

This is exactly the semantic shape asserted by every lexicographic constraint the external encoder
adds; the tool adds one for **each** `g ≠ e`, so the quantifier here is `∀ g ∈ G`. -/
def OrbitMin [LE α] (G : Finset (Equiv.Perm α)) (P : α → Prop) (a : α) : Prop :=
  P a ∧ ∀ g ∈ G, a ≤ g a

/-- **Faithfulness (the main theorem of this module)**: the broken predicate is satisfiable if and
only if the original predicate is.

`⟸` is the content of this module (take the orbit minimum); `⟹` is trivial. **Both directions are
proved**: `⟹` is the direction the route needs (its contrapositive is "a broken predicate that is
unsatisfiable implies an original predicate that is unsatisfiable"), while `⟸` rules out being
**too tight**: it asserts that every orbit keeps at least one representative, so that breaking does
not cut away all solutions. -/
theorem orbitMin_iff_exists [LinearOrder α] (G : Finset (Equiv.Perm α)) (h1 : 1 ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, h * g ∈ G) (P : α → Prop) (hP : IsInvariant G P) :
    (∃ a, OrbitMin G P a) ↔ (∃ a, P a) := by
  constructor
  · rintro ⟨a, ha, _⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, hmin⟩ :=
      exists_min_orbitOf G ⟨a, self_mem_orbitOf G h1 a⟩
    obtain ⟨g, hg, hga⟩ := mem_orbitOf.mp hm
    have hPm : P m := by
      rw [← hga]
      exact (hP g hg a).mpr ha
    refine ⟨m, hPm, fun h hh => ?_⟩
    exact hmin (h m) (mem_orbitOf.mpr ⟨h * g, hmul g hg h hh, by rw [← hga]; rfl⟩)

/-- **The direction the route needs, in contrapositive form**: if the broken predicate is
unsatisfiable then so is the original predicate.

This shape is chosen so as to correspond word for word to the usage on the tool side, where the
solver reports UNSAT and the conclusion lands on the original statement. -/
theorem not_exists_of_not_exists_orbitMin [LinearOrder α] (G : Finset (Equiv.Perm α))
    (h1 : 1 ∈ G) (hmul : ∀ g ∈ G, ∀ h ∈ G, h * g ∈ G) (P : α → Prop)
    (hP : IsInvariant G P) :
    ¬ (∃ a, OrbitMin G P a) → ¬ (∃ a, P a) :=
  fun h => h ∘ (orbitMin_iff_exists G h1 hmul P hP).mpr

/-! ## Instantiation: the BB $[[144,12,12]]$ translation group and the light logical operators

The three facts supplied by `Codes/BB144Symmetry.lean` (weight preservation, preservation of the
row spaces on both sides, and preservation of the pairing) combine into "this action maps logical
operators to logical operators", which is the `IsInvariant` required by this module. The group
`bb144Group` below takes the 72 translations (the `--perms all` setting of the tool), and `1 ∈ G`
comes from the `(0,0)` entry. -/

open QECCertificates.BB144Distance

/-- The translation group of BB144, as a finite set of permutations (the 72 of the tool's
`--perms all` setting). -/
noncomputable def bb144Group : Finset (Equiv.Perm (Fin 144)) :=
  Finset.univ.image fun t : GrossGroup => bb144Trans t

/-- The identity is in the group, which is the premise of the `⟸` half. -/
theorem bb144Group_one_mem : (1 : Equiv.Perm (Fin 144)) ∈ bb144Group := by
  refine Finset.mem_image.mpr ⟨(0 : GrossGroup), Finset.mem_univ 0, ?_⟩
  ext c
  simp [bb144Trans]

/-- **Invariance**: a translation maps logical operators to logical operators.

The four hypotheses correspond one by one to the definition of a logical operator on a pair
`(x, w)`: `x` lies in the kernel of `H_X`, `w` lies in the kernel of `H_Z`, the pairing is 1, and
the weight is bounded. The first three come from the three facts of `Codes/BB144Symmetry.lean`, and
the weight bound from `bb144Trans_hammingNorm`. -/
theorem bb144_isLogical_invariant (t : GrossGroup) (v w : Vec 144)
    (hv : inKerB bb144Hx v = true) (hw : inKerB bb144Hz w = true)
    (hpair : v ⬝ᵥ w = 1) (hwt : hammingNorm v ≤ 11) :
    inKerB bb144Hx (permVec (bb144Trans t) v) = true ∧
    inKerB bb144Hz (permVec (bb144Trans t) w) = true ∧
    (permVec (bb144Trans t) v) ⬝ᵥ (permVec (bb144Trans t) w) = 1 ∧
    hammingNorm (permVec (bb144Trans t) v) ≤ 11 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- x 在核里：置换保核（`inKerB_permVec`），假设是「逆置换把校验行映成校验行」
    exact inKerB_permVec bb144Hx (bb144Trans t)
      (fun i => by
        rw [bb144Trans_symm_eq]
        exact bb144_permVec_hxRow_mem (-t) (List.mem_ofFn.mpr ⟨i, rfl⟩)) hv
  · exact inKerB_permVec bb144Hz (bb144Trans t)
      (fun i => by
        rw [bb144Trans_symm_eq]
        exact bb144_permVec_hzRow_mem (-t) (List.mem_ofFn.mpr ⟨i, rfl⟩)) hw
  · rw [bb144Trans_dotProduct]
    exact hpair
  · rw [bb144Trans_hammingNorm]
    exact hwt

end QECCertificates
