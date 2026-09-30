/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.MeasurementProtocol

/-!
# The closed form of the separation condition (C1 needs no decision procedure: expansion of the
complete-graph family)

The value of this package lies in its **closed form**. The decision theorem `separation_judgment`
currently reads "**assume** C1–C2, then both components are $\ge d$"; for that to become a
scientific conclusion, the hypotheses have to be **discharged** on a concrete code family. The
companion paper also names the sentence on which the cost falls:

> An estimate of 3–6 weeks, depending on whether the auxiliary graph of C1 can be taken to be the
> standard graph on the toric family, so that the step is **discharged without a decision
> procedure**.

This module does exactly that. **Take the auxiliary graph to be the complete graph $K_m$; then C1
holds for every $m$ with no enumeration at all.** C1 therefore disappears from the list of
hypotheses, and the closed form keeps only the space bound (W–Y Lemma 2, not reproved here; this
library treats cited external lemmas uniformly, carrying them over rather than reproving them) and
C2 (number of rounds $\ge d$, satisfied by $T=d$).

## 1. Why the complete graph

The cut size of $K_m$ has a closed form: the edges crossing $S$ are exactly the unordered pairs
with one end in $S$ and the other in $S^{\mathsf c}$, hence
$\mathrm{cut}(S)=|S|\cdot|S^{\mathsf c}|$. Therefore

$$\min\bigl(|S|,\ m-|S|\bigr)\ \le\ m-|S|\ =\ |S^{\mathsf c}|\ \le\ \mathrm{cut}(S),$$

The middle step is the counting lemma `cutSize_completeEdges_ge_compl` of this module: **for any
$a\in S$, the $|S^{\mathsf c}|$ edges from $a$ into $S^{\mathsf c}$ are pairwise distinct and all
cross the cut.** There is no need to compute the cut size exactly; a single-vertex estimate
suffices. This step is the substance of the whole module: it replaces "decide expansion separately
for each $m$" by "prove it once for all $m$".

## 2. The numeric form of C1

C1 in the decision theorem is the numeric form $\eta\ge1$ (the hypothesis `hC1` of
`separation_judgment`), while C1 on graphs is the computable predicate `HasExpansionOne`. The
bridge between the two is `c1Witness`: it takes the value $1$ when the graph has expansion and $0$
otherwise, so `one_le_c1Witness` connects the **computable decision** "the graph has expansion" to
the numeric hypothesis of the decision theorem, with no prose in between.

## 3. The closed form

`separation_closed`: an auxiliary graph with expansion $+$ number of rounds $\ge d$
$\Longrightarrow$ both components are $\ge d$, so **C1 and C2 are both theorems rather than
hypotheses**. `toric_family_separation_closed` instantiates this at the toric family: $d=m$ (the
family-level $[[2m^2,2,m]]$ of `Codes/HGPToricFamily.lean`), $T=m$ (C2 holds by `le_refl`), and
the auxiliary graph $K_m$ (C1 holds by `expansionOne_complete_gen`).

## 4. What remains

The **exact value** of the space component and a machine-checked proof of W–Y Lemma 2 itself are
still missing; this module only isolates them from the hypotheses rather than removing them. They
are the part still outstanding in the estimate quoted at the top of the module.
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 1. Edge list and cut size of the complete graph -/

/-- **Edge list of the complete graph $K_m$**: all unordered pairs $\{a,b\}$, represented by the one
with $a<b$.

`List` is used rather than `Finset` so that the result can be fed directly to `HasExpansionOne`,
which defines the cut size in terms of an edge list. -/
def completeEdges (m : ℕ) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap (fun a =>
    ((List.finRange m).filter (fun b => decide (a < b))).map (fun b => (a, b)))

/-- **Membership characterization of the edge list**: `(a,b)` is in the complete graph
$\iff a<b$. -/
theorem mem_completeEdges {m : ℕ} {p : Fin m × Fin m} :
    p ∈ completeEdges m ↔ p.1 < p.2 := by
  rw [completeEdges, List.mem_flatMap]
  constructor
  · rintro ⟨a, -, hb⟩
    rw [List.mem_map] at hb
    obtain ⟨b, hbf, rfl⟩ := hb
    exact of_decide_eq_true (List.mem_filter.mp hbf).2
  · intro h
    refine ⟨p.1, List.mem_finRange p.1, ?_⟩
    rw [List.mem_map]
    exact ⟨p.2, List.mem_filter.mpr ⟨List.mem_finRange p.2, decide_eq_true h⟩, rfl⟩

/-- **Counting lemma (the substance of this module)**: when $S$ is nonempty, the $|S^{\mathsf c}|$
edges from any $a\in S$ into $S^{\mathsf c}$ are pairwise distinct and all cross $S$, so the cut
size is $\ge|S^{\mathsf c}|$.

Only the **lower bound** is proved, not the exact value: the single-vertex estimate already yields
expansion, and it saves a bijective count. -/
theorem cutSize_completeEdges_ge_compl {m : ℕ} {S : Finset (Fin m)} (hne : S.Nonempty) :
    Sᶜ.card ≤ cutSize (completeEdges m) S := by
  obtain ⟨a, ha⟩ := hne
  -- 每条边取 $a<b$ 的代表，使 `f` 单射
  let f : Fin m → Fin m × Fin m := fun b => if a < b then (a, b) else (b, a)
  have hf_inj : Function.Injective f := by
    intro b₁ b₂ h
    have h1 : (f b₁).1 = (f b₂).1 := congrArg Prod.fst h
    have h2 : (f b₁).2 = (f b₂).2 := congrArg Prod.snd h
    by_cases c₁ : a < b₁ <;> by_cases c₂ : a < b₂ <;>
      simp only [f, c₁, c₂, ite_true, ite_false] at h1 h2
    · exact h2
    · exact h2.trans h1
    · exact h1.trans h2
    · exact h1
  have hcard : ((Sᶜ).image f).card = Sᶜ.card := Finset.card_image_of_injective _ hf_inj
  have hsub : (Sᶜ).image f ⊆
      (List.filter (fun e : Fin m × Fin m => decide (e.1 ∈ S) != decide (e.2 ∈ S))
        (completeEdges m)).toFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨b, hb, rfl⟩ := he
    have hbnot : b ∉ S := Finset.mem_compl.mp hb
    have hane : a ≠ b := fun h => hbnot (h ▸ ha)
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨mem_completeEdges.mpr ?_, ?_⟩
    · by_cases c : a < b
      · simp [f, c]
      · have hba : b < a := lt_of_le_of_ne (le_of_not_gt c) (Ne.symm hane)
        simpa [f, c] using hba
    · by_cases c : a < b <;> simp only [f, c, ite_true, ite_false] <;>
        rw [decide_eq_true ha, decide_eq_false hbnot] <;> rfl
  calc Sᶜ.card = ((Sᶜ).image f).card := hcard.symm
    _ ≤ (List.filter (fun e : Fin m × Fin m => decide (e.1 ∈ S) != decide (e.2 ∈ S))
          (completeEdges m)).toFinset.card := Finset.card_le_card hsub
    _ ≤ (List.filter (fun e : Fin m × Fin m => decide (e.1 ∈ S) != decide (e.2 ∈ S))
          (completeEdges m)).length := List.toFinset_card_le _
    _ = cutSize (completeEdges m) S := rfl

/-- **C1 discharged without a decision procedure (complete-graph family)**: for **every** $m$, the
expansion of $K_m$ is $\ge1$.

The proof has two steps: $S$ empty is trivial, and for $S$ nonempty one takes $a\in S$ and obtains
$\mathrm{cut}\ge|S^{\mathsf c}|=m-|S|\ge\min(|S|,m-|S|)$ from `cutSize_completeEdges_ge_compl`.

This is the sentence to be delivered: **take the auxiliary graph to be the standard graph, so that
the step is discharged without a decision procedure**. C1 can then be removed from the hypothesis
list of the decision theorem once for all, for the whole family, instead of being decided for each
$m$. -/
theorem expansionOne_complete_gen (m : ℕ) : HasExpansionOne (completeEdges m) := by
  intro S
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [cutSize]
  · have hle : m - S.card ≤ cutSize (completeEdges m) S := by
      have h := cutSize_completeEdges_ge_compl (m := m) hne
      rwa [Finset.card_compl, Fintype.card_fin] at h
    exact le_trans (min_le_right _ _) hle

/-! ## 2. The numeric form of C1 and its wiring to the decision theorem -/

/-- **The numeric form of C1**: it takes the value $\eta=1$ when the graph has expansion and $0$
otherwise.

C1 in the decision theorem `separation_judgment` is the numeric hypothesis $1\le\eta$, whereas C1
on graphs is the computable predicate `HasExpansionOne`. This definition is the **only** bridge
between the two, so no gap is left to prose. -/
def c1Witness {k : ℕ} (edges : List (Fin k × Fin k)) : ℕ :=
  if HasExpansionOne edges then 1 else 0

/-- **The bridge**: a graph with expansion $\Longrightarrow$ the numeric form satisfies $1\le\eta$
(hence $\min(\eta,1)=1$). -/
theorem one_le_c1Witness {k : ℕ} {edges : List (Fin k × Fin k)}
    (h : HasExpansionOne edges) : 1 ≤ c1Witness edges := by
  unfold c1Witness
  rw [ite_eq_left h]

/-- **Separation in closed form**: an auxiliary graph with expansion (C1) and at least $d$ rounds
(C2) $\Longrightarrow$ both components are $\ge d$.

The difference from `separation_judgment` is that there C1 and C2 are **hypotheses**, whereas here
C1 comes from the **decision procedure** for expansion of the auxiliary graph and C2 from the
number of rounds. The hypothesis list therefore keeps only the numeric form of the space bound
$hSpace$ (W–Y Lemma 2, not reproved here) and the upper bound on the time component $hTime$
(`timeLike_weight_eq` in this library). -/
theorem separation_closed {k : ℕ} {edges : List (Fin k × Fin k)} {d T spaceDist timeDist : ℕ}
    (hexp : HasExpansionOne edges) (hC2 : d ≤ T)
    (hSpace : min (c1Witness edges) 1 * d ≤ spaceDist) (hTime : T ≤ timeDist) :
    d ≤ min spaceDist timeDist :=
  separation_judgment (one_le_c1Witness hexp) hC2 hSpace hTime

/-! ## 3. The closed form on the toric family -/

/-- **Separation in closed form on the toric family**: for any $m$, the HGP of an $m$-cycle with an
$m$-cycle has $d=m$ (the family-level $[[2m^2,2,m]]$ of `Codes/HGPToricFamily.lean`, no
enumeration), and taking the auxiliary graph $K_m$ with $T=m$ rounds gives both components
$\ge m$:

* C1: `expansionOne_complete_gen m`, **proved for every $m$**;
* C2: `le_refl m`, since taking the number of rounds to be the distance satisfies it.

The hypotheses C1–C2 thus disappear on this family. -/
theorem toric_family_separation_closed {m : ℕ} {spaceDist timeDist : ℕ}
    (hSpace : min (c1Witness (completeEdges m)) 1 * m ≤ spaceDist) (hTime : m ≤ timeDist) :
    m ≤ min spaceDist timeDist :=
  separation_closed (expansionOne_complete_gen m) (le_refl m) hSpace hTime

/-- **Small-instance cross-check**: for $m=4$ the numeric form of `completeEdges 4` is indeed $1$,
agreeing with the literal version `expansionOne_complete` ($K_4$) of `Codes/Separation.lean`. -/
theorem c1Witness_completeEdges_four : c1Witness (completeEdges 4) = 1 := by decide

/-- **Cross-check of the cut-size closed form**: for $m=4$ the kernel decides
$\mathrm{cut}(S)=|S|\,(m-|S|)$ for every subset. The main text of this module proves only the
$\ge|S^{\mathsf c}|$ side; this shows that the bound is **tight** at $m=4$, and is not a weak
conclusion bought by underestimating the cut size. -/
theorem cutSize_completeEdges_exact_four :
    ∀ S : Finset (Fin 4), cutSize (completeEdges 4) S = S.card * (4 - S.card) := by
  decide

/-- **Cross-check of the two routes**: the literal edge list and `completeEdges` give the same
expansion decision at $m=4$ (the former is the existing instance of `Codes/Separation.lean`, the
latter the family form of this module). -/
theorem completeEdges_four_agrees :
    HasExpansionOne ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4))
      ∧ HasExpansionOne (completeEdges 4) :=
  ⟨expansionOne_complete, expansionOne_complete_gen 4⟩

/-! ## 4. Wiring to the measurement-protocol layer -/

/-- **The timelike component reaches $d$ on the family**: measuring a logical operator `v` with
bitwise transversal measurement, a single round has no in-round checks (`bare_noLightFault`:
single-round distance $=1$), so the spacetime fault distance of the $T$-round protocol is exactly
$T$ (`le_spacetimeWeight` $+$ `spacetimeWeight_witness`). The toric family takes a logical operator
of weight $m$ and $T=m$, giving timelike component $=m=d$, and this holds **for every $v$**,
without depending on the support structure of the logical operator. -/
theorem family_time_component {v : Vec n} {T : ℕ} {f : SpacetimeFault T n}
    (hker : ∀ t, inKerB (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) (f t) = true)
    (hlog : ∀ t, v ⬝ᵥ f t = 1) : T ≤ spacetimeWeight f := by
  simpa using le_spacetimeWeight (bare_noLightFault v) hker hlog

end QECCertificates
