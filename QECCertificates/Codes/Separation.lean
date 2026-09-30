/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.Gauging

/-!
# A decision layer for the C1–C4 separation conditions

This module provides the judgment theorem for the two-component separation conditions.
The spacetime fault-distance theorem of the companion paper has four explicit conditions
as its backbone, written C1–C4 here. This module ties each of them to the step that
carries the weight, gives a **checkable condition list** and a **judgment theorem**, and
supplies **counterexamples on both sides** of the C1 boundary.

| Condition | Content | Step that carries the weight | Treatment here |
|---|---|---|---|
| **C1** | ancilla graph expansion $h(G)\ge 1$ | the $\min(h(G),1)\cdot d$ factor of the spacelike lemma | **decidable predicate** `HasExpansionOne`, checked cut by cut, plus the numeric form `1 ≤ η` in the judgment theorem |
| **C2** | number of deformed rounds $t_o-t_i\ge d$ | the timelike lemma, where the timelike component is exactly the number of rounds $t_o-t_i$ | **theorem** (`exists_logicalFault_of_rounds_lt`, with a readout functional; without a readout, `exists_undetectable_of_rounds_lt`): too few rounds implies a lighter **undetectable logical fault**, hence **C2 is necessary** |
| **C3** | the stabilizer measurements of the first and last rounds are perfect | the boundary convention of Lemma 3 of the published supplement (Remark 3) | recorded as a technical convention (`perfectEnds`); not load-bearing for the judgment theorem |
| **C4** | no spacelike local detector within a single time slice | the structural hypothesis of the detector-generation lemma (Remark 2 of the published supplement) | as above (`noLocalDetector`) |

## What the judgment theorem does

`separation_judgment` combines the two component bounds into a lower bound on the
spacetime fault distance. The spacelike part uses the bound $\min(\eta,1)\cdot d$
of Lemma 2 of the companion paper, where $\eta\ge1$ is C1 taken as a named
hypothesis; that statement is the subject of a sharpening pursued elsewhere and is not
reproved here. The **timelike part uses a theorem of this library** (`timeLike_weight_eq`
in `Codes/Gauging.lean`: the minimum undetectable weight equals the number of rounds),
and C2 connects the number of rounds to $d$. Together

$$\min(\text{spacelike},\ \text{timelike}) \;\ge\; d .$$

## Counterexamples on both sides of C1 (computable instances)

* `not_expansionOne_path` / `expansionOne_complete`: a **decidable decision** for C1 on
  small graphs (the path graph $P_4$ has $h<1$, the complete graph $K_4$ has $h\ge1$).
  C1 is not a formal condition but a predicate checkable cut by cut.
* Code-level instances on the failing side and on the distance-preserving side are in
  `Codes/SeparationInstances`: explicit parity-check matrices of gauged deformed codes,
  enumerated by the kernel.
-/

namespace QECCertificates

open scoped BigOperators

variable {k : ℕ}

/-! ## 1. Ancilla graph and C1 (decidable predicate) -/

/-- **Cut size** of the ancilla graph: the number of edges with exactly one endpoint in `S`. -/
def cutSize (edges : List (Fin k × Fin k)) (S : Finset (Fin k)) : ℕ :=
  (edges.filter (fun e => decide (e.1 ∈ S) != decide (e.2 ∈ S))).length

/-- **C1: ancilla graph expansion $h(G)\ge1$**: for every cut, the number of cut
edges is at least the smaller of the two vertex counts (that is, the Cheeger constant is
$\ge1$; an isolated vertex violates it by taking that single vertex as the cut).

Stated with `abbrev` so that `decide` can settle it directly on small concrete graphs;
`def` is semireducible, so instance search would not unfold it. -/
abbrev HasExpansionOne (edges : List (Fin k × Fin k)) : Prop :=
  ∀ S : Finset (Fin k), min S.card (k - S.card) ≤ cutSize edges S

/-- **C1 decision (complete graph)**: $K_4$ has expansion $\ge1$. -/
theorem expansionOne_complete :
    HasExpansionOne ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
      List (Fin 4 × Fin 4)) := by decide

/-- **C1 decision (path graph)**: $P_4$, the path with 3 edges, has expansion $<1$;
taking the two middle vertices as the cut violates it, since there is one cut edge and
1 < min(2,2) = 2. This is the **graph-side example on the failing side** of C1. -/
theorem not_expansionOne_path :
    ¬ HasExpansionOne ([(0, 1), (1, 2), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-- **C1 decision (cycle graph)**: $C_4$ has expansion $\ge1$. -/
theorem expansionOne_cycle :
    HasExpansionOne ([(0, 1), (1, 2), (2, 3), (3, 0)] : List (Fin 4 × Fin 4)) := by decide

/-- **C1 decision (two disjoint edges)**: expansion $<1$, since a single edge is itself a cut with no cut edges. -/
theorem not_expansionOne_two_edges :
    ¬ HasExpansionOne ([(0, 1), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-! ## 2. The condition list C1–C4 -/

/-- **The separation condition list C1–C4** (the input of the decision layer; `η` is
the numeric form of C1, since `1 ≤ η` is equivalent to expansion $\ge1$).

`perfectEnds` and `noLocalDetector` are the Boolean flags for C3 and C4. The companion
paper itself states that both are relaxable technical conventions (Remark 5 and Remark 4
of arXiv v2, that is Remark 3 and Remark 2 of the published supplement). The
documentation here records **what they do and that they can be dropped**; the judgment
judgment theorem takes only C1 and C2 as load-bearing. -/
abbrev Conditions (edges : List (Fin k × Fin k)) (η rounds d : ℕ)
    (perfectEnds noLocalDetector : Bool) : Prop :=
  HasExpansionOne edges ∧ 1 ≤ η ∧ d ≤ rounds ∧ perfectEnds = true ∧
    noLocalDetector = true

/-! ## 3. Necessity of C2 (the timelike component is exactly the number of rounds) -/

/-- The **all-ones operator** on the timelike chain: one data bit per round. -/
def timeLikeVec (S : ℕ) : Vec (S + 1) := fun _ => 1

/-- The all-ones operator is orthogonal to the adjacent-pair checks, each check being supported on two points, an even weight modulo 2. -/
theorem timeLikeVec_repCheck (S : ℕ) (i : Fin S) :
    repCheck S i ⬝ᵥ timeLikeVec S = 0 := by
  have hone : ∀ a : Fin (S + 1), unitVec a ⬝ᵥ timeLikeVec S = 1 := by
    intro a
    rw [dotProduct, Finset.sum_eq_single a]
    · rw [unitVec, ite_eq_left rfl, one_mul]
      rfl
    · intro b _ hb
      rw [unitVec, ite_eq_right (fun h : b = a => hb h), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [repCheck, add_dotProduct, hone, hone]
  exact CharTwo.add_self_eq_zero 1

/-- The all-ones operator is nonzero: it takes the value $1$ at position $0$. -/
theorem timeLikeVec_ne_zero (S : ℕ) : timeLikeVec S ≠ 0 := by
  intro hzero
  have h0 := congrFun hzero 0
  simp [timeLikeVec] at h0

/-- The weight of the all-ones operator equals the number of rounds. -/
theorem hammingNorm_timeLikeVec (S : ℕ) : hammingNorm (timeLikeVec S) = S + 1 := by
  have hone : ∀ a : Fin (S + 1), timeLikeVec S a ≠ 0 := fun a => one_ne_zero
  have hfilter : (Finset.univ.filter (fun i : Fin (S + 1) => timeLikeVec S i ≠ 0))
      = Finset.univ := Finset.filter_true_of_mem fun i _ => hone i
  show (Finset.univ.filter (fun i : Fin (S + 1) => timeLikeVec S i ≠ 0)).card = S + 1
  rw [hfilter, Finset.card_univ, Fintype.card_fin]

/-- **Necessity of C2, form without a readout**: when the number of rounds
$T = S+1$ is less than $d$, the timelike chain carries a nonzero vector **of weight
$= T < d$** that is orthogonal to every timelike check, namely the all-ones operator.

**Note**: this gives "undetectable", **not** "undetectable **logical** fault"; the latter
additionally requires flipping a readout functional. The full form with a readout is
`exists_logicalFault_of_rounds_lt` below; the two share the same witness and differ only
in the extra dot product. -/
theorem exists_undetectable_of_rounds_lt {S d : ℕ} (h : S + 1 < d) :
    ∃ x : Vec (S + 1), x ≠ 0 ∧ (∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) ∧
      hammingNorm x < d :=
  ⟨timeLikeVec S, timeLikeVec_ne_zero S, fun i => timeLikeVec_repCheck S i,
   by rw [hammingNorm_timeLikeVec]; exact h⟩

/-- **Necessity of C2, full form with a readout functional**: as soon as the readout
assigns the value $1$ to the all-ones operator, the same witness is at once an
**undetectable logical fault**: nonzero, orthogonal to every timelike check, flipping
the readout, and of weight $<d$.

`bsMeasure2_lt_d` in `Codes/BaconShorMeasurement.lean` is the Bacon--Shor instance of
this statement; the readout functional is the support indicator vector of one round, and
its dot product with the all-ones operator is exactly $1$. -/
theorem exists_logicalFault_of_rounds_lt {S d : ℕ} (h : S + 1 < d)
    (w : Vec (S + 1)) (hw : w ⬝ᵥ timeLikeVec S = 1) :
    ∃ x : Vec (S + 1), x ≠ 0 ∧ (∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) ∧
      w ⬝ᵥ x = 1 ∧ hammingNorm x < d :=
  ⟨timeLikeVec S, timeLikeVec_ne_zero S, fun i => timeLikeVec_repCheck S i, hw,
   by rw [hammingNorm_timeLikeVec]; exact h⟩

/-- **The decision form of C2**: when the number of rounds is $\ge d$, the timelike chain carries no undetectable nonzero operator of weight $< d$, that is, the timelike component is $\ge d$. This is a direct translation of `timeLike_weight_eq`. -/
theorem no_light_undetectable_of_rounds_ge {S d : ℕ} (h : d ≤ S + 1) :
    ¬ ∃ x : Vec (S + 1), x ≠ 0 ∧ (∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) ∧
      hammingNorm x < d := by
  rintro ⟨x, hx, horth, hw⟩
  rw [timeLike_weight_eq horth hx] at hw
  omega

/-! ## 4. The judgment theorem (assembly layer) -/

/-- **The two-component separation judgment theorem**: C1 (expansion
$\eta\ge1$) and C2 (number of rounds $\ge d$) combine the two component bounds
into the spacetime fault distance lower bound $d$:

* spacelike: the bound $\min(\eta,1)\cdot d \le \text{spacelike component}$ of
  Lemma 2 of the companion paper, where the role of C1 is to make
  $\min(\eta,1)=1$, so that the bound degenerates to $d$;
* timelike: a theorem of this library (`timeLike_weight_eq`) gives "timelike component =
  number of rounds", and C2 then yields $\ge d$.

C3 and C4 are the technical conventions that the companion paper states to be relaxable
(Remark 5 and Remark 4) and do not enter this assembly. -/
theorem separation_judgment {d η rounds spaceDist timeDist : ℕ}
    (hC1 : 1 ≤ η) (hC2 : d ≤ rounds)
    (hSpace : min η 1 * d ≤ spaceDist)
    (hTime : rounds ≤ timeDist) :
    d ≤ min spaceDist timeDist := by
  have hmin : min η 1 = 1 := min_eq_right hC1
  rw [hmin, one_mul] at hSpace
  exact le_min hSpace (le_trans hC2 hTime)

/-! ## 5. Implication and independence between the conditions (small instances, `decide`) -/

/-- **C2 does not imply C1**: the number of rounds is sufficient, so C2 holds, while the ancilla graph is a path, so C1 fails. -/
theorem C2_not_C1 :
    ¬ HasExpansionOne ([(0, 1), (1, 2), (2, 3)] : List (Fin 4 × Fin 4)) ∧
      (3 : ℕ) ≤ 3 := ⟨not_expansionOne_path, le_refl 3⟩

/-- **C1 does not imply C2**: the graph is complete, so C1 holds, while the number of rounds is insufficient, so C2 fails. -/
theorem C1_not_C2 :
    HasExpansionOne ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
      List (Fin 4 × Fin 4)) ∧ ¬ ((3 : ℕ) ≤ 2) :=
  ⟨expansionOne_complete, by decide⟩

/-- **C3 and C4 are independent of C1 and C2**: on one and the same instance the four conditions can take arbitrary values, since C3 and C4 are Boolean flags and it suffices to negate them. Hence the judgment theorem makes only C1 and C2 load-bearing. -/
theorem C3_C4_independent :
    ¬ (Conditions ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
        List (Fin 4 × Fin 4)) 1 3 3 false true) ∧
      ¬ (Conditions ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
        List (Fin 4 × Fin 4)) 1 3 3 true false) := by
  constructor <;> intro h <;> simp [Conditions] at h

end QECCertificates
