/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.Separation

/-!
# The edge census for C1: how many ancillas the expansion condition really needs

C1 of `Codes/Separation.lean` is `HasExpansionOne`: on the ancilla graph the number of cut
edges of every cut is at least the smaller of the two vertex counts. The paper's sentence
about it is: taking the ancilla graph to be the **complete graph** $K_m$ lets C1 dispense
with a member-by-member check, but each edge of the ancilla graph carries one ancilla bit,
so this recipe costs $m(m-1)/2$ ancillas at support size $m$ -- "and this is exactly the
resource the expansion condition is there to save".

This module quantifies that sentence. **The question**: on $m$ vertices, how few edges can
an edge list satisfying C1 have?

## Results

* `expansionOne_star_two` through `_six`: the **star graph** (centre `0`, leaves `1..k`)
  satisfies C1 with only $k$ edges on $k+1$ vertices -- that is, $m-1$ edges suffice on
  $m$ vertices. These are decided **for each concrete $m$**.
* `expansionOne_append`: **adding an edge does not break C1** (the cut size is monotone in
  the edge list). This is a general lemma, so "the star graph plus any number of chords"
  automatically satisfies C1, **with no case-by-case check**.
* Together: from $m-1$ edges (the star) to $m-1+r$ edges (the star plus $r$ chords) every
  list is a C1 witness, while $K_m$ needs $m(m-1)/2$. At $m=4$ **with three independent
  cycles (cycle rank $3$) both are $6$** -- which is why $K_4$ is not wasteful on the BB
  $[[18,4,4]]$ instance; the gap opens as $m$ grows ($m=7$ at cycle rank $3$: $9$ against
  $21$).

## Honest boundary

* **Optimality is proved**: `Codes/C1Optimal.lean`'s
  `card_sub_one_le_length_of_hasExpansionOne` shows that an edge list on $k$ vertices
  satisfying C1 has at least $k-1$ edges, and **by linear algebra rather than graph
  theory** (the kernel of the endpoint-difference map consists only of constant
  functions). So this module and that one together make "the least number of edges for C1
  on $k$ vertices is exactly $k-1$" a **theorem**; the census's exhaustive computation is
  its cross-check.
* **The family form is proved too**: `expansionOne_star_gen` shows the star graph
  satisfies C1 for **every** $k$, and the per-$m$ statements (`expansionOne_star_two`
  through `_six`) become its special cases. The proof **only counts a lower bound**: every
  edge of the star is $(0,v)$, so the vertices $v$ with an endpoint on either side of $S$
  and $S^{\mathsf c}$ give **distinct** crossing edges, and it suffices to take the side
  attaining the $\max$; the exact cut formula is never needed. Together with the lower
  bound from `Codes/C1Optimal.lean`: **the least number of edges for C1 on $k$ vertices is
  exactly $k-1$**, with both directions in the kernel.
* **The cycle-rank side**: `Codes/C1CycleRank.lean`'s `card_ge_of_finrank_cycleSpace`
  gives "cycle-space dimension $\ge r$ $\Rightarrow$ edge count $\ge k-1+r$", and the upper
  bound is given by the star plus $r$ chords (`expansionOne_append_list`), so **at cycle
  rank $\ge r$ the least number of edges for C1 is exactly $m-1+r$**. The construction
  **defines no boundary map and proves no transpose equal-rank fact**: the cycle space
  takes the **dual description** (the edge vectors orthogonal to every cut), whose
  dimension is pinned directly by `LinearMap.BilinForm.finrank_orthogonal`. **This module
  leaves no gap.**

## Relation to [12]

[12] = Cowtan–He–Williamson–Yoder. There C1 is the $\min(h(G),1)\cdot d$ factor of the
spacelike lemma; this module does not change that bound, only **the cost of paying it**.
-/

namespace QECCertificates

open scoped BigOperators

-- `starEdges` is a `finRange` + `map` definition, and `decide` has to reduce it to a
-- literal edge list before checking cut by cut, so both the recursion depth and the
-- heartbeat budget are relaxed (the same module-level option convention as
-- `Codes/CaseMatrix.lean`).
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {k : ℕ}

/-! ## 1. A general lemma: adding an edge does not break C1 -/

/-- The cut size is **monotone** in the edge list: appending one edge never makes any cut
smaller (a cut can only gain edges). -/
theorem cutSize_append_le (L : List (Fin k × Fin k)) (e : Fin k × Fin k)
    (S : Finset (Fin k)) :
    cutSize L S ≤ cutSize (L ++ [e]) S := by
  rw [cutSize, cutSize, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

/-- **C1 is closed under adding an edge**: an edge list satisfying C1 still satisfies it
after any edge is appended. -/
theorem expansionOne_append {L : List (Fin k × Fin k)} (h : HasExpansionOne L)
    (e : Fin k × Fin k) : HasExpansionOne (L ++ [e]) := by
  intro S
  exact le_trans (h S) (cutSize_append_le L e S)

/-- C1 is closed under appending a **whole list** of edges. -/
theorem expansionOne_append_list {L M : List (Fin k × Fin k)}
    (h : HasExpansionOne L) : HasExpansionOne (L ++ M) := by
  induction M generalizing L with
  | nil => simpa using h
  | cons e rest ih =>
      have h1 : HasExpansionOne ((L ++ [e]) ++ rest) := ih (expansionOne_append h e)
      simpa [List.append_assoc] using h1

/-! ## 2. The star: $m$ vertices, $m-1$ edges -/

/-- The star graph: centre `0`, leaves `1..k` (defined on `Fin (k+1)`, so `k+1` vertices
and `k` edges). -/
def starEdges (k : ℕ) : List (Fin (k + 1) × Fin (k + 1)) :=
  (List.finRange k).map (fun i => ((0 : Fin (k + 1)), i.succ))

/-- The star satisfies C1 ($3$ vertices, $2$ edges). -/
theorem expansionOne_star_two : HasExpansionOne (starEdges 2) := by decide

/-- The star satisfies C1 ($4$ vertices, $3$ edges). -/
theorem expansionOne_star_three : HasExpansionOne (starEdges 3) := by decide

/-- The star satisfies C1 ($5$ vertices, $4$ edges). -/
theorem expansionOne_star_four : HasExpansionOne (starEdges 4) := by decide

/-- The star satisfies C1 ($6$ vertices, $5$ edges). -/
theorem expansionOne_star_five : HasExpansionOne (starEdges 5) := by decide

/-- The star satisfies C1 ($7$ vertices, $6$ edges). -/
theorem expansionOne_star_six : HasExpansionOne (starEdges 6) := by decide

/-! ## 3. The star plus chords: a witness with $m-1+r$ edges (derived from monotonicity,
without a case-by-case check) -/

/-- $7$ vertices, $9$ edges: the star plus the $3$ chords $(1,2),(1,3),(1,4)$ satisfies
C1. Against the $21$ edges of $K_7$ -- the same C1 at $3/7$ of the cost. -/
theorem expansionOne_seven_edges_nine :
    HasExpansionOne (starEdges 6 ++
      [((1 : Fin 7), 2), ((1 : Fin 7), 3), ((1 : Fin 7), 4)]) :=
  expansionOne_append_list expansionOne_star_six

/-! ## 4. The family form: the star satisfies C1 for **every** $k$

The statements above are decided for each concrete $m$. Here that "per-$m$" is removed.

**The route asks for a lower bound, not the exact cut formula** -- this is the key that
makes the statement provable. Every edge of the star is $(0,v)$, so the vertices $v$ with
an endpoint on either side of $S$ and $S^{\mathsf c}$ give **distinct** crossing edges:

* when $0 \in S$, every $v \notin S$ (with $v \ne 0$) gives a crossing edge, $k+1-|S|$ of
  them in all;
* when $0 \notin S$, every $v \in S$ gives a crossing edge, $|S|$ of them in all.

Both are $\ge \min(|S|, k+1-|S|)$. The crossing edges are collected into a `Finset.image`,
whose cardinality is counted with `card_image_of_injective` and then transferred to
`cutSize` with `List.toFinset_card_le`. -/

/-- The star's edge list contains $(0,v)$ whenever $v \ne 0$. -/
theorem starEdges_mem_of_ne_zero {k : ℕ} {v : Fin (k + 1)} (hv : v ≠ 0) :
    ((0 : Fin (k + 1)), v) ∈ starEdges k := by
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hv
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

/-- The star satisfies C1 **for every $k$**. The per-$m$ decisions above are its special
cases. -/
theorem expansionOne_star_gen (k : ℕ) : HasExpansionOne (starEdges k) := by
  intro S
  -- inject the "crossing edges" into the filtered list, so that only a lower bound is
  -- counted
  have key : ∀ T : Finset (Fin (k + 1)),
      (∀ v ∈ T, v ≠ 0) →
      (∀ v ∈ T, v ∈ S ↔ ¬ (0 : Fin (k + 1)) ∈ S) →
      T.card ≤ cutSize (starEdges k) S := by
    intro T hne hcross
    have hinj : Function.Injective (fun v : Fin (k + 1) =>
        (((0 : Fin (k + 1)), v) : Fin (k+1) × Fin (k+1))) :=
      fun a b hab => by simpa using hab
    rw [← Finset.card_image_of_injective T hinj]
    refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨starEdges_mem_of_ne_zero (hne v hv), ?_⟩
    by_cases h0 : (0 : Fin (k + 1)) ∈ S
    · have hv' : v ∉ S := fun h => (hcross v hv).mp h h0
      simp [h0, hv']
    · have hv' : v ∈ S := (hcross v hv).mpr h0
      simp [h0, hv']
  by_cases h0 : (0 : Fin (k + 1)) ∈ S
  · -- the centre lies in `S`: count the `Sᶜ` side, `k+1-|S|` edges in all
    have hle := key Sᶜ
      (fun v hv => by
        rw [Finset.mem_compl] at hv
        exact fun h => hv (h ▸ h0))
      (fun v hv => by
        rw [Finset.mem_compl] at hv
        exact ⟨fun h => absurd h hv, fun h => absurd h0 h⟩)
    rw [Finset.card_compl, Fintype.card_fin] at hle
    exact le_trans (min_le_right _ _) hle
  · -- the centre is not in `S`: count the `S` side, `|S|` edges in all
    have hle := key S
      (fun v hv => fun h => h0 (h ▸ hv))
      (fun v hv => ⟨fun _ => h0, fun _ => hv⟩)
    exact le_trans (min_le_left _ _) hle

end QECCertificates
