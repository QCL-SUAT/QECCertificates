/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB18Anchor
import QECCertificates.Codes.Gauging
import QECCertificates.GF2.RankEchelon

/-!
# A gauging instance in the BB family: $[[18,4,4]]$ through a $K_4$ ancilla graph $\to$ $[[24,3,4]]$

This module is a **concrete gauging instance**: it promotes a weight-4 X-type logical
operator $L$ of the BB $[[18,4,4]]$ code to a stabilizer, with the ancilla graph taken to be
$K_4$ (its vertices are the 4 support qubits of $L$), and obtains

$$[[18,4,4]] \;\longrightarrow\; [[24,3,4]],$$

so $k$ drops by exactly one while the distance is preserved. This is the **realisation** of
the three representation-level theorems of `Codes/Gauging.lean` (`deformX_css` preserving
compatibility, $L=\prod_v A_v$ in `gauss_prod_eq_vertex_prod`, and the drop by exactly one
in `deformX_k`) on one and the same instance, and it is also the smallest nontrivial
concrete instance of spacelike gauging.

## Construction (line by line with an independent Python implementation of the same route)

* the ancilla graph $K_4$: its 4 vertices are the support qubits of $L$ and each of its
  6 edges carries one ancilla (numbered $18..23$);
* the Gauss law $A_v = X_v\prod_{e\ni v} X_e$ ($v \in V$), whose product
  $\prod_v A_v$ cancels pairwise on the ancillas and is **exactly $L$**;
* X checks = the original $H_X$ (9 rows) + $A_v$ (4 rows);
* Z checks = the original Z rows, whose intersection with $L$ is paired into edges inside
  $K_4$ and then given an ancilla (9 rows), plus the fluxes $B_p$ on a cycle basis of
  $K_4$ (3 rows).

## Main results (all `by decide` inside the kernel)

* `bb24_k`: $24-11-10=3$, the **drop by exactly one** (compare `deformX_k`);
* `bb24_dx` / `bb24_dz`: the distance on both sides is **exactly 4** (lower bound: the
  weight-bounded candidate list is empty, through the `List`-shaped entry point
  `eq_minWeight_of_lightCand_nil`, which avoids the O(N²) deduplication of `List.toFinset`;
  upper bound: an explicit weight-4 witness together with a dual witness pairing to 1).

## Relation to the numerical side

An independent preliminary study using MaxSAT, MILP and brute force reports the same
readings ($n=24$, $k=3$, $d=4$, `css_orthogonal`, `L_equals_prod_A`).

## The gauging step itself ($\S$4 and $\S$5)

The two parity-check matrices of $\S$1–$\S$3 are **literal matrices**. Section 4 moves the
**construction** of "base code + $L$ + $K_4$ $\to$ gauged matrices" into the kernel: the
Gauss laws $A_v$, the paired edges (a T-join) and the flux cycle basis are all **built**
from the vertex, edge and cycle data of $K_4$, and the constructed matrices agree with the
literal ones component by component (`bb24HxC_eq` / `bb24HzC_eq`). The structural theorems
fall into three parts: **the sum of the Gauss laws equals the logical operator being
gauged** (`bb24_gauss_sum`, the ancillas cancelling pairwise), **the gauged logical enters
the parity-check row space** (`bb24L_mem_rowSpace`, the literal meaning at the row-space
level of "promoting $L$ to a check"), and **the dimensional drop by one by the theorem
route** (`bb18_gauged_drop`, an instance of `deformX_k` whose hypothesis is discharged by
the kernel). The claim that "the gauging step itself is checked numerically" therefore
drops off the boundary list of this instance: the whole chain from the base code to the
deformed code lives inside the kernel.
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## Parity-check matrices (assembled from row lists) -/

/-- The X-type checks $H_X'$ of the gauged code (the original $H_X$ 9 rows plus the Gauss
laws $A_v$ 4 rows). -/
def bb24Hx : Matrix (Fin 13) (Fin 24) (ZMod 2) :=
  Matrix.of ![
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 24),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 24),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 24),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 24),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 24),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 24),
    (e 0 + e 18 + e 19 + e 20 : Vec 24),
    (e 2 + e 18 + e 21 + e 22 : Vec 24),
    (e 6 + e 19 + e 21 + e 23 : Vec 24),
    (e 9 + e 20 + e 22 + e 23 : Vec 24)]

/-- The Z-type checks $H_Z'$ of the gauged code (the deformed Z checks 9 rows plus the
fluxes 3 rows). -/
def bb24Hz : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  Matrix.of ![
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 + e 20 : Vec 24),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 + e 22 : Vec 24),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 + e 18 : Vec 24),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 + e 23 : Vec 24),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 + e 19 : Vec 24),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 + e 21 : Vec 24),
    (e 18 + e 19 + e 21 : Vec 24),
    (e 18 + e 20 + e 21 + e 23 : Vec 24),
    (e 21 + e 22 + e 23 : Vec 24)]

/-- The list of X-check rows (literals, row for row the same as `bb24Hx`; `bb24_ofFn_x`
pins the two together). -/
def bb24Rx : List (Vec 24) :=
  [(e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 24),
   (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 24),
   (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 24),
   (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 24),
   (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
   (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
   (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 24),
   (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
   (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 24),
   (e 0 + e 18 + e 19 + e 20 : Vec 24),
   (e 2 + e 18 + e 21 + e 22 : Vec 24),
   (e 6 + e 19 + e 21 + e 23 : Vec 24),
   (e 9 + e 20 + e 22 + e 23 : Vec 24)]

/-- The list of Z-check rows (literals, row for row the same as `bb24Hz`). -/
def bb24Rz : List (Vec 24) :=
  [(e 0 + e 1 + e 3 + e 9 + e 11 + e 15 + e 20 : Vec 24),
   (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 + e 22 : Vec 24),
   (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 + e 18 : Vec 24),
   (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 + e 23 : Vec 24),
   (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
   (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
   (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 + e 19 : Vec 24),
   (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
   (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 + e 21 : Vec 24),
   (e 18 + e 19 + e 21 : Vec 24),
   (e 18 + e 20 + e 21 + e 23 : Vec 24),
   (e 21 + e 22 + e 23 : Vec 24)]

/-- The X-type witness: a weight-4 X logical operator ($\in \ker H_X'$). -/
def bb24XW : Vec 24 := (e 3 + e 4 + e 10 + e 11 : Vec 24)

/-- The Z-type witness: a weight-4 Z logical operator ($\in \ker H_Z'$). -/
def bb24ZW : Vec 24 := (e 0 + e 1 + e 7 + e 10 : Vec 24)

/-- A dual witness for `bb24XW`: it lies $\in \ker H_Z'$ and pairs with `bb24XW` to give
1. -/
def bb24XWdual : Vec 24 := (e 1 + e 2 + e 3 + e 5 + e 6 + e 7 : Vec 24)

/-- A dual witness for `bb24ZW`: it lies $\in \ker H_X'$ and pairs with `bb24ZW` to give
1. -/
def bb24ZWdual : Vec 24 := (e 3 + e 4 + e 10 + e 11 : Vec 24)

/-! ## Row-list bridge (the matrices are assembled from row lists; this only pins the `List.ofFn` form) -/

theorem bb24_ofFn_x : List.ofFn (fun i => bb24Hx i) = bb24Rx := by decide
theorem bb24_ofFn_z : List.ofFn (fun i => bb24Hz i) = bb24Rz := by decide

/-! ## Dimension: $k$ drops by exactly one -/

/-- **The dimension of [[24,3,4]]**: $24 - 11 - 10 = 3$ (against $k=4$ for the base code
$[[18,4,4]]$).

The reduction goes through the **append-only echelon form** `rankEchelon` of
`GF2/RankEchelon.lean`: its pivot rows carry no back-substitution, so a new pivot row is
never copied into every old row. That copying is exactly what makes the cost of `rowReduce`
grow multiplicatively with each round at width 24, failing to converge from row 7 onwards
after more than 200 s. The bridge theorem `rankEchelon_eq_length_rowReduce` guarantees that
the two reductions give **the same rank**, so the **statement of this theorem is still
written in the `rowReduce` form** and is word for word comparable with the other `_k`
theorems; only the evaluation path is exchanged, not the mathematical content. With the
reduction down to milliseconds, no per-theorem heartbeat budget is needed any more. -/
theorem bb24_k : 24 - (rowReduce (List.ofFn fun i => bb24Hx i)).length
    - (rowReduce (List.ofFn fun i => bb24Hz i)).length = 3 := by
  rw [bb24_ofFn_x, bb24_ofFn_z]
  simp only [← rankEchelon_eq_length_rowReduce]
  decide

/-! ## Distance: exactly 4 on both sides (the lower bound uses the **echelon backend**)

`lightCand` in `GF2/LowerBound.lean` uses `inSpanB`, and `inSpanB` runs `rowReduce`
internally: at width 24 that costs **more than 200 s per candidate**, so 2325 candidates
cannot get through (a measurement reached 80 GB without converging).

Here **the same candidate set** is moved to `inSpanEch` (the echelon backend of
`GF2/RankEchelon.lean`, milliseconds) and the implication "the candidates are empty
$\Rightarrow$ the distance lower bound" is proved inside this file, mirroring the
arrangement of `lowerHyp_of_lightCand_nil`. **The core module `GF2/LowerBound.lean` is
untouched.** -/

/-- The light-operator predicate for BB24 (echelon backend): nonzero weight, commuting with
`M₁`, and not in the row space of `M₂`. -/
abbrev bb24Light {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (v : Vec 24) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧ inSpanEch (List.ofFn fun i => M₂ i) v = false

/-- The candidate set of light operators for BB24: those of weight $\le 3$ (that is,
$< d = 4$). -/
def bb24LightCand {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2)) :
    List (Vec 24) :=
  (lightVecs 24 3).filter (fun v => decide (bb24Light M₁ M₂ v))

/-- **Lower-bound certificate (X side)**: the candidate list is empty. -/
theorem bb24_lightCand_x : bb24LightCand bb24Hx bb24Hz = [] := by decide

/-- **Lower-bound certificate (Z side)**: the candidate list is empty. -/
theorem bb24_lightCand_z : bb24LightCand bb24Hz bb24Hx = [] := by decide

/-- **Lower-bound hypothesis** (mirroring `lowerHyp_of_lightCand_nil`): empty candidates
$\Rightarrow$ distance $\ge 4$. -/
theorem bb24_lowerHyp {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (h : bb24LightCand M₁ M₂ = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → 4 ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < 4 := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.rowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs 24 (4 - 1) := by
    refine mem_lightVecs 24 (4 - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ bb24LightCand M₁ M₂ := by
    unfold bb24LightCand
    rw [List.mem_filter]
    refine ⟨hcov, ?_⟩
    rw [decide_eq_true_eq]
    exact ⟨hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanEch_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem

/-- **Distance 4 on the X side** (empty candidate list for the lower bound, plus an
explicit weight-4 witness for the upper bound and a dual witness pairing to 1).

Lower bound: `bb24LightCand bb24Hx bb24Hz = []` (echelon backend, `by decide`);
upper bound: the explicit weight-4 logical operator `bb24XW`.

(The lower bound uses the `echelonFrom` backend: deciding the candidate set takes
milliseconds and does not read the rank of a wide matrix, whereas the `rowReduce` backend
of `inSpanB` performs one wide-matrix elimination per candidate and was measured at 80 GB
without converging.) -/
theorem bb24_dx : min_weight_ker_not_mem_rowspace bb24Hx bb24Hz = 4 :=
  eq_minWeight_of_bounds bb24Hx bb24Hz (by decide) (E := bb24XW)
    (mem_ker_of_inKerB bb24Hx (by decide))
    (not_mem_rowSpace_of_dualCheck bb24Hz (w := bb24XWdual) (by decide) (by decide))
    (by decide)
    (bb24_lowerHyp bb24Hx bb24Hz bb24_lightCand_x)

/-- **Distance 4 on the Z side** (as on the X side, with the lower bound using the
candidate set of the echelon backend). -/
theorem bb24_dz : min_weight_ker_not_mem_rowspace bb24Hz bb24Hx = 4 :=
  eq_minWeight_of_bounds bb24Hz bb24Hx (by decide) (E := bb24ZW)
    (mem_ker_of_inKerB bb24Hz (by decide))
    (not_mem_rowSpace_of_dualCheck bb24Hx (w := bb24ZWdual) (by decide) (by decide))
    (by decide)
    (bb24_lowerHyp bb24Hz bb24Hx bb24_lightCand_z)

/-! ## 4. Construction of the gauging step (building both parity-check matrices from bb18L and K4) -/

/-- The weight-4 X-type logical operator being gauged (support $\{0,2,6,9\}$). -/
def bb18L : Vec 18 := e 0 + e 2 + e 6 + e 9

/-- The four vertices of K4, namely the support qubits of `bb18L`. -/
def k4Vert : Fin 4 → Fin 18 := ![(0 : Fin 18), 2, 6, 9]

/-- The six edges of K4 (an enumeration of vertex pairs). -/
def k4Ends : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The ancilla slot of each edge (18..23). -/
def k4EdgeSlot : Fin 6 → Fin 24 := ![18, 19, 20, 21, 22, 23]

/-- Zero-pad an 18-coordinate data vector into 24 coordinates (the ancilla slots receive
zeros). -/
def bb24Pad (v : Vec 18) : Vec 24 :=
  fun j => if h : j.val < 18 then v ⟨j.val, h⟩ else 0

/-- The Gauss law $A_v = X_v\prod_{e\ni v}X_e$ (in row-vector form: the vertex slot plus
the ancilla slots of the incident edges). -/
def bb24Av (v : Fin 4) : Vec 24 :=
  bb24Pad (e (k4Vert v)) + ∑ f : Fin 6,
    (if (k4Ends f).1 = v ∨ (k4Ends f).2 = v then e (k4EdgeSlot f) else 0)

/-- The paired edge of a base-code Z row: the intersection of row $i$ with
$\mathrm{supp}(L)$ is exactly the pair of endpoints of one edge (`none` means the
intersection is empty). -/
def bb24MuZ : Fin 9 → Option (Fin 6) :=
  ![some 2, some 4, some 0, some 5, none, none, some 1, none, some 3]

/-- A deformed Z row is the base-code row (zero-padded) plus its paired edge. -/
def bb24DzRow (i : Fin 9) : Vec 24 :=
  bb24Pad (bb18Hz i) + match bb24MuZ i with
    | some f => e (k4EdgeSlot f)
    | none => 0

/-- A cycle basis of K4 (the edge sets of the three flux checks). -/
def k4Cycles : Fin 3 → List (Fin 6) := ![[0, 1, 3], [0, 2, 3, 5], [3, 4, 5]]

/-- The flux check $B_p$: the sum of the ancilla slots of the edges on the cycle. -/
def bb24Bp (p : Fin 3) : Vec 24 :=
  (k4Cycles p).foldr (fun f acc => e (k4EdgeSlot f) + acc) 0

/-- **The constructed X parity-check matrix**: the 9 base-code rows (zero-padded) plus the
4 Gauss laws. -/
def bb24HxC : Matrix (Fin 13) (Fin 24) (ZMod 2) := Matrix.of
  ![bb24Pad (bb18Hx 0), bb24Pad (bb18Hx 1), bb24Pad (bb18Hx 2), bb24Pad (bb18Hx 3),
    bb24Pad (bb18Hx 4), bb24Pad (bb18Hx 5), bb24Pad (bb18Hx 6), bb24Pad (bb18Hx 7),
    bb24Pad (bb18Hx 8), bb24Av 0, bb24Av 1, bb24Av 2, bb24Av 3]

/-- **The constructed Z parity-check matrix**: the 9 deformed Z rows plus the 3
fluxes. -/
def bb24HzC : Matrix (Fin 12) (Fin 24) (ZMod 2) := Matrix.of
  ![bb24DzRow 0, bb24DzRow 1, bb24DzRow 2, bb24DzRow 3, bb24DzRow 4, bb24DzRow 5,
    bb24DzRow 6, bb24DzRow 7, bb24DzRow 8, bb24Bp 0, bb24Bp 1, bb24Bp 2]

/-- **The operator being gauged really is a logical operator**: it lies in the kernel, not
in the row space, and has weight exactly 4. -/
theorem bb18L_logical :
    inKerB bb18Hz bb18L = true ∧ inSpanB bb18Rx bb18L = false ∧ hammingNorm bb18L = 4 := by
  decide

/-- **The sum of the Gauss laws equals the logical operator being gauged** (the ancilla
slots cancel pairwise and the vertex slots leave $L$). -/
theorem bb24_gauss_sum : ∑ v : Fin 4, bb24Av v = bb24Pad bb18L := by
  decide

/-- **The constructed matrix is the literal matrix (X side).** -/
theorem bb24HxC_eq : bb24HxC = bb24Hx := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- **The constructed matrix is the literal matrix (Z side).** -/
theorem bb24HzC_eq : bb24HzC = bb24Hz := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## 5. Structural theorems -/

/-- **The gauged logical enters the parity-check row space**: $L$ (zero-padded) is a row
combination of the X checks of the gauged code, namely the sum of the four Gauss laws. This
is the literal meaning, at the level of the row space, of gauging as "promoting a logical
operator to a check". -/
theorem bb24L_mem_rowSpace : bb24Pad bb18L ∈ bb24Hx.rowSpace := by
  rw [Matrix.rowSpace_eq_spanL_ofFn, bb24_ofFn_x]
  have h1 : bb24Pad bb18L ∈ spanL [bb24Av 0, bb24Av 1, bb24Av 2, bb24Av 3] := by
    rw [← bb24_gauss_sum]
    refine Submodule.sum_mem _ fun v _ => subset_spanL ?_
    fin_cases v <;> decide
  have hsub : spanL [bb24Av 0, bb24Av 1, bb24Av 2, bb24Av 3] ≤ spanL bb24Rx := by
    refine spanL_mono_of_subset ?_
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | h4
    · decide
    · decide
    · decide
    · rcases h4 with rfl | hnil
      · decide
      · exact nomatch hnil
  exact hsub h1

/-- **The paired edges really do pair**: for a row with a paired edge, its intersection
with $\mathrm{supp}(L)$ is exactly the two endpoints of that edge; for a row without one the
intersection is empty. -/
theorem bb24_deformZ_matching (i : Fin 9) (f : Fin 6) (h : bb24MuZ i = some f) :
    ∀ b : Fin 18, bb18Hz i b * bb18L b = 1 ↔
      b = k4Vert (k4Ends f).1 ∨ b = k4Vert (k4Ends f).2 := by
  fin_cases i <;> fin_cases f <;> first
    | exact absurd h (by decide)
    | decide

theorem bb24_deformZ_none (i : Fin 9) (h : bb24MuZ i = none) :
    ∀ b : Fin 18, bb18Hz i b * bb18L b = 0 := by
  fin_cases i <;> first
    | exact absurd h (by decide)
    | decide

/-- **Every flux commutes with every Gauss law**: each cycle has even degree at each
vertex. -/
theorem bb24_flux_commute : ∀ (p : Fin 3) (v : Fin 4), bb24Bp p ⬝ᵥ bb24Av v = 0 := by
  decide

/-- **The constructed code is a CSS code**: the two families of checks are row-wise
orthogonal. -/
theorem bb24_orth : ∀ i j, bb24Hx i ⬝ᵥ bb24Hz j = 0 := by
  decide

/-- **The dimensional drop at the representation level (theorem route)**: appending $L$ to
the base-code list of X rows drops $k$ by exactly one, an instance of `deformX_k` whose
hypothesis is discharged by the kernel. -/
theorem bb18_gauged_drop :
    18 - (rowReduce (bb18Rx ++ [bb18L])).length - (rowReduce bb18Rz).length
      = (18 - (rowReduce bb18Rx).length - (rowReduce bb18Rz).length) - 1 :=
  deformX_k ((inSpanB_eq_false_iff bb18Rx bb18L).mp bb18L_logical.2.1)

/-- **$k=3$ at the gauged representation level**: the drop by one applied to the base code
with $k=4$. -/
theorem bb18_gauged_k :
    18 - (rowReduce (bb18Rx ++ [bb18L])).length - (rowReduce bb18Rz).length = 3 := by
  have h4 := bb18_k
  rw [bb18_ofFn_x, bb18_ofFn_z] at h4
  have h := bb18_gauged_drop
  omega


end QECCertificates
