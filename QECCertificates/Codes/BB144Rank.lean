/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.RankEchelon
import QECCertificates.Codes.BB144Witness

/-! # The dimension of $[[144,12,12]]$

`Codes/BB144Witness.lean` records the size of this code: literal $72\times144$ matrices whose
dot products take about five minutes of kernel reduction. Row reduction is even less
feasible at this width, so that module never states a rank, and the companion paper's table
has always recorded the dimension of the last row as "from the original presentation". This
module supplies it, with **two cheap criteria on each side** (the general criterion lives in
`GF2/RankEchelon.lean`):

* **Lower bound**: `bb144CertXD` / `bb144CertZD` have 66 rows each, every row being a GF(2)
  sum of original check rows (`bb144RowSum`), with pairwise distinct pivot columns.
  Membership is an algebraic proof (one proof for all 66 rows, independent of the width) and
  the pivots are distinct by finite decision, giving $66 \le \dim$.
* **Upper bound**: the head consists of 66 linearly independent original rows
  (`bb144RxHeadIdx`), and each of the remaining six rows equals a GF(2) sum of rows of the
  head (the family `bb144RelX*`, decided bit by bit), so the whole row list is spanned by
  the 66 rows of the head, giving $\dim \le 66$.

The head is **not a prefix**: the first 66 rows of $H_X$ have rank only 64, whereas `spanL`
sees the set of elements and not their order, so it suffices to take the original rows that
produced a pivot during elimination. This is precisely where the upper bound of this module
differs from the prefix form.

The two sides together give $\operatorname{rank}H_X=\operatorname{rank}H_Z=66$, hence

$$k \;=\; n-\operatorname{rank}H_X-\operatorname{rank}H_Z \;=\; 144-66-66 \;=\; 12,$$

matching the $[[144,12,12]]$ reported in the original literature: **the dimension holds
inside the kernel**, rather than resting on the original presentation. The width bound is
recorded as well: the cost of the rank check is $O(n\cdot\text{rank})$, independent of
$2^n$.

**Boundary (unrelated to the dimension, and unchanged)**: the treatment of the distance side
is unchanged. The witnesses give $d\le12$, and the lower bound restates an independently
formalized per-family argument in the GF(2) language of this library, proving entry by entry
that the two matrices agree (`bb144Hx_eq_LE_X` in `Codes/BB144Literal.lean`); what this
development contributes on that side is the restatement and the identity.

## Data and reproducibility

The index subsets and pivot columns were computed by an independent external script (Julia,
no external dependencies, byte-for-byte reproducible when re-run), taking as input a
plain-text dump of the matrices as printed from the library by `#eval`; they were then
checked by recomputing from the emitted data. **Consistency is backstopped by the kernel**:
the certificate rows are sums of the original rows in Lean and the relations are bitwise
equalities, so if the input data disagreed with the library the relevant `decide` calls
would fail on the spot.
-/

namespace QECCertificates

open scoped BigOperators

-- 判定是 66×66 与 72×144 量级的逐位归约，放宽内核预算（与 `Codes/BB144Witness.lean` 同款）
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ## Preliminaries: row lists and partial sums

`bb144Hx` is a `Matrix`, and `Matrix` is a semireducible def: at `implicit` transparency,
`List.map bb144Hx` reports that `Matrix (Fin 72) (Fin 144) (ZMod 2)` is not
`Fin 72 → Fin 144 → ZMod 2`. The rows are therefore extracted as a function first
(`bb144HxRow`), and only that is used from here on.
-/

/-- The `k`-th row of $H_X$ (row by row of `bb144Hx`, see above). -/
def bb144HxRow (k : Fin 72) : Vec 144 := bb144Hx k

/-- The `k`-th row of $H_Z$. -/
def bb144HzRow (k : Fin 72) : Vec 144 := bb144Hz k

/-- The original row list of $H_X$. -/
def bb144Rx : List (Vec 144) := List.ofFn bb144HxRow

/-- The original row list of $H_Z$. -/
def bb144Rz : List (Vec 144) := List.ofFn bb144HzRow

/-- The GF(2) sum of several rows of `H_X`. -/
def bb144RowSum (s : List (Fin 72)) : Vec 144 := (s.map bb144HxRow).sum

/-- The GF(2) sum of several rows of `H_Z`. -/
def bb144RowSumZ (s : List (Fin 72)) : Vec 144 := (s.map bb144HzRow).sum

/-- **A partial sum of rows of `H_X` lies in the row space** (a structural proof: each term
is an original row and the sum uses `add_mem`). -/
lemma bb144RowSum_mem_spanL (s : List (Fin 72)) : bb144RowSum s ∈ spanL bb144Rx := by
  have hrow : ∀ k : Fin 72, bb144HxRow k ∈ spanL bb144Rx := fun k =>
    subset_spanL (by rw [bb144Rx]; exact List.mem_ofFn.mpr ⟨k, rfl⟩)
  unfold bb144RowSum
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (hrow k) ih

/-- **A partial sum of rows of `H_Z` lies in the row space**. -/
lemma bb144RowSumZ_mem_spanL (s : List (Fin 72)) : bb144RowSumZ s ∈ spanL bb144Rz := by
  have hrow : ∀ k : Fin 72, bb144HzRow k ∈ spanL bb144Rz := fun k =>
    subset_spanL (by rw [bb144Rz]; exact List.mem_ofFn.mpr ⟨k, rfl⟩)
  unfold bb144RowSumZ
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (hrow k) ih

/-! ## X side, lower bound: a 66-row echelon certificate -/

/-- The raw data of the X-side certificate: 66 pairs of an index subset of original rows and
a pivot column, computed over GF(2) by the external script (the row order is the order of
the append-only echelon form). -/
def bb144CertXRaw : List (List (Fin 72) × Fin 144) :=
  [([0], 1),
   ([1], 2),
   ([2], 3),
   ([3], 4),
   ([4], 0),
   ([0, 1, 2, 3, 4, 5], 18),
   ([6], 7),
   ([7], 8),
   ([8], 9),
   ([9], 10),
   ([10], 6),
   ([6, 7, 8, 9, 10, 11], 24),
   ([12], 13),
   ([13], 14),
   ([14], 15),
   ([15], 16),
   ([16], 12),
   ([12, 13, 14, 15, 16, 17], 30),
   ([18], 19),
   ([19], 20),
   ([20], 21),
   ([21], 22),
   ([0, 1, 2, 3, 4, 5, 18, 20, 22], 36),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23], 37),
   ([24], 25),
   ([25], 26),
   ([26], 27),
   ([27], 28),
   ([6, 7, 8, 9, 10, 11, 24, 26, 28], 42),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29], 43),
   ([30], 31),
   ([31], 32),
   ([32], 33),
   ([33], 34),
   ([12, 13, 14, 15, 16, 17, 30, 32, 34], 48),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35], 49),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23, 36], 38),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23, 36, 37], 41),
   ([38], 39),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23, 36, 37, 39], 40),
   ([18, 19, 20, 21, 22, 23, 36, 38, 40], 54),
   ([18, 19, 20, 21, 22, 23, 37, 39, 41], 55),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29, 42], 44),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29, 42, 43], 47),
   ([44], 45),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29, 42, 43, 45], 46),
   ([24, 25, 26, 27, 28, 29, 42, 44, 46], 60),
   ([24, 25, 26, 27, 28, 29, 43, 45, 47], 61),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35, 48], 50),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35, 48, 49], 53),
   ([50], 51),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35, 48, 49, 51], 52),
   ([30, 31, 32, 33, 34, 35, 48, 50, 52], 66),
   ([30, 31, 32, 33, 34, 35, 49, 51, 53], 67),
   ([0, 1, 2, 3, 5, 18, 20, 21, 22, 37, 39, 40, 54], 5),
   ([5, 18, 19, 20, 21, 22, 23, 37, 39, 41, 54, 55], 23),
   ([1, 2, 3, 4, 18, 20, 37, 38, 39, 40, 54, 56], 72),
   ([1, 5, 18, 19, 20, 21, 37, 41, 54, 55, 56, 57], 74),
   ([0, 2, 19, 20, 21, 22, 36, 38, 55, 56, 57, 58], 75),
   ([2, 4, 18, 21, 22, 23, 38, 40, 54, 57, 58, 59], 73),
   ([1, 3, 6, 7, 8, 9, 11, 20, 21, 22, 23, 24, 26, 27, 28, 37, 39, 43, 45, 46, 56, 57, 58, 59, 60], 11),
   ([1, 2, 3, 4, 11, 18, 20, 24, 25, 26, 27, 28, 29, 37, 38, 39, 40, 43, 45, 47, 54, 56, 60, 61], 29),
   ([3, 5, 7, 8, 9, 10, 18, 19, 22, 23, 24, 26, 39, 41, 43, 44, 45, 46, 54, 55, 58, 59, 60, 62], 78),
   ([0, 4, 8, 9, 10, 11, 18, 19, 20, 23, 25, 27, 36, 40, 44, 45, 46, 47, 54, 55, 56, 59, 61, 63], 79),
   ([1, 5, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 24, 26, 30, 32, 33, 34, 37, 41, 43, 44, 45, 46, 49, 51, 52, 54, 55, 56, 57, 60, 62, 66], 17),
   ([0, 1, 2, 5, 7, 11, 17, 18, 22, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 41, 43, 47, 49, 51, 53, 54, 58, 60, 61, 62, 63, 66, 67], 35)]

/-- **The X-side certificate**: each index subset is replaced by the GF(2) sum of the
corresponding original rows, with the pivot columns carried over unchanged. -/
def bb144CertXD : List (PivRow 144) := bb144CertXRaw.map (fun q => (bb144RowSum q.1, q.2))

/-- **Every row of the certificate is a GF(2) sum of original rows**, hence lies in the
original row space. All 66 rows are covered by **a single** proof, which uses the algebra of
term-by-term addition (`bb144RowSum_mem_spanL`) and is **independent of the width**; this is
what makes the argument feasible at a large width. -/
theorem bb144CertX_mem : ∀ v ∈ rowList bb144CertXD, v ∈ spanL bb144Rx := by
  intro v hv
  unfold rowList at hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  unfold bb144CertXD at ha
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
  exact bb144RowSum_mem_spanL q.1

/-- The **indexed** form of the previous statement (used by
`length_le_finrank_spanL_of_certificate`). -/
theorem bb144CertX_get_mem (i : Fin bb144CertXD.length) :
    (bb144CertXD.get i).1 ∈ spanL bb144Rx :=
  bb144CertX_mem _ (by
    rw [rowList]
    exact List.mem_map.mpr ⟨_, List.get_mem _ i, rfl⟩)

/-- The echelon invariant of the certificate: every row takes the value 1 at its own pivot
column, and a later row takes the value 0 at the pivot columns of the earlier ones. -/
theorem bb144CertX_ech : EchSelf bb144CertXD ∧ EchPair bb144CertXD :=
  ⟨by unfold EchSelf; decide, by unfold EchPair; decide⟩

/-! ## X side, upper bound: the whole row list is spanned by 66 original rows -/

/-- The **head** used for the upper bound: 66 linearly independent original rows, namely the
rows that produced a pivot during elimination (the indices were selected over GF(2) by the
external script). `spanL` sees the set of elements and not their order, so the head need not
be a prefix: at width 144 the first 66 rows have rank only 64, and the prefix form does not
hold there. -/
def bb144RxHeadIdx : List (Fin 72) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
   12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
   36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 66, 67]

/-- The head as a row list. -/
def bb144RxHead : List (Vec 144) := bb144RxHeadIdx.map bb144HxRow

/-- The head has exactly 66 rows. -/
lemma bb144RxHead_length : bb144RxHead.length = 66 := by
  simp [bb144RxHead, bb144RxHeadIdx]

/-- Every original row in the head lies in the span of the head. -/
lemma bb144HxRow_mem_head (k : Fin 72) (hk : k ∈ bb144RxHeadIdx) :
    bb144HxRow k ∈ spanL bb144RxHead := by
  rw [bb144RxHead]
  exact subset_spanL (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- A sum of several rows of the head (all indices lying in the head) lies in the span of
the head. -/
lemma bb144RowSum_mem_head (s : List (Fin 72)) (hs : ∀ k ∈ s, k ∈ bb144RxHeadIdx) :
    bb144RowSum s ∈ spanL bb144RxHead := by
  unfold bb144RowSum
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (bb144HxRow_mem_head k (hs k (by simp)))
        (ih (fun k hk => hs k (by simp [hk])))

/-- Original row 64 is the GF(2) sum of 31 rows of the head (decided bit by bit). -/
theorem bb144RelX64 : bb144HxRow 64 = bb144RowSum [0, 1, 3, 4, 6, 7, 9, 10, 18, 19, 21, 22, 24, 25, 27, 28, 36, 37, 39, 40, 42, 43, 45, 46, 54, 55, 57, 58, 60, 61, 63] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelX64_mem : bb144HxRow 64 ∈ spanL bb144RxHead := by
  rw [bb144RelX64]
  exact bb144RowSum_mem_head _ (by decide)

/-- Original row 65 is the GF(2) sum of 31 rows of the head (decided bit by bit). -/
theorem bb144RelX65 : bb144HxRow 65 = bb144RowSum [0, 2, 3, 5, 6, 8, 9, 11, 18, 20, 21, 23, 24, 26, 27, 29, 36, 38, 39, 41, 42, 44, 45, 47, 54, 56, 57, 59, 60, 62, 63] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelX65_mem : bb144HxRow 65 ∈ spanL bb144RxHead := by
  rw [bb144RelX65]
  exact bb144RowSum_mem_head _ (by decide)

/-- Original row 68 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelX68 : bb144HxRow 68 = bb144RowSum [0, 4, 7, 11, 13, 14, 15, 16, 18, 19, 20, 23, 24, 25, 26, 27, 30, 32, 36, 40, 43, 47, 49, 50, 51, 52, 54, 55, 56, 59, 60, 61, 62, 63, 66] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelX68_mem : bb144HxRow 68 ∈ spanL bb144RxHead := by
  rw [bb144RelX68]
  exact bb144RowSum_mem_head _ (by decide)

/-- Original row 69 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelX69 : bb144HxRow 69 = bb144RowSum [0, 3, 4, 5, 7, 8, 9, 10, 14, 15, 16, 17, 20, 22, 24, 26, 31, 33, 36, 39, 40, 41, 43, 44, 45, 46, 50, 51, 52, 53, 56, 58, 60, 62, 67] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelX69_mem : bb144HxRow 69 ∈ spanL bb144RxHead := by
  rw [bb144RelX69]
  exact bb144RowSum_mem_head _ (by decide)

/-- Original row 70 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelX70 : bb144HxRow 70 = bb144RowSum [1, 5, 7, 8, 9, 10, 12, 13, 14, 17, 18, 19, 20, 21, 24, 26, 30, 34, 37, 41, 43, 44, 45, 46, 48, 49, 50, 53, 54, 55, 56, 57, 60, 62, 66] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelX70_mem : bb144HxRow 70 ∈ spanL bb144RxHead := by
  rw [bb144RelX70]
  exact bb144RowSum_mem_head _ (by decide)

/-- Original row 71 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelX71 : bb144HxRow 71 = bb144RowSum [0, 2, 8, 9, 10, 11, 12, 13, 14, 15, 19, 20, 21, 22, 25, 27, 31, 35, 36, 38, 44, 45, 46, 47, 48, 49, 50, 51, 55, 56, 57, 58, 61, 63, 67] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelX71_mem : bb144HxRow 71 ∈ spanL bb144RxHead := by
  rw [bb144RelX71]
  exact bb144RowSum_mem_head _ (by decide)

/-- **The whole row list lies in the span of the head**: the rows of the head are in the head
one by one, and each of the remaining rows has a relation of its own. -/
theorem bb144Rx_mem_head : ∀ v ∈ bb144Rx, v ∈ spanL bb144RxHead := by
  intro v hv
  unfold bb144Rx at hv
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hv
  rw [← hj]
  fin_cases j
  · exact bb144HxRow_mem_head 0 (by decide)
  · exact bb144HxRow_mem_head 1 (by decide)
  · exact bb144HxRow_mem_head 2 (by decide)
  · exact bb144HxRow_mem_head 3 (by decide)
  · exact bb144HxRow_mem_head 4 (by decide)
  · exact bb144HxRow_mem_head 5 (by decide)
  · exact bb144HxRow_mem_head 6 (by decide)
  · exact bb144HxRow_mem_head 7 (by decide)
  · exact bb144HxRow_mem_head 8 (by decide)
  · exact bb144HxRow_mem_head 9 (by decide)
  · exact bb144HxRow_mem_head 10 (by decide)
  · exact bb144HxRow_mem_head 11 (by decide)
  · exact bb144HxRow_mem_head 12 (by decide)
  · exact bb144HxRow_mem_head 13 (by decide)
  · exact bb144HxRow_mem_head 14 (by decide)
  · exact bb144HxRow_mem_head 15 (by decide)
  · exact bb144HxRow_mem_head 16 (by decide)
  · exact bb144HxRow_mem_head 17 (by decide)
  · exact bb144HxRow_mem_head 18 (by decide)
  · exact bb144HxRow_mem_head 19 (by decide)
  · exact bb144HxRow_mem_head 20 (by decide)
  · exact bb144HxRow_mem_head 21 (by decide)
  · exact bb144HxRow_mem_head 22 (by decide)
  · exact bb144HxRow_mem_head 23 (by decide)
  · exact bb144HxRow_mem_head 24 (by decide)
  · exact bb144HxRow_mem_head 25 (by decide)
  · exact bb144HxRow_mem_head 26 (by decide)
  · exact bb144HxRow_mem_head 27 (by decide)
  · exact bb144HxRow_mem_head 28 (by decide)
  · exact bb144HxRow_mem_head 29 (by decide)
  · exact bb144HxRow_mem_head 30 (by decide)
  · exact bb144HxRow_mem_head 31 (by decide)
  · exact bb144HxRow_mem_head 32 (by decide)
  · exact bb144HxRow_mem_head 33 (by decide)
  · exact bb144HxRow_mem_head 34 (by decide)
  · exact bb144HxRow_mem_head 35 (by decide)
  · exact bb144HxRow_mem_head 36 (by decide)
  · exact bb144HxRow_mem_head 37 (by decide)
  · exact bb144HxRow_mem_head 38 (by decide)
  · exact bb144HxRow_mem_head 39 (by decide)
  · exact bb144HxRow_mem_head 40 (by decide)
  · exact bb144HxRow_mem_head 41 (by decide)
  · exact bb144HxRow_mem_head 42 (by decide)
  · exact bb144HxRow_mem_head 43 (by decide)
  · exact bb144HxRow_mem_head 44 (by decide)
  · exact bb144HxRow_mem_head 45 (by decide)
  · exact bb144HxRow_mem_head 46 (by decide)
  · exact bb144HxRow_mem_head 47 (by decide)
  · exact bb144HxRow_mem_head 48 (by decide)
  · exact bb144HxRow_mem_head 49 (by decide)
  · exact bb144HxRow_mem_head 50 (by decide)
  · exact bb144HxRow_mem_head 51 (by decide)
  · exact bb144HxRow_mem_head 52 (by decide)
  · exact bb144HxRow_mem_head 53 (by decide)
  · exact bb144HxRow_mem_head 54 (by decide)
  · exact bb144HxRow_mem_head 55 (by decide)
  · exact bb144HxRow_mem_head 56 (by decide)
  · exact bb144HxRow_mem_head 57 (by decide)
  · exact bb144HxRow_mem_head 58 (by decide)
  · exact bb144HxRow_mem_head 59 (by decide)
  · exact bb144HxRow_mem_head 60 (by decide)
  · exact bb144HxRow_mem_head 61 (by decide)
  · exact bb144HxRow_mem_head 62 (by decide)
  · exact bb144HxRow_mem_head 63 (by decide)
  · exact bb144RelX64_mem
  · exact bb144RelX65_mem
  · exact bb144HxRow_mem_head 66 (by decide)
  · exact bb144HxRow_mem_head 67 (by decide)
  · exact bb144RelX68_mem
  · exact bb144RelX69_mem
  · exact bb144RelX70_mem
  · exact bb144RelX71_mem

/-- **Upper bound on the rank**: the whole row list is spanned by the 66 rows of the
head. -/
theorem bb144_rankX_le : Module.finrank (ZMod 2) (spanL bb144Rx) ≤ 66 := by
  have h := finrank_spanL_le_of_mem_of_subset (A := bb144RxHead) (L := bb144Rx) bb144Rx_mem_head
  rwa [bb144RxHead_length] at h

/-- **Lower bound on the rank**: the 66 rows of the certificate are linearly independent and
all lie in the row space. -/
theorem bb144_rankX_ge : 66 ≤ Module.finrank (ZMod 2) (spanL bb144Rx) :=
  length_le_finrank_spanL_of_certificate bb144CertX_get_mem bb144CertX_ech.1 bb144CertX_ech.2

/-- **The row space of the X-side parity-check matrix has dimension 66**. -/
theorem bb144_rankX : Module.finrank (ZMod 2) (spanL bb144Rx) = 66 :=
  le_antisymm bb144_rankX_le bb144_rankX_ge

/-! ## Z side, lower bound: a 66-row echelon certificate -/

/-- The raw data of the Z-side certificate: 66 pairs of an index subset of original rows and
a pivot column, computed over GF(2) by the external script (the row order is the order of
the append-only echelon form). -/
def bb144CertZRaw : List (List (Fin 72) × Fin 144) :=
  [([0], 3),
   ([1], 4),
   ([2], 5),
   ([3], 0),
   ([4], 1),
   ([5], 2),
   ([3, 6], 9),
   ([4, 7], 10),
   ([5, 8], 11),
   ([0, 9], 6),
   ([1, 10], 7),
   ([2, 11], 8),
   ([0, 3, 9, 12], 15),
   ([1, 4, 10, 13], 16),
   ([2, 5, 11, 14], 17),
   ([0, 3, 6, 15], 12),
   ([1, 4, 7, 16], 13),
   ([2, 5, 8, 17], 14),
   ([3, 6, 9, 15, 18], 21),
   ([4, 7, 10, 16, 19], 22),
   ([5, 8, 11, 17, 20], 23),
   ([0, 6, 9, 12, 21], 18),
   ([1, 7, 10, 13, 22], 19),
   ([2, 8, 11, 14, 23], 20),
   ([3, 9, 12, 15, 21, 24], 27),
   ([4, 10, 13, 16, 22, 25], 28),
   ([5, 11, 14, 17, 23, 26], 29),
   ([0, 6, 12, 15, 18, 27], 24),
   ([1, 7, 13, 16, 19, 28], 25),
   ([2, 8, 14, 17, 20, 29], 26),
   ([9, 15, 18, 21, 27, 30], 33),
   ([10, 16, 19, 22, 28, 31], 34),
   ([11, 17, 20, 23, 29, 32], 35),
   ([6, 12, 18, 21, 24, 33], 30),
   ([7, 13, 19, 22, 25, 34], 31),
   ([8, 14, 20, 23, 26, 35], 32),
   ([0, 15, 21, 24, 27, 33, 36], 39),
   ([1, 16, 22, 25, 28, 34, 37], 40),
   ([2, 17, 23, 26, 29, 35, 38], 41),
   ([3, 12, 18, 24, 27, 30, 39], 36),
   ([4, 13, 19, 25, 28, 31, 40], 37),
   ([5, 14, 20, 26, 29, 32, 41], 38),
   ([3, 6, 21, 27, 30, 33, 39, 42], 45),
   ([4, 7, 22, 28, 31, 34, 40, 43], 46),
   ([5, 8, 23, 29, 32, 35, 41, 44], 47),
   ([0, 9, 18, 24, 30, 33, 36, 45], 42),
   ([1, 10, 19, 25, 31, 34, 37, 46], 43),
   ([2, 11, 20, 26, 32, 35, 38, 47], 44),
   ([0, 3, 9, 12, 27, 33, 36, 39, 45, 48], 51),
   ([1, 4, 10, 13, 28, 34, 37, 40, 46, 49], 52),
   ([2, 5, 11, 14, 29, 35, 38, 41, 47, 50], 53),
   ([0, 3, 6, 15, 24, 30, 36, 39, 42, 51], 48),
   ([1, 4, 7, 16, 25, 31, 37, 40, 43, 52], 49),
   ([2, 5, 8, 17, 26, 32, 38, 41, 44, 53], 50),
   ([3, 6, 9, 15, 18, 33, 39, 42, 45, 51, 54], 57),
   ([4, 7, 10, 16, 19, 34, 40, 43, 46, 52, 55], 58),
   ([5, 8, 11, 17, 20, 35, 41, 44, 47, 53, 56], 59),
   ([0, 6, 9, 12, 21, 30, 36, 42, 45, 48, 57], 54),
   ([1, 7, 10, 13, 22, 31, 37, 43, 46, 49, 58], 55),
   ([2, 8, 11, 14, 23, 32, 38, 44, 47, 50, 59], 56),
   ([3, 9, 12, 15, 21, 24, 39, 45, 48, 51, 57, 60], 73),
   ([4, 10, 13, 16, 22, 25, 40, 46, 49, 52, 58, 61], 74),
   ([5, 11, 14, 17, 23, 26, 41, 47, 50, 53, 59, 62], 75),
   ([0, 6, 12, 15, 18, 27, 36, 42, 48, 51, 54, 63], 72),
   ([0, 5, 6, 9, 11, 12, 14, 17, 21, 23, 26, 30, 36, 41, 42, 45, 47, 48, 50, 53, 57, 59, 62, 66], 79),
   ([0, 1, 6, 7, 10, 12, 13, 15, 18, 22, 27, 31, 36, 37, 42, 43, 46, 48, 49, 51, 54, 58, 63, 67], 78)]

/-- **The Z-side certificate**: each index subset is replaced by the GF(2) sum of the
corresponding original rows, with the pivot columns carried over unchanged. -/
def bb144CertZD : List (PivRow 144) := bb144CertZRaw.map (fun q => (bb144RowSumZ q.1, q.2))

/-- **Every row of the certificate is a GF(2) sum of original rows**, hence lies in the
original row space. All 66 rows are covered by **a single** proof, which uses the algebra of
term-by-term addition (`bb144RowSumZ_mem_spanL`) and is **independent of the width**; this
is what makes the argument feasible at a large width. -/
theorem bb144CertZ_mem : ∀ v ∈ rowList bb144CertZD, v ∈ spanL bb144Rz := by
  intro v hv
  unfold rowList at hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  unfold bb144CertZD at ha
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
  exact bb144RowSumZ_mem_spanL q.1

/-- The **indexed** form of the previous statement (used by
`length_le_finrank_spanL_of_certificate`). -/
theorem bb144CertZ_get_mem (i : Fin bb144CertZD.length) :
    (bb144CertZD.get i).1 ∈ spanL bb144Rz :=
  bb144CertZ_mem _ (by
    rw [rowList]
    exact List.mem_map.mpr ⟨_, List.get_mem _ i, rfl⟩)

/-- The echelon invariant of the certificate: every row takes the value 1 at its own pivot
column, and a later row takes the value 0 at the pivot columns of the earlier ones. -/
theorem bb144CertZ_ech : EchSelf bb144CertZD ∧ EchPair bb144CertZD :=
  ⟨by unfold EchSelf; decide, by unfold EchPair; decide⟩

/-! ## Z side, upper bound: the whole row list is spanned by 66 original rows -/

/-- The **head** used for the upper bound: 66 linearly independent original rows, namely the
rows that produced a pivot during elimination (the indices were selected over GF(2) by the
external script). `spanL` sees the set of elements and not their order, so the head need not
be a prefix: at width 144 the first 66 rows have rank only 64, and the prefix form does not
hold there. -/
def bb144RzHeadIdx : List (Fin 72) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
   12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
   36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 66, 67]

/-- The head as a row list. -/
def bb144RzHead : List (Vec 144) := bb144RzHeadIdx.map bb144HzRow

/-- The head has exactly 66 rows. -/
lemma bb144RzHead_length : bb144RzHead.length = 66 := by
  simp [bb144RzHead, bb144RzHeadIdx]

/-- Every original row in the head lies in the span of the head. -/
lemma bb144HzRow_mem_head (k : Fin 72) (hk : k ∈ bb144RzHeadIdx) :
    bb144HzRow k ∈ spanL bb144RzHead := by
  rw [bb144RzHead]
  exact subset_spanL (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- A sum of several rows of the head (all indices lying in the head) lies in the span of
the head. -/
lemma bb144RowSumZ_mem_head (s : List (Fin 72)) (hs : ∀ k ∈ s, k ∈ bb144RzHeadIdx) :
    bb144RowSumZ s ∈ spanL bb144RzHead := by
  unfold bb144RowSumZ
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (bb144HzRow_mem_head k (hs k (by simp)))
        (ih (fun k hk => hs k (by simp [hk])))

/-- Original row 64 is the GF(2) sum of 31 rows of the head (decided bit by bit). -/
theorem bb144RelZ64 : bb144HzRow 64 = bb144RowSumZ [0, 1, 3, 4, 6, 7, 9, 10, 18, 19, 21, 22, 24, 25, 27, 28, 36, 37, 39, 40, 42, 43, 45, 46, 54, 55, 57, 58, 60, 61, 63] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelZ64_mem : bb144HzRow 64 ∈ spanL bb144RzHead := by
  rw [bb144RelZ64]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- Original row 65 is the GF(2) sum of 31 rows of the head (decided bit by bit). -/
theorem bb144RelZ65 : bb144HzRow 65 = bb144RowSumZ [0, 2, 3, 5, 6, 8, 9, 11, 18, 20, 21, 23, 24, 26, 27, 29, 36, 38, 39, 41, 42, 44, 45, 47, 54, 56, 57, 59, 60, 62, 63] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelZ65_mem : bb144HzRow 65 ∈ spanL bb144RzHead := by
  rw [bb144RelZ65]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- Original row 68 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelZ68 : bb144HzRow 68 = bb144RowSumZ [2, 3, 4, 5, 8, 10, 12, 13, 16, 17, 18, 22, 24, 25, 26, 27, 30, 32, 38, 39, 40, 41, 44, 46, 48, 49, 52, 53, 54, 58, 60, 61, 62, 63, 66] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelZ68_mem : bb144HzRow 68 ∈ spanL bb144RzHead := by
  rw [bb144RelZ68]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- Original row 69 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelZ69 : bb144HzRow 69 = bb144RowSumZ [1, 5, 6, 7, 10, 11, 12, 13, 14, 17, 18, 21, 22, 23, 24, 26, 31, 33, 37, 41, 42, 43, 46, 47, 48, 49, 50, 53, 54, 57, 58, 59, 60, 62, 67] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelZ69_mem : bb144HzRow 69 ∈ spanL bb144RzHead := by
  rw [bb144RelZ69]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- Original row 70 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelZ70 : bb144HzRow 70 = bb144RowSumZ [0, 3, 4, 5, 6, 7, 10, 11, 14, 15, 16, 17, 19, 23, 24, 26, 30, 34, 36, 39, 40, 41, 42, 43, 46, 47, 50, 51, 52, 53, 55, 59, 60, 62, 66] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelZ70_mem : bb144HzRow 70 ∈ spanL bb144RzHead := by
  rw [bb144RelZ70]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- Original row 71 is the GF(2) sum of 35 rows of the head (decided bit by bit). -/
theorem bb144RelZ71 : bb144HzRow 71 = bb144RowSumZ [0, 1, 4, 5, 6, 7, 8, 11, 12, 15, 16, 17, 18, 20, 25, 27, 31, 35, 36, 37, 40, 41, 42, 43, 44, 47, 48, 51, 52, 53, 54, 56, 61, 63, 67] := by
  funext c
  fin_cases c <;> decide

/-- The membership form of the previous statement. -/
theorem bb144RelZ71_mem : bb144HzRow 71 ∈ spanL bb144RzHead := by
  rw [bb144RelZ71]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- **The whole row list lies in the span of the head**: the rows of the head are in the head
one by one, and each of the remaining rows has a relation of its own. -/
theorem bb144Rz_mem_head : ∀ v ∈ bb144Rz, v ∈ spanL bb144RzHead := by
  intro v hv
  unfold bb144Rz at hv
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hv
  rw [← hj]
  fin_cases j
  · exact bb144HzRow_mem_head 0 (by decide)
  · exact bb144HzRow_mem_head 1 (by decide)
  · exact bb144HzRow_mem_head 2 (by decide)
  · exact bb144HzRow_mem_head 3 (by decide)
  · exact bb144HzRow_mem_head 4 (by decide)
  · exact bb144HzRow_mem_head 5 (by decide)
  · exact bb144HzRow_mem_head 6 (by decide)
  · exact bb144HzRow_mem_head 7 (by decide)
  · exact bb144HzRow_mem_head 8 (by decide)
  · exact bb144HzRow_mem_head 9 (by decide)
  · exact bb144HzRow_mem_head 10 (by decide)
  · exact bb144HzRow_mem_head 11 (by decide)
  · exact bb144HzRow_mem_head 12 (by decide)
  · exact bb144HzRow_mem_head 13 (by decide)
  · exact bb144HzRow_mem_head 14 (by decide)
  · exact bb144HzRow_mem_head 15 (by decide)
  · exact bb144HzRow_mem_head 16 (by decide)
  · exact bb144HzRow_mem_head 17 (by decide)
  · exact bb144HzRow_mem_head 18 (by decide)
  · exact bb144HzRow_mem_head 19 (by decide)
  · exact bb144HzRow_mem_head 20 (by decide)
  · exact bb144HzRow_mem_head 21 (by decide)
  · exact bb144HzRow_mem_head 22 (by decide)
  · exact bb144HzRow_mem_head 23 (by decide)
  · exact bb144HzRow_mem_head 24 (by decide)
  · exact bb144HzRow_mem_head 25 (by decide)
  · exact bb144HzRow_mem_head 26 (by decide)
  · exact bb144HzRow_mem_head 27 (by decide)
  · exact bb144HzRow_mem_head 28 (by decide)
  · exact bb144HzRow_mem_head 29 (by decide)
  · exact bb144HzRow_mem_head 30 (by decide)
  · exact bb144HzRow_mem_head 31 (by decide)
  · exact bb144HzRow_mem_head 32 (by decide)
  · exact bb144HzRow_mem_head 33 (by decide)
  · exact bb144HzRow_mem_head 34 (by decide)
  · exact bb144HzRow_mem_head 35 (by decide)
  · exact bb144HzRow_mem_head 36 (by decide)
  · exact bb144HzRow_mem_head 37 (by decide)
  · exact bb144HzRow_mem_head 38 (by decide)
  · exact bb144HzRow_mem_head 39 (by decide)
  · exact bb144HzRow_mem_head 40 (by decide)
  · exact bb144HzRow_mem_head 41 (by decide)
  · exact bb144HzRow_mem_head 42 (by decide)
  · exact bb144HzRow_mem_head 43 (by decide)
  · exact bb144HzRow_mem_head 44 (by decide)
  · exact bb144HzRow_mem_head 45 (by decide)
  · exact bb144HzRow_mem_head 46 (by decide)
  · exact bb144HzRow_mem_head 47 (by decide)
  · exact bb144HzRow_mem_head 48 (by decide)
  · exact bb144HzRow_mem_head 49 (by decide)
  · exact bb144HzRow_mem_head 50 (by decide)
  · exact bb144HzRow_mem_head 51 (by decide)
  · exact bb144HzRow_mem_head 52 (by decide)
  · exact bb144HzRow_mem_head 53 (by decide)
  · exact bb144HzRow_mem_head 54 (by decide)
  · exact bb144HzRow_mem_head 55 (by decide)
  · exact bb144HzRow_mem_head 56 (by decide)
  · exact bb144HzRow_mem_head 57 (by decide)
  · exact bb144HzRow_mem_head 58 (by decide)
  · exact bb144HzRow_mem_head 59 (by decide)
  · exact bb144HzRow_mem_head 60 (by decide)
  · exact bb144HzRow_mem_head 61 (by decide)
  · exact bb144HzRow_mem_head 62 (by decide)
  · exact bb144HzRow_mem_head 63 (by decide)
  · exact bb144RelZ64_mem
  · exact bb144RelZ65_mem
  · exact bb144HzRow_mem_head 66 (by decide)
  · exact bb144HzRow_mem_head 67 (by decide)
  · exact bb144RelZ68_mem
  · exact bb144RelZ69_mem
  · exact bb144RelZ70_mem
  · exact bb144RelZ71_mem

/-- **Upper bound on the rank**: the whole row list is spanned by the 66 rows of the
head. -/
theorem bb144_rankZ_le : Module.finrank (ZMod 2) (spanL bb144Rz) ≤ 66 := by
  have h := finrank_spanL_le_of_mem_of_subset (A := bb144RzHead) (L := bb144Rz) bb144Rz_mem_head
  rwa [bb144RzHead_length] at h

/-- **Lower bound on the rank**: the 66 rows of the certificate are linearly independent and
all lie in the row space. -/
theorem bb144_rankZ_ge : 66 ≤ Module.finrank (ZMod 2) (spanL bb144Rz) :=
  length_le_finrank_spanL_of_certificate bb144CertZ_get_mem bb144CertZ_ech.1 bb144CertZ_ech.2

/-- **The row space of the Z-side parity-check matrix has dimension 66**. -/
theorem bb144_rankZ : Module.finrank (ZMod 2) (spanL bb144Rz) = 66 :=
  le_antisymm bb144_rankZ_le bb144_rankZ_ge

/-! ## Dimension -/

/-- **The dimension of $[[144,12,12]]$**: $k=n-\operatorname{rank}H_X-\operatorname{rank}H_Z=12$,
obtained from the certificates **without performing row reduction**. -/
theorem bb144_rowReduceX : (rowReduce bb144Rx).length = 66 := by
  rw [← rankEchelon_eq_length_rowReduce (L := bb144Rx)]
  rw [rankEchelon]
  rw [← finrank_spanL_eq_length_echelonFrom (L := bb144Rx)]
  exact bb144_rankX

/-- The elimination output for $H_Z$ is 66 rows as well (changing the backend does not
affect the rank). -/
theorem bb144_rowReduceZ : (rowReduce bb144Rz).length = 66 := by
  rw [← rankEchelon_eq_length_rowReduce (L := bb144Rz)]
  rw [rankEchelon]
  rw [← finrank_spanL_eq_length_echelonFrom (L := bb144Rz)]
  exact bb144_rankZ

theorem bb144_k : 144 - (rowReduce bb144Rx).length - (rowReduce bb144Rz).length = 12 := by
  norm_num [bb144_rowReduceX, bb144_rowReduceZ]

end QECCertificates
