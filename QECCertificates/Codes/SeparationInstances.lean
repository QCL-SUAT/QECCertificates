/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.Separation
import QECCertificates.Codes.CaseMatrix
import QECCertificates.Codes.BoundaryCollapse

/-!
#  Two instances: **two-sided counterexamples** to C1 (a failing side and a
distance-preserving side)

Both instances come from the smallest toric-code family `toricHx`/`toricHz`, the
$[[8,2,2]]$ code of `Codes/CaseMatrix.lean`. Fix an X-type logical operator $L$ to be tested
and an auxiliary graph $G$, then build the deformed code by W–Y gauging:

* the data qubits $0..7$ and the original X-type checks `toricHx` are kept;
* the vertices of the auxiliary graph are `supp L`, and each edge carries an ancilla,
  numbered from $8$ on after the data qubits;
* the Gauss law $A_v = X_v\prod_{e\ni v}X_e$ is added to the X-type checks;
* a deformed Z row is the original Z row completed by $Z_e$ along the matching of that row,
  plus the flux rows on a spanning-tree cycle basis.

**Every assertion in this module is checked by the kernel with `by decide`**, on matrices of
width 11 and 14:

| instance | auxiliary graph | C1 | the two distances of the deformed code | conclusion |
|---|---|---|---|---|
| `sepFail*` | a path (connected, $h<1$) | ✗ | $5$ on the X side, $1$ on the Z side | C1 **cannot be weakened further** (failing side) |
| `sepKeep*` | a connected sparse graph ($h<1$) | ✗ | $3$ on the X side, $2$ on the Z side | C1 is not necessary (distance-preserving side) |

**The two sides have unequal distances in both instances**, so the four numbers become four
separate theorems (§4), and any reference to them has to name the side. Reporting a single
number would read "there is a witness of weight 2" as "the distance of the deformed code is
2", whereas the Z side is 2 and the X side is 3.
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. The failing side: the auxiliary graph $P_4$ violates C1, and the deformed code
gains a weight-1 logical -/

/-- The X-type checks of the failing-side deformed code, 8 rows over 11 bits, in matrix
form, which `inKerB` and `lightSet` take. -/
def sepFailHxM : Matrix (Fin 8) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 1 + e 4 + e 6 : Vec 11),
    (0 + e 0 + e 1 + e 5 + e 7 : Vec 11),
    (0 + e 2 + e 3 + e 4 + e 6 : Vec 11),
    (0 + e 2 + e 3 + e 5 + e 7 : Vec 11),
    (0 + e 0 + e 8 + e 9 : Vec 11),
    (0 + e 2 + e 8 : Vec 11),
    (0 + e 4 + e 9 + e 10 : Vec 11),
    (0 + e 5 + e 10 : Vec 11)]

/-- The same checks in row-list form, which `inSpanB` takes. -/
def sepFailHx : List (Vec 11) :=
  List.ofFn sepFailHxM

/-- The Z-type checks of the failing-side deformed code, 4 rows over 11 bits, in matrix
form, which `inKerB` and `lightSet` take. -/
def sepFailHzM : Matrix (Fin 4) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 2 + e 4 + e 5 + e 8 + e 10 : Vec 11),
    (0 + e 1 + e 3 + e 4 + e 5 + e 10 : Vec 11),
    (0 + e 0 + e 2 + e 6 + e 7 + e 8 : Vec 11),
    (0 + e 1 + e 3 + e 6 + e 7 : Vec 11)]

/-- The same checks in row-list form, which `inSpanB` takes. -/
def sepFailHz : List (Vec 11) :=
  List.ofFn sepFailHzM

-- Fail: N=11 V=[0, 2, 4, 5] edges=[(0, 2), (0, 4), (4, 5)] 匹配=[(0, 2), (2,), (0,), ()] C1=False 违反割=([0, 2], 1)
-- 重量 1 的 ker(Hx)：[]；重量 1 的 ker(Hz)：[(9,)]
-- 重量 2 的 ker(Hx)：[]；重量 2 的 ker(Hz)：[(0, 2), (0, 8)]

/-- The X-type checks of the distance-preserving deformed code, 10 rows over 14 bits, in
matrix form, which `inKerB` and `lightSet` take. -/
def sepKeepHxM : Matrix (Fin 10) (Fin 14) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 1 + e 4 + e 6 : Vec 14),
    (0 + e 0 + e 1 + e 5 + e 7 : Vec 14),
    (0 + e 2 + e 3 + e 4 + e 6 : Vec 14),
    (0 + e 2 + e 3 + e 5 + e 7 : Vec 14),
    (0 + e 0 + e 8 + e 9 + e 10 + e 11 : Vec 14),
    (0 + e 1 + e 8 + e 12 : Vec 14),
    (0 + e 2 + e 9 : Vec 14),
    (0 + e 3 + e 10 + e 12 : Vec 14),
    (0 + e 4 + e 11 + e 13 : Vec 14),
    (0 + e 5 + e 13 : Vec 14)]

/-- The same checks in row-list form, which `inSpanB` takes. -/
def sepKeepHx : List (Vec 14) :=
  List.ofFn sepKeepHxM

/-- The Z-type checks of the distance-preserving deformed code, 5 rows over 14 bits, in
matrix form, which `inKerB` and `lightSet` take. -/
def sepKeepHzM : Matrix (Fin 5) (Fin 14) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 2 + e 4 + e 5 + e 9 + e 13 : Vec 14),
    (0 + e 1 + e 3 + e 4 + e 5 + e 12 + e 13 : Vec 14),
    (0 + e 0 + e 2 + e 6 + e 7 + e 9 : Vec 14),
    (0 + e 1 + e 3 + e 6 + e 7 + e 12 : Vec 14),
    (0 + e 8 + e 10 + e 12 : Vec 14)]

/-- The same checks in row-list form, which `inSpanB` takes. -/
def sepKeepHz : List (Vec 14) :=
  List.ofFn sepKeepHzM

-- Keep: N=14 V=[0, 1, 2, 3, 4, 5] edges=[(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (4, 5)] 匹配=[(1, 5), (4, 5), (1,), (4,)] C1=False 违反割=([4, 5], 1)
-- 重量 1 的 ker(Hx)：[]；重量 1 的 ker(Hz)：[(11,)]
-- 重量 2 的 ker(Hx)：[]；重量 2 的 ker(Hz)：[(0, 2), (0, 9)]

/-! ## 3. Kernel assertions: two-sided counterexamples to C1

Each of the two chains closes on its own:

* **Failing side**: the auxiliary graph, a path on 4 vertices, violates C1, hence the
  deformed code has a **weight-1** logical operator, hence the deformed distance is
  $1 < d = 2$: C1 cannot be weakened further.
* **Distance-preserving side**: the auxiliary graph, a connected sparse graph on 6 vertices,
  violates C1, hence the deformed code has **no logical of weight ≤ 1** and does have a
  witness of weight 2, hence the deformed distance is $= d = 2$: C1 is not necessary.

Both conclusions are stated on **the side on which the witness lives**, the comparison of $h$
with the distance holding on both sides at once; the two sides have unequal numerical values,
given in §4.
-/

/-- **The failing side, the C1 verdict**: the auxiliary graph is a path on 4 vertices, so
the expansion is $<1$. -/
theorem sepFail_not_C1 :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-- **The failing side, the witness**: the deformed code has a weight-1 logical operator,
the single bit 9, orthogonal to every X-type check and outside the row space of the Z-type
checks. -/
theorem sepFail_lightLogical :
    ∃ v : Vec 11, v ≠ 0 ∧ inKerB sepFailHzM v = true ∧ inSpanB sepFailHx v = false ∧
      hammingNorm v = 1 :=
  ⟨(e 9 : Vec 11), by decide, by decide, by decide, by decide⟩

/-- **The failing side, the conclusion**: C1 is violated, the deformed code has a weight-1
logical, and the base code has distance 2, so the deformed distance is $1 < 2 = d$: **C1
cannot be weakened further**. -/
theorem sepFail_summary :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (2, 3)] : List (Fin 4 × Fin 4)) ∧
      (∃ v : Vec 11, v ≠ 0 ∧ inKerB sepFailHzM v = true ∧ inSpanB sepFailHx v = false ∧
        hammingNorm v = 1) ∧
      min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  ⟨sepFail_not_C1, sepFail_lightLogical, toric_dx⟩

/-- **The distance-preserving side, the C1 verdict**: a connected sparse graph on 6
vertices, whose expansion is $<1$ across the cut $\{4,5\}$. -/
theorem sepKeep_not_C1 :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (4, 5)] :
      List (Fin 6 × Fin 6)) := by decide

/-- **The distance-preserving side, the lower bound**: the deformed code has no logical
operator of weight $\le1$. Both sides are checked, with 15 candidates per side supplied by
weight-bounded enumeration. -/
theorem sepKeep_no_lightLogical :
    (lightSet sepKeepHxM sepKeepHzM 2).card = 0 ∧
      (lightSet sepKeepHzM sepKeepHxM 2).card = 0 := by decide

/-- **The distance-preserving side, the upper bound**: the deformed code has a weight-2
logical operator, the bit pair $\{0,2\}$, which together with the lower bound gives the
deformed distance $= 2 = d$: **C1 is not necessary**. -/
theorem sepKeep_lightLogical_two :
    ∃ v : Vec 14, v ≠ 0 ∧ inKerB sepKeepHzM v = true ∧ inSpanB sepKeepHx v = false ∧
      hammingNorm v = 2 :=
  ⟨(e 0 + e 2 : Vec 14), by decide, by decide, by decide, by decide⟩

/-- **The distance-preserving side, the conclusion**: C1 is violated and the distance of
the deformed code is still $= d = 2$, so **C1 is not a necessary condition**. Together with
the failing side this gives a two-sided picture of the C1 boundary: for $h<1$ the distance may
survive or collapse, and the bound $\min(h,1)\cdot d$ indeed only reaches $<d$ when $h<1$. -/
theorem sepKeep_summary :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (4, 5)] :
        List (Fin 6 × Fin 6)) ∧
      (lightSet sepKeepHxM sepKeepHzM 2).card = 0 ∧
      (lightSet sepKeepHzM sepKeepHxM 2).card = 0 ∧
      min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  ⟨sepKeep_not_C1, sepKeep_no_lightLogical.1, sepKeep_no_lightLogical.2, toric_dx⟩

/-! ## 4. The two-sided distances: both C1 witnesses are deformed codes whose **two sides
differ**

The two-sidedness of C1 is carried by these two deformed codes, and their X-side and Z-side
distances **are not equal**. `Codes/DistanceLabel.lean` has an `_dx_eq_dz` line for
every instance whose two sides agree, and **these two are the only ones without one**:
that equation cannot be proved here.

So the four numbers become four separate theorems, and a reference to them has to name the
side. Reporting a single number would read "there is a witness of weight 2" as "the distance
of the deformed code is 2", whereas the Z side is 2 and the X side is 3. -/

/-- **Failing side, X distance $=5$**, with `sepFailHxM` as the kernel: the lower bound is
that the candidate set of weight $\le4$ is empty, and the upper bound is the weight-5 logical
operator on the bits $\{0,1,4,6,9\}$. -/
theorem sepFail_dx : min_weight_ker_not_mem_rowspace sepFailHxM sepFailHzM = 5 :=
  eq_minWeight_of_decide (d := 5) sepFailHxM sepFailHzM (by decide) (by decide)
    (E := (e 0 + e 1 + e 4 + e 6 + e 9 : Vec 11))
    (mem_ker_of_inKerB sepFailHxM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepFailHzM (by decide))
    (by decide)

/-- **Failing side, Z distance $=1$**, with `sepFailHzM` as the kernel: the witness is bit
9, and weight 1 is already the lower bound. -/
theorem sepFail_dz : min_weight_ker_not_mem_rowspace sepFailHzM sepFailHxM = 1 :=
  eq_minWeight_of_decide (d := 1) sepFailHzM sepFailHxM (by decide) (by decide)
    (E := (e 9 : Vec 11))
    (mem_ker_of_inKerB sepFailHzM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepFailHxM (by decide))
    (by decide)

/-- **Distance-preserving side, X distance $=3$**, with `sepKeepHxM` as the kernel: the
lower bound is that the candidate set of weight $\le2$ is empty, and the upper bound is the
weight-3 logical operator on the bits $\{0,1,8\}$. -/
theorem sepKeep_dx : min_weight_ker_not_mem_rowspace sepKeepHxM sepKeepHzM = 3 :=
  eq_minWeight_of_decide (d := 3) sepKeepHxM sepKeepHzM (by decide) (by decide)
    (E := (e 0 + e 1 + e 8 : Vec 14))
    (mem_ker_of_inKerB sepKeepHxM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepKeepHzM (by decide))
    (by decide)

/-- **Distance-preserving side, Z distance $=2$**, with `sepKeepHzM` as the kernel: the
witness is the bit pair $\{0,2\}$, and the lower bound is the Z-side half of
`sepKeep_no_lightLogical`. -/
theorem sepKeep_dz : min_weight_ker_not_mem_rowspace sepKeepHzM sepKeepHxM = 2 :=
  eq_minWeight_of_decide (d := 2) sepKeepHzM sepKeepHxM (by decide)
    sepKeep_no_lightLogical.2
    (E := (e 0 + e 2 : Vec 14))
    (mem_ker_of_inKerB sepKeepHzM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepKeepHxM (by decide))
    (by decide)

/-- **The failing side has unequal sides**: $5 \ne 1$. -/
theorem sepFail_dx_ne_dz :
    min_weight_ker_not_mem_rowspace sepFailHxM sepFailHzM ≠
      min_weight_ker_not_mem_rowspace sepFailHzM sepFailHxM := by
  rw [sepFail_dx, sepFail_dz]
  decide

/-- **The distance-preserving side has unequal sides**: $3 \ne 2$. -/
theorem sepKeep_dx_ne_dz :
    min_weight_ker_not_mem_rowspace sepKeepHxM sepKeepHzM ≠
      min_weight_ker_not_mem_rowspace sepKeepHzM sepKeepHxM := by
  rw [sepKeep_dx, sepKeep_dz]
  decide

/-! ## 5. The **mechanism lemma** for the failing side: a zero column implies distance 1

The weight-1 logical operators of the two instances above were previously read off instance
by instance with `by decide`. This section raises that to a **general lemma**: if some column
of the deformed Z-type parity-check matrix is identically zero, that ancilla being seen by no
Z row, while its unit vector is not in the row space of the X-type checks, then the Z-side
distance is $\le 1$, and together with the fact that the zero vector is not a logical operator
it is **exactly $1$**.

This lemma is the mechanism of `sepFail` itself: on the **path** that forms the auxiliary
graph, the edge $(0,4)$ lies outside **every** valid matching, since matching it off would
leave $2$ and $5$ behind and $2$–$5$ is not an edge of the path, so the column of ancilla $9$
is identically zero. **The lemma is independent of the code**: given the matrix, there are
only two criteria, a zero column and absence from the row space. -/

/-- **The zero-column criterion**: a column of the Z-type parity-check matrix that is
identically zero puts the corresponding unit vector in the kernel on that side. -/
theorem inKerB_e_of_zero_column {m₁ n : ℕ} (Hz : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (q : Fin n) (hcol : ∀ i, Hz i q = 0) : inKerB Hz (e q) = true := by
  rw [inKerB_iff, mem_ker_iff_dotProd_rows_eq_zero]
  intro i
  rw [dot_e (Hz i) q, hcol i]

/-- **The mechanism of the failing side, in general form**: if a column of the Z-type
parity-check matrix is identically zero and the corresponding unit vector is not in the row
space of the X-type checks, then the Z-side distance is $\le 1$.

The proof uses a single witness: that unit vector **is itself** an undetectable nontrivial
operator of weight $1$ (`minWeight_le_of_witness`), an order of magnitude cheaper than an
instance-by-instance `by decide` and **independent of the size of the code**. -/
theorem minWeight_le_one_of_zero_column {m₁ m₂ n : ℕ}
    (Hz : Matrix (Fin m₁) (Fin n) (ZMod 2)) (Hx : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (q : Fin n) (hcol : ∀ i, Hz i q = 0) (hnot : e q ∉ Hx.rowSpace) :
    min_weight_ker_not_mem_rowspace Hz Hx ≤ 1 :=
  minWeight_le_of_witness Hz Hx (mem_ker_of_inKerB Hz (inKerB_e_of_zero_column Hz q hcol))
    hnot (hammingNorm_e q)



/-- **The structure behind the failing side**: the Z column of ancilla $9$, the edge
   $(0,4)$ of the auxiliary graph, is identically zero, so the mechanism lemma gives distance
   $\le 1$ directly, **without enumerating the whole set of light operators instance by
   instance**.

   Why the column of $(0,4)$ is identically zero: a deformed Z row is the original Z row plus
   the **matching** of that row on its support, and $\{0,2,4,5\}$ admits **only one** perfect
   matching on this path, namely $\{(0,2),(4,5)\}$, since pairing $0$ with $4$ would leave $2$
   and $5$ behind and $2$–$5$ is not an edge of the path, so $(0,4)$ falls outside the
   matching of **every** row. -/
theorem sepFail_dist_le_one_structural :
    min_weight_ker_not_mem_rowspace sepFailHzM sepFailHxM ≤ 1 :=
  minWeight_le_one_of_zero_column sepFailHzM sepFailHxM 9
    (by decide) (not_mem_rowSpace_of_inSpanB_false sepFailHxM (by decide))

/-- The other half of the same structural reproduction: the column **is** identically zero.
   The hypothesis of the theorem above is kept as a separate theorem, so that the text can
   cite it as the zero-column criterion. -/
theorem sepFail_ancilla_nine_column_zero : ∀ i : Fin 4, sepFailHzM i 9 = 0 := by decide

/-! ## 6. **A second route on the same logical operator**: C1 does not decide the outcome

The two witnesses above test **two different** logical operators, supported on 4 and on 6
vertices, so their difference lies in C1 and elsewhere at the same time. This section adds a
second route on the **same code and the same logical operator**: it **shares the tested X-type
logical** with `sepFail` on the failing side, both supported on $\{0,2,4,5\}$, and **changes
only the way the auxiliary graph is wired**:

| | auxiliary graph | C1 | Z-side distance |
|---|---|---|---|
| `sepFail*` | the path $2$–$0$–$4$–$5$ | ✗ | $1$ |
| `sepKeepPath*` | the path $0$–$4$–$5$–$2$ | ✗ | $2$ |

**Both graphs are $P_4$**, so C1 takes the same value, violated in both, **and the distances
differ**. Collapse on failure therefore **cannot** be decided by C1 alone: with the same code,
the same logical operator and the same value of C1, both outcomes occur. What decides it is
the **matching**: on the path of the failing side, the edge $(0,4)$ lies outside the matching
of **every** row, since $\{0,2,4,5\}$ admits only one perfect matching on that graph, so the Z
column of ancilla $9$ is identically zero (`minWeight_le_one_of_zero_column`). -/

/-- The X-type checks of the distance-preserving deformed code on the same logical
operator, 8 rows over 11 bits. -/
def sepKeepPathHxM : Matrix (Fin 8) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 1 + e 4 + e 6 : Vec 11),
    (0 + e 0 + e 1 + e 5 + e 7 : Vec 11),
    (0 + e 2 + e 3 + e 4 + e 6 : Vec 11),
    (0 + e 2 + e 3 + e 5 + e 7 : Vec 11),
    (0 + e 0 + e 8 : Vec 11),
    (0 + e 2 + e 9 : Vec 11),
    (0 + e 4 + e 8 + e 10 : Vec 11),
    (0 + e 5 + e 9 + e 10 : Vec 11)]

/-- The same checks in row-list form. -/
def sepKeepPathHx : List (Vec 11) := List.ofFn sepKeepPathHxM

/-- The Z-type checks of the distance-preserving deformed code on the same logical
operator, 4 rows over 11 bits. -/
def sepKeepPathHzM : Matrix (Fin 4) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 2 + e 4 + e 5 + e 8 + e 9 : Vec 11),
    (0 + e 1 + e 3 + e 4 + e 5 + e 10 : Vec 11),
    (0 + e 0 + e 2 + e 6 + e 7 : Vec 11),
    (0 + e 1 + e 3 + e 6 + e 7 : Vec 11)]

/-- The same checks in row-list form. -/
def sepKeepPathHz : List (Vec 11) := List.ofFn sepKeepPathHzM

/-- **The distance-preserving side, the C1 verdict**: the path $0$–$4$–$5$–$2$ likewise
violates C1.

**The edge list is written on the relabelled four vertices $0,1,2,3$** — the support qubits
$0,2,4,5$ renamed in increasing order — the same convention `sepFail_not_C1` above already
uses, so the two witnesses sit on one and the same index type and C1 is read the same way in
both. The code's own labels are what one must **not** write down here: `Fin` literals reduce
modulo the index bound (`(4 : Fin 4) = 0`, `(5 : Fin 4) = 1`), so `[(0,4),(2,5),(4,5)]` on
`Fin 4` expands to `[(0,0),(2,1),(0,1)]`, a graph with a self-loop, and `by decide` accepts it
all the same. On `Fin 6` the same four labels would instead leave $1$ and $3$ isolated, and an
isolated vertex violates expansion on its own, so the verdict would hold for the wrong reason.
The statement below is the non-trivial one: the cut $\{0,2\}$ has one edge leaving it against
a minimum of two. -/
theorem sepKeepPath_not_C1 :
    ¬ HasExpansionOne ([(0, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-- **The distance-preserving side, the lower bound**: the deformed code has no logical
operator of weight $\le 1$. Both sides are checked. -/
theorem sepKeepPath_no_lightLogical :
    (lightSet sepKeepPathHxM sepKeepPathHzM 2).card = 0 ∧
      (lightSet sepKeepPathHzM sepKeepPathHxM 2).card = 0 := by decide

/-- **The distance-preserving side, the upper bound**: the deformed code has a weight-2
logical operator. -/
theorem sepKeepPath_lightLogical_two :
    ∃ v : Vec 11, v ≠ 0 ∧ inKerB sepKeepPathHzM v = true ∧
      inSpanB sepKeepPathHx v = false ∧ hammingNorm v = 2 :=
  ⟨(e 0 + e 2 : Vec 11), by decide, by decide, by decide, by decide⟩

/-- **The distance-preserving side, the conclusion**: C1 is violated, yet the Z-side
distance of the deformed code is still $2=d$. -/
theorem sepKeepPath_summary :
    ¬ HasExpansionOne ([(0, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4)) ∧
      (lightSet sepKeepPathHxM sepKeepPathHzM 2).card = 0 ∧
      (lightSet sepKeepPathHzM sepKeepPathHxM 2).card = 0 ∧
      min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  ⟨sepKeepPath_not_C1, sepKeepPath_no_lightLogical.1,
   sepKeepPath_no_lightLogical.2, toric_dx⟩


/-! ## 7. A **control instance**: a code whose two sides are independent

The two witnesses above both fall outside C4, since their local detectors come from **the code
itself**: the four X-type checks of the toric code are linearly dependent and their product is
the identity. The control here is the `[[9,1,3]]` Shor code, whose **8 stabilizer generators,
6 of Z type and 2 of X type, are pairwise independent**, so C4 holds for it and it is not a
code carrying local relations. This answers the question whether a code with independent sides
is at hand: **no instance is built on one, but the code itself qualifies**. -/

/-- The 6 Z-type and 2 X-type stabilizers of the `[[9,1,3]]` Shor code, with zero-based bit
numbering. -/
def shorGenerators : List (Vec 9) :=
  [ (e 0 + e 1 : Vec 9), (e 1 + e 2 : Vec 9), (e 3 + e 4 : Vec 9),
    (e 4 + e 5 : Vec 9), (e 6 + e 7 : Vec 9), (e 7 + e 8 : Vec 9),
    (e 0 + e 1 + e 2 + e 3 + e 4 + e 5 : Vec 9),
    (e 3 + e 4 + e 5 + e 6 + e 7 + e 8 : Vec 9) ]

/-- **The control: pairwise independence**: no generator lies in the row space of the
others. -/
theorem shor_generators_independent :
    ∀ r ∈ shorGenerators, inSpanB (shorGenerators.erase r) r = false := by decide


end QECCertificates
