/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.CaseMatrix
import QECCertificates.GF2.HGPCompression

/-!
# The timelike detector code of the BB gauging measurement circuit: $|V| = 4$ Gauss laws, $T = 4 = d$ rounds

`Codes/BB24Gauged.lean` gives the **spacelike** instance of BB $[[18,4,4]]$ gauged by the
$K_4$ ancilla graph to $[[24,3,4]]$ ($k$ drops by one, the distance is preserved). This
module supplies its **circuit-side** dual: it computes the timelike (spacetime) fault
distance of the gauging **measurement circuit** as a named, reproducible instance whose
value is decided inside the kernel, in the same shape and along the same reduction chain
as the Bacon–Shor detector code of `Codes/TimeLikeInstance.lean` (an external encoder and
solver, then `Reflect/LRATDataCircuit.lean` and `Reflect/FaithfulCircuit.lean`).

## Which part of the BB gauging measurement circuit this is

Gauging measures $L$ by decomposing it into $|V|$ **Gauss laws**
$A_v = X_v\prod_{e \ni v}X_e$ (the $K_4$ ancilla graph, whose vertices are the 4 support
qubits of $L$), measuring **each law once with its own ancilla**, and multiplying the
$|V|$ outcomes to obtain the readout of $L$ ($\prod_v A_v = L$: the edge qubits cancel in
pairs, see `gauss_prod_eq_vertex_prod` in `Codes/Gauging.lean`). That step, the repeated
measurement of these 4 laws, is what this module encodes.

* The number of checks is $m = |V| = 4$, fixed by the gauging structure (the 4 vertices
  of $K_4$) and not a free parameter;
* the number of rounds is $T = 4 = d$, where $d$ is the distance of the gauged code
  $[[24,3,4]]$ (`bb24_dx` / `bb24_dz` in `Codes/BB24Gauged.lean`). Taking $T = d$ makes
  the **timelike component exactly $d$**, so that together with the spacelike component
  the two components are both $\ge d$; this is the same statement as the $T = d = 3$ case
  in `Codes/BaconShorMeasurement.lean`.

So there are $N = mT = 16$ qubits and $m(T-1) = 12$ detectors, and the minimum
undetectable weight is $T = 4 = d$.

## Main results

* `bbGauge44_d`: $\min\{\mathrm{wt}(f) : Hf = 0,\ f \neq 0\} = 4$, by a **two-sided
  squeeze**: the lower bound from the family-level theorem (below), the upper bound from
  the explicit witness `bbGauge44W` (the first law reports an error in 4 consecutive
  rounds);
* `bbGauge44_le_weight_of_ker`: the **family-level theorem route** to the lower bound:
  every block of a kernel vector is constant, hence at least one law has an entirely
  non-zero time axis, hence that slice has weight exactly $4$, hence the injective
  pull-back gives $4 \le \mathrm{wt}(f)$. **No enumeration anywhere.**
* `bbGauge44_lightSet_zero`: a **second certificate** for the same lower bound (a
  weight-limited enumeration over $\sum_{k \le 3}\binom{16}{k} = 697$ candidates,
  `by decide`), following this package's practice of computing one assertion along two
  routes;
* `bbGauge44_ker_slice_const`: the point at which **the family-level theorem is reused**:
  the 4 rounds of each law are read as a slice `Vec 4`, row-by-row orthogonality supplies
  the hypothesis of `timeLike_eq_of_repCheck` from `Codes/Gauging.lean`, and the
  family-level theorem gives constancy directly;
* `bbGauge44Checks_rows` / `bbGauge44Checks_prod`: the 4 Gauss laws are **pinned
  literally** to rows $9..12$ of `bb24Hx` in `Codes/BB24Gauged.lean`, and their product is
  exactly the indicator vector of the 4 vertex qubits ($L = \prod_v A_v$). These two are
  what makes the 4 repeatedly measured operators really the 4 laws of the gauging.

## Honest boundaries (what this module does **not** do)

1. **The full-scale circuit is not reproduced**: this module encodes only the repeated
   measurement of the $|V| = 4$ Gauss laws of the gauging step. It is **not** the full
   syndrome-extraction cycle over the 13 X checks and 12 Z checks of the whole gauged code
   $[[24,3,4]]$. Copying that over would give a CNF with $m \approx 13$ and $N \approx 52$,
   whose kernel replay is beyond this package's budget (as recorded in
   `Codes/BB24Gauged.lean`: on width 24, `inSpanB`/`rowReduce` stops converging from row 7
   on). The trade-off and its reasons are documented in the module header of the external
   encoder and in the description of the `bbgauge44` entry of
   `Reflect/LRATDataCircuit.lean`. **This is a simplification, not the full circuit.**
2. **No general gate-level circuit calculus is carried out**: the timelike structure here
   is the **phenomenological** model of "the parity of the reported outcomes of the same
   check in two adjacent rounds" (the same model as in
   `Codes/MeasurementProtocol.lean`). It does **not** contain gate-level positions (it is
   not a gate-by-gate circuit simulation), nor the intra-round spacelike checks (the
   Gauss-law product $\prod_v \sigma_{v,t}$ inside a round is a **spacelike** component
   and belongs to the other component).
3. **The 4 laws are not bridged to `gaussOp` of `Codes/Gauging.lean` at the index level**:
   `gaussOp` uses the $\mathrm{Fin}\,k \oplus \mathrm{Fin}\,m$ numbering whereas this
   module uses the 24-qubit numbering of `Codes/BB24Gauged.lean`. The **formulas** are the
   same and the **content** is verified one by one in the 24-qubit numbering by
   `bbGauge44Checks_rows` / `bbGauge44Checks_prod`, but the formal bridge between the two
   numberings is not built.
4. **The lower bound on the timelike component covers only the case "all detectors silent
   and the fault non-zero"**: the same convention as `Codes/TimeLikeInstance.lean`
   (`zeroRows`), **not** the `IsUndetectedFault` branch of
   `Codes/MeasurementProtocol.lean`, which carries the logical functional $w \cdot f = 1$.
   There is no $w$ here, because the readout of a gauging measurement is the product of 4
   outcomes and does not form another constraint on the timelike chain.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. The 4 Gauss laws that are measured repeatedly (pinned to `Codes/BB24Gauged.lean`) -/

/-- The vertices of $K_4$: the 4 support qubits of the weight-4 X-type logical operator $L$ that is
promoted to a stabilizer (in the 24-qubit numbering of `Codes/BB24Gauged.lean`, ordered as the
vertices of $K_4$). -/
def bbGauge44Vert : Fin 4 → Fin 24 := ![0, 2, 6, 9]

/-- **The 4 Gauss laws** $A_v = X_v\prod_{e \ni v}X_e$ (the $K_4$ ancilla graph: the vertex qubit is
`bbGauge44Vert v`, and each of the 3 incident edges carries an ancilla, numbered $18..23$).

The verbatim description is the same as rows $9..12$ of `bb24Hx` in `Codes/BB24Gauged.lean`;
`bbGauge44Checks_rows` pins that down as a theorem. -/
def bbGauge44Star : Fin 4 → Vec 24 :=
  ![ (e 0 + e 18 + e 19 + e 20 : Vec 24),
     (e 2 + e 18 + e 21 + e 22 : Vec 24),
     (e 6 + e 19 + e 21 + e 23 : Vec 24),
     (e 9 + e 20 + e 22 + e 23 : Vec 24) ]

/-- The list of rows of the 4 Gauss laws (the 4 operators that one round of the gauging measurement measures). -/
def bbGauge44Checks : List (Vec 24) := List.ofFn bbGauge44Star

/-- **Pinned literally to the X checks of the gauged code**: these 4 laws are rows $9..12$ of
`bb24Hx` in `Codes/BB24Gauged.lean`, the 4 rows appended to the original $H_X$ by the gauging. -/
theorem bbGauge44Checks_rows :
    bbGauge44Checks = (List.ofFn (fun i : Fin 13 => bb24Hx i)).drop 9 := by decide

/-- Every Gauss law has weight exactly $4 = 1$ (the vertex) $+\ 3$ (the degree of that vertex in $K_4$). -/
theorem bbGauge44Star_weight (v : Fin 4) : hammingNorm (bbGauge44Star v) = 4 := by
  fin_cases v <;> decide

/-- **$L = \prod_v A_v$** (an instance of `gauss_prod_eq_vertex_prod` in `Codes/Gauging.lean`):
each of the 6 edge qubits occurs in two laws and cancels in pairs, so the sum of the 4 laws is
exactly the indicator vector of the 4 vertex qubits, that is, the weight-4 logical operator $L$ that
the gauging promotes to a stabilizer.

Hence multiplying the readouts of the $|V|$ laws does give the readout of $L$: the 4 laws of this
module are not an arbitrary choice of 4 operators. -/
theorem bbGauge44Checks_prod :
    (∑ v : Fin 4, bbGauge44Star v) = ∑ v : Fin 4, e (bbGauge44Vert v) := by decide

/-! ## 2. The timelike detector code ($|V| = 4$ laws, $T = 4$ rounds) -/

/-- **The parity-check matrix of the timelike detector code**: $12$ rows, $16$ columns.

Qubit $4v + t$ is the **reported outcome** of the `v`-th Gauss law in round `t`, and row $(v,t)$
is the pair $e_{4v+t} + e_{4v+t+1}$ of **the same law in two adjacent rounds**: two adjacent rounds
should agree, so the detector is their parity. The row order is the lexicographic order on $(v,t)$. -/
def bbGauge44H : Matrix (Fin 12) (Fin 16) (ZMod 2) :=
  Matrix.of ![
    e 0 + e 1,   e 1 + e 2,   e 2 + e 3,
    e 4 + e 5,   e 5 + e 6,   e 6 + e 7,
    e 8 + e 9,   e 9 + e 10,  e 10 + e 11,
    e 12 + e 13, e 13 + e 14, e 14 + e 15
  ]

/-- A witness: **the first Gauss law reports an error in 4 consecutive rounds**, of weight $4 = T$.

It lies in the kernel and is the non-zero kernel vector of minimum weight, the explicit operator
behind "the undetectable duration of the timelike component equals the number of rounds" (the
readout of one law is flipped, hence the logical readout $\prod_v$ is flipped, while every detector
stays silent). -/
def bbGauge44W : Vec 16 := e 0 + e 1 + e 2 + e 3

/-! ## 3. The three facts about the witness -/

/-- It lies in the kernel: $H w = 0$ (the readings of adjacent rounds agree for every law). -/
theorem bbGauge44_witness_mem_ker : bbGauge44H *ᵥ bbGauge44W = 0 := by decide

/-- It is non-zero. -/
theorem bbGauge44_witness_ne_zero : bbGauge44W ≠ 0 := by decide

/-- Its weight is exactly the number of rounds $T = 4$. -/
theorem bbGauge44_witness_weight : hammingNorm bbGauge44W = 4 := by decide

/-- **Each of the 4 laws has its own minimum-weight undetectable direction**: the four rounds of any
single law being wrong is a kernel vector, so there are $|V| = 4$ implementations of the minimum weight
(the lower bound does not rest on one accidental vector). -/
theorem bbGauge44_block_witnesses :
    (bbGauge44H *ᵥ (e 0 + e 1 + e 2 + e 3 : Vec 16) = 0 ∧
     bbGauge44H *ᵥ (e 4 + e 5 + e 6 + e 7 : Vec 16) = 0 ∧
     bbGauge44H *ᵥ (e 8 + e 9 + e 10 + e 11 : Vec 16) = 0 ∧
     bbGauge44H *ᵥ (e 12 + e 13 + e 14 + e 15 : Vec 16) = 0) := by decide

/-! ## 4. Block indices and slices (the bridge that reuses the family-level theorem) -/

/-- The qubit number of the `v`-th law in round `t`: $4v + t$. -/
def bbGauge44Blk (v : Fin 4) (t : Fin 4) : Fin 16 :=
  ⟨4 * v.val + t.val, by have := v.isLt; have := t.isLt; omega⟩

/-- The row number of the $(v,i)$-th detector: $3v + i$. -/
def bbGauge44RowIdx (v : Fin 4) (i : Fin 3) : Fin 12 :=
  ⟨3 * v.val + i.val, by have := v.isLt; have := i.isLt; omega⟩

/-- The first non-zero column of row $(v,i)$: round `i` of the `v`-th law. -/
def bbGauge44RowL (v : Fin 4) (i : Fin 3) : Fin 16 := bbGauge44Blk v (Fin.castSucc i)

/-- The second non-zero column of row $(v,i)$: round `i+1` of the `v`-th law. -/
def bbGauge44RowR (v : Fin 4) (i : Fin 3) : Fin 16 := bbGauge44Blk v (Fin.succ i)

/-- **The time-axis slice of the `v`-th law**: the values of the 4 rounds read as a `Vec 4`, which is
the object the family-level theorem `timeLike_eq_of_repCheck` acts on. -/
def bbGauge44Slice (v : Fin 4) (f : Vec 16) : Vec 4 :=
  fun t => f (bbGauge44Blk v t)

/-- The time axis of the `v`-th law is injective (the 4 rounds land on 4 distinct qubits). -/
theorem bbGauge44Blk_injective (v : Fin 4) : Function.Injective (bbGauge44Blk v) := by
  intro a b h
  have h' : 4 * v.val + a.val = 4 * v.val + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- Every row of the parity-check matrix really is a pair of adjacent rounds of one law. -/
theorem bbGauge44H_row (v : Fin 4) (i : Fin 3) :
    bbGauge44H (bbGauge44RowIdx v i)
      = (e (bbGauge44RowL v i) + e (bbGauge44RowR v i) : Vec 16) := by
  fin_cases v <;> fin_cases i <;> decide

/-- The dot product on a support reads `e i` as the `i`-th component (`e` and `unitVec` are the same
definition, so `unitVec_dot` of `Codes/Gauging.lean` applies directly). -/
theorem e_dot {n : ℕ} (i : Fin n) (x : Vec n) : e i ⬝ᵥ x = x i := by
  have h : e i = unitVec i := rfl
  rw [h]
  exact unitVec_dot i x

/-- Row-by-row orthogonality (`inKerB` unfolds to "the dot product of every row is zero"). -/
theorem inKerB_dot_row {k n : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) {f : Vec n}
    (h : inKerB M f = true) (i : Fin k) : M i ⬝ᵥ f = 0 := by
  unfold inKerB at h
  rw [List.all_eq_true] at h
  have hmem : decide (M i ⬝ᵥ f = 0) ∈
      List.ofFn (fun i : Fin k => decide (M i ⬝ᵥ f = 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  simpa using h _ hmem

/-- A silent detector gives the adjacent-round equality inside a block (round `i` and round `i+1`
read the same). -/
theorem bbGauge44_ker_row_eq {f : Vec 16} (hf : inKerB bbGauge44H f = true)
    (v : Fin 4) (i : Fin 3) :
    f (bbGauge44RowL v i) = f (bbGauge44RowR v i) := by
  have hrow := inKerB_dot_row bbGauge44H hf (bbGauge44RowIdx v i)
  rw [bbGauge44H_row, add_dotProduct, e_dot, e_dot] at hrow
  exact (add_eq_zero_iff_eq _ _).mp hrow

/-- Every qubit lies on the time axis of some law ($4v + t$ runs over $0..15$). -/
theorem bbGauge44Blk_surjective :
    ∀ j : Fin 16, ∃ v : Fin 4, ∃ t : Fin 4, j = bbGauge44Blk v t := by
  decide

/-! ## 5. The kernel characterisation: the family-level theorem used block by block -/

/-- **A kernel vector takes a constant value on the time axis of every Gauss law**, which is the
**block form** of the family-level theorem `timeLike_eq_of_repCheck` of `Codes/Gauging.lean`: the
4 rounds of the `v`-th law are read as the slice `bbGauge44Slice v f : Vec 4`, row-by-row
orthogonality gives `repCheck 3 i ⬝ᵥ slice = 0` (adjacent rounds are equal); the family-level theorem
then yields "the value is the same in every round".

With this, the lower bound of the present instance no longer rests on enumeration but on the same
family-level theorem; the enumeration-based lower bound of `Codes/TimeLikeInstance.lean` and the one
here cross-check each other. -/
theorem bbGauge44_ker_slice_const {f : Vec 16} (hf : inKerB bbGauge44H f = true)
    (v : Fin 4) : ∀ i j : Fin 4, bbGauge44Slice v f i = bbGauge44Slice v f j := by
  refine timeLike_eq_of_repCheck (S := 3) (x := bbGauge44Slice v f) ?_
  intro i
  have hL : bbGauge44Slice v f (Fin.castSucc i) = f (bbGauge44RowL v i) := rfl
  have hR : bbGauge44Slice v f (Fin.succ i) = f (bbGauge44RowR v i) := rfl
  have hrow : f (bbGauge44RowL v i) = f (bbGauge44RowR v i) := bbGauge44_ker_row_eq hf v i
  rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot, hL, hR, hrow]
  exact CharTwo.add_self_eq_zero _

/-- **The lower bound (family-level theorem route)**: a non-zero vector in the kernel has weight at least $T = 4$.

The proof is structural throughout: in the kernel every block is constant, so at least one law has an
entirely non-zero time axis (otherwise $f = 0$), so that slice has weight exactly $4$
(`timeLike_weight_eq`), and by the injective pull-back the weight is at most the weight of the whole
vector (`hammingNorm_le_of_injective`), so $4 \le \mathrm{wt}(f)$. **No enumeration anywhere.** -/
theorem bbGauge44_le_weight_of_ker {f : Vec 16} (hf : inKerB bbGauge44H f = true)
    (hne : f ≠ 0) : 4 ≤ hammingNorm f := by
  have hex : ∃ v : Fin 4, bbGauge44Slice v f ≠ 0 := by
    by_contra h
    push Not at h
    refine hne (funext fun j => ?_)
    obtain ⟨v, t, rfl⟩ := bbGauge44Blk_surjective j
    exact congrFun (h v) t
  obtain ⟨v, hv⟩ := hex
  have hker : ∀ i : Fin 3, repCheck 3 i ⬝ᵥ bbGauge44Slice v f = 0 := by
    intro i
    have hL : bbGauge44Slice v f (Fin.castSucc i) = f (bbGauge44RowL v i) := rfl
    have hR : bbGauge44Slice v f (Fin.succ i) = f (bbGauge44RowR v i) := rfl
    have hrow : f (bbGauge44RowL v i) = f (bbGauge44RowR v i) := bbGauge44_ker_row_eq hf v i
    rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot, hL, hR, hrow]
    exact CharTwo.add_self_eq_zero _
  have hwt : hammingNorm (bbGauge44Slice v f) = 4 := timeLike_weight_eq hker hv
  calc (4 : ℕ) = hammingNorm (bbGauge44Slice v f) := hwt.symm
    _ ≤ hammingNorm f :=
        hammingNorm_le_of_injective (bbGauge44Blk v) (bbGauge44Blk_injective v) f

/-! ## 6. Minimum undetectable weight = rounds = code distance (two-sided squeeze) -/

/-- **The main assertion**: for the gauging measurement circuit with $|V| = 4$ Gauss laws and
$T = 4$ rounds, the minimum undetectable spacetime weight is exactly $4$.

The lower bound comes from Section 5 (the family-level theorem, no enumeration) and the upper bound
from the explicit witness `bbGauge44W`. -/
theorem bbGauge44_d : min_weight_ker_not_mem_rowspace bbGauge44H (zeroRows 16) = 4 :=
  eq_minWeight_of_bounds bbGauge44H (zeroRows 16) (by decide) (E := bbGauge44W)
    (mem_ker_of_inKerB bbGauge44H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 16) (by decide))
    (by decide)
    (fun E hker hnot =>
      bbGauge44_le_weight_of_ker ((inKerB_iff bbGauge44H E).mpr hker)
        (fun h0 => hnot (h0 ▸ (zeroRows 16).rowSpace.zero_mem)))

/-- **A second certificate for the same lower bound**: the candidate set of weight $\le 3$ is empty
(a weight-limited enumeration over $\sum_{k \le 3}\binom{16}{k} = 697$ candidates, `by decide`).

This and the family-level theorem route of `bbGauge44_le_weight_of_ker` are **two independent
routes** to the same assertion. A third independent route (enumeration of the whole $2^{16}$ space)
lives on the Python side of the external encoder. -/
theorem bbGauge44_lightSet_zero : (lightSet bbGauge44H (zeroRows 16) 4).card = 0 := by decide

/-- **The timelike component = the code distance**: $4$ is both the timelike fault distance of this
measurement circuit and the distance of the gauged code $[[24,3,4]]$ (`bb24_dx` in
`Codes/BB24Gauged.lean`).

Taking $T = d$ rounds gives "the timelike component $\ge d$", which is the circuit-side dual of the
spacelike instance of `Codes/BB24Gauged.lean` ($d = 4$ preserved). -/
theorem bbGauge44_d_eq_codeDistance :
    min_weight_ker_not_mem_rowspace bbGauge44H (zeroRows 16)
      = min_weight_ker_not_mem_rowspace bb24Hx bb24Hz := by
  rw [bbGauge44_d, bb24_dx]

end QECCertificates
