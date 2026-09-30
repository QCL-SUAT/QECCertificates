/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.CaseMatrix

/-!
# Bacon–Shor $[[9,1,3]]$: the structure and distance of a **subsystem code**, checked by the kernel

This is the **representation-layer foundation** of this package's work on the time
axis: before the logical operators of a transversal Bacon–Shor measurement can be
discussed, the code has to be set up inside the kernel as a **subsystem code**, with its
gauge generators, its center (the stabilizer), its bare logicals, and its number of
logical qubits and distance.

## Two differences from a stabilizer code

1. **The gauge generators need not commute pairwise.** The X-type ones are horizontal
   edges ($X_iX_j$, two adjacent qubits in the same row, 6 of them) and the Z-type ones
   are vertical edges ($Z_iZ_j$, two adjacent rows in the same column, 6 of them); a
   horizontal edge and a vertical edge anticommute when they share a qubit, and there
   are exactly 16 such pairs. **This is what "subsystem" means**: the gauge degrees of
   freedom are not stabilizers. So this module does **not** require $H_XH_Z^\top=0$
   (that is the stabilizer-code condition).
2. **The counting uses dimensions in the Pauli group**, not ranks of a vector space.
   The $X$-type and $Z$-type generators span two independent symplectic directions, so
   $\operatorname{rank}(\text{gauge}) = r_X + r_Z$ (here $6+6$), rather than being
   treated as one batch of $F_2^9$ vectors and rank-ordered (which gives 8 and a wrong
   $k$). The counting formulas are: $c = c_X + c_Z$ for the rank of the center,
   $g = (r_X + r_Z - c)/2$ for the number of gauge qubits, and $k = n - c - g$. This
   module computes $r_X$, $r_Z$, $c_X$ and $c_Z$ **one by one, inside the kernel**
   ($6,6,2,2$), hence $g = 4$ and $k = 9-4-4 = 1$.

## The assertions landed here (n = 9, each closed by `by decide`)

* `bst_rX` / `bst_rZ`: the ranks of the gauge generators, 6 each;
* `bst_centerX_rank` / `bst_centerZ_rank`: the ranks of the **center**, 2 each. The
  X-type elements of the center are the products of all X's on two adjacent columns
  (weight 6) and the Z-type ones are the products of all Z's on two adjacent rows; in
  the implementation the $2^9$ vectors are filtered by "in the gauge group of its own
  type and commuting with every generator of the other type", and the rank is taken
  afterwards;
* `bstSX_mem_ker` / `bstSX_mem_gauge`: the X-type stabilizer (two adjacent columns,
  weight 6) lies both in the kernel of the other type and in the gauge group, so it is
  a stabilizer, not a logical operator;
* `bstXW_mem_ker` / `bstXW_not_mem_gauge`: the weight-3 **bare logical** (all X's on a
  single column) lies in the kernel and not in the gauge group;
* `bst_dX` / `bst_dZ`: the two distances are **exactly 3** (the lower bound by a
  weight-limited enumeration, the upper bound by an explicit witness).
  **One exception to the naming convention, recorded next to the names**: in these two
  names `bst_dX` is read in the **textbook convention** (the kernel is taken from
  `bstHz`), whereas the `_dx` of every other instance in this library follows the
  `libDX` convention (the kernel is taken from `Hx`, see the named convention in
  `Codes/DistanceLabel.lean`). Both sides are 3 here, so the numbers do not differ, and
  the companion paper's statement that the two readings agree on every instance is
  unaffected. **Do not copy these two names when writing a new instance**; use the
  named `libDX`/`textbookDX` forms to say which side is meant.

## Relation to the literature

The Bacon–Shor $[[9,1,3]]$ of the literature uses a $d\times d$ array with the
$(d-1)\times(d-1)$ faces as gauge generators; **edge** operators are used here. The two
give the same code (the $k$ and $d$ of this module agree with the literature). Edge
operators are chosen because they let the center be generated directly by whole
adjacent rows and columns, which makes the proofs shorter.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. Gauge generators (3×3 array, qubit numbering $q = 3r + c$) -/

/-- **X-type gauge generators**: horizontal edges $X_iX_j$ (two adjacent columns in the same row), 6 of them. -/
def bstHx : Matrix (Fin 6) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 3 + e 4, e 4 + e 5, e 6 + e 7, e 7 + e 8]

/-- **Z-type gauge generators**: vertical edges $Z_iZ_j$ (two adjacent rows in the same column), 6 of them. -/
def bstHz : Matrix (Fin 6) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 3, e 3 + e 6, e 1 + e 4, e 4 + e 7, e 2 + e 5, e 5 + e 8]

/-- The rank of the gauge generators (X-type), 6. -/
theorem bst_rX : (rowReduce (List.ofFn fun i => bstHx i)).length = 6 := by decide

/-- The rank of the gauge generators (Z-type), 6. -/
theorem bst_rZ : (rowReduce (List.ofFn fun i => bstHz i)).length = 6 := by decide

/-! ## 2. The rank of the center (the stabilizer)

The center is defined as the elements that lie in the gauge group of their own type and
commute with **every** generator of the other type. At $n = 9$ the whole space holds
only $2^9$ vectors, so filtering once and taking the rank is much shorter than working
with submodule language. -/

/-- The X-type part of the center: the **non-zero** vectors that lie in the gauge group of their own
type and commute with every Z-type generator. -/
def bstCenterX : List (Vec 9) :=
  (lightVecs 9 9).filter (fun v => decide (
    v ≠ 0 ∧ inSpanB (List.ofFn fun i => bstHx i) v = true ∧
      (List.ofFn fun i => bstHz i).all (fun z => decide (z ⬝ᵥ v = 0))))

/-- The Z-type part of the center. -/
def bstCenterZ : List (Vec 9) :=
  (lightVecs 9 9).filter (fun v => decide (
    v ≠ 0 ∧ inSpanB (List.ofFn fun i => bstHz i) v = true ∧
      (List.ofFn fun i => bstHx i).all (fun z => decide (z ⬝ᵥ v = 0))))

/-- **The rank of the center (X-type) = 2**. -/
theorem bst_centerX_rank : (rowReduce bstCenterX).length = 2 := by decide

/-- **The rank of the center (Z-type) = 2**. -/
theorem bst_centerZ_rank : (rowReduce bstCenterZ).length = 2 := by decide

/-- **Counting**: $c = c_X + c_Z = 4$, $g = (r_X+r_Z-c)/2 = 4$, $k = n - c - g = 1$.

Every term on the left is given by one of the four kernel-checked assertions above
($r_X = r_Z = 6$ from `bst_rX`/`bst_rZ`, $c_X = c_Z = 2$ from
`bst_centerX_rank`/`bst_centerZ_rank`), so this theorem is arithmetic that substitutes
**machine-checked inputs** into the formulas, not an independent claim. -/
theorem bst_k : 9 - (2 + 2) - ((6 + 6 - (2 + 2)) / 2) = 1 := by decide

/-! ## 3. Stabilizers and bare logicals -/

/-- The X-type stabilizer: the product of all X's on two adjacent columns (weight 6). -/
def bstSX : Vec 9 := e 0 + e 3 + e 6 + e 1 + e 4 + e 7

/-- The Z-type stabilizer: the product of all Z's on two adjacent rows (weight 6). -/
def bstSZ : Vec 9 := e 0 + e 1 + e 2 + e 3 + e 4 + e 5

/-- A witness for the X-type bare logical: **all X's on a single column** (weight 3). -/
def bstXW : Vec 9 := e 0 + e 3 + e 6

/-- A witness for the Z-type bare logical: all Z's on a single row (weight 3). -/
def bstZW : Vec 9 := e 0 + e 1 + e 2

/-- The stabilizer commutes with every generator of the other type (so it lies in the center). -/
theorem bstSX_mem_ker : bstHz *ᵥ bstSX = 0 := by decide

/-- The stabilizer **is in the gauge group**, which is exactly why it cannot serve as a logical operator. -/
theorem bstSX_mem_gauge : inSpanB (List.ofFn fun i => bstHx i) bstSX = true := by decide

/-- The bare logical commutes with every generator of the other type. -/
theorem bstXW_mem_ker : bstHz *ᵥ bstXW = 0 := by decide

/-- The bare logical is **not** in the gauge group. -/
theorem bstXW_not_mem_gauge : inSpanB (List.ofFn fun i => bstHx i) bstXW = false := by decide

/-! ## 4. The two distances are $= 3$ -/

/-- **X-type distance**: $\min\{\mathrm{wt}(v) : v\in\ker H_Z,\ v\notin\mathrm{row}\,H_X\} = 3$.

The lower bound comes from a weight-limited enumeration (the candidate set of weight
$\le2$ is empty) and the upper bound from the explicit witness `bstXW`. -/
theorem bst_dX : min_weight_ker_not_mem_rowspace bstHz bstHx = 3 :=
  eq_minWeight_of_decide (d := 3) bstHz bstHx (by decide) (by decide) (E := bstXW)
    (mem_ker_of_inKerB bstHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false bstHx (by decide))
    (by decide)

/-- **Z-type distance**: the symmetric side. -/
theorem bst_dZ : min_weight_ker_not_mem_rowspace bstHx bstHz = 3 :=
  eq_minWeight_of_decide (d := 3) bstHx bstHz (by decide) (by decide) (E := bstZW)
    (mem_ker_of_inKerB bstHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false bstHz (by decide))
    (by decide)

end QECCertificates
