/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

import QECCertificates.GF2.LowerBound

/-!
# The case matrix: machine-checked claims about code parameters, end to end

The goal is a machine check of **at least 3 code families and at least 10 sets of code
parameters**, carried out here instance by instance. For each code the module provides

* an **explicit parity-check matrix**, that is, concrete computable data rather than an
  abstract existence statement;
* the **dimension `k`**: `n - Σ rank(parity checks)`, the rank being the number of rows
  produced by `rowReduce`;
* **both bounds**: the lower bound from `lightSet` being empty (`by decide`, the kernel
  enumerating the whole Pauli space itself) and the upper bound from an **explicit
  low-weight logical operator**. Squeezing the two sides with `eq_minWeight_of_decide`
  yields that the code distance is **exactly** $d$.

**Trusted base**: nothing but `by decide`, that is, kernel computation. No SAT solver, no
`native_decide`, no custom axiom.

## One interface for three kinds of code

| kind of code | `M₁` (supplies the kernel) | `M₂` (supplies the row space) | weight |
|---|---|---|---|
| classical linear code | the parity-check matrix `H` | the zero-row matrix (`rowSpace = ⊥`) | weight of a nonzero codeword |
| CSS code | one side's parity checks | the other side's | weight of a logical operator |
| general stabilizer code | the **symplectic transpose** of the generators | the generators themselves | Pauli weight |

## Independent cross-check

Every set of parameters has also been recomputed by brute force with a script that follows
an independent route: it performs only GF(2) bit operations and is entirely separate from
the kernel reduction. **That script is not part of this repository**; it lives in a
companion development. A `Numbers` passage in the companion paper records the same thing in
the same terms.
-/

namespace QECCertificates

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000


/-- Concatenating a symplectic pair of vectors: `z` in the first `n` positions and `x` in
the last `n`.

**The `if`-lambda is deliberate, in place of `Fin.append`**: under kernel reduction the
elimination rules of `Fin.append` get stuck on the proof transport of `Fin.cast` and
`Fin.natAdd`, so `by decide` cannot reduce it, and the measured failure is
"reduction got stuck"; an explicit branch reduces coordinate by coordinate. -/
def zx {n : ℕ} (z x : Vec n) : Vec (n + n) :=
  fun i => if h : (i : ℕ) < n then z ⟨i, h⟩ else x ⟨(i : ℕ) - n, by omega⟩

/-- The symplectic concatenation in the 5-bit case, with the length parameter pinned to 5
so that `?n + ?n = 10` does not disturb elaboration. -/
abbrev zx5 (z x : Vec 5) : Vec 10 := zx z x

/-! ## 1. The repetition-code family $[n,1,n]$ -/

/-- The parity-check matrix of the $[3,1,3]$ repetition code. -/
def rep3H : Matrix (Fin 2) (Fin 3) (ZMod 2) := Matrix.of ![e 0 + e 1, e 1 + e 2]

/-- The all-ones vector, the only nonzero codeword of the repetition code. -/
def rep3W : Vec 3 := e 0 + e 1 + e 2

theorem rep3_k : 3 - (rowReduce (List.ofFn fun i => rep3H i)).length = 1 := by decide

/-- $[3,1,3]$: the distance is exactly 3. -/
theorem rep3_d : min_weight_ker_not_mem_rowspace rep3H (zeroRows 3) = 3 :=
  eq_minWeight_of_decide (d := 3) rep3H (zeroRows 3) (by decide) (by decide) (E := rep3W)
    (mem_ker_of_inKerB rep3H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 3) (by decide))
    (by decide)

/-- The parity-check matrix of the $[5,1,5]$ repetition code. -/
def rep5H : Matrix (Fin 4) (Fin 5) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 2 + e 3, e 3 + e 4]

def rep5W : Vec 5 := e 0 + e 1 + e 2 + e 3 + e 4

theorem rep5_k : 5 - (rowReduce (List.ofFn fun i => rep5H i)).length = 1 := by decide

theorem rep5_d : min_weight_ker_not_mem_rowspace rep5H (zeroRows 5) = 5 :=
  eq_minWeight_of_decide (d := 5) rep5H (zeroRows 5) (by decide) (by decide) (E := rep5W)
    (mem_ker_of_inKerB rep5H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 5) (by decide))
    (by decide)

/-- The parity-check matrix of the $[7,1,7]$ repetition code. -/
def rep7H : Matrix (Fin 6) (Fin 7) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 2 + e 3, e 3 + e 4, e 4 + e 5, e 5 + e 6]

def rep7W : Vec 7 := e 0 + e 1 + e 2 + e 3 + e 4 + e 5 + e 6

theorem rep7_k : 7 - (rowReduce (List.ofFn fun i => rep7H i)).length = 1 := by decide

theorem rep7_d : min_weight_ker_not_mem_rowspace rep7H (zeroRows 7) = 7 :=
  eq_minWeight_of_decide (d := 7) rep7H (zeroRows 7) (by decide) (by decide) (E := rep7W)
    (mem_ker_of_inKerB rep7H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 7) (by decide))
    (by decide)

/-! ## 2. The classical Hamming family

The columns of the parity-check matrix are the binary expansions of the position numbers,
which start at 1. This is exactly the construction in which any two columns are linearly
independent while some three are dependent, so the minimum distance is exactly 3. -/

/-- The parity-check matrix of the $[7,4,3]$ Hamming code (the columns are the binary
expansions of 1…7). -/
def ham7H : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 4 + e 6, e 1 + e 2 + e 5 + e 6, e 3 + e 4 + e 5 + e 6]

/-- A weight-3 codeword: columns 1…3 sum to zero. -/
def ham7W : Vec 7 := e 0 + e 1 + e 2

theorem ham7_k : 7 - (rowReduce (List.ofFn fun i => ham7H i)).length = 4 := by decide

theorem ham7_d : min_weight_ker_not_mem_rowspace ham7H (zeroRows 7) = 3 :=
  eq_minWeight_of_decide (d := 3) ham7H (zeroRows 7) (by decide) (by decide) (E := ham7W)
    (mem_ker_of_inKerB ham7H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 7) (by decide))
    (by decide)

/-- The parity-check matrix of the $[15,11,3]$ Hamming code (the columns are the binary
expansions of 1…15).

$n = 15$ is the **first point at which the weight-bounded enumeration succeeds**:
enumerating the whole space left this case unfinished after more than three minutes, whereas
`lightVecs 15 2` offers 121 candidates instead of 32768 and passes in seconds. -/
def ham15H : Matrix (Fin 4) (Fin 15) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 4 + e 6 + e 8 + e 10 + e 12 + e 14,
              e 1 + e 2 + e 5 + e 6 + e 9 + e 10 + e 13 + e 14,
              e 3 + e 4 + e 5 + e 6 + e 11 + e 12 + e 13 + e 14,
              e 7 + e 8 + e 9 + e 10 + e 11 + e 12 + e 13 + e 14]

def ham15W : Vec 15 := e 0 + e 1 + e 2

theorem ham15_k : 15 - (rowReduce (List.ofFn fun i => ham15H i)).length = 11 := by decide

theorem ham15_d : min_weight_ker_not_mem_rowspace ham15H (zeroRows 15) = 3 :=
  eq_minWeight_of_decide (d := 3) ham15H (zeroRows 15) (by decide) (by decide) (E := ham15W)
    (mem_ker_of_inKerB ham15H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 15) (by decide))
    (by decide)

/-! ## 3. The Steane code $[[7,1,3]]$ (the quantum Hamming code)

$H_X = H_Z = $ the parity-check matrix of the Hamming $[7,4,3]$ code. When the two sides use
the same matrix, `dX = f(H₂,H₁)` and `dZ = f(H₁,H₂)` are the same number. -/

def steaneHx : Matrix (Fin 3) (Fin 7) (ZMod 2) := ham7H

def steaneHz : Matrix (Fin 3) (Fin 7) (ZMod 2) := ham7H

/-- A weight-3 logical operator. The X side and the Z side share this one witness, which
is the symmetry between X and Z in the Steane code. -/
def steaneW : Vec 7 := e 0 + e 1 + e 2

theorem steane_k : 7 - (rowReduce (List.ofFn fun i => steaneHx i)).length
    - (rowReduce (List.ofFn fun i => steaneHz i)).length = 1 := by decide

theorem steane_dx : min_weight_ker_not_mem_rowspace steaneHx steaneHz = 3 :=
  eq_minWeight_of_decide (d := 3) steaneHx steaneHz (by decide) (by decide) (E := steaneW)
    (mem_ker_of_inKerB steaneHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false steaneHz (by decide))
    (by decide)

theorem steane_dz : min_weight_ker_not_mem_rowspace steaneHz steaneHx = 3 :=
  eq_minWeight_of_decide (d := 3) steaneHz steaneHx (by decide) (by decide) (E := steaneW)
    (mem_ker_of_inKerB steaneHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false steaneHx (by decide))
    (by decide)

/-! ## 4. The Shor code $[[9,1,3]]$ (three-level concatenation)

The 9 bits form 3 blocks. The Z-type checks are the `ZZ` pairs of neighbouring bits within
a block, 6 of them; the X-type checks are `XXXXXX` over a whole block, the first two blocks
and the last two, 2 in total. -/

def shorHx : Matrix (Fin 2) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 1 + e 2 + e 3 + e 4 + e 5, e 3 + e 4 + e 5 + e 6 + e 7 + e 8]

def shorHz : Matrix (Fin 6) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 3 + e 4, e 4 + e 5, e 6 + e 7, e 7 + e 8]

/-- The witness for `dX`: one bit from each block, a cross-block operator, of weight 3. -/
def shorXW : Vec 9 := e 0 + e 3 + e 6

/-- The witness for `dZ`: a whole-block flip, of weight 3. -/
def shorZW : Vec 9 := e 0 + e 1 + e 2

theorem shor_k : 9 - (rowReduce (List.ofFn fun i => shorHx i)).length
    - (rowReduce (List.ofFn fun i => shorHz i)).length = 1 := by decide

theorem shor_dx : min_weight_ker_not_mem_rowspace shorHx shorHz = 3 :=
  eq_minWeight_of_decide (d := 3) shorHx shorHz (by decide) (by decide) (E := shorXW)
    (mem_ker_of_inKerB shorHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false shorHz (by decide))
    (by decide)

theorem shor_dz : min_weight_ker_not_mem_rowspace shorHz shorHx = 3 :=
  eq_minWeight_of_decide (d := 3) shorHz shorHx (by decide) (by decide) (E := shorZW)
    (mem_ker_of_inKerB shorHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false shorHx (by decide))
    (by decide)

/-! ## 5. The $[[4,2,2]]$ code

$H_X = H_Z = (1,1,1,1)$: the only check is the overall parity, so every codeword has even
weight, and a weight-2 codeword such as `e₀+e₁` is not itself a check, so the distance is
exactly 2. -/

def fourHx : Matrix (Fin 1) (Fin 4) (ZMod 2) := Matrix.of ![e 0 + e 1 + e 2 + e 3]

def fourHz : Matrix (Fin 1) (Fin 4) (ZMod 2) := Matrix.of ![e 0 + e 1 + e 2 + e 3]

def fourW : Vec 4 := e 0 + e 1

theorem four_k : 4 - (rowReduce (List.ofFn fun i => fourHx i)).length
    - (rowReduce (List.ofFn fun i => fourHz i)).length = 2 := by decide

theorem four_dx : min_weight_ker_not_mem_rowspace fourHx fourHz = 2 :=
  eq_minWeight_of_decide (d := 2) fourHx fourHz (by decide) (by decide) (E := fourW)
    (mem_ker_of_inKerB fourHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false fourHz (by decide))
    (by decide)

theorem four_dz : min_weight_ker_not_mem_rowspace fourHz fourHx = 2 :=
  eq_minWeight_of_decide (d := 2) fourHz fourHx (by decide) (by decide) (E := fourW)
    (mem_ker_of_inKerB fourHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false fourHx (by decide))
    (by decide)

/-! ## 6. The toric code $[[8,2,2]]$ ($2\times 2$ torus, the topological family)

There are 8 edges, 4 horizontal and 4 vertical; the vertex star operators are X-type and
the face operators are Z-type, 4 of each. On a $2\times2$ torus the horizontal and vertical
struts are pairwise parallel, so the shortest nontrivial cycle has length 2. -/

def toricHz : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 4 + e 5, e 1 + e 3 + e 4 + e 5,
              e 0 + e 2 + e 6 + e 7, e 1 + e 3 + e 6 + e 7]

def toricHx : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  Matrix.of ![e 0 + e 1 + e 4 + e 6, e 0 + e 1 + e 5 + e 7,
              e 2 + e 3 + e 4 + e 6, e 2 + e 3 + e 5 + e 7]

/-- A nontrivial cycle made of a pair of parallel edges. -/
def toricXW : Vec 8 := e 0 + e 1

/-- A pair of parallel edges in the other direction. -/
def toricZW : Vec 8 := e 0 + e 2

theorem toric_k : 8 - (rowReduce (List.ofFn fun i => toricHx i)).length
    - (rowReduce (List.ofFn fun i => toricHz i)).length = 2 := by decide

theorem toric_dx : min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  eq_minWeight_of_decide (d := 2) toricHx toricHz (by decide) (by decide) (E := toricXW)
    (mem_ker_of_inKerB toricHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false toricHz (by decide))
    (by decide)

theorem toric_dz : min_weight_ker_not_mem_rowspace toricHz toricHx = 2 :=
  eq_minWeight_of_decide (d := 2) toricHz toricHx (by decide) (by decide) (E := toricZW)
    (mem_ker_of_inKerB toricHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false toricHx (by decide))
    (by decide)

/-- **The toric code $[[18,2,3]]$** ($3\\times 3$ torus, the topological family): 18 edges.

$n = 18$ is the **frontier** reached by the weight-bounded enumeration: enumerating the
whole space ($2^{18} = 262144$) is not feasible, whereas `lightVecs 18 2` has only 172
candidates. -/
def toric3Hz : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of ![e 0 + e 3 + e 9 + e 10, e 1 + e 4 + e 10 + e 11, e 2 + e 5 + e 9 + e 11,
              e 3 + e 6 + e 12 + e 13, e 4 + e 7 + e 13 + e 14, e 5 + e 8 + e 12 + e 14,
              e 0 + e 6 + e 15 + e 16, e 1 + e 7 + e 16 + e 17, e 2 + e 8 + e 15 + e 17]

def toric3Hx : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 9 + e 15, e 0 + e 1 + e 10 + e 16, e 1 + e 2 + e 11 + e 17,
              e 3 + e 5 + e 9 + e 12, e 3 + e 4 + e 10 + e 13, e 4 + e 5 + e 11 + e 14,
              e 6 + e 8 + e 12 + e 15, e 6 + e 7 + e 13 + e 16, e 7 + e 8 + e 14 + e 17]

/-- The row-list form of `toric3Hz`.

**Why it is needed**: on wide 18 matrices the kernel-reduction cost of `rowReduce` comes
mostly from the indexing layer of `Matrix.of` and `List.ofFn`: the same elimination finishes
in about 95 seconds in the pure `List` form, whereas under `Matrix.of ![…]` plus `ofFn` it
burns through the heartbeat budget after 5 minutes. The rank claim for `k` therefore goes
through a row list together with a bridging equation
(`toric3_ofFn_hz`/`toric3_ofFn_hx` plus `toric3_k`). -/
def toric3Rz : List (Vec 18) :=
  [e 0 + e 3 + e 9 + e 10, e 1 + e 4 + e 10 + e 11, e 2 + e 5 + e 9 + e 11,
   e 3 + e 6 + e 12 + e 13, e 4 + e 7 + e 13 + e 14, e 5 + e 8 + e 12 + e 14,
   e 0 + e 6 + e 15 + e 16, e 1 + e 7 + e 16 + e 17, e 2 + e 8 + e 15 + e 17]

/-- The row-list form of `toric3Hx` (as above). -/
def toric3Rx : List (Vec 18) :=
  [e 0 + e 2 + e 9 + e 15, e 0 + e 1 + e 10 + e 16, e 1 + e 2 + e 11 + e 17,
   e 3 + e 5 + e 9 + e 12, e 3 + e 4 + e 10 + e 13, e 4 + e 5 + e 11 + e 14,
   e 6 + e 8 + e 12 + e 15, e 6 + e 7 + e 13 + e 16, e 7 + e 8 + e 14 + e 17]

/-- The row list and the matrix form agree row by row, a pure index comparison that the
kernel performs in milliseconds.

**The parentheses are not optional**: without them the lambda body of
`fun i => toric3Hz i = toric3Rz` would take in the whole equation. -/
theorem toric3_ofFn_hz : (List.ofFn fun i => toric3Hz i) = toric3Rz := by decide

/-- As above, on the `Hx` side. -/
theorem toric3_ofFn_hx : (List.ofFn fun i => toric3Hx i) = toric3Rx := by decide

set_option maxHeartbeats 40000000 in
/-- **The dimension $k = 2$**: $18 - \operatorname{rank}(H_x) - \operatorname{rank}(H_z)$,
where both ranks are 8: every edge belongs to exactly two faces, the 9 check rows sum to
zero, and any 8 of them are independent.

The proof first `rw`s the bridging equations to replace the `List.ofFn` layer by a pure row
list and then runs `decide`. The pure `List` form takes about 95 seconds, more than three
times faster than `decide` directly on the `ofFn` form, which times out after 5 minutes. The
heartbeat budget is raised to 40M per theorem, since the module default of 8M is not
enough. -/
theorem toric3_k : 18 - (rowReduce (List.ofFn fun i => toric3Hx i)).length
    - (rowReduce (List.ofFn fun i => toric3Hz i)).length = 2 := by
  rw [toric3_ofFn_hx, toric3_ofFn_hz]
  decide

/-- A short cycle winding once around the torus, of 3 edges. -/
def toric3XW : Vec 18 := e 0 + e 1 + e 2

/-- A short cycle in the other direction. -/
def toric3ZW : Vec 18 := e 0 + e 3 + e 6

theorem toric3_dx : min_weight_ker_not_mem_rowspace toric3Hx toric3Hz = 3 :=
  eq_minWeight_of_decide (d := 3) toric3Hx toric3Hz (by decide) (by decide) (E := toric3XW)
    (mem_ker_of_inKerB toric3Hx (by decide))
    (not_mem_rowSpace_of_dualCheck toric3Hz (w := toric3ZW) (by decide) (by decide))
    (by decide)

theorem toric3_dz : min_weight_ker_not_mem_rowspace toric3Hz toric3Hx = 3 :=
  eq_minWeight_of_decide (d := 3) toric3Hz toric3Hx (by decide) (by decide) (E := toric3ZW)
    (mem_ker_of_inKerB toric3Hz (by decide))
    (not_mem_rowSpace_of_dualCheck toric3Hx (w := toric3XW) (by decide) (by decide))
    (by decide)

/-! ## 7. The $[[5,1,3]]$ perfect code (not CSS, so it goes through the symplectic layer)

$[[5,1,3]]$ is the only nondegenerate 5-bit code that corrects a single-bit error, and it is
**not a CSS code**, so it has to go through the general symplectic representation. The
encoding: a generator is written as a 10-bit vector `g` concatenating its Z half with its X
half, the normalizer condition `⟨g, v⟩ = 0` is equivalent to `v` being orthogonal to `J g`,
where `J` exchanges the two halves, and so `d = f(J's row matrix, the generator matrix)`
while `k = n − rank(G)`.

The generators, in the standard form:
`X Z Z X I`, `I X Z Z X`, `X I X Z Z`, `Z X I X Z`. -/

/-- The generator matrix: row `i` is `zx (Z half) (X half)`. -/
def p5G : Matrix (Fin 4) (Fin 10) (ZMod 2) :=
  Matrix.of ![zx5 (e 1 + e 2) (e 0 + e 3),
              zx5 (e 2 + e 3) (e 1 + e 4),
              zx5 (e 3 + e 4) (e 0 + e 2),
              zx5 (e 0 + e 4) (e 1 + e 3)]

/-- The symplectic transpose: row `i` is generator `i` with its two halves exchanged, the
Z half and the X half swapped. -/
def p5J : Matrix (Fin 4) (Fin 10) (ZMod 2) :=
  Matrix.of ![zx5 (e 0 + e 3) (e 1 + e 2),
              zx5 (e 1 + e 4) (e 2 + e 3),
              zx5 (e 0 + e 2) (e 3 + e 4),
              zx5 (e 1 + e 3) (e 0 + e 4)]

/-- A weight-3 logical operator: weight 2 in the `Z` half and weight 1 in the `X`
half. -/
def p5W : Vec 10 := zx5 (e 1 + e 4) (e 0)

/-- **The generators commute pairwise**: every row of `J` is orthogonal to every row of
`G`, symplectic commutation being ordinary orthogonality. -/
theorem p5_pairwise_commute : ∀ i j : Fin 4, (p5J i) ⬝ᵥ (p5G j) = 0 := by decide

/-- $k = n - \operatorname{rank}(G)$: four independent generators, hence one logical
qubit. -/
theorem p5_k : 5 - (rowReduce (List.ofFn fun i => p5G i)).length = 1 := by decide

/-- $[[5,1,3]]$: the distance is exactly 3. -/
theorem p5_d : min_weight_ker_not_mem_rowspace p5J p5G = 3 :=
  eq_minWeight_of_decide (d := 3) p5J p5G (by decide) (by decide) (E := p5W)
    (mem_ker_of_inKerB p5J (by decide))
    (not_mem_rowSpace_of_inSpanB_false p5G (by decide))
    (by decide)

/-! ## Summary of the case matrix

| code | $n$ | $k$ | $d$ | family |
|---|---|---|---|---|
| `rep3_d` | 3 | 1 | 3 | repetition |
| `rep5_d` | 5 | 1 | 5 | repetition |
| `rep7_d` | 7 | 1 | 7 | repetition |
| `ham7_d` | 7 | 4 | 3 | classical Hamming |
| `ham15_d` | 15 | 11 | 3 | classical Hamming |
| `steane_dx`/`steane_dz` | 7 | 1 | 3 | quantum Hamming (CSS) |
| `shor_dx`/`shor_dz` | 9 | 1 | 3 | concatenated (CSS) |
| `four_dx`/`four_dz` | 4 | 2 | 2 | small CSS |
| `toric_dx`/`toric_dz` | 8 | 2 | 2 | topological ($2\times2$ torus) |
| `toric3_k`/`toric3_dx`/`toric3_dz` | 18 | 2 | 3 | topological ($3\times3$ torus) |
| `p5_d` | 5 | 1 | 3 | perfect (not CSS) |

That is **7 code families and 16 sets of code parameters**.

For the $3\times3$ toric code ($n = 18$) the **full set of parameters** $[[18,2,3]]$ is
machine-checked. On wide matrices two implementation routes are both indispensable: the
**distance upper bound** goes through a **dual witness** (`not_mem_rowSpace_of_dualCheck`,
which performs no row elimination and brings the whole module down from 304 s to 16 s),
while the **rank and `k`** go through a **row-list bridge**, since the
`Matrix.of`/`List.ofFn` indexing layer times out after 5 minutes whereas the pure `List`
form takes about 95 s. -/

end QECCertificates
