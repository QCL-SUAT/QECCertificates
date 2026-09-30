/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.CaseMatrix

/-!
# A named instance of the timelike component: the repetition-measurement detector code with $m = 3$ checks and $T = 4$ rounds

`Codes/Gauging.lean` proves the timelike component at the **family level**
(`timeLike_eq_of_repCheck` and `timeLike_weight_eq`: a nonzero vector orthogonal to every
timelike check takes a single value, so its weight is exactly the number of rounds). A
family-level theorem is stronger than any instance, but it is **not** an object that can
be named. Saying that the timelike component has a concrete instance calls for a
written-down parity-check matrix, a written-down witness, and a distance value decided
inside the kernel, of the same shape as the code instances of `Codes/CaseMatrix.lean`.
That is what this module adds.

## The shape of the detector code

$m$ checks are measured repeatedly over $T$ rounds, and the bits are labelled by check $a$
and round $t$. The timelike checks join **adjacent rounds**:

$$H_{(a,t)} = e_{a,t} + e_{a,t+1},\qquad a < m,\ t < T-1 .$$

This module takes $m = 3$ and $T = 4$, so there are $N = mT = 12$ bits and $9$ checks. A
nonzero vector in the kernel is constant along the time axis of each check, so the minimum
weight is exactly $T = 4$: **one check reporting wrongly in four consecutive rounds**,
which is the physical content of the undetectable duration of the timelike component. The
witness is `timeLike34W`.

## What this instance establishes

* `timeLike34_d`: $\min\{\mathrm{wt}(v) : Hv = 0,\ v \neq 0\} = 4$, where the lower bound
  comes from the emptiness of the candidate set of weight $\le 3$ (`by decide`) and the
  upper bound from the explicit witness;
* `timeLike34_witness_*`: the three witness facts (in the kernel, nonzero, weight 4), each
  checkable on its own;
* the relation to the family-level theorem: the general round count is covered by
  `timeLike_weight_eq`, while this instance is the **concrete** value $m = 3$. The
  family-level theorem covers an arbitrary $S$; the instance gives an object that can be
  cited by name.

## Parity with the spacelike side

The kernel-checked instance on the spacelike side is BB $[[24,3,4]]$
(`Codes/BB24Gauged.lean`). With this module, each of the two components has a named
example that can be recomputed and whose value is decided inside the kernel. That is what
the claim that the two components each have a named one rests on.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. The parity-check matrix and the witness -/

/-- The timelike parity-check matrix of the repetition-measurement detector code with
$m = 3$ and $T = 4$: $9$ rows and $12$ columns.

Bits are numbered $4a + t$ (check $a < 3$, round $t < 4$); row $(a,t)$ is the pair of
adjacent rounds $t$ and $t+1$. -/
def timeLike34H : Matrix (Fin 9) (Fin 12) (ZMod 2) :=
  Matrix.of ![
    e 0 + e 1,   e 1 + e 2,   e 2 + e 3,
    e 4 + e 5,   e 5 + e 6,   e 6 + e 7,
    e 8 + e 9,   e 9 + e 10,  e 10 + e 11
  ]

/-- Witness: **the first check errs in four consecutive rounds**, weight $4 = T$.

It is the nonzero vector of least weight in the kernel: an explicit operator for the
statement that the undetectable duration of the timelike component equals the number of
rounds. -/
def timeLike34W : Vec 12 := e 0 + e 1 + e 2 + e 3

/-! ## 2. The three witness facts -/

/-- In the kernel: $H w = 0$. -/
theorem timeLike34_witness_mem_ker : timeLike34H *ᵥ timeLike34W = 0 := by decide

/-- Nonzero. -/
theorem timeLike34_witness_ne_zero : timeLike34W ≠ 0 := by decide

/-- The weight is exactly the number of rounds, $T = 4$. -/
theorem timeLike34_witness_weight : hammingNorm timeLike34W = 4 := by decide

/-! ## 3. The minimum undetectable weight equals the number of rounds -/

/-- **The instance assertion for the timelike component**: for the detector code with
$m = 3$ and $T = 4$ the minimum undetectable weight is exactly $4$.

The lower bound is a weight-bounded enumeration (the candidate set of weight $\le 3$ is
empty, `by decide`, with $\sum_{k\le3}\binom{12}{k} = 299$ candidates), and the upper
bound is the explicit witness `timeLike34W`. -/
theorem timeLike34_d : min_weight_ker_not_mem_rowspace timeLike34H (zeroRows 12) = 4 :=
  eq_minWeight_of_decide (d := 4) timeLike34H (zeroRows 12) (by decide) (by decide)
    (E := timeLike34W)
    (mem_ker_of_inKerB timeLike34H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 12) (by decide))
    (by decide)

/-- **Each of the three checks has its own minimum-weight undetectable direction**: all
four rounds of a check block being wrong is a kernel vector, so the minimum weight is
attained three times, for $a = 0, 1, 2$ respectively.

This writes the independence of the timelike component across checks as a checkable
conjunction, and shows that the lower bound of `timeLike34_d` does not rest on an
accidental vector. -/
theorem timeLike34_block_witnesses :
    (timeLike34H *ᵥ (e 0 + e 1 + e 2 + e 3 : Vec 12) = 0 ∧
     timeLike34H *ᵥ (e 4 + e 5 + e 6 + e 7 : Vec 12) = 0 ∧
     timeLike34H *ᵥ (e 8 + e 9 + e 10 + e 11 : Vec 12) = 0) := by decide

end QECCertificates
