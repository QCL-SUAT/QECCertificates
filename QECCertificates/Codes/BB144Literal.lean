/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB144Distance
import QECCertificates.Codes.BB144Witness

/-!
# BB $[[144,12,12]]$: the literal matrix **is** the QECLean spelling (the last step towards $d=12$)

`Codes/BB144Witness.lean` supplies a weight-12 witness on the **literal** $72\times144$
parity-check matrices `bb144Hx`/`bb144Hz` of this library, which gives the upper bound
$d\le12$. The Gross theorem that `Codes/BB144Distance.lean` imports from QECLean gives
the lower bound $12\le d$ on the **group-ring spelling** `LE_X`/`LE_Z`. The two hold
independently of each other, and the step in between is exactly this matrix identity:
this module establishes it, so that both ends of $d=12$ land on the same object, namely
the matrices of this library.

## Proof route

Applying `by decide` to a whole matrix times out at 8000000 heartbeats (the entries of
`LE_X` unfold the `Matrix.kronecker_fin`/`reindex`/`cyclic_shift` chain). The route taken
is **entry by entry**:

* the outer `funext g` + `fin_cases g` splits into **rows** ($144$ entries per goal), and
  the inner `funext c` + `fin_cases c` splits into **single entries**, each closed by
  `decide`.

Measured: one `decide` for a whole row takes about $28$ seconds (a single huge
`Decidable` term), whereas the entrywise route averages about $3$ seconds per row, the
same mathematical content at an order of magnitude less. The whole module (both sides)
takes about $5$ minutes, the same order as `BB144Witness`, and is a one-off cost.

## Conclusion

With the identity in place, the two sides close to the exact distance **on the matrices of
this library**:

* `bb144_dX_eq_12` / `bb144_dZ_eq_12`: $\min\{\mathrm{wt}(v): v\in\ker H_X,\
  v\notin\mathrm{row}\,H_Z\}=12$ and its dual, with the upper bound from the weight-12
  witness of this library and the lower bound from the imported Gross theorem.

The lower bound is still carried over from QECLean's per-code analytic proof: it is not
re-proved here, and it is not an LRAT replay either. What this module adds is the step
that **their matrices and ours are the same one**.
-/

namespace QECCertificates

open _root_.Matrix

open QECCertificates.BB144Distance

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. The literal matrix equals the group-ring spelling (entrywise) -/

/-- **X-side identity**: the literal `bb144Hx` of this library is the QECLean spelling
`LE_X` of `BB144_X_mat`. -/
theorem bb144Hx_eq_LE_X : bb144Hx = LE_X := by
  funext g
  fin_cases g <;> (funext c; fin_cases c <;> decide)

/-- **Z-side identity**: the literal `bb144Hz` of this library is `LE_Z`. -/
theorem bb144Hz_eq_LE_Z : bb144Hz = LE_Z := by
  funext g
  fin_cases g <;> (funext c; fin_cases c <;> decide)

/-! ## 2. The exact distance on the matrices of this library: $d_X=d_Z=12$ -/

/-- **$d_X=12$ (on the literal matrices of this library)**: the upper bound is the
weight-12 witness of this library (`bb144_libDX_le_12`) and the lower bound is the
imported Gross theorem (`BB144_dZ_ge_12`). Note that `libDX` takes the X-type checks as
its kernel, so it is the textbook $d_X$ with the two sides interchanged; see
`Codes/DistanceLabel.lean`. -/
theorem bb144_dX_eq_12 : min_weight_ker_not_mem_rowspace bb144Hx bb144Hz = 12 := by
  refine le_antisymm bb144_libDX_le_12 ?_
  have h := BB144_dZ_ge_12
  rwa [← bb144Hx_eq_LE_X, ← bb144Hz_eq_LE_Z] at h

/-- **$d_Z=12$ (on the literal matrices of this library)**: the mirror image. -/
theorem bb144_dZ_eq_12 : min_weight_ker_not_mem_rowspace bb144Hz bb144Hx = 12 := by
  refine le_antisymm bb144_libDZ_le_12 ?_
  have h := BB144_dX_ge_12
  rwa [← bb144Hz_eq_LE_Z, ← bb144Hx_eq_LE_X] at h

/-- **The two sides agree**: $d_X=d_Z$ on the matrices of this library, so the X/Z
labelling is unambiguous for this instance. -/
theorem bb144_dx_eq_dz :
    min_weight_ker_not_mem_rowspace bb144Hx bb144Hz
      = min_weight_ker_not_mem_rowspace bb144Hz bb144Hx := by
  rw [bb144_dX_eq_12, bb144_dZ_eq_12]

end QECCertificates
