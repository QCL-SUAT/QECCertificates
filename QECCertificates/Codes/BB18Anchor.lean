/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.CaseMatrix

/-!
# The BB anchor: all parameters of $[[18,4,4]]$ (the smallest instance of the IBM BB family, the base code of gauging)

The parity-check matrices are **rebuilt row by row** from the BitVec hexadecimal form of a
public Lean-QEC example (row-major, LSB). This module lands them on the library's GF(2)
representation layer and records **all parameters**: $k=4$ (by direct row reduction) and
$dX=dZ=4$ (a lower bound from an empty `lightSet` plus an upper bound from an explicit
weight-4 witness). This is the **base code** of the statement that gauging BB$[[18,4,4]]$
on the $K_4$ auxiliary graph gives $[[24,3,4]]$: the gauging instance starts here.
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The X-type checks of BB18 ($H_X=[A\mid B]$, rebuilt from the Lean-QEC hex form). -/
def bb18Hx : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of ![
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 18),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 18),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 18),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 18),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 18),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 18),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 18),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 18),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 18)
  ]

/-- The Z-type checks of BB18 ($H_Z=[B^\top\mid A^\top]$). -/
def bb18Hz : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of ![
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 18),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 18),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 18),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 18),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 18),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 18),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 18),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 18),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 18)
  ]

/-- The X-type witness: a weight-4 X logical operator. -/
def bb18XW : Vec 18 := (e 0 + e 2 + e 6 + e 9 : Vec 18)

/-- The Z-type witness: it pairs with the X witness to give 1. -/
def bb18ZW : Vec 18 := (e 0 + e 3 + e 5 + e 12 : Vec 18)

/-- The rows of the X checks as an explicit list (bridging to `List.ofFn`). -/
def bb18Rx : List (Vec 18) :=
  [
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 18),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 18),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 18),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 18),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 18),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 18),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 18),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 18),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 18)
  ]

/-- The rows of the Z checks as an explicit list. -/
def bb18Rz : List (Vec 18) :=
  [
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 18),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 18),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 18),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 18),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 18),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 18),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 18),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 18),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 18)
  ]

theorem bb18_ofFn_x : List.ofFn (fun i => bb18Hx i) = bb18Rx := by decide
theorem bb18_ofFn_z : List.ofFn (fun i => bb18Hz i) = bb18Rz := by decide

/--
**The dimension of BB18**: $18 - 7 - 7 = 4$. The statement is about the **parity-check
matrices themselves** (bridged to the row lists by `List.ofFn`) and matches the established
form of `toric3_k`.
-/
theorem bb18_k : 18 - (rowReduce (List.ofFn fun i => bb18Hx i)).length
    - (rowReduce (List.ofFn fun i => bb18Hz i)).length = 4 := by
  rw [bb18_ofFn_x, bb18_ofFn_z]
  decide

/-- **The X-side distance of BB18 is 4**. -/
theorem bb18_dx : min_weight_ker_not_mem_rowspace bb18Hx bb18Hz = 4 :=
  eq_minWeight_of_decide (d := 4) bb18Hx bb18Hz (by decide) (by decide) (E := bb18XW)
    (mem_ker_of_inKerB bb18Hx (by decide))
    (not_mem_rowSpace_of_dualCheck bb18Hz (w := bb18ZW) (by decide) (by decide))
    (by decide)

/-- **The Z-side distance of BB18 is 4**. -/
theorem bb18_dz : min_weight_ker_not_mem_rowspace bb18Hz bb18Hx = 4 :=
  eq_minWeight_of_decide (d := 4) bb18Hz bb18Hx (by decide) (by decide) (E := bb18ZW)
    (mem_ker_of_inKerB bb18Hz (by decide))
    (not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18XW) (by decide) (by decide))
    (by decide)

end QECCertificates
