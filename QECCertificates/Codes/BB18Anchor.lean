/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix

/-!
# BB 锚点：$[[18,4,4]]$ 全参数（IBM BB 族最小实例，gauging 基码）

校验矩阵从 Lean-QEC 公开示例的 BitVec 十六进制**逐行重建**（行主序、LSB），
本模块把它落到本库 GF(2) 表示层并给出**全参数**：$k=4$（行消元直算）、
$dX=dZ=4$（下界 `lightSet` 为空 + 上界显式重量-4 见证）。
这是"BB[[18,4,4]] 经 K4 辅助图 gauging 得 [[24,3,4]]"这条断言的
**基码**——gauging 实例以此为出发点。
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- BB18 的 X 型校验（$H_X=[A\mid B]$，重建自 Lean-QEC hex）。 -/
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

/-- BB18 的 Z 型校验（$H_Z=[B^\top\mid A^\top]$）。 -/
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

/-- X 型见证：重量 4 的 X 逻辑算符。 -/
def bb18XW : Vec 18 := (e 0 + e 2 + e 6 + e 9 : Vec 18)

/-- Z 型见证：与 X 见证配对为 1。 -/
def bb18ZW : Vec 18 := (e 0 + e 3 + e 5 + e 12 : Vec 18)

/-- X 校验的行列表（字面量，桥接 `List.ofFn`）。 -/
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

/-- Z 校验的行列表。 -/
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

/-- **BB18 维数**：$18 - 7 - 7 = 4$。陈述针对**校验矩阵本身**（经 `List.ofFn` 桥接行列表），
与 `toric3_k` 的既定范式一致。 -/
theorem bb18_k : 18 - (rowReduce (List.ofFn fun i => bb18Hx i)).length
    - (rowReduce (List.ofFn fun i => bb18Hz i)).length = 4 := by
  rw [bb18_ofFn_x, bb18_ofFn_z]
  decide

/-- **BB18 的 X 侧码距 = 4**。 -/
theorem bb18_dx : min_weight_ker_not_mem_rowspace bb18Hx bb18Hz = 4 :=
  eq_minWeight_of_decide (d := 4) bb18Hx bb18Hz (by decide) (by decide) (E := bb18XW)
    (mem_ker_of_inKerB bb18Hx (by decide))
    (not_mem_rowSpace_of_dualCheck bb18Hz (w := bb18ZW) (by decide) (by decide))
    (by decide)

/-- **BB18 的 Z 侧码距 = 4**。 -/
theorem bb18_dz : min_weight_ker_not_mem_rowspace bb18Hz bb18Hx = 4 :=
  eq_minWeight_of_decide (d := 4) bb18Hz bb18Hx (by decide) (by decide) (E := bb18ZW)
    (mem_ker_of_inKerB bb18Hz (by decide))
    (not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18XW) (by decide) (by decide))
    (by decide)

end QECCertificates
