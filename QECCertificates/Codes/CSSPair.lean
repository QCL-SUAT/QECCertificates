/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix
import LeanQEC.Stabilizer.CSS

/-!
# 回灌 LeanQEC 的 `CSS_pair`：案例矩阵的距离结论接到上游接口（生态对齐）

本包的距离结论一直停在**自己的**公式形态——
`min_weight_ker_not_mem_rowspace M₁ M₂`（与 LeanQEC 逐字同一定义，但从未
实例化上游的 `CSS_pair` 结构）。本模块闭合这最后一层：用上游的快捷构造器
`CSS_pair.of_matrices`（只要一个"行两两正交"的内核可判条件）把案例矩阵里
**全部五个 CSS 码**（Steane、Shor、$[[4,2,2]]$、两个尺度的环面码）装进
`CSS_pair`，于是上游的 `CSS_pair.dX / dZ` 与本包案例矩阵的距离定理
逐字相等——`steanePair.dX = 3` 的证明项**就是** `steane_dx`。

至此三层闭合：① 判定层（`inSpanB`/`inKerB`）→ ② 距离层（案例矩阵的
`by decide` 断言）→ ③ 上游结构层（LeanQEC `CSS_pair`）。
**零额外数学假设**：正交条件由 `by decide` 核出，距离结论由既有定理转移。
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- "行两两正交"的裸量化形态（`mutually_orth_rows` 是 plain `def : Prop`，
实例搜索不展开它，`by decide` 合不出判定子——先经这条 `Iff.rfl` 桥）。 -/
theorem mutually_orth_rows_iff {k₁ k₂ n : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    M₁.mutually_orth_rows M₂ ↔ ∀ a b, M₁ a ⬝ᵥ M₂ b = 0 := Iff.rfl

/-! ## Steane $[[7,1,3]]$ -/

/-- Steane 码的 `CSS_pair` 实例：`H₁` = Z 校验、`H₂` = X 校验（上游约定：
`dZ = f(H₁, H₂)`、`dX = f(H₂, H₁)`，与本库 `steane_dz`/`steane_dx` 同向）。 -/
def steanePair : CSS_pair 7 3 3 :=
  CSS_pair.of_matrices steaneHz steaneHx
    ((mutually_orth_rows_iff steaneHz steaneHx).mpr (by decide))

/-- **回灌（Steane）**：上游 `CSS_pair.dX` 就是本库的 `steane_dx`——证明项逐字相同。 -/
theorem steanePair_dX : CSS_pair.dX steanePair = 3 := steane_dx

/-- **回灌（Steane）**：上游 `CSS_pair.dZ` 就是本库的 `steane_dz`。 -/
theorem steanePair_dZ : CSS_pair.dZ steanePair = 3 := steane_dz

/-! ## Shor $[[9,1,3]]$ -/

/-- Shor 码的 `CSS_pair` 实例（Z 侧 6 行、X 侧 2 行）。 -/
def shorPair : CSS_pair 9 6 2 :=
  CSS_pair.of_matrices shorHz shorHx
    ((mutually_orth_rows_iff shorHz shorHx).mpr (by decide))

/-- **回灌（Shor）**：上游 `dX` 即本库 `shor_dx`。 -/
theorem shorPair_dX : CSS_pair.dX shorPair = 3 := shor_dx

/-- **回灌（Shor）**：上游 `dZ` 即本库 `shor_dz`。 -/
theorem shorPair_dZ : CSS_pair.dZ shorPair = 3 := shor_dz

/-! ## $[[4,2,2]]$ -/

/-- $[[4,2,2]]$ 码的 `CSS_pair` 实例（两侧各 1 行）。 -/
def fourPair : CSS_pair 4 1 1 :=
  CSS_pair.of_matrices fourHz fourHx
    ((mutually_orth_rows_iff fourHz fourHx).mpr (by decide))

/-- **回灌（$[[4,2,2]]$）**：上游 `dX` 即本库 `four_dx`。 -/
theorem fourPair_dX : CSS_pair.dX fourPair = 2 := four_dx

/-- **回灌（$[[4,2,2]]$）**：上游 `dZ` 即本库 `four_dz`。 -/
theorem fourPair_dZ : CSS_pair.dZ fourPair = 2 := four_dz

/-! ## 环面码（两个尺度） -/

/-- $2\times2$ 环面码 $[[8,2,2]]$ 的 `CSS_pair` 实例。 -/
def toricPair : CSS_pair 8 4 4 :=
  CSS_pair.of_matrices toricHz toricHx
    ((mutually_orth_rows_iff toricHz toricHx).mpr (by decide))

/-- **回灌（环面 $2\times2$）**：上游 `dX` 即本库 `toric_dx`。 -/
theorem toricPair_dX : CSS_pair.dX toricPair = 2 := toric_dx

/-- **回灌（环面 $2\times2$）**：上游 `dZ` 即本库 `toric_dz`。 -/
theorem toricPair_dZ : CSS_pair.dZ toricPair = 2 := toric_dz

/-- $3\times3$ 环面码 $[[18,2,3]]$ 的 `CSS_pair` 实例（$n = 18$；
正交条件 9×9 个点积，内核秒级——与 `toric3_css` 同型）。 -/
def toric3Pair : CSS_pair 18 9 9 :=
  CSS_pair.of_matrices toric3Hz toric3Hx
    ((mutually_orth_rows_iff toric3Hz toric3Hx).mpr (by decide))

/-- **回灌（环面 $3\times3$）**：上游 `dX` 即本库 `toric3_dx`。 -/
theorem toric3Pair_dX : CSS_pair.dX toric3Pair = 3 := toric3_dx

/-- **回灌（环面 $3\times3$）**：上游 `dZ` 即本库 `toric3_dz`。 -/
theorem toric3Pair_dZ : CSS_pair.dZ toric3Pair = 3 := toric3_dz

end QECCertificates
