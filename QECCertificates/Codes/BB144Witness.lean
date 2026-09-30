/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix

/-!
# BB $[[144,12,12]]$：witness 上界的内核内断言（IBM 主推码）

校验矩阵由 IBM 参数（$l=12, m=6$，$A=x^3+y+y^2$，$B=y^3+x+x^2$）构造，
规模 $72\times144$、行重 6。本模块给出**两侧距离上界** $d_X\le12$、$d_Z\le12$：
显式重量-12 的 X/Z 逻辑算符，三件事——在核里、不在另一侧的行空间里、重量为 12——
全部由内核 `by decide` 逐项核出。非成员判定走**对偶见证**（与另一侧校验对易、
且与见证配对为 1 的向量），不用 `inSpanB`：宽矩阵上这是数量级的差别。

本模块**接入默认构建与公理审计区**（见 `lean/QECCertificates.lean`）。代价须知道：
字面 $72\times144$ 矩阵上的点积由内核直接归约，本模块实测约 5 分钟、峰值 RSS 数 GB，
比库内其他模块贵；这是一次性开销，olean 落盘后增量构建不再重算。把每个点积从
144 项降到 12 项（支撑分解：`dotProduct` 对 $\sum_{i\in s} e_i$ 展开成
$\sum_{i\in s} v_i$）可以再降一个量级，留作后续优化。

**证据形态对照**：QECLean 以逐码解析证明在内核内闭合了该码的精确距离 $d=12$，
Lean-QEC 的 BB144 走 SAT/位爆破（`bv_decide`，未关内核检查）。本模块只给**上界**
$d_X,d_Z\le12$；下界 $\ge12$ 由 `cadical` 给出，证明经自写的 RUP 检查器与第三方
`drat-trim` 逐条复算（`tools/bb144_server/`），两侧合拢得
$d_X=d_Z=12$。把该证书搬进 Lean 内核回放是下一步。
-/

namespace QECCertificates

open _root_.Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- BB144 的 X 型校验 $H_X=[A\mid B]$（72 行 × 144 列，行重 6）。 -/
def bb144Hx : Matrix (Fin 72) (Fin 144) (ZMod 2) :=
  Matrix.of ![
    (e 1 + e 2 + e 18 + e 75 + e 78 + e 84 : Vec 144),
    (e 2 + e 3 + e 19 + e 76 + e 79 + e 85 : Vec 144),
    (e 3 + e 4 + e 20 + e 77 + e 80 + e 86 : Vec 144),
    (e 4 + e 5 + e 21 + e 72 + e 81 + e 87 : Vec 144),
    (e 0 + e 5 + e 22 + e 73 + e 82 + e 88 : Vec 144),
    (e 0 + e 1 + e 23 + e 74 + e 83 + e 89 : Vec 144),
    (e 7 + e 8 + e 24 + e 81 + e 84 + e 90 : Vec 144),
    (e 8 + e 9 + e 25 + e 82 + e 85 + e 91 : Vec 144),
    (e 9 + e 10 + e 26 + e 83 + e 86 + e 92 : Vec 144),
    (e 10 + e 11 + e 27 + e 78 + e 87 + e 93 : Vec 144),
    (e 6 + e 11 + e 28 + e 79 + e 88 + e 94 : Vec 144),
    (e 6 + e 7 + e 29 + e 80 + e 89 + e 95 : Vec 144),
    (e 13 + e 14 + e 30 + e 87 + e 90 + e 96 : Vec 144),
    (e 14 + e 15 + e 31 + e 88 + e 91 + e 97 : Vec 144),
    (e 15 + e 16 + e 32 + e 89 + e 92 + e 98 : Vec 144),
    (e 16 + e 17 + e 33 + e 84 + e 93 + e 99 : Vec 144),
    (e 12 + e 17 + e 34 + e 85 + e 94 + e 100 : Vec 144),
    (e 12 + e 13 + e 35 + e 86 + e 95 + e 101 : Vec 144),
    (e 19 + e 20 + e 36 + e 93 + e 96 + e 102 : Vec 144),
    (e 20 + e 21 + e 37 + e 94 + e 97 + e 103 : Vec 144),
    (e 21 + e 22 + e 38 + e 95 + e 98 + e 104 : Vec 144),
    (e 22 + e 23 + e 39 + e 90 + e 99 + e 105 : Vec 144),
    (e 18 + e 23 + e 40 + e 91 + e 100 + e 106 : Vec 144),
    (e 18 + e 19 + e 41 + e 92 + e 101 + e 107 : Vec 144),
    (e 25 + e 26 + e 42 + e 99 + e 102 + e 108 : Vec 144),
    (e 26 + e 27 + e 43 + e 100 + e 103 + e 109 : Vec 144),
    (e 27 + e 28 + e 44 + e 101 + e 104 + e 110 : Vec 144),
    (e 28 + e 29 + e 45 + e 96 + e 105 + e 111 : Vec 144),
    (e 24 + e 29 + e 46 + e 97 + e 106 + e 112 : Vec 144),
    (e 24 + e 25 + e 47 + e 98 + e 107 + e 113 : Vec 144),
    (e 31 + e 32 + e 48 + e 105 + e 108 + e 114 : Vec 144),
    (e 32 + e 33 + e 49 + e 106 + e 109 + e 115 : Vec 144),
    (e 33 + e 34 + e 50 + e 107 + e 110 + e 116 : Vec 144),
    (e 34 + e 35 + e 51 + e 102 + e 111 + e 117 : Vec 144),
    (e 30 + e 35 + e 52 + e 103 + e 112 + e 118 : Vec 144),
    (e 30 + e 31 + e 53 + e 104 + e 113 + e 119 : Vec 144),
    (e 37 + e 38 + e 54 + e 111 + e 114 + e 120 : Vec 144),
    (e 38 + e 39 + e 55 + e 112 + e 115 + e 121 : Vec 144),
    (e 39 + e 40 + e 56 + e 113 + e 116 + e 122 : Vec 144),
    (e 40 + e 41 + e 57 + e 108 + e 117 + e 123 : Vec 144),
    (e 36 + e 41 + e 58 + e 109 + e 118 + e 124 : Vec 144),
    (e 36 + e 37 + e 59 + e 110 + e 119 + e 125 : Vec 144),
    (e 43 + e 44 + e 60 + e 117 + e 120 + e 126 : Vec 144),
    (e 44 + e 45 + e 61 + e 118 + e 121 + e 127 : Vec 144),
    (e 45 + e 46 + e 62 + e 119 + e 122 + e 128 : Vec 144),
    (e 46 + e 47 + e 63 + e 114 + e 123 + e 129 : Vec 144),
    (e 42 + e 47 + e 64 + e 115 + e 124 + e 130 : Vec 144),
    (e 42 + e 43 + e 65 + e 116 + e 125 + e 131 : Vec 144),
    (e 49 + e 50 + e 66 + e 123 + e 126 + e 132 : Vec 144),
    (e 50 + e 51 + e 67 + e 124 + e 127 + e 133 : Vec 144),
    (e 51 + e 52 + e 68 + e 125 + e 128 + e 134 : Vec 144),
    (e 52 + e 53 + e 69 + e 120 + e 129 + e 135 : Vec 144),
    (e 48 + e 53 + e 70 + e 121 + e 130 + e 136 : Vec 144),
    (e 48 + e 49 + e 71 + e 122 + e 131 + e 137 : Vec 144),
    (e 0 + e 55 + e 56 + e 129 + e 132 + e 138 : Vec 144),
    (e 1 + e 56 + e 57 + e 130 + e 133 + e 139 : Vec 144),
    (e 2 + e 57 + e 58 + e 131 + e 134 + e 140 : Vec 144),
    (e 3 + e 58 + e 59 + e 126 + e 135 + e 141 : Vec 144),
    (e 4 + e 54 + e 59 + e 127 + e 136 + e 142 : Vec 144),
    (e 5 + e 54 + e 55 + e 128 + e 137 + e 143 : Vec 144),
    (e 6 + e 61 + e 62 + e 72 + e 135 + e 138 : Vec 144),
    (e 7 + e 62 + e 63 + e 73 + e 136 + e 139 : Vec 144),
    (e 8 + e 63 + e 64 + e 74 + e 137 + e 140 : Vec 144),
    (e 9 + e 64 + e 65 + e 75 + e 132 + e 141 : Vec 144),
    (e 10 + e 60 + e 65 + e 76 + e 133 + e 142 : Vec 144),
    (e 11 + e 60 + e 61 + e 77 + e 134 + e 143 : Vec 144),
    (e 12 + e 67 + e 68 + e 72 + e 78 + e 141 : Vec 144),
    (e 13 + e 68 + e 69 + e 73 + e 79 + e 142 : Vec 144),
    (e 14 + e 69 + e 70 + e 74 + e 80 + e 143 : Vec 144),
    (e 15 + e 70 + e 71 + e 75 + e 81 + e 138 : Vec 144),
    (e 16 + e 66 + e 71 + e 76 + e 82 + e 139 : Vec 144),
    (e 17 + e 66 + e 67 + e 77 + e 83 + e 140 : Vec 144)
  ]

/-- BB144 的 Z 型校验 $H_Z=[B^\top\mid A^\top]$。 -/
def bb144Hz : Matrix (Fin 72) (Fin 144) (ZMod 2) :=
  Matrix.of ![
    (e 3 + e 60 + e 66 + e 76 + e 77 + e 126 : Vec 144),
    (e 4 + e 61 + e 67 + e 72 + e 77 + e 127 : Vec 144),
    (e 5 + e 62 + e 68 + e 72 + e 73 + e 128 : Vec 144),
    (e 0 + e 63 + e 69 + e 73 + e 74 + e 129 : Vec 144),
    (e 1 + e 64 + e 70 + e 74 + e 75 + e 130 : Vec 144),
    (e 2 + e 65 + e 71 + e 75 + e 76 + e 131 : Vec 144),
    (e 0 + e 9 + e 66 + e 82 + e 83 + e 132 : Vec 144),
    (e 1 + e 10 + e 67 + e 78 + e 83 + e 133 : Vec 144),
    (e 2 + e 11 + e 68 + e 78 + e 79 + e 134 : Vec 144),
    (e 3 + e 6 + e 69 + e 79 + e 80 + e 135 : Vec 144),
    (e 4 + e 7 + e 70 + e 80 + e 81 + e 136 : Vec 144),
    (e 5 + e 8 + e 71 + e 81 + e 82 + e 137 : Vec 144),
    (e 0 + e 6 + e 15 + e 88 + e 89 + e 138 : Vec 144),
    (e 1 + e 7 + e 16 + e 84 + e 89 + e 139 : Vec 144),
    (e 2 + e 8 + e 17 + e 84 + e 85 + e 140 : Vec 144),
    (e 3 + e 9 + e 12 + e 85 + e 86 + e 141 : Vec 144),
    (e 4 + e 10 + e 13 + e 86 + e 87 + e 142 : Vec 144),
    (e 5 + e 11 + e 14 + e 87 + e 88 + e 143 : Vec 144),
    (e 6 + e 12 + e 21 + e 72 + e 94 + e 95 : Vec 144),
    (e 7 + e 13 + e 22 + e 73 + e 90 + e 95 : Vec 144),
    (e 8 + e 14 + e 23 + e 74 + e 90 + e 91 : Vec 144),
    (e 9 + e 15 + e 18 + e 75 + e 91 + e 92 : Vec 144),
    (e 10 + e 16 + e 19 + e 76 + e 92 + e 93 : Vec 144),
    (e 11 + e 17 + e 20 + e 77 + e 93 + e 94 : Vec 144),
    (e 12 + e 18 + e 27 + e 78 + e 100 + e 101 : Vec 144),
    (e 13 + e 19 + e 28 + e 79 + e 96 + e 101 : Vec 144),
    (e 14 + e 20 + e 29 + e 80 + e 96 + e 97 : Vec 144),
    (e 15 + e 21 + e 24 + e 81 + e 97 + e 98 : Vec 144),
    (e 16 + e 22 + e 25 + e 82 + e 98 + e 99 : Vec 144),
    (e 17 + e 23 + e 26 + e 83 + e 99 + e 100 : Vec 144),
    (e 18 + e 24 + e 33 + e 84 + e 106 + e 107 : Vec 144),
    (e 19 + e 25 + e 34 + e 85 + e 102 + e 107 : Vec 144),
    (e 20 + e 26 + e 35 + e 86 + e 102 + e 103 : Vec 144),
    (e 21 + e 27 + e 30 + e 87 + e 103 + e 104 : Vec 144),
    (e 22 + e 28 + e 31 + e 88 + e 104 + e 105 : Vec 144),
    (e 23 + e 29 + e 32 + e 89 + e 105 + e 106 : Vec 144),
    (e 24 + e 30 + e 39 + e 90 + e 112 + e 113 : Vec 144),
    (e 25 + e 31 + e 40 + e 91 + e 108 + e 113 : Vec 144),
    (e 26 + e 32 + e 41 + e 92 + e 108 + e 109 : Vec 144),
    (e 27 + e 33 + e 36 + e 93 + e 109 + e 110 : Vec 144),
    (e 28 + e 34 + e 37 + e 94 + e 110 + e 111 : Vec 144),
    (e 29 + e 35 + e 38 + e 95 + e 111 + e 112 : Vec 144),
    (e 30 + e 36 + e 45 + e 96 + e 118 + e 119 : Vec 144),
    (e 31 + e 37 + e 46 + e 97 + e 114 + e 119 : Vec 144),
    (e 32 + e 38 + e 47 + e 98 + e 114 + e 115 : Vec 144),
    (e 33 + e 39 + e 42 + e 99 + e 115 + e 116 : Vec 144),
    (e 34 + e 40 + e 43 + e 100 + e 116 + e 117 : Vec 144),
    (e 35 + e 41 + e 44 + e 101 + e 117 + e 118 : Vec 144),
    (e 36 + e 42 + e 51 + e 102 + e 124 + e 125 : Vec 144),
    (e 37 + e 43 + e 52 + e 103 + e 120 + e 125 : Vec 144),
    (e 38 + e 44 + e 53 + e 104 + e 120 + e 121 : Vec 144),
    (e 39 + e 45 + e 48 + e 105 + e 121 + e 122 : Vec 144),
    (e 40 + e 46 + e 49 + e 106 + e 122 + e 123 : Vec 144),
    (e 41 + e 47 + e 50 + e 107 + e 123 + e 124 : Vec 144),
    (e 42 + e 48 + e 57 + e 108 + e 130 + e 131 : Vec 144),
    (e 43 + e 49 + e 58 + e 109 + e 126 + e 131 : Vec 144),
    (e 44 + e 50 + e 59 + e 110 + e 126 + e 127 : Vec 144),
    (e 45 + e 51 + e 54 + e 111 + e 127 + e 128 : Vec 144),
    (e 46 + e 52 + e 55 + e 112 + e 128 + e 129 : Vec 144),
    (e 47 + e 53 + e 56 + e 113 + e 129 + e 130 : Vec 144),
    (e 48 + e 54 + e 63 + e 114 + e 136 + e 137 : Vec 144),
    (e 49 + e 55 + e 64 + e 115 + e 132 + e 137 : Vec 144),
    (e 50 + e 56 + e 65 + e 116 + e 132 + e 133 : Vec 144),
    (e 51 + e 57 + e 60 + e 117 + e 133 + e 134 : Vec 144),
    (e 52 + e 58 + e 61 + e 118 + e 134 + e 135 : Vec 144),
    (e 53 + e 59 + e 62 + e 119 + e 135 + e 136 : Vec 144),
    (e 54 + e 60 + e 69 + e 120 + e 142 + e 143 : Vec 144),
    (e 55 + e 61 + e 70 + e 121 + e 138 + e 143 : Vec 144),
    (e 56 + e 62 + e 71 + e 122 + e 138 + e 139 : Vec 144),
    (e 57 + e 63 + e 66 + e 123 + e 139 + e 140 : Vec 144),
    (e 58 + e 64 + e 67 + e 124 + e 140 + e 141 : Vec 144),
    (e 59 + e 65 + e 68 + e 125 + e 141 + e 142 : Vec 144)
  ]

/-- X 型见证：重量 12 的 X 逻辑算符。 -/
def bb144XW : Vec 144 := (e 0 + e 1 + e 4 + e 5 + e 18 + e 20 + e 36 + e 37 + e 40 + e 41 + e 54 + e 56 : Vec 144)

/-- Z 型见证：与 X 见证配对为 1。 -/
def bb144ZW : Vec 144 := (e 0 + e 1 + e 3 + e 4 + e 6 + e 7 + e 9 + e 10 + e 72 + e 73 + e 75 + e 76 : Vec 144)

/-- **$dX \le 12$**：X 见证在 $\ker H_X$ 中、不在 $H_Z$ 行空间中、重量 12。 -/
theorem bb144_X_logical :
    bb144Hx *ᵥ bb144XW = 0 ∧ bb144XW ∉ bb144Hz.rowSpace ∧ hammingNorm bb144XW = 12 :=
  ⟨by decide,
    not_mem_rowSpace_of_dualCheck bb144Hz (w := bb144ZW) (by decide) (by decide),
    by decide⟩

/-- **$dZ \le 12$**：Z 侧对称。 -/
theorem bb144_Z_logical :
    bb144Hz *ᵥ bb144ZW = 0 ∧ bb144ZW ∉ bb144Hx.rowSpace ∧ hammingNorm bb144ZW = 12 :=
  ⟨by decide,
    not_mem_rowSpace_of_dualCheck bb144Hx (w := bb144XW) (by decide) (by decide),
    by decide⟩

end QECCertificates
