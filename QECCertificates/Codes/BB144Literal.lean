/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB144Distance
import QECCertificates.Codes.BB144Witness

/-!
# BB $[[144,12,12]]$：字面矩阵与 QECLean 拼写的**同一性**（$d=12$ 的最后一步）

`Codes/BB144Witness.lean` 给的是**本库字面** $72\times144$ 校验矩阵
`bb144Hx`/`bb144Hz` 上的重量-12 见证（上界 $d\le12$）；
`Codes/BB144Distance.lean` 搬运的 QECLean Gross 定理给的是**群环拼写**
`LE_X`/`LE_Z` 上的下界 $12\le d$。两者各自独立成立，**中间的这一步正是这条矩阵同一性**：
本模块给出它，于是本库自己的矩阵上 $d=12$ 的两端落在同一个对象上。

## 证明路线

整矩阵 `by decide` 会在 8000000 心跳下超时（`LE_X` 的条目要展开
`Matrix.kronecker_fin`/`reindex`/`cyclic_shift` 那一串）。改走**逐条目**：

* 外层 `funext g` + `fin_cases g` 拆到**每一行**（$144$ 个条目一个目标），
  内层 `funext c` + `fin_cases c` 拆到**每一条目**再 `decide`。

实测：整行一次性 `decide` 约 $28$ 秒（一个巨大的 `Decidable` 项），
而逐条目平均每行约 $3$ 秒——**同一个数学内容，一个数量级的差别**。
整模块（两侧矩阵）约 $5$ 分钟，与 `BB144Witness` 同量级，是一次性开销。

## 结论

同一性一落，两侧合拢即得**本库矩阵上**的精确距离：

* `bb144_dX_eq_12` / `bb144_dZ_eq_12`：$\min\{\mathrm{wt}(v): v\in\ker H_X,\
  v\notin\mathrm{row}\,H_Z\}=12$ 及其对偶，上界走本库的重量-12 见证、
  下界走搬运来的 Gross 定理。

**口径**：下界仍是 QECLean 逐码解析证明的搬运（不是本库重证，也不是 LRAT 回放，
后者见任务 #20）；本模块补的是**它们的矩阵与我们的矩阵是同一个**这一步。
-/

namespace QECCertificates

open _root_.Matrix

open QECCertificates.BB144Distance

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、字面矩阵 = 群环拼写（逐条目） -/

/-- **X 侧同一性**：本库字面 `bb144Hx` 就是 QECLean 的 `BB144_X_mat` 拼写 `LE_X`。 -/
theorem bb144Hx_eq_LE_X : bb144Hx = LE_X := by
  funext g
  fin_cases g <;> (funext c; fin_cases c <;> decide)

/-- **Z 侧同一性**：本库字面 `bb144Hz` 就是 `LE_Z`。 -/
theorem bb144Hz_eq_LE_Z : bb144Hz = LE_Z := by
  funext g
  fin_cases g <;> (funext c; fin_cases c <;> decide)

/-! ## 二、本库矩阵上的精确距离 $d_X=d_Z=12$ -/

/-- **$d_X=12$（本库字面矩阵上）**：上界是本库的重量-12 见证
（`bb144_libDX_le_12`），下界是搬运来的 Gross 定理
（`BB144_dZ_ge_12`——注意本库 `libDX` 以 X 型校验作核，与教科书的 $d_X$ 互为换序，
见 `Codes/DistanceLabel.lean`）。 -/
theorem bb144_dX_eq_12 : min_weight_ker_not_mem_rowspace bb144Hx bb144Hz = 12 := by
  refine le_antisymm bb144_libDX_le_12 ?_
  have h := BB144_dZ_ge_12
  rwa [← bb144Hx_eq_LE_X, ← bb144Hz_eq_LE_Z] at h

/-- **$d_Z=12$（本库字面矩阵上）**：对称的一侧。 -/
theorem bb144_dZ_eq_12 : min_weight_ker_not_mem_rowspace bb144Hz bb144Hx = 12 := by
  refine le_antisymm bb144_libDZ_le_12 ?_
  have h := BB144_dX_ge_12
  rwa [← bb144Hz_eq_LE_Z, ← bb144Hx_eq_LE_X] at h

/-- **两侧相等**：本库矩阵上 $d_X=d_Z$，于是 X/Z 标签读法在此实例上无分歧。 -/
theorem bb144_dx_eq_dz :
    min_weight_ker_not_mem_rowspace bb144Hx bb144Hz
      = min_weight_ker_not_mem_rowspace bb144Hz bb144Hx := by
  rw [bb144_dX_eq_12, bb144_dZ_eq_12]

end QECCertificates
