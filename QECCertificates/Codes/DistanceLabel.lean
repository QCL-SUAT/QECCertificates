/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix
import QECCertificates.Codes.BB18Anchor
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.CSSPair
import QECCertificates.Codes.LPAnchor

/-!
# X/Z 距离标签：把约定钉死，并把"两侧相等"做成机器核对的总账

`min_weight_ker_not_mem_rowspace M₁ M₂` 的第一个参数供**核**、第二个供**行空间**。
问题在于"哪个矩阵供核"这件事有两套读法，而**两套给出的数在两侧不相等时是不同的**：

* **本库与上游口径**（`libDX`）：`dX` 以 **X 型校验矩阵**作核，即
  $\min\{\mathrm{wt}(v) : v\in\ker H_X,\ v\notin\mathrm{row}\,H_Z\}$。
  上游 `CSS_pair.dX = min_weight_ker_not_mem_rowspace C.H₂ C.H₁`，而
  `CSS_BSM` 把 $H_1$ 放进 Z 槽、$H_2$ 放进 X 槽（`Z2Z2_Pauli_equiv (1,0) = X`），
  故 $H_1$ 是 Z 型校验、$H_2$ 是 X 型校验——**与本库同序**。
* **教科书口径**（`textbookDX`）：X 型逻辑算符须与 Z 型稳定子对易，故
  $d_X=\min\{\mathrm{wt}(v):v\in\ker H_Z,\ v\notin\mathrm{row}\,H_X\}$——
  **以 Z 型校验作核**，正好是上一条的换序。

两条 `rfl` 桥（`libDX_eq_textbookDZ`、`libDZ_eq_textbookDX`）把这件事记成定理而不是
散文：**本库的 `_dx` 定理数值上就是教科书的 $d_Z$，反之亦然。**

## 为什么这不成问题，以及什么时候会成问题

本库已实例化的 19 组码**两侧距离全相等**（下表逐条机器核对），故两套读法给出同一个
数字，任何已发布的数都不受影响。会出问题的是**两侧不等**的实例——而 gauging 正是
最可能打破对称的那类构造。故本模块同时是**新实例的前置**：写 gauging 实例时一律用
`libDX`/`textbookDX` 具名写出你要的是哪一个，不要靠"`_dx` 这个名字"。

## 两侧相等的总账

`_dx_eq_dz` 族把每个实例的两条既有定理拼成一条等式：左边是 `libDX`、右边是 `libDZ`，
两者都等于该实例的距离值。它是**机器核对**，不是声明——任一新实例两侧不等，
这条就证不出来。

* HGP 族的三个实例给的是**界**而不是 `min_weight` 等式（下界走清洗定理、
  上界走显式见证），故其两侧相等由 $d_X$ 与 $d_Z$ 的界合拢分别给出，
  见 `Codes/HGPToricFamily.lean` 的 `hgp_toric_family`（两分量在同一条合取里）。
-/

namespace QECCertificates

open _root_.Matrix

/-! ## 一、两套具名定义 -/

/-- **本库与上游口径的 X 距离**：以 X 型校验矩阵 `Hx` 作核。

即 $\min\{\mathrm{wt}(v) : H_X v = 0,\ v\notin\mathrm{row}\,H_Z\}$。
与上游 `CSS_pair.dX` 同序（见 `libDX_eq_CSSpair_dX`）。 -/
noncomputable def libDX {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hx Hz

/-- **本库与上游口径的 Z 距离**：以 Z 型校验矩阵 `Hz` 作核。 -/
noncomputable def libDZ {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hz Hx

/-- **教科书口径的 X 距离**：以 Z 型校验矩阵作核（X 型算符与 Z 型稳定子对易）。 -/
noncomputable def textbookDX {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hz Hx

/-- **教科书口径的 Z 距离**：以 X 型校验矩阵作核。 -/
noncomputable def textbookDZ {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hx Hz

/-- **换序桥（X 侧）**：本库口径的 `dX` 就是教科书口径的 `dZ`。 -/
theorem libDX_eq_textbookDZ {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) :
    libDX Hx Hz = textbookDZ Hx Hz := rfl

/-- **换序桥（Z 侧）**：本库口径的 `dZ` 就是教科书口径的 `dX`。 -/
theorem libDZ_eq_textbookDX {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) :
    libDZ Hx Hz = textbookDX Hx Hz := rfl

/-- **与上游字段的逐字对应**：把 `CSS_pair` 的两个矩阵按上游的角色代入
（`C.H₂` 是 X 型校验、`C.H₁` 是 Z 型校验），本库的 `libDX` 就是 `CSS_pair.dX`。

这条是定义级的，所以两个开发的距离字段**可直接互相代换**，
不需要任何换算系数——这正是 d"语义对齐"要的东西。 -/
theorem libDX_eq_CSSpair_dX {n k₁ k₂ : ℕ} (C : CSS_pair n k₁ k₂) :
    libDX C.H₂ C.H₁ = CSS_pair.dX C := rfl

/-- 上游 `CSS_pair.dZ` 与本库 `libDZ` 的对应。 -/
theorem libDZ_eq_CSSpair_dZ {n k₁ k₂ : ℕ} (C : CSS_pair n k₁ k₂) :
    libDZ C.H₂ C.H₁ = CSS_pair.dZ C := rfl

/-! ## 二、两侧相等的总账（已实例化的每一个 CSS 码） -/

/-- Steane 码：两侧距离相等。 -/
theorem steane_dx_eq_dz : libDX steaneHx steaneHz = libDZ steaneHx steaneHz := by
  rw [libDX, libDZ, steane_dx, steane_dz]

/-- Shor 码：两侧距离相等。 -/
theorem shor_dx_eq_dz : libDX shorHx shorHz = libDZ shorHx shorHz := by
  rw [libDX, libDZ, shor_dx, shor_dz]

/-- $[[4,2,2]]$：两侧距离相等。 -/
theorem four_dx_eq_dz : libDX fourHx fourHz = libDZ fourHx fourHz := by
  rw [libDX, libDZ, four_dx, four_dz]

/-- 环面码 $[[8,2,2]]$：两侧距离相等。 -/
theorem toric_dx_eq_dz : libDX toricHx toricHz = libDZ toricHx toricHz := by
  rw [libDX, libDZ, toric_dx, toric_dz]

/-- 环面码 $[[18,2,3]]$：两侧距离相等。 -/
theorem toric3_dx_eq_dz : libDX toric3Hx toric3Hz = libDZ toric3Hx toric3Hz := by
  rw [libDX, libDZ, toric3_dx, toric3_dz]

/-- BB $[[18,4,4]]$：两侧距离相等。 -/
theorem bb18_dx_eq_dz : libDX bb18Hx bb18Hz = libDZ bb18Hx bb18Hz := by
  rw [libDX, libDZ, bb18_dx, bb18_dz]

/-- gauging 后的 BB $[[24,3,4]]$：两侧距离相等。

这一条尤其要看：gauging 会打破 X/Z 的显式对称，故它两侧相等**不是显然的**，
而是机器核出来的。 -/
theorem bb24_dx_eq_dz : libDX bb24Hx bb24Hz = libDZ bb24Hx bb24Hz := by
  rw [libDX, libDZ, bb24_dx, bb24_dz]

/-- Lifted-Product $[[24,8,3]]$（$D_6$ 上的 2BGA）：两侧距离相等。 -/
theorem lpAnchor_dx_eq_dz : libDX lpAnchorHx lpAnchorHz = libDZ lpAnchorHx lpAnchorHz := by
  rw [libDX, libDZ, lpAnchor_dx, lpAnchor_dz]

/-- Lifted-Product $[[24,12,2]]$（$D_6$ 上的 2BGA）：两侧距离相等。 -/
theorem lpAnchor2_dx_eq_dz : libDX lpAnchor2Hx lpAnchor2Hz = libDZ lpAnchor2Hx lpAnchor2Hz := by
  rw [libDX, libDZ, lpAnchor2_dx, lpAnchor2_dz]

end QECCertificates
