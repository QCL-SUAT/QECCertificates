/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix
import QECCertificates.GF2.RankEchelon
import QECCertificates.GF2.LiftedProduct

/-!
# Lifted-Product 锚点：$D_6$ 上的 2BGA 实例（Lifted-Product 族）

`GF2/LiftedProduct.lean` 给出了 lifted product 的通用定义与结构定理
（$H_XH_Z^{\top} = 0$、对 HGP 的退化）。本模块把构造**实例化**到文献表格上，
并按 `Codes/CaseMatrix.lean` 的三步模板给出**内核可检的全参数**。

## 复现的文献行

Lin–Pryadko, *Quantum two-block group algebra codes*, PRA **109**, 022407 (2024)，DOI `10.1103/PhysRevA.109.022407`；**出版版 Appendix C 的 Table III**（那两页种子与 $(k,d)$ 逐字对过出版版，与预印本 v1 的同表一致），$m = 6$ 那一行：
群 $D_6 = \langle r,s \mid r^6 = s^2 = (rs)^2 = 1\rangle$（12 元）、$n = 4m = 24$，
两个参数对 $(k, d) = (8, 3)$ 与 $(12, 2)$，种子

| 实例 | $k$ | $d$ | $a$ | $b$ |
|---|---|---|---|---|
| 实例 1 | 8 | 3 | $1 + r^4$ | $1 + sr^4 + r^3 + r^4 + sr^2 + r$ |
| 实例 2 | 12 | 2 | $1 + r^3$ | $1 + sr + r^3 + r^4 + sr^4 + r$ |

（该表的口径：$W_a = 2$、$W_b = 6$，表中每一行都满足 $kd = n$。）

## 落地的断言（全部内核 `by decide`）

* `lpAnchorHx` / `lpAnchorHz`：由 **LP 构造**（1 × 1 种子，即 2BGA）经元素编号重标得到
  （`d6Equiv` 把 12 个群元素编号为 `0..11`；列编号为"左块 0..11、右块 12..23"）；
* `lpAnchor_css`：$H_XH_Z^{\top} = 0$（通用定理 `lp2_orthogonal` 的实例）；
* `lpAnchor_k` / `lpAnchor2_k`：维数 $k$ 由行消元直算（走 `rankEchelon` 只追加梯队形后端）；
* `lpAnchor_dx` / `lpAnchor_dz`（及实例 2 的两条）：码距**恰为** $d$——
  下界由重量限定候选列表为空给出（`lpAnchor_lowerHyp`，镜像 `lowerHyp_of_lightCand_nil` 的编排，
  但走 `inSpanEch` 的梯队形后端），上界由一个**显式低重量逻辑算符**给出。

## 与数值侧的关系（第二路对账）

`tools/verify_codes.py` 的 `lp_anchor()` 用**独立的 Python 实现**（同一群、同一种子、
同一元素序与列序）重算同一条链：$H_XH_Z^{\top}=0$、`k = n - rank H_X - rank H_Z`、
重量限定枚举为空（下界）、显式见证 + 对偶见证配对 1（上界），得到同一组读数
（实例 1 $n=24,k=8,d_X=d_Z=3$、实例 2 $n=24,k=12,d_X=d_Z=2$，
见证列号分别是 `{0,2,4}` 与 `{0,3}`）。本模块把其中属于内核可判定的部分
升格为机器检验断言——两侧互证，但只有内核侧进可信基。
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、群 $D_6$ 的元素编号 -/

/-- $D_6$ 的元素按 `r^0..r^5, sr^0..sr^5` 编号为 `0..11`。 -/
def d6Code (x : DihedralGroup 6) : Fin 12 :=
  match x with
  | .r i => ⟨i.val, by have h := ZMod.val_lt i; omega⟩
  | .sr i => ⟨6 + i.val, by have h := ZMod.val_lt i; omega⟩

/-- `d6Code` 的逆（只用到 `ZMod` 的自然数转换，不构造 `Fin`）。 -/
def d6Index (k : Fin 12) : DihedralGroup 6 :=
  if (k : ℕ) < 6 then DihedralGroup.r (((k : ℕ) : ZMod 6))
  else DihedralGroup.sr ((((k : ℕ) - 6 : ℕ)) : ZMod 6)

theorem d6Index_code : Function.LeftInverse d6Index d6Code := by decide

theorem d6Code_index : Function.RightInverse d6Index d6Code := by decide

/-- 行指标的重标：$D_6 \simeq \{0,\dots,11\}$。 -/
def d6Equiv : DihedralGroup 6 ≃ Fin 12 where
  toFun := d6Code
  invFun := d6Index
  left_inv := d6Index_code
  right_inv := d6Code_index

/-- 列指标的重标：两个 $D_6$ 块 $\simeq \{0,\dots,23\}$（**左块 0..11、右块 12..23**）。 -/
def d6ColEquiv : (DihedralGroup 6 ⊕ DihedralGroup 6) ≃ Fin 24 :=
  (Equiv.sumCongr d6Equiv d6Equiv).trans finSumFinEquiv

/-- 群代数元 $\sum_{g \in s} g$（在 $s$ 上系数为 1）。 -/
def gsum (s : Finset (DihedralGroup 6)) : DihedralGroup 6 → ZMod 2 :=
  fun g => if g ∈ s then 1 else 0

/-! ## 二、实例 1：种子 $a = 1 + r^4$、$b = 1 + sr^4 + r^3 + r^4 + sr^2 + r$ -/

/-- 实例 1 的种子 $a = 1 + r^4$。 -/
def lpSeedA : DihedralGroup 6 → ZMod 2 := gsum {(1 : DihedralGroup 6), DihedralGroup.r 4}

/-- 实例 1 的种子 $b = 1 + sr^4 + r^3 + r^4 + sr^2 + r$。 -/
def lpSeedB : DihedralGroup 6 → ZMod 2 :=
  gsum {(1 : DihedralGroup 6), DihedralGroup.r 1, DihedralGroup.r 3, DihedralGroup.r 4,
    DihedralGroup.sr 2, DihedralGroup.sr 4}

/-- 实例 1 的 X 型校验：LP 构造（1 x 1 种子）经元素编号重标到 `Fin 12 x Fin 24`。 -/
def lpAnchorHx : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HX lpSeedA lpSeedB)

/-- 实例 1 的 Z 型校验。 -/
def lpAnchorHz : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HZ lpSeedA lpSeedB)

/-- **锚点等式（CSS 相容性）**：LP 构造的 $H_XH_Z^{\top} = 0$ 在实例上成立
（通用定理 `lp2_orthogonal` 的实例化）。 -/
theorem lpAnchor_css : lpAnchorHx * (lpAnchorHz).transpose = 0 := by decide

/-- 实例 1 的 X 型见证：重量 3 的逻辑算符（列 `0, 2, 4`，即左块的 $r^0, r^2, r^4$）。 -/
def lpXW : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-- 实例 1 的 X 型对偶见证（与 `lpXW` 配对为 1、落在 $H_Z$ 的核里）。 -/
def lpXWdual : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-- 实例 1 的 Z 型见证。 -/
def lpZW : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-- 实例 1 的 Z 型对偶见证。 -/
def lpZWdual : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-! ## 三、实例 2：种子 $a = 1 + r^3$、$b = 1 + sr + r^3 + r^4 + sr^4 + r$ -/

/-- 实例 2 的种子 $a = 1 + r^3$。 -/
def lpSeed2A : DihedralGroup 6 → ZMod 2 := gsum {(1 : DihedralGroup 6), DihedralGroup.r 3}

/-- 实例 2 的种子 $b = 1 + sr + r^3 + r^4 + sr^4 + r$。 -/
def lpSeed2B : DihedralGroup 6 → ZMod 2 :=
  gsum {(1 : DihedralGroup 6), DihedralGroup.r 1, DihedralGroup.r 3, DihedralGroup.r 4,
    DihedralGroup.sr 1, DihedralGroup.sr 4}

/-- 实例 2 的 X 型校验。 -/
def lpAnchor2Hx : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HX lpSeed2A lpSeed2B)

/-- 实例 2 的 Z 型校验。 -/
def lpAnchor2Hz : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HZ lpSeed2A lpSeed2B)

/-- **锚点等式（CSS 相容性）**，实例 2。 -/
theorem lpAnchor2_css : lpAnchor2Hx * (lpAnchor2Hz).transpose = 0 := by decide

/-- 实例 2 的 X 型见证：重量 2（列 `0, 3`）。 -/
def lp2XW : Vec 24 := (e 0 + e 3 : Vec 24)

def lp2XWdual : Vec 24 := (e 0 + e 2 + e 6 + e 7 : Vec 24)

def lp2ZW : Vec 24 := (e 0 + e 3 : Vec 24)

def lp2ZWdual : Vec 24 := (e 0 + e 1 + e 7 + e 12 : Vec 24)

/-! ## 四、维数：行消元直算（只追加梯队形后端） -/

/-- **实例 1 的维数**：$24 - 8 - 8 = 8$。

归约走 `GF2/RankEchelon.lean` 的只追加梯队形（宽 24 上 `rowReduce` 的回代消去代价逐轮相乘）；
桥定理 `rankEchelon_eq_length_rowReduce` 保证两者给出同一个秩，故陈述仍写成 `rowReduce` 形态。 -/
theorem lpAnchor_k : 24 - (rowReduce (List.ofFn fun i => lpAnchorHx i)).length
    - (rowReduce (List.ofFn fun i => lpAnchorHz i)).length = 8 := by
  simp only [← rankEchelon_eq_length_rowReduce]
  decide

/-- **实例 2 的维数**：$24 - 6 - 6 = 12$。 -/
theorem lpAnchor2_k : 24 - (rowReduce (List.ofFn fun i => lpAnchor2Hx i)).length
    - (rowReduce (List.ofFn fun i => lpAnchor2Hz i)).length = 12 := by
  simp only [← rankEchelon_eq_length_rowReduce]
  decide

/-! ## 五、距离：重量限定候选列表为空 ⟹ 下界（梯队形后端）

`GF2/LowerBound.lean` 的 `lightCand` 用 `inSpanB`（内部跑 `rowReduce`），宽 24 上太贵；
这里把**同一个候选集**搬到 `inSpanEch`（只追加梯队形后端）上，并在本文件内证
"候选为空 ⟹ 距离下界"（镜像 `lowerHyp_of_lightCand_nil` 的编排）。 -/

/-- 轻算符判定（梯队形后端）：重量非零、与 `M₁` 对易、且不在 `M₂` 的行空间里。 -/
abbrev lpLight {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (v : Vec 24) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧ inSpanEch (List.ofFn fun i => M₂ i) v = false

/-- 重量 $\le w$ 的候选集。 -/
def lpLightCand (w : ℕ) {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2)) :
    List (Vec 24) :=
  (lightVecs 24 w).filter (fun v => decide (lpLight M₁ M₂ v))

/-- **下界假设**（镜像 `lowerHyp_of_lightCand_nil`）：重量 $\le d-1$ 的候选为空 ⟹ 距离 $\ge d$。 -/
theorem lpAnchor_lowerHyp {m₁ m₂ d : ℕ} (hd : 1 ≤ d)
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (h : lpLightCand (d - 1) M₁ M₂ = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.rowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs 24 (d - 1) := by
    refine mem_lightVecs 24 (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lpLightCand (d - 1) M₁ M₂ := by
    unfold lpLightCand
    rw [List.mem_filter]
    refine ⟨hcov, ?_⟩
    rw [decide_eq_true_eq]
    exact ⟨hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanEch_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem

/-- **下界证书（实例 1，X 侧）**：重量 $\le 2$ 的候选列表为空。 -/
theorem lpAnchor_lightCand_x : lpLightCand 2 lpAnchorHx lpAnchorHz = [] := by decide

/-- **下界证书（实例 1，Z 侧）**。 -/
theorem lpAnchor_lightCand_z : lpLightCand 2 lpAnchorHz lpAnchorHx = [] := by decide

/-- **下界证书（实例 2，X 侧）**：重量 $\le 1$ 的候选列表为空。 -/
theorem lpAnchor2_lightCand_x : lpLightCand 1 lpAnchor2Hx lpAnchor2Hz = [] := by decide

/-- **下界证书（实例 2，Z 侧）**。 -/
theorem lpAnchor2_lightCand_z : lpLightCand 1 lpAnchor2Hz lpAnchor2Hx = [] := by decide

/-! ## 六、精确码距 -/

/-- **实例 1 的 X 侧码距 = 3**：下界候选列表为空，上界是显式重量-3 逻辑算符（配双对偶见证）。 -/
theorem lpAnchor_dx : min_weight_ker_not_mem_rowspace lpAnchorHx lpAnchorHz = 3 :=
  eq_minWeight_of_bounds lpAnchorHx lpAnchorHz (by decide) (E := lpXW)
    (mem_ker_of_inKerB lpAnchorHx (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchorHz (w := lpXWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 3) (by decide) lpAnchorHx lpAnchorHz lpAnchor_lightCand_x)

/-- **实例 1 的 Z 侧码距 = 3**。 -/
theorem lpAnchor_dz : min_weight_ker_not_mem_rowspace lpAnchorHz lpAnchorHx = 3 :=
  eq_minWeight_of_bounds lpAnchorHz lpAnchorHx (by decide) (E := lpZW)
    (mem_ker_of_inKerB lpAnchorHz (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchorHx (w := lpZWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 3) (by decide) lpAnchorHz lpAnchorHx lpAnchor_lightCand_z)

/-- **实例 2 的 X 侧码距 = 2**。 -/
theorem lpAnchor2_dx : min_weight_ker_not_mem_rowspace lpAnchor2Hx lpAnchor2Hz = 2 :=
  eq_minWeight_of_bounds lpAnchor2Hx lpAnchor2Hz (by decide) (E := lp2XW)
    (mem_ker_of_inKerB lpAnchor2Hx (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchor2Hz (w := lp2XWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 2) (by decide) lpAnchor2Hx lpAnchor2Hz lpAnchor2_lightCand_x)

/-- **实例 2 的 Z 侧码距 = 2**。 -/
theorem lpAnchor2_dz : min_weight_ker_not_mem_rowspace lpAnchor2Hz lpAnchor2Hx = 2 :=
  eq_minWeight_of_bounds lpAnchor2Hz lpAnchor2Hx (by decide) (E := lp2ZW)
    (mem_ker_of_inKerB lpAnchor2Hz (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchor2Hx (w := lp2ZWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 2) (by decide) lpAnchor2Hz lpAnchor2Hx lpAnchor2_lightCand_z)

end QECCertificates
