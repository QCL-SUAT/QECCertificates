/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.Gauging

/-!
# C1–C4 分离条件的判定层（逻辑测量容错距离）

本模块的交付物是"两分量分离条件判定定理"：文献 [12] 的
时空故障距离定理以四条显式条件为主干（本包记作 C1–C4），本包**逐条钉到承重环节**、
给出**可计算的条件清单**与**判定定理**，并给出 C1 边界的**双侧反例**。

| 条件 | 内容 | 承重环节 | 本模块的处理 |
|---|---|---|---|
| **C1** | 辅助图膨胀 $h(G)\ge 1$ | 空间型引理的 $\min(h(G),1)\cdot d$ 因子 | **可计算谓词** `HasExpansionOne`（逐割判定）+ 判定定理里的数值形态 `1 ≤ η` |
| **C2** | 变形轮数 $t_o-t_i\ge d$ | 时间型引理（时间型分量恰为轮数 $t_o-t_i$） | **定理**（`exists_logicalFault_of_rounds_lt`，带读出泛函；不带读出的形态 `exists_undetectable_of_rounds_lt`）：轮数不足 ⟹ 存在更轻的**不可探测逻辑故障** ⟹ **C2 必要** |
| **C3** | 首末轮稳定子测量完美 | 出版版 SI Lemma 3 的边界约定（Remark 3） | 记为技术约定（`perfectEnds`），判定定理不承重 |
| **C4** | 单时间片内无空间型局部探测器 | 探测器生成引理的结构假设（出版版 SI Remark 2） | 同上（`noLocalDetector`） |

## 判定定理的作用

`separation_judgment` 把两条分量界合成时空故障距离下界：
空间型用论文 Lemma 2 的界 $\min(\eta,1)\cdot d$（$\eta\ge1$ 即 C1，作为具名假设——
本条属数学负责人主导的锐化对象，本侧不重证），**时间型用本库定理**
（`Codes/Gauging.lean` 的 `timeLike_weight_eq`：最小不可探测重量 = 轮数），
C2 把轮数与 $d$ 接起来。合起来

$$\min(\text{空间型},\ \text{时间型}) \;\ge\; d .$$

## C1 的双侧反例（可计算实例）

* `not_expansionOne_path` / `expansionOne_complete`：小图上 C1 的**可计算判定**
  （路径图 $P_4$：$h<1$；完全图 $K_4$：$h\ge1$）——C1 不是形式条件，而是逐割可核的谓词。
* 失效侧与保距侧的**码级实例**见 `Codes/SeparationInstances`（gauging 变形码的
  显式校验矩阵 + 内核枚举）。
-/

namespace QECCertificates

open scoped BigOperators

variable {k : ℕ}

/-! ## 一、辅助图与 C1（可计算谓词） -/

/-- 辅助图的**割大小**：恰有一个端点落在 `S` 中的边数。 -/
def cutSize (edges : List (Fin k × Fin k)) (S : Finset (Fin k)) : ℕ :=
  (edges.filter (fun e => decide (e.1 ∈ S) != decide (e.2 ∈ S))).length

/-- **C1：辅助图膨胀 $h(G)\ge1$**——每个割的割边数不小于两侧顶点数的较小者
（即 Cheeger 常数 $\ge1$；孤立点 ⟹ 取单点为割即违反）。

用 `abbrev` 以便 `decide` 在具体小图上直接判定（`def` 半可还原，实例搜索不展开）。 -/
abbrev HasExpansionOne (edges : List (Fin k × Fin k)) : Prop :=
  ∀ S : Finset (Fin k), min S.card (k - S.card) ≤ cutSize edges S

/-- **C1 判定（完全图）**：$K_4$ 的膨胀 $\ge1$。 -/
theorem expansionOne_complete :
    HasExpansionOne ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
      List (Fin 4 × Fin 4)) := by decide

/-- **C1 判定（路径图）**：$P_4$（3 条边的路径）的膨胀 $<1$——取中间两点为割
即违反（割边 1 < min(2,2) = 2）；这是 C1 的**失效侧图例**。 -/
theorem not_expansionOne_path :
    ¬ HasExpansionOne ([(0, 1), (1, 2), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-- **C1 判定（圈图）**：$C_4$ 的膨胀 $\ge1$。 -/
theorem expansionOne_cycle :
    HasExpansionOne ([(0, 1), (1, 2), (2, 3), (3, 0)] : List (Fin 4 × Fin 4)) := by decide

/-- **C1 判定（两条不相交的边）**：膨胀 $<1$（一条边自身即割、割边数为 0）。 -/
theorem not_expansionOne_two_edges :
    ¬ HasExpansionOne ([(0, 1), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-! ## 二、条件清单 C1–C4 -/

/-- **分离条件清单 C1–C4**（判定层的输入；`η` 是 C1 的数值形态：`1 ≤ η` ⟺ 膨胀 $\ge1$）。

`perfectEnds`/`noLocalDetector` 是 C3/C4 的布尔标记——原文自陈二者为可放宽的
技术约定（arXiv v2 的 Remark 5 / Remark 4，即出版版 SI 的 Remark 3 / Remark 2），
本模块把它们的**作用与可去性**写在文档里，判定定理只承重 C1 与 C2。 -/
abbrev Conditions (edges : List (Fin k × Fin k)) (η rounds d : ℕ)
    (perfectEnds noLocalDetector : Bool) : Prop :=
  HasExpansionOne edges ∧ 1 ≤ η ∧ d ≤ rounds ∧ perfectEnds = true ∧
    noLocalDetector = true

/-! ## 三、C2 的必要性（时间型分量恰为轮数） -/

/-- 时间型链上的**全一算符**（每轮取一个数据比特）。 -/
def timeLikeVec (S : ℕ) : Vec (S + 1) := fun _ => 1

/-- 全一算符与相邻对校验正交（校验的支撑是两点，模 2 权重为偶）。 -/
theorem timeLikeVec_repCheck (S : ℕ) (i : Fin S) :
    repCheck S i ⬝ᵥ timeLikeVec S = 0 := by
  have hone : ∀ a : Fin (S + 1), unitVec a ⬝ᵥ timeLikeVec S = 1 := by
    intro a
    rw [dotProduct, Finset.sum_eq_single a]
    · rw [unitVec, ite_eq_left rfl, one_mul]
      rfl
    · intro b _ hb
      rw [unitVec, ite_eq_right (fun h : b = a => hb h), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [repCheck, add_dotProduct, hone, hone]
  exact CharTwo.add_self_eq_zero 1

/-- 全一算符非零（它在第 $0$ 位取 $1$）。 -/
theorem timeLikeVec_ne_zero (S : ℕ) : timeLikeVec S ≠ 0 := by
  intro hzero
  have h0 := congrFun hzero 0
  simp [timeLikeVec] at h0

/-- 全一算符的重量 = 轮数。 -/
theorem hammingNorm_timeLikeVec (S : ℕ) : hammingNorm (timeLikeVec S) = S + 1 := by
  have hone : ∀ a : Fin (S + 1), timeLikeVec S a ≠ 0 := fun a => one_ne_zero
  have hfilter : (Finset.univ.filter (fun i : Fin (S + 1) => timeLikeVec S i ≠ 0))
      = Finset.univ := Finset.filter_true_of_mem fun i _ => hone i
  show (Finset.univ.filter (fun i : Fin (S + 1) => timeLikeVec S i ≠ 0)).card = S + 1
  rw [hfilter, Finset.card_univ, Fintype.card_fin]

/-- **C2 的必要性（不带读出的形态）**：轮数 $T = S+1$ 小于 $d$ 时，时间型链上存在
**重量 $= T < d$** 的非零、与所有时间校验正交的向量（全一算符）。

**口径**：这条给的是"不可探测"，**不是**"不可探测的**逻辑**故障"——后者还要翻转一个
读出泛函。带读出的完整形态见下面的 `exists_logicalFault_of_rounds_lt`；两者共用同一个
见证，差别只在多出来的那一条点积。 -/
theorem exists_undetectable_of_rounds_lt {S d : ℕ} (h : S + 1 < d) :
    ∃ x : Vec (S + 1), x ≠ 0 ∧ (∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) ∧
      hammingNorm x < d :=
  ⟨timeLikeVec S, timeLikeVec_ne_zero S, fun i => timeLikeVec_repCheck S i,
   by rw [hammingNorm_timeLikeVec]; exact h⟩

/-- **C2 的必要性（完整形态：带读出泛函）**：只要读出让全一算子取值 $1$，同一个见证
就同时是**不可探测的逻辑故障**——非零、与每条时间校验正交、翻转读出、且重量 $<d$。

`Codes/BaconShorMeasurement.lean` 的 `bsMeasure2_lt_d` 是这条在 Bacon--Shor 上的实例：
读出泛函取某一轮的支撑指示向量，它与全一算子的点积恰为 $1$。 -/
theorem exists_logicalFault_of_rounds_lt {S d : ℕ} (h : S + 1 < d)
    (w : Vec (S + 1)) (hw : w ⬝ᵥ timeLikeVec S = 1) :
    ∃ x : Vec (S + 1), x ≠ 0 ∧ (∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) ∧
      w ⬝ᵥ x = 1 ∧ hammingNorm x < d :=
  ⟨timeLikeVec S, timeLikeVec_ne_zero S, fun i => timeLikeVec_repCheck S i, hw,
   by rw [hammingNorm_timeLikeVec]; exact h⟩

/-- **C2 的判定形态**：轮数 $\ge d$ 时，时间型链上不存在重量 $< d$ 的不可探测非零算符
（即时间型分量 $\ge d$）——正是 `timeLike_weight_eq` 的直接翻译。 -/
theorem no_light_undetectable_of_rounds_ge {S d : ℕ} (h : d ≤ S + 1) :
    ¬ ∃ x : Vec (S + 1), x ≠ 0 ∧ (∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) ∧
      hammingNorm x < d := by
  rintro ⟨x, hx, horth, hw⟩
  rw [timeLike_weight_eq horth hx] at hw
  omega

/-! ## 四、判定定理（组装层） -/

/-- **两分量分离条件判定定理**：C1（膨胀 $\eta\ge1$）与 C2（轮数 $\ge d$）把
两条分量界合成时空故障距离下界 $d$：

* 空间型：论文 Lemma 2 的界 $\min(\eta,1)\cdot d \le \text{空间型分量}$
  （C1 的作用就是让 $\min(\eta,1)=1$，界退化为 $d$）；
* 时间型：本库定理（`timeLike_weight_eq`）给出"时间型分量 = 轮数"，
  再由 C2 得 $\ge d$。

C3/C4 是原文自陈可放宽的技术约定（Remark 5 / Remark 4），不进入这条组装。 -/
theorem separation_judgment {d η rounds spaceDist timeDist : ℕ}
    (hC1 : 1 ≤ η) (hC2 : d ≤ rounds)
    (hSpace : min η 1 * d ≤ spaceDist)
    (hTime : rounds ≤ timeDist) :
    d ≤ min spaceDist timeDist := by
  have hmin : min η 1 = 1 := min_eq_right hC1
  rw [hmin, one_mul] at hSpace
  exact le_min hSpace (le_trans hC2 hTime)

/-! ## 五、条件间的蕴含 / 独立结构（小实例，`decide`） -/

/-- **C2 不蕴含 C1**：轮数充足（C2 成立）但辅助图为路径（C1 不成立）。 -/
theorem C2_not_C1 :
    ¬ HasExpansionOne ([(0, 1), (1, 2), (2, 3)] : List (Fin 4 × Fin 4)) ∧
      (3 : ℕ) ≤ 3 := ⟨not_expansionOne_path, le_refl 3⟩

/-- **C1 不蕴含 C2**：完全图（C1 成立）但轮数不足（C2 不成立）。 -/
theorem C1_not_C2 :
    HasExpansionOne ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
      List (Fin 4 × Fin 4)) ∧ ¬ ((3 : ℕ) ≤ 2) :=
  ⟨expansionOne_complete, by decide⟩

/-- **C3/C4 与 C1/C2 独立**：四项条件在同一实例上可任意取值
（C3/C4 是布尔标记，取其否定即可）——故判定定理只让 C1、C2 承重。 -/
theorem C3_C4_independent :
    ¬ (Conditions ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
        List (Fin 4 × Fin 4)) 1 3 3 false true) ∧
      ¬ (Conditions ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] :
        List (Fin 4 × Fin 4)) 1 3 3 true false) := by
  constructor <;> intro h <;> simp [Conditions] at h

end QECCertificates
