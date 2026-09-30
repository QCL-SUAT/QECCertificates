/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.SeparationClosedForm

/-!
# BB $[[24,3,4]]$ 的两分量分离陈述（C1 由 $K_4$ 的膨胀免判定）

BB 分离有两个候选族，其中对 BB 族的那一条最直接：

> BB24 已经给了 $k$ 与 $d$ 的 kernel 断言，但"两分量分离"这件事在 BB24 上
> **没有被陈述过**（现有断言是与 $k$ 无关的距离）。

本模块补这一句。BB $[[18,4,4]]$ 经 $K_4$ 辅助图 gauging 得 $[[24,3,4]]$，
于是分离条件的三件事在这条实例上都**指得出来**：

* **空间轴**：$d_X=d_Z=4$——`Codes/BB24Gauged.lean` 的内核断言 `bb24_dx` / `bb24_dz`
  直接给出，故本模块的分离闭式把 $d$ 钉在**码距本身**而不是一个字面量 $4$；
* **C1**：辅助图是 $K_4$，膨胀 $\ge1$ 由 `expansionOne_complete` 与族形态
  `expansionOne_complete_gen 4` 两道给出；
* **C2**：轮数取 $T=d=4$，`le_refl` 即满足；
* **$k$**：$4\to3$（`bb24_k`）。

结论是两分量都 $\ge d$，且 C1 与 C2 都已是定理——本模块的假设清单里只剩空间界的
数值形态与时间分量的上界（W–Y Lemma 2 与本库的时间型定理，见 `Codes/Separation.lean` 的口径）。
-/

namespace QECCertificates

open scoped BigOperators

/-- **BB $[[24,3,4]]$ 的两分量分离（C1、C2 均已证）**。

$d$ 取成码距本身 `min_weight_ker_not_mem_rowspace bb24Hx bb24Hz`（由 `bb24_dx` 知它 $=4$），
辅助图 $K_4$、轮数 $T=d$——于是判定定理的 C1 与 C2 两条假设都被消掉，
两分量都 $\ge d$。 -/
theorem bb24_separation_closed {spaceDist timeDist : ℕ}
    (hSpace : min (c1Witness (completeEdges 4)) 1
        * min_weight_ker_not_mem_rowspace bb24Hx bb24Hz ≤ spaceDist)
    (hTime : min_weight_ker_not_mem_rowspace bb24Hx bb24Hz ≤ timeDist) :
    min_weight_ker_not_mem_rowspace bb24Hx bb24Hz ≤ min spaceDist timeDist := by
  rw [bb24_dx] at hSpace hTime ⊢
  exact separation_closed (expansionOne_complete_gen 4) (le_refl 4) hSpace hTime

/-- **同一条实例的双侧距离**：$d_X=d_Z=4$——两分量分离陈述里"$d$"这个名字的落点。 -/
theorem bb24_both_distances :
    min_weight_ker_not_mem_rowspace bb24Hx bb24Hz = 4
      ∧ min_weight_ker_not_mem_rowspace bb24Hz bb24Hx = 4 :=
  ⟨bb24_dx, bb24_dz⟩

/-! ## 空间界在本实例上是**定理**而不是假设

$\S$一 的 `bb24_separation_closed` 仍把空间界的数值形态
$\min(\eta,1)\cdot d\le\text{spaceDist}$（W–Y Lemma 2）当输入。在本实例上它**可以证**：
不等式两侧的量在本库里都已被内核算出——

* 左边的 $d$ 是**基码**（BB $[[18,4,4]]$）的码距：`bb18_dx` 给出 $=4$；
* 右边的 spaceDist 是**变形码**（BB $[[24,3,4]]$）的码距：`bb24_dx` 给出 $=4$；
* $\min(\eta,1)=1$ 由 $K_4$ 的膨胀给出。

于是 $\min(\eta,1)\cdot d=1\cdot4\le4=\text{spaceDist}$ 由**两条独立的内核距离断言**直接闭合。

**口径**：这不是把 W–Y 的一般引理机器检验了一遍——那是另一件事。这里做的是把该引理
在**这一条实例上**的结论用另一条路（两侧码距各自独立算出）验掉，于是判定定理在本实例上的
假设清单里不再有它。一般情形下的 W–Y 引理仍是外部的。 -/

/-- **空间界（本实例上是定理）**：$\min(\eta,1)\cdot d\le$ 变形码距离，
两侧分别由 `bb18_dx` 与 `bb24_dx` 两条内核断言给出。 -/
theorem bb24_space_bound :
    min (c1Witness (completeEdges 4)) 1
        * min_weight_ker_not_mem_rowspace bb18Hx bb18Hz
      ≤ min_weight_ker_not_mem_rowspace bb24Hx bb24Hz := by
  rw [c1Witness_completeEdges_four, bb18_dx, bb24_dx]
  norm_num

/-- **BB $[[24,3,4]]$ 的分离闭式（假设清单里只剩"时间分量"这个待定名）**：
四项条件各自落地——

* **C1**：`expansionOne_complete_gen 4`（$K_4$ 的膨胀，族形态）；
* **C2**：`bb18_dx` ⟹ $d=4$ 与轮数相等；
* **空间界**：`bb24_space_bound`——不再是假设；
* **时间分量**：$T=4$ 轮横向测量的时空故障重量，由
  `Codes/MeasurementProtocol.lean` 的时间轴律给出 $\ge T$。

于是两分量都 $\ge d$，而假设清单里只剩"时间分量"这个名字本身（它的值由测量协议层定义）。 -/
theorem bb24_separation_closed_noHyp {N : ℕ} {L : Vec N} {f : SpacetimeFault 4 N}
    (hker : ∀ t, inKerB (0 : Matrix (Fin 0) (Fin N) (ZMod 2)) (f t) = true)
    (hlog : ∀ t, L ⬝ᵥ f t = 1) :
    min_weight_ker_not_mem_rowspace bb18Hx bb18Hz
      ≤ min (min_weight_ker_not_mem_rowspace bb24Hx bb24Hz) (spacetimeWeight f) := by
  have hC2 : min_weight_ker_not_mem_rowspace bb18Hx bb18Hz ≤ 4 := by rw [bb18_dx]
  exact separation_closed (edges := completeEdges 4)
    (d := min_weight_ker_not_mem_rowspace bb18Hx bb18Hz) (T := 4)
    (spaceDist := min_weight_ker_not_mem_rowspace bb24Hx bb24Hz)
    (expansionOne_complete_gen 4) hC2 bb24_space_bound (family_time_component hker hlog)

end QECCertificates
