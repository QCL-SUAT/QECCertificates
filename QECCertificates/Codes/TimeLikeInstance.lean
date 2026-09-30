/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix

/-!
# 时间型分量的具名实例：$m = 3$ 个校验、$T = 4$ 轮的重复测量探测码

`Codes/Gauging.lean` 把时间型分量证成了**族级**定理（`timeLike_eq_of_repCheck` +
`timeLike_weight_eq`：与全部时间校验正交的非零向量取值全一，重量恰为轮数）。族级定理
比任何实例都强，但它**不是**一个可指名的对象：论文里说"时间型分量有一个真实例"时，
要的是一张写出来的校验矩阵、一个写出来的见证、以及在内核内判出的距离值——与
`Codes/CaseMatrix.lean` 的码实例同形。本模块补的就是这一件。

## 探测码的形状

$m$ 个校验在 $T$ 轮上重复测量，比特按"校验 $a$、轮次 $t$"编号。时间校验取**相邻轮**：

$$H_{(a,t)} = e_{a,t} + e_{a,t+1},\qquad a < m,\ t < T-1 .$$

本模块取 $m = 3$、$T = 4$，于是 $N = mT = 12$ 个比特、$9$ 条校验。核里的非零向量在
每个校验的时间轴上取常值，故最小重量恰为 $T = 4$——**一个校验连续四轮出错**，
这正是时间型分量"不可探测时长"的物理内容。见证写成 `timeLike34W`。

## 这个实例证明什么

* `timeLike34_d`：$\min\{\mathrm{wt}(v) : Hv = 0,\ v \neq 0\} = 4$，
  下界由重量 $\le 3$ 的候选集为空（`by decide`）给出、上界由显式见证给出；
* `timeLike34_witness_*`：见证三事实（在核里、非零、重量 4）逐条可查；
* 与族级定理的关系：$m = 1$ 的一般轮数由 `timeLike_weight_eq` 覆盖，
  本实例是 $m = 3$ 的**具体**取值——族级定理给"任意 $S$"，实例给"论文可引用的对象"。

## 与空间型侧对等

空间型侧的内核内实例是 BB $[[24,3,4]]$（`Codes/BB24Gauged.lean`）。加上本模块，
两个分量各有一个具名、可复算、在内核内判出数值的实例——这是本包
"两分量各有实例"这句话的落点。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、校验矩阵与见证 -/

/-- $m = 3$、$T = 4$ 的重复测量探测码的时间校验矩阵：$9$ 行、$12$ 列。

比特编号 $4a + t$（校验 $a < 3$、轮次 $t < 4$）；第 $(a,t)$ 行是相邻轮
$t$ 与 $t+1$ 的一对。 -/
def timeLike34H : Matrix (Fin 9) (Fin 12) (ZMod 2) :=
  Matrix.of ![
    e 0 + e 1,   e 1 + e 2,   e 2 + e 3,
    e 4 + e 5,   e 5 + e 6,   e 6 + e 7,
    e 8 + e 9,   e 9 + e 10,  e 10 + e 11
  ]

/-- 见证：**第一个校验连续四轮出错**，重量 $4 = T$。

它是核里重量最小的非零向量——时间型分量"不可探测时长 = 轮数"的显式算符。 -/
def timeLike34W : Vec 12 := e 0 + e 1 + e 2 + e 3

/-! ## 二、见证三事实 -/

/-- 在核里：$H w = 0$。 -/
theorem timeLike34_witness_mem_ker : timeLike34H *ᵥ timeLike34W = 0 := by decide

/-- 非零。 -/
theorem timeLike34_witness_ne_zero : timeLike34W ≠ 0 := by decide

/-- 重量恰为轮数 $T = 4$。 -/
theorem timeLike34_witness_weight : hammingNorm timeLike34W = 4 := by decide

/-! ## 三、最小不可探测重量 = 轮数 -/

/-- **时间型分量的实例断言**：$m = 3$、$T = 4$ 的探测码，最小不可探测重量恰为 $4$。

下界走重量限定枚举（重量 $\le 3$ 的候选集为空，`by decide`——候选数
$\sum_{k\le3}\binom{12}{k} = 299$），上界走显式见证 `timeLike34W`。 -/
theorem timeLike34_d : min_weight_ker_not_mem_rowspace timeLike34H (zeroRows 12) = 4 :=
  eq_minWeight_of_decide (d := 4) timeLike34H (zeroRows 12) (by decide) (by decide)
    (E := timeLike34W)
    (mem_ker_of_inKerB timeLike34H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 12) (by decide))
    (by decide)

/-- **三个校验各有自己的最小不可探测方向**：每个校验块的四轮全错都是核向量，
故最小重量的实现有三个，分别对应 $a = 0, 1, 2$。

这条把"时间型分量对每个校验独立"这件事写成可查的合取，也说明
`timeLike34_d` 的下界不是靠某个偶然的向量撑起来的。 -/
theorem timeLike34_block_witnesses :
    (timeLike34H *ᵥ (e 0 + e 1 + e 2 + e 3 : Vec 12) = 0 ∧
     timeLike34H *ᵥ (e 4 + e 5 + e 6 + e 7 : Vec 12) = 0 ∧
     timeLike34H *ᵥ (e 8 + e 9 + e 10 + e 11 : Vec 12) = 0) := by decide

end QECCertificates
