/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.LRATDataCircuit
import QECCertificates.Codes.TimeLikeInstance
import QECCertificates.Codes.GaugeMeasurementInstance

/-!
# 线路侧的编码忠实性：内核回放的那份 CNF 就是编码器的输出

本模块是 `Reflect/Faithful.lean` 的**线路侧兄弟**。码侧那条链（`Reflect/Encode.lean`
的可靠性 + `Reflect/Faithful.lean` 的同一性 + `Reflect/LRATData.lean` 的回放）证明的是

    求解器的证据是真的 —— 它给出的赋值对应一个"带对偶见证的轻逻辑算符"。

本模块把同一套东西接到**时空故障**上：《申报指南》方向（八）原话要求
"将量子码**及量子线路**的距离判定归约为 SAT 问题"，码侧早已落地，线路侧的落点在这里。
被编码的对象是**两个**测量线路的时间型探测码，共用同一个探测器形状：$m$ 个校验重复
测量 $T$ 轮，一个比特 = 一次"校验 $a$ 在第 $t$ 轮的**报告结果**"（编号 `T*a + t`），
探测器取同一校验的相邻两轮（$H_{(a,t)} = e_{T a + t} + e_{T a + t + 1}$）；
"所有探测器静默"即 $Hf = 0$。核里的非零向量在每个校验的时间轴上取常值，故最小
不可探测重量恰为 $T$。

| 档 | 被重复测量的 $m$ 个校验 | $T$ |
|---|---|---|
| `timelike34` | `Codes/TimeLikeInstance.lean` 的 `timeLike34H` 的三条重复测量校验 | 4 |
| `bbgauge44` | BB gauging 测量线路的 $\lvert V \rvert = 4$ 条 Gauss 律（`Codes/GaugeMeasurementInstance.lean`） | $4 = d$ |

**与两个 Codes 模块的关系（口径必须说准）**：本模块回放的 CNF 断言的是
"不存在 $0 \ne f$、$\mathrm{wt}(f) \le 3$、$Hf = 0$"，与那里的 `<实例>_d`
（`min_weight_ker_not_mem_rowspace <实例>H (zeroRows N) = 4`）**是同一句命题**——
`timelike34Ker_rows` / `bbgauge44Ker_rows` 把行表逐字钉在两个实例矩阵上。
注意这两档问的是"探测器全静默且非零"（核的最小重量），**不是**
`Codes/MeasurementProtocol.lean` 里带逻辑泛函 $w\cdot f=1$ 的 `IsUndetectedFault`
那一支——这两个实例都没有 $w$，两者不同口径。

**方向说明**：与 `Reflect/Faithful.lean` 一样，本模块给出的是**可靠性方向**
（"求解器给出的证据是真的"）；反方向（"没有轻故障 ⟹ CNF 不可满足"）同样需要构造
辅助变量取值，尚未形式化。下界本身另有独立路线（`Codes/TimeLikeInstance.lean` 与
`Codes/GaugeMeasurementInstance.lean` 的重量限定枚举、以及后者更进一步的族级定理
`bbGauge44_le_weight_of_ker`），不依赖这一条。
-/

namespace QECCertificates.LRAT

set_option maxRecDepth 1000000

set_option maxHeartbeats 8000000

/-! ## 一、Bacon–Shor 探测码的行表

来源与 `tools/timelike_server/timelike_sat.py` 逐字一致：9 条探测器行，行是**列索引表**
（列 = 比特编号 $4a+t$）。配对侧为空列表——这一档只问"探测器全静默的非零故障"，
这正是 `Codes/TimeLikeInstance.lean` 里 `zeroRows 12` 所扮演的角色。 -/

/-- 时间型探测码（$m=3$、$T=4$）的 9 条探测器行。 -/
def timelike34Ker : List (List Nat) :=
  [[0, 1], [1, 2], [2, 3], [4, 5], [5, 6], [6, 7], [8, 9], [9, 10], [10, 11]]

/-- 配对侧为空（无逻辑泛函 $w$；见模块头的口径说明）。 -/
def timelike34Pair : List (List Nat) := []

/-- 回放用的 `timelike34CNF` 就是编码器作用在这批行表上的输出。 -/
theorem timelike34_eq : buildPair timelike34Ker timelike34Pair 12 3 = timelike34CNF := by decide

/-- **行表钉在协议矩阵上**：本档的 9 条探测器行逐字等于 `Codes/TimeLikeInstance.lean`
的 `timeLike34H`。有了它，"回放的这档 CNF"与"已机检的时间型实例"才真的是同一个对象。 -/
theorem timelike34Ker_rows :
    (timelike34Ker.map (fun r => fun j : Fin 12 => if j.val ∈ r then (1 : ZMod 2) else 0))
      = List.ofFn (fun i : Fin 9 => timeLike34H i) := by decide

/-- 时间型实例：满足 `timelike34CNF` 的赋值给出重量 ≤ 3、且每个探测器都静默的故障。 -/
theorem timelike34_certified {σ : Assign} (h : SatFormula σ timelike34CNF) :
    cntS σ (List.range 12) ≤ 3 ∧
    (∀ r ∈ timelike34Ker, dotS σ r = false) ∧
    (∀ r ∈ timelike34Pair, dotS (fun t => σ (12 + t)) r = false) ∧
    dotS (fun t => σ t && σ (12 + t)) (List.range 12) = true := by
  rw [← timelike34_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-! ## 二、BB gauging 测量线路的行表

同样与 `tools/timelike_server/timelike_sat.py` 逐字一致：$|V| = 4$ 条 Gauss 律、
$T = 4$ 轮，$12$ 条探测器行，行是**列索引表**（列 = 比特编号 $4v+t$）。
**规模取舍**（与 `Codes/GaugeMeasurementInstance.lean` 的模块头一致）：这一档只覆盖
gauging 测量那一步的 $|V|$ 条 Gauss 律，**不是**整个 gauged 码 $[[24,3,4]]$ 的
完整综合征提取循环。 -/

/-- BB gauging 测量线路（$|V|=4$ 条 Gauss 律、$T=4$ 轮）的 12 条探测器行。 -/
def bbgauge44Ker : List (List Nat) :=
  [[0, 1], [1, 2], [2, 3], [4, 5], [5, 6], [6, 7],
   [8, 9], [9, 10], [10, 11], [12, 13], [13, 14], [14, 15]]

/-- 配对侧为空（同 `timelike34Pair`：无逻辑泛函 $w$）。 -/
def bbgauge44Pair : List (List Nat) := []

/-- 回放用的 `bbgauge44CNF` 就是编码器作用在这批行表上的输出。 -/
theorem bbgauge44_eq : buildPair bbgauge44Ker bbgauge44Pair 16 3 = bbgauge44CNF := by decide

/-- **行表钉在协议矩阵上**：本档的 12 条探测器行逐字等于
`Codes/GaugeMeasurementInstance.lean` 的 `bbGauge44H`（$|V| = 4$ 条 Gauss 律的
相邻轮比较）。有了它，"回放的这档 CNF"与"已机检的 gauging 测量线路实例"才真的是
同一个对象。 -/
theorem bbgauge44Ker_rows :
    (bbgauge44Ker.map (fun r => fun j : Fin 16 => if j.val ∈ r then (1 : ZMod 2) else 0))
      = List.ofFn (fun i : Fin 12 => bbGauge44H i) := by decide

/-- BB gauging 测量线路实例：满足 `bbgauge44CNF` 的赋值给出重量 ≤ 3、
且每条 Gauss 律的每个探测器都静默的时空故障。 -/
theorem bbgauge44_certified {σ : Assign} (h : SatFormula σ bbgauge44CNF) :
    cntS σ (List.range 16) ≤ 3 ∧
    (∀ r ∈ bbgauge44Ker, dotS σ r = false) ∧
    (∀ r ∈ bbgauge44Pair, dotS (fun t => σ (16 + t)) r = false) ∧
    dotS (fun t => σ t && σ (16 + t)) (List.range 16) = true := by
  rw [← bbgauge44_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

end QECCertificates.LRAT
