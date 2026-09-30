/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.MeasurementProtocol
import QECCertificates.Codes.BaconShor

/-!
# Bacon–Shor $[[9,1,3]]$ 横向测量的两分量（内核内实例）

`Codes/BaconShor.lean` 给了这个码的**静态**结构（$k=1$、$d_X=d_Z=3$），
`Codes/MeasurementProtocol.lean` 给了**测量协议**的表示层（单轮故障模式、
跨轮拼接、时间轴律 $T\cdot s$）。本模块把两者接起来，在两个坐标系统里各给一个
内核内实例。

## 协议

X 型裸逻辑是 $\bar X = $ 单列的全 $X$（重量 $3$，`bstXW`）。它是**逐比特算符之积**，
故可以被**横向测量**：对支撑上的每个比特各测一次 $X$，逻辑读出值就是三个结果的乘积。
两个问题各对应一个分量：

* **空间轴**——一轮之内，逻辑读出只是**一个经典比特**。若只测这三个比特，没有任何
  校验能发现其中一个结果报错（`bare_noLightFault`：单轮故障距离 $=1$）。
  若把**整个 $3\times3$ 阵列**都测 $X$，则码的两条 X 型稳定子（相邻两列之积，重量 $6$）
  成了轮内校验——此时单轮故障距离跳到 $3=d$（§一）。
* **时间轴**——只测支撑时唯一的保护是**重复并比较各轮读出**。$\S$二 把这一条
  算成精确值：$T$ 轮的时空故障距离恰为 $T$（§三）。取 $T=d=3$ 即得两分量都 $\ge d$。

## 两个坐标系统，同一个协议

$\S$二 用**扁平坐标**：$9$ 个比特编号 $3t+i$（第 $t$ 轮、支撑比特 $i$），跨轮校验写成
一条显式的 $2\times9$ 校验矩阵 `bsCrossChecks`——与 `Codes/CaseMatrix.lean` 的码实例同形，
可直接 `by decide`。$\S$四 用**分层坐标** `Fin 3 → Vec 3`，把 `MeasurementProtocol` 的
时间轴律实例化。两者给出同一个数 $3$，互为对账。

## 逃逸模式的几何

$\S$一 的核刻画值得单独说：躲过两条 X 型稳定子的故障模式，恰好是"三列奇偶性相同"的
那些（`bsCrossChecks_ker_iff` 的空间轴版本）——而"三列全奇"的那一半正是
$\text{Z 型裸逻辑} + \text{Z 型规范群}$（见 `tools/probeA/bs_measure_probe.py` 的逐条核对）。
最小实现是**单行全 X**（$=$ 码的 Z 型裸逻辑 `bstZW`）：横向测量的逻辑翻转故障，
在空间轴上就是码的一个逻辑算符。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、空间轴：单轮，整个阵列测 X（轮内校验 = 码的 X 型稳定子） -/

/-- **横向测量的单轮读出泛函**（逻辑支撑上三个比特的奇偶性）。

$3$ 个比特、每个各测一次 $X$、逻辑读出 $=$ 三个结果的乘积——这就是横向测量的全部内容。 -/
def bsColumnReadout : Vec 3 := fun _ => 1

/-- 第二条 X 型稳定子：相邻两列 $\{1,2\}$ 的全 $X$（重量 $6$）。
第一条就是 `Codes/BaconShor.lean` 里的 `bstSX`（列 $\{0,1\}$）。 -/
def bsCol12 : Vec 9 := e 1 + e 2 + e 4 + e 5 + e 7 + e 8

/-- **单轮的轮内校验**：把整个阵列都测 $X$ 才能抽出的两条 X 型稳定子。 -/
def bsStabChecks : Matrix (Fin 2) (Fin 9) (ZMod 2) := Matrix.of ![bstSX, bsCol12]

/-- **单轮故障距离 $=3=d$**：躲过两条 X 型稳定子又翻转逻辑读出的故障模式，重量至少 $3$。

证书是重量限定枚举（`faultCand`，候选 $46$ 个）为空——故"三个结果里任一个错都会被
发现"，要翻转逻辑得在**每一列**各放奇数个错。 -/
theorem bsSingleRound_noLightFault : NoLightFault bsStabChecks bstXW 3 :=
  noLightFault_of_faultCand_nil bsStabChecks bstXW (by decide)

/-- **见证**：单行的全 $X$（$=$ 码的 Z 型裸逻辑 `bstZW`）躲过两条 X 型稳定子、
却翻转逻辑读出，重量恰为 $3$。

故"逃逸模式"不是抽象的：它就是码自己的一个逻辑算符，横向搬到测量结果上。 -/
theorem bsSingleRound_witness :
    inKerB bsStabChecks bstZW = true ∧ bstXW ⬝ᵥ bstZW = 1 ∧ hammingNorm bstZW = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- **空间轴的两向夹逼**：单轮故障距离恰为 $3$——下界是上面那条，上界是 `bstZW` 的见证。 -/
theorem bsSingleRound_eq_d :
    (NoLightFault bsStabChecks bstXW 3) ∧
      (∃ f : Vec 9, inKerB bsStabChecks f = true ∧ bstXW ⬝ᵥ f = 1 ∧ hammingNorm f = 3) :=
  ⟨bsSingleRound_noLightFault, bstZW, bsSingleRound_witness.1, bsSingleRound_witness.2.1,
    bsSingleRound_witness.2.2⟩

/-! ## 二、时间轴：只测支撑，重复 $T$ 轮（扁平坐标，显式校验矩阵）

比特编号 $3t+i$（第 $t$ 轮、支撑比特 $i$，$t<3$、$i<3$）。跨轮校验是"第 $t$ 轮与第 $t+1$ 轮
的全部比特"——两条相邻轮读出相等则校验为零，故这 $2$ 条校验**恰是"各轮读出全同"**。 -/

/-- 第 $t$ 轮的读出（该轮三个比特的指示向量）。 -/
def bsRound0 : Vec 9 := e 0 + e 1 + e 2

/-- 第 $1$ 轮的读出。 -/
def bsRound1 : Vec 9 := e 3 + e 4 + e 5

/-- 第 $2$ 轮的读出。 -/
def bsRound2 : Vec 9 := e 6 + e 7 + e 8

/-- **跨轮校验矩阵**（$T=3$）：第 $0$ 行是第 $0,1$ 轮的全部比特，第 $1$ 行是第 $1,2$ 轮的全部比特。 -/
def bsCrossChecks : Matrix (Fin 2) (Fin 9) (ZMod 2) :=
  Matrix.of ![
    e 0 + e 1 + e 2 + e 3 + e 4 + e 5,
    e 3 + e 4 + e 5 + e 6 + e 7 + e 8
  ]

/-- **跨轮校验的核刻画**：校验全零 $\iff$ 三轮读出全同——这就是"跨轮校验"的全部内容。 -/
theorem bsCrossChecks_ker_iff :
    ∀ f : Vec 9, inKerB bsCrossChecks f = true ↔
      (bsRound0 ⬝ᵥ f = bsRound1 ⬝ᵥ f ∧ bsRound1 ⬝ᵥ f = bsRound2 ⬝ᵥ f) := by
  decide

/-- **见证**：每一轮都把**同一个**比特的结果报错（重量 $3=T$）——三轮读出一致地翻转，
跨轮比较看不出任何异常。 -/
def bsMeasureW : Vec 9 := e 0 + e 3 + e 6

/-- 见证三事实：在校验核里（三轮读出全同且全为 $1$）、逻辑读出被翻转、重量 $=3=T$。 -/
theorem bsMeasureW_witness :
    inKerB bsCrossChecks bsMeasureW = true ∧ bsRound0 ⬝ᵥ bsMeasureW = 1 ∧
      hammingNorm bsMeasureW = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- **时间轴分量 $=3=T=d$（下界）**：躲过跨轮校验又翻转逻辑读出的故障模式，重量至少 $3$。

即"三轮里每一轮都必须各自不可探测地翻转一次"——一轮不同就暴露。 -/
theorem bsMeasure_noLightFault : NoLightFault bsCrossChecks bsRound0 3 :=
  noLightFault_of_faultCand_nil bsCrossChecks bsRound0 (by decide)

/-- **时间轴分量的两向夹逼**：$T=3$ 轮的横向测量，时空故障距离恰为 $3$——
下界见 `bsMeasure_noLightFault`，上界是 `bsMeasureW` 的见证。取 $T=d=3$ 即两分量都 $\ge d$。 -/
theorem bsMeasure_eq_T :
    (NoLightFault bsCrossChecks bsRound0 3) ∧
      (∃ f : Vec 9, inKerB bsCrossChecks f = true ∧ bsRound0 ⬝ᵥ f = 1 ∧ hammingNorm f = 3) :=
  ⟨bsMeasure_noLightFault, bsMeasureW, bsMeasureW_witness.1, bsMeasureW_witness.2.1,
    bsMeasureW_witness.2.2⟩

/-! ## 三、C2 的锐性：$T=2$ 时距离只有 $2<d$

"轮数 $\ge d$"不是一条宽松的充分条件，而是**恰好**的门槛：同一协议取 $T=2$ 时，
同样的构造给出距离 $2<3=d$——故 $T\ge d$ 是必要条件方向也成立的那条线。 -/

/-- $T=2$ 的跨轮校验矩阵：一行，两根轮的比特。 -/
def bsCrossChecks2 : Matrix (Fin 1) (Fin 6) (ZMod 2) :=
  Matrix.of (fun _ => (e 0 + e 1 + e 2 + e 3 + e 4 + e 5 : Vec 6))

/-- $T=2$ 时第 $0$ 轮的读出。 -/
def bsRound0of2 : Vec 6 := e 0 + e 1 + e 2

/-- **$T=2$ 时故障距离 $=2$**（下界）。 -/
theorem bsMeasure2_noLightFault : NoLightFault bsCrossChecks2 bsRound0of2 2 :=
  noLightFault_of_faultCand_nil bsCrossChecks2 bsRound0of2 (by decide)

/-- **C2 的锐性**：$T=2$ 的同一协议给出重量恰好 $2$ 的不可探测逻辑故障，而 $2<3=d$。
故"轮数 $<d$ $\Rightarrow$ 时间轴分量 $<d$"在这里是**显式见证**，不只是下界。 -/
theorem bsMeasure2_lt_d :
    ∃ f : Vec 6, inKerB bsCrossChecks2 f = true ∧ bsRound0of2 ⬝ᵥ f = 1 ∧
      hammingNorm f = 2 ∧ 2 < 3 :=
  ⟨e 0 + e 3, by decide, by decide, by decide, by norm_num⟩

/-! ### 三之二：另外两个轮数的读数（$T=1$ 与 $T=4$）

Figure 2 的测量曲线取四个轮数；下面两条把 $T=1$ 与 $T=4$ 也落成内核读数，
于是那条曲线的**每一个画出来的点**都有内核断言（四个轮数各一条）。 -/

/-- **$T=1$：一轮之内没有任何跨轮校验**，故重量 $1$ 的读数错误既不可探测又翻转逻辑，
距离恰为 $1$——这正是"横向测量必须靠时间轴保护"的极端读数。 -/
theorem bsMeasure1_eq_one :
    (NoLightFault (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) (e 0 + e 1 + e 2 : Vec 3) 1) ∧
      (∃ f : Vec 3,
        inKerB (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) f = true ∧
          (e 0 + e 1 + e 2 : Vec 3) ⬝ᵥ f = 1 ∧ hammingNorm f = 1) :=
  ⟨noLightFault_of_faultCand_nil _ _ (by decide),
    ⟨e 0, by decide, by decide, by decide⟩⟩

/-- $T=4$ 的跨轮校验矩阵：三行，第 $i$ 行是第 $i$ 与 $i+1$ 轮的全部比特。 -/
def bsCrossChecks4 : Matrix (Fin 3) (Fin 12) (ZMod 2) :=
  Matrix.of ![(e 0 + e 1 + e 2 + e 3 + e 4 + e 5 : Vec 12),
               (e 3 + e 4 + e 5 + e 6 + e 7 + e 8 : Vec 12),
               (e 6 + e 7 + e 8 + e 9 + e 10 + e 11 : Vec 12)]

/-- $T=4$ 时第 $0$ 轮的读出。 -/
def bsRound0of4 : Vec 12 := e 0 + e 1 + e 2

/-- **$T=4$ 的时间轴分量 $=4=T$（下界）**。 -/
theorem bsMeasure4_noLightFault : NoLightFault bsCrossChecks4 bsRound0of4 4 :=
  noLightFault_of_faultCand_nil bsCrossChecks4 bsRound0of4 (by decide)

/-- **$T=4$ 的见证**：每轮翻同一个比特，重量 $=4=T$。 -/
def bsMeasure4W : Vec 12 := e 0 + e 3 + e 6 + e 9

/-- 见证三事实：在校验核里、逻辑读出被翻转、重量 $=4=T$。 -/
theorem bsMeasure4W_witness :
    inKerB bsCrossChecks4 bsMeasure4W = true ∧ bsRound0of4 ⬝ᵥ bsMeasure4W = 1 ∧
      hammingNorm bsMeasure4W = 4 :=
  ⟨by decide, by decide, by decide⟩

/-- **$T=4$ 的时间轴分量两向夹逼：距离恰为 $4=T$**——测量曲线的第四点。 -/
theorem bsMeasure4_eq_T :
    (NoLightFault bsCrossChecks4 bsRound0of4 4) ∧
      (∃ f : Vec 12, inKerB bsCrossChecks4 f = true ∧ bsRound0of4 ⬝ᵥ f = 1 ∧
        hammingNorm f = 4) :=
  ⟨bsMeasure4_noLightFault, bsMeasure4W, bsMeasure4W_witness.1, bsMeasure4W_witness.2.1,
    bsMeasure4W_witness.2.2⟩

/-! ## 四、分层坐标：把 `MeasurementProtocol` 的时间轴律实例化

$\S$二 的扁平坐标便于 `by decide`，$\S$四 的分层坐标 `Fin T → Vec 3` 是
`MeasurementProtocol` 的通用形态。两者是同一个协议的两种写法，给出同一个数。 -/

/-- **时间轴律在此协议上的实例**：单轮距离 $s=1$（`bare_noLightFault`：只测支撑时
一轮之内无校验），故 $T$ 轮的时空故障重量 $\ge T\cdot 1=T$。 -/
theorem bsTransversal_time_lower {T : ℕ} (f : SpacetimeFault T 3)
    (hker : ∀ t, inKerB (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) (f t) = true)
    (hlog : ∀ t, bsColumnReadout ⬝ᵥ f t = 1) : T ≤ spacetimeWeight f := by
  simpa using le_spacetimeWeight (bare_noLightFault bsColumnReadout (n := 3)) hker hlog

/-- **$T=3$ 的见证**：每轮翻同一个比特，重量 $=3=T$——与 $\S$二 的 `bsMeasureW` 是同一模式
（把它按 $3t+i$ 摊开就是 $e_0+e_3+e_6$）。 -/
theorem bsTransversal_T3_witness :
    ∃ f : SpacetimeFault 3 3,
      IsUndetectedSpacetimeFault (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) bsColumnReadout f ∧
      spacetimeWeight f = 3 := by
  have h := spacetimeWeight_witness (T := 3) (s := 1) (H := (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)))
    (w := bsColumnReadout) (e (0 : Fin 3)) (by decide) (by decide) (by decide)
  simpa using h

/-- **测量型时间轴的通用下界（对一切轮数）**：各轮读出全同、且多数轮翻转时，
时空重量 $\ge T$。

证明只有一步：读出全同（`AgreeOn`）给出公共值 $b$；$b=1$ 时每一轮自己都有
$w\cdot f_t=1$，故每轮重量 $\ge1$，加起来即 $T$；$b=0$ 时没有一轮翻转，
与"多数轮翻转"直接矛盾。**注意跨轮约束在这里没有别的出路**：它只把各轮绑成同一个值，
而"翻转"要求那个值是 $1$，于是每一轮都得各自付一份重量。 -/
theorem le_spacetimeWeight_of_agree {T : ℕ} {f : SpacetimeFault T 3}
    (hagree : AgreeOn bsColumnReadout f)
    (hlog : T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card) :
    T ≤ spacetimeWeight f := by
  obtain ⟨b, hb⟩ := hagree
  have hcases : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
  by_cases hb1 : b = 1
  · have hone : ∀ t : Fin T, bsColumnReadout ⬝ᵥ f t = 1 := by
      intro t; rw [hb t, hb1]
    have hpos : ∀ t : Fin T, 1 ≤ hammingNorm (f t) := by
      intro t
      have hne : f t ≠ 0 := by
        intro h0
        have hd : bsColumnReadout ⬝ᵥ (0 : Vec 3) = 0 := by simp [dotProduct]
        have hd1 : bsColumnReadout ⬝ᵥ (0 : Vec 3) = 1 := by rw [← h0]; exact hone t
        rw [hd] at hd1
        exact one_ne_zero hd1.symm
      exact Nat.pos_of_ne_zero fun hz => hne (hammingNorm_eq_zero.mp hz)
    calc T = ∑ _t : Fin T, 1 := by simp
      _ ≤ ∑ t : Fin T, hammingNorm (f t) := Finset.sum_le_sum fun t _ => hpos t
      _ = spacetimeWeight f := rfl
  · have hb0 : b = 0 := hcases b hb1
    have hne : ∀ t : Fin T, bsColumnReadout ⬝ᵥ f t ≠ 1 := by
      intro t h1
      have hz : bsColumnReadout ⬝ᵥ f t = (0 : ZMod 2) := by rw [hb t, hb0]
      rw [hz] at h1
      exact one_ne_zero h1.symm
    have hemp : (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun t _ => hne t
    rw [hemp] at hlog
    simp at hlog

/-- **测量型时间轴的通用可达界（对一切轮数）**：把单轮见证复制到每一轮，
重量恰为 $T$——下界与它合起来即"距离 $=T$"。 -/
theorem spacetimeWeight_witness_of_agree {T : ℕ} (hT : 0 < T) :
    ∃ f : SpacetimeFault T 3, AgreeOn bsColumnReadout f ∧
      T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card ∧
      spacetimeWeight f = T := by
  have hdot : bsColumnReadout ⬝ᵥ (e 0 : Vec 3) = 1 := by decide
  have hwt : hammingNorm (e 0 : Vec 3) = 1 := by decide
  refine ⟨fun _ => (e 0 : Vec 3), ⟨1, fun _ => hdot⟩, ?_, ?_⟩
  · have hfil : (Finset.univ.filter
        (fun t : Fin T => bsColumnReadout ⬝ᵥ (fun _ => (e 0 : Vec 3)) t = 1)) = Finset.univ :=
      Finset.filter_eq_self.mpr fun _ _ => hdot
    rw [hfil, Finset.card_univ, Fintype.card_fin]
    omega
  · simp only [spacetimeWeight]
    rw [Finset.sum_congr rfl fun t _ => hwt, Finset.sum_const, Finset.card_univ]
    simp

/-- **只靠跨轮比较的测量模型，故障距离恰为轮数 $T$**（任意 $T\ge1$）：
下界是 `le_spacetimeWeight_of_agree`，可达是 `spacetimeWeight_witness_of_agree`。
$\S$三 的四条逐 $T$ 读数（$T=1,2,3,4$）就是这条的两侧在具体轮数上的取值。 -/
theorem measureTime_distance_eq_rounds {T : ℕ} (hT : 0 < T) :
    (∀ f : SpacetimeFault T 3, AgreeOn bsColumnReadout f →
      T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card →
      T ≤ spacetimeWeight f) ∧
    (∃ f : SpacetimeFault T 3, AgreeOn bsColumnReadout f ∧
      T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card ∧
      spacetimeWeight f = T) :=
  ⟨fun _ h1 h2 => le_spacetimeWeight_of_agree h1 h2, spacetimeWeight_witness_of_agree hT⟩

/-- **两分量各有一个内核实例**：空间轴 $3=d$（$\S$一）、时间轴 $T=d=3$（$\S$二/$\S$三），
而 $3$ 正是 `Codes/BaconShor.lean` 判出的码距 `bst_dX`。 -/
theorem bsMeasure_T_eq_codeDistance :
    (3 : ℕ) = min_weight_ker_not_mem_rowspace bstHz bstHx := by
  rw [bst_dX]

end QECCertificates
