/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BaconShorMeasurement

/-!
# 全协议的故障模型：数据 / 辅助比特 / 测量三类错误（Bacon–Shor 实例）

`Codes/MeasurementProtocol.lean` 的模型只含**测量错误**——"报告结果被翻转"。
对**横向测量**（把逻辑算符逐比特测掉、读出 = 乘积）这是够的：数据错误与测量错误
在结果上不可区分。但一旦校验由**辅助比特**测出，两类错误就分开了，而**分开的代价是
距离减半**——这正是 circuit-level 的 hook error。

本模块把模型扩到三类，并在 Bacon–Shor 上把数算出来：

| 故障 | 记号 | 翻转什么 |
|---|---|---|
| **数据错误** | `d` | **跨轮持续**：既翻转含它的校验、也翻转各轮读出 |
| **测量错误** | `μ` | **只影响本轮**：翻转本轮的校验与读出 |
| **辅助比特错误** | `g` | **只翻转本轮校验结果**、不动数据 |

$T$ 轮：累计数据错误 $f_t=\sum_{s\le t}d_s$；syndrome
$\sigma_t=H(f_t+\mu_t)+g_t$；探测器 $D_0=\sigma_0$（**边界**：初态在码空间里）
与 $D_t=\sigma_t+\sigma_{t-1}$；第 $t$ 轮读出 $=w\cdot(f_t+\mu_t)$；
逻辑出错 $\iff$ **多数轮**读出被翻转。

## 内核内算出的三条（`tools/probeA/full_protocol_probe.py` 逐条对拍）

1. **单轮距离 $=2=\lceil d/2\rceil$**（`bsHook_T1_distance_eq_two`）：
   一处数据错误 $d=e_q$（$q$ 在逻辑支撑上）配一处辅助比特错误 $g=Hd$——
   两者在 syndrome 上相消，数据错误却留了下来。**而只用测量错误时距离是 $3=d$**
   （`bsSingleRound_noLightFault`，见 `Codes/BaconShorMeasurement.lean`）：
   **辅助比特错误就是那半距离。**
2. **两轮起恢复**（`bsHook_T2_no_light` / `bsHook_T3_no_light`）：加边界检查后，
   重量 $\le2$ 的故障在 $T\ge2$ 轮里不再存在——数据错误跨轮持续，第二轮就露馅。
   **机制本身对任意轮数成立**（`bsDetectorsOK_syndrome_eq_zero`）：边界探测器先定下
   第一轮的 syndrome，相邻轮比较再逐轮把它递推到零，故"持续"从第二轮起无处藏身；
   上面两条 `decide` 是这条机制在 $T=2,3$ 上的读数。
3. **边界检查不可去**（`noBoundary_light_of_any_rounds`，**对任意轮数**）：去掉 $D_0$
   后，只在第 $0$ 轮出现的那一处数据错误从第 $0$ 轮起一直留在数据上，各轮 syndrome
   完全相同、相邻轮比较看不出差异，而每一轮的读出都被翻转——重量恰为 $1$。
   这条把判定层的 **C3**（首轮稳定子测量完美）量化成了数，且是**对一切 $T\ge1$ 的
   定理**，不是逐 $T$ 的枚举；`bsHook_noBoundary_weight_one` 是它在 $T=1$ 上的读数。

4. **C3 的两半不是两件事**（`c3_both_ends_agree`）：判定层把 C3 读作*"首轮与末轮都取为
   完美"*，而上面第三条只把**首轮**那一半变成了探测器。§六 补上**末轮**那一半并证明
   两者互为推论：首轮 + 相邻轮比较 ⟹ 全部 syndrome 为零（`bsDetectorsOK_closed_of_firstEnd`），
   **反过来**末轮 + 相邻轮比较也把全部 syndrome 钉在零（`bsDetectorsOK_firstEnd_syndrome_eq_zero`，
   反向归纳）；且补上末轮那一半**不改变候选集**（`hookCandClosed_eq`），故两半给出同一个距离。
   真正不可省的是"**至少有一端**完美"——两端都没有时第 3 条已把距离打到 $1$。

**口径**：模型仍是**现象学**的（每个故障位置翻转结果 / 传播到结果），
不是逐门的电路级仿真；辅助比特错误对数据的**传播**（hook 的另一半）在这里
表现为"辅助比特错误 + 数据错误配对"的模式。把门级位置逐一展开是它的下一步。

**C3 的两端都已建模**（§六）：判定层说的"首轮与末轮都取为完美"在本模块里是
**互为推论**的两条命题，而不是一条已建模、一条留白。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、表示层：三类故障与探测器 -/

/-! 每轮的故障位置数是 $20$：$9$ 个数据比特（$0..8$）、$9$ 个测量位置（$9..17$）、
$2$ 个校验的辅助比特（$18,19$）。故障模式写成 `Vec (T * 20)`，
**它的 Hamming 重量就是故障数**。 -/

/-- 第 `t` 轮的数据错误（跨轮持续）。 -/
def dataErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 20 + i.val, by have := i.isLt; have := t.isLt; omega⟩

/-- 第 `t` 轮的测量错误（只影响本轮）。 -/
def measErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 20 + 9 + i.val, by have := i.isLt; have := t.isLt; omega⟩

/-- 第 `t` 轮的辅助比特错误（只翻转本轮的校验结果）。 -/
def ancErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 2 :=
  fun c => f ⟨t.val * 20 + 18 + c.val, by have := c.isLt; have := t.isLt; omega⟩

/-- 到第 `t` 轮为止的**累计数据错误**（数据错误跨轮持续，这正是时间轴的来源）。 -/
def cumErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 9 :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val ≤ t.val), dataErr f s

/-- 第 `t` 轮的 syndrome：数据与测量错误都从结果里看得见，辅助比特错误只改校验。 -/
def bsSyndrome {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 2 :=
  bsStabChecks *ᵥ (cumErr f t + measErr f t) + ancErr f t

variable {T : ℕ}

/-- **探测器**：初态边界 $D_0=\sigma_0$ 加上相邻轮比较 $D_t=\sigma_t+\sigma_{t-1}$。

边界那一条是物理的：协议开始时码处在码空间里（syndrome 为零），
故第一轮的 syndrome 非零即已被发现。 -/
abbrev bsDetectorsOK (f : Vec (T * 20)) : Prop :=
  (∀ t : Fin T, t.val = 0 → bsSyndrome f t = 0) ∧
    (∀ t u : Fin T, u.val = t.val + 1 → bsSyndrome f t = bsSyndrome f u)

/-- 探测器，但**去掉边界那一条**（用来量化 C3 的作用）。 -/
abbrev bsDetectorsOK_noBoundary (f : Vec (T * 20)) : Prop :=
  ∀ t u : Fin T, u.val = t.val + 1 → bsSyndrome f t = bsSyndrome f u

/-- **恢复的机制（对任意 $T$）**：边界探测器加相邻轮比较，把所有 syndrome 一齐钉在零。

$D_0=\sigma_0$ 先定下第一轮，$D_t=\sigma_t+\sigma_{t-1}$ 再逐轮把它递推下去——
于是"故障跨轮持续"这件事从第二轮起无处藏身。这正是 $T\ge2$ 就恢复的机制：
持续的数据错误不是被**某一轮**的校验抓住的，而是被"两轮之间必须一致"这条约束抓住的。

一条对任意轮数成立的定理，而不是逐 $T$ 的枚举：前面 `bsHook_T2_no_light` 等
四条 `decide` 算的是这条机制在具体轮数上的读数。 -/
theorem bsDetectorsOK_syndrome_eq_zero {f : Vec (T * 20)}
    (h : bsDetectorsOK f) (t : Fin T) : bsSyndrome f t = 0 := by
  obtain ⟨hb, hs⟩ := h
  have key : ∀ k, ∀ t : Fin T, t.val = k → bsSyndrome f t = 0 := by
    intro k
    induction k with
    | zero => intro t ht; exact hb t ht
    | succ k ih =>
      intro t ht
      have hk : k < T := by have := t.isLt; omega
      have hstep : bsSyndrome f ⟨k, hk⟩ = bsSyndrome f t :=
        hs ⟨k, hk⟩ t (by omega)
      rw [← hstep]
      exact ih ⟨k, hk⟩ rfl
  exact key t.val t rfl

/-- 第 `t` 轮读出的逻辑值（逻辑支撑上三个结果的乘积）。 -/
def bsReadout (f : Vec (T * 20)) (t : Fin T) : ZMod 2 :=
  bstXW ⬝ᵥ (cumErr f t + measErr f t)

/-- **逻辑出错**：多数轮的读出被翻转（$T$ 轮的重复正是为了这一票）。 -/
abbrev bsLogicalFault (f : Vec (T * 20)) : Prop :=
  T < 2 * (Finset.univ.filter (fun t : Fin T => bsReadout f t = 1)).card

/-- **全协议下重量 $\le s$ 的不可探测逻辑故障候选**（与库内 `lightCand` 同形：
重量限定的枚举，**故障重量就是向量的 Hamming 重量**）。 -/
def hookCand (T s : ℕ) : List (Vec (T * 20)) :=
  (lightVecs (T * 20) s).filter
    (fun f => decide (bsDetectorsOK f ∧ bsLogicalFault f))

/-! ## 二、单轮：hook error，距离 $2=\lceil d/2\rceil$ -/

/-- **见证（hook error）**：一处数据错误（逻辑支撑上比特 $0$，即列 $0$ 的顶点）
配一处辅助比特错误（校验 $S_{01}$）。数据错误使 $S_{01}$ 的结果翻转，
辅助比特错误把它翻回去——syndrome 为零，而数据错误留在数据上并翻转了读出。

按每轮 20 个位置编号，这是"位置 $0$ + 位置 $18$"。 -/
def hookW1 : Vec (1 * 20) :=
  (e ⟨0, by omega⟩ : Vec (1 * 20)) + (e ⟨18, by omega⟩ : Vec (1 * 20))

/-- 见证三事实：探测器全零（含边界）、逻辑被翻转、重量恰为 $2$。 -/
theorem bsHook_T1_witness :
    bsDetectorsOK hookW1 ∧ bsLogicalFault hookW1 ∧ hammingNorm hookW1 = 2 :=
  ⟨by decide, by decide, by decide⟩

/-- **单轮下界**：重量 $\le1$ 的故障不可能既不可探测又翻转逻辑。 -/
theorem bsHook_T1_no_light_one : hookCand 1 1 = [] := by decide

/-- **单轮故障距离 $=2$**（两向夹逼）。

与只用测量错误的模型对照：那里单轮距离是 $3=d$（`bsSingleRound_noLightFault`）。
**辅助比特错误把距离减半**——这正是 hook error 的内容，也是"只在测量错误模型里
算距离会高估"的量化。 -/
theorem bsHook_T1_distance_eq_two :
    (hookCand 1 1 = []) ∧
      (∃ f : Vec (1 * 20),
        bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 2) :=
  ⟨bsHook_T1_no_light_one, hookW1, bsHook_T1_witness.1, bsHook_T1_witness.2.1,
    bsHook_T1_witness.2.2⟩

/-! ## 三、两轮起恢复：数据错误跨轮持续，第二轮就露馅 -/

/-- **$T=2$：重量 $\le2$ 的故障不再存在**——边界检查 + 第二轮把 hook 抓住。 -/
theorem bsHook_T2_no_light : hookCand 2 2 = [] := by decide

/-- **$T=3$：同样**。 -/
theorem bsHook_T3_no_light : hookCand 3 2 = [] := by decide

-- **注意 `set_option ... in` 必须写在 docstring 之前**：写在 docstring 与 `theorem` 之间时，
-- docstring 会挂到 `set_option` 上，报 `unexpected token 'set_option'; expected 'lemma'`。
set_option maxHeartbeats 40000000 in
/-- **$T=4$：同样没有重量 $\le2$ 的逃逸**。

四条 $T$ 里最贵的一条：候选集是 `lightVecs 80 2` 的过滤（$1+80+\binom{80}{2}=3241$ 个），
故逐定理给心跳预算（模块级的 8M 不够，实测 40M 通过、约 5 分 40 秒）。 -/
theorem bsHook_T4_no_light : hookCand 4 2 = [] := by decide

/-- **恢复后的最优逃逸模式**：把码的一个重量-$3$ 逻辑算符（单行全 $X$，即
`Codes/BaconShor.lean` 的 `bstZW`）当作**从第 $0$ 轮起持续**的数据错误。
它与每条校验的相交都是偶数——syndrome 全零，各轮读出全一样且都被翻转。

这正是"逃不掉的那半"：hook 被第二轮抓住之后，最省的逃逸退回**空间型**逻辑错误，
重量 $3=d$。探针给出的重量-$3$ 逃逸就是它（`tools/probeA/full_protocol_probe.py`）。 -/
def hookW3 (T : ℕ) : Vec ((T + 1) * 20) :=
  (e ⟨0, by omega⟩ : Vec ((T + 1) * 20)) + e ⟨1, by omega⟩ + e ⟨2, by omega⟩

/-- 两轮协议里这条重量-$3$ 见证的三事实。 -/
theorem bsHook_twoRounds_witness :
    bsDetectorsOK (hookW3 1) ∧ bsLogicalFault (hookW3 1) ∧ hammingNorm (hookW3 1) = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- 三轮协议里同样。 -/
theorem bsHook_threeRounds_witness :
    bsDetectorsOK (hookW3 2) ∧ bsLogicalFault (hookW3 2) ∧ hammingNorm (hookW3 2) = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- 四轮协议里同样（`hookW3 3 : Vec (4 * 20)`）。 -/
theorem bsHook_fourRounds_witness :
    bsDetectorsOK (hookW3 3) ∧ bsLogicalFault (hookW3 3) ∧ hammingNorm (hookW3 3) = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- **$T=2$ 的故障距离恰为 $3=d$**（两向夹逼）：重量 $\le2$ 的逃逸不存在，
而重量 $3$ 的有显式见证。**hook 被抓住了，逃逸退回空间型。** -/
theorem bsHook_T2_distance_eq_three :
    (hookCand 2 2 = []) ∧
      (∃ f : Vec (2 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3) :=
  ⟨bsHook_T2_no_light, hookW3 1, bsHook_twoRounds_witness.1,
    bsHook_twoRounds_witness.2.1, bsHook_twoRounds_witness.2.2⟩

/-- **$T=3$ 的故障距离同样恰为 $3=d$**。 -/
theorem bsHook_T3_distance_eq_three :
    (hookCand 3 2 = []) ∧
      (∃ f : Vec (3 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3) :=
  ⟨bsHook_T3_no_light, hookW3 2, bsHook_threeRounds_witness.1,
    bsHook_threeRounds_witness.2.1, bsHook_threeRounds_witness.2.2⟩

/-- **$T=4$ 的故障距离同样恰为 $3=d$**——四轮的读数是 Figure 2 完整协议曲线的第四点。 -/
theorem bsHook_T4_distance_eq_three :
    (hookCand 4 2 = []) ∧
      (∃ f : Vec (4 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3) :=
  ⟨bsHook_T4_no_light, hookW3 3, bsHook_fourRounds_witness.1,
    bsHook_fourRounds_witness.2.1, bsHook_fourRounds_witness.2.2⟩

/-! ## 四、边界检查不可去（把判定层的 C3 量化） -/

/-- **去掉边界探测器后，重量 $1$ 的数据错误即不可探测**：它让所有轮的 syndrome
一起平移，相邻轮比较看不出任何差异，读出却被翻转——故距离塌到 $1$。

这条是判定层 **C3**（首轮稳定子测量完美）的量化：C3 不是技术约定，
它支撑的正是"时间轴从第一轮起就有参照"这件事。

**注意 $T=1$ 时它是空的**：没有相邻轮，故"相邻轮比较"这个合取恒成立，
本条只说"一个探测器都没有时重量 1 的故障跑得掉"。实质内容在
`noBoundary_light_of_any_rounds`，那一条对任意轮数成立。 -/
theorem bsHook_noBoundary_weight_one :
    ∃ f : Vec (1 * 20),
      bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1 :=
  ⟨(e ⟨0, by omega⟩ : Vec (1 * 20)), by decide, by decide, by decide⟩

/-! ## 五、边界检查不可去：对**任意轮数**成立的那一条

上一节的 `bsHook_noBoundary_weight_one` 是 $T=1$ 的实例，而 $T=1$ 时"相邻轮比较"
这个合取是空的——它其实什么都没验。下面这条才是"边界检查不可去"的实质内容。 -/

/-- 去掉边界探测器后用到的见证：**只在第 0 轮出现的一处数据错误**（位置 0，
即逻辑支撑上的比特 0）。数据错误在 `cumErr` 里是累计的，故它从第 0 轮起一直
留在数据上，各轮的 syndrome 因此完全相同。 -/
def noBoundW (T : ℕ) (h : 0 < T) : Vec (T * 20) :=
  e ⟨0, by omega⟩

private lemma ne_zero_index {T : ℕ} {k : ℕ} (hk : k ≠ 0) (h : k < T * 20) :
    (⟨k, h⟩ : Fin (T * 20)) ≠ (⟨0, by omega⟩ : Fin (T * 20)) := by
  intro hcon
  exact hk (by have := congrArg Fin.val hcon; simp only at this; exact this)

private lemma noBoundW_dataErr_zero {T : ℕ} (h : 0 < T) {s : Fin T} (hs : s.val ≠ 0) :
    dataErr (noBoundW T h) s = 0 := by
  funext i
  simp only [dataErr, noBoundW, e]
  have hne := ne_zero_index (T := T) (k := s.val * 20 + i.val)
    (by omega) (by have := i.isLt; have := s.isLt; omega)
  rw [ite_eq_right hne]
  rfl

private lemma noBoundW_dataErr_self {T : ℕ} (h : 0 < T) :
    dataErr (noBoundW T h) ⟨0, h⟩ = (e ⟨0, by norm_num⟩ : Vec 9) := by
  funext i
  simp only [dataErr, noBoundW, e]
  by_cases hi : i.val = 0
  · have h1 : (⟨0 * 20 + i.val, by omega⟩ : Fin (T * 20)) = ⟨0, by omega⟩ := by
      apply Fin.ext; simp only; omega
    have h2 : i = (⟨0, by norm_num⟩ : Fin 9) := by
      apply Fin.ext; simp only; omega
    rw [ite_eq_left h1, ite_eq_left h2]
  · have h1 := ne_zero_index (T := T) (k := 0 * 20 + i.val)
      (by omega) (by omega)
    have h2 : ¬ (i = (⟨0, by norm_num⟩ : Fin 9)) := by
      intro hcon; exact hi (by have := congrArg Fin.val hcon; simp only at this; omega)
    rw [ite_eq_right h1, ite_eq_right h2]

private lemma noBoundW_cumErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    cumErr (noBoundW T h) t = (e ⟨0, by norm_num⟩ : Vec 9) := by
  rw [cumErr, Finset.sum_filter]
  have hsingle : (Finset.sum Finset.univ (fun s : Fin T =>
      if s.val ≤ t.val then dataErr (noBoundW T h) s else 0))
      = dataErr (noBoundW T h) ⟨0, h⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin T)))
      (f := fun s : Fin T => if s.val ≤ t.val then dataErr (noBoundW T h) s else 0)
      ⟨0, h⟩ ?_ ?_
    · intro b _ hb
      by_cases hle : b.val ≤ t.val
      · rw [ite_eq_left hle]
        exact noBoundW_dataErr_zero h (fun hz => hb (Fin.ext hz))
      · rw [ite_eq_right hle]
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, h⟩ : Fin T)) hnot
  rw [hsingle]
  exact noBoundW_dataErr_self h

private lemma noBoundW_measErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    measErr (noBoundW T h) t = 0 := by
  funext i
  simp only [measErr, noBoundW, e]
  have hne := ne_zero_index (T := T) (k := t.val * 20 + 9 + i.val)
    (by omega) (by have := i.isLt; have := t.isLt; omega)
  rw [ite_eq_right hne]
  rfl

private lemma noBoundW_ancErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    ancErr (noBoundW T h) t = 0 := by
  funext c
  simp only [ancErr, noBoundW, e]
  have hne := ne_zero_index (T := T) (k := t.val * 20 + 18 + c.val)
    (by omega) (by have := c.isLt; have := t.isLt; omega)
  rw [ite_eq_right hne]
  rfl

private lemma noBoundW_syndrome {T : ℕ} (h : 0 < T) (t : Fin T) :
    bsSyndrome (noBoundW T h) t = bsSyndrome (noBoundW T h) ⟨0, h⟩ := by
  simp only [bsSyndrome, noBoundW_cumErr h t, noBoundW_cumErr h ⟨0, h⟩,
    noBoundW_measErr h t, noBoundW_measErr h ⟨0, h⟩,
    noBoundW_ancErr h t, noBoundW_ancErr h ⟨0, h⟩]

private lemma bstXW_dot_e0 : bstXW ⬝ᵥ (e ⟨0, by norm_num⟩ : Vec 9) = 1 := by decide

private lemma noBoundW_readout {T : ℕ} (h : 0 < T) (t : Fin T) :
    bsReadout (noBoundW T h) t = 1 := by
  simp only [bsReadout, noBoundW_cumErr h t, noBoundW_measErr h t, add_zero]
  exact bstXW_dot_e0

private lemma noBoundW_weight {T : ℕ} (h : 0 < T) :
    hammingNorm (noBoundW T h) = 1 := by
  rw [← weight_eq_hammingNorm]
  have hsingle : support (noBoundW T h) = {⟨0, by omega⟩} := by
    ext j
    rw [mem_support, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      exact hj (by simp [noBoundW, e, hne])
    · intro hj
      rw [hj]
      simp [noBoundW, e]
  rw [hsingle, Finset.card_singleton]

/-- **去掉边界探测器后，任意轮数下都有重量 1 的不可探测逻辑故障**。

与 `bsHook_noBoundary_weight_one` 的关系：那一条是 $T=1$ 的实例，而 $T=1$ 时
"相邻轮比较"这个合取是空的，故它其实什么都没验；本条才是"边界检查不可去"
那句的实质内容——见证在**每一轮**都翻转读出，而各轮 syndrome 完全相同。 -/
theorem noBoundary_light_of_any_rounds {T : ℕ} (h : 0 < T) :
    ∃ f : Vec (T * 20),
      bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1 := by
  refine ⟨noBoundW T h, ?_, ?_, noBoundW_weight h⟩
  · intro t u _
    rw [noBoundW_syndrome h t, noBoundW_syndrome h u]
  · have hall : ∀ t : Fin T, bsReadout (noBoundW T h) t = 1 := noBoundW_readout h
    have hfilter : (Finset.univ.filter
        (fun t : Fin T => bsReadout (noBoundW T h) t = 1)) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun t _ => hall t)
    rw [bsLogicalFault, hfilter, Finset.card_univ, Fintype.card_fin]
    omega

/-- **对照汇总**：三条数放在一起——单轮 $2$，两轮起回到 $\ge$ 边界，
去掉边界则在**任意轮数**下塌到 $1$。

最后一条是 `noBoundary_light_of_any_rounds`（对一切 $T\ge1$），
而不是 $T=1$ 的那个空实例；两条都留着，因为 $T=1$ 那条是它的读数。 -/
theorem bsHook_summary :
    (hookCand 1 1 = []) ∧ (hookCand 2 2 = []) ∧ (hookCand 3 2 = []) ∧
      (hookCand 4 2 = []) ∧
      (∃ f : Vec (1 * 20),
        bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1) ∧
      (∀ T : ℕ, 0 < T → ∃ f : Vec (T * 20),
        bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1) :=
  ⟨bsHook_T1_no_light_one, bsHook_T2_no_light, bsHook_T3_no_light, bsHook_T4_no_light,
    bsHook_noBoundary_weight_one, fun _ hT => noBoundary_light_of_any_rounds hT⟩

/-! ## 六、C3 的两半：**任一端**的完美都足以定下整条时间轴

判定层把 C3 读作**边界条件**：*"首轮与末轮都取为完美"*。本模块把**首轮**那一半
变成探测器——$D_0=\sigma_0$，理由是协议开始时码处在码空间里。**末轮**那一半是：
最后一轮之后码仍在码空间里，故末轮的 syndrome 也为零。

这一节证明这两半在模型里**不是独立的两件事**，而是同一条链的两端：

* 首轮 + 相邻轮比较 $\Rightarrow$ 所有 syndrome 为零（§一已有的机制），末轮那条是**被蕴含的**；
* **反过来同样成立**：末轮 + 相邻轮比较也把所有 syndrome 钉在零（反向归纳，见下）。

于是"本模块只建模了 C3 的首轮一半"**不再是一个缺口**——两半互为推论，且
**两侧给出的候选集逐元素相同**，故 C3 的两半给出同一个距离。真正不可省的是
"至少有一端完美"：两端都没有时，`noBoundary_light_of_any_rounds` 已经把距离打到 1。 -/

/-- 探测器，**两侧边界都写出来**（首轮 $D_0=\sigma_0$ 与末轮 $\sigma_{T-1}=0$）。 -/
abbrev bsDetectorsOK_closed (f : Vec (T * 20)) : Prop :=
  bsDetectorsOK f ∧ ∀ t : Fin T, t.val + 1 = T → bsSyndrome f t = 0

/-- 探测器，**只有末轮那一端**（相邻轮比较加末轮 $\sigma_{T-1}=0$，去掉首轮的 $D_0$）。 -/
abbrev bsDetectorsOK_terminal (f : Vec (T * 20)) : Prop :=
  (∀ t u : Fin T, u.val = t.val + 1 → bsSyndrome f t = bsSyndrome f u) ∧
    ∀ t : Fin T, t.val + 1 = T → bsSyndrome f t = 0

/-- **末轮那一端由首轮那一端蕴含**（§一那条机制的直接推论）。 -/
theorem bsDetectorsOK_closed_of_firstEnd {f : Vec (T * 20)}
    (h : bsDetectorsOK f) : bsDetectorsOK_closed f :=
  ⟨h, fun t _ => bsDetectorsOK_syndrome_eq_zero h t⟩

/-- **首轮那一端由末轮那一端蕴含**（反向归纳：末轮先定零，相邻轮比较再往前推）。 -/
theorem bsDetectorsOK_firstEnd_syndrome_eq_zero {f : Vec (T * 20)}
    (h : bsDetectorsOK_terminal f) (t : Fin T) : bsSyndrome f t = 0 := by
  obtain ⟨hs, hterm⟩ := h
  have key : ∀ k, ∀ t : Fin T, t.val + k = T - 1 → bsSyndrome f t = 0 := by
    intro k
    induction k with
    | zero =>
      intro t ht
      exact hterm t (by omega)
    | succ k ih =>
      intro t ht
      have hlt : t.val + 1 < T := by omega
      rw [hs t ⟨t.val + 1, hlt⟩ rfl]
      exact ih ⟨t.val + 1, hlt⟩ (by simp only; omega)
  exact key (T - 1 - t.val) t (by omega)

/-- **两端等价**：末轮那一端 + 相邻轮比较，与"首轮那一端 + 相邻轮比较"给出同一个
零 syndrome 结论（两条定理互为镜像）。 -/
theorem bsDetectorsOK_syndrome_eq_zero_of_terminal {f : Vec (T * 20)}
    (h : bsDetectorsOK_terminal f) (t : Fin T) : bsSyndrome f t = 0 :=
  bsDetectorsOK_firstEnd_syndrome_eq_zero h t

/-- 用**两侧边界**的探测器集做同一个重量限定枚举。 -/
def hookCandClosed (T s : ℕ) : List (Vec (T * 20)) :=
  (lightVecs (T * 20) s).filter
    (fun f => decide (bsDetectorsOK_closed f ∧ bsLogicalFault f))

-- 不设 `hookCandTerminal`（用末轮那端的探测器集做的同一个枚举）：它不会被使用，而
-- "两端给出同一个候选集"这件事**已经**由 `hookCandClosed_eq` 证了
-- （closed 与首端逐元素相同，配 `bsDetectorsOK_firstEnd_syndrome_eq_zero` 把末端
-- 也算进来）。留一个没有定理支撑的镜像定义，比不留更容易被误读成"那一侧也证过"。
/-- **两侧边界不改变候选集**：把末轮那一半补进探测器集，重量限定的候选集逐元素相同
（故 C3 的两半给出同一个距离）。 -/
theorem hookCandClosed_eq (T s : ℕ) : hookCandClosed T s = hookCand T s := by
  unfold hookCandClosed hookCand
  refine List.filter_congr fun f _ => ?_
  congr 1
  exact propext
    ⟨fun h => ⟨h.1.1, h.2⟩,
     fun h => ⟨bsDetectorsOK_closed_of_firstEnd h.1, h.2⟩⟩

/-- **C3 两半的裁定**：判定层那句"首轮与末轮都取为完美"里，**任一端**在本模型里
都已经把整条时间轴的 syndrome 定为零；两端同时写上不改变候选集。
故"只建模了首轮那一半"不是一个缺口——末轮那一半由已建模的那一半发放。 -/
theorem c3_both_ends_agree (T s : ℕ) :
    hookCandClosed T s = hookCand T s ∧
      (∀ f : Vec (T * 20), bsDetectorsOK_terminal f →
        ∀ t : Fin T, bsSyndrome f t = 0) :=
  ⟨hookCandClosed_eq T s, fun _ h => bsDetectorsOK_firstEnd_syndrome_eq_zero h⟩

/-! ## 七、万有恢复：$T\ge2$ 的"重量 $\le2$ 无逃逸"对一切轮数成立

$\S$三 的 `bsHook_T2_no_light` / `bsHook_T3_no_light` / `bsHook_T4_no_light` 是三条
逐 $T$ 的 `decide` 读数。这一节把"堵死"升成**定理**：$T\ge4$ 直接证，$T=2,3$ 沿用
`decide`，合起来对一切 $T\ge2$ 成立——与 $\S$五 那条对任意轮数的塌缩
（`noBoundary_light_of_any_rounds`）恰成对照：**删探测器的一侧对一切 $T$ 成立，
堵死逃逸的一侧也对一切 $T$ 成立**。

论证三步，每步一行可读：

1. **未被碰的轮读出为零**。重量 $\le2$ 的故障至多占据两个轮次；在没被碰的轮 $t$ 上
   $\mu_t=\gamma_t=0$，故 $\sigma_t=H\cdot\mathrm{cum}_t$，而机制定理（$\S$一）已把
   $\sigma_t$ 钉在零——**累计数据错误落在核里**。它的重量不超过故障重量 $\le2$，
   小于单轮距离 $3$（`bsSingleRound_noLightFault`），故读出泛函取零。
2. **翻转轮 $\subseteq$ 被碰轮**，而被碰轮数 $\le$ 故障重量 $\le2$（每轮至少占一个
   非零槽位）。
3. **多数票不够**：$T<2\times\text{翻转轮数}\le4$，与 $T\ge4$ 矛盾。

第 1 步正是 hook error 必须拉上一个辅助比特错误的原因：纯数据错误若轻于 $3$，
要么被核排除，要么根本翻不动读出。 -/

/-- **被碰轮次**：故障支撑所在的那几个轮（槽位号除以 $20$）。 -/
def touchedRounds {T : ℕ} (f : Vec (T * 20)) : Finset (Fin T) :=
  (support f).image (fun j => ⟨j.val / 20, by have := j.isLt; omega⟩)

/-- **被碰轮数 $\le$ 故障重量**：每个被碰轮至少占用一个非零槽位。 -/
theorem card_touchedRounds_le {T : ℕ} (f : Vec (T * 20)) :
    (touchedRounds f).card ≤ hammingNorm f := by
  rw [touchedRounds, ← weight_eq_hammingNorm]
  exact Finset.card_image_le

/-- **累计数据错误的重量 $\le$ 故障重量**：核支撑的每个非零坐标来自某个非零数据槽
（和为零则每项为零，取一个非零项即得单射）。 -/
theorem wt_cumErr_le {T : ℕ} (f : Vec (T * 20)) (t : Fin T) :
    hammingNorm (cumErr f t) ≤ hammingNorm f := by
  classical
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm]
  have hex : ∀ i : Fin 9, ∃ s : Fin T, s.val ≤ t.val ∧
      (i ∈ support (cumErr f t) → f ⟨s.val * 20 + i.val,
        by have := s.isLt; have := i.isLt; omega⟩ ≠ 0) := by
    intro i
    by_cases hi : i ∈ support (cumErr f t)
    · by_contra hcon
      push Not at hcon
      have hz : cumErr f t i = 0 := by
        rw [cumErr]
        simp only [dataErr, Finset.sum_apply]
        refine Finset.sum_eq_zero fun s hsm => ?_
        by_cases hs : s.val ≤ t.val
        · exact (hcon s hs).2
        · exact absurd (Finset.mem_filter.mp hsm).2 hs
      exact (mem_support.mp hi) hz
    · exact ⟨t, le_refl _, fun h => absurd h hi⟩
  choose φ hφ using hex
  have hbnd : ∀ i : Fin 9, (φ i).val * 20 + i.val < T * 20 := by
    intro i
    have h1 := (φ i).isLt
    have h2 := i.isLt
    omega
  refine Finset.card_le_card_of_injOn
    (f := fun i : Fin 9 => ⟨(φ i).val * 20 + i.val, hbnd i⟩) ?_ ?_
  · intro i hi
    exact mem_support.mpr ((hφ i).2 (Finset.mem_coe.mp hi))
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    have hfa := (φ a).isLt
    have hfb := (φ b).isLt
    have ha := a.isLt
    have hb := b.isLt
    exact Fin.val_injective (by omega)

/-- 未被碰的轮上，该轮的全部槽位都是零。 -/
private lemma slot_zero_of_untouched {T : ℕ} {f : Vec (T * 20)} {t : Fin T}
    (hnt : t ∉ touchedRounds f) (k : ℕ) (hk : k < 20) :
    f ⟨t.val * 20 + k, by have := t.isLt; omega⟩ = 0 := by
  by_contra hne
  have ht := t.isLt
  refine hnt (Finset.mem_image.mpr ⟨⟨t.val * 20 + k, by omega⟩,
    mem_support.mpr hne, by
      exact Fin.ext (show (t.val * 20 + k) / 20 = t.val by omega)⟩)

/-- 未被碰的轮上，测量错误与辅助比特错误都是零。 -/
private lemma untouched_parts {T : ℕ} {f : Vec (T * 20)} {t : Fin T}
    (hnt : t ∉ touchedRounds f) :
    measErr f t = 0 ∧ ancErr f t = 0 := by
  constructor
  · funext c
    have hc := c.isLt
    have ht := t.isLt
    have h0 := slot_zero_of_untouched hnt (9 + c.val) (by omega)
    have hconv : (⟨t.val * 20 + 9 + c.val, by omega⟩ : Fin (T * 20))
        = ⟨t.val * 20 + (9 + c.val), by omega⟩ :=
      Fin.ext (show t.val * 20 + 9 + c.val = t.val * 20 + (9 + c.val) by omega)
    rw [measErr, hconv]
    exact h0
  · funext c
    have hc := c.isLt
    have ht := t.isLt
    have h0 := slot_zero_of_untouched hnt (18 + c.val) (by omega)
    have hconv : (⟨t.val * 20 + 18 + c.val, by omega⟩ : Fin (T * 20))
        = ⟨t.val * 20 + (18 + c.val), by omega⟩ :=
      Fin.ext (show t.val * 20 + 18 + c.val = t.val * 20 + (18 + c.val) by omega)
    rw [ancErr, hconv]
    exact h0

/-- **第 1 步**：未被碰的轮上读出为零——累计数据错误落在核里、重量 $<3$，
而单轮距离恰为 $3$，故读出泛函取零。 -/
private lemma readout_eq_zero_of_untouched {T : ℕ} {f : Vec (T * 20)}
    (hdet : bsDetectorsOK f) (hw : hammingNorm f ≤ 2) {t : Fin T}
    (hnt : t ∉ touchedRounds f) : bsReadout f t = 0 := by
  obtain ⟨hμ, hγ⟩ := untouched_parts hnt
  have hσ := bsDetectorsOK_syndrome_eq_zero hdet t
  rw [bsSyndrome, hμ, hγ, add_zero, add_zero] at hσ
  have hker : inKerB bsStabChecks (cumErr f t) = true := by
    rw [inKerB_iff, mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    have hi : (bsStabChecks *ᵥ cumErr f t) i = 0 := congrFun hσ i
    simpa [Matrix.mulVec] using hi
  have hwt : hammingNorm (cumErr f t) ≤ 2 := le_trans (wt_cumErr_le f t) hw
  show bstXW ⬝ᵥ (cumErr f t + measErr f t) = 0
  rw [hμ, add_zero]
  have h01 : bstXW ⬝ᵥ cumErr f t = 0 ∨ bstXW ⬝ᵥ cumErr f t = 1 := by
    have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact hx _
  rcases h01 with h0 | h1
  · exact h0
  · exact absurd (bsSingleRound_noLightFault (cumErr f t) ⟨hker, h1⟩) (by omega)

/-- **万有恢复（下界侧）**：$T\ge4$ 轮里，重量 $\le2$ 的故障不可能既不可探测又翻转
逻辑。 -/
theorem bsHook_no_light_of_four_le {T : ℕ} (hT : 4 ≤ T) {f : Vec (T * 20)}
    (hw : hammingNorm f ≤ 2) (hdet : bsDetectorsOK f) : ¬ bsLogicalFault f := by
  intro hlog
  have hsub : (Finset.univ.filter (fun t : Fin T => bsReadout f t = 1))
      ⊆ touchedRounds f := by
    intro t ht
    by_contra hnt
    have h0 := readout_eq_zero_of_untouched hdet hw hnt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h0] at ht
    exact absurd ht (by decide)
  have hcard := Finset.card_le_card hsub
  have h2 := le_trans hcard (le_trans (card_touchedRounds_le f) hw)
  rw [bsLogicalFault] at hlog
  omega

/-- **万有恢复**：对一切 $T\ge2$，重量 $\le2$ 的不可探测逻辑故障不存在
（$T=2,3$ 是既有 `decide`，$T\ge4$ 是上面的定理）。 -/
theorem bsHook_no_light_universal {T : ℕ} (hT : 2 ≤ T) : hookCand T 2 = [] := by
  rcases (show T = 2 ∨ T = 3 ∨ 4 ≤ T by omega) with rfl | rfl | h4
  · exact bsHook_T2_no_light
  · exact bsHook_T3_no_light
  · refine (List.filter_eq_nil_iff).mpr fun f hf => ?_
    have hw : hammingNorm f ≤ 2 := by
      have hwt := wt_le_of_mem_lightVecs (T * 20) 2 f hf
      rwa [wtRec_eq_hammingNorm] at hwt
    simp only [decide_eq_true_eq]
    intro hp
    obtain ⟨hdet, hlog⟩ := hp
    exact bsHook_no_light_of_four_le h4 hw hdet hlog

/-- **空间型逃逸（对一切轮数）**：把码的单行全 $X$（$=$ Z 型裸逻辑 `bstZW`，重量 $3$）
当作从第 $0$ 轮起持续的数据错误——它与每条轮内校验相交偶数次，syndrome 全零，
各轮读出全为 $1$。写成槽位指示向量：前三个槽位（第 $0$ 轮的数据比特 $0,1,2$）。 -/
def hookW3gen (T : ℕ) : Vec (T * 20) :=
  fun j => if j.val = 0 ∨ j.val = 1 ∨ j.val = 2 then 1 else 0

/-- `bstZW` 逐坐标就是这个三槽指示（闭式，`decide` 直证）。 -/
private theorem bstZW_apply : ∀ i : Fin 9,
    bstZW i = if i.val = 0 ∨ i.val = 1 ∨ i.val = 2 then (1 : ZMod 2) else 0 := by decide

private lemma hookW3gen_dataErr_zero {T : ℕ} {s : Fin T} (hs : s.val ≠ 0) :
    dataErr (hookW3gen T) s = 0 := by
  funext i
  show (if s.val * 20 + i.val = 0 ∨ s.val * 20 + i.val = 1 ∨ s.val * 20 + i.val = 2
      then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3gen_dataErr_self {T : ℕ} (h : 0 < T) :
    dataErr (hookW3gen T) ⟨0, h⟩ = bstZW := by
  funext i
  show (if (0 : ℕ) * 20 + i.val = 0 ∨ 0 * 20 + i.val = 1 ∨ 0 * 20 + i.val = 2
      then (1 : ZMod 2) else 0) = bstZW i
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [bstZW_apply]

private lemma hookW3gen_cumErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    cumErr (hookW3gen T) t = bstZW := by
  rw [cumErr, Finset.sum_filter]
  have hsingle : ∑ s ∈ Finset.univ, (if s.val ≤ t.val then dataErr (hookW3gen T) s else 0)
      = dataErr (hookW3gen T) ⟨0, h⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin T)))
      (f := fun s : Fin T => if s.val ≤ t.val then dataErr (hookW3gen T) s else 0)
      ⟨0, h⟩ ?_ ?_
    · intro b _ hb
      by_cases hle : b.val ≤ t.val
      · rw [ite_eq_left hle]
        exact hookW3gen_dataErr_zero (fun hz => hb (Fin.ext hz))
      · rw [ite_eq_right hle]
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, h⟩ : Fin T)) hnot
  rw [hsingle]
  exact hookW3gen_dataErr_self h

private lemma hookW3gen_measErr {T : ℕ} (t : Fin T) :
    measErr (hookW3gen T) t = 0 := by
  funext c
  show (if t.val * 20 + 9 + c.val = 0 ∨ t.val * 20 + 9 + c.val = 1 ∨
      t.val * 20 + 9 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3gen_ancErr {T : ℕ} (t : Fin T) :
    ancErr (hookW3gen T) t = 0 := by
  funext c
  show (if t.val * 20 + 18 + c.val = 0 ∨ t.val * 20 + 18 + c.val = 1 ∨
      t.val * 20 + 18 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

/-- `inKerB` 报真则矩阵乘向量为零（`readout` 一侧用的逆向桥）。 -/
private lemma mulVec_eq_zero_of_inKerB {k : ℕ} (M : Matrix (Fin k) (Fin 9) (ZMod 2))
    {x : Vec 9} (h : inKerB M x = true) : M *ᵥ x = 0 := by
  funext i
  have hrows : ∀ i, (M i) ⬝ᵥ x = 0 := by
    have hker := (inKerB_iff M x).mp h
    rwa [mem_ker_iff_dotProd_rows_eq_zero] at hker
  simpa [Matrix.mulVec] using hrows i

/-- **空间型逃逸对一切轮数存在**：探测器全零、每轮读出都翻转、重量恰为 $3$。 -/
theorem hookW3gen_witness {T : ℕ} (h : 0 < T) :
    bsDetectorsOK (hookW3gen T) ∧ bsLogicalFault (hookW3gen T) ∧
      hammingNorm (hookW3gen T) = 3 := by
  have hσ : ∀ t : Fin T, bsSyndrome (hookW3gen T) t = 0 := by
    intro t
    rw [bsSyndrome, hookW3gen_cumErr h t, hookW3gen_measErr, hookW3gen_ancErr, add_zero,
      add_zero]
    exact mulVec_eq_zero_of_inKerB bsStabChecks bsSingleRound_witness.1
  have hread : ∀ t : Fin T, bsReadout (hookW3gen T) t = 1 := by
    intro t
    rw [bsReadout, hookW3gen_cumErr h t, hookW3gen_measErr, add_zero]
    exact bsSingleRound_witness.2.1
  refine ⟨⟨fun t _ => hσ t, fun t u _ => by rw [hσ t, hσ u]⟩, ?_, ?_⟩
  · have hfil : (Finset.univ.filter (fun t : Fin T => bsReadout (hookW3gen T) t = 1))
        = Finset.univ :=
      Finset.filter_eq_self.mpr (fun t _ => hread t)
    rw [bsLogicalFault, hfil, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [← weight_eq_hammingNorm]
    have hsupp : support (hookW3gen T) = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
      ext j
      rw [mem_support]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2
      · have hv : hookW3gen T j = 1 := by simp [hookW3gen, hc]
        rw [hv]
        constructor
        · intro _
          rcases hc with h0 | h1 | h2
          · left; exact Fin.ext h0
          · right; left; exact Fin.ext h1
          · right; right; exact Fin.ext h2
        · intro _
          exact one_ne_zero
      · have hv : hookW3gen T j = 0 := by simp [hookW3gen, hc]
        rw [hv]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hmem
          rcases hmem with h0 | h1 | h2
          · exact absurd (Or.inl (congrArg Fin.val h0)) hc
          · exact absurd (Or.inr (Or.inl (congrArg Fin.val h1))) hc
          · exact absurd (Or.inr (Or.inr (congrArg Fin.val h2))) hc
    rw [hsupp]
    simp

/-- **万有恢复的完整形态**：对一切 $T\ge2$，全协议的故障距离恰为 $3=d$——
重量 $\le2$ 的逃逸不存在（万有定理），重量 $3$ 的空间型逃逸永远存在（万有见证）。 -/
theorem bsHook_distance_eq_three_universal {T : ℕ} (hT : 2 ≤ T) :
    hookCand T 2 = [] ∧
      ∃ f : Vec (T * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3 := by
  have hpos : 0 < T := by omega
  have hw := hookW3gen_witness hpos
  exact ⟨bsHook_no_light_universal hT, hookW3gen T, hw.1, hw.2.1, hw.2.2⟩


/-! ## 八、C4 的协议层价格：重复一条校验行，距离不降反升

$\S$七 之外还挂着一条边界：C4 的零价定理是**码层**的（核与行空间不变），
把一条重复的校验抄进**协议**里对时空距离有什么影响，此前不在断言之列。本节补上
一个方向的一般定理与一个实例读数：

* **一般方向（$\S$八.2）**：把第 $0$ 条校验行复制一遍（三条校验、每轮 $21$ 个槽位），
  **任何**重量限定的逃逸都不增——原型里没有的逃逸，复制版里也没有。机制是
  **投影映射**：丢掉第三个辅助槽位，前两类错误与读出逐点不变，探测器条件
  是子集（原型只查前两条校验的 syndrome），重量只降不升。
* **实例读数（$\S$八.3）**：单轮时距离从 $2$ **升**到 $3$——hook 那对"数据错误 +
  辅助比特错误"现在必须把两条相同校验都瞒过去，得付两份辅助比特错误。
  两轮起的距离仍是 $3$（一般定理给下界，空间型逃逸给上界）。

合起来：**重复的校验行在协议层同样免费，甚至更稳**——这把 $\S$五 那句
"对码的价格为零"补齐成"对码与对协议都不亏"。 -/

/-- **复制版校验**：第 $0$ 条 X 型稳定子抄一遍（$3\times9$）。 -/
def dupChecks : Matrix (Fin 3) (Fin 9) (ZMod 2) := Matrix.of ![bstSX, bsCol12, bstSX]

/-- 复制版模型的每轮槽位数：$9$ 数据 + $9$ 测量 + $3$ 辅助比特。 -/
def dupDataErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 21 + i.val, by have := i.isLt; have := t.isLt; omega⟩

def dupMeasErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 21 + 9 + i.val, by have := i.isLt; have := t.isLt; omega⟩

def dupAncErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 3 :=
  fun c => f ⟨t.val * 21 + 18 + c.val, by have := c.isLt; have := t.isLt; omega⟩

def dupCumErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 9 :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val ≤ t.val), dupDataErr f s

def dupSyndrome {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 3 :=
  dupChecks *ᵥ (dupCumErr f t + dupMeasErr f t) + dupAncErr f t

abbrev dupDetectorsOK {T : ℕ} (f : Vec (T * 21)) : Prop :=
  (∀ t : Fin T, t.val = 0 → dupSyndrome f t = 0) ∧
    (∀ t u : Fin T, u.val = t.val + 1 → dupSyndrome f t = dupSyndrome f u)

def dupReadout {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : ZMod 2 :=
  bstXW ⬝ᵥ (dupCumErr f t + dupMeasErr f t)

abbrev dupLogicalFault {T : ℕ} (f : Vec (T * 21)) : Prop :=
  T < 2 * (Finset.univ.filter (fun t : Fin T => dupReadout f t = 1)).card

def hookCandDup (T s : ℕ) : List (Vec (T * 21)) :=
  (lightVecs (T * 21) s).filter
    (fun f => decide (dupDetectorsOK f ∧ dupLogicalFault f))

/-! ### 投影映射：丢掉第三个辅助槽位 -/

/-- **投影**：把每轮第 $0$..$19$ 个槽位的值原样搬回 $20$ 槽模型（第 $20$ 槽被丢弃）。
槽位号 $j=t\cdot20+k$（$k<20$）映到 $t\cdot21+k$——同一轮、同一偏移。 -/
def dupDrop {T : ℕ} (f : Vec (T * 21)) : Vec (T * 20) :=
  fun j => f ⟨j.val / 20 * 21 + j.val % 20, by have := j.isLt; omega⟩

private lemma dupDrop_dataErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    dataErr (dupDrop f) t = dupDataErr f t := by
  funext i
  have hi := i.isLt
  have ht := t.isLt
  show f ⟨(t.val * 20 + i.val) / 20 * 21 + (t.val * 20 + i.val) % 20, by omega⟩
    = f ⟨t.val * 21 + i.val, by omega⟩
  have hval : (t.val * 20 + i.val) / 20 * 21 + (t.val * 20 + i.val) % 20
    = t.val * 21 + i.val := by omega
  exact congrArg f (Fin.ext hval)

private lemma dupDrop_measErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    measErr (dupDrop f) t = dupMeasErr f t := by
  funext c
  have hc := c.isLt
  have ht := t.isLt
  show f ⟨((t.val * 20) + 9 + c.val) / 20 * 21 + ((t.val * 20) + 9 + c.val) % 20, by omega⟩
    = f ⟨t.val * 21 + 9 + c.val, by omega⟩
  have hval : ((t.val * 20) + 9 + c.val) / 20 * 21 + ((t.val * 20) + 9 + c.val) % 20
    = t.val * 21 + 9 + c.val := by omega
  exact congrArg f (Fin.ext hval)

private lemma dupDrop_ancErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) (c : Fin 2) :
    ancErr (dupDrop f) t c = dupAncErr f t ⟨c.val, by omega⟩ := by
  have hc := c.isLt
  have ht := t.isLt
  show f ⟨((t.val * 20) + 18 + c.val) / 20 * 21 + ((t.val * 20) + 18 + c.val) % 20, by omega⟩
    = f ⟨t.val * 21 + 18 + c.val, by omega⟩
  have hval : ((t.val * 20) + 18 + c.val) / 20 * 21 + ((t.val * 20) + 18 + c.val) % 20
    = t.val * 21 + 18 + c.val := by omega
  exact congrArg f (Fin.ext hval)

private lemma dupDrop_cumErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    cumErr (dupDrop f) t = dupCumErr f t := by
  rw [cumErr, dupCumErr]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dupDrop_dataErr]

/-- **读出不变**：投影不动数据与测量槽位，读出只看它们。 -/
private lemma dupDrop_readout {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    bsReadout (dupDrop f) t = dupReadout f t := by
  show bstXW ⬝ᵥ (cumErr (dupDrop f) t + measErr (dupDrop f) t)
    = bstXW ⬝ᵥ (dupCumErr f t + dupMeasErr f t)
  rw [dupDrop_cumErr, dupDrop_measErr]

/-- **重量只降不升**：投影丢掉一个槽位。 -/
private lemma dupDrop_weight {T : ℕ} (f : Vec (T * 21)) :
    hammingNorm (dupDrop f) ≤ hammingNorm f := by
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm]
  refine Finset.card_le_card_of_injOn
    (f := fun j : Fin (T * 20) => ⟨j.val / 20 * 21 + j.val % 20, by
      have := j.isLt; omega⟩) ?_ ?_
  · intro j hj
    refine Finset.mem_coe.mpr (mem_support.mpr ?_)
    have hv : dupDrop f j ≠ 0 := mem_support.mp (Finset.mem_coe.mp hj)
    exact hv
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    exact Fin.val_injective (by
      have ha := a.isLt
      have hb := b.isLt
      have hae := Nat.div_add_mod (a.val) 20
      have hbe := Nat.div_add_mod (b.val) 20
      omega)

/-- **前两条校验的 syndrome 逐分量相同**（复制行在第 $2$ 位，投影不读它）。 -/
private lemma dupDrop_syndrome {T : ℕ} (f : Vec (T * 21)) (t : Fin T) (c : Fin 2) :
    bsSyndrome (dupDrop f) t c = dupSyndrome f t ⟨c.val, by omega⟩ := by
  show bsStabChecks c ⬝ᵥ (cumErr (dupDrop f) t + measErr (dupDrop f) t)
      + ancErr (dupDrop f) t c
    = dupChecks ⟨c.val, by omega⟩ ⬝ᵥ (dupCumErr f t + dupMeasErr f t)
      + dupAncErr f t ⟨c.val, by omega⟩
  rw [dupDrop_cumErr, dupDrop_measErr, dupDrop_ancErr]
  fin_cases c <;> rfl

/-- **探测器条件是子集**：原型只查前两条校验，复制版的条件蕴含原型的。 -/
private lemma dupDrop_detectors {T : ℕ} {f : Vec (T * 21)} (h : dupDetectorsOK f) :
    bsDetectorsOK (dupDrop f) := by
  obtain ⟨hb, hs⟩ := h
  constructor
  · intro t ht
    funext c
    have h0 := hb t ht
    rw [dupDrop_syndrome f t c]
    exact congrFun h0 _
  · intro t u htu
    funext c
    have hcmp := hs t u htu
    have hc := congrFun hcmp (⟨c.val, by omega⟩ : Fin 3)
    simp only [dupDrop_syndrome f t c, dupDrop_syndrome f u c]
    exact hc

/-- **逻辑翻转不变**：读出逐轮相同，多数票相同。 -/
private lemma dupDrop_logical {T : ℕ} {f : Vec (T * 21)} (h : dupLogicalFault f) :
    bsLogicalFault (dupDrop f) := by
  have hfil : (Finset.univ.filter (fun t : Fin T => bsReadout (dupDrop f) t = 1))
      = Finset.univ.filter (fun t : Fin T => dupReadout f t = 1) := by
    refine Finset.filter_congr fun t _ => ?_
    rw [dupDrop_readout]
  rw [bsLogicalFault, hfil]
  exact h

/-- **C4 的协议层价格（一般方向）**：原型里没有的重量限定逃逸，复制版里也没有
——重复一条校验行**不降低**协议的故障距离。 -/
theorem hookCandDup_no_light_of {T s : ℕ} (h : hookCand T s = []) :
    hookCandDup T s = [] := by
  refine (List.filter_eq_nil_iff).mpr fun f hf hp => ?_
  have hw20 : hammingNorm (dupDrop f) ≤ s :=
    le_trans (dupDrop_weight f) (by
      have hw := wt_le_of_mem_lightVecs (T * 21) s f hf
      rwa [wtRec_eq_hammingNorm] at hw)
  have hmem : dupDrop f ∈ hookCand T s := by
    refine (List.mem_filter).mpr ⟨mem_lightVecs (T * 20) s (dupDrop f) ?_, ?_⟩
    · rw [wtRec_eq_hammingNorm]
      exact hw20
    · simp only [decide_eq_true_eq]
      exact ⟨dupDrop_detectors (of_decide_eq_true hp).1,
             dupDrop_logical (of_decide_eq_true hp).2⟩
  rw [h] at hmem
  exact absurd hmem (by simp)

/-! ### 实例读数 -/

/-- **复制版单轮的 hook 见证**：数据错误（位置 $0$）配**两份**辅助比特错误
（位置 $18$ 与 $20$——原行与复制行各一）。 -/
def dupW1 : Vec (1 * 21) :=
  fun j => if j.val = 0 ∨ j.val = 18 ∨ j.val = 20 then 1 else 0

/-- 见证三事实：探测器全零、逻辑翻转、重量恰为 $3$。 -/
theorem dupHook_T1_witness :
    dupDetectorsOK dupW1 ∧ dupLogicalFault dupW1 ∧ hammingNorm dupW1 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **$T=1$：复制版没有重量 $\le2$ 的逃逸**——hook 得同时瞒过两条相同的校验。 -/
theorem hookCandDup_T1_no_light_two : hookCandDup 1 2 = [] := by decide

/-- **$T=1$ 的复制版距离恰为 $3$**（高于原型的 $2$）：重复的校验行把 hook 的价格
从一份辅助比特错误抬到两份，单轮距离回到码距。 -/
theorem hookCandDup_T1_distance_eq_three :
    hookCandDup 1 2 = [] ∧
      ∃ f : Vec (1 * 21), dupDetectorsOK f ∧ dupLogicalFault f ∧ hammingNorm f = 3 :=
  ⟨hookCandDup_T1_no_light_two, dupW1, dupHook_T1_witness.1, dupHook_T1_witness.2.1,
    dupHook_T1_witness.2.2⟩

/-- **空间型逃逸（复制版，对一切轮数）**：与原型同一模式——数据槽位 $0,1,2$。 -/
def hookW3Dup (T : ℕ) : Vec (T * 21) :=
  fun j => if j.val = 0 ∨ j.val = 1 ∨ j.val = 2 then 1 else 0

private theorem bstZW_apply' : ∀ i : Fin 9,
    bstZW i = if i.val = 0 ∨ i.val = 1 ∨ i.val = 2 then (1 : ZMod 2) else 0 := by decide

private lemma hookW3Dup_dataErr_zero {T : ℕ} {s : Fin T} (hs : s.val ≠ 0) :
    dupDataErr (hookW3Dup T) s = 0 := by
  funext i
  show (if s.val * 21 + i.val = 0 ∨ s.val * 21 + i.val = 1 ∨ s.val * 21 + i.val = 2
      then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3Dup_dataErr_self {T : ℕ} (h : 0 < T) :
    dupDataErr (hookW3Dup T) ⟨0, h⟩ = bstZW := by
  funext i
  show (if (0 : ℕ) * 21 + i.val = 0 ∨ 0 * 21 + i.val = 1 ∨ 0 * 21 + i.val = 2
      then (1 : ZMod 2) else 0) = bstZW i
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [bstZW_apply']

private lemma hookW3Dup_cumErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    dupCumErr (hookW3Dup T) t = bstZW := by
  rw [dupCumErr, Finset.sum_filter]
  have hsingle : ∑ s ∈ Finset.univ, (if s.val ≤ t.val then dupDataErr (hookW3Dup T) s else 0)
      = dupDataErr (hookW3Dup T) ⟨0, h⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin T)))
      (f := fun s : Fin T => if s.val ≤ t.val then dupDataErr (hookW3Dup T) s else 0)
      ⟨0, h⟩ ?_ ?_
    · intro b _ hb
      by_cases hle : b.val ≤ t.val
      · rw [ite_eq_left hle]
        exact hookW3Dup_dataErr_zero (fun hz => hb (Fin.ext hz))
      · rw [ite_eq_right hle]
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, h⟩ : Fin T)) hnot
  rw [hsingle]
  exact hookW3Dup_dataErr_self h

private lemma hookW3Dup_measErr {T : ℕ} (t : Fin T) :
    dupMeasErr (hookW3Dup T) t = 0 := by
  funext c
  show (if t.val * 21 + 9 + c.val = 0 ∨ t.val * 21 + 9 + c.val = 1 ∨
      t.val * 21 + 9 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3Dup_ancErr {T : ℕ} (t : Fin T) :
    dupAncErr (hookW3Dup T) t = 0 := by
  funext c
  show (if t.val * 21 + 18 + c.val = 0 ∨ t.val * 21 + 18 + c.val = 1 ∨
      t.val * 21 + 18 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

/-- **复制版的空间型逃逸对一切轮数存在**（与原型同模式：syndrome 全零、逐轮翻转、
重量 $3$）。 -/
theorem hookW3Dup_witness {T : ℕ} (h : 0 < T) :
    dupDetectorsOK (hookW3Dup T) ∧ dupLogicalFault (hookW3Dup T) ∧
      hammingNorm (hookW3Dup T) = 3 := by
  have hker : dupChecks *ᵥ bstZW = 0 := by decide
  have hσ : ∀ t : Fin T, dupSyndrome (hookW3Dup T) t = 0 := by
    intro t
    rw [dupSyndrome, hookW3Dup_cumErr h t, hookW3Dup_measErr, hookW3Dup_ancErr, add_zero,
      add_zero]
    exact hker
  have hread : ∀ t : Fin T, dupReadout (hookW3Dup T) t = 1 := by
    intro t
    rw [dupReadout, hookW3Dup_cumErr h t, hookW3Dup_measErr, add_zero]
    exact bsSingleRound_witness.2.1
  refine ⟨⟨fun t _ => hσ t, fun t u _ => by rw [hσ t, hσ u]⟩, ?_, ?_⟩
  · have hfil : (Finset.univ.filter (fun t : Fin T => dupReadout (hookW3Dup T) t = 1))
        = Finset.univ :=
      Finset.filter_eq_self.mpr (fun t _ => hread t)
    rw [dupLogicalFault, hfil, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [← weight_eq_hammingNorm]
    have hsupp : support (hookW3Dup T) = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
      ext j
      rw [mem_support]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2
      · have hv : hookW3Dup T j = 1 := by simp [hookW3Dup, hc]
        rw [hv]
        constructor
        · intro _
          rcases hc with h0 | h1 | h2
          · left; exact Fin.ext h0
          · right; left; exact Fin.ext h1
          · right; right; exact Fin.ext h2
        · intro _
          exact one_ne_zero
      · have hv : hookW3Dup T j = 0 := by simp [hookW3Dup, hc]
        rw [hv]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hmem
          rcases hmem with h0 | h1 | h2
          · exact absurd (Or.inl (congrArg Fin.val h0)) hc
          · exact absurd (Or.inr (Or.inl (congrArg Fin.val h1))) hc
          · exact absurd (Or.inr (Or.inr (congrArg Fin.val h2))) hc
    rw [hsupp]
    simp

/-- **C4 协议层价格的完整裁定**：重复一条校验行，任何重量限定下逃逸不增（一般
定理）；单轮读数从 $2$ 升到 $3$；两轮起距离仍是 $3$。 -/
theorem c4_dup_price_verdict {T : ℕ} (hT : 2 ≤ T) :
    hookCandDup T 2 = [] ∧
      ∃ f : Vec (T * 21), dupDetectorsOK f ∧ dupLogicalFault f ∧ hammingNorm f = 3 := by
  have hpos : 0 < T := by omega
  have hw := hookW3Dup_witness hpos
  exact ⟨hookCandDup_no_light_of (bsHook_no_light_universal hT), hookW3Dup T, hw.1, hw.2.1,
    hw.2.2⟩

/-! ## 九、单轮闭式：T=1 的距离 = min{wt(y)+wt(Hy) : w·y=1}

$\S$二 的 `bsHook_T1_distance_eq_two` 是逐项 `decide` 的读数。这一节把它升成
**闭式**——单轮的全协议距离由一个只依赖单轮数据的量给出：

$$\min\{\,\mathrm{wt}(y)+\mathrm{wt}(Hy)\;:\;w\cdot y=1\,\}.$$

读法：单轮里故障 $(d,\mu,\gamma)$ 不可探测 $\iff \gamma=H(d+\mu)$，读出翻转
$\iff w\cdot(d+\mu)=1$；把 $y:=d+\mu$ 合并后，代价恰是"$y$ 自身的重量 +
用辅助比特错误顶掉 syndrome 的那份重量"。hook 就是 $y=e_0$：数据位一份、
辅助位一份。 -/

/-- **定义桥**：T=1 时三类错误的取值就是对应槽位的值（rfl 级）。 -/
private lemma dataErr_apply (f : Vec (1 * 20)) (i : Fin 9) :
    dataErr f ⟨0, by omega⟩ i = f ⟨0 * 20 + i.val, by have := i.isLt; omega⟩ := rfl

private lemma measErr_apply (f : Vec (1 * 20)) (i : Fin 9) :
    measErr f ⟨0, by omega⟩ i = f ⟨0 * 20 + 9 + i.val, by have := i.isLt; omega⟩ := rfl

private lemma ancErr_apply (f : Vec (1 * 20)) (c : Fin 2) :
    ancErr f ⟨0, by omega⟩ c = f ⟨0 * 20 + 18 + c.val, by have := c.isLt; omega⟩ := rfl

/-- `hammingNorm` 次可加：支撑之并的子集关系。 -/
private lemma hammingNorm_add_le {n : ℕ} (x y : Vec n) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  classical
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm, ← weight_eq_hammingNorm]
  have hsub : support (x + y) ⊆ support x ∪ support y := by
    intro i hi
    simp only [support, Finset.mem_filter, Finset.mem_union] at hi ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hv : (x + y) i = x i + y i := rfl
    rw [h1 (Finset.mem_univ i), h2 (Finset.mem_univ i)] at hv
    rw [hv] at hi
    simp at hi
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- T=1 的累计 = 第 0 轮的数据错误（filter 里只剩 $s=0$ 一项）。 -/
private lemma cumErr_T1 (f : Vec (1 * 20)) :
    cumErr f ⟨0, by omega⟩ = dataErr f ⟨0, by omega⟩ := by
  rw [cumErr, Finset.sum_filter]
  have hsingle : ∑ s ∈ Finset.univ, (if s.val ≤ 0 then dataErr f s else 0)
      = dataErr f ⟨0, by omega⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin 1)))
      (f := fun s : Fin 1 => if s.val ≤ 0 then dataErr f s else 0)
      ⟨0, by omega⟩ ?_ ?_
    · intro b _ hb
      have hbl : b.val = 0 := by have := b.isLt; omega
      exact absurd (Fin.ext hbl) hb
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, by omega⟩ : Fin 1)) hnot
  rw [hsingle]

/-- 单轮探测器条件 ⟺ 辅助比特错误恰是 syndrome。 -/
private lemma syndrome_of_T1 {f : Vec (1 * 20)} (h : bsDetectorsOK f) :
    ancErr f ⟨0, by omega⟩ = bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩
      + measErr f ⟨0, by omega⟩) := by
  have h0 := h.1 ⟨0, by omega⟩ rfl
  rw [bsSyndrome, cumErr_T1] at h0
  funext c
  have hc : (bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩)
      + ancErr f ⟨0, by omega⟩) c = 0 := congrFun h0 c
  have hsplit : (bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩
      + measErr f ⟨0, by omega⟩) + ancErr f ⟨0, by omega⟩) c
      = (bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩)) c
        + ancErr f ⟨0, by omega⟩ c := rfl
  rw [hsplit] at hc
  exact ((add_eq_zero_iff_eq _ _).mp hc).symm

/-! ### 重量分解：三个支撑的像互斥地落进故障支撑 -/

/-- 数据槽位的嵌入。 -/
private def slotD (i : Fin 9) : Fin (1 * 20) := ⟨0 * 20 + i.val, by have := i.isLt; omega⟩

/-- 测量槽位的嵌入。 -/
private def slotM (i : Fin 9) : Fin (1 * 20) := ⟨0 * 20 + 9 + i.val, by have := i.isLt; omega⟩

/-- 辅助槽位的嵌入。 -/
private def slotA (c : Fin 2) : Fin (1 * 20) := ⟨0 * 20 + 18 + c.val, by have := c.isLt; omega⟩

/-- 三个支撑像两两互斥：互斥全部由槽位值域的 omega 给出。 -/
private lemma images_disjoint (f : Vec (1 * 20)) :
    Disjoint ((support (dataErr f ⟨0, by omega⟩)).image slotD)
      ((support (measErr f ⟨0, by omega⟩)).image slotM
        ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA)
    ∧ Disjoint ((support (measErr f ⟨0, by omega⟩)).image slotM)
      ((support (ancErr f ⟨0, by omega⟩)).image slotA) := by
  constructor
  · refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
    · refine Finset.disjoint_right.mpr fun a ha hmem => ?_
      obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hmem
      have hval : (0 : ℕ) * 20 + i.val = 0 * 20 + 9 + j.val :=
        congrArg Fin.val (hia.trans hja.symm)
      omega
    · refine Finset.disjoint_right.mpr fun a ha hmem => ?_
      obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hmem
      have hval : (0 : ℕ) * 20 + i.val = 0 * 20 + 18 + c.val :=
        congrArg Fin.val (hia.trans hca.symm)
      have := i.isLt
      have := c.isLt
      omega
  · refine Finset.disjoint_right.mpr fun a ha hmem => ?_
    obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hmem
    have hval : (0 : ℕ) * 20 + 9 + i.val = 0 * 20 + 18 + c.val :=
      congrArg Fin.val (hia.trans hca.symm)
    have := i.isLt
    have := c.isLt
    omega

private lemma slotD_inj : Function.Injective slotD := fun a b h =>
  Fin.val_injective (by
    have hval : (0 : ℕ) * 20 + a.val = 0 * 20 + b.val := congrArg Fin.val h
    omega)

private lemma slotM_inj : Function.Injective slotM := fun a b h =>
  Fin.val_injective (by
    have hval : (0 : ℕ) * 20 + 9 + a.val = 0 * 20 + 9 + b.val := congrArg Fin.val h
    omega)

private lemma slotA_inj : Function.Injective slotA := fun a b h =>
  Fin.val_injective (by
    have hval : (0 : ℕ) * 20 + 18 + a.val = 0 * 20 + 18 + b.val := congrArg Fin.val h
    omega)

/-- **T=1 的重量分解（≤ 方向）**：三类错误的支撑经槽位嵌入互斥地落进故障支撑。 -/
private lemma weight_one_round_le (f : Vec (1 * 20)) :
    hammingNorm (dataErr f ⟨0, by omega⟩) + hammingNorm (measErr f ⟨0, by omega⟩)
      + hammingNorm (ancErr f ⟨0, by omega⟩) ≤ hammingNorm f := by
  classical
  obtain ⟨hout, hin⟩ := images_disjoint f
  have hc1 := Finset.card_union_of_disjoint hout
  have hc2 := Finset.card_union_of_disjoint hin
  have cD : ((support (dataErr f ⟨0, by omega⟩)).image slotD).card
      = (support (dataErr f ⟨0, by omega⟩)).card :=
    Finset.card_image_of_injective _ slotD_inj
  have cM : ((support (measErr f ⟨0, by omega⟩)).image slotM).card
      = (support (measErr f ⟨0, by omega⟩)).card :=
    Finset.card_image_of_injective _ slotM_inj
  have cA : ((support (ancErr f ⟨0, by omega⟩)).image slotA).card
      = (support (ancErr f ⟨0, by omega⟩)).card :=
    Finset.card_image_of_injective _ slotA_inj
  have hkey : ((support (dataErr f ⟨0, by omega⟩)).image slotD
      ∪ ((support (measErr f ⟨0, by omega⟩)).image slotM
        ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA)).card
      = (support (dataErr f ⟨0, by omega⟩)).card
        + ((support (measErr f ⟨0, by omega⟩)).card
          + (support (ancErr f ⟨0, by omega⟩)).card) := by
    rw [hc1, hc2, cD, cM, cA]
  have hsub : ((support (dataErr f ⟨0, by omega⟩)).image slotD
      ∪ ((support (measErr f ⟨0, by omega⟩)).image slotM
        ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA)) ⊆ support f := by
    intro a ha
    have ha' : a ∈ (support (dataErr f ⟨0, by omega⟩)).image slotD
        ∨ a ∈ ((support (measErr f ⟨0, by omega⟩)).image slotM
          ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA) := Finset.mem_union.mp ha
    rcases ha' with h | h
    · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp h
      rw [← hia]
      exact mem_support.mpr ((dataErr_apply f i) ▸ (mem_support.mp hi))
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp h
        rw [← hia]
        exact mem_support.mpr ((measErr_apply f i) ▸ (mem_support.mp hi))
      · obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp h
        rw [← hca]
        exact mem_support.mpr ((ancErr_apply f c) ▸ (mem_support.mp hc))
  rw [← weight_eq_hammingNorm (dataErr f ⟨0, by omega⟩),
    ← weight_eq_hammingNorm (measErr f ⟨0, by omega⟩),
    ← weight_eq_hammingNorm (ancErr f ⟨0, by omega⟩), ← weight_eq_hammingNorm f]
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [hkey]
  omega


/-! ### 闭式 -/

/-- **单轮读出翻转的提取**：T=1 的多数票只有一个轮次可翻。 -/
private lemma logical_T1 {f : Vec (1 * 20)} (h : bsLogicalFault f) :
    bsReadout f ⟨0, by omega⟩ = 1 := by
  rw [bsLogicalFault] at h
  have hle : (Finset.univ.filter (fun t : Fin 1 => bsReadout f t = 1)).card
      ≤ (Finset.univ : Finset (Fin 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  have h1 : (Finset.univ.filter (fun t : Fin 1 => bsReadout f t = 1)).card = 1 := by omega
  have hpos : 0 < (Finset.univ.filter (fun t : Fin 1 => bsReadout f t = 1)).card := by
    rw [h1]; exact zero_lt_one
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  have hte : t = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := t.isLt; omega)
  have := (Finset.mem_filter.mp ht).2
  rw [hte] at this
  exact this

/-- **下界方向**：任何单轮逃逸给出一个更便宜的 $y$。 -/
private lemma formula_lower {f : Vec (1 * 20)} {s : ℕ} (hdet : bsDetectorsOK f)
    (_hlog : bsLogicalFault f) (hw : hammingNorm f ≤ s) (y : Vec 9)
    (hy : dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩ = y) :
    hammingNorm y + hammingNorm (bsStabChecks *ᵥ y) ≤ s := by
  have h1 : hammingNorm (dataErr f ⟨0, by omega⟩) + hammingNorm (measErr f ⟨0, by omega⟩)
      ≥ hammingNorm (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩) :=
    hammingNorm_add_le _ _
  have h2 := weight_one_round_le f
  have h3 : ancErr f ⟨0, by omega⟩ = bsStabChecks *ᵥ y := by
    rw [syndrome_of_T1 hdet, ← hy]
  rw [h3] at h2
  rw [hy] at h1
  omega

/-- **单轮见证**：把 $y$ 放进数据槽、syndrome 放进辅助槽。 -/
def t1Wit (y : Vec 9) : Vec (1 * 20) :=
  fun j => if h : j.val < 9 then y ⟨j.val, h⟩
    else if h2 : j.val < 18 then 0
    else (bsStabChecks *ᵥ y) ⟨j.val - 18, by omega⟩

private lemma t1Wit_lt9 (y : Vec 9) (j : Fin (1 * 20)) (h : j.val < 9) :
    t1Wit y j = y ⟨j.val, by omega⟩ := by
  show dite (j.val < 9) _ _ = _
  rw [dite_eq_left h]

private lemma t1Wit_mid (y : Vec 9) (j : Fin (1 * 20)) (h1 : ¬ j.val < 9) (h2 : j.val < 18) :
    t1Wit y j = 0 := by
  show dite (j.val < 9) _ _ = _
  rw [dite_eq_right h1, dite_eq_left h2]

private lemma t1Wit_ge18 (y : Vec 9) (j : Fin (1 * 20)) (h1 : ¬ j.val < 9) (h2 : ¬ j.val < 18) :
    t1Wit y j = (bsStabChecks *ᵥ y) ⟨j.val - 18, by omega⟩ := by
  show dite (j.val < 9) _ _ = _
  rw [dite_eq_right h1, dite_eq_right h2]

private lemma t1Wit_dataErr (y : Vec 9) : dataErr (t1Wit y) ⟨0, by omega⟩ = y := by
  funext i
  rw [dataErr_apply]
  show (t1Wit y) ⟨0 * 20 + i.val, by have := i.isLt; omega⟩ = y i
  simp only [t1Wit]
  have hi : 0 * 20 + i.val < 9 := by have := i.isLt; omega
  rw [dite_eq_left hi]
  have hidx : (⟨0 * 20 + i.val, hi⟩ : Fin 9) = i := Fin.ext (by
    have hv1 : (⟨0 * 20 + i.val, hi⟩ : Fin 9).val = 0 * 20 + i.val := rfl
    omega)
  rw [hidx]

private lemma t1Wit_measErr (y : Vec 9) : measErr (t1Wit y) ⟨0, by omega⟩ = 0 := by
  funext i
  rw [measErr_apply]
  show (t1Wit y) ⟨0 * 20 + 9 + i.val, by have := i.isLt; omega⟩ = 0
  simp only [t1Wit]
  have hi : ¬ (0 * 20 + 9 + i.val < 9) := by omega
  have hi2 : 0 * 20 + 9 + i.val < 18 := by have := i.isLt; omega
  rw [dite_eq_right hi, dite_eq_left hi2]

private lemma t1Wit_ancErr (y : Vec 9) :
    ancErr (t1Wit y) ⟨0, by omega⟩ = bsStabChecks *ᵥ y := by
  funext c
  rw [ancErr_apply]
  show (t1Wit y) ⟨0 * 20 + 18 + c.val, by have := c.isLt; omega⟩
    = (bsStabChecks *ᵥ y) c
  simp only [t1Wit]
  have hi : ¬ (0 * 20 + 18 + c.val < 9) := by omega
  have hi2 : ¬ (0 * 20 + 18 + c.val < 18) := by omega
  rw [dite_eq_right hi, dite_eq_right hi2]
  have hidx : (⟨0 * 20 + 18 + c.val - 18, by omega⟩ : Fin 2) = c :=
    Fin.ext (by
      have hv1 : (⟨0 * 20 + 18 + c.val - 18, by omega⟩ : Fin 2).val
          = 0 * 20 + 18 + c.val - 18 := rfl
      omega)
  rw [hidx]

/-- **上界方向**：见证的重量不超过 $\mathrm{wt}(y)+\mathrm{wt}(Hy)$
（数据槽与辅助槽的像覆盖支撑）。 -/
private lemma t1Wit_weight (y : Vec 9) :
    hammingNorm (t1Wit y)
      ≤ hammingNorm y + hammingNorm (bsStabChecks *ᵥ y) := by
  classical
  rw [← weight_eq_hammingNorm (t1Wit y)]
  have hsub : support (t1Wit y)
      ⊆ (support y).image slotD ∪ (support (bsStabChecks *ᵥ y)).image slotA := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_image]
    by_cases h9 : j.val < 9
    · left
      have hd : (⟨j.val, by have := j.isLt; omega⟩ : Fin (1 * 20)) = j :=
        Fin.ext (by
          have hv1 : (⟨j.val, by have := j.isLt; omega⟩ : Fin (1 * 20)).val = j.val := rfl
          omega)
      have hv : t1Wit y j = y ⟨j.val, by omega⟩ := t1Wit_lt9 y j h9
      refine ⟨⟨j.val, h9⟩, ?_, ?_⟩
      · rw [mem_support]
        have hv : t1Wit y j = y ⟨j.val, h9⟩ := t1Wit_lt9 y j h9
        have hval := mem_support.mp hj
        rw [hv] at hval
        exact hval
      · exact Fin.ext (by
          have hv1 : (slotD ⟨j.val, h9⟩).val = 0 * 20 + j.val := rfl
          omega)
    · right
      have h18 : ¬ (j.val < 18) := by
        intro hcon
        have hval := mem_support.mp hj
        rw [t1Wit_mid y j h9 hcon] at hval
        exact hval rfl
      obtain ⟨hc, hceq⟩ : ∃ hc : Fin 2,
          hc = ⟨j.val - 18, by have := j.isLt; omega⟩ := ⟨_, rfl⟩
      have hm : hc ∈ support (bsStabChecks *ᵥ y) := by
        rw [mem_support]
        have hv : t1Wit y j = (bsStabChecks *ᵥ y) hc := by
          rw [hceq]
          exact t1Wit_ge18 y j h9 h18
        have hval := mem_support.mp hj
        rw [hv] at hval
        exact hval
      have heq : slotA hc = j := by
        rw [hceq]
        exact Fin.ext (by
          have hv1 : (slotA ⟨j.val - 18, by have := j.isLt; omega⟩).val
              = 0 * 20 + 18 + (j.val - 18) := rfl
          omega)
      exact Finset.mem_image.mpr ⟨hc, hm, heq⟩
  rw [← weight_eq_hammingNorm y, ← weight_eq_hammingNorm (bsStabChecks *ᵥ y)]
  have hd : Disjoint ((support y).image slotD)
      ((support (bsStabChecks *ᵥ y)).image slotA) := by
    refine Finset.disjoint_right.mpr fun a ha hmem => ?_
    obtain ⟨c, _, hca⟩ := Finset.mem_image.mp ha
    obtain ⟨i, _, hia⟩ := Finset.mem_image.mp hmem
    have hval : (0 : ℕ) * 20 + i.val = 0 * 20 + 18 + c.val :=
      congrArg Fin.val (hia.trans hca.symm)
    have := i.isLt
    have := c.isLt
    omega
  have hcard : ((support y).image slotD
      ∪ (support (bsStabChecks *ᵥ y)).image slotA).card
      = (support y).card + (support (bsStabChecks *ᵥ y)).card := by
    rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ slotD_inj,
      Finset.card_image_of_injective _ slotA_inj]
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [hcard]

private lemma t1Wit_detectors (y : Vec 9) : bsDetectorsOK (t1Wit y) := by
  constructor
  · intro t _
    have ht : t = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := t.isLt; omega)
    rw [ht]
    rw [bsSyndrome]
    have hcum : cumErr (t1Wit y) ⟨0, by omega⟩ = y := by
      rw [cumErr_T1, t1Wit_dataErr]
    rw [hcum, t1Wit_measErr, add_zero, t1Wit_ancErr]
    exact add_self _
  · intro t u htu
    have := t.isLt
    have := u.isLt
    omega

private lemma t1Wit_logical {y : Vec 9} (hy : bstXW ⬝ᵥ y = 1) :
    bsLogicalFault (t1Wit y) := by
  have hread : bsReadout (t1Wit y) ⟨0, by omega⟩ = 1 := by
    rw [bsReadout, cumErr_T1, t1Wit_dataErr, t1Wit_measErr, add_zero]
    exact hy
  have hfil : (Finset.univ.filter (fun t : Fin 1 => bsReadout (t1Wit y) t = 1))
      = Finset.univ := by
    refine Finset.filter_eq_self.mpr fun t _ => ?_
    have hte : t = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := t.isLt; omega)
    rw [hte]
    exact hread
  rw [bsLogicalFault, hfil, Finset.card_univ, Fintype.card_fin]
  omega

/-- **单轮闭式**：重量 $\le s$ 的逃逸不存在 $\iff$ 每个翻转读出的 $y$ 都付得起
$\mathrm{wt}(y)+\mathrm{wt}(Hy) > s$。 -/
theorem bsHook_T1_formula (s : ℕ) :
    hookCand 1 s = [] ↔ ∀ y : Vec 9, bstXW ⬝ᵥ y = 1 →
      s < hammingNorm y + hammingNorm (bsStabChecks *ᵥ y) := by
  constructor
  · intro h y hy
    by_contra hcon
    push Not at hcon
    have hmem : t1Wit y ∈ hookCand 1 s := by
      refine (List.mem_filter).mpr ⟨mem_lightVecs _ s _ ?_, ?_⟩
      · rw [wtRec_eq_hammingNorm]
        exact le_trans (t1Wit_weight y) (by omega)
      · simp only [decide_eq_true_eq]
        exact ⟨t1Wit_detectors y, t1Wit_logical hy⟩
    rw [h] at hmem
    exact absurd hmem (by simp)
  · intro h
    refine (List.filter_eq_nil_iff).mpr fun f hf hp => ?_
    simp only [decide_eq_true_eq] at hp
    obtain ⟨hdet, hlog⟩ := hp
    have hwf : hammingNorm f ≤ s := by
      have hwt := wt_le_of_mem_lightVecs (1 * 20) s f hf
      rwa [wtRec_eq_hammingNorm] at hwt
    have hread := logical_T1 hlog
    -- 读出 = w·(cum+μ) = w·y
    have hy : bstXW ⬝ᵥ (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩) = 1 := by
      rw [← cumErr_T1 f]
      rw [bsReadout] at hread
      exact hread
    have := formula_lower hdet hlog hwf _ rfl
    exact absurd (h _ hy) (not_lt.mpr this)

/-- **单轮距离读数（闭式两向）**：下界与 $y=e_0$ 的取等，$\min=2$。 -/
theorem bsHook_T1_min :
    (∀ y : Vec 9, bstXW ⬝ᵥ y = 1 →
      2 ≤ hammingNorm y + hammingNorm (bsStabChecks *ᵥ y))
    ∧ bstXW ⬝ᵥ ((e ⟨0, by norm_num⟩ : Vec 9)) = 1
    ∧ hammingNorm ((e ⟨0, by norm_num⟩ : Vec 9))
      + hammingNorm (bsStabChecks *ᵥ (e ⟨0, by norm_num⟩ : Vec 9)) = 2 := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- **闭式与逐项读数的合账**：单轮故障距离恰为由闭式给出的 $2$。 -/
theorem bsHook_T1_distance_eq_two_formula :
    hookCand 1 1 = [] ∧
      (∀ y : Vec 9, bstXW ⬝ᵥ y = 1 →
        2 ≤ hammingNorm y + hammingNorm (bsStabChecks *ᵥ y)) ∧
      ∃ f : Vec (1 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 2 := by
  refine ⟨bsHook_T1_formula 1 |>.mpr (fun y hy => by
      have h2 := bsHook_T1_min.1 y hy
      omega), bsHook_T1_min.1, ?_⟩
  refine ⟨t1Wit (e ⟨0, by norm_num⟩ : Vec 9), t1Wit_detectors _,
    t1Wit_logical bsHook_T1_min.2.1, ?_⟩
  have hle := t1Wit_weight (e ⟨0, by norm_num⟩ : Vec 9)
  have h2 := bsHook_T1_min.2.2
  have hge : 2 ≤ hammingNorm (t1Wit (e ⟨0, by norm_num⟩ : Vec 9)) := by
    have := formula_lower (t1Wit_detectors _) (t1Wit_logical bsHook_T1_min.2.1)
      (le_of_eq rfl) (e ⟨0, by norm_num⟩ : Vec 9)
      (by rw [t1Wit_dataErr, t1Wit_measErr, add_zero])
    omega
  omega
end QECCertificates
