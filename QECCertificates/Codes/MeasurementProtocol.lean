/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.Separation
import QECCertificates.Codes.CaseMatrix

/-!
# 测量协议的表示层（时空故障模型与两分量的时间轴）

`Codes/Separation.lean` 把两个分量写成**抽象参数**（`rounds`、`d`、`η`），
`Codes/Gauging.lean` 把时间轴证成一条**链上**的定理（相邻轮校验 ⟹ 取值全一 ⟹
重量 = 轮数）。两者之间缺一层：**把"一个测量协议"本身写成对象**，
使"轮数"不再是外部参数，而是协议的字段，"时间轴分量"成为从协议算出来的数。

本模块补这一层。它只用三个概念：

## 一、单轮：故障模式与"不可探测的逻辑故障"

一轮测量做完后，哪些比特的**报告结果**错了，就是一个故障模式 $f \in \mathbb F_2^n$。
两个后果各是一行线性泛函：

* **校验**：轮内可用的校验矩阵 $H$（每行是一条稳定子），syndrome 是 $Hf$——
  全零即"没被发现"（`inKerB H f = true`）；
* **逻辑**：逻辑读出值是 $w \cdot f$（$w$ 是逻辑算符的支撑指示向量）——
  等于 $1$ 即"读出的值被翻转了"。

两者合起来就是 `IsUndetectedFault H w f`。**注意这里必须是"逻辑泛函 $=1$"而不是
"$f$ 不在 $H$ 的行空间里"**——两者在别的码上并不等价（本库自己的
`min_weight_ker_not_mem_rowspace` 用的是后者），差别在下面的 Bacon–Shor 实例上
是 $2$ 与 $3$ 的差别。判定用重量限定枚举（`faultCand`，与 `lightCand` 同形），
可靠性同样只依赖覆盖定理 `mem_lightVecs`。

## 二、跨轮：时空故障模式与"读出全同"

把测量重复 $T$ 轮，每轮一个故障模式（`SpacetimeFault T n = Fin T → Vec n`）。
**跨轮校验就是"各轮的逻辑读出值全相同"**：某轮的读出与别轮不一致，本身就是一个
可见的异常（这正是重复测量的用处）。于是时空不可探测逻辑故障 = 每轮都躲过轮内校验
＋各轮读出全同且全为 $1$。

## 三、时间轴律：两分量**相乘**而不是取小

设单轮的不可探测逻辑故障最小重量是 $s$。则 $T$ 轮协议的时空故障距离**恰为** $T \cdot s$：

* **下界**（`le_spacetimeWeight`）：各轮读出全为 $1$ ⟹ 每轮都各自是一个不可探测的
  逻辑翻转 ⟹ 每轮重量 $\ge s$ ⟹ 总重量 $\ge T\cdot s$；
* **可达**（`spacetimeWeight_witness`）：把单轮见证复制到每一轮，即得重量 $T\cdot s$ 的
  时空故障。

**为什么是相乘**：因为"全同"这条跨轮约束把各轮**绑在一起**——只要有一轮读出与别轮
不同就暴露，故要么每轮都翻转（$T$ 份代价），要么一轮都不翻转（无害）。
单轮无校验时 $s=1$（`bare_noLightFault`：逻辑是一串结果的乘积，任何一个报错都翻转它，
一轮之内无从发现），于是协议距离 $=T$——**这正是 C2 的 `d ≤ rounds`**：
`Codes/Separation.lean` 的 `exists_undetectable_of_rounds_lt` 说轮数 $<d$ 时存在更轻的
不可探测算符，本模块把它算成了**精确值**（`separation_C2` 与实例模块的两向夹逼）。
-/

namespace QECCertificates

open scoped BigOperators

variable {n m : ℕ}

/-! ## 一、单轮的故障模式 -/

/-- **不可探测的逻辑故障**（单轮）：故障模式 `f`（哪些比特的报告结果被翻转）
躲过了轮内全部校验（syndrome 为零），却翻转了逻辑读出值。

两个合取项分别是可计算判定 `inKerB` 与可计算泛函 `⬝ᵥ`，故整个谓词可被内核归约。 -/
abbrev IsUndetectedFault {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (w : Vec n)
    (f : Vec n) : Prop :=
  inKerB H f = true ∧ w ⬝ᵥ f = 1

/-- **故障候选集**（重量限定枚举，与 `lightCand` 同形）：重量 $\le d-1$ 的故障模式里，
那些不可探测却翻转逻辑的。 -/
def faultCand {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (w : Vec n) (d : ℕ) :
    List (Vec n) :=
  (lightVecs n (d - 1)).filter (fun f => decide (IsUndetectedFault H w f))

/-- 成员刻画（把 `faultCand` 展开到候选集与谓词）。 -/
theorem mem_faultCand {m : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    {d : ℕ} {f : Vec n} :
    f ∈ faultCand H w d ↔ f ∈ lightVecs n (d - 1) ∧ IsUndetectedFault H w f := by
  rw [faultCand, List.mem_filter, decide_eq_true_eq]

/-- **单轮下界假设**：任何不可探测的逻辑故障，重量至少 `s`。

这是"单轮故障距离 $\ge s$"的可计算形态——它是判定层要证的**假设**，
而 `faultCand` 为空是它的**证书**（`noLightFault_of_faultCand_nil`）。 -/
abbrev NoLightFault {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (w : Vec n) (s : ℕ) :
    Prop :=
  ∀ f : Vec n, IsUndetectedFault H w f → s ≤ hammingNorm f

/-- **证书 ⟹ 假设**：重量限定枚举里没有不可探测的逻辑故障，就给出下界 `d`。

证明与 `lowerHyp_of_lightCand_nil` 同构：反证 → 覆盖（`mem_lightVecs`）→ 放回集合。 -/
theorem noLightFault_of_faultCand_nil {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) {d : ℕ} (h : faultCand H w d = []) : NoLightFault H w d := by
  intro f hf
  by_contra hlt
  have hlt' : hammingNorm f < d := not_le.mp hlt
  have hcov : f ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) f ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : f ∈ faultCand H w d := mem_faultCand.mpr ⟨hcov, hf⟩
  rw [h] at hmem
  simp at hmem

/-- **无轮内校验的横向测量：单轮故障距离 = 1**。

逻辑读出一串结果的乘积时，三个结果里任何一个报错就翻转它，而一轮之内**没有任何校验**
可以发现这件事——故故障模式只要重量 $1$ 就够。这是"横向测量必须靠时间轴保护"的
表示层内容，也是实例里 C2 从"充分"变成"恰好"的原因。 -/
theorem bare_noLightFault (w : Vec n) :
    NoLightFault (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) w 1 := by
  intro f hf
  have hne : f ≠ 0 := by
    intro h0
    have hd : w ⬝ᵥ (0 : Vec n) = 0 := by simp [dotProduct]
    rw [h0] at hf
    exact one_ne_zero (hf.2.symm.trans hd)
  have hpos : 0 < hammingNorm f :=
    Nat.pos_of_ne_zero fun hz => hne (hammingNorm_eq_zero.mp hz)
  omega

/-! ## 二、跨轮的时空故障模式 -/

/-- **时空故障模式**：每轮一个故障向量（第 `t` 轮的故障模式是 `f t`）。 -/
abbrev SpacetimeFault (T n : ℕ) := Fin T → Vec n

/-- **时空故障的重量** = 各轮重量之和（每一处报告错误计一次）。 -/
def spacetimeWeight {T n : ℕ} (f : SpacetimeFault T n) : ℕ := ∑ t, hammingNorm (f t)

/-- **读出全同**：各轮的逻辑读出值取同一个值——跨轮比较看不出任何异常。 -/
abbrev AgreeOn {T n : ℕ} (w : Vec n) (f : SpacetimeFault T n) : Prop :=
  ∃ b : ZMod 2, ∀ t, w ⬝ᵥ f t = b

/-- **时空不可探测逻辑故障**：每轮都躲过轮内校验，各轮读出全同，且全为 `1`
（逻辑读出被翻转）。 -/
abbrev IsUndetectedSpacetimeFault {T n m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) (f : SpacetimeFault T n) : Prop :=
  (∀ t, inKerB H (f t) = true) ∧ (∀ t, w ⬝ᵥ f t = 1)

/-! ## 三、时间轴律：距离 = 轮数 × 单轮距离 -/

/-- **时间轴律（下界）**：单轮距离 $\ge s$ ⟹ $T$ 轮协议的时空故障重量 $\ge T\cdot s$。

证明只用一件事：各轮读出全为 `1`，故**每一轮自己**就是一个单轮的不可探测逻辑故障，
于是每一轮的重量都 $\ge s$，加起来即 $T\cdot s$——跨轮约束"全同"没有别的出路。 -/
theorem le_spacetimeWeight {T : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    {s : ℕ} (h : NoLightFault H w s) {f : SpacetimeFault T n}
    (hker : ∀ t, inKerB H (f t) = true) (hlog : ∀ t, w ⬝ᵥ f t = 1) :
    T * s ≤ spacetimeWeight f := by
  have hstep : ∀ t : Fin T, s ≤ hammingNorm (f t) := fun t => h (f t) ⟨hker t, hlog t⟩
  have hsum : (∑ _t : Fin T, s) = T * s := by
    simp [Finset.sum_const, Finset.card_univ]
  calc T * s = ∑ _t : Fin T, s := hsum.symm
    _ ≤ ∑ t : Fin T, hammingNorm (f t) := Finset.sum_le_sum fun t _ => hstep t
    _ = spacetimeWeight f := rfl

/-- **时间轴律（可达）**：把单轮见证复制到每一轮，即得重量恰为 $T\cdot s$ 的时空故障。

于是"时空故障距离 $=T\cdot s$"两向夹逼齐了——下界见 `le_spacetimeWeight`。 -/
theorem spacetimeWeight_witness {T : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    {s : ℕ} (f₀ : Vec n) (hker : inKerB H f₀ = true) (hlog : w ⬝ᵥ f₀ = 1)
    (hw : hammingNorm f₀ = s) :
    ∃ f : SpacetimeFault T n, IsUndetectedSpacetimeFault H w f ∧
      spacetimeWeight f = T * s := by
  have hfault : IsUndetectedSpacetimeFault H w (fun _ : Fin T => f₀) :=
    ⟨fun _ => hker, fun _ => hlog⟩
  have hwt : spacetimeWeight (fun _ : Fin T => f₀) = T * s := by
    have hterm : ∀ t : Fin T, hammingNorm ((fun _ : Fin T => f₀) t) = s := fun _ => hw
    simp only [spacetimeWeight]
    rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const, Finset.card_univ]
    simp
  exact ⟨fun _ => f₀, hfault, hwt⟩

/-- **C2 的落点**：要"时空故障距离 $\ge d$"成立，充分条件是 $d\le T\cdot s$。

对无轮内校验的横向测量（`s = 1`）这就是原文的 $d\le T$，即轮数不少于码距——
实例模块把这条在 Bacon–Shor 上算成**精确值**并给出锐性。 -/
theorem separation_C2 {T s d : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    (hds : d ≤ T * s) (h : NoLightFault H w s) {f : SpacetimeFault T n}
    (hker : ∀ t, inKerB H (f t) = true) (hlog : ∀ t, w ⬝ᵥ f t = 1) :
    d ≤ spacetimeWeight f :=
  le_trans hds (le_spacetimeWeight h hker hlog)

end QECCertificates
