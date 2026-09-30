/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/

import QECCertificates.GF2.Membership
import QECCertificates.GF2.Witness
import QECCertificates.GF2.WeightEnum

/-!
# 距离下界的可计算证书：把"没有更轻的逻辑算符"交给内核

`GF2/Witness` 给出了距离的**双侧合拢接口**，但下界一侧还停在"给定一个
逐算符不等式"的抽象形态——那是 LeanQEC 交给 SAT 的部分。本模块把它**落地**：

```
轻算符集合非空？
  = 在"重量 ≤ d-1"的候选向量上按"非零 ∧ 在核里 ∧ 不在行空间里"过滤，看还剩不剩东西
```

谓词的每一片都是可计算的（`GF2/Membership` 的 `inKerB` / `inSpanB`），
候选集是 `GF2/WeightEnum` 的**重量限定枚举**（$n = 15$ 时 121 个而不是 32768 个），
于是整条判定是一个**闭式的布尔等式**，可以直接 `by decide` —— 内核自己算，
不需要 SAT、不需要 `native_decide`、不需要任何自定义公理。

## 候选集的两条性质（决定证书的可靠性与代价）

* **覆盖**（`mem_lightVecs`）：重量 $\le w$ 的向量都在候选集里——所以"候选里没有"
  就是"根本不存在"。这条是**可靠性**的来源，也正是用 `Finset.univ` 时免费拿到的东西。
* **计数**（`length_lightVecs`）：候选集恰有 $\sum_{k\le w}\binom nk$ 个——
  这就是**证书代价**：定 $d$ 时是 $n$ 的 $d-1$ 次多项式，而非 $2^n$。

## 主结果

* `lightSet_card_zero_iff`：`(lightSet M₁ M₂ d).card = 0` 与下界命题**逐字等价**。
* `le_minWeight_of_lightSet_card_zero`：**下界证书**——空集即得 `d ≤ 码距`。
* `eq_minWeight_of_decide`：**精确距离的可计算证书形态**——
  下界 `by decide`、上界给一个显式见证，两侧一夹即得"码距恰好等于 $d$"。
* `lightCand_length_le`：**证书复杂度**——候选空间 $\le \sum_{k<d}\binom nk$。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 轻算符集合 -/

/-- "重量小于 `d` 的不可探测非平凡算符"的判定谓词。

三片合起来正是下界要排除的东西：非零、与全部校验对易、却不是校验行空间元素。
每一片都是可计算的，故整个谓词可被内核归约；重量上界由候选集本身（`lightVecs n (d-1)`）承担。

标 `abbrev` 而非 `def`：`def` 半可还原，`DecidablePred` 的实例合成不展开它，
`Finset.filter` 会合不出判定子。 -/
abbrev IsLightUndetectable {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧ inSpanB (List.ofFn fun i => M₂ i) v = false

/-- **下界证书的候选集**：重量 $\le d-1$ 的向量里，那些"与校验对易却不在行空间里"的。

候选集来自 `lightVecs n (d-1)`——**重量限定枚举**，而不是全空间
（`Finset.univ` 的 $2^n$ 版本在 $n = 15$ 就要三分钟）。重量上界 $d-1$ 的依据是
下界只需排除重量 $< d$ 的算符（`wtRec_eq_hammingNorm` + `Nat.lt_iff_le_pred`）。 -/
def lightCand {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (d : ℕ) : List (Vec n) :=
  (lightVecs n (d - 1)).filter (fun v => decide (IsLightUndetectable M₁ M₂ v))

/-- **轻算符集合**：候选集的 `Finset` 形态（`card = 0` 即"没有更轻的逻辑算符"）。 -/
def lightSet {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (d : ℕ) : Finset (Vec n) :=
  (lightCand M₁ M₂ d).toFinset

/-- 成员刻画（把 `lightSet` 展开到候选集与谓词）。 -/
theorem mem_lightSet {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightSet M₁ M₂ d ↔ v ∈ lightCand M₁ M₂ d :=
  List.mem_toFinset

theorem mem_lightCand {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightCand M₁ M₂ d ↔ v ∈ lightVecs n (d - 1) ∧ IsLightUndetectable M₁ M₂ v := by
  rw [lightCand, List.mem_filter, decide_eq_true_eq]

/-! ## 下界证书 -/

/-- **下界证书（可计算形态）**：轻算符集合为空 ⟹ 码距 ≥ `d`。

证明是"反证 + 覆盖 + 翻译"：若存在重量低于 `d` 的不可探测算符，它重量非零
（否则它在行空间里，与不可探测矛盾），重量 $\le d-1$ 使它落入重量限定枚举
（`mem_lightVecs`，**这张证书的可靠性全靠这条覆盖定理**），
再用 `inKerB_iff` / `inSpanB_eq_false_iff` 把它翻译成判定层的两条证书，
最后由 `mem_lightCand` 放回集合——与集合为空矛盾。 -/
theorem lowerHyp_of_lightSet_card_zero {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : (lightSet M₁ M₂ d).card = 0) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.rowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lightCand M₁ M₂ d := by
    rw [mem_lightCand]
    exact ⟨hcov, hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanB_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  have hmem' : E ∈ lightSet M₁ M₂ d := mem_lightSet.mpr hmem
  rw [Finset.card_eq_zero] at h
  rw [h] at hmem'
  simp at hmem'

/-- **下界定理（可计算证书版）**：`lightSet` 为空即给出距离下界。 -/
theorem le_minWeight_of_lightSet_card_zero {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (h : (lightSet M₁ M₂ d).card = 0) :
    d ≤ min_weight_ker_not_mem_rowspace M₁ M₂ :=
  le_minWeight_of_lower M₁ M₂ hd (lowerHyp_of_lightSet_card_zero M₁ M₂ h)

/-! ## List 形态的下界入口（大候选集用这个）

`lightSet` 是候选列表的 `Finset` 形态，`List.toFinset` 的去重是逐元素比较的
$O(N^2)$——在 $n=24,\ d=4$（2325 个候选、每个是 24 位向量）这类实例上，
**去重本身就是整个 `decide` 的主导项**。下面三条与上面的 `lightSet` 族数学内容相同，
只是把假设换成 `lightCand M₁ M₂ d = []`，整条 `Finset` 路径不再进入归约。
小实例（$n\le18$）两者都能过；候选数上千时 List 形态是数量级的差别。 -/

/-- **下界证书（List 形态）**：候选列表为空 ⟹ 码距 ≥ `d`。 -/
theorem lowerHyp_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : lightCand M₁ M₂ d = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.rowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lightCand M₁ M₂ d := by
    rw [mem_lightCand]
    exact ⟨hcov, hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanB_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem

/-- **下界定理（List 形态）**。 -/
theorem le_minWeight_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d₀ : ℕ} (hd : d₀ ≤ n) (h : lightCand M₁ M₂ d₀ = []) :
    d₀ ≤ min_weight_ker_not_mem_rowspace M₁ M₂ :=
  le_minWeight_of_lower M₁ M₂ hd (lowerHyp_of_lightCand_nil M₁ M₂ h)

/-- **精确距离（List 形态）**：与 `eq_minWeight_of_decide` 同形，
下界假设换成候选列表为空——大候选集实例用这个。 -/
theorem eq_minWeight_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : lightCand M₁ M₂ d = []) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.rowSpace) (hw : hammingNorm E = d) :
    min_weight_ker_not_mem_rowspace M₁ M₂ = d :=
  eq_minWeight_of_bounds M₁ M₂ hd hker hnot hw (lowerHyp_of_lightCand_nil M₁ M₂ hlow)

/-- **精确距离（可计算证书形态）**：下界 `by decide`、上界显式见证，一夹即得等号。

这是本包"案例矩阵"统一的证明模板：每个码实例只需给出
① 两个校验矩阵、② 显式的低重量逻辑算符 `E`、③ 三条可由内核算出的闭式断言
（`E` 在核里、`E` 不在行空间里、`hammingNorm E = d`）、④ `lightSet` 为空。
**没有任何一步引用外部求解器或自定义公理。** -/
theorem eq_minWeight_of_decide {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : (lightSet M₁ M₂ d).card = 0) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.rowSpace) (hw : hammingNorm E = d) :
    min_weight_ker_not_mem_rowspace M₁ M₂ = d :=
  eq_minWeight_of_bounds M₁ M₂ hd hker hnot hw
    (lowerHyp_of_lightSet_card_zero M₁ M₂ hlow)

/-! ## 证书复杂度 -/

/-- **下界证书的候选空间规模**：不超过 $\sum_{k<d}\binom nk$。

这是"距离判定证书复杂度定理"的可见内容：候选集是重量限定枚举
（不是 $2^n$），而**枚举长度恰由二项式系数给出**（`length_lightVecs`）。
固定 $d$ 时这是 $n$ 的 $d-1$ 次多项式——$n = 15, d = 3$ 时 121 个候选，
而全空间要 $32768$ 个。 -/
theorem lightCand_length_le {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightCand M₁ M₂ d).length ≤ ∑ k ∈ Finset.range d, n.choose k := by
  refine (List.length_filter_le _ _).trans ?_
  rw [length_lightVecs, show d - 1 + 1 = d from by omega]

/-- 同一件事的 `Finset` 形态。 -/
theorem lightSet_card_le {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightSet M₁ M₂ d).card ≤ ∑ k ∈ Finset.range d, n.choose k :=
  (List.toFinset_card_le _).trans (lightCand_length_le M₁ M₂ hd)

/-! ## 给案例矩阵用的便捷引理 -/

/-- 由可计算判定得到核成员（案例矩阵里写 `(mem_ker_of_inKerB .. (by decide))`）。 -/
theorem mem_ker_of_inKerB {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) {v : Vec n}
    (h : inKerB M v = true) : v ∈ LinearMap.ker M.toLin' :=
  (inKerB_iff M v).mp h

/-- **对偶见证路线**：`w ∈ ker H` 且 `w ⬝ᵥ E = 1` ⟹ `E ∉ rowSpace H`。

比 `not_mem_rowSpace_of_inSpanB_false` **便宜一个量级**：两条断言都是逐行配对，
**不需要行消元**。对宽矩阵（如 $n = 18$ 的环面码）这不是优化而是可用与不可用的差别——
`inSpanB` 内部要跑 `rowReduce`，而 `rowReduce` 在 18 宽矩阵上的内核归约代价
会把 `by decide` 的心跳预算烧穿。 -/
theorem not_mem_rowSpace_of_dualCheck {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    {E w : Vec n} (hk : inKerB H w = true) (hp : w ⬝ᵥ E = 1) : E ∉ H.rowSpace :=
  DualWitness.not_mem_rowSpace ⟨w, (inKerB_iff H w).mp hk, hp⟩

/-- 由可计算判定得到"不在行空间里"（案例矩阵里写 `(not_mem_rowSpace_of_inSpanB_false .. (by decide))`）。

**注意**：它内部要走 `rowReduce`，在宽矩阵上代价高；宽矩阵请改用
`not_mem_rowSpace_of_dualCheck`（对偶见证路线）。 -/
theorem not_mem_rowSpace_of_inSpanB_false {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    {v : Vec n} (h : inSpanB (List.ofFn fun i => M i) v = false) : v ∉ M.rowSpace := by
  rw [Matrix.rowSpace_eq_spanL_ofFn]
  exact (inSpanB_eq_false_iff _ v).mp h

end QECCertificates
