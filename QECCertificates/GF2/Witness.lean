/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.RankCertificate

/-!
# 对偶见证证书与精确距离双定理（/）

码距的判定是双侧的：**下界**说"没有更轻的逻辑算符"（需要对低重量算符做穷举/归约），
**上界**说"这里就有一个"（只需一个实物证据）。本模块把上界一侧做成
**可独立检查的证书**，并与 LeanQEC 的距离定义合拢成"恰好等于 $d$"的封闭断言。

## 对偶见证

要证明算符 `E` **不在**校验行空间里，不必穷举：只要拿出一个与所有校验对易、
却与 `E` 反对易的向量 `w`——即

  `w ∈ ker H`　且　`w ⬝ᵥ E = 1`.

这是 LeanQEC `not_mem_rowspace_iff_exists_mem_ker` 的证书化包装：
**证书只有两项、逐项可核**，且完备性（`E ∉ rowSpace → 存在这样的 w`）由该定理给出。

## 双矩阵形式

下表（`M₁` 提供核、`M₂` 提供行空间）覆盖本包全部三类码：

| 码类 | `M₁` | `M₂` | 重量 = |
|---|---|---|---|
| 经典线性码 | 校验矩阵 `H` | 空矩阵 | 非零码字重量 |
| CSS 码 | 一侧校验 | 另一侧校验 | X/Z 型逻辑算符重量 |
| 一般稳定子码 | 生成元的**辛换位** | 生成元本身 | Pauli 重量（两半合计） |

后一类之所以成立：辛内积 `⟨g, v⟩ = (J g) ⬝ᵥ v`（`J` 交换"`Z` 半"与"`X` 半"），
于是"与全部生成元对易"就是"落在 `J` 的行正交补（即 `ker J`）里"。

## 主结果

* `DualWitness`：对偶见证证书结构；`DualWitness.not_mem_rowSpace` 为其内核可检的结论。
* `exists_dualWitness_iff`：**证书完备**——`E ∉ 行空间` 等价于存在对偶见证。
* `minWeight_le_of_witness`：**上界定理**——一个实物证据给出码距上界。
* `le_minWeight_of_lower`：**下界定理**——逐算符下界给出码距下界。
* `eq_minWeight_of_bounds`：**精确距离**——两侧合拢即"恰好等于 $d$"。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 对偶见证 -/

/-- **对偶见证**：与校验矩阵 `H` 的每一行都正交（对易），但与 `E` 的配对为 1。

两项数据、逐项可核：第一项是"与所有校验对易"，第二项是"与 `E` 反对易"。
两者合起来证明 `E` 不是稳定子群的元素——这是"逻辑算符"判定的最小证书。 -/
structure DualWitness {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) where
  /-- 见证向量。 -/
  w : Vec n
  /-- 与所有校验行正交。 -/
  mem_ker : w ∈ LinearMap.ker H.toLin'
  /-- 与目标算符的配对为 1（GF(2) 上即"反对易"）。 -/
  pairing : w ⬝ᵥ E = 1

/-- **证书可靠性**：持有对偶见证即证明 `E` 不在校验行空间里（故为逻辑算符）。 -/
theorem DualWitness.not_mem_rowSpace {m : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {E : Vec n}
    (hw : DualWitness H E) : E ∉ H.rowSpace :=
  (not_mem_rowspace_iff_exists_mem_ker H E).mpr ⟨hw.w, hw.mem_ker, hw.pairing⟩

/-- **证书完备性**：`E` 不在行空间里 ⟺ 存在对偶见证。

完备性由 LeanQEC 的 `not_mem_rowspace_iff_exists_mem_ker` 给出——
本包把它的存在性输出包装成"可检查的证书"这一形态。 -/
theorem exists_dualWitness_iff {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) :
    (∃ _ : DualWitness H E, True) ↔ E ∉ H.rowSpace := by
  constructor
  · rintro ⟨hw, -⟩; exact hw.not_mem_rowSpace
  · intro hE
    obtain ⟨w, hker, hpair⟩ := (not_mem_rowspace_iff_exists_mem_ker H E).mp hE
    exact ⟨⟨w, hker, hpair⟩, trivial⟩

/-! ## 码距的双侧刻画 -/

/-- 不可探测非平凡算符的集合：与 `M₁` 的每一行正交、却不是 `M₂` 行空间元素。

`ker M₁ \ rowSpace M₂` 正是"逻辑算符模稳定子"的空间——不被探测、
却不是稳定子群元素（真的翻转逻辑）的算符。标记 `@[reducible]` 是为了让下文
`Set.toFinset` 的实例合成能展开它。 -/
@[reducible] def undetectableSet {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) : Set (Vec n) :=
  (↑(LinearMap.ker M₁.toLin') : Set (Vec n)) \ (↑M₂.rowSpace : Set (Vec n))

/-- **码距**：沿用 LeanQEC 的 `min_weight_ker_not_mem_rowspace`（不可探测非平凡算符的
最低重量；集合为空时取 `n + 1`），并对角特化到"校验矩阵与行空间取同一个"。

与上游定义**逐字相同**，故本模块的结论可直接回灌到 LeanQEC 的距离归约链。
一般（双矩阵）情形请直接用 `min_weight_ker_not_mem_rowspace`。 -/
noncomputable abbrev codeDistance {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace H H

/-- 重量为 `d₀` 的不可探测非平凡算符的存在性，落入最小值集合。 -/
lemma mem_image_hammingNorm_of_witness {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.rowSpace)
    (hw : hammingNorm E = d₀) :
    d₀ ∈ Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset := by
  rw [Finset.mem_image]
  exact ⟨E, by rw [Set.mem_toFinset]; exact ⟨hker, hnot⟩, hw⟩

/-- **上界定理**：存在重量为 `d₀` 的不可探测非平凡算符 ⟹ 码距 ≤ `d₀`。

这就是"witness 上界"：证书是一个具体的低重量逻辑算符，内核只需核
`E ∈ ker M₁`、`E ∉ rowSpace M₂`、`hammingNorm E = d₀` 三项。 -/
theorem minWeight_le_of_witness {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.rowSpace)
    (hw : hammingNorm E = d₀) :
    min_weight_ker_not_mem_rowspace M₁ M₂ ≤ d₀ := by
  have hmem := mem_image_hammingNorm_of_witness M₁ M₂ hker hnot hw
  have hle : Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset)
      ≤ (d₀ : WithTop ℕ) := Finset.min_le hmem
  unfold min_weight_ker_not_mem_rowspace
  change (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
    | none => n + 1
    | some a => a) ≤ d₀
  split
  · rename_i htop
    have hempty : Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset = ∅ :=
      Finset.min_eq_top.mp
        (show (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset).min = ⊤ from htop)
    rw [hempty] at hmem
    simp at hmem
  · rename_i a ha
    rw [ha] at hle
    exact WithTop.coe_le_coe.mp hle

/-- **下界定理**：若每个不可探测非平凡算符的重量都不少于 `d₀`，则码距 ≥ `d₀`。

下界一侧没有短证书（除非有结构化论证），正是 LeanQEC 走 SAT/UNSAT 归约的原因；
本定理的作用是给"下界侧的结果"与"上界侧的 witness"提供同一个合拢接口。
下界侧的可计算证书见 `QECCertificates.GF2.LowerBound`。 -/
theorem le_minWeight_of_lower {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  change d₀ ≤ (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
    | none => n + 1
    | some a => a)
  split
  · exact Nat.le_trans hd (Nat.le_succ n)
  · rename_i a ha
    have hmem := Finset.mem_of_min ha
    rw [Finset.mem_image] at hmem
    obtain ⟨E, hE, hEw⟩ := hmem
    rw [Set.mem_toFinset] at hE
    rw [← hEw]
    exact h E hE.1 hE.2

/-- **精确距离（双侧合拢）**：下界与上界相等，即得"距离恰好等于 $d$"。

这是"精确距离断言"的形式骨架：
下界由内核证明（或经 SAT/LRAT 归约），上界交给一个具体的低重量逻辑算符。 -/
theorem eq_minWeight_of_bounds {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.rowSpace) (hw : hammingNorm E = d₀)
    (hlower : ∀ F, F ∈ LinearMap.ker M₁.toLin' → F ∉ M₂.rowSpace → d₀ ≤ hammingNorm F) :
    min_weight_ker_not_mem_rowspace M₁ M₂ = d₀ :=
  le_antisymm (minWeight_le_of_witness M₁ M₂ hker hnot hw) (le_minWeight_of_lower M₁ M₂ hd hlower)

end QECCertificates
