/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.HGPCleaning

/-!
# HGP 第三片（对偶侧）：Z 距离下界（转置码运输）

X 侧（`GF2/HGPCleaning`）证了 $v\in\ker H_X$、$v\notin\mathrm{row}H_Z$
$\Longrightarrow \min(d_1,d_2^\top)\le|v|$。本模块给出对偶陈述

$$v\in\ker H_Z,\; v\notin\mathrm{row}H_X \;\Longrightarrow\;
\min(d_1^\top,\, d_2) \le |v|,\qquad
d_1^\top=\min\ker H_1^\top,\; d_2=\min\ker H_2 .$$

**路线：转置码运输。** 第二片已证（`hgpHZ_transpose_inputs_apply`）
$$H_Z(H_1^\top,H_2^\top)\ \text{的第 }x\text{ 行}
= \big(H_X(H_1,H_2)\ \text{的第 }x\text{ 行}\big)\circ(\text{分块交换}),$$
即两个矩阵**逐条目相同、只差列的分块交换**。于是：

* `hgpHZ_row_eq_swap`：行恒等式（逐条目，直接来自第二片的转置码关系）；
* `mulVec_swap_eq` / `hgpHZ_mulVec_eq_zero_iff_swap`：$v\in\ker H_Z(H_1,H_2)$ ⟺
  交换后的 $v$ 落在 $\ker H_X(H_1^\top,H_2^\top)$——**两个点积逐行相等**，不只是"同时为零"；
* `mem_rowSpace_X_of_swap_mem_rowSpace_Z`：行空间的对应（生成元逐条对应 + 子空间归纳）；
* `hammingNorm_swapBlocks`：分块交换保重量。

四条合起来，**Z 侧定理直接是 X 侧定理在转置输入上的实例**（`hgp_Z_distance_ge`）：
清洗论证不必重做一遍——这正是"转置码"一词在距离分析里的作用。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 一、分块交换 -/

/-- **分块交换**（自逆）：$\alpha\oplus\beta \to \beta\oplus\alpha$
——正是 `hgpHZ_transpose_inputs_apply` 里的 `Equiv.sumComm`。 -/
def swapBlocks {α β : Type*} : α ⊕ β → β ⊕ α := Sum.swap

/-- 分块交换自逆。 -/
lemma swapBlocks_swapBlocks {α β : Type*} (c : α ⊕ β) : swapBlocks (swapBlocks c) = c := by
  rcases c with ab | st <;> rfl

/-- 分块交换是单射。 -/
lemma swapBlocks_injective {α β : Type*} : Function.Injective (swapBlocks (α := α) (β := β)) := by
  intro a b hab
  have h := congrArg (swapBlocks (α := β) (β := α)) hab
  simpa only [swapBlocks_swapBlocks] using h

/-- **分块交换保重量**。 -/
lemma hammingNorm_swapBlocks
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hammingNorm (fun c => v (swapBlocks c)) = hammingNorm v := by
  have h₁ : hammingNorm (fun c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) => v (swapBlocks c))
      ≤ hammingNorm v :=
    hammingNorm_le_of_injective (fun c => swapBlocks c)
      (fun _ _ hab => swapBlocks_injective hab) v
  have h₂ : hammingNorm v
      ≤ hammingNorm (fun c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) => v (swapBlocks c)) := by
    have h := hammingNorm_le_of_injective (swapBlocks (α := (Fin n₁ × Fin n₂)) (β := (Fin r₁ × Fin r₂)))
      (swapBlocks_injective) (fun c => v (swapBlocks c))
    simpa only [swapBlocks_swapBlocks] using h
  exact le_antisymm h₁ h₂

/-! ## 二、行恒等式与核的对应 -/

/-- **行恒等式**：$H_Z(H_1^\top,H_2^\top)$ 的第 $x$ 行 = $H_X(H_1,H_2)$ 的第 $x$ 行
再作分块交换（逐条目，直接来自第二片的转置码关系）。 -/
lemma hgpHZ_row_eq_swap (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin n₁ × Fin r₂) :
    hgpHZ H₁ H₂ x = fun c => hgpHX H₁.transpose H₂.transpose x (swapBlocks c) := by
  funext c
  rcases c with ab | st
  · have h := hgpHZ_transpose_inputs_apply H₁.transpose H₂.transpose x (Sum.inl ab)
    simpa only [Equiv.sumComm_apply, swapBlocks, Matrix.transpose_transpose] using h
  · have h := hgpHZ_transpose_inputs_apply H₁.transpose H₂.transpose x (Sum.inr st)
    simpa only [Equiv.sumComm_apply, swapBlocks, Matrix.transpose_transpose] using h

/-- **点积的行恒等式**：两个核条件逐行相等（不只是"同时为零"）。 -/
theorem mulVec_swap_eq (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (x : Fin n₁ × Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) x
      = (hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c))) x := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  have h₁ : (∑ c, hgpHZ H₁ H₂ x c * v c)
      = ∑ c, hgpHX H₁.transpose H₂.transpose x (swapBlocks c) * v c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [congrFun (hgpHZ_row_eq_swap H₁ H₂ x) c]
  rw [h₁]
  refine Finset.sum_bij (fun c _ => swapBlocks c) ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro c _ c' _ h; exact swapBlocks_injective h
  · intro c' _; exact ⟨swapBlocks c', Finset.mem_univ _, swapBlocks_swapBlocks c'⟩
  · intro c _
    rw [swapBlocks_swapBlocks]

/-- **核的对应**：$v\in\ker H_Z(H_1,H_2)$ ⟺ 交换后的 $v$ 落在 $\ker H_X(H_1^\top,H_2^\top)$。 -/
theorem hgpHZ_mulVec_eq_zero_iff_swap (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔
      hgpHX H₁.transpose H₂.transpose *ᵥ (fun c => v (swapBlocks c)) = 0 := by
  constructor <;> intro h
  · funext x
    rw [← mulVec_swap_eq H₁ H₂ v x, congrFun h x]
  · funext x
    rw [mulVec_swap_eq H₁ H₂ v x, congrFun h x]

/-- **行空间的对应**：交换后落在 $H_Z(H_1^\top,H_2^\top)$ 行空间中的向量 $w$，
其"再交换一次"落在 $H_X(H_1,H_2)$ 的行空间中——对 $v := w\circ\text{swap}$ 即
$v\in\mathrm{row}H_X(H_1,H_2)$。 -/
theorem mem_rowSpace_X_of_swap_mem_rowSpace_Z (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (h : (fun c => v (swapBlocks c)) ∈ (hgpHZ H₁.transpose H₂.transpose).rowSpace) :
    v ∈ (hgpHX H₁ H₂).rowSpace := by
  have hgen : ∀ x : Fin r₁ × Fin n₂,
      (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
        (hgpHZ H₁.transpose H₂.transpose x) (swapBlocks c)) ∈ (hgpHX H₁ H₂).rowSpace := by
    intro x
    have hrow : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
        (hgpHZ H₁.transpose H₂.transpose x) (swapBlocks c)) = hgpHX H₁ H₂ x := by
      funext c
      rw [hgpHZ_transpose_inputs_apply H₁ H₂ x (swapBlocks c)]
      congr 1
      rcases c with ab | st
      · rfl
      · rfl
    rw [hrow]
    exact Submodule.subset_span ⟨x, rfl⟩
  have hclosure : ∀ w : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) → ZMod 2,
      w ∈ (hgpHZ H₁.transpose H₂.transpose).rowSpace →
      (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => w (swapBlocks c))
        ∈ (hgpHX H₁ H₂).rowSpace := by
    intro w hw
    have hw' : w ∈ Submodule.span (ZMod 2)
        (Set.range fun x : Fin r₁ × Fin n₂ => hgpHZ H₁.transpose H₂.transpose x) := hw
    refine Submodule.span_induction
      (p := fun w _ => (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => w (swapBlocks c))
        ∈ (hgpHX H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hw'
    · intro g hg
      obtain ⟨x, rfl⟩ := hg
      exact hgen x
    · have hz : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
          (0 : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) → ZMod 2) (swapBlocks c)) = 0 := by
        funext c; rfl
      rw [hz]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      have hadd : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => (a + b) (swapBlocks c))
          = (fun c => a (swapBlocks c)) + fun c => b (swapBlocks c) := by
        funext c; rfl
      rw [hadd]
      exact Submodule.add_mem _ ha hb
    · intro cf a _ ha
      have hsmul : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => (cf • a) (swapBlocks c))
          = cf • (fun c => a (swapBlocks c)) := by
        funext c; rfl
      rw [hsmul]
      exact Submodule.smul_mem _ cf ha
  have := hclosure (fun c => v (swapBlocks c)) h
  simpa only [swapBlocks_swapBlocks] using this

/-! ## 三、Z 距离下界（X 侧定理的转置实例） -/

/-- **HGP 的 Z 距离下界**：不在 `H_X` 行空间中的非零 Z 型算符重量至少是
$\min(d_1^\top, d_2)$——**转置码距离**与右码距的较小者。

证明：把 $v$ 作分块交换后套用 X 侧定理（输入取 $(H_1^\top,H_2^\top)$）——
转置把 $d_1\leftrightarrow d_1^\top$、$d_2^\top\leftrightarrow d_2$ 互换，
故 X 侧的 $\min(d_1,d_2^\top)$ 在这里正是 $\min(d_1^\top,d_2)$。 -/
theorem hgp_Z_distance_ge (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).rowSpace) {d₁T d₂ : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w) :
    min d₁T d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge (H₁ := H₁.transpose) (H₂ := H₂.transpose)
    (v := fun c => v (swapBlocks c)) (d₁ := d₁T) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
  rwa [hammingNorm_swapBlocks] at hmain

/-! ## 四、四条"清洗步可卸"的 Z 侧版本（X 侧定理的转置实例）

X 侧（`GF2/HGPCleaning` §六）证了清洗下界的两步**各自可以换成一条核条件**，于是下界只剩
一个因子。本节把四条逐条搬到 Z 侧——**论证一字未改**，只做与 `hgp_Z_distance_ge` 相同的
三步运输（核的对应、行空间的对应、保重量）。两条"行清洁可卸"的搬成 $d_2\le|v|$、
两条"列清洁可卸"的搬成 $d_1^\top\le|v|$：

| X 侧（核条件 → 只剩的因子） | Z 侧 |
|---|---|
| $\ker H_1=0$（或 $\ker H_2=0$）$\Rightarrow d_2^\top$ | $\ker H_1^\top=0$（或 $\ker H_2^\top=0$）$\Rightarrow d_2$ |
| $\ker H_1^\top=0$（或 $\ker H_2^\top=0$）$\Rightarrow d_1$ | $\ker H_1=0$（或 $\ker H_2=0$）$\Rightarrow d_1^\top$ | -/

/-- **$d_Z$ 的下界（$\ker H_1=0$ 支）**：$H_1$ 单射时 $d_1^\top$ 一个因子就够。 -/
theorem hgp_Z_distance_ge_of_H1Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).rowSpace) {d₁T : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) :
    d₁T ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_adjoint_ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₁ := d₁T)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun u hu => by simpa [Matrix.transpose_transpose] using hT u hu)
  rwa [hammingNorm_swapBlocks] at hmain

/-- **$d_Z$ 的下界（$\ker H_2^\top=0$ 支）**：$H_2^\top$ 单射时 $d_2$ 一个因子就够。 -/
theorem hgp_Z_distance_ge_of_H2TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).rowSpace) {d₂ : ℕ}
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) :
    d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H2Ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
    hT
  rwa [hammingNorm_swapBlocks] at hmain

/-- **$d_Z$ 的下界（$\ker H_1^\top=0$ 支）**：$H_1^\top$ 单射时 $d_2$ 一个因子就够。 -/
theorem hgp_Z_distance_ge_of_H1TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).rowSpace) {d₂ : ℕ}
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H1Ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
    hT
  rwa [hammingNorm_swapBlocks] at hmain

/-- **$d_Z$ 的下界（$\ker H_2=0$ 支）**：$H_2$ 单射时 $d_1^\top$ 一个因子就够。 -/
theorem hgp_Z_distance_ge_of_H2Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).rowSpace) {d₁T : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) :
    d₁T ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H2TKer_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₁ := d₁T)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun u hu => by simpa [Matrix.transpose_transpose] using hT u hu)
  rwa [hammingNorm_swapBlocks] at hmain

end QECCertificates