/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.HGP

/-!
# HGP 第二片：压缩恒等式、转置码与单块重量下界（ 续）

第一片（`GF2/HGP`）给出了构造与 CSS 正交性。本模块给出**距离分析**所需的三块骨架。

## 一、压缩恒等式

把向量 `v` 按列空间的两个分块读成两个矩阵 `blockL v`（$n_1\times n_2$）与
`blockR v`（$r_1\times r_2$）。逐条目计算给出

$$H_X\, v = 0 \iff H_1 \cdot \mathrm{blockL}\,v = \mathrm{blockR}\,v \cdot H_2,\qquad
H_Z\, v = 0 \iff \mathrm{blockL}\,v \cdot H_2^\top = H_1^\top \cdot \mathrm{blockR}\,v.$$

第二式把 $(U, R)$ 说成**交换方块**（$H_1 U = R H_2$）——这正是超图积的
"链映射"图景在逐条目层面的形式。距离下界的一切 case 分析都从这条恒等式出发。

## 二、转置码

把输入取转置后当作**新的**校验矩阵：`hgpHZ H₁ᵀ H₂ᵀ` 的列空间是
$(r_1 r_2) \oplus (n_1 n_2)$（两块的形状互换），其行 `(a, d)` 在"交换两分块"
后的条目**逐字等于** `hgpHX H₁ H₂` 的同行条目：

`hgpHZ H₁ᵀ H₂ᵀ x c = hgpHX H₁ H₂ x (sumComm c)`。

于是 `HGP(H₁ᵀ, H₂ᵀ)` 正是 `HGP(H₁, H₂)` 的**转置码**：X 侧分析与 Z 侧分析是
同一条论证的两次应用——下界公式里出现 `ker H₂ᵀ` 的距离（转置码距离）的根源。

## 三、单块重量下界

若 X 型算符只在左半块有支撑（`blockR v = 0`），则压缩恒等式迫使
"每一列都是 $H_1$ 的核向量"；任一非零列的重量 ≥ 左码距离 `d₁`，
而单列重量不超过全向量重量：

  `d₁ ≤ hammingNorm (列) ≤ hammingNorm v`

右半块同理给出 `d₂ᵀ`（$\ker H_2^\top$ 的距离）。**两块同时非零的情形**
（即两条贡献相互抵消）需要"清洗/商"论证，仍未形式化——本模块只做已形式化的那一半，不声称这一条。

## 主结果

* `hgpHX_mulVec_eq_zero_iff` / `hgpHZ_mulVec_eq_zero_iff`：压缩恒等式。
* `hgpHZ_transpose_inputs_apply`：转置码关系。
* `hgp_hammingNorm_ge_of_pure_left` / `_of_pure_right`：单块重量下界。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 分块读取 -/

/-- 把向量在左半块（$n_1\times n_2$）上读成矩阵。 -/
def blockL (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    Matrix (Fin n₁) (Fin n₂) (ZMod 2) :=
  fun a b => v (Sum.inl (a, b))

/-- 把向量在右半块（$r_1\times r_2$）上读成矩阵。 -/
def blockR (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    Matrix (Fin r₁) (Fin r₂) (ZMod 2) :=
  fun s t => v (Sum.inr (s, t))

@[simp] lemma blockL_apply (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (a : Fin n₁) (b : Fin n₂) : blockL v a b = v (Sum.inl (a, b)) := rfl

@[simp] lemma blockR_apply (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2)
    (s : Fin r₁) (t : Fin r₂) : blockR v s t = v (Sum.inr (s, t)) := rfl

/-! ## 逐条目计算的切片引理 -/

/-- 乘积索引上的"取一列"：`Σ_{a,b} A a · [j = b] · F a b = Σ_a A a · F a j`。 -/
lemma sum_prod_slice_snd {m k : ℕ} (A : Fin m → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (j : Fin k) :
    (∑ p : Fin m × Fin k, A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)
      = ∑ a, A a * F a j := by
  rw [Fintype.sum_prod_type (f := fun p : Fin m × Fin k =>
    A p.1 * (if j = p.2 then 1 else 0) * F p.1 p.2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (s := Finset.univ)
    (f := fun b => A a * (if j = b then 1 else 0) * F a b) j ?_ ?_]
  · rw [ite_eq_left rfl, mul_one]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb h.symm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- 乘积索引上的"取一行"：`Σ_{a,b} [i = a] · B b · F a b = Σ_b B b · F i b`。 -/
lemma sum_prod_slice_fst {m k : ℕ} (B : Fin k → ZMod 2) (F : Fin m → Fin k → ZMod 2)
    (i : Fin m) :
    (∑ p : Fin m × Fin k, (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)
      = ∑ b, B b * F i b := by
  rw [Fintype.sum_prod_type (f := fun p : Fin m × Fin k =>
    (if i = p.1 then 1 else 0) * B p.2 * F p.1 p.2)]
  rw [Finset.sum_eq_single (s := Finset.univ)
    (f := fun a : Fin m => ∑ b : Fin k, (if i = a then 1 else 0) * B b * F a b) i ?_ ?_]
  · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (fun h => ha h.symm), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## 压缩恒等式 -/

/-- **X 侧逐条目**：`(H_X v)_{(i,j)} = (H_1 · U)_{ij} + (R · H_2)_{ij}`，
其中 `U = blockL v`、`R = blockR v`。

两个和式分别按 `H_X`、`H_1 ⊗ I`、`I ⊗ H_2` 的**定义**归约（`rfl` 级），
再各用一次切片引理把乘积索引上的和塌成单指标和。 -/
theorem hgpHX_mulVec_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (i : Fin r₁) (j : Fin n₂) :
    (hgpHX H₁ H₂ *ᵥ v) (i, j) = (H₁ * blockL v) i j + (blockR v * H₂) i j := by
  have hL : (hgpHX H₁ H₂ *ᵥ v) (i, j)
      = (∑ ab : Fin n₁ × Fin n₂, (H₁ i ab.1 * (if j = ab.2 then 1 else 0)) * v (Sum.inl ab))
      + (∑ st : Fin r₁ × Fin r₂, ((if i = st.1 then 1 else 0) * H₂ st.2 j) * v (Sum.inr st)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    congr 1
  have hR1 : (H₁ * blockL v) i j = ∑ a, H₁ i a * v (Sum.inl (a, j)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [blockL_apply]
  have hR2 : (blockR v * H₂) i j = ∑ t, H₂ t j * v (Sum.inr (i, t)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [blockR_apply, mul_comm]
  rw [hL, hR1, hR2,
    sum_prod_slice_snd (A := fun a => H₁ i a) (F := fun a b => v (Sum.inl (a, b))) j,
    sum_prod_slice_fst (B := fun t => H₂ t j) (F := fun s t => v (Sum.inr (s, t))) i]

/-- **Z 侧逐条目**：`(H_Z v)_{(a,d)} = (U · H_2ᵀ)_{ad} + (H_1ᵀ · R)_{ad}`。 -/
theorem hgpHZ_mulVec_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (a : Fin n₁) (d : Fin r₂) :
    (hgpHZ H₁ H₂ *ᵥ v) (a, d) = (blockL v * H₂.transpose) a d + (H₁.transpose * blockR v) a d := by
  have hL : (hgpHZ H₁ H₂ *ᵥ v) (a, d)
      = (∑ ab : Fin n₁ × Fin n₂, ((if a = ab.1 then 1 else 0) * H₂ d ab.2) * v (Sum.inl ab))
      + (∑ st : Fin r₁ × Fin r₂, (H₁ st.1 a * (if d = st.2 then 1 else 0)) * v (Sum.inr st)) := by
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    congr 1
  have hR1 : (blockL v * H₂.transpose) a d = ∑ b, H₂ d b * v (Sum.inl (a, b)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Matrix.transpose_apply, blockL_apply, mul_comm]
  have hR2 : (H₁.transpose * blockR v) a d = ∑ s, H₁ s a * v (Sum.inr (s, d)) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Matrix.transpose_apply, blockR_apply]
  rw [hL, hR1, hR2,
    sum_prod_slice_fst (B := fun b => H₂ d b) (F := fun a b => v (Sum.inl (a, b))) a,
    sum_prod_slice_snd (A := fun s => H₁ s a) (F := fun s t => v (Sum.inr (s, t))) d]

/-- **压缩恒等式（X 侧）**：$H_X v = 0 \iff H_1\,U = R\,H_2$。

右端的等式正是"$(U, R)$ 是链映射"的陈述；距离下界的 case 分析全部由此展开。 -/
theorem hgpHX_mulVec_eq_zero_iff (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHX H₁ H₂ *ᵥ v = 0 ↔ H₁ * blockL v = blockR v * H₂ := by
  constructor
  · intro hv
    funext i j
    have h := congrFun hv (i, j)
    rw [hgpHX_mulVec_apply] at h
    simp only [Pi.zero_apply] at h
    exact (add_eq_zero_iff_eq _ _).mp h
  · intro hcomp
    funext x
    obtain ⟨i, j⟩ := x
    rw [hgpHX_mulVec_apply, hcomp]
    simp only [Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- **压缩恒等式（Z 侧）**：$H_Z v = 0 \iff U\,H_2^\top = H_1^\top\,R$。 -/
theorem hgpHZ_mulVec_eq_zero_iff (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔ blockL v * H₂.transpose = H₁.transpose * blockR v := by
  constructor
  · intro hv
    funext a d
    have h := congrFun hv (a, d)
    rw [hgpHZ_mulVec_apply] at h
    simp only [Pi.zero_apply] at h
    exact (add_eq_zero_iff_eq _ _).mp h
  · intro hcomp
    funext x
    obtain ⟨a, d⟩ := x
    rw [hgpHZ_mulVec_apply, hcomp]
    simp only [Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-! ## 转置码 -/

/-- **转置码关系**：把输入转置后得到的 Z 校验矩阵，在"交换两个分块"的列重标号下
逐条目等于原 X 校验矩阵。于是 `HGP(H₁ᵀ, H₂ᵀ)` 是 `HGP(H₁, H₂)` 的转置码——
X 侧与 Z 侧的距离分析是同一条论证的两次应用。 -/
theorem hgpHZ_transpose_inputs_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin r₁ × Fin n₂)
    (c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂)) :
    hgpHZ H₁.transpose H₂.transpose x c
      = hgpHX H₁ H₂ x (Equiv.sumComm _ _ c) := by
  rcases c with st | ab
  · obtain ⟨s, t⟩ := st; rfl
  · obtain ⟨a, b⟩ := ab; rfl

/-! ## 单块重量下界 -/

/-- 沿单射拉回的重量不超过原重量（支撑集在单射下嵌入）。 -/
lemma hammingNorm_le_of_injective {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (he : Function.Injective e) (v : β → ZMod 2) :
    hammingNorm (fun a => v (e a)) ≤ hammingNorm v := by
  show (Finset.univ.filter (fun a => v (e a) ≠ 0)).card
    ≤ (Finset.univ.filter (fun b => v b ≠ 0)).card
  refine Finset.card_le_card_of_injOn e ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact he h

/-- **单块重量下界（左）**：X 型算符若只在左半块有支撑，其重量 ≥ 左码距离 `d₁`。

左半块的每一列都落在 `ker H₁` 里（压缩恒等式 + `blockR v = 0`），
非零列的重量 ≥ `d₁`，而单列重量 ≤ 全向量重量。 -/
theorem hgp_hammingNorm_ge_of_pure_left {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hR : blockR v = 0) {d : ℕ}
    (hd : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d ≤ hammingNorm w)
    (hL : blockL v ≠ 0) : d ≤ hammingNorm v := by
  have hcomp : H₁ * blockL v = 0 := by
    have h := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
    rw [hR, Matrix.zero_mul] at h
    exact h
  obtain ⟨a, b, hab⟩ : ∃ a b, blockL v a b ≠ 0 := by
    by_contra hcon
    exact hL (funext fun a => funext fun b => by
      by_contra hc
      exact hcon ⟨a, b, hc⟩)
  have hcol : H₁ *ᵥ (fun a' => blockL v a' b) = 0 := by
    funext a'
    have h2 : (H₁ * blockL v) a' b = 0 := by rw [hcomp]; rfl
    rw [Matrix.mulVec, dotProduct, ← Matrix.mul_apply]
    exact h2
  have hcolne : (fun a' => blockL v a' b) ≠ 0 :=
    fun h => hab (by simpa using congrFun h a)
  calc d ≤ hammingNorm (fun a' => blockL v a' b) := hd _ hcolne hcol
    _ ≤ hammingNorm (fun p : Fin n₁ × Fin n₂ => blockL v p.1 p.2) :=
        hammingNorm_le_of_injective (fun a' : Fin n₁ => (a', b))
          (fun _ _ h => congrArg Prod.fst h) (fun p : Fin n₁ × Fin n₂ => blockL v p.1 p.2)
    _ ≤ hammingNorm v :=
        hammingNorm_le_of_injective (fun p : Fin n₁ × Fin n₂ => Sum.inl p)
          Sum.inl_injective v

/-- **单块重量下界（右）**：X 型算符若只在右半块有支撑，其重量 ≥ `ker H₂ᵀ` 的距离
（**转置码距离** `d₂ᵀ`）——这正是下界公式里出现转置码的根源。

右半块的每一行 `r_i` 满足 `H₂ᵀ r_i = 0`（压缩恒等式 + `blockL v = 0`）。 -/
theorem hgp_hammingNorm_ge_of_pure_right {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0) (hL : blockL v = 0) {d : ℕ}
    (hd : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d ≤ hammingNorm w)
    (hR : blockR v ≠ 0) : d ≤ hammingNorm v := by
  have hcomp : blockR v * H₂ = 0 := by
    have h := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
    rw [hL, Matrix.mul_zero] at h
    exact h.symm
  obtain ⟨s, t, hst⟩ : ∃ s t, blockR v s t ≠ 0 := by
    by_contra hcon
    exact hR (funext fun s => funext fun t => by
      by_contra hc
      exact hcon ⟨s, t, hc⟩)
  have hrow : H₂.transpose *ᵥ (fun t' => blockR v s t') = 0 := by
    funext t'
    have h2 : (blockR v * H₂) s t' = 0 := by rw [hcomp]; rfl
    have h3 : (H₂.transpose *ᵥ (fun t' => blockR v s t')) t' = (blockR v * H₂) s t' := by
      rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun t _ => by rw [Matrix.transpose_apply, mul_comm]
    rw [h3]
    exact h2
  have hrowne : (fun t' => blockR v s t') ≠ 0 :=
    fun h => hst (by simpa using congrFun h t)
  calc d ≤ hammingNorm (fun t' => blockR v s t') := hd _ hrowne hrow
    _ ≤ hammingNorm (fun q : Fin r₁ × Fin r₂ => blockR v q.1 q.2) :=
        hammingNorm_le_of_injective (fun t' : Fin r₂ => (s, t'))
          (fun _ _ h => congrArg Prod.snd h) (fun q : Fin r₁ × Fin r₂ => blockR v q.1 q.2)
    _ ≤ hammingNorm v :=
        hammingNorm_le_of_injective (fun q : Fin r₁ × Fin r₂ => Sum.inr q)
          Sum.inr_injective v

end QECCertificates
