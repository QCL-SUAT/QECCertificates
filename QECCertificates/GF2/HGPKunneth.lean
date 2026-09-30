/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.KunnethCore

/-!
# HGP 的维数张量公式 `k = k₁k₂ + k₁ᵀk₂ᵀ`（ 收官）

Tillich–Zémor 超图积的**逻辑比特数**满足 Künneth 型张量公式：

$$k(\mathrm{HGP}(H_1,H_2)) \;=\; k_1k_2 + k_1^\top k_2^\top,\qquad
k_1 = \dim\ker H_1,\quad k_1^\top=\dim\ker H_1^\top,$$

其中 $k = n - \operatorname{rank}H_X - \operatorname{rank}H_Z$（$n = n_1n_2+r_1r_2$）。
第一片给出了构造与 CSS 正交性、第二片压缩恒等式、第三片距离下界——本模块补上**维数一侧**，
 由此收官（距离 + 维数两侧都成了对任意输入 $H_1,H_2$ 的结构化定理）。

## 证明骨架

`hgpHX` 的秩是分块矩阵的秩：

$$\operatorname{rank}[\,A\otimes I_s \mid I_p\otimes B^\top\,]
= \operatorname{rank}(A\otimes I_s) + \operatorname{rank}(I_p\otimes B^\top)
 - \dim\big(\mathrm{im}(A\otimes I_s)\cap \mathrm{im}(I_p\otimes B^\top)\big),$$

三项各自是 `KunnethCore` 的维数事实：

| 项 | 识别 | 维数 |
|---|---|---|
| `im(A ⊗ I)` | 列 ⊆ `col A` 的矩阵（`colsSub`） | `s · rank A`（`finrank_colsSub`） |
| `im(I ⊗ Bᵀ)` | 行 ⊆ `row B` 的矩阵（`rowsSub`） | `p · rank B`（`finrank_rowsSub`） |
| 交集 | **列 ⊆ `col A` 且行 ⊆ `row B`** | `rank A · rank B`（`finrank_colsRows`，即"子空间张量交"） |

对 $H_Z$ 走**转置码运输**（第三片的 `mulVec_swap_eq`）：$H_Z(A,B)$ 与
$H_X(A^\top,B^\top)$ 只差列的分块交换，秩相同——与距离一侧共用同一套论证。

## 主结果

* `rank_hgpHX_add`：`rank H_X + rank A · rank B = n₂ · rank A + r₁ · rank B`；
* `rank_hgpHZ_add`：`rank H_Z + rank A · rank B = r₂ · rank A + n₁ · rank B`；
* **`hgp_kunneth`**：$k = k_1k_2+k_1^\top k_2^\top$（减法形）。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 一、两个块映射 `M ↦ A·M` 与 `N ↦ N·B` -/

/-- **左乘块** `M ↦ A·M`（即 $A\otimes I$）：行 `p` 由 `A` 作用、列不动。 -/
noncomputable def mulLeft (A : Matrix (Fin p) (Fin q) (ZMod 2)) : VMat q s →ₗ[ZMod 2] VMat p s where
  toFun M := fun ij => ∑ a, A ij.1 a * M (a, ij.2)
  map_add' M N := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- **右乘块** `N ↦ N·B`（即 $I\otimes B$）：列由 `B` 作用、行不动。 -/
noncomputable def mulRight (B : Matrix (Fin r) (Fin s) (ZMod 2)) : VMat p r →ₗ[ZMod 2] VMat p s where
  toFun N := fun ij => ∑ t, N (ij.1, t) * B t ij.2
  map_add' M N := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-! ## 二、两个块的像：列约束 / 行约束 -/

/-- **左乘块的像 = 列约束空间**：`M ↦ A·M` 的像恰是"每列都在 `A` 的列空间中"的矩阵。 -/
theorem range_mulLeft (A : Matrix (Fin p) (Fin q) (ZMod 2)) :
    LinearMap.range (mulLeft (s := s) A) = colsSub (LinearMap.range A.mulVecLin) := by
  ext X
  constructor
  · rintro ⟨M, rfl⟩ j
    refine ⟨colOf M j, ?_⟩
    funext i
    rw [Matrix.mulVecLin_apply]
    simp only [Matrix.mulVec, dotProduct, colOf_apply, mulLeft, LinearMap.coe_mk,
      AddHom.coe_mk]
  · intro hX
    choose f hf using fun j => hX j
    refine ⟨fun aj => f aj.2 aj.1, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    have hstep : ∑ x, A i x * f j x = X (i, j) := by
      have h := congrFun (hf j) i
      rw [Matrix.mulVecLin_apply] at h
      simp only [Matrix.mulVec, dotProduct, colOf_apply] at h
      exact h
    exact hstep

/-- **右乘块的像 = 行约束空间**：`N ↦ N·B` 的像恰是"每行都在 `B` 的行空间中"的矩阵。 -/
theorem range_mulRight (B : Matrix (Fin r) (Fin s) (ZMod 2)) :
    LinearMap.range (mulRight (p := p) B) = rowsSub (Matrix.rowSpace B) := by
  ext X
  constructor
  · rintro ⟨N, rfl⟩ i
    have hrow : rowOf (mulRight B N) i = ∑ t, N (i, t) • (fun j => B t j) := by
      funext j
      simp only [rowOf_apply, mulRight, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    rw [hrow]
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro hX
    choose f hf using fun i => (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)
      (v := B) (x := rowOf X i)).mp (hX i)
    refine ⟨fun it => f it.1 it.2, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    have hstep : ∑ t, f i t * B t j = X (i, j) := by
      have h := congrFun (hf i) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply] at h
      exact h
    exact hstep

/-! ## 三、`H_X` 的秩 -/

/-- 分块读取（乘积索引）：左半块 `n₁×n₂`。 -/
def blkL (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) : VMat n₁ n₂ :=
  fun ab => v (Sum.inl ab)

/-- 分块读取（乘积索引）：右半块 `r₁×r₂`。 -/
def blkR (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) : VMat r₁ r₂ :=
  fun st => v (Sum.inr st)

/-- **`H_X` 的分块作用**：`H_X v = A·U + R·B`（`U = blkL v`、`R = blkR v`）——
压缩恒等式的"矩阵之和"形态。 -/
theorem hgpHX_mulVecLin_eq_blocks (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    (hgpHX A B).mulVecLin v
      = mulLeft (s := n₂) A (blkL v) + mulRight (p := r₁) B (blkR v) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  rw [Matrix.mulVecLin_apply, hgpHX_mulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rfl

/-- **`H_X` 的秩 = 两个块的像之和的维数**。 -/
theorem rank_hgpHX_add (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHX A B).rank + A.rank * B.rank = A.rank * n₂ + B.rank * r₁ := by
  have hrange : LinearMap.range (hgpHX A B).mulVecLin
      = LinearMap.range (mulLeft (s := n₂) A) ⊔ LinearMap.range (mulRight (p := r₁) B) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro X ⟨v, rfl⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨blkL v, rfl⟩)
        (Submodule.mem_sup_right ⟨blkR v, rfl⟩)
    · rintro X ⟨M, rfl⟩
      refine ⟨Sum.elim M (0 : VMat r₁ r₂), ?_⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      have h1 : blkL (Sum.elim M (0 : VMat r₁ r₂)) = M := rfl
      have h2 : blkR (Sum.elim M (0 : VMat r₁ r₂)) = 0 := rfl
      rw [h1, h2, map_zero, add_zero]
    · rintro X ⟨N, rfl⟩
      refine ⟨Sum.elim (0 : VMat n₁ n₂) N, ?_⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      have h1 : blkL (Sum.elim (0 : VMat n₁ n₂) N) = 0 := rfl
      have h2 : blkR (Sum.elim (0 : VMat n₁ n₂) N) = N := rfl
      rw [h1, h2, map_zero, zero_add]
  let L1 : Submodule (ZMod 2) (VMat r₁ n₂) := LinearMap.range (mulLeft (s := n₂) A)
  let L2 : Submodule (ZMod 2) (VMat r₁ n₂) := LinearMap.range (mulRight (p := r₁) B)
  have hL1 : L1 = colsSub (LinearMap.range A.mulVecLin) := range_mulLeft A
  have hL2 : L2 = rowsSub (Matrix.rowSpace B) := range_mulRight B
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (V := VMat r₁ n₂)
    (s := L1) (t := L2)
  have h1 : Module.finrank (ZMod 2) L1 = A.rank * n₂ := by
    rw [hL1, finrank_colsSub]
    exact mul_comm _ _
  have h2 : Module.finrank (ZMod 2) L2 = B.rank * r₁ := by
    rw [hL2, finrank_rowsSub, ← Matrix.rank_eq_finrank_rowSpace B]
    exact mul_comm _ _
  have h3 : Module.finrank (ZMod 2) ↥(L1 ⊓ L2) = A.rank * B.rank := by
    rw [hL1, hL2, finrank_colsRows, ← Matrix.rank_eq_finrank_rowSpace B]
    rfl
  have hrank : (hgpHX A B).rank = Module.finrank (ZMod 2) ↥(L1 ⊔ L2) := by
    rw [Matrix.rank, hrange]
  rw [hrank]
  rw [h3, h1, h2] at hsup
  exact hsup

/-! ## 四、`H_Z` 的秩（转置码运输） -/

/-- **`H_Z` 的秩 = `H_X` 在转置输入上的秩**：两个矩阵只差列的分块交换
（第三片的 `mulVec_swap_eq`），故像相同。 -/
theorem rank_hgpHZ_eq (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank = (hgpHX A.transpose B.transpose).rank := by
  have hrange : LinearMap.range (hgpHZ A B).mulVecLin
      = LinearMap.range (hgpHX A.transpose B.transpose).mulVecLin := by
    ext X
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨fun c => v (swapBlocks c), by
        funext x
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_swap_eq]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun c => w (swapBlocks c), by
        funext x
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_swap_eq]
        congr 1
        funext c
        simp only [swapBlocks_swapBlocks]⟩
  rw [Matrix.rank, Matrix.rank, hrange]

/-- **`H_Z` 的秩**：与 `rank_hgpHX_add` 同形，`n₂ ↦ r₂`、`r₁ ↦ n₁`。 -/
theorem rank_hgpHZ_add (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank + A.rank * B.rank = A.rank * r₂ + B.rank * n₁ := by
  have h := rank_hgpHX_add A.transpose B.transpose
  rw [Matrix.rank_transpose, Matrix.rank_transpose] at h
  rw [rank_hgpHZ_eq]
  exact h

/-! ## 五、维数张量公式 -/

/-- **维数张量公式（整数形式）**：把 `k = n - rank H_X - rank H_Z` 写成加法，
在 `ℤ` 上做多项式算术（`nlinarith`），避免 `ℕ` 截断减法。 -/
theorem hgp_kunneth_int (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ)
      + (((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank))
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ := by
  have h1 : ((hgpHX A B).rank : ℤ) + (A.rank : ℤ) * B.rank
      = (A.rank : ℤ) * n₂ + (B.rank : ℤ) * r₁ := by
    exact_mod_cast rank_hgpHX_add A B
  have h2 : ((hgpHZ A B).rank : ℤ) + (A.rank : ℤ) * B.rank
      = (A.rank : ℤ) * r₂ + (B.rank : ℤ) * n₁ := by
    exact_mod_cast rank_hgpHZ_add A B
  nlinarith [h1, h2]

/-- **HGP 的维数张量公式（Künneth）**：逻辑比特数 $k = n - \operatorname{rank}H_X -
\operatorname{rank}H_Z$ 恰为 $k_1k_2 + k_1^\top k_2^\top$（两个经典码的核维数之积的和）。

这是  的最后一块：距离一侧（第三片 + 对偶侧）与维数一侧（本定理）合起来，
$n\ge144$ 的 HGP 族参数有了**不依赖枚举**的结构化断言。 -/
theorem hgp_kunneth (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank
      = (n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) := by
  have hA1 : A.rank ≤ n₁ := A.rank_le_width
  have hA2 : A.rank ≤ r₁ := A.rank_le_height
  have hB1 : B.rank ≤ n₂ := B.rank_le_width
  have hB2 : B.rank ≤ r₂ := B.rank_le_height
  -- 和的界（由 ℤ 恒等式 + 两个乘积非负）
  have hb : (hgpHX A B).rank + (hgpHZ A B).rank ≤ n₁ * n₂ + r₁ * r₂ := by
    by_contra hcon
    have hlt : ((n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂)
        < ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ) := by
      exact_mod_cast Nat.not_le.mp hcon
    have h1' : (0 : ℤ) ≤ (n₁ : ℤ) - A.rank := by
      have : (A.rank : ℤ) ≤ (n₁ : ℤ) := by exact_mod_cast hA1
      linarith
    have h2' : (0 : ℤ) ≤ (n₂ : ℤ) - B.rank := by
      have : (B.rank : ℤ) ≤ (n₂ : ℤ) := by exact_mod_cast hB1
      linarith
    have h3' : (0 : ℤ) ≤ (r₁ : ℤ) - A.rank := by
      have : (A.rank : ℤ) ≤ (r₁ : ℤ) := by exact_mod_cast hA2
      linarith
    have h4' : (0 : ℤ) ≤ (r₂ : ℤ) - B.rank := by
      have : (B.rank : ℤ) ≤ (r₂ : ℤ) := by exact_mod_cast hB2
      linarith
    have hnn : (0 : ℤ) ≤ ((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank) := by nlinarith [h1', h2', h3', h4']
    have := hgp_kunneth_int A B
    linarith
  -- 两侧取 `ℤ` 后由恒等式收尾
  have hle1 : (hgpHX A B).rank ≤ n₁ * n₂ + r₁ * r₂ := le_trans (Nat.le_add_right _ _) hb
  have hle2 : (hgpHZ A B).rank ≤ (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank := by omega
  apply Nat.cast_injective (R := ℤ)
  have hcast : (((n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank : ℕ) : ℤ)
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ - (hgpHX A B).rank - (hgpHZ A B).rank := by
    rw [Nat.cast_sub hle2, Nat.cast_sub hle1]
    push_cast
    ring
  have hcast2 : (((n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) : ℕ) : ℤ)
      = ((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank) := by
    push_cast [Nat.cast_sub hA1, Nat.cast_sub hA2, Nat.cast_sub hB1, Nat.cast_sub hB2]
    ring
  rw [hcast, hcast2]
  linarith [hgp_kunneth_int A B]

end QECCertificates
