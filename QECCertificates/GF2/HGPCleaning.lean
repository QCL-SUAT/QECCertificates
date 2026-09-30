/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.HGPCompression
import QECCertificates.GF2.Canonical
import QECCertificates.GF2.KernelBasis

/-!
# HGP 第三片：清洗论证与 X 距离下界（ 收官）

第一片给了构造与 CSS 正交性，第二片给了压缩恒等式 $H_Xv=0 \iff H_1U=RH_2$、
转置码关系与**单块**重量下界。本片补上混合块（两块同时非零）的"清洗/商"论证，
于是 HGP 的 X 距离下界对**任意**非平凡逻辑算符成立：

$$d_X \ge \min(d_1,\; d_2^\top),\qquad
d_1 = \min\ker H_1,\quad d_2^\top = \min\ker H_2^\top.$$

## 一、清洗引理（本片的核心）

设 $v = (U,R) \in \ker H_X$（即 $H_1U = RH_2$），记 $|v|$ 为重量。

* **行清洁**（`blockL_rows_mem_of_small`）：若 $|v| < d_1$，则 $U$ 的每一行都落在
  $H_2$ 的行空间中。
  证明：若某行 $U_{a\cdot}$ 与 $z\in\ker H_2$ 的点积非零，令 $x_a := U_{a\cdot}\cdot z$；
  由压缩恒等式 $H_1 x = 0$，而 $x \ne 0$ 且 $|x| \le |v| < d_1$——与"核向量重量 $\ge d_1$"矛盾。
* **列清洁**（`blockR_cols_mem_of_small`）：若 $|v| < d_2^\top$，则 $R$ 的每一列都在
  $H_1$ 的列空间中（对称论证，用 $w\in\ker H_1^\top$）。

两条都是**重量计数**论证：矛盾来自"核向量重量 $\ge$ 码距"与"该向量的支撑是 $v$ 支撑的
子集"这两件事的直接冲突——不需要任何枚举。

## 二、consistency（清洗证书）

行清洁给出 $C_0$ 使 $C_0H_2 = U$；列清洁给出 $\rho := R + H_1C_0$ 的每一列都在
$H_1$ 的列空间中，且 $\rho H_2 = 0$。本片证明（`exists_cleaning_cert`）：

$$\text{列都在 }\mathrm{col}(H_1)\text{ 中}\;\wedge\;\rho H_2 = 0
\;\Longrightarrow\; \exists D,\; H_1D = \rho \;\wedge\; DH_2 = 0.$$

**构造是显式的**：把 $\rho$ 的列用 `rowReduce`（`colList H₁`）读回（`col_decomp`），
系数取枢轴行的条目，再乘预像 `preimage`。

## 三、组装

$C := C_0 + D$ 同时满足 $CH_2 = U$ 与 $H_1C = R$，于是
$v = (CH_2,\, H_1C) = \sum_{a,d}C_{ad}\cdot(\text{row }(a,d)\text{ of }H_Z)$
落在 $\mathrm{row}\,H_Z$ 中（`sum_smul_hgpHZ_apply` + `mem_spanL_hgpHZ_of_blocks`）。

## 主结果

* `exists_ker_dot_ne_zero_of_not_mem` / `mem_spanL_of_forall_dot_eq_zero`：
  **分离引理**——行空间恰是核的正交补（构造性地用消元残差 + 核向量实现）。
* `blockL_rows_mem_of_small` / `blockR_cols_mem_of_small`：两条清洁引理。
* `exists_cleaning_cert`：清洗证书的一致性构造。
* **`hgp_X_distance_ge`**：$v\in\ker H_X$、$v\notin\mathrm{row}H_Z$、$v\ne0$
  $\Longrightarrow \min(d_1, d_2^\top) \le |v|$——X 型逻辑算符的通用下界，
  与第二片的单块下界（无需商即可用）互补。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 一、行 / 列列表与预像 -/

/-- 矩阵的行（作为 `Vec` 列表）。 -/
def matRowList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) : List (Vec k) :=
  List.ofFn fun i => fun j => M i j

/-- 矩阵的列（作为 `Vec` 列表，向量长度 = 行数）。 -/
def colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) : List (Vec m) :=
  matRowList M.transpose

lemma mem_matRowList {m k : ℕ} {M : Matrix (Fin m) (Fin k) (ZMod 2)} {y : Vec k} :
    y ∈ matRowList M ↔ ∃ i, (fun j => M i j) = y := by
  rw [matRowList, List.mem_ofFn]

/-- 列张成空间中的向量必是右乘的像（列就是单位向量在此映射下的像）。 -/
lemma exists_mulVec_of_mem_spanL_colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec m} (h : y ∈ spanL (colList M)) : ∃ x : Vec k, M *ᵥ x = y := by
  have h' : y ∈ Submodule.span (ZMod 2) {v : Vec m | v ∈ colList M} := h
  refine Submodule.span_induction (p := fun v _ => ∃ x : Vec k, M *ᵥ x = v)
    ?_ ?_ ?_ ?_ h'
  · intro v hv
    obtain ⟨i, hi⟩ := mem_matRowList.mp hv
    refine ⟨unitVec i, ?_⟩
    funext j
    rw [← congrFun hi j]
    rw [Matrix.mulVec, dotProduct]
    have hsum : (∑ b, M j b * unitVec i b) = M j i := by
      rw [Finset.sum_eq_single i]
      · rw [unitVec, ite_eq_left rfl, mul_one]
      · intro b _ hb
        rw [unitVec, ite_eq_right (fun h : b = i => hb h), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum]
    exact (Matrix.transpose_apply M i j).symm
  · exact ⟨0, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [Matrix.mulVec_add, ha, hb]⟩
  · intro c x _ hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by rw [Matrix.mulVec_smul, ha]⟩

/-- 右乘的像落在列张成空间中。 -/
lemma mulVec_mem_spanL_colList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (x : Vec k) :
    M *ᵥ x ∈ spanL (colList M) := by
  have hsum : M *ᵥ x = ∑ t : Fin k, x t • (fun i => M i t) := by
    funext i
    rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hsum]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  refine subset_spanL ?_
  rw [colList, matRowList, List.mem_ofFn]
  exact ⟨t, rfl⟩

/-- 行张成空间中的向量必是某个系数向量与各行作线性组合：`∃ λ, ∀ j, Σ_t λ_t M_{tj} = y_j`。 -/
lemma exists_coeff_of_mem_spanL_matRowList {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∈ spanL (matRowList M)) :
    ∃ co : Vec m, ∀ j, (∑ t, co t * M t j) = y j := by
  have h' : y ∈ Submodule.span (ZMod 2) {v : Vec k | v ∈ matRowList M} := h
  refine Submodule.span_induction
    (p := fun v _ => ∃ co : Vec m, ∀ j, (∑ t, co t * M t j) = v j) ?_ ?_ ?_ ?_ h'
  · intro v hv
    obtain ⟨i, hi⟩ := mem_matRowList.mp hv
    refine ⟨unitVec i, fun j => ?_⟩
    rw [← hi]
    have hsum : (∑ t, unitVec i t * M t j) = M i j := by
      rw [Finset.sum_eq_single i]
      · rw [unitVec, ite_eq_left rfl, one_mul]
      · intro b _ hb
        rw [unitVec, ite_eq_right (fun h : b = i => hb h), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum]
  · exact ⟨0, fun j => by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, fun j => ?_⟩
    change (∑ t, (a + b) t * M t j) = x j + y j
    rw [← ha j, ← hb j]
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.add_apply, add_mul]
  · intro c x _ hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨c • a, fun j => ?_⟩
    change (∑ t, (c • a) t * M t j) = c • (x j)
    rw [← ha j, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- 右乘的预像：`M *ᵥ preimage M y = y`（当 `y` 在列张成空间中时，见 `preimage_spec`）。 -/
noncomputable def preimage {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (y : Vec m) : Vec k :=
  if h : ∃ x : Vec k, M *ᵥ x = y then Classical.choose h else 0

lemma preimage_spec {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) {y : Vec m}
    (h : ∃ x : Vec k, M *ᵥ x = y) : M *ᵥ preimage M y = y := by
  rw [preimage, dite_eq_left h]
  exact Classical.choose_spec h

/-- **行分解**：`U` 的每一行都在 `M` 的行空间中 ⟹ `U = C * M`。 -/
lemma exists_mul_eq_of_rows_mem {m k p : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    (U : Matrix (Fin p) (Fin k) (ZMod 2))
    (h : ∀ a, (fun j => U a j) ∈ spanL (matRowList M)) :
    ∃ C : Matrix (Fin p) (Fin m) (ZMod 2), C * M = U := by
  classical
  choose c hc using fun a => exists_coeff_of_mem_spanL_matRowList M (h a)
  refine ⟨Matrix.of fun a t => c a t, ?_⟩
  ext a j
  rw [Matrix.mul_apply]
  simpa only [Matrix.of_apply] using hc a j

/-! ## 二、分离引理：行空间 = 核的正交补 -/

/-- 核向量与整个行空间正交。 -/
lemma dot_eq_zero_of_mem_kerL_of_mem_spanL {n : ℕ} {L : List (Vec n)} {z u : Vec n}
    (hz : z ∈ kerL L) (hu : u ∈ spanL L) : u ⬝ᵥ z = 0 := by
  refine Submodule.span_induction (p := fun u _ => u ⬝ᵥ z = 0) ?_ ?_ ?_ ?_ hu
  · intro v hv
    exact (mem_kerL.mp hz) v hv
  · simp
  · intro x y _ _ hx hy
    rw [add_dotProduct, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_dotProduct, hx, smul_zero]

/-- **分离引理**：不在行空间中的向量必与某个核向量点积非零。

构造是显式的：把 `y` 对消元输出约化，残差 `y'` 非零（否则 `y` 在行空间中）、
在枢轴列上为零；取 `y'` 非零的那个自由列 `j`，`kerVec D j` 就是所需的核向量
（它在自由列 `j` 上取 1、其余自由列取 0，而 `y'` 只在自由列上非零）。 -/
theorem exists_ker_dot_ne_zero_of_not_mem {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : y ∉ spanL (matRowList M)) :
    ∃ z : Vec k, M *ᵥ z = 0 ∧ y ⬝ᵥ z ≠ 0 := by
  classical
  set D : List (PivRow k) := rowReduce (matRowList M) with hD
  set y' : Vec k := reduceAgainst D y with hy'
  have hDred : IsReduced D := by rw [hD]; exact isReduced_rowReduce _
  have hy'mem : y + y' ∈ spanL (matRowList M) := by
    rw [hy', hD, ← spanL_rowReduce (matRowList M)]
    exact add_reduceAgainst_mem _ _
  have hy'0 : y' ≠ 0 := by
    intro hzero
    exact h (by rw [hzero, add_zero] at hy'mem; exact hy'mem)
  obtain ⟨j, hj⟩ : ∃ j, y' j ≠ 0 := by
    by_contra hcon
    refine hy'0 (funext fun j => ?_)
    by_contra hc
    exact hcon ⟨j, hc⟩
  have hfree : IsFreeCol D j := by
    by_contra hnf
    have hex : ∃ ri ∈ D, ri.2 = j := by simpa [IsFreeCol] using hnf
    obtain ⟨ri, hri, hrj⟩ := hex
    have hzero := reduceAgainst_apply_piv hDred y ri hri
    rw [hrj] at hzero
    exact hj hzero
  have hker : kerVec D j ∈ kerL (matRowList M) := by
    have h1 : kerVec D j ∈ kerL (rowList D) := kerVec_mem_kerL hDred j
    have h2 : kerL (rowList D) = kerL (matRowList M) := by
      apply kerL_eq_of_spanL_eq
      rw [hD]
      exact spanL_rowReduce (matRowList M)
    rwa [h2] at h1
  refine ⟨kerVec D j, ?_, ?_⟩
  · funext i
    rw [Matrix.mulVec, dotProduct]
    exact (mem_kerL.mp hker) (fun b => M i b) (by
      rw [matRowList, List.mem_ofFn]; exact ⟨i, rfl⟩)
  · intro hzero
    have hsplit : y = y' + (y + y') := by rw [add_add_same_right]
    have hdot : y ⬝ᵥ kerVec D j
        = y' ⬝ᵥ kerVec D j + (y + y') ⬝ᵥ kerVec D j := by
      calc y ⬝ᵥ kerVec D j = (y' + (y + y')) ⬝ᵥ kerVec D j :=
            congrArg (fun u => u ⬝ᵥ kerVec D j) hsplit
        _ = y' ⬝ᵥ kerVec D j + (y + y') ⬝ᵥ kerVec D j := by rw [add_dotProduct]
    have hsecond : (y + y') ⬝ᵥ kerVec D j = 0 :=
      dot_eq_zero_of_mem_kerL_of_mem_spanL hker hy'mem
    have hfirst : y' ⬝ᵥ kerVec D j = y' j := by
      rw [dotProduct]
      refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin k)))
        (f := fun b => y' b * kerVec D j b) j ?_ ?_).trans ?_
      · intro b _ hb
        by_cases hbfree : IsFreeCol D b
        · rw [kerVec_apply_free hbfree, ite_eq_right hb, mul_zero]
        · have hex : ∃ ri ∈ D, ri.2 = b := by simpa [IsFreeCol] using hbfree
          obtain ⟨ri, hri, hrb⟩ := hex
          rw [← hrb, hy', reduceAgainst_apply_piv hDred y ri hri, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ j) hnot
      · rw [kerVec_apply_free hfree, ite_eq_left rfl, mul_one]
    rw [hdot, hfirst, hsecond, add_zero] at hzero
    exact hj hzero

/-- **分离引理的判定形式**：与整个核正交的向量必在行空间中。 -/
theorem mem_spanL_of_forall_dot_eq_zero {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : ∀ z : Vec k, M *ᵥ z = 0 → y ⬝ᵥ z = 0) :
    y ∈ spanL (matRowList M) := by
  by_contra hmem
  obtain ⟨z, hz, hdot⟩ := exists_ker_dot_ne_zero_of_not_mem M hmem
  exact hdot (h z hz)

/-! ## 三、重量计数：逐行 / 逐列点积后重量不增 -/

/-- 逐行点积后的重量不超过全向量重量（每行非零就贡献一个支撑点）。 -/
lemma rowDot_hammingNorm_le
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (z : Vec n₂) :
    hammingNorm (fun a : Fin n₁ => ∑ b, v (Sum.inl (a, b)) * z b) ≤ hammingNorm v := by
  classical
  rcases isEmpty_or_nonempty (Fin n₂) with hemp | hne
  · show (Finset.univ.filter (fun a : Fin n₁ => (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    have hzero : ∀ a : Fin n₁, (∑ b : Fin n₂, v (Sum.inl (a, b)) * z b) = 0 :=
      fun a => Finset.sum_eq_zero fun b _ => (hemp.false b).elim
    simp only [hzero, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.zero_le]
  · obtain ⟨b₀⟩ := hne
    show (Finset.univ.filter (fun a : Fin n₁ => (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    let g : Fin n₁ → Fin n₂ := fun a =>
      if h : ∃ b, v (Sum.inl (a, b)) ≠ 0 then Classical.choose h else b₀
    refine Finset.card_le_card_of_injOn
      (fun a => (Sum.inl (a, g a) : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂))) ?_ ?_
    · intro a ha
      have hne : (∑ b, v (Sum.inl (a, b)) * z b) ≠ 0 := (Finset.mem_filter.mp ha).2
      have hex : ∃ b, v (Sum.inl (a, b)) ≠ 0 := by
        by_contra hcon
        exact hne (Finset.sum_eq_zero fun b _ => by
          have hb : v (Sum.inl (a, b)) = 0 := by by_contra hb'; exact hcon ⟨b, hb'⟩
          rw [hb, zero_mul])
      have hg : v (Sum.inl (a, g a)) ≠ 0 := by
        dsimp only [g]
        rw [dite_eq_left hex]
        exact Classical.choose_spec hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    · intro a _ a' _ h
      exact congrArg Prod.fst (Sum.inl_injective h)

/-- 逐列点积后的重量不超过全向量重量（每列非零就贡献一个支撑点）。 -/
lemma colDot_hammingNorm_le
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) (w : Vec r₁) :
    hammingNorm (fun t : Fin r₂ => ∑ i, v (Sum.inr (i, t)) * w i) ≤ hammingNorm v := by
  classical
  rcases isEmpty_or_nonempty (Fin r₁) with hemp | hne
  · show (Finset.univ.filter (fun t : Fin r₂ => (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    have hzero : ∀ t : Fin r₂, (∑ i : Fin r₁, v (Sum.inr (i, t)) * w i) = 0 :=
      fun t => Finset.sum_eq_zero fun i _ => (hemp.false i).elim
    simp only [hzero, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
      Nat.zero_le]
  · obtain ⟨i₀⟩ := hne
    show (Finset.univ.filter (fun t : Fin r₂ => (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0)).card
      ≤ (Finset.univ.filter (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => v c ≠ 0)).card
    let g : Fin r₂ → Fin r₁ := fun t =>
      if h : ∃ i, v (Sum.inr (i, t)) ≠ 0 then Classical.choose h else i₀
    refine Finset.card_le_card_of_injOn
      (fun t => (Sum.inr (g t, t) : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂))) ?_ ?_
    · intro t ht
      have hne : (∑ i, v (Sum.inr (i, t)) * w i) ≠ 0 := (Finset.mem_filter.mp ht).2
      have hex : ∃ i, v (Sum.inr (i, t)) ≠ 0 := by
        by_contra hcon
        exact hne (Finset.sum_eq_zero fun i _ => by
          have hi : v (Sum.inr (i, t)) = 0 := by by_contra hi'; exact hcon ⟨i, hi'⟩
          rw [hi, zero_mul])
      have hg : v (Sum.inr (g t, t)) ≠ 0 := by
        dsimp only [g]
        rw [dite_eq_left hex]
        exact Classical.choose_spec hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    · intro t _ t' _ h
      exact congrArg Prod.snd (Sum.inr_injective h)

/-! ## 四、清洗引理 -/

/-- **行清洁**：$|v| < d_1$ 时 `blockL v` 的每一行都落在 `H₂` 的行空间中。

证明用压缩恒等式的**矩阵级**形态：若某行与 `z ∈ ker H₂` 的点积非零，则
`blockL v *ᵥ z ≠ 0`，而 `H₁ *ᵥ (blockL v *ᵥ z) = (H₁ * blockL v) *ᵥ z
= (blockR v * H₂) *ᵥ z = blockR v *ᵥ (H₂ *ᵥ z) = 0`——它与 `d₁` 矛盾。 -/
theorem blockL_rows_mem_of_small
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₁) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by
  refine mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => ?_
  by_contra hne
  let u : Vec n₁ := fun a => ∑ b, blockL v a b * z b
  have hu_eq : u = blockL v *ᵥ z := rfl
  have hxzero : H₁ *ᵥ u = 0 := by
    rw [hu_eq, Matrix.mulVec_mulVec, hcomp, ← Matrix.mulVec_mulVec, hz]
    simp
  have hxne : u ≠ 0 := by
    intro hzero
    refine hne ?_
    rw [dotProduct]
    have h1 : u a = 0 := by rw [hzero]; rfl
    exact h1
  have hge : d₁ ≤ hammingNorm u := hd₁ _ hxne hxzero
  have hle : hammingNorm u ≤ hammingNorm v := rowDot_hammingNorm_le v z
  omega

/-- **列清洁**：$|v| < d_2^\top$ 时 `blockR v` 的每一列都落在 `H₁` 的列空间中。

对偶的矩阵级论证：`(blockR v)ᵀ *ᵥ w` 的转置码恒等式给出
`H₂ᵀ *ᵥ ((blockR v)ᵀ *ᵥ w) = (blockL v)ᵀ *ᵥ (H₁ᵀ *ᵥ w) = 0`。 -/
theorem blockR_cols_mem_of_small
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₂T) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by
  rw [colList]
  refine mem_spanL_of_forall_dot_eq_zero H₁.transpose fun w hw => ?_
  by_contra hne
  let y : Vec r₂ := fun t => ∑ i, blockR v i t * w i
  have hy_eq : y = (blockR v).transpose *ᵥ w := rfl
  have hyzero : H₂.transpose *ᵥ y = 0 := by
    rw [hy_eq, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hcomp, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, hw]
    simp
  have hyne : y ≠ 0 := by
    intro hzero
    refine hne ?_
    rw [dotProduct]
    have h1 : y t = 0 := by rw [hzero]; rfl
    exact h1
  have hge : d₂T ≤ hammingNorm y := hd₂ _ hyne hyzero
  have hle : hammingNorm y ≤ hammingNorm v := colDot_hammingNorm_le v w
  omega

/-! ## 五、consistency：列分解与清洗证书 -/

/-- **列分解**（消元读回）：若 `M` 的每一列都在行列表 `c` 的生成空间中，
则消元输出的枢轴行给出一组显式系数：`M i j = Σ_{ri} M ri.2 j * ri.1 i`。 -/
lemma col_decomp {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (c : List (Vec m))
    (hc : ∀ j : Fin k, (fun i => M i j) ∈ spanL c) (i : Fin m) (j : Fin k) :
    M i j = ∑ ri ∈ (rowReduce c).toFinset, (M ri.2 j) * (ri.1 i) := by
  have hmem : (fun i => M i j) ∈ spanL (rowList (rowReduce c)) := by
    rw [spanL_rowReduce]
    exact hc j
  have h := congrFun (readOff_eq_of_mem_spanL (isReduced_rowReduce c) hmem) i
  rw [readOff_apply] at h
  exact h.symm

/-- **清洗证书（consistency）**：列都在 `H₁` 列空间中、且 `ρ H₂ = 0` 的矩阵 `ρ`
可写成 `H₁ D`（且 `D H₂ = 0`）——即"可清洗"。

构造：`D = Σ_{ri} preimage(ri.1) ⊗ (ρ 的第 ri.2 行)`，
其中 `ri` 取遍 `rowReduce (colList H₁)` 的枢轴行（`col_decomp` 给出系数）。 -/
theorem exists_cleaning_cert {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)} {ρ : Matrix (Fin r₁) (Fin r₂) (ZMod 2)}
    (hcol : ∀ j, (fun i => ρ i j) ∈ spanL (colList H₁))
    (hrow : ρ * H₂ = 0) :
    ∃ D : Matrix (Fin n₁) (Fin r₂) (ZMod 2), H₁ * D = ρ ∧ D * H₂ = 0 := by
  classical
  have hmem : ∀ ri ∈ rowReduce (colList H₁), ri.1 ∈ spanL (colList H₁) := by
    intro ri hri
    have h1 : ri.1 ∈ spanL (rowList (rowReduce (colList H₁))) :=
      subset_spanL (by rw [rowList]; exact List.mem_map_of_mem hri)
    rwa [spanL_rowReduce] at h1
  refine ⟨Matrix.of fun a j => ∑ ri ∈ (rowReduce (colList H₁)).toFinset,
    ρ ri.2 j * (preimage H₁ ri.1) a, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ ri ∈ (rowReduce (colList H₁)).toFinset,
        (∑ a, H₁ i a * (ρ ri.2 j * (preimage H₁ ri.1) a)) = ρ ri.2 j * ri.1 i := by
      intro ri hri
      have hpre : H₁ *ᵥ preimage H₁ ri.1 = ri.1 :=
        preimage_spec H₁ (exists_mulVec_of_mem_spanL_colList H₁
          (hmem ri (List.mem_toFinset.mp hri)))
      have hstep : (∑ a, H₁ i a * (ρ ri.2 j * (preimage H₁ ri.1) a))
          = ρ ri.2 j * (H₁ *ᵥ preimage H₁ ri.1) i := by
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hstep, hpre]
    rw [Finset.sum_congr rfl hinner]
    exact (col_decomp ρ (colList H₁) hcol i j).symm
  · ext a t
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ri _ => ?_
    have hstep : (∑ j, (ρ ri.2 j * (preimage H₁ ri.1) a) * H₂ j t)
        = (preimage H₁ ri.1) a * (ρ * H₂) ri.2 t := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hstep, hrow]
    simp

/-! ## 六、组装：`H_Z` 行的组合与主定理 -/

/-- `(C H₂, H₁ C)` 形式的向量是 `H_Z` 各行的线性组合（逐条目计算）。 -/
theorem sum_smul_hgpHZ_apply (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (C : Matrix (Fin n₁) (Fin r₂) (ZMod 2))
    (c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) :
    (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p) c
      = Sum.elim (fun ab => (C * H₂) ab.1 ab.2) (fun st => (H₁ * C) st.1 st.2) c := by
  rw [Finset.sum_apply]
  rcases c with ab | st
  · obtain ⟨a, b⟩ := ab
    simp only [Pi.smul_apply, smul_eq_mul, hgpHZ_inl]
    change (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 * ((if p.1 = a then 1 else 0) * H₂ p.2 b))
      = (C * H₂) a b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hstep : ∀ a' : Fin n₁, (∑ d, C a' d * ((if a' = a then 1 else 0) * H₂ d b))
        = (if a' = a then 1 else 0) * (∑ d, C a' d * H₂ d b) := by
      intro a'
      have hterm : ∀ d : Fin r₂, C a' d * ((if a' = a then 1 else 0) * H₂ d b)
          = (if a' = a then 1 else 0) * (C a' d * H₂ d b) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a' _ => hstep a']
    rw [Finset.sum_eq_single a]
    · rw [ite_eq_left rfl, one_mul]
    · intro a' _ ha'
      rw [ite_eq_right (fun h : a' = a => ha' h), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · obtain ⟨s, t⟩ := st
    simp only [Pi.smul_apply, smul_eq_mul, hgpHZ_inr]
    change (∑ p : Fin n₁ × Fin r₂, C p.1 p.2 * (H₁ s p.1 * (if p.2 = t then 1 else 0)))
      = (H₁ * C) s t
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hstep : ∀ a' : Fin n₁, (∑ d, C a' d * (H₁ s a' * (if d = t then 1 else 0)))
        = H₁ s a' * C a' t := by
      intro a'
      have hterm : ∀ d : Fin r₂, C a' d * (H₁ s a' * (if d = t then 1 else 0))
          = H₁ s a' * (C a' d * (if d = t then 1 else 0)) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => hterm d]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_eq_single t]
      · rw [ite_eq_left rfl, mul_one]
      · intro d _ hd
        rw [ite_eq_right (fun h : d = t => hd h), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ t) h
    rw [Finset.sum_congr rfl fun a' _ => hstep a']

/-- 两块分别是 `C H₂` 与 `H₁ C` 的向量落在 `H_Z` 的行空间中
（与 LeanQEC 的 `Matrix.rowSpace` 同一对象）。 -/
theorem mem_rowSpace_hgpHZ_of_blocks {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    {C : Matrix (Fin n₁) (Fin r₂) (ZMod 2)}
    (hU : blockL v = C * H₂) (hR : blockR v = H₁ * C) :
    v ∈ (hgpHZ H₁ H₂).rowSpace := by
  have hv : v = ∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p := by
    funext c
    rw [sum_smul_hgpHZ_apply]
    rcases c with ab | st
    · obtain ⟨a, b⟩ := ab
      rw [← hU]
      rfl
    · obtain ⟨s, t⟩ := st
      rw [← hR]
      rfl
  rw [hv]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨p, rfl⟩

/-- **HGP 的 X 距离下界（清洗定理）**：不在 `H_Z` 行空间中的非零 X 型算符
（即非平凡 X 型逻辑算符）的重量至少是 $\min(d_1, d_2^\top)$——
左码距与转置码距的较小者。

与第二片的单块下界互补：那两条不需要"不在行空间"这一假设，
本定理对**混合块**（两块同时非零）也成立，代价是要在商里陈述。 -/
theorem hgp_X_distance_ge (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₁ d₂T : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w) :
    min d₁ d₂T ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  have hsmall₁ : hammingNorm v < d₁ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hsmall₂ : hammingNorm v < d₂T := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨C₀, hC₀⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v)
    (fun a => blockL_rows_mem_of_small hcomp hd₁ hsmall₁ a)
  have hcol : ∀ j, (fun i => (blockR v + H₁ * C₀) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C₀) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact blockR_cols_mem_of_small (H₁ := H₁) (H₂ := H₂) hcomp hd₂ hsmall₂ j
    · change H₁ *ᵥ (fun t => C₀ t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C₀ t j)
  have hrowρ : (blockR v + H₁ * C₀) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C₀ * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C₀ * H₂ = H₁ * (C₀ * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC₀, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcol hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C₀ + D) ?_ ?_
  · rw [Matrix.add_mul, hC₀, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm

/-! ## 六、清洗下界的两条前提**各自可以卸掉**：只有一条路线算数

清洗下界 `hgp_X_distance_ge` 的两步各要一个**重量前提**：行清洁要 $|v|<d_1$、列清洁要
$|v|<d_2^\top$。本节证明**每一步都能换成一条核条件**，于是下界只剩一个因子：

* **行清洁**（`blockL v` 的行落在 $H_2$ 的行空间中）在 $\ker H_1=0$ **或** $\ker H_2=0$ 时
  **无条件**成立。前者是**单射**：该步的恒等式把 $u:=U z$ 映到 $H_1u=0$，于是 $u=0$；
  后者使该步要证的正交性**空真**（$\ker H_2$ 里只有 $0$）。
* **列清洁**（`blockR v` 的列落在 $H_1$ 的列空间中）对称地由 $\ker H_1^\top=0$（列空间已满）
  **或** $\ker H_2^\top=0$（$y:=R^\top w$ 被 $H_2^\top y=0$ 与单射钉成 $0$）卸掉。

四条距离定理是本节的产出：前两条给 $d_2^\top\le|v|$（此时 $d_1$ 那个因子**不参与**），
后两条给 $d_1\le|v|$（$d_2^\top$ 不参与）。**这正是"某条路线的证书核平凡"那一类**：
§十七（`Codes/HGPGeneralWitness.lean`）用它把 C1 的"$\ge$"那一半在残余类上闭合。 -/

/-! ### 六之一：四条"清洁步可卸"的引理 -/

/-- **行清洁（$\ker H_1=0$ 支）**：$H_1$ 单射时 `blockL v` 的每一行**无条件**落在 $H_2$ 的行空间中。

与 `blockL_rows_mem_of_small` 同构，但把"与 $d_1$ 矛盾"那一步换成**单射**：该步的恒等式
已经把 $u:=U z$ 送到 $\ker H_1$ 里，于是 $u=0$——不需要 $u$ 非零、也不需要重量前提。 -/
theorem blockL_rows_mem_of_H1Ker_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by
  refine mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => ?_
  have hzero : blockL v *ᵥ z = 0 := hT _ (by
    rw [Matrix.mulVec_mulVec, hcomp, ← Matrix.mulVec_mulVec, hz]
    simp)
  have := congrFun hzero a
  rw [dotProduct]
  exact this

/-- **行清洁（$\ker H_2=0$ 支）**：$H_2$ 单射时正交性假设**空真**——要证的
$\langle U_{a\cdot},z\rangle=0$ 只对 $z\in\ker H_2$ 提出，而那里只有 $z=0$。
（因此这一支**不需要**压缩恒等式：结论只谈 `blockL v` 与 $H_2$。） -/
theorem blockL_rows_mem_of_H2Ker_trivial
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) :=
  mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => by
    rw [hT z hz]
    simp [dotProduct]

/-- **列清洁（$\ker H_1^\top=0$ 支）**：此时 $H_1$ 的列已张满整个 `Vec r₁`，结论**无条件**成立。
（同样**不需要**压缩恒等式。） -/
theorem blockR_cols_mem_of_adjoint_ker_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) :=
  mem_spanL_of_forall_dot_eq_zero H₁.transpose fun z hz => by
    rw [hT z hz]
    simp [dotProduct]

/-- **列清洁（$\ker H_2^\top=0$ 支）**：与 `blockR_cols_mem_of_small` 同构，但把"与 $d_2^\top$
矛盾"换成**单射**：恒等式已把 $y:=R^\top w$ 送进 $\ker H_2^\top$，于是 $y=0$。 -/
theorem blockR_cols_mem_of_H2TKer_trivial
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by
  rw [colList]
  refine mem_spanL_of_forall_dot_eq_zero H₁.transpose fun w hw => ?_
  have hyzero : H₂.transpose *ᵥ ((blockR v).transpose *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hcomp, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, hw]
    simp
  have hy := hT _ hyzero
  have hy' : ∀ t, ((blockR v).transpose *ᵥ w) t = 0 := fun t => by
    simpa using congrFun hy t
  rw [dotProduct]
  exact hy' t

/-! ### 六之二：两条装配定理（各卸掉一步） -/

/-- **行清洁已自由时的清洗下界**：只要 `blockL v` 的行**无条件**落在 $H_2$ 的行空间中，
$d_2^\top$ 一个因子就够——余下与 `hgp_X_distance_ge` 逐字相同（列清洁仍用 $|v|<d_2^\top$）。 -/
theorem hgp_X_distance_ge_of_rowClean_free
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hrow : ∀ a, (fun b => blockL v a b) ∈ spanL (matRowList H₂)) :
    d₂T ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  obtain ⟨C, hC⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v) hrow
  have hrowρ : (blockR v + H₁ * C) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C * H₂ = H₁ * (C * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcolρ : ∀ j, (fun i => (blockR v + H₁ * C) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact blockR_cols_mem_of_small hcomp hd₂ hlt j
    · change H₁ *ᵥ (fun t => C t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C t j)
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcolρ hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C + D) ?_ ?_
  · rw [Matrix.add_mul, hC, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm

/-- **列清洁已自由时的清洗下界**：只要 `blockR v` 的列**无条件**落在 $H_1$ 的列空间中，
$d_1$ 一个因子就够（行清洁仍用 $|v|<d_1$）。 -/
theorem hgp_X_distance_ge_of_colClean_free
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hcol : ∀ t, (fun i => blockR v i t) ∈ spanL (colList H₁)) :
    d₁ ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  obtain ⟨C, hC⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v)
    (fun a => blockL_rows_mem_of_small hcomp hd₁ hlt a)
  have hrowρ : (blockR v + H₁ * C) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C * H₂ = H₁ * (C * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcolρ : ∀ j, (fun i => (blockR v + H₁ * C) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact hcol j
    · change H₁ *ᵥ (fun t => C t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C t j)
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcolρ hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C + D) ?_ ?_
  · rw [Matrix.add_mul, hC, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm

/-! ### 六之三：四条距离定理 -/

/-- **$d_X$ 的下界（$\ker H_1=0$ 支）**：$H_1$ 单射时 $d_2^\top$ 一个因子就够。 -/
theorem hgp_X_distance_ge_of_H1Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) :
    d₂T ≤ hammingNorm v :=
  hgp_X_distance_ge_of_rowClean_free H₁ H₂ hv hlog hd₂ fun a =>
    blockL_rows_mem_of_H1Ker_trivial (H₁ := H₁) (H₂ := H₂)
      ((hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv) hT a

/-- **$d_X$ 的下界（$\ker H_2=0$ 支）**：$H_2$ 单射时 $d_2^\top$ 一个因子就够。 -/
theorem hgp_X_distance_ge_of_H2Ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hT : ∀ u : Vec n₂, H₂ *ᵥ u = 0 → u = 0) :
    d₂T ≤ hammingNorm v :=
  hgp_X_distance_ge_of_rowClean_free H₁ H₂ hv hlog hd₂ fun a =>
    blockL_rows_mem_of_H2Ker_trivial (H₂ := H₂) hT a

/-- **$d_X$ 的下界（$\ker H_2^\top=0$ 支）**：$H_2^\top$ 单射时 $d_1$ 一个因子就够。 -/
theorem hgp_X_distance_ge_of_H2TKer_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v :=
  hgp_X_distance_ge_of_colClean_free H₁ H₂ hv hlog hd₁ fun t =>
    blockR_cols_mem_of_H2TKer_trivial (H₁ := H₁) (H₂ := H₂)
      ((hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv) hT t

/-- **$d_X$ 的下界，证书核平凡的那一支**：若 $\ker H_1^\top = 0$，则任何 X 型逻辑算符的重量
$\ge d_1$。

**它补的是哪一格**：清洗下界 `hgp_X_distance_ge` 给的是 $\min(d_1,d_2^\top)$，而 $d_2^\top$ 可能
**严格更小却取不到**——"右路线的证书核平凡"（$\ker H_1^\top=0$）正是那个情形。本定理说，此时
那个更小的值**不参与**下界，$d_1$ 一个就够。

**证明**（与清洗下界同构，但只用**行清洁**加一条**满射性**）：设 $|v|<d_1$。
行清洁给 $U = C\,H_2$（$U$ 是 `blockL v`），于是余项 $\rho := R + H_1C$ 满足 $\rho H_2 = 0$。
而 $\ker H_1^\top = 0$ 经分离引理 `mem_spanL_of_forall_dot_eq_zero` 给 **$H_1$ 列满射**
（每个 `Vec r₁` 向量都落在 $\mathrm{colList}\,H_1$ 的张成里），故 $\rho$ 的每一列也在那里——
两条件齐备，`exists_cleaning_cert` 给出 $D$ 使 $H_1D = \rho$、$DH_2 = 0$，
于是 $v$ 与 $(C+D)$ 配成稳定子、落在行空间里，与"$v$ 不是逻辑算符"矛盾。 -/
theorem hgp_X_distance_ge_of_adjoint_ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).rowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v :=
  hgp_X_distance_ge_of_colClean_free H₁ H₂ hv hlog hd₁ fun t =>
    blockR_cols_mem_of_adjoint_ker_trivial (H₁ := H₁) hT t

end QECCertificates
