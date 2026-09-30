/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.HGPKunneth
import QECCertificates.GF2.HGPCleaning
import QECCertificates.GF2.HGPCleaningDual

/-!
# HGP 族 $n\ge144$ 实例与环面族全族定理（路线图 F 节点）

`GF2/HGPKunneth`（维数张量公式）与 `GF2/HGPCleaning(±Dual)`（两侧距离下界）
给出的是**族级**结构定理。本模块把它们实例化到 $m$-圈种子 $\mathrm{cyc}_m$
的超图积上：$m=9$ 得 $[[162,2,9]]$、$m=12$ 得 $[[288,2,12]]$、$m=16$ 得
$[[512,2,16]]$，且进一步给出**全族定理** `hgp_toric_family`：对任意
$m\ge2$，HGP($\mathrm{cyc}_m$,$\mathrm{cyc}_m$) 是 $[[\,2m^2,\,2,\,m\,]]$——
种子三事实（行和为偶、秩 $m-1$、两个方向的核最小重量 $m$）由**核常值性**
（`cycMat_ker_const`：行方程 $w_i+w_{i+1}=0$ 在特征 2 下沿链传递 ⟹ 核向量
必为常值）结构化给出，**零枚举、对每个 $m$ 成立**。全程不做任何
宽度 $\ge100$ 的求秩或枚举，证书量级 $O(m^2)$：

* **维数 $k=2$**（`hgp_toric9_k` / `hgp_toric12_k`）：Künneth 公式只需要
  $m\times m$ 种子矩阵的秩，$162$（或 $288$）宽大矩阵的秩从不计算；
* **两侧距离下界 $d\ge m$**（`hgp_toric9_dx_lb` 等）：清洗定理只需要种子
  核最小重量（$2^m$ 空间上的 `by decide`）；
* **witness 上界 $d\le m$**（`hgp_toric9_X_logical` 等）：显式重量-$m$ 逻辑
  算符——核成员经压缩恒等式化归为两个 $m\times m$ 分块等式，非成员经
  **一般索引的对偶见证**（`not_mem_rowSpace_of_ker_dot`，本模块新增：
  `GF2/LowerBound.lean` 的同名 Fin 版不覆盖积/和索引）由一条点积证书给出。

这也是与 QECLean 在 $[[144,12,12]]$ 上枚举式证据的**形态对照**：
$n\ge144$ 时逐算符枚举（$\sum_{k<d}\binom nk$）在内核内不可行，
而结构化断言的证书仍是 $O(m^2)$。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、一般索引的对偶见证引理 -/

/-- **对偶见证（任意索引版）**：若 `w` 与 `M` 的每一行正交（`M *ᵥ w = 0`），
而 `w ⬝ᵥ E = 1`，则 `E` 不在 `M` 的行空间中。

`GF2/LowerBound.lean` 的 `not_mem_rowSpace_of_dualCheck` 限定行/列索引为
`Fin`；HGP 校验矩阵的索引是积/和类型，这里给出可直接使用的一般版本。
证明即"行空间里的向量与核正交"：把 `E` 按 `M` 的行展开后逐项配对即塌缩为
`∑ cᵢ·(M *ᵥ w)ᵢ = 0`，与点积为 1 矛盾。 -/
theorem not_mem_rowSpace_of_ker_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod 2)) {E w : κ → ZMod 2}
    (hker : M *ᵥ w = 0) (hdot : w ⬝ᵥ E = 1) : E ∉ M.rowSpace := by
  intro hmem
  have hspan : E ∈ Submodule.span (ZMod 2) (Set.range M) := hmem
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := M) (x := E)).mp hspan
  -- E 的逐坐标展开
  have hc' : ∑ i, c i • (fun j => M i j) = E := hc
  have hcoord : ∀ j, E j = ∑ i, c i * M i j := by
    intro j
    have hj : (∑ i, c i • (fun j' => M i j')) j = E j := congrFun hc' j
    rw [← hj, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  -- 点积交换求和序后逐项为零
  have hexpand : ∀ j, w j * E j = ∑ i, w j * (c i * M i j) := by
    intro j; rw [hcoord j, Finset.mul_sum]
  have h1 : w ⬝ᵥ E = ∑ j, ∑ i, w j * (c i * M i j) := by
    rw [dotProduct, Finset.sum_congr rfl (fun j _ => hexpand j)]
  have h2 : ∑ j, ∑ i, w j * (c i * M i j) = ∑ i, ∑ j, c i * (M i j * w j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∀ i, ∑ j, c i * (M i j * w j) = c i * ((M *ᵥ w) i) := by
    intro i
    have hv : ((M *ᵥ w) i) = ∑ j, M i j * w j := rfl
    rw [hv, ← Finset.mul_sum]
  have hzero : ∀ i, c i * ((M *ᵥ w) i) = 0 := by
    intro i; rw [congrFun hker i]; simp
  rw [h1, h2, Finset.sum_congr rfl (fun i _ => h3 i)] at hdot
  rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const_zero] at hdot
  exact absurd hdot (by simp)

/-! ## 二、$m$-圈种子与环面族 witness（通用定义） -/

/-- **$m$-圈关联矩阵** $\mathrm{cyc}_m$：第 $i$ 行在第 $i$ 与第 $i{+}1$
（模 $m$）列为 1——每行恰两个 1（行和为偶），秩为 $m-1$，核由全 1 向量
张成。$\mathrm{HGP}(\mathrm{cyc}_m,\mathrm{cyc}_m)$ 即 $m\times m$ 环面码
$[[2m^2, 2, m]]$（$m=3$ 时为案例矩阵的 toric3，见 `Codes/HGPAnchor.lean`）。 -/
def cycMat (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j => if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m then 1 else 0

/-- **X 型 witness**：左半块（$n_1\times n_2$ 格点）上第 $0$ 列全 1、
右半块全 0——环面上沿一个方向的闭环，重量 $m$。 -/
def hgpToricXW (m : ℕ) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun ab => if (ab.2 : ℕ) = 0 then 1 else 0) (fun _ => 0)

/-- **Z 型 witness**：左半块上第 $0$ 行全 1、右半块全 0——沿另一方向的
闭环，与 `hgpToricXW` 恰在一个格点相交（点积为 1）。 -/
def hgpToricZW (m : ℕ) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun ab => if (ab.1 : ℕ) = 0 then 1 else 0) (fun _ => 0)

/-! ## 三、witness 的结构化核成员（对任意 $m$，只依赖"行和为偶"） -/

/-- X 型 witness 的右半块为空（定义性事实）。 -/
theorem blockR_toricXW_zero (m : ℕ) : blockR (hgpToricXW m) = 0 := by
  ext s t; rfl

/-- Z 型 witness 的右半块为空（定义性事实）。 -/
theorem blockR_toricZW_zero (m : ℕ) : blockR (hgpToricZW m) = 0 := by
  ext s t; rfl

/-- X 型 witness 左半块被 $\mathrm{cyc}_m$ 作用为零：每一列要么是全 1
（被"行和为偶"杀死）要么是零。 -/
theorem cycMat_mul_blockL_XW {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    cycMat m * blockL (hgpToricXW m) = 0 := by
  ext i j
  change ∑ a : Fin m, cycMat m i a * hgpToricXW m (Sum.inl (a, j)) = 0
  by_cases hj : (j : ℕ) = 0
  · have he : ∀ a : Fin m, cycMat m i a * hgpToricXW m (Sum.inl (a, j)) = cycMat m i a * 1 := by
      intro a; congr 1; simp [hgpToricXW, hj]
    rw [Finset.sum_congr rfl (fun a _ => he a)]
    exact congrFun hone i
  · have he : ∀ a : Fin m, cycMat m i a * hgpToricXW m (Sum.inl (a, j)) = 0 := by
      intro a; simp [hgpToricXW, hj]
    rw [Finset.sum_congr rfl (fun a _ => he a), Finset.sum_const_zero]

/-- Z 型 witness 左半块右乘 $\mathrm{cyc}_m^\top$ 为零：每一行要么是全 1
（转置不改行和）要么是零。 -/
theorem blockL_ZW_mul_transpose {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    blockL (hgpToricZW m) * (cycMat m).transpose = 0 := by
  ext a d
  change ∑ b : Fin m, hgpToricZW m (Sum.inl (a, b)) * cycMat m d b = 0
  by_cases ha : (a : ℕ) = 0
  · have he : ∀ b : Fin m, hgpToricZW m (Sum.inl (a, b)) * cycMat m d b
        = cycMat m d b * 1 := by
      intro b
      rw [mul_comm (hgpToricZW m (Sum.inl (a, b)))]
      congr 1; simp [hgpToricZW, ha]
    rw [Finset.sum_congr rfl (fun b _ => he b)]
    exact congrFun hone d
  · have he : ∀ b : Fin m, hgpToricZW m (Sum.inl (a, b)) * cycMat m d b = 0 := by
      intro b; simp [hgpToricZW, ha]
    rw [Finset.sum_congr rfl (fun b _ => he b), Finset.sum_const_zero]

/-- **X 型 witness 是 X 校验的核向量**（压缩恒等式 + 两个分块事实）。 -/
theorem toricXW_ker {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    hgpHX (cycMat m) (cycMat m) *ᵥ hgpToricXW m = 0 := by
  rw [hgpHX_mulVec_eq_zero_iff, cycMat_mul_blockL_XW hone, blockR_toricXW_zero, zero_mul]

/-- **Z 型 witness 是 Z 校验的核向量**。 -/
theorem toricZW_ker {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    hgpHZ (cycMat m) (cycMat m) *ᵥ hgpToricZW m = 0 := by
  rw [hgpHZ_mulVec_eq_zero_iff, blockL_ZW_mul_transpose hone, blockR_toricZW_zero,
    Matrix.mul_zero]

/-! ## 四、族级组装器：种子三事实 ⟹ HGP 环面实例参数 -/

/-- **族级维数**：种子秩 $m-1$ ⟹ $\mathrm{HGP}(\mathrm{cyc}_m,\mathrm{cyc}_m)$
的逻辑比特数 $k = (m-(m-1))^2 + (m-(m-1))^2 = 2$（Künneth 公式，
大矩阵的秩从不计算）。 -/
theorem hgp_toric_k {m : ℕ} (hm : 1 ≤ m) (hrank : (cycMat m).rank = m - 1) :
    (m * m + m * m) - (hgpHX (cycMat m) (cycMat m)).rank
      - (hgpHZ (cycMat m) (cycMat m)).rank = 2 := by
  rw [hgp_kunneth, hrank]
  have h1 : m - (m - 1) = 1 := by omega
  rw [h1]

/-- **族级 X 距离下界**：种子核最小重量 $m$（两个方向）⟹ 任何非平凡
X 型逻辑算符重量 $\ge m$（清洗定理）。 -/
theorem hgp_toric_dx_lb {m : ℕ}
    (hmin : ∀ w : Vec m, w ≠ 0 → cycMat m *ᵥ w = 0 → m ≤ hammingNorm w)
    (hminT : ∀ w : Vec m, w ≠ 0 → (cycMat m).transpose *ᵥ w = 0 → m ≤ hammingNorm w)
    {v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2}
    (hv : hgpHX (cycMat m) (cycMat m) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace) :
    m ≤ hammingNorm v := by
  have h := hgp_X_distance_ge (cycMat m) (cycMat m) hv hlog hmin hminT
  rwa [min_self] at h

/-- **族级 Z 距离下界**。 -/
theorem hgp_toric_dz_lb {m : ℕ}
    (hmin : ∀ w : Vec m, w ≠ 0 → cycMat m *ᵥ w = 0 → m ≤ hammingNorm w)
    (hminT : ∀ w : Vec m, w ≠ 0 → (cycMat m).transpose *ᵥ w = 0 → m ≤ hammingNorm w)
    {v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2}
    (hv : hgpHZ (cycMat m) (cycMat m) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace) :
    m ≤ hammingNorm v := by
  have h := hgp_Z_distance_ge (cycMat m) (cycMat m) hv hlog hminT hmin
  rwa [min_self] at h

/-- **族级 witness 非成员**：X 型 witness 不在 Z 校验行空间中，证书是
Z witness 的核成员 + 一条点积。 -/
theorem toricXW_not_mem {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0)
    (hdot : hgpToricXW m ⬝ᵥ hgpToricZW m = 1) :
    hgpToricXW m ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace := by
  refine not_mem_rowSpace_of_ker_dot _ (toricZW_ker hone) ?_
  rw [dotProduct_comm]; exact hdot

/-- **族级 witness 非成员（Z 侧）**。 -/
theorem toricZW_not_mem {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0)
    (hdot : hgpToricXW m ⬝ᵥ hgpToricZW m = 1) :
    hgpToricZW m ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace :=
  not_mem_rowSpace_of_ker_dot _ (toricXW_ker hone) hdot

/-! ## 五、实例一：$m=9$，$[[162,2,9]]$ -/

/-- 种子行和为偶（全 1 向量在核中）。 -/
theorem cyc9_one_ker : cycMat 9 *ᵥ (fun _ : Fin 9 => 1) = 0 := by decide

/-- 种子秩为 $8$。 -/
theorem rank_cyc9 : (cycMat 9).rank = 8 := by
  rw [Matrix.rank_eq_length_rowReduce]; decide

/-- 种子核最小重量为 $9$（$2^9$ 空间逐向量核出）。 -/
theorem cyc9_ker_min : ∀ w : Vec 9, w ≠ 0 → cycMat 9 *ᵥ w = 0 →
    9 ≤ hammingNorm w := by decide

/-- 种子转置核最小重量为 $9$。 -/
theorem cyc9T_ker_min : ∀ w : Vec 9, w ≠ 0 → (cycMat 9).transpose *ᵥ w = 0 →
    9 ≤ hammingNorm w := by decide

/-- 两个 witness 的点积恰为 1（各 162 项的求和，逐项核出）。 -/
theorem toric9_dot : hgpToricXW 9 ⬝ᵥ hgpToricZW 9 = 1 := by decide

/-- X 型 witness 重量为 9。 -/
theorem toric9_XW_weight : hammingNorm (hgpToricXW 9) = 9 := by decide

/-- Z 型 witness 重量为 9。 -/
theorem toric9_ZW_weight : hammingNorm (hgpToricZW 9) = 9 := by decide

/-- 码长 $n = 81 + 81 = 162$。 -/
theorem toric9_n : Fintype.card ((Fin 9 × Fin 9) ⊕ (Fin 9 × Fin 9)) = 162 := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **$[[162,2,9]]$ 之 $k$**：$\mathrm{HGP}(\mathrm{cyc}_9,\mathrm{cyc}_9)$
的逻辑比特数为 2（Künneth + 种子秩 8；宽度 162 的矩阵秩从不计算）。 -/
theorem hgp_toric9_k :
    (9 * 9 + 9 * 9) - (hgpHX (cycMat 9) (cycMat 9)).rank
      - (hgpHZ (cycMat 9) (cycMat 9)).rank = 2 :=
  hgp_toric_k (by decide) rank_cyc9

/-- **$[[162,2,9]]$ 之 $d_X \ge 9$**：任何非平凡 X 型逻辑算符重量 ≥ 9。 -/
theorem hgp_toric9_dx_lb {v : (Fin 9 × Fin 9) ⊕ (Fin 9 × Fin 9) → ZMod 2}
    (hv : hgpHX (cycMat 9) (cycMat 9) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat 9) (cycMat 9)).rowSpace) :
    9 ≤ hammingNorm v :=
  hgp_toric_dx_lb cyc9_ker_min cyc9T_ker_min hv hlog

/-- **$[[162,2,9]]$ 之 $d_Z \ge 9$**。 -/
theorem hgp_toric9_dz_lb {v : (Fin 9 × Fin 9) ⊕ (Fin 9 × Fin 9) → ZMod 2}
    (hv : hgpHZ (cycMat 9) (cycMat 9) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat 9) (cycMat 9)).rowSpace) :
    9 ≤ hammingNorm v :=
  hgp_toric_dz_lb cyc9_ker_min cyc9T_ker_min hv hlog

/-- **$[[162,2,9]]$ 之 $d_X \le 9$**：重量 9 的 X 型逻辑算符实物
（核成员结构化，非成员由对偶见证证书给出）。 -/
theorem hgp_toric9_X_logical :
    hgpHX (cycMat 9) (cycMat 9) *ᵥ hgpToricXW 9 = 0
      ∧ hgpToricXW 9 ∉ (hgpHZ (cycMat 9) (cycMat 9)).rowSpace
      ∧ hammingNorm (hgpToricXW 9) = 9 :=
  ⟨toricXW_ker cyc9_one_ker, toricXW_not_mem cyc9_one_ker toric9_dot,
    toric9_XW_weight⟩

/-- **$[[162,2,9]]$ 之 $d_Z \le 9$**。 -/
theorem hgp_toric9_Z_logical :
    hgpHZ (cycMat 9) (cycMat 9) *ᵥ hgpToricZW 9 = 0
      ∧ hgpToricZW 9 ∉ (hgpHX (cycMat 9) (cycMat 9)).rowSpace
      ∧ hammingNorm (hgpToricZW 9) = 9 :=
  ⟨toricZW_ker cyc9_one_ker, toricZW_not_mem cyc9_one_ker toric9_dot,
    toric9_ZW_weight⟩

/-! ## 六、实例二：$m=12$，$[[288,2,12]]$ -/

/-- 种子行和为偶。 -/
theorem cyc12_one_ker : cycMat 12 *ᵥ (fun _ : Fin 12 => 1) = 0 := by decide

/-- 种子秩为 $11$。 -/
theorem rank_cyc12 : (cycMat 12).rank = 11 := by
  rw [Matrix.rank_eq_length_rowReduce]; decide

/-- 种子核最小重量为 $12$（$2^{12}$ 空间逐向量核出）。 -/
theorem cyc12_ker_min : ∀ w : Vec 12, w ≠ 0 → cycMat 12 *ᵥ w = 0 →
    12 ≤ hammingNorm w := by decide

/-- 种子转置核最小重量为 $12$。 -/
theorem cyc12T_ker_min : ∀ w : Vec 12, w ≠ 0 → (cycMat 12).transpose *ᵥ w = 0 →
    12 ≤ hammingNorm w := by decide

/-- 两个 witness 的点积恰为 1（各 288 项的求和，逐项核出）。 -/
theorem toric12_dot : hgpToricXW 12 ⬝ᵥ hgpToricZW 12 = 1 := by decide

/-- X 型 witness 重量为 12。 -/
theorem toric12_XW_weight : hammingNorm (hgpToricXW 12) = 12 := by decide

/-- Z 型 witness 重量为 12。 -/
theorem toric12_ZW_weight : hammingNorm (hgpToricZW 12) = 12 := by decide

/-- 码长 $n = 144 + 144 = 288$。 -/
theorem toric12_n : Fintype.card ((Fin 12 × Fin 12) ⊕ (Fin 12 × Fin 12)) = 288 := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **$[[288,2,12]]$ 之 $k$**。 -/
theorem hgp_toric12_k :
    (12 * 12 + 12 * 12) - (hgpHX (cycMat 12) (cycMat 12)).rank
      - (hgpHZ (cycMat 12) (cycMat 12)).rank = 2 :=
  hgp_toric_k (by decide) rank_cyc12

/-- **$[[288,2,12]]$ 之 $d_X \ge 12$**。 -/
theorem hgp_toric12_dx_lb {v : (Fin 12 × Fin 12) ⊕ (Fin 12 × Fin 12) → ZMod 2}
    (hv : hgpHX (cycMat 12) (cycMat 12) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat 12) (cycMat 12)).rowSpace) :
    12 ≤ hammingNorm v :=
  hgp_toric_dx_lb cyc12_ker_min cyc12T_ker_min hv hlog

/-- **$[[288,2,12]]$ 之 $d_Z \ge 12$**。 -/
theorem hgp_toric12_dz_lb {v : (Fin 12 × Fin 12) ⊕ (Fin 12 × Fin 12) → ZMod 2}
    (hv : hgpHZ (cycMat 12) (cycMat 12) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat 12) (cycMat 12)).rowSpace) :
    12 ≤ hammingNorm v :=
  hgp_toric_dz_lb cyc12_ker_min cyc12T_ker_min hv hlog

/-- **$[[288,2,12]]$ 之 $d_X \le 12$**。 -/
theorem hgp_toric12_X_logical :
    hgpHX (cycMat 12) (cycMat 12) *ᵥ hgpToricXW 12 = 0
      ∧ hgpToricXW 12 ∉ (hgpHZ (cycMat 12) (cycMat 12)).rowSpace
      ∧ hammingNorm (hgpToricXW 12) = 12 :=
  ⟨toricXW_ker cyc12_one_ker, toricXW_not_mem cyc12_one_ker toric12_dot,
    toric12_XW_weight⟩

/-- **$[[288,2,12]]$ 之 $d_Z \le 12$**。 -/
theorem hgp_toric12_Z_logical :
    hgpHZ (cycMat 12) (cycMat 12) *ᵥ hgpToricZW 12 = 0
      ∧ hgpToricZW 12 ∉ (hgpHX (cycMat 12) (cycMat 12)).rowSpace
      ∧ hammingNorm (hgpToricZW 12) = 12 :=
  ⟨toricZW_ker cyc12_one_ker, toricZW_not_mem cyc12_one_ker toric12_dot,
    toric12_ZW_weight⟩

/-! ## 七、全族结构化：核常值性 ⟹ 种子事实零枚举（对任意 $m$） -/

/-- **双热点求和**：指示恰在两个不同位置非零的求和等于两处取值之和。 -/
theorem sum_two_hot {m : ℕ} (a b : Fin m) (hab : a ≠ b) (f : Fin m → ZMod 2) :
    (∑ j : Fin m, if (j : ℕ) = (a : ℕ) ∨ (j : ℕ) = (b : ℕ) then f j else 0) = f a + f b := by
  rw [← Finset.sum_filter
      (p := fun j : Fin m => (j : ℕ) = (a : ℕ) ∨ (j : ℕ) = (b : ℕ))]
  have hset : (Finset.univ.filter (fun j : Fin m => (j : ℕ) = (a : ℕ) ∨ (j : ℕ) = (b : ℕ)))
      = ({a, b} : Finset (Fin m)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    simp [Fin.val_inj]
  rw [hset]
  exact Finset.sum_pair hab

/-- 第 $i$ 行的两个热点列互不相同（$m\ge2$）。 -/
theorem cycMat_ne_next {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    (i : ℕ) ≠ ((i : ℕ) + 1) % m := by
  intro heq
  rcases Nat.lt_or_ge ((i : ℕ) + 1) m with h | h
  · rw [Nat.mod_eq_of_lt h] at heq; omega
  · have him : (i : ℕ) + 1 = m := by omega
    rw [him, Nat.mod_self] at heq; omega

/-- **行方程**：$m$-圈矩阵作用于向量的第 $i$ 个分量恰为 $w_i + w_{(i+1)\bmod m}$。 -/
theorem cycMat_mulVec_apply {m : ℕ} (hm : 2 ≤ m) (w : Vec m) (i : Fin m) :
    (cycMat m *ᵥ w) i = w i + w ⟨((i : ℕ) + 1) % m, Nat.mod_lt ((i : ℕ) + 1) (by omega)⟩ := by
  have hot : ∀ j : Fin m, cycMat m i j * w j
      = (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m then w j else 0) := by
    intro j
    by_cases h : (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
    · simp [cycMat, h]
    · simp [cycMat, h]
  change (∑ j : Fin m, cycMat m i j * w j)
    = w i + w ⟨((i : ℕ) + 1) % m, Nat.mod_lt ((i : ℕ) + 1) (by omega)⟩
  rw [Finset.sum_congr rfl (fun j _ => hot j),
    sum_two_hot i ⟨((i : ℕ) + 1) % m, Nat.mod_lt ((i : ℕ) + 1) (by omega)⟩
      (by intro heq; exact cycMat_ne_next hm i (congrArg Fin.val heq)) w]

/-- **行和为偶（结构化）**：全 1 向量在核中——每个行方程是 $1+1=0$。 -/
theorem cycMat_one_ker {m : ℕ} (hm : 2 ≤ m) : cycMat m *ᵥ (fun _ => 1) = 0 := by
  funext i
  rw [cycMat_mulVec_apply hm _ i]
  exact CharTwo.add_self_eq_zero _

/-- **核常值性**：$m$-圈矩阵的核向量必为常值——行方程 $w_i + w_{i+1} = 0$
在特征 2 下即 $w_{i+1} = w_i$，沿链传递。 -/
theorem cycMat_ker_const {m : ℕ} (hm : 2 ≤ m) {w : Vec m} (h : cycMat m *ᵥ w = 0) :
    ∃ c : ZMod 2, w = fun _ => c := by
  have hstep : ∀ k : ℕ, (hk : k + 1 < m) → w ⟨k + 1, by omega⟩ = w ⟨k, by omega⟩ := by
    intro k hk
    have hrow := congrFun h ⟨k, by omega⟩
    rw [cycMat_mulVec_apply hm w ⟨k, by omega⟩] at hrow
    simp only [Pi.zero_apply, Nat.mod_eq_of_lt hk] at hrow
    exact ((add_eq_zero_iff_eq _ _).mp hrow).symm
  have key : ∀ k : ℕ, (hk : k < m) → w ⟨k, by omega⟩ = w ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        exact (hstep n (by omega)).trans (ih (by omega))
  refine ⟨w ⟨0, by omega⟩, funext fun i => key (i : ℕ) i.isLt⟩

/-- **转置的行方程**（$j\ge1$ 的行）：两个热点在 $j-1$ 与 $j$。 -/
theorem cycMatT_mulVec_pred {m : ℕ} (_hm : 2 ≤ m) (w : Vec m) {j : Fin m} (hj : 1 ≤ (j : ℕ)) :
    ((cycMat m).transpose *ᵥ w) j
      = w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ + w j := by
  have hot : ∀ i : Fin m, (cycMat m).transpose j i * w i
      = (if (i : ℕ) = (j : ℕ) - 1 ∨ (i : ℕ) = (j : ℕ) then w i else 0) := by
    intro i
    by_cases h1 : (i : ℕ) = (j : ℕ) - 1 ∨ (i : ℕ) = (j : ℕ)
    · have hval : cycMat m i j = 1 := by
        change (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
            then (1 : ZMod 2) else 0) = 1
        rcases h1 with h | h
        · have hmod : (j : ℕ) = ((i : ℕ) + 1) % m := by
            rw [h, Nat.sub_add_cancel hj, Nat.mod_eq_of_lt j.isLt]
          rw [ite_eq_left (Or.inr hmod)]
        · rw [ite_eq_left (Or.inl h.symm)]
      rw [Matrix.transpose_apply, ite_eq_left h1, hval, one_mul]
    · have hval : cycMat m i j = 0 := by
        change (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
            then (1 : ZMod 2) else 0) = 0
        have hnot : ¬((j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m) := by
          rcases Nat.lt_or_ge ((i : ℕ) + 1) m with h2 | h2
          · rw [Nat.mod_eq_of_lt h2]
            omega
          · have him : (i : ℕ) + 1 = m := by omega
            rw [show ((i : ℕ) + 1) % m = 0 from by rw [him, Nat.mod_self]]
            omega
        rw [ite_eq_right hnot]
      rw [Matrix.transpose_apply, ite_eq_right h1, hval, zero_mul]
  change (∑ i : Fin m, (cycMat m).transpose j i * w i)
    = w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ + w j
  rw [Finset.sum_congr rfl (fun i _ => hot i),
    sum_two_hot ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ j
      (by intro heq
          have h0 : ((⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin m) : ℕ)
              = (j : ℕ) - 1 := rfl
          have hv := congrArg (fun x : Fin m => (x : ℕ)) heq
          rw [h0] at hv
          have := j.isLt
          omega) w]

/-- **转置核常值性**：转置的核向量也必为常值（沿 $j-1$ 方向的同一论证）。 -/
theorem cycMatT_ker_const {m : ℕ} (hm : 2 ≤ m) {w : Vec m}
    (h : (cycMat m).transpose *ᵥ w = 0) : ∃ c : ZMod 2, w = fun _ => c := by
  have hstep : ∀ k : ℕ, (hk : k + 1 < m) → w ⟨k + 1, by omega⟩ = w ⟨k, by omega⟩ := by
    intro k hk
    have hrow := congrFun h ⟨k + 1, by omega⟩
    rw [cycMatT_mulVec_pred hm w (by simp)] at hrow
    simp only [Pi.zero_apply] at hrow
    exact ((add_eq_zero_iff_eq _ _).mp hrow).symm
  have key : ∀ k : ℕ, (hk : k < m) → w ⟨k, by omega⟩ = w ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        exact (hstep n (by omega)).trans (ih (by omega))
  refine ⟨w ⟨0, by omega⟩, funext fun i => key (i : ℕ) i.isLt⟩

/-- 常值向量的重量：非零常值为 $m$、零常值为 $0$。 -/
theorem hammingNorm_const {m : ℕ} {c : ZMod 2} (hc : c ≠ 0) :
    hammingNorm (fun _ : Fin m => c) = m := by
  change (Finset.univ.filter (fun i : Fin m => (fun _ : Fin m => c) i ≠ 0)).card = m
  have hfil : (Finset.univ.filter (fun _ : Fin m => c ≠ 0)) = Finset.univ :=
    Finset.ext fun x => by simp [hc]
  rw [hfil, Finset.card_univ, Fintype.card_fin]

/-- **种子核最小重量（结构化，零枚举）**：非零核向量是常值，重量即 $m$。 -/
theorem cycMat_ker_min {m : ℕ} (hm : 2 ≤ m) {w : Vec m} (hne : w ≠ 0)
    (h : cycMat m *ᵥ w = 0) : m ≤ hammingNorm w := by
  obtain ⟨c, rfl⟩ := cycMat_ker_const hm h
  have hc : c ≠ 0 := by
    intro hc0
    exact hne (by rw [hc0]; rfl)
  rw [hammingNorm_const hc]

/-- **转置核最小重量（结构化）**。 -/
theorem cycMatT_ker_min {m : ℕ} (hm : 2 ≤ m) {w : Vec m} (hne : w ≠ 0)
    (h : (cycMat m).transpose *ᵥ w = 0) : m ≤ hammingNorm w := by
  obtain ⟨c, rfl⟩ := cycMatT_ker_const hm h
  have hc : c ≠ 0 := by
    intro hc0
    exact hne (by rw [hc0]; rfl)
  rw [hammingNorm_const hc]

/-- **种子秩（结构化）**：核 = 常值向量的张成（一维），秩—零化度给出 $m-1$。 -/
theorem rank_cycMat {m : ℕ} (hm : 2 ≤ m) : (cycMat m).rank = m - 1 := by
  have hspan : LinearMap.ker (cycMat m).mulVecLin
      = Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
    apply le_antisymm
    · intro w hw
      have h0 : cycMat m *ᵥ w = 0 := LinearMap.mem_ker.mp hw
      obtain ⟨c, rfl⟩ := cycMat_ker_const hm h0
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      funext i
      simp
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      refine LinearMap.mem_ker.mpr ?_
      rw [(cycMat m).mulVecLin.map_smul]
      change c • (cycMat m *ᵥ (fun _ => (1 : ZMod 2))) = 0
      rw [cycMat_one_ker hm, smul_zero]
  have hfr : Module.finrank (ZMod 2) ↥(LinearMap.ker (cycMat m).mulVecLin) = 1 := by
    rw [hspan, finrank_span_singleton]
    intro h
    exact one_ne_zero (congrFun h ⟨0, by omega⟩)
  have hrn := LinearMap.finrank_range_add_finrank_ker (cycMat m).mulVecLin
  have hdim : Module.finrank (ZMod 2) (Fin m → ZMod 2) = m := by
    simp
  change Module.finrank (ZMod 2) ↥(LinearMap.range (cycMat m).mulVecLin) = m - 1
  omega

/-- **环面族全族定理**：对任意 $m \ge 2$，$\mathrm{HGP}(\mathrm{cyc}_m,\mathrm{cyc}_m)$
是 $[[\,2m^2,\,2,\,m\,]]$——维数经 Künneth 公式、两侧距离下界经清洗定理，
而全部种子事实（行和为偶、秩 $=m-1$、两个方向的核最小重量 $=m$）都由
**核常值性**结构化给出：**零枚举，对每个 $m$ 成立**。

这是"结构化证据 vs 逐实例枚举"形态对照的极限形态：$m$ 任意大时
种子侧不再需要任何 $2^m$ 计算，证书量级只剩 witness 的 $O(m^2)$ 逐项核对。 -/
theorem hgp_toric_family {m : ℕ} (hm : 2 ≤ m) :
    (m * m + m * m) - (hgpHX (cycMat m) (cycMat m)).rank
        - (hgpHZ (cycMat m) (cycMat m)).rank = 2
      ∧ (∀ v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2,
          hgpHX (cycMat m) (cycMat m) *ᵥ v = 0 →
            v ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace → m ≤ hammingNorm v)
      ∧ (∀ v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2,
          hgpHZ (cycMat m) (cycMat m) *ᵥ v = 0 →
            v ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace → m ≤ hammingNorm v) :=
  ⟨hgp_toric_k (by omega) (rank_cycMat hm),
   fun v hv hlog => hgp_toric_dx_lb (fun w hne h => cycMat_ker_min hm hne h)
     (fun w hne h => cycMatT_ker_min hm hne h) hv hlog,
   fun v hv hlog => hgp_toric_dz_lb (fun w hne h => cycMat_ker_min hm hne h)
     (fun w hne h => cycMatT_ker_min hm hne h) hv hlog⟩

/-! ## 八、实例三：$m=16$，$[[512,2,16]]$（全族定理的种子事实 + witness 逐项核对） -/

/-- 两个 witness 的点积恰为 1（512 项求和，逐项核出）。 -/
theorem toric16_dot : hgpToricXW 16 ⬝ᵥ hgpToricZW 16 = 1 := by decide

/-- X 型 witness 重量为 16。 -/
theorem toric16_XW_weight : hammingNorm (hgpToricXW 16) = 16 := by decide

/-- Z 型 witness 重量为 16。 -/
theorem toric16_ZW_weight : hammingNorm (hgpToricZW 16) = 16 := by decide

/-- **$[[512,2,16]]$ 之 $k$**（Künneth + 结构化种子秩）。 -/
theorem hgp_toric16_k :
    (16 * 16 + 16 * 16) - (hgpHX (cycMat 16) (cycMat 16)).rank
      - (hgpHZ (cycMat 16) (cycMat 16)).rank = 2 :=
  hgp_toric_k (by decide) (rank_cycMat (by decide))

/-- **$[[512,2,16]]$ 之 $d_X \ge 16$**（清洗定理 + 结构化种子事实）。 -/
theorem hgp_toric16_dx_lb {v : (Fin 16 × Fin 16) ⊕ (Fin 16 × Fin 16) → ZMod 2}
    (hv : hgpHX (cycMat 16) (cycMat 16) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat 16) (cycMat 16)).rowSpace) :
    16 ≤ hammingNorm v :=
  hgp_toric_dx_lb (fun w hne h => cycMat_ker_min (by decide) hne h) (fun w hne h => cycMatT_ker_min (by decide) hne h) hv hlog

/-- **$[[512,2,16]]$ 之 $d_Z \ge 16$**。 -/
theorem hgp_toric16_dz_lb {v : (Fin 16 × Fin 16) ⊕ (Fin 16 × Fin 16) → ZMod 2}
    (hv : hgpHZ (cycMat 16) (cycMat 16) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat 16) (cycMat 16)).rowSpace) :
    16 ≤ hammingNorm v :=
  hgp_toric_dz_lb (fun w hne h => cycMat_ker_min (by decide) hne h) (fun w hne h => cycMatT_ker_min (by decide) hne h) hv hlog

/-- **$[[512,2,16]]$ 之 $d_X \le 16$**。 -/
theorem hgp_toric16_X_logical :
    hgpHX (cycMat 16) (cycMat 16) *ᵥ hgpToricXW 16 = 0
      ∧ hgpToricXW 16 ∉ (hgpHZ (cycMat 16) (cycMat 16)).rowSpace
      ∧ hammingNorm (hgpToricXW 16) = 16 :=
  ⟨toricXW_ker (cycMat_one_ker (by decide)),
    toricXW_not_mem (cycMat_one_ker (by decide)) toric16_dot, toric16_XW_weight⟩

/-- **$[[512,2,16]]$ 之 $d_Z \le 16$**。 -/
theorem hgp_toric16_Z_logical :
    hgpHZ (cycMat 16) (cycMat 16) *ᵥ hgpToricZW 16 = 0
      ∧ hgpToricZW 16 ∉ (hgpHX (cycMat 16) (cycMat 16)).rowSpace
      ∧ hammingNorm (hgpToricZW 16) = 16 :=
  ⟨toricZW_ker (cycMat_one_ker (by decide)),
    toricZW_not_mem (cycMat_one_ker (by decide)) toric16_dot, toric16_ZW_weight⟩

end QECCertificates
