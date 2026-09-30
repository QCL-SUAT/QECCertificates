/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors.
-/
import QECCertificates.GF2.RankEchelon
import QECCertificates.Codes.BB144Witness

/-! # $[[144,12,12]]$ 的维数

`Codes/BB144Witness.lean` 记着这个码的规模：字面 $72\times144$ 矩阵、点积的内核归约约五分钟。
行消元在这个宽度上更不可行，故该模块从不做秩断言，论文的表一直写着末行的维数"来自原始呈现"。
本模块把它补上，两侧各两条**便宜判据**（一般判据在 `GF2/RankEchelon.lean`）：

* **下界**：`bb144CertXD` / `bb144CertZD` 各 66 行，每行是若干原校验行的 GF(2) 和
  （`bb144RowSum`），枢轴列互异。成员关系是代数证明（66 行一条证明、与宽度无关），
  枢轴互异是有限判定 ⟹ $66 \le \dim$。
* **上界**：头部取 66 条线性无关的原行（`bb144RxHeadIdx`），其余六行各自等于头部里若干行的
  GF(2) 和（`bb144RelX*` 一族，逐位判定）⟹ 整张行列表由头部 $66$ 行张成 ⟹ $\dim \le 66$。

头部**不是前缀**：$H_X$ 的前 66 行只有秩 64，而 `spanL` 只看元素集合、不看顺序，
故取"消元中产生枢轴的那些原行"即可——这正是本模块的上界与前缀形态的差别所在。

两侧合起来 $\operatorname{rank}H_X=\operatorname{rank}H_Z=66$，于是

$$k \;=\; n-\operatorname{rank}H_X-\operatorname{rank}H_Z \;=\; 144-66-66 \;=\; 12,$$

与原始文献报的 $[[144,12,12]]$ 一致——**维数在内核里成立**，不再只靠原始呈现。
宽度上界也一并记着：秩的检查量是 $O(n\cdot\text{秩})$，与 $2^n$ 无关。

**边界（与维数无关、仍不动）**：距离那一侧的口径不变——见证给 $d\le12$，
下界是把独立形式化的逐族论证**搬运**进本库的 GF(2) 语言并逐条目证明两张矩阵相同
（`Codes/BB144Literal.lean` 的 `bb144Hx_eq_LE_X`），本开发在那条上贡献的是搬运与同一性。

## 数据与可复现

下标子集与枢轴列由 `tools/gen_bb_rank_cert.jl` 算出（Julia，无外部依赖，重跑逐字节一致），
输入是 `tools/bb_rank_mats.txt`（由库内矩阵 `#eval` 打印后整理），且**按发射出去的数据重算复核**过。
**一致性由内核兜底**：证书行在 Lean 里是原行的和、关系式是逐位等式，若输入数据与库内不一致，
那几组 `decide` 会当场失败。
-/

namespace QECCertificates

open scoped BigOperators

-- 判定是 66×66 与 72×144 量级的逐位归约，放宽内核预算（与 `Codes/BB144Witness.lean` 同款）
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ## 预备：行列表与部分和

`bb144Hx` 是 `Matrix`，而 `Matrix` 是 semireducible def：`List.map bb144Hx` 在 `implicit`
透明度下会报"`Matrix (Fin 72) (Fin 144) (ZMod 2)` 不是 `Fin 72 → Fin 144 → ZMod 2`"。
故先把逐行取出来当函数用（`bb144HxRow`），全文只用它。
-/

/-- $H_X$ 的第 `k` 行（`bb144Hx` 的逐行，见上）。 -/
def bb144HxRow (k : Fin 72) : Vec 144 := bb144Hx k

/-- $H_Z$ 的第 `k` 行。 -/
def bb144HzRow (k : Fin 72) : Vec 144 := bb144Hz k

/-- 原行列表 $H_X$。 -/
def bb144Rx : List (Vec 144) := List.ofFn bb144HxRow

/-- 原行列表 $H_Z$。 -/
def bb144Rz : List (Vec 144) := List.ofFn bb144HzRow

/-- `H_X` 若干行的 GF(2) 和。 -/
def bb144RowSum (s : List (Fin 72)) : Vec 144 := (s.map bb144HxRow).sum

/-- `H_Z` 若干行的 GF(2) 和。 -/
def bb144RowSumZ (s : List (Fin 72)) : Vec 144 := (s.map bb144HzRow).sum

/-- **`H_X` 的部分和落在行空间里**（结构证明：逐项用原行、和用 `add_mem`）。 -/
lemma bb144RowSum_mem_spanL (s : List (Fin 72)) : bb144RowSum s ∈ spanL bb144Rx := by
  have hrow : ∀ k : Fin 72, bb144HxRow k ∈ spanL bb144Rx := fun k =>
    subset_spanL (by rw [bb144Rx]; exact List.mem_ofFn.mpr ⟨k, rfl⟩)
  unfold bb144RowSum
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (hrow k) ih

/-- **`H_Z` 的部分和落在行空间里**。 -/
lemma bb144RowSumZ_mem_spanL (s : List (Fin 72)) : bb144RowSumZ s ∈ spanL bb144Rz := by
  have hrow : ∀ k : Fin 72, bb144HzRow k ∈ spanL bb144Rz := fun k =>
    subset_spanL (by rw [bb144Rz]; exact List.mem_ofFn.mpr ⟨k, rfl⟩)
  unfold bb144RowSumZ
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (hrow k) ih

/-! ## X 侧 · 下界：66 行梯队证书 -/

/-- X 侧证书的原始数据：66 条"原行下标子集 + 枢轴列"，
由 `tools/gen_bb_rank_cert.jl` 在 GF(2) 上算出（行序 = 只追加梯队形的顺序）。 -/
def bb144CertXRaw : List (List (Fin 72) × Fin 144) :=
  [([0], 1),
   ([1], 2),
   ([2], 3),
   ([3], 4),
   ([4], 0),
   ([0, 1, 2, 3, 4, 5], 18),
   ([6], 7),
   ([7], 8),
   ([8], 9),
   ([9], 10),
   ([10], 6),
   ([6, 7, 8, 9, 10, 11], 24),
   ([12], 13),
   ([13], 14),
   ([14], 15),
   ([15], 16),
   ([16], 12),
   ([12, 13, 14, 15, 16, 17], 30),
   ([18], 19),
   ([19], 20),
   ([20], 21),
   ([21], 22),
   ([0, 1, 2, 3, 4, 5, 18, 20, 22], 36),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23], 37),
   ([24], 25),
   ([25], 26),
   ([26], 27),
   ([27], 28),
   ([6, 7, 8, 9, 10, 11, 24, 26, 28], 42),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29], 43),
   ([30], 31),
   ([31], 32),
   ([32], 33),
   ([33], 34),
   ([12, 13, 14, 15, 16, 17, 30, 32, 34], 48),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35], 49),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23, 36], 38),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23, 36, 37], 41),
   ([38], 39),
   ([0, 1, 2, 3, 4, 5, 19, 21, 23, 36, 37, 39], 40),
   ([18, 19, 20, 21, 22, 23, 36, 38, 40], 54),
   ([18, 19, 20, 21, 22, 23, 37, 39, 41], 55),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29, 42], 44),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29, 42, 43], 47),
   ([44], 45),
   ([6, 7, 8, 9, 10, 11, 25, 27, 29, 42, 43, 45], 46),
   ([24, 25, 26, 27, 28, 29, 42, 44, 46], 60),
   ([24, 25, 26, 27, 28, 29, 43, 45, 47], 61),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35, 48], 50),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35, 48, 49], 53),
   ([50], 51),
   ([12, 13, 14, 15, 16, 17, 31, 33, 35, 48, 49, 51], 52),
   ([30, 31, 32, 33, 34, 35, 48, 50, 52], 66),
   ([30, 31, 32, 33, 34, 35, 49, 51, 53], 67),
   ([0, 1, 2, 3, 5, 18, 20, 21, 22, 37, 39, 40, 54], 5),
   ([5, 18, 19, 20, 21, 22, 23, 37, 39, 41, 54, 55], 23),
   ([1, 2, 3, 4, 18, 20, 37, 38, 39, 40, 54, 56], 72),
   ([1, 5, 18, 19, 20, 21, 37, 41, 54, 55, 56, 57], 74),
   ([0, 2, 19, 20, 21, 22, 36, 38, 55, 56, 57, 58], 75),
   ([2, 4, 18, 21, 22, 23, 38, 40, 54, 57, 58, 59], 73),
   ([1, 3, 6, 7, 8, 9, 11, 20, 21, 22, 23, 24, 26, 27, 28, 37, 39, 43, 45, 46, 56, 57, 58, 59, 60], 11),
   ([1, 2, 3, 4, 11, 18, 20, 24, 25, 26, 27, 28, 29, 37, 38, 39, 40, 43, 45, 47, 54, 56, 60, 61], 29),
   ([3, 5, 7, 8, 9, 10, 18, 19, 22, 23, 24, 26, 39, 41, 43, 44, 45, 46, 54, 55, 58, 59, 60, 62], 78),
   ([0, 4, 8, 9, 10, 11, 18, 19, 20, 23, 25, 27, 36, 40, 44, 45, 46, 47, 54, 55, 56, 59, 61, 63], 79),
   ([1, 5, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 24, 26, 30, 32, 33, 34, 37, 41, 43, 44, 45, 46, 49, 51, 52, 54, 55, 56, 57, 60, 62, 66], 17),
   ([0, 1, 2, 5, 7, 11, 17, 18, 22, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 41, 43, 47, 49, 51, 53, 54, 58, 60, 61, 62, 63, 66, 67], 35)]

/-- **X 侧证书**：把每条"下标子集"换成原行的 GF(2) 和，枢轴列原样带上。 -/
def bb144CertXD : List (PivRow 144) := bb144CertXRaw.map (fun q => (bb144RowSum q.1, q.2))

/-- **证书每一行都是原行的 GF(2) 和**，故落在原行空间里。66 行由**一条**证明覆盖，
走的是逐项相加的代数（`bb144RowSum_mem_spanL`），**与宽度无关**——这是大宽度上仍可行的关键。 -/
theorem bb144CertX_mem : ∀ v ∈ rowList bb144CertXD, v ∈ spanL bb144Rx := by
  intro v hv
  unfold rowList at hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  unfold bb144CertXD at ha
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
  exact bb144RowSum_mem_spanL q.1

/-- 上一条的**按下标**形态（供 `length_le_finrank_spanL_of_certificate` 使用）。 -/
theorem bb144CertX_get_mem (i : Fin bb144CertXD.length) :
    (bb144CertXD.get i).1 ∈ spanL bb144Rx :=
  bb144CertX_mem _ (by
    rw [rowList]
    exact List.mem_map.mpr ⟨_, List.get_mem _ i, rfl⟩)

/-- 证书的梯队不变量：每行在自枢轴列取 1，更靠后的行在更靠前的枢轴列上取 0。 -/
theorem bb144CertX_ech : EchSelf bb144CertXD ∧ EchPair bb144CertXD :=
  ⟨by unfold EchSelf; decide, by unfold EchPair; decide⟩

/-! ## X 侧 · 上界：整张行列表由 66 条原行张成 -/

/-- 上界所用的**头部**：66 条线性无关的原行，即消元过程中产生枢轴的那些行
（下标由 `tools/gen_bb_rank_cert.jl` 在 GF(2) 上选出）。`spanL` 只看元素集合、不看顺序，
故头部不必是前缀——宽 144 上前 66 行只有秩 64，前缀形态在那里不成立。 -/
def bb144RxHeadIdx : List (Fin 72) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
   12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
   36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 66, 67]

/-- 头部行列表。 -/
def bb144RxHead : List (Vec 144) := bb144RxHeadIdx.map bb144HxRow

/-- 头部恰好 66 条。 -/
lemma bb144RxHead_length : bb144RxHead.length = 66 := by
  simp [bb144RxHead, bb144RxHeadIdx]

/-- 头部里的每一条原行都落在头部的张成里。 -/
lemma bb144HxRow_mem_head (k : Fin 72) (hk : k ∈ bb144RxHeadIdx) :
    bb144HxRow k ∈ spanL bb144RxHead := by
  rw [bb144RxHead]
  exact subset_spanL (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- 头部若干行的和（下标都在头部里）落在头部的张成里。 -/
lemma bb144RowSum_mem_head (s : List (Fin 72)) (hs : ∀ k ∈ s, k ∈ bb144RxHeadIdx) :
    bb144RowSum s ∈ spanL bb144RxHead := by
  unfold bb144RowSum
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (bb144HxRow_mem_head k (hs k (by simp)))
        (ih (fun k hk => hs k (by simp [hk])))

/-- 原行 64 是头部 31 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelX64 : bb144HxRow 64 = bb144RowSum [0, 1, 3, 4, 6, 7, 9, 10, 18, 19, 21, 22, 24, 25, 27, 28, 36, 37, 39, 40, 42, 43, 45, 46, 54, 55, 57, 58, 60, 61, 63] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelX64_mem : bb144HxRow 64 ∈ spanL bb144RxHead := by
  rw [bb144RelX64]
  exact bb144RowSum_mem_head _ (by decide)

/-- 原行 65 是头部 31 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelX65 : bb144HxRow 65 = bb144RowSum [0, 2, 3, 5, 6, 8, 9, 11, 18, 20, 21, 23, 24, 26, 27, 29, 36, 38, 39, 41, 42, 44, 45, 47, 54, 56, 57, 59, 60, 62, 63] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelX65_mem : bb144HxRow 65 ∈ spanL bb144RxHead := by
  rw [bb144RelX65]
  exact bb144RowSum_mem_head _ (by decide)

/-- 原行 68 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelX68 : bb144HxRow 68 = bb144RowSum [0, 4, 7, 11, 13, 14, 15, 16, 18, 19, 20, 23, 24, 25, 26, 27, 30, 32, 36, 40, 43, 47, 49, 50, 51, 52, 54, 55, 56, 59, 60, 61, 62, 63, 66] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelX68_mem : bb144HxRow 68 ∈ spanL bb144RxHead := by
  rw [bb144RelX68]
  exact bb144RowSum_mem_head _ (by decide)

/-- 原行 69 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelX69 : bb144HxRow 69 = bb144RowSum [0, 3, 4, 5, 7, 8, 9, 10, 14, 15, 16, 17, 20, 22, 24, 26, 31, 33, 36, 39, 40, 41, 43, 44, 45, 46, 50, 51, 52, 53, 56, 58, 60, 62, 67] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelX69_mem : bb144HxRow 69 ∈ spanL bb144RxHead := by
  rw [bb144RelX69]
  exact bb144RowSum_mem_head _ (by decide)

/-- 原行 70 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelX70 : bb144HxRow 70 = bb144RowSum [1, 5, 7, 8, 9, 10, 12, 13, 14, 17, 18, 19, 20, 21, 24, 26, 30, 34, 37, 41, 43, 44, 45, 46, 48, 49, 50, 53, 54, 55, 56, 57, 60, 62, 66] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelX70_mem : bb144HxRow 70 ∈ spanL bb144RxHead := by
  rw [bb144RelX70]
  exact bb144RowSum_mem_head _ (by decide)

/-- 原行 71 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelX71 : bb144HxRow 71 = bb144RowSum [0, 2, 8, 9, 10, 11, 12, 13, 14, 15, 19, 20, 21, 22, 25, 27, 31, 35, 36, 38, 44, 45, 46, 47, 48, 49, 50, 51, 55, 56, 57, 58, 61, 63, 67] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelX71_mem : bb144HxRow 71 ∈ spanL bb144RxHead := by
  rw [bb144RelX71]
  exact bb144RowSum_mem_head _ (by decide)

/-- **整张行列表都落在头部的张成里**：头部那些行逐个在头部里，其余各行各有一条关系式。 -/
theorem bb144Rx_mem_head : ∀ v ∈ bb144Rx, v ∈ spanL bb144RxHead := by
  intro v hv
  unfold bb144Rx at hv
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hv
  rw [← hj]
  fin_cases j
  · exact bb144HxRow_mem_head 0 (by decide)
  · exact bb144HxRow_mem_head 1 (by decide)
  · exact bb144HxRow_mem_head 2 (by decide)
  · exact bb144HxRow_mem_head 3 (by decide)
  · exact bb144HxRow_mem_head 4 (by decide)
  · exact bb144HxRow_mem_head 5 (by decide)
  · exact bb144HxRow_mem_head 6 (by decide)
  · exact bb144HxRow_mem_head 7 (by decide)
  · exact bb144HxRow_mem_head 8 (by decide)
  · exact bb144HxRow_mem_head 9 (by decide)
  · exact bb144HxRow_mem_head 10 (by decide)
  · exact bb144HxRow_mem_head 11 (by decide)
  · exact bb144HxRow_mem_head 12 (by decide)
  · exact bb144HxRow_mem_head 13 (by decide)
  · exact bb144HxRow_mem_head 14 (by decide)
  · exact bb144HxRow_mem_head 15 (by decide)
  · exact bb144HxRow_mem_head 16 (by decide)
  · exact bb144HxRow_mem_head 17 (by decide)
  · exact bb144HxRow_mem_head 18 (by decide)
  · exact bb144HxRow_mem_head 19 (by decide)
  · exact bb144HxRow_mem_head 20 (by decide)
  · exact bb144HxRow_mem_head 21 (by decide)
  · exact bb144HxRow_mem_head 22 (by decide)
  · exact bb144HxRow_mem_head 23 (by decide)
  · exact bb144HxRow_mem_head 24 (by decide)
  · exact bb144HxRow_mem_head 25 (by decide)
  · exact bb144HxRow_mem_head 26 (by decide)
  · exact bb144HxRow_mem_head 27 (by decide)
  · exact bb144HxRow_mem_head 28 (by decide)
  · exact bb144HxRow_mem_head 29 (by decide)
  · exact bb144HxRow_mem_head 30 (by decide)
  · exact bb144HxRow_mem_head 31 (by decide)
  · exact bb144HxRow_mem_head 32 (by decide)
  · exact bb144HxRow_mem_head 33 (by decide)
  · exact bb144HxRow_mem_head 34 (by decide)
  · exact bb144HxRow_mem_head 35 (by decide)
  · exact bb144HxRow_mem_head 36 (by decide)
  · exact bb144HxRow_mem_head 37 (by decide)
  · exact bb144HxRow_mem_head 38 (by decide)
  · exact bb144HxRow_mem_head 39 (by decide)
  · exact bb144HxRow_mem_head 40 (by decide)
  · exact bb144HxRow_mem_head 41 (by decide)
  · exact bb144HxRow_mem_head 42 (by decide)
  · exact bb144HxRow_mem_head 43 (by decide)
  · exact bb144HxRow_mem_head 44 (by decide)
  · exact bb144HxRow_mem_head 45 (by decide)
  · exact bb144HxRow_mem_head 46 (by decide)
  · exact bb144HxRow_mem_head 47 (by decide)
  · exact bb144HxRow_mem_head 48 (by decide)
  · exact bb144HxRow_mem_head 49 (by decide)
  · exact bb144HxRow_mem_head 50 (by decide)
  · exact bb144HxRow_mem_head 51 (by decide)
  · exact bb144HxRow_mem_head 52 (by decide)
  · exact bb144HxRow_mem_head 53 (by decide)
  · exact bb144HxRow_mem_head 54 (by decide)
  · exact bb144HxRow_mem_head 55 (by decide)
  · exact bb144HxRow_mem_head 56 (by decide)
  · exact bb144HxRow_mem_head 57 (by decide)
  · exact bb144HxRow_mem_head 58 (by decide)
  · exact bb144HxRow_mem_head 59 (by decide)
  · exact bb144HxRow_mem_head 60 (by decide)
  · exact bb144HxRow_mem_head 61 (by decide)
  · exact bb144HxRow_mem_head 62 (by decide)
  · exact bb144HxRow_mem_head 63 (by decide)
  · exact bb144RelX64_mem
  · exact bb144RelX65_mem
  · exact bb144HxRow_mem_head 66 (by decide)
  · exact bb144HxRow_mem_head 67 (by decide)
  · exact bb144RelX68_mem
  · exact bb144RelX69_mem
  · exact bb144RelX70_mem
  · exact bb144RelX71_mem

/-- **秩的上界**：整张行列表由头部 66 行张成。 -/
theorem bb144_rankX_le : Module.finrank (ZMod 2) (spanL bb144Rx) ≤ 66 := by
  have h := finrank_spanL_le_of_mem_of_subset (A := bb144RxHead) (L := bb144Rx) bb144Rx_mem_head
  rwa [bb144RxHead_length] at h

/-- **秩的下界**：证书的 66 行线性无关，且都在行空间里。 -/
theorem bb144_rankX_ge : 66 ≤ Module.finrank (ZMod 2) (spanL bb144Rx) :=
  length_le_finrank_spanL_of_certificate bb144CertX_get_mem bb144CertX_ech.1 bb144CertX_ech.2

/-- **X 侧校验矩阵的行空间维数是 66**。 -/
theorem bb144_rankX : Module.finrank (ZMod 2) (spanL bb144Rx) = 66 :=
  le_antisymm bb144_rankX_le bb144_rankX_ge

/-! ## Z 侧 · 下界：66 行梯队证书 -/

/-- Z 侧证书的原始数据：66 条"原行下标子集 + 枢轴列"，
由 `tools/gen_bb_rank_cert.jl` 在 GF(2) 上算出（行序 = 只追加梯队形的顺序）。 -/
def bb144CertZRaw : List (List (Fin 72) × Fin 144) :=
  [([0], 3),
   ([1], 4),
   ([2], 5),
   ([3], 0),
   ([4], 1),
   ([5], 2),
   ([3, 6], 9),
   ([4, 7], 10),
   ([5, 8], 11),
   ([0, 9], 6),
   ([1, 10], 7),
   ([2, 11], 8),
   ([0, 3, 9, 12], 15),
   ([1, 4, 10, 13], 16),
   ([2, 5, 11, 14], 17),
   ([0, 3, 6, 15], 12),
   ([1, 4, 7, 16], 13),
   ([2, 5, 8, 17], 14),
   ([3, 6, 9, 15, 18], 21),
   ([4, 7, 10, 16, 19], 22),
   ([5, 8, 11, 17, 20], 23),
   ([0, 6, 9, 12, 21], 18),
   ([1, 7, 10, 13, 22], 19),
   ([2, 8, 11, 14, 23], 20),
   ([3, 9, 12, 15, 21, 24], 27),
   ([4, 10, 13, 16, 22, 25], 28),
   ([5, 11, 14, 17, 23, 26], 29),
   ([0, 6, 12, 15, 18, 27], 24),
   ([1, 7, 13, 16, 19, 28], 25),
   ([2, 8, 14, 17, 20, 29], 26),
   ([9, 15, 18, 21, 27, 30], 33),
   ([10, 16, 19, 22, 28, 31], 34),
   ([11, 17, 20, 23, 29, 32], 35),
   ([6, 12, 18, 21, 24, 33], 30),
   ([7, 13, 19, 22, 25, 34], 31),
   ([8, 14, 20, 23, 26, 35], 32),
   ([0, 15, 21, 24, 27, 33, 36], 39),
   ([1, 16, 22, 25, 28, 34, 37], 40),
   ([2, 17, 23, 26, 29, 35, 38], 41),
   ([3, 12, 18, 24, 27, 30, 39], 36),
   ([4, 13, 19, 25, 28, 31, 40], 37),
   ([5, 14, 20, 26, 29, 32, 41], 38),
   ([3, 6, 21, 27, 30, 33, 39, 42], 45),
   ([4, 7, 22, 28, 31, 34, 40, 43], 46),
   ([5, 8, 23, 29, 32, 35, 41, 44], 47),
   ([0, 9, 18, 24, 30, 33, 36, 45], 42),
   ([1, 10, 19, 25, 31, 34, 37, 46], 43),
   ([2, 11, 20, 26, 32, 35, 38, 47], 44),
   ([0, 3, 9, 12, 27, 33, 36, 39, 45, 48], 51),
   ([1, 4, 10, 13, 28, 34, 37, 40, 46, 49], 52),
   ([2, 5, 11, 14, 29, 35, 38, 41, 47, 50], 53),
   ([0, 3, 6, 15, 24, 30, 36, 39, 42, 51], 48),
   ([1, 4, 7, 16, 25, 31, 37, 40, 43, 52], 49),
   ([2, 5, 8, 17, 26, 32, 38, 41, 44, 53], 50),
   ([3, 6, 9, 15, 18, 33, 39, 42, 45, 51, 54], 57),
   ([4, 7, 10, 16, 19, 34, 40, 43, 46, 52, 55], 58),
   ([5, 8, 11, 17, 20, 35, 41, 44, 47, 53, 56], 59),
   ([0, 6, 9, 12, 21, 30, 36, 42, 45, 48, 57], 54),
   ([1, 7, 10, 13, 22, 31, 37, 43, 46, 49, 58], 55),
   ([2, 8, 11, 14, 23, 32, 38, 44, 47, 50, 59], 56),
   ([3, 9, 12, 15, 21, 24, 39, 45, 48, 51, 57, 60], 73),
   ([4, 10, 13, 16, 22, 25, 40, 46, 49, 52, 58, 61], 74),
   ([5, 11, 14, 17, 23, 26, 41, 47, 50, 53, 59, 62], 75),
   ([0, 6, 12, 15, 18, 27, 36, 42, 48, 51, 54, 63], 72),
   ([0, 5, 6, 9, 11, 12, 14, 17, 21, 23, 26, 30, 36, 41, 42, 45, 47, 48, 50, 53, 57, 59, 62, 66], 79),
   ([0, 1, 6, 7, 10, 12, 13, 15, 18, 22, 27, 31, 36, 37, 42, 43, 46, 48, 49, 51, 54, 58, 63, 67], 78)]

/-- **Z 侧证书**：把每条"下标子集"换成原行的 GF(2) 和，枢轴列原样带上。 -/
def bb144CertZD : List (PivRow 144) := bb144CertZRaw.map (fun q => (bb144RowSumZ q.1, q.2))

/-- **证书每一行都是原行的 GF(2) 和**，故落在原行空间里。66 行由**一条**证明覆盖，
走的是逐项相加的代数（`bb144RowSumZ_mem_spanL`），**与宽度无关**——这是大宽度上仍可行的关键。 -/
theorem bb144CertZ_mem : ∀ v ∈ rowList bb144CertZD, v ∈ spanL bb144Rz := by
  intro v hv
  unfold rowList at hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  unfold bb144CertZD at ha
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp ha
  exact bb144RowSumZ_mem_spanL q.1

/-- 上一条的**按下标**形态（供 `length_le_finrank_spanL_of_certificate` 使用）。 -/
theorem bb144CertZ_get_mem (i : Fin bb144CertZD.length) :
    (bb144CertZD.get i).1 ∈ spanL bb144Rz :=
  bb144CertZ_mem _ (by
    rw [rowList]
    exact List.mem_map.mpr ⟨_, List.get_mem _ i, rfl⟩)

/-- 证书的梯队不变量：每行在自枢轴列取 1，更靠后的行在更靠前的枢轴列上取 0。 -/
theorem bb144CertZ_ech : EchSelf bb144CertZD ∧ EchPair bb144CertZD :=
  ⟨by unfold EchSelf; decide, by unfold EchPair; decide⟩

/-! ## Z 侧 · 上界：整张行列表由 66 条原行张成 -/

/-- 上界所用的**头部**：66 条线性无关的原行，即消元过程中产生枢轴的那些行
（下标由 `tools/gen_bb_rank_cert.jl` 在 GF(2) 上选出）。`spanL` 只看元素集合、不看顺序，
故头部不必是前缀——宽 144 上前 66 行只有秩 64，前缀形态在那里不成立。 -/
def bb144RzHeadIdx : List (Fin 72) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
   12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
   36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 66, 67]

/-- 头部行列表。 -/
def bb144RzHead : List (Vec 144) := bb144RzHeadIdx.map bb144HzRow

/-- 头部恰好 66 条。 -/
lemma bb144RzHead_length : bb144RzHead.length = 66 := by
  simp [bb144RzHead, bb144RzHeadIdx]

/-- 头部里的每一条原行都落在头部的张成里。 -/
lemma bb144HzRow_mem_head (k : Fin 72) (hk : k ∈ bb144RzHeadIdx) :
    bb144HzRow k ∈ spanL bb144RzHead := by
  rw [bb144RzHead]
  exact subset_spanL (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- 头部若干行的和（下标都在头部里）落在头部的张成里。 -/
lemma bb144RowSumZ_mem_head (s : List (Fin 72)) (hs : ∀ k ∈ s, k ∈ bb144RzHeadIdx) :
    bb144RowSumZ s ∈ spanL bb144RzHead := by
  unfold bb144RowSumZ
  induction s with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.sum_cons]
      exact Submodule.add_mem _ (bb144HzRow_mem_head k (hs k (by simp)))
        (ih (fun k hk => hs k (by simp [hk])))

/-- 原行 64 是头部 31 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelZ64 : bb144HzRow 64 = bb144RowSumZ [0, 1, 3, 4, 6, 7, 9, 10, 18, 19, 21, 22, 24, 25, 27, 28, 36, 37, 39, 40, 42, 43, 45, 46, 54, 55, 57, 58, 60, 61, 63] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelZ64_mem : bb144HzRow 64 ∈ spanL bb144RzHead := by
  rw [bb144RelZ64]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- 原行 65 是头部 31 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelZ65 : bb144HzRow 65 = bb144RowSumZ [0, 2, 3, 5, 6, 8, 9, 11, 18, 20, 21, 23, 24, 26, 27, 29, 36, 38, 39, 41, 42, 44, 45, 47, 54, 56, 57, 59, 60, 62, 63] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelZ65_mem : bb144HzRow 65 ∈ spanL bb144RzHead := by
  rw [bb144RelZ65]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- 原行 68 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelZ68 : bb144HzRow 68 = bb144RowSumZ [2, 3, 4, 5, 8, 10, 12, 13, 16, 17, 18, 22, 24, 25, 26, 27, 30, 32, 38, 39, 40, 41, 44, 46, 48, 49, 52, 53, 54, 58, 60, 61, 62, 63, 66] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelZ68_mem : bb144HzRow 68 ∈ spanL bb144RzHead := by
  rw [bb144RelZ68]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- 原行 69 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelZ69 : bb144HzRow 69 = bb144RowSumZ [1, 5, 6, 7, 10, 11, 12, 13, 14, 17, 18, 21, 22, 23, 24, 26, 31, 33, 37, 41, 42, 43, 46, 47, 48, 49, 50, 53, 54, 57, 58, 59, 60, 62, 67] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelZ69_mem : bb144HzRow 69 ∈ spanL bb144RzHead := by
  rw [bb144RelZ69]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- 原行 70 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelZ70 : bb144HzRow 70 = bb144RowSumZ [0, 3, 4, 5, 6, 7, 10, 11, 14, 15, 16, 17, 19, 23, 24, 26, 30, 34, 36, 39, 40, 41, 42, 43, 46, 47, 50, 51, 52, 53, 55, 59, 60, 62, 66] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelZ70_mem : bb144HzRow 70 ∈ spanL bb144RzHead := by
  rw [bb144RelZ70]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- 原行 71 是头部 35 行的 GF(2) 和（逐位判定）。 -/
theorem bb144RelZ71 : bb144HzRow 71 = bb144RowSumZ [0, 1, 4, 5, 6, 7, 8, 11, 12, 15, 16, 17, 18, 20, 25, 27, 31, 35, 36, 37, 40, 41, 42, 43, 44, 47, 48, 51, 52, 53, 54, 56, 61, 63, 67] := by
  funext c
  fin_cases c <;> decide

/-- 上一条的成员关系形态。 -/
theorem bb144RelZ71_mem : bb144HzRow 71 ∈ spanL bb144RzHead := by
  rw [bb144RelZ71]
  exact bb144RowSumZ_mem_head _ (by decide)

/-- **整张行列表都落在头部的张成里**：头部那些行逐个在头部里，其余各行各有一条关系式。 -/
theorem bb144Rz_mem_head : ∀ v ∈ bb144Rz, v ∈ spanL bb144RzHead := by
  intro v hv
  unfold bb144Rz at hv
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hv
  rw [← hj]
  fin_cases j
  · exact bb144HzRow_mem_head 0 (by decide)
  · exact bb144HzRow_mem_head 1 (by decide)
  · exact bb144HzRow_mem_head 2 (by decide)
  · exact bb144HzRow_mem_head 3 (by decide)
  · exact bb144HzRow_mem_head 4 (by decide)
  · exact bb144HzRow_mem_head 5 (by decide)
  · exact bb144HzRow_mem_head 6 (by decide)
  · exact bb144HzRow_mem_head 7 (by decide)
  · exact bb144HzRow_mem_head 8 (by decide)
  · exact bb144HzRow_mem_head 9 (by decide)
  · exact bb144HzRow_mem_head 10 (by decide)
  · exact bb144HzRow_mem_head 11 (by decide)
  · exact bb144HzRow_mem_head 12 (by decide)
  · exact bb144HzRow_mem_head 13 (by decide)
  · exact bb144HzRow_mem_head 14 (by decide)
  · exact bb144HzRow_mem_head 15 (by decide)
  · exact bb144HzRow_mem_head 16 (by decide)
  · exact bb144HzRow_mem_head 17 (by decide)
  · exact bb144HzRow_mem_head 18 (by decide)
  · exact bb144HzRow_mem_head 19 (by decide)
  · exact bb144HzRow_mem_head 20 (by decide)
  · exact bb144HzRow_mem_head 21 (by decide)
  · exact bb144HzRow_mem_head 22 (by decide)
  · exact bb144HzRow_mem_head 23 (by decide)
  · exact bb144HzRow_mem_head 24 (by decide)
  · exact bb144HzRow_mem_head 25 (by decide)
  · exact bb144HzRow_mem_head 26 (by decide)
  · exact bb144HzRow_mem_head 27 (by decide)
  · exact bb144HzRow_mem_head 28 (by decide)
  · exact bb144HzRow_mem_head 29 (by decide)
  · exact bb144HzRow_mem_head 30 (by decide)
  · exact bb144HzRow_mem_head 31 (by decide)
  · exact bb144HzRow_mem_head 32 (by decide)
  · exact bb144HzRow_mem_head 33 (by decide)
  · exact bb144HzRow_mem_head 34 (by decide)
  · exact bb144HzRow_mem_head 35 (by decide)
  · exact bb144HzRow_mem_head 36 (by decide)
  · exact bb144HzRow_mem_head 37 (by decide)
  · exact bb144HzRow_mem_head 38 (by decide)
  · exact bb144HzRow_mem_head 39 (by decide)
  · exact bb144HzRow_mem_head 40 (by decide)
  · exact bb144HzRow_mem_head 41 (by decide)
  · exact bb144HzRow_mem_head 42 (by decide)
  · exact bb144HzRow_mem_head 43 (by decide)
  · exact bb144HzRow_mem_head 44 (by decide)
  · exact bb144HzRow_mem_head 45 (by decide)
  · exact bb144HzRow_mem_head 46 (by decide)
  · exact bb144HzRow_mem_head 47 (by decide)
  · exact bb144HzRow_mem_head 48 (by decide)
  · exact bb144HzRow_mem_head 49 (by decide)
  · exact bb144HzRow_mem_head 50 (by decide)
  · exact bb144HzRow_mem_head 51 (by decide)
  · exact bb144HzRow_mem_head 52 (by decide)
  · exact bb144HzRow_mem_head 53 (by decide)
  · exact bb144HzRow_mem_head 54 (by decide)
  · exact bb144HzRow_mem_head 55 (by decide)
  · exact bb144HzRow_mem_head 56 (by decide)
  · exact bb144HzRow_mem_head 57 (by decide)
  · exact bb144HzRow_mem_head 58 (by decide)
  · exact bb144HzRow_mem_head 59 (by decide)
  · exact bb144HzRow_mem_head 60 (by decide)
  · exact bb144HzRow_mem_head 61 (by decide)
  · exact bb144HzRow_mem_head 62 (by decide)
  · exact bb144HzRow_mem_head 63 (by decide)
  · exact bb144RelZ64_mem
  · exact bb144RelZ65_mem
  · exact bb144HzRow_mem_head 66 (by decide)
  · exact bb144HzRow_mem_head 67 (by decide)
  · exact bb144RelZ68_mem
  · exact bb144RelZ69_mem
  · exact bb144RelZ70_mem
  · exact bb144RelZ71_mem

/-- **秩的上界**：整张行列表由头部 66 行张成。 -/
theorem bb144_rankZ_le : Module.finrank (ZMod 2) (spanL bb144Rz) ≤ 66 := by
  have h := finrank_spanL_le_of_mem_of_subset (A := bb144RzHead) (L := bb144Rz) bb144Rz_mem_head
  rwa [bb144RzHead_length] at h

/-- **秩的下界**：证书的 66 行线性无关，且都在行空间里。 -/
theorem bb144_rankZ_ge : 66 ≤ Module.finrank (ZMod 2) (spanL bb144Rz) :=
  length_le_finrank_spanL_of_certificate bb144CertZ_get_mem bb144CertZ_ech.1 bb144CertZ_ech.2

/-- **Z 侧校验矩阵的行空间维数是 66**。 -/
theorem bb144_rankZ : Module.finrank (ZMod 2) (spanL bb144Rz) = 66 :=
  le_antisymm bb144_rankZ_le bb144_rankZ_ge

/-! ## 维数 -/

/-- **$[[144,12,12]]$ 的维数**：$k=n-\operatorname{rank}H_X-\operatorname{rank}H_Z=12$，
在**不做行消元**的前提下由证书给出。 -/
theorem bb144_rowReduceX : (rowReduce bb144Rx).length = 66 := by
  rw [← rankEchelon_eq_length_rowReduce (L := bb144Rx)]
  rw [rankEchelon]
  rw [← finrank_spanL_eq_length_echelonFrom (L := bb144Rx)]
  exact bb144_rankX

/-- $H_Z$ 的消元输出同为 66 行（换后端不影响秩）。 -/
theorem bb144_rowReduceZ : (rowReduce bb144Rz).length = 66 := by
  rw [← rankEchelon_eq_length_rowReduce (L := bb144Rz)]
  rw [rankEchelon]
  rw [← finrank_spanL_eq_length_echelonFrom (L := bb144Rz)]
  exact bb144_rankZ

theorem bb144_k : 144 - (rowReduce bb144Rx).length - (rowReduce bb144Rz).length = 12 := by
  norm_num [bb144_rowReduceX, bb144_rowReduceZ]

end QECCertificates
