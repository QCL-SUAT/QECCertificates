/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.HGPToricFamily
import QECCertificates.Codes.SeparationClosedForm
import QECCertificates.GF2.Witness

/-!
# 环面族的**空间侧**（变形码两侧距离 $=m$，带重量 $m$ 的存活见证）

本包剩下的空间侧缺口是这一句：

> 环面族的空间侧——该族的变形码距离需要一个重量 $m$ 的存活见证，内核里没算过
> （BB24 能闭合是因为它是实例、两侧码距都算过）。

本模块把这一句做掉，并把"W–Y Lemma 2 的计数核"单独做成定理。**先说清模型**：

本库与预研 `probeB_gauging.py` 采用的 gauging **表示层**是"把被测逻辑 $\ell$
作为新的一行接到 X 校验上"（`Codes/Gauging.lean` 的 `deformXRows`：
$H_X' = H_X + [\ell]$、$H_Z' = H_Z$）。论文 [12] 的**电路级**构造另有辅助比特
（Gauss 律 $A_v$、flux 检查 $B_p$、按完美匹配变形的校验 $\tilde s_i$），本库在
`Codes/BB24Gauged.lean` 与 `Codes/SeparationInstances.lean` 里逐实例落地。
本模块的结论全部在**表示层模型**内——这是本库与预研脚本 `probeB_gauging.py` 共用的那个模型，
不是电路级模型。

## 一、一般事实：追加一行校验只会让逻辑算符集合变小

`le_minWeight_of_lower_appendRow`（X 侧追加行：核变小）与
`le_minWeight_of_lower_rowSpace_appendRow`（Z 侧追加行：行空间变大）说明：
$\ker M_1 \setminus \mathrm{row}\,M_2$ 在两个方向上都只减不增，于是**任何**对该码
成立的逐算符下界自动转移给变形码。这就是"gauging 不会凭空造出更轻的逻辑算符"
的一般论证，它在表示层模型里对**一切**码成立。论文 [12] 的 Lemma 2 不在此列：
电路级模型里辅助比特可以让重量 1 的算符存活（`Codes/SeparationInstances.lean` 的
失效侧 `sepFail_lightLogical` 就是这个现象的内核证据）。

## 二、环面族的存活见证与双侧距离 $=m$

被测逻辑取 `hgpToricZW m`（重量 $m$ 的 X 型逻辑：`H_Z` 的核向量、不在 `H_X`
的行空间里）。原有 X 侧见证 `hgpToricXW m` 与它配对为 $1$，**被杀死**（不再与
$\ell$ 对易——`toricXWFin_not_mem_ker` 就是这条的机器版）；**存活下来**的是右半块的行见证
`toricRW m s₀`（重量 $m$、与 $\ell$ 的支撑不交故对易（`dot_toricRW_toricZW`）、
且仍不在 `H_Z` 行空间里）。Z 侧同理由右半块的列见证
`toricRWZ m t₀` 存活。三条右半块事实（两个核成员性 + 一个行空间非成员性）
用的都是 `cycMat` 的**列**和为偶（`cycMat_col_sum`——左半块的既有见证用的是行和，
`cycMat` 不对称，两者不能互推）：

* `toric_family_deformed_dx`：$\mathrm{dx}(H_X', H_Z) = m$；
* `toric_family_deformed_dz`：$\mathrm{dz}(H_Z, H_X') = m$。

上下界出自**不同**的论证：下界是基码的清洗定理（`hgp_toric_family`）加上一般
集合包含；上界是显式的重量 $m$ 存活见证加上对偶见证。

## 三、分离闭式的空间侧

`toric_family_space_bound` 把 §二 接回 `separation_closed` 的空间界假设
（论文 [12] Lemma 2 的 $\min(\eta,1)\cdot d \le \text{spaceDist}$）——
在该族上它不再是假设。`toric_family_separation_closed_spatial` 是最终形态。

## 四、W–Y Lemma 2 的计数核（引理本身的一半，诚实清单见下）

`space_fault_weight_ge_of_expansion` 把论文 [12] Methods Lemma 2 的**计数步骤**
单独机检：清洗（乘 $\prod_{v\in T}A_v$）把顶点支撑 $S$ 变成 $S\triangle T$、
被加的边支撑是割 $\partial T$；取到 $|T|\le |V|/2$ 的代表元后，Cheeger 常数 $\ge1$
（本库的 C1）给出 $|T|\le|\partial T|$，于是"清洗后限制到原码比特上是原码的逻辑算符
（重量 $\ge d$）"推出 $|S|+|\partial T|+w \ge d$。

**没做到的**：论文完整 Lemma 2 还需要两件本模块没有形式化的东西——
(i) 变形码的**电路级**定义（辅助比特、$A_v$、$B_p$、完美匹配 $\tilde s_i$）；
(ii) 由此导出"边上的 X 型支撑是某顶点集的**割**"（图论对偶：割空间 = 圈空间的正交补）
与"清洗后限制到原码比特上是原码的逻辑算符"。这两片以**假设**形式写在计数核的陈述里，
本模块只把计数那一片做成定理。**不声称**把 Lemma 2 的一般情形机器检验了一遍
（本库同此口径：只把计数那一片做成定理，不声称 Lemma 2 的一般情形已在机器上核过）。

## 五、边界

* 泛型 $h(G)<1$ 那一支（$\min(h,1)=\eta$）需要有理值的 Cheeger 常数；本库的 C1 是
  $\eta\ge1$ 的 0/1 形态（`HasExpansionOne`/`c1Witness`），故本模块只覆盖 $h\ge1$ 支。
* 本模块**不**含 $k$ 的读数（`deformX_k` 已在 `Codes/Gauging.lean` 对任意码给出
  $k$ 恰减一；本模块只需"$\ell$ 是非平凡逻辑"这一条，由 `toricZW_not_mem` 给出）。
* HGP 的校验矩阵行/列指标都是乘积/直和类型，而 `min_weight_ker_not_mem_rowspace`
  要求 `Fin` 索引；§二用一条**列重排运输**（`flatVec`）把两者接起来，
  运输本身是 `Fintype.sum_equiv` 级的重标号，不带数学内容。
* 本模块用到的两条"$m$-圈矩阵"事实是 `cycMat_one_ker`（行和为偶，`Codes/HGPToricFamily.lean`
  已有）与 `cycMat_col_sum`（**列**和为偶，本模块新增；`cycMat` 不对称，两者不能互推）。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {n : ℕ}

/-! ## 一、追加一行校验（表示层 gauging 的代数形式） -/

/-- **追加一行**：把 `v` 接在 `M` 下方作为新的最后一行——本库表示层 gauging
（$H_X \mapsto H_X + [\ell]$）的矩阵形态。行指标是 `Fin m`（故可在末位追加）。 -/
def appendRow {m : ℕ} {κ : Type*} (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) :
    Matrix (Fin (m + 1)) κ (ZMod 2) :=
  fun i => Fin.lastCases v (fun j => M j) i

/-- 追加行在旧下标处与原矩阵一致。 -/
theorem appendRow_castSucc {m : ℕ} {κ : Type*} (M : Matrix (Fin m) κ (ZMod 2))
    (v : κ → ZMod 2) (j : Fin m) : appendRow M v (Fin.castSucc j) = M j := by
  simp only [appendRow, Fin.lastCases_castSucc]

/-- 追加行落在最后一位。 -/
theorem appendRow_last {m : ℕ} {κ : Type*} (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) :
    appendRow M v (Fin.last m) = v := by
  simp only [appendRow, Fin.lastCases_last]

/-- 核成员：`toLin'` 形态与矩阵-向量形态等价。 -/
theorem mem_ker_toLin'_iff {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ (ZMod 2)) (x : κ → ZMod 2) : x ∈ LinearMap.ker M.toLin' ↔ M *ᵥ x = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]

/-- 矩阵-向量作用为零 $\iff$ 每一行都与之正交。 -/
theorem mulVec_eq_zero_iff {ι κ : Type*} [Fintype κ] (M : Matrix ι κ (ZMod 2))
    (x : κ → ZMod 2) : M *ᵥ x = 0 ↔ ∀ i, M i ⬝ᵥ x = 0 := by
  constructor
  · intro h i
    have hi := congrFun h i
    change M i ⬝ᵥ x = 0 at hi
    exact hi
  · intro h
    funext i
    change M i ⬝ᵥ x = 0
    exact h i

/-- **追加行的核刻画**：新核 = 原核 ∩ 与新增行正交。
这是"核变小"这一步的全部内容（也是"gauging 只可能杀死逻辑算符"的来源）。 -/
theorem mem_ker_appendRow {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) (E : κ → ZMod 2) :
    E ∈ LinearMap.ker (appendRow M v).toLin' ↔ E ∈ LinearMap.ker M.toLin' ∧ v ⬝ᵥ E = 0 := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have hj := h (Fin.castSucc j)
      rwa [appendRow_castSucc] at hj
    · have hl := h (Fin.last m)
      rwa [appendRow_last] at hl
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases (motive := fun i => (appendRow M v i) ⬝ᵥ E = 0) ?_ ?_ i
    · rw [appendRow_last]; exact h2
    · intro j; rw [appendRow_castSucc]; exact h1 j

/-- 追加行的矩阵-向量作用：新旧两部分各自为零。 -/
theorem mulVec_appendRow_eq_zero_iff {m : ℕ} {κ : Type*} [Fintype κ]
    (M : Matrix (Fin m) κ (ZMod 2)) (v E : κ → ZMod 2) :
    (appendRow M v) *ᵥ E = 0 ↔ M *ᵥ E = 0 ∧ v ⬝ᵥ E = 0 := by
  rw [mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have hj := h (Fin.castSucc j)
      rwa [appendRow_castSucc] at hj
    · have hl := h (Fin.last m)
      rwa [appendRow_last] at hl
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases (motive := fun i => (appendRow M v i) ⬝ᵥ E = 0) ?_ ?_ i
    · rw [appendRow_last]; exact h2
    · intro j; rw [appendRow_castSucc]; exact h1 j

/-- **追加行的行空间包含原行空间**（"行空间变大"这一步）。 -/
theorem rowSpace_appendRow_le {m : ℕ} {κ : Type*} [Fintype κ]
    (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) :
    M.rowSpace ≤ (appendRow M v).rowSpace := by
  refine Submodule.span_mono ?_
  rintro x ⟨j, rfl⟩
  exact ⟨Fin.castSucc j, appendRow_castSucc M v j⟩

/-- **一般论证（X 侧）**：在 X 校验上追加一行，逐算符下界原样转移——
"gauging 不会造出更轻的 X 侧逻辑算符"。 -/
theorem le_minWeight_of_lower_appendRow {m₁ m₂ n : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) {d₀ : ℕ} (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ min_weight_ker_not_mem_rowspace (appendRow M₁ v) M₂ :=
  le_minWeight_of_lower _ _ hd fun E hker hnot =>
    h E ((mem_ker_appendRow M₁ v E).mp hker).1 hnot

/-- **一般论证（Z 侧）**：在 Z 校验上追加一行，逐算符下界原样转移——
"gauging 不会造出更轻的 Z 侧逻辑算符"。 -/
theorem le_minWeight_of_lower_rowSpace_appendRow {m₁ m₂ n : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) {d₀ : ℕ} (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ min_weight_ker_not_mem_rowspace M₁ (appendRow M₂ v) :=
  le_minWeight_of_lower _ _ hd fun E hker hnot =>
    h E hker fun hmem => hnot (rowSpace_appendRow_le M₂ v hmem)

/-! ## 二、列重排的运输（HGP 的列索引是直和类型，`min_weight` 要 `Fin`）

`flatVec e v := v ∘ e.symm` 把直和/积索引上的向量搬到 `Fin` 上；
下面四条说明它保值：重量、点积、核成员、（一个方向的）行空间成员。 -/

/-- **列重排**：把 `α` 上的向量沿 `e : α ≃ β` 搬到 `β` 上。 -/
def flatVec {α β : Type*} (e : α ≃ β) (v : α → ZMod 2) : β → ZMod 2 := v ∘ ⇑e.symm

theorem flatVec_apply {α β : Type*} (e : α ≃ β) (v : α → ZMod 2) (j : β) :
    flatVec e v j = v (e.symm j) := rfl

theorem flatVec_comp {α β : Type*} (e : α ≃ β) (v : α → ZMod 2) :
    flatVec e v ∘ ⇑e = v := by
  funext a
  simp [flatVec_apply]

/-- 列重排后的矩阵-向量作用就是原作用（向量经 `flatVec` 运输）。 -/
theorem mulVec_submatrix {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) (w : β → ZMod 2) :
    (M.submatrix id ⇑e.symm) *ᵥ w = M *ᵥ (w ∘ ⇑e) := by
  funext i
  simp only [Matrix.mulVec_apply, Matrix.submatrix_apply, Matrix.row_apply, dotProduct,
    Function.comp_apply]
  exact Fintype.sum_equiv e.symm (fun j : β => M i (e.symm j) * w j)
    (fun a : α => M i a * w (e a)) (fun j => by rw [Equiv.apply_symm_apply])

/-- 列重排不改核。 -/
theorem mem_ker_submatrix {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) (w : β → ZMod 2) :
    w ∈ LinearMap.ker (M.submatrix id ⇑e.symm).toLin' ↔ (w ∘ ⇑e) ∈ LinearMap.ker M.toLin' := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, ← mulVec_submatrix M e w]

/-- 列重排不改重量。 -/
theorem hammingNorm_flatVec {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (v : α → ZMod 2) : hammingNorm (flatVec e v) = hammingNorm v := by
  have hset : (Finset.univ.filter (fun j : β => flatVec e v j ≠ 0))
      = (Finset.univ.filter (fun a : α => v a ≠ 0)).image ⇑e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨e.symm j, by simpa [flatVec_apply] using h, e.apply_symm_apply j⟩
    · rintro ⟨a, ha, rfl⟩
      simpa [flatVec_apply] using ha
  show (Finset.univ.filter (fun j : β => flatVec e v j ≠ 0)).card
      = (Finset.univ.filter (fun a : α => v a ≠ 0)).card
  rw [hset, Finset.card_image_of_injective _ e.injective]

/-- 列重排不改（双线性）点积。 -/
theorem dotProduct_flatVec {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (u w : α → ZMod 2) : flatVec e u ⬝ᵥ flatVec e w = u ⬝ᵥ w := by
  rw [dotProduct, dotProduct, flatVec, flatVec, Function.comp_def, Function.comp_def]
  exact Fintype.sum_equiv e.symm
    (fun j : β => u (e.symm j) * w (e.symm j)) (fun a : α => u a * w a) (fun _ => rfl)

/-- 行空间成员沿列重排运输（用于把"变形码里的逻辑算符"降回基码）。 -/
theorem comp_symm_mem_rowSpace {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) {x : α → ZMod 2} (hx : x ∈ M.rowSpace) :
    flatVec e x ∈ (M.submatrix id ⇑e.symm).rowSpace := by
  refine Submodule.span_induction
    (p := fun y _ => flatVec e y ∈ (M.submatrix id ⇑e.symm).rowSpace) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    have hrow : (M.submatrix id ⇑e.symm) i = flatVec e (M i) := by
      funext j
      simp [flatVec_apply, Matrix.submatrix_apply]
    exact Submodule.subset_span ⟨i, hrow⟩
  · simp [flatVec]
  · intro a b _ _ ha hb
    have hgoal : flatVec e (a + b) = flatVec e a + flatVec e b := by
      funext j
      simp [flatVec_apply, Pi.add_apply]
    rw [hgoal]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have hgoal : flatVec e (c • a) = c • flatVec e a := by
      funext j
      simp [flatVec_apply, Pi.smul_apply]
    rw [hgoal]
    exact Submodule.smul_mem _ c ha

/-- 运输的逆方向：`E ∘ e` 在原行空间里 $\Longrightarrow$ `E` 在重排行空间里。 -/
theorem unflatVec_mem_rowSpace {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) {E : β → ZMod 2}
    (h : E ∘ ⇑e ∈ M.rowSpace) : E ∈ (M.submatrix id ⇑e.symm).rowSpace := by
  have hx := comp_symm_mem_rowSpace M e h
  rwa [show flatVec e (E ∘ ⇑e) = E from by
    funext j; simp [flatVec_apply]] at hx

/-! ## 三、$m$-圈矩阵的列和（右半块见证的核成员性要用）

左半块的既有见证（`hgpToricZW`）进 `ker H_Z` 靠 `cycMat` 的**行**和为偶；
右半块的三个见证（`toricRW` 进 `ker H_X`、`toricRWZ` 进 `ker H_Z`）靠的是
**列**和为偶。后者需要单独一条（`cycMat` 不是对称矩阵，两者不能互推）。 -/

/-- $m$-圈矩阵第 `j` 列的**前驱列**：`j` 的列支撑恰是 `{j, predIdx hm j}`。 -/
def predIdx {m : ℕ} (hm : 2 ≤ m) (j : Fin m) : Fin m :=
  ⟨if (j : ℕ) = 0 then m - 1 else (j : ℕ) - 1, by split <;> omega⟩

theorem predIdx_val {m : ℕ} (hm : 2 ≤ m) (j : Fin m) :
    (predIdx hm j : ℕ) = if (j : ℕ) = 0 then m - 1 else (j : ℕ) - 1 := rfl

/-- **后向**：若 `(i+1) mod m = j`，则 `i` 就是 `j` 的前驱列。 -/
theorem predIdx_of_succ {m : ℕ} (hm : 2 ≤ m) {i j : Fin m}
    (h : ((i : ℕ) + 1) % m = (j : ℕ)) : (i : ℕ) = (predIdx hm j : ℕ) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [predIdx_val]
  by_cases hj0 : (j : ℕ) = 0
  · rw [ite_eq_left hj0]
    by_cases hlt : (i : ℕ) + 1 < m
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · omega
  · rw [ite_eq_right hj0]
    by_cases hlt : (i : ℕ) + 1 < m
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have hm1 : (i : ℕ) + 1 = m := by omega
      rw [hm1, Nat.mod_self] at h
      exact absurd h.symm hj0

/-- **前向**：前驱列的下一列就是 `j` 本身。 -/
theorem succ_of_predIdx {m : ℕ} (hm : 2 ≤ m) {i j : Fin m}
    (h : (i : ℕ) = (predIdx hm j : ℕ)) : ((i : ℕ) + 1) % m = (j : ℕ) := by
  have hj := j.isLt
  rw [predIdx_val] at h
  by_cases hj0 : (j : ℕ) = 0
  · rw [ite_eq_left hj0] at h
    rw [h, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self, hj0]
  · rw [ite_eq_right hj0] at h
    rw [h, Nat.sub_add_cancel (by omega : 1 ≤ (j : ℕ)), Nat.mod_eq_of_lt hj]

/-- **列支撑的刻画**：`i` 落在第 `j` 列的支撑里 $\iff$ `i = j` 或 `i = predIdx hm j`。 -/
theorem cycMat_col_supp {m : ℕ} (hm : 2 ≤ m) (i j : Fin m) :
    ((j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m)
      ↔ ((i : ℕ) = (j : ℕ) ∨ (i : ℕ) = (predIdx hm j : ℕ)) :=
  ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (predIdx_of_succ hm h.symm)),
   fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (succ_of_predIdx hm h).symm)⟩

/-- **列和为偶（结构化）**：$m$-圈矩阵每一列恰有两个 1（`j` 与其前驱）。 -/
theorem cycMat_col_sum {m : ℕ} (hm : 2 ≤ m) (j : Fin m) :
    (∑ i : Fin m, cycMat m i j) = 0 := by
  have hne : j ≠ predIdx hm j := by
    intro h
    have hv : (j : ℕ) = (predIdx hm j : ℕ) := congrArg Fin.val h
    rw [predIdx_val] at hv
    by_cases hj0 : (j : ℕ) = 0
    · rw [ite_eq_left hj0] at hv; omega
    · rw [ite_eq_right hj0] at hv; omega
  have hhot : ∀ i : Fin m, cycMat m i j
      = (if (i : ℕ) = (j : ℕ) ∨ (i : ℕ) = (predIdx hm j : ℕ) then (1 : ZMod 2) else 0) := by
    intro i
    rw [cycMat]
    by_cases h : (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
    · rw [ite_eq_left h, ite_eq_left ((cycMat_col_supp hm i j).mp h)]
    · rw [ite_eq_right h, ite_eq_right fun hc => h ((cycMat_col_supp hm i j).mpr hc)]
  rw [Finset.sum_congr rfl fun i _ => hhot i]
  rw [sum_two_hot j (predIdx hm j) hne fun _ => (1 : ZMod 2)]
  exact CharTwo.add_self_eq_zero 1

/-- **转置行和为偶**：`cycMatᵀ *ᵥ 1` 的第 `a` 个分量（即 `cycMat` 第 `a` 列之和）为零。 -/
theorem cycMatT_one_ker_row {m : ℕ} (hm : 2 ≤ m) (a : Fin m) :
    (∑ i : Fin m, cycMat m i a * 1) = 0 := by
  simpa only [mul_one] using cycMat_col_sum hm a

/-! ## 四、右半块的两个重量 $m$ 见证 -/

/-- **右半块行见证**：右半块上第 `s₀` 行全 1、其余为 0（重量 $m$）。

它是**存活见证**：与左半块上的被测逻辑 `hgpToricZW m` 支撑不交 $\Longrightarrow$ 对易，
故 gauging 之后仍在核里；而左半块的 `hgpToricXW m` 与 `hgpToricZW m` 配对为 1，
被杀死（这正是本模块要找的那个"重量 $m$ 存活见证"）。 -/
def toricRW {m : ℕ} (s₀ : Fin m) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun st => if st.1 = s₀ then 1 else 0)

/-- **右半块列见证**：右半块上第 `t₀` 列全 1、其余为 0（重量 $m$）。

它是 `toricRW` 的**对偶见证**：进 `H_Z` 的核（靠 `cycMat` 的列和为偶），
且与 `toricRW s₀` 恰在一个格点相交（配对为 1）。 -/
def toricRWZ {m : ℕ} (t₀ : Fin m) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun st => if st.2 = t₀ then 1 else 0)

theorem toricRW_inl {m : ℕ} (s₀ : Fin m) (ab : Fin m × Fin m) :
    toricRW s₀ (Sum.inl ab) = 0 := rfl

theorem toricRW_inr {m : ℕ} (s₀ : Fin m) (st : Fin m × Fin m) :
    toricRW s₀ (Sum.inr st) = (if st.1 = s₀ then 1 else 0) := rfl

theorem toricRWZ_inl {m : ℕ} (t₀ : Fin m) (ab : Fin m × Fin m) :
    toricRWZ t₀ (Sum.inl ab) = 0 := rfl

theorem toricRWZ_inr {m : ℕ} (t₀ : Fin m) (st : Fin m × Fin m) :
    toricRWZ t₀ (Sum.inr st) = (if st.2 = t₀ then 1 else 0) := rfl

/-- **`toricRW` 在 X 校验的核里**：右半块的行模式经过 `blockR` 后每行是 `cycMat`
的一列元素之和（列和为偶）。 -/
theorem toricRW_ker {m : ℕ} (hm : 2 ≤ m) (s₀ : Fin m) :
    hgpHX (cycMat m) (cycMat m) *ᵥ toricRW s₀ = 0 := by
  rw [hgpHX_mulVec_eq_zero_iff]
  have hL : blockL (toricRW s₀) = 0 := by ext a b; rfl
  rw [hL, Matrix.mul_zero]
  symm
  ext s d
  rw [Matrix.mul_apply]
  change (∑ t : Fin m, blockR (toricRW s₀) s t * cycMat m t d) = 0
  by_cases hs : s = s₀
  · have he : ∀ t : Fin m, blockR (toricRW s₀) s t * cycMat m t d = cycMat m t d * 1 := by
      intro t
      rw [blockR_apply, toricRW_inr, ite_eq_left hs, one_mul, mul_one]
    rw [Finset.sum_congr rfl fun t _ => he t]
    exact cycMatT_one_ker_row hm d
  · have he : ∀ t : Fin m, blockR (toricRW s₀) s t * cycMat m t d = 0 := by
      intro t
      rw [blockR_apply, toricRW_inr, ite_eq_right hs, zero_mul]
    rw [Finset.sum_congr rfl fun t _ => he t, Finset.sum_const_zero]

/-- **`toricRWZ` 在 Z 校验的核里**：右半块的列模式经过 `cycMatᵀ` 后每列是 `cycMat`
的一列元素之和（列和为偶）。 -/
theorem toricRWZ_ker {m : ℕ} (hm : 2 ≤ m) (t₀ : Fin m) :
    hgpHZ (cycMat m) (cycMat m) *ᵥ toricRWZ t₀ = 0 := by
  rw [hgpHZ_mulVec_eq_zero_iff]
  have hL : blockL (toricRWZ t₀) = 0 := by ext a b; rfl
  rw [hL, Matrix.zero_mul]
  symm
  ext a d
  rw [Matrix.mul_apply]
  change (∑ s : Fin m, (cycMat m).transpose a s * blockR (toricRWZ t₀) s d) = 0
  have he : ∀ s : Fin m, (cycMat m).transpose a s * blockR (toricRWZ t₀) s d
      = cycMat m s a * (if d = t₀ then 1 else 0) := by
    intro s
    rw [Matrix.transpose_apply, blockR_apply, toricRWZ_inr]
  rw [Finset.sum_congr rfl fun s _ => he s]
  by_cases hd : d = t₀
  · rw [ite_eq_left hd]
    exact cycMatT_one_ker_row hm a
  · rw [ite_eq_right hd, Finset.sum_congr rfl fun s _ => mul_zero (cycMat m s a),
      Finset.sum_const_zero]

/-- **重量 $m$**：`toricRW` 的支撑是右半块的一整行。 -/
theorem hammingNorm_toricRW {m : ℕ} (s₀ : Fin m) : hammingNorm (toricRW s₀) = m := by
  have hinj : Function.Injective fun t : Fin m =>
      (Sum.inr (s₀, t) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := by
    intro a b h
    exact congrArg Prod.snd ((Sum.inr.injEq (s₀, a) (s₀, b)).mp h)
  have hset : (Finset.univ.filter (fun i => toricRW s₀ i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun t => Sum.inr (s₀, t)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · exact absurd (toricRW_inl s₀ ab) hi
      · refine ⟨st.2, Finset.mem_univ _, ?_⟩
        by_cases h : st.1 = s₀
        · exact congrArg Sum.inr (Prod.ext h.symm rfl)
        · rw [toricRW_inr, ite_eq_right h] at hi
          exact absurd rfl hi
    · rintro ⟨t, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [toricRW_inr, ite_eq_left rfl]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => toricRW s₀ i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **重量 $m$**：`toricRWZ` 的支撑是右半块的一整列。 -/
theorem hammingNorm_toricRWZ {m : ℕ} (t₀ : Fin m) : hammingNorm (toricRWZ t₀) = m := by
  have hinj : Function.Injective fun s : Fin m =>
      (Sum.inr (s, t₀) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := by
    intro a b h
    exact congrArg Prod.fst ((Sum.inr.injEq (a, t₀) (b, t₀)).mp h)
  have hset : (Finset.univ.filter (fun i => toricRWZ t₀ i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun s => Sum.inr (s, t₀)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · exact absurd (toricRWZ_inl t₀ ab) hi
      · refine ⟨st.1, Finset.mem_univ _, ?_⟩
        by_cases h : st.2 = t₀
        · exact congrArg Sum.inr (Prod.ext rfl h.symm)
        · rw [toricRWZ_inr, ite_eq_right h] at hi
          exact absurd rfl hi
    · rintro ⟨s, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [toricRWZ_inr, ite_eq_left rfl]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => toricRWZ t₀ i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **配对为零**：`toricRW`（右半块）与 `hgpToricZW`（左半块）支撑不交——
这正是"存活"（对易）的机制。 -/
theorem dot_toricRW_toricZW {m : ℕ} (s₀ : Fin m) :
    toricRW s₀ ⬝ᵥ hgpToricZW m = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases i with ab | st <;> simp [toricRW_inl, toricRW_inr, hgpToricZW]

/-- **配对为 1**：`toricRW s₀` 与 `toricRWZ t₀` 恰在格点 `(s₀, t₀)` 相交——
故 `toricRWZ` 是 `toricRW ∉ row H_Z` 的对偶见证。 -/
theorem dot_toricRW_toricRWZ {m : ℕ} (s₀ t₀ : Fin m) :
    toricRW s₀ ⬝ᵥ toricRWZ t₀ = 1 := by
  rw [dotProduct, Fintype.sum_sum_type]
  have hL : (∑ ab : Fin m × Fin m, toricRW s₀ (Sum.inl ab) * toricRWZ t₀ (Sum.inl ab)) = 0 :=
    Finset.sum_eq_zero fun ab _ => by rw [toricRW_inl, zero_mul]
  have hR : (∑ st : Fin m × Fin m, toricRW s₀ (Sum.inr st) * toricRWZ t₀ (Sum.inr st)) = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single s₀]
    · rw [Finset.sum_eq_single t₀]
      · rw [toricRW_inr, toricRWZ_inr, ite_eq_left rfl, ite_eq_left rfl, mul_one]
      · intro t _ ht
        rw [toricRWZ_inr, ite_eq_right ht, mul_zero]
      · intro h; exact absurd (Finset.mem_univ t₀) h
    · intro s _ hs
      exact Finset.sum_eq_zero fun t _ => by rw [toricRW_inr, ite_eq_right hs, zero_mul]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  rw [hL, hR, zero_add]

/-- 既有 X 型见证（左半块第 0 列）在直和索引下的两个分块（`rfl` 级）。 -/
theorem hgpToricXW_inl {m : ℕ} (ab : Fin m × Fin m) :
    hgpToricXW m (Sum.inl ab) = (if (ab.2 : ℕ) = 0 then 1 else 0) := rfl

theorem hgpToricXW_inr {m : ℕ} (st : Fin m × Fin m) : hgpToricXW m (Sum.inr st) = 0 := rfl

theorem hgpToricZW_inl {m : ℕ} (ab : Fin m × Fin m) :
    hgpToricZW m (Sum.inl ab) = (if (ab.1 : ℕ) = 0 then 1 else 0) := rfl

theorem hgpToricZW_inr {m : ℕ} (st : Fin m × Fin m) : hgpToricZW m (Sum.inr st) = 0 := rfl

/-- **被测逻辑与旧见证配对为 1**（对一切 $m\ge2$）：两者恰在格点 `(0,0)` 相交。

库内对 $m=9,12,16$ 有 `decide` 的实例（`toric9_dot` 等）；这里给出
**结构化**证明（对一切 $m$ 成立），因为下面"旧见证被杀死"要用它。 -/
theorem dot_toricXW_toricZW {m : ℕ} (hm : 2 ≤ m) : hgpToricXW m ⬝ᵥ hgpToricZW m = 1 := by
  obtain ⟨z, hz⟩ : ∃ z : Fin m, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  rw [dotProduct, Fintype.sum_sum_type]
  have hL : (∑ ab : Fin m × Fin m, hgpToricXW m (Sum.inl ab) * hgpToricZW m (Sum.inl ab)) = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single z]
    · rw [Finset.sum_eq_single z]
      · simp [hgpToricXW_inl, hgpToricZW_inl, hz]
      · intro t _ ht
        have ht' : ¬((t : ℕ) = 0) := fun h0 => ht (Fin.ext (h0.trans hz.symm))
        simp [hgpToricXW_inl, hgpToricZW_inl, hz, ht']
      · intro h; exact absurd (Finset.mem_univ z) h
    · intro a _ ha
      have ha' : ¬((a : ℕ) = 0) := fun h0 => ha (Fin.ext (h0.trans hz.symm))
      exact Finset.sum_eq_zero fun t _ => by simp [hgpToricXW_inl, hgpToricZW_inl, ha']
    · intro h; exact absurd (Finset.mem_univ z) h
  have hR : (∑ st : Fin m × Fin m, hgpToricXW m (Sum.inr st) * hgpToricZW m (Sum.inr st)) = 0 :=
    Finset.sum_eq_zero fun st _ => by simp [hgpToricXW_inr, hgpToricZW_inr]
  rw [hL, hR, add_zero]

/-- **左半块行见证的重量**（`hgpToricZW`，被测逻辑）：支撑是左半块的一整行。 -/
theorem hammingNorm_hgpToricZW {m : ℕ} (hm : 2 ≤ m) : hammingNorm (hgpToricZW m) = m := by
  obtain ⟨z, hz⟩ : ∃ z : Fin m, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hinj : Function.Injective fun b : Fin m =>
      (Sum.inl (z, b) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := fun a b h =>
    congrArg Prod.snd ((Sum.inl.injEq (z, a) (z, b)).mp h)
  have hset : (Finset.univ.filter (fun i => hgpToricZW m i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun b => Sum.inl (z, b)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · refine ⟨ab.2, Finset.mem_univ _, ?_⟩
        by_cases h : (ab.1 : ℕ) = 0
        · exact congrArg Sum.inl (Prod.ext (Fin.ext (h.trans hz.symm).symm) rfl)
        · rw [hgpToricZW_inl, ite_eq_right h] at hi
          exact absurd rfl hi
      · exact absurd (hgpToricZW_inr st) hi
    · rintro ⟨b, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [hgpToricZW_inl, ite_eq_left hz]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => hgpToricZW m i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **左半块列见证的重量**（`hgpToricXW`）：支撑是左半块的一整列。 -/
theorem hammingNorm_hgpToricXW {m : ℕ} (hm : 2 ≤ m) : hammingNorm (hgpToricXW m) = m := by
  obtain ⟨z, hz⟩ : ∃ z : Fin m, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hinj : Function.Injective fun a : Fin m =>
      (Sum.inl (a, z) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := fun a b h =>
    congrArg Prod.fst ((Sum.inl.injEq (a, z) (b, z)).mp h)
  have hset : (Finset.univ.filter (fun i => hgpToricXW m i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun a => Sum.inl (a, z)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · refine ⟨ab.1, Finset.mem_univ _, ?_⟩
        by_cases h : (ab.2 : ℕ) = 0
        · exact congrArg Sum.inl (Prod.ext rfl (Fin.ext (h.trans hz.symm).symm))
        · rw [hgpToricXW_inl, ite_eq_right h] at hi
          exact absurd rfl hi
      · exact absurd (hgpToricXW_inr st) hi
    · rintro ⟨a, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [hgpToricXW_inl, ite_eq_left hz]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => hgpToricXW m i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## 五、环面族的变形码（表示层 gauging）与列拍平 -/

/-- 行重排：`Fin (m*m) ≃ Fin m × Fin m`（HGP 的行指标是乘积类型，
`min_weight_ker_not_mem_rowspace` 要 `Fin` 索引，故先把行拍平）。 -/
def pairIdx (m : ℕ) : Fin (m * m) ≃ Fin m × Fin m :=
  (finProdFinEquiv (m := m) (n := m)).symm

/-- 列重排：`(Fin m × Fin m) ⊕ (Fin m × Fin m) ≃ Fin (m*m + m*m)`。 -/
def colIdx (m : ℕ) :
    ((Fin m × Fin m) ⊕ (Fin m × Fin m)) ≃ Fin (m * m + m * m) :=
  (Equiv.sumCongr (pairIdx m).symm (pairIdx m).symm).trans finSumFinEquiv

/-- 环面族 X 校验的行列表形态（按 `pairIdx` 重排到 `Fin (m*m)`，行空间与核不变）。 -/
def toricHxRows (m : ℕ) : Matrix (Fin (m * m)) ((Fin m × Fin m) ⊕ (Fin m × Fin m)) (ZMod 2) :=
  fun i => hgpHX (cycMat m) (cycMat m) (pairIdx m i)

/-- 环面族 Z 校验的行列表形态（同上，只为拿 `Fin` 索引）。 -/
def toricHzRows (m : ℕ) : Matrix (Fin (m * m)) ((Fin m × Fin m) ⊕ (Fin m × Fin m)) (ZMod 2) :=
  fun i => hgpHZ (cycMat m) (cycMat m) (pairIdx m i)

/-- **环面族变形码的 X 校验**：$H_X' = H_X + [\ell]$，$\ell$ 是被测的 X 型逻辑
`hgpToricZW m`（表示层 gauging，`Codes/Gauging.lean` 的 `deformXRows`）。
列指标取 `Fin` 形态（`colIdx` 拍平）。 -/
def toricGaugedHx (m : ℕ) : Matrix (Fin (m * m + 1)) (Fin (m * m + m * m)) (ZMod 2) :=
  (appendRow (toricHxRows m) (hgpToricZW m)).submatrix id ⇑(colIdx m).symm

/-- 环面族 Z 校验的 `Fin` 列形态。 -/
def toricHzFin (m : ℕ) : Matrix (Fin (m * m)) (Fin (m * m + m * m)) (ZMod 2) :=
  (toricHzRows m).submatrix id ⇑(colIdx m).symm

/-- 环面族 X 校验的 `Fin` 列形态（下界论证用）。 -/
def toricHxFin (m : ℕ) : Matrix (Fin (m * m)) (Fin (m * m + m * m)) (ZMod 2) :=
  (toricHxRows m).submatrix id ⇑(colIdx m).symm

/-- 存活见证（`Fin` 列形态）。 -/
def toricRWFin (m : ℕ) (s₀ : Fin m) : Vec (m * m + m * m) :=
  flatVec (colIdx m) (toricRW s₀)

/-- 对偶见证（`Fin` 列形态）。 -/
def toricRWZFin (m : ℕ) (t₀ : Fin m) : Vec (m * m + m * m) :=
  flatVec (colIdx m) (toricRWZ t₀)

/-- 行重排不改核（X 侧）。 -/
theorem mem_ker_toricHxRows {m : ℕ} {E : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2} :
    E ∈ LinearMap.ker (toricHxRows m).toLin'
      ↔ E ∈ LinearMap.ker (hgpHX (cycMat m) (cycMat m)).toLin' := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  exact ⟨fun h i => by
      have := h ((pairIdx m).symm i)
      simpa [toricHxRows, Equiv.apply_symm_apply] using this,
    fun h j => by
      have := h (pairIdx m j)
      simpa [toricHxRows] using this⟩

/-- 行重排不改核（Z 侧）。 -/
theorem mem_ker_toricHzRows {m : ℕ} {E : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2} :
    E ∈ LinearMap.ker (toricHzRows m).toLin'
      ↔ E ∈ LinearMap.ker (hgpHZ (cycMat m) (cycMat m)).toLin' := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  exact ⟨fun h i => by
      have := h ((pairIdx m).symm i)
      simpa [toricHzRows, Equiv.apply_symm_apply] using this,
    fun h j => by
      have := h (pairIdx m j)
      simpa [toricHzRows] using this⟩

/-- 行重排不改行空间（X 侧）。 -/
theorem rowSpace_toricHxRows {m : ℕ} :
    (hgpHX (cycMat m) (cycMat m)).rowSpace = (toricHxRows m).rowSpace := by
  unfold Matrix.rowSpace
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pairIdx m).symm i, by simp only [toricHxRows, Equiv.apply_symm_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨pairIdx m j, by simp only [toricHxRows]⟩

/-- 行重排不改行空间（Z 侧）。 -/
theorem rowSpace_toricHzRows {m : ℕ} :
    (hgpHZ (cycMat m) (cycMat m)).rowSpace = (toricHzRows m).rowSpace := by
  unfold Matrix.rowSpace
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pairIdx m).symm i, by simp only [toricHzRows, Equiv.apply_symm_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨pairIdx m j, by simp only [toricHzRows]⟩

/-- 变形码的行空间包含原行空间（"行空间变大"）。 -/
theorem rowSpace_toricHx_le_gaugedRows {m : ℕ} :
    (toricHxRows m).rowSpace ≤ (appendRow (toricHxRows m) (hgpToricZW m)).rowSpace :=
  rowSpace_appendRow_le _ _

/-- **`toricRW` 在变形码的核里**（存活）：与 $\ell$ 对易（配对 0）且在原核里。 -/
theorem toricRWFin_mem_ker {m : ℕ} (hm : 2 ≤ m) (s₀ : Fin m) :
    toricRWFin m s₀ ∈ LinearMap.ker (toricGaugedHx m).toLin' := by
  rw [mem_ker_toLin'_iff]
  show (appendRow (toricHxRows m) (hgpToricZW m)).submatrix id ⇑(colIdx m).symm
    *ᵥ flatVec (colIdx m) (toricRW s₀) = 0
  rw [mulVec_submatrix (appendRow (toricHxRows m) (hgpToricZW m)) (colIdx m), flatVec_comp]
  rw [mulVec_appendRow_eq_zero_iff, mulVec_eq_zero_iff]
  refine ⟨fun i => ?_, ?_⟩
  · exact congrFun (toricRW_ker hm s₀) (pairIdx m i)
  · rw [dotProduct_comm]; exact dot_toricRW_toricZW s₀

/-- **旧见证被杀死**：`hgpToricXW m`（左半块第 0 列）与被测逻辑 `hgpToricZW m`
配对为 $1$，故 gauging 之后它**不再**落在核里。

这条与 `toricRWFin_mem_ker` 合起来说明那个"重量 $m$ 存活见证"为什么必须是**新**的：`toricRW` 与 $\ell$ 支撑不交（配对 $0$）故存活，
而 `hgpToricXW` 与 $\ell$ 配对 $1$ 故被杀死。 -/
theorem toricXWFin_not_mem_ker {m : ℕ} (hm : 2 ≤ m) :
    flatVec (colIdx m) (hgpToricXW m) ∉ LinearMap.ker (toricGaugedHx m).toLin' := by
  intro hmem
  have hker := (mem_ker_submatrix (appendRow (toricHxRows m) (hgpToricZW m)) (colIdx m)
    (flatVec (colIdx m) (hgpToricXW m))).mp hmem
  rw [flatVec_comp] at hker
  rw [mem_ker_appendRow] at hker
  have hpair := hker.2
  rw [dotProduct_comm] at hpair
  exact absurd (hpair.symm.trans (dot_toricXW_toricZW hm)) zero_ne_one

/-- **`toricRWFin` 不是 Z 校验行空间元素**：对偶见证是 `toricRWZFin`。 -/
theorem toricRWFin_not_mem {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    toricRWFin m s₀ ∉ (toricHzFin m).rowSpace := by
  refine not_mem_rowSpace_of_ker_dot (toricHzFin m)
    (E := toricRWFin m s₀) (w := toricRWZFin m t₀) ?_ ?_
  · show (toricHzRows m).submatrix id ⇑(colIdx m).symm
      *ᵥ flatVec (colIdx m) (toricRWZ t₀) = 0
    rw [mulVec_submatrix (toricHzRows m) (colIdx m), flatVec_comp, mulVec_eq_zero_iff]
    intro i
    exact congrFun (toricRWZ_ker hm t₀) (pairIdx m i)
  · show flatVec (colIdx m) (toricRWZ t₀) ⬝ᵥ flatVec (colIdx m) (toricRW s₀) = 1
    rw [dotProduct_flatVec, dotProduct_comm]
    exact dot_toricRW_toricRWZ s₀ t₀

/-- **`toricRWZFin` 不在变形码的行空间里**：对偶见证是 `toricRWFin`（它在变形码核里）。
这一条需要"存活"（`toricRWFin_mem_ker`），是 Z 侧上界的关键。 -/
theorem toricRWZFin_not_mem {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    toricRWZFin m t₀ ∉ (toricGaugedHx m).rowSpace :=
  not_mem_rowSpace_of_ker_dot _ (E := toricRWZFin m t₀) (w := toricRWFin m s₀)
    (by
      rw [← mem_ker_toLin'_iff]
      exact toricRWFin_mem_ker hm s₀)
    (by
      show flatVec (colIdx m) (toricRW s₀) ⬝ᵥ flatVec (colIdx m) (toricRWZ t₀) = 1
      rw [dotProduct_flatVec]
      exact dot_toricRW_toricRWZ s₀ t₀)

/-! ## 六、双侧距离 $=m$ -/

/-- 变形码的行空间包含（列拍平后的）原 X 行空间——Z 侧下界要用。 -/
theorem rowSpace_toricHxFin_le_gauged {m : ℕ} :
    (toricHxFin m).rowSpace ≤ (toricGaugedHx m).rowSpace := by
  refine Submodule.span_mono ?_
  rintro x ⟨i, rfl⟩
  exact ⟨Fin.castSucc i, by
    funext j
    simp only [toricGaugedHx, toricHxFin, Matrix.submatrix_apply, id_eq, appendRow_castSucc]⟩

/-- X 侧下界：清洗定理（基码）＋ 一般集合包含（核只变小）。 -/
theorem toricGauged_dx_lower {m : ℕ} (hm : 2 ≤ m) {E : Vec (m * m + m * m)}
    (hker : E ∈ LinearMap.ker (toricGaugedHx m).toLin')
    (hnot : E ∉ (toricHzFin m).rowSpace) : m ≤ hammingNorm E := by
  have hker' : (E ∘ ⇑(colIdx m)) ∈
      LinearMap.ker (appendRow (toricHxRows m) (hgpToricZW m)).toLin' :=
    (mem_ker_submatrix (appendRow (toricHxRows m) (hgpToricZW m)) (colIdx m) E).mp hker
  have hnot' : (E ∘ ⇑(colIdx m)) ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace := by
    intro hmem
    rw [rowSpace_toricHzRows] at hmem
    exact hnot (unflatVec_mem_rowSpace (toricHzRows m) (colIdx m) hmem)
  have hbase := (hgp_toric_family hm).2.1 (E ∘ ⇑(colIdx m))
    ((mem_ker_toLin'_iff _ _).mp ((mem_ker_toricHxRows).mp
      ((mem_ker_appendRow (toricHxRows m) (hgpToricZW m) _).mp hker').1)) hnot'
  calc m ≤ hammingNorm (E ∘ ⇑(colIdx m)) := hbase
    _ = hammingNorm E := by
        rw [← hammingNorm_flatVec (colIdx m) (E ∘ ⇑(colIdx m))]
        congr 1
        funext j
        simp [flatVec_apply]

/-- Z 侧下界：清洗定理（基码）＋ 一般集合包含（行空间只变大）。 -/
theorem toricGauged_dz_lower {m : ℕ} (hm : 2 ≤ m) {E : Vec (m * m + m * m)}
    (hker : E ∈ LinearMap.ker (toricHzFin m).toLin')
    (hnot : E ∉ (toricGaugedHx m).rowSpace) : m ≤ hammingNorm E := by
  have hker' : (E ∘ ⇑(colIdx m)) ∈ LinearMap.ker (hgpHZ (cycMat m) (cycMat m)).toLin' :=
    (mem_ker_toricHzRows).mp ((mem_ker_submatrix (toricHzRows m) (colIdx m) E).mp hker)
  have hnot' : (E ∘ ⇑(colIdx m)) ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace := by
    intro hmem
    refine hnot (rowSpace_toricHxFin_le_gauged ?_)
    exact unflatVec_mem_rowSpace (toricHxRows m) (colIdx m) (by rwa [rowSpace_toricHxRows] at hmem)
  have hbase := (hgp_toric_family hm).2.2 (E ∘ ⇑(colIdx m))
    ((mem_ker_toLin'_iff _ _).mp hker') hnot'
  calc m ≤ hammingNorm (E ∘ ⇑(colIdx m)) := hbase
    _ = hammingNorm E := by
        rw [← hammingNorm_flatVec (colIdx m) (E ∘ ⇑(colIdx m))]
        congr 1
        funext j
        simp [flatVec_apply]

/-- 对偶见证 `toricRWZFin` 的核成员性（从直和索引的 `toricRWZ_ker` 运输）。 -/
theorem toricRWZFin_mem_ker {m : ℕ} (hm : 2 ≤ m) (t₀ : Fin m) :
    toricRWZFin m t₀ ∈ LinearMap.ker (toricHzFin m).toLin' := by
  rw [mem_ker_toLin'_iff]
  show (toricHzRows m).submatrix id ⇑(colIdx m).symm
    *ᵥ flatVec (colIdx m) (toricRWZ t₀) = 0
  rw [mulVec_submatrix (toricHzRows m) (colIdx m), flatVec_comp, mulVec_eq_zero_iff]
  intro i
  exact congrFun (toricRWZ_ker hm t₀) (pairIdx m i)

/-- 重量 $m$（`Fin` 列形态）。 -/
theorem hammingNorm_toricRWFin {m : ℕ} (s₀ : Fin m) : hammingNorm (toricRWFin m s₀) = m := by
  rw [toricRWFin, hammingNorm_flatVec]
  exact hammingNorm_toricRW s₀

/-- 重量 $m$（`Fin` 列形态）。 -/
theorem hammingNorm_toricRWZFin {m : ℕ} (t₀ : Fin m) : hammingNorm (toricRWZFin m t₀) = m := by
  rw [toricRWZFin, hammingNorm_flatVec]
  exact hammingNorm_toricRWZ t₀

/-- **X 侧变形距离 $=m$**：上界是存活见证 `toricRW`（重量 $m$、在核里、不在 `H_Z`
行空间里），下界是基码清洗定理（`hgp_toric_family`）加上"核只变小"。

与 `Codes/BB24Separation.lean` 的 BB24 实例对照：那里两侧距离都是逐实例的
内核读数；这里是**族级**读数，见证与下界论证都对一切 $m\ge2$ 成立。 -/
theorem toric_family_deformed_dx {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    min_weight_ker_not_mem_rowspace (toricGaugedHx m) (toricHzFin m) = m := by
  refine le_antisymm ?_ ?_
  · refine minWeight_le_of_witness _ _ (toricRWFin_mem_ker hm s₀)
      (toricRWFin_not_mem hm s₀ t₀) (hammingNorm_toricRWFin s₀)
  · exact le_minWeight_of_lower _ _ (by nlinarith [hm]) fun E hker hnot =>
      toricGauged_dx_lower hm hker hnot

/-- **Z 侧变形距离 $=m$**：上界是存活见证 `toricRWZ`，下界是基码清洗定理
加上"行空间只变大"。 -/
theorem toric_family_deformed_dz {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    min_weight_ker_not_mem_rowspace (toricHzFin m) (toricGaugedHx m) = m := by
  refine le_antisymm ?_ ?_
  · refine minWeight_le_of_witness _ _ (toricRWZFin_mem_ker hm t₀)
      (toricRWZFin_not_mem hm s₀ t₀) (hammingNorm_toricRWZFin t₀)
  · exact le_minWeight_of_lower _ _ (by nlinarith [hm]) fun E hker hnot =>
      toricGauged_dz_lower hm hker hnot

/-! ## 七、分离闭式的空间侧落地 -/

/-- **环面族的空间界（本模型下是定理）**：$\min(\eta,1)\cdot m \le$ 变形码距离。

这就是 `separation_judgment` 里以具名假设出现的 W–Y Lemma 2 空间界
（$d$ 处是基码距离 $m$、`spaceDist` 处是变形码距离）——在本族上它由
`toric_family_deformed_dx`（变形距离 $=m$）与 $K_m$ 的膨胀（$\min(\eta,1)=1$）闭合。 -/
theorem toric_family_space_bound {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    min (c1Witness (completeEdges m)) 1 * m
      ≤ min_weight_ker_not_mem_rowspace (toricGaugedHx m) (toricHzFin m) := by
  rw [toric_family_deformed_dx hm s₀ t₀,
    min_eq_right (one_le_c1Witness (expansionOne_complete_gen m)), one_mul]

/-- **环面族的分离闭式（空间侧不再是假设）**：变形码距离 $=m$、辅助图 $K_m$
的膨胀（C1）、轮数 $T=m$（C2）——于是 `separation_closed` 的整条假设清单里
只剩时间分量 `timeDist` 这个待定名。

对照 `toric_family_separation_closed`（`Codes/SeparationClosedForm.lean`）：
那一条仍把空间界当输入，本条把它在该族上消掉。 -/
theorem toric_family_separation_closed_spatial {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m)
    {timeDist : ℕ} (hTime : m ≤ timeDist) :
    m ≤ min (min_weight_ker_not_mem_rowspace (toricGaugedHx m) (toricHzFin m)) timeDist :=
  separation_closed (edges := completeEdges m) (d := m) (T := m)
    (expansionOne_complete_gen m) (le_refl m) (toric_family_space_bound hm s₀ t₀) hTime

/-! ## 八、W–Y Lemma 2 的计数核（引理本身的一半）

论文 [12] Methods Lemma 2 的证明可拆成三片：

1. **图论对偶**：变形码逻辑算符在边上的 X 型支撑 $M$ 与所有 flux 检查 $B_p$
   （圈）对易 $\iff$ $M$ 是 1-上循环 $\iff$ $M$ 是某个顶点集 $T$ 的**割** $\partial T$
   （割空间 $=$ 圈空间的正交补）；
2. **清洗**：乘 $\prod_{v\in T}A_v$ 把边支撑消掉、把顶点支撑从 $S$ 换成 $S\triangle T$；
   剩下的算符限制到原码比特上必须是**原码的逻辑算符**（重量 $\ge d$）；
   又因 $\prod_{v\in V}A_v$ 就是被测逻辑本身（变形码的稳定子），可取 $|T|\le|V|/2$；
3. **计数**：Cheeger 常数 $\ge1$（C1）给出 $|T|\le|\partial T|$，于是重量
   $|S|+|\partial T|+w \ge |S\triangle T| + w \ge d$。

下面这一条把**第 3 片**做成定理；第 1、2 片以显式假设写进陈述
（`hT` 是"代表元可取一半以下"、`hlog` 是"清洗后限制到原码上是逻辑算符"）。
**不声称** Lemma 2 一般情形已机器检验——见模块头 §四的诚实清单。 -/

/-- **W–Y Lemma 2 的计数核**：在辅助图膨胀 $\ge1$（C1）下，一个变形码逻辑算符的
顶点-X-支撑 $S$ 与边-X-支撑（清洗所需的割 $\partial T$）之和至少是基码距离 $d$。

假设与论文一一对应：`hG` 是 C1（$h(G)\ge1$）、`hT` 是"代表元支撑 $\le|V|/2$"、
`hlog` 是"清洗后限制到原码比特上是原码的逻辑算符"（其重量 $\ge d$）。
结论里 `w` 是算符在其余比特（原码非顶点比特、辅助比特的剩余部分）上的重量贡献。 -/
theorem space_fault_weight_ge_of_expansion {k : ℕ} (edges : List (Fin k × Fin k))
    (hG : HasExpansionOne edges) {S T : Finset (Fin k)} {d w : ℕ}
    (hT : T.card ≤ k - T.card)
    (hlog : d ≤ (S \ T ∪ T \ S).card + w) :
    d ≤ S.card + cutSize edges T + w := by
  have hcut : T.card ≤ cutSize edges T := by
    have := hG T
    rwa [min_eq_left hT] at this
  have htri : (S \ T ∪ T \ S).card ≤ S.card + T.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    exact hx.elim (fun h => Or.inl (Finset.mem_sdiff.mp h).1)
      (fun h => Or.inr (Finset.mem_sdiff.mp h).1)
  omega

end QECCertificates
