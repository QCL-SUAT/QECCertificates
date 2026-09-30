/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.KernelBasis

/-!
# 秩证书：`finrank (rowSpace H) = #(行消元输出)`

申请表的表 1"码率 / 秩"一行的缺口是**行消元预处理未形式化**。 已给出可信行消元；
本模块把它接成**秩证书**：把校验矩阵消元后**数行数**即得秩，且这一步在内核内可检。

## 机制

`rowReduce` 的输出是互约化的枢轴行集（`IsReduced`）。要把它变成"秩"，需要两件事：

1. **枢轴行线性无关**——在每一行自己的枢轴列上取值，行 (R1) 给出 1、(R2) 给出 0，
   故任一线性组合 `∑ cᵢ rᵢ` 在 `rⱼ` 的枢轴列上的取值恰为 `cⱼ`；
   由此 `∑ cᵢ rᵢ = 0 → cⱼ = 0`。
2. **各行互不相同**（否则 `Fin D.length` 索引不单射，第 1 条不成立）。
   本模块证明 `rowReduce` 的输出满足更强的 `NodupPiv`（**枢轴列互不相同**）：
   新增行的枢轴列处既有行全为 0、而新行为 1，故新行必不与任何既有行重合。

两件事合起来给出 `finrank (spanL (rowList (rowReduce L))) = (rowReduce L).length`，
再由  的 `spanL_rowReduce` 换成原行列表。

## 主结果

* `NodupPiv`：枢轴列互不相同的结构不变量（`rowReduce` 全程保持）。
* `linearIndependent_rowList_of_isReduced`：互约化行列表线性无关。
* `finrank_spanL_eq_length_rowReduce`：**秩 = 消元输出的行数**。
* `Matrix.rank_eq_length_rowReduce`：与 Mathlib `Matrix.rank` 的接口。
-/

namespace QECCertificates

open scoped BigOperators

-- `*ᵥ` 是 `open _root_.Matrix` 才引入的记号：在 `namespace QECCertificates` 内写 `open Matrix`
-- 会被判歧义且**静默不打开**（见规则库 #610），故一律用全限定名。
open _root_.Matrix

variable {n : ℕ}

/-! ## 枢轴列互不相同的不变量 -/

/-- `D` 的枢轴列两两不同。这是 `rowReduce` 输出的结构不变量，
也是"行数 = 秩"成立的前提（否则 `Fin D.length` 索引不单射）。 -/
def NodupPiv (D : List (PivRow n)) : Prop := (D.map (·.2)).Nodup

lemma nodupPiv_nil : NodupPiv ([] : List (PivRow n)) := by simp [NodupPiv]

/-- 插入一行后枢轴列列表只是多了一个 `p`。 -/
lemma map_piv_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    (insertPivot D w p).map (·.2) = (D.map (·.2)) ++ [p] := by
  simp [insertPivot, List.map_map, Function.comp_def]

lemma nodupPiv_insertPivot {D : List (PivRow n)} (hD : NodupPiv D) {w : Vec n} {p : Fin n}
    (hp : p ∉ D.map (·.2)) : NodupPiv (insertPivot D w p) := by
  rw [NodupPiv, map_piv_insertPivot, List.nodup_append]
  refine ⟨hD, List.nodup_singleton p, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact fun h => hp (h ▸ ha)

lemma nodupPiv_step {D : List (PivRow n)} (hred : IsReduced D) (hD : NodupPiv D) (v : Vec n) :
    NodupPiv (step D v) := by
  unfold step
  split
  · exact hD
  · rename_i hw
    refine nodupPiv_insertPivot hD ?_
    intro hmem
    obtain ⟨ri, hri, hri2⟩ := List.mem_map.mp hmem
    have h1 : reduceAgainst D v ri.2 = 0 := reduceAgainst_apply_piv hred v ri hri
    rw [hri2, leadIdx_eq_one (reduceAgainst D v) hw] at h1
    exact one_ne_zero h1

lemma nodupPiv_rowReduceFrom (D : List (PivRow n)) (rest : List (Vec n)) :
    IsReduced D → NodupPiv D → NodupPiv (rowReduceFrom D rest) := by
  induction rest generalizing D with
  | nil => intro _ hD; exact hD
  | cons v rest ih =>
      intro hred hD
      rw [rowReduceFrom_cons]
      exact ih (step D v) (isReduced_step hred v) (nodupPiv_step hred hD v)

/-- `rowReduce` 的输出枢轴列两两不同。 -/
theorem nodupPiv_rowReduce (L : List (Vec n)) : NodupPiv (rowReduce L) :=
  nodupPiv_rowReduceFrom [] L isReduced_nil nodupPiv_nil

/-- 互约化不变量的尾部仍是互约化。 -/
lemma IsReduced.tail {r : PivRow n} {D : List (PivRow n)} (h : IsReduced (r :: D)) :
    IsReduced D :=
  ⟨fun ri hri => h.1 ri (List.mem_cons_of_mem r hri),
   fun ri hri rj hrj hne =>
      h.2 ri (List.mem_cons_of_mem r hri) rj (List.mem_cons_of_mem r hrj) hne⟩

/-- 枢轴列互不相同 ⟹ 各行互不相同。 -/
lemma nodup_of_nodupPiv (D : List (PivRow n)) :
    IsReduced D → NodupPiv D → D.Nodup := by
  induction D with
  | nil => intro _ _; simp
  | cons r D ih =>
      intro hred h
      rw [List.nodup_cons]
      have hmap : (D.map (·.2)).Nodup := by
        have hh : ((r :: D).map (·.2)).Nodup := h
        rw [List.map_cons, List.nodup_cons] at hh
        exact hh.2
      refine ⟨?_, ih hred.tail hmap⟩
      intro hmem
      have hh : ((r :: D).map (·.2)).Nodup := h
      rw [List.map_cons, List.nodup_cons] at hh
      exact hh.1 (List.mem_map_of_mem hmem)

/-! ## 枢轴行线性无关 -/

/-- **互约化行列表线性无关**：在每一行自己的枢轴列上取值即可分离每个系数。 -/
theorem linearIndependent_rowList_of_isReduced {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by
  have hnod : D.Nodup := nodup_of_nodupPiv D hD hnd
  rw [linearIndependent_iff']
  intro s g hsum i hi
  -- 在 `D.get i` 的枢轴列上取值
  have h := congrFun hsum ((D.get i).2)
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hcongr : ∑ j ∈ s, g j * ((D.get j).1 ((D.get i).2))
      = ∑ j ∈ s, g j * (if j = i then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · rw [hji, ite_eq_left rfl, mul_one, hD.1 (D.get i) (List.get_mem D i), mul_one]
    · have hne : D.get j ≠ D.get i := fun hEq => hji (hnod.get_inj_iff.mp hEq)
      rw [ite_eq_right hji, mul_zero,
        hD.2 (D.get j) (List.get_mem D j) (D.get i) (List.get_mem D i) hne, mul_zero]
  rw [hcongr] at h
  have hcollapse : ∑ j ∈ s, g j * (if j = i then (1 : ZMod 2) else 0) = g i := by
    have hh := Finset.sum_eq_single (s := s)
      (f := fun j => g j * (if j = i then (1 : ZMod 2) else 0)) i
      (fun b _ hne => by rw [ite_eq_right (fun hc => hne hc), mul_zero])
      (fun hnot => absurd hi hnot)
    rwa [ite_eq_left rfl, mul_one] at hh
  rw [hcollapse] at h
  exact h

/-- `D.get` 的值域就是 `D` 的行列表。 -/
lemma range_get_eq_rowList (D : List (PivRow n)) :
    Set.range (fun i : Fin D.length => (D.get i).1) = {x | x ∈ rowList D} := by
  ext x
  rw [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.mem_map_of_mem (List.get_mem D i)
  · intro hx
    have hx' : x ∈ rowList D := hx
    rw [rowList, List.mem_map] at hx'
    obtain ⟨ri, hri, rfl⟩ := hx'
    rw [List.mem_iff_get] at hri
    obtain ⟨i, rfl⟩ := hri
    exact ⟨i, rfl⟩

/-- 枢轴列互不相同 ⟹ 枢轴列数 = 行数。 -/
lemma card_pivCols_eq_length {D : List (PivRow n)} (h : NodupPiv D) :
    (pivCols D).card = D.length := by
  rw [pivCols, List.toFinset_card_of_nodup h, List.length_map]

/-! ## 主定理 -/

/-- **秩 = 消元输出的行数**（对已消元的状态陈述）。 -/
theorem finrank_spanL_eq_length_of_isReduced {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    Module.finrank (ZMod 2) (spanL (rowList D)) = D.length := by
  have hcard := finrank_span_eq_card (linearIndependent_rowList_of_isReduced hD hnd)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList D)) = Fintype.card (Fin D.length) :=
    hcard
  simpa [Fintype.card_fin] using hcard'

/-- **秩证书（主定理）**：行列表张成的空间的维数等于行消元输出的行数。

消元产出的那列枢轴行本身就是证书：内核只需数行数、核 `IsReduced`，
即可独立核验秩——不需要信任任何外部脚本。 -/
theorem finrank_spanL_eq_length_rowReduce (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (rowReduce L).length := by
  rw [← spanL_rowReduce L]
  exact finrank_spanL_eq_length_of_isReduced (isReduced_rowReduce L) (nodupPiv_rowReduce L)

/-- 秩不超过编码长度。 -/
theorem length_rowReduce_le (L : List (Vec n)) : (rowReduce L).length ≤ n := by
  rw [← card_pivCols_eq_length (nodupPiv_rowReduce L)]
  calc (pivCols (rowReduce L)).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

/-- Mathlib 的 `Matrix.rank` 就是行空间的维数。 -/
theorem Matrix.rank_eq_finrank_rowSpace {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = Module.finrank (ZMod 2) M.rowSpace := by
  rw [Matrix.rank_eq_finrank_span_row]
  rfl

/-- **矩阵形式的秩证书**：把校验矩阵的行消元后数行数，即得其秩。

`Matrix.rank` 是 LeanQEC 侧距离归约读秩的入口；这条定理让本包验证过的
行消元直接接管该读数。 -/
theorem Matrix.rank_eq_length_rowReduce {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = (rowReduce (List.ofFn fun i => M i)).length := by
  rw [Matrix.rank_eq_finrank_rowSpace, Matrix.rowSpace_eq_spanL_ofFn]
  exact finrank_spanL_eq_length_rowReduce _

/-! ## 秩不满时的非零核向量（准入阈值那一侧的桥） -/

/-- **秩不满 $\Longrightarrow$ 非零核向量**：$M.\mathrm{rank}<n$ 时 $\ker M\ne0$。

构造是显式的：行消元后枢轴列不足 $n$ 个，于是有**自由列** $j$，`kerVec` 在那个列上取 1
（`exists_light_mem_kerL`）——它与 $M$ 的每一行正交，故被 $M$ 右乘为零。

**它是准入阈值那一侧的桥**：$k=k_1k_2+k_1^\top k_2^\top$ 的每个因子都是 $\dim\ker$，
而"核非平凡"（路线可用）要的是**存在非零核向量**，不是维数；这条换算在稿子里只用
算术说过，本定理把它落进内核。 -/
theorem exists_ne_zero_mulVec_eq_zero_of_rank_lt {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : M.rank < n) : ∃ v : Vec n, M *ᵥ v = 0 ∧ v ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, IsFreeCol (rowReduce (List.ofFn fun i => M i)) j := by
    by_contra hcon
    have hall : pivCols (rowReduce (List.ofFn fun i => M i)) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun j => ?_
      by_contra hj
      exact hcon ⟨j, fun ri hri heq => hj (mem_pivCols.mpr ⟨ri, hri, heq⟩)⟩
    have hcard := card_pivCols_eq_length (nodupPiv_rowReduce (List.ofFn fun i => M i))
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
    rw [Matrix.rank_eq_length_rowReduce] at h
    omega
  obtain ⟨v, hv, hvne, -⟩ := exists_light_mem_kerL (List.ofFn fun i => M i) hj
  refine ⟨v, ?_, hvne⟩
  have hrow : ∀ i : Fin m, (fun j => M i j) ∈ List.ofFn (fun i => M i) := by
    intro i
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  funext i
  have hdot : (fun j => M i j) ⬝ᵥ v = 0 := (mem_kerL.mp hv) _ (hrow i)
  simpa [Matrix.mulVec] using hdot

end QECCertificates
