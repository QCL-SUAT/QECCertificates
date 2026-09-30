/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/

import QECCertificates.GF2.RowReduce
import LeanQEC.LinearAlgebra.RowspaceKernel

/-!
# 可计算的成员判定：让"精确距离"能由内核直接算

`Submodule.span` 的成员关系**不可判定**（它是归纳定义的谓词，没有可计算判定子），
因此 LeanQEC 的距离定义 `min_weight_ker_not_mem_rowspace` 是 `noncomputable`——
外部只能"信"SAT 求解器的输出。本模块补上缺口：把行空间与核的成员判定做成
**内核可归约的布尔计算**，并证明它们与子空间语义**逐字等价**。

于是"没有重量更轻的逻辑算符"这类下界命题可以写成一个**闭式的布尔等式**，
直接由内核归约（`by decide`）算出真假——不需要 SAT、不需要 `native_decide`、
不需要任何自定义公理。这是"距离判定证书"把外部求解器请出可信基的
关键一步。

## 两条判定的构造

* **行空间**：`inSpanB L v := reduceAgainst (rowReduce L) v = 0`。
  行消元把 `L` 化成互约化的枢轴行集；再用这套枢轴把 `v` 逐列消去——
  `v` 落在行空间里 ⟺ 消完只剩零。正确性两侧分别由
  `add_reduceAgainst_mem`（约化量的落点）与 `reduceAgainst_self_mem`
  （约化在生成元上取零 + 线性性 ⟹ 在整个行空间上取零）给出。
* **核**：`inKerB M x := ∀ i, (M i) ⬝ᵥ x = 0`——逐行正交，有限合取。
  与 LeanQEC 的 `mem_ker_iff_dotProd_rows_eq_zero` 逐字对齐。

## 主结果

* `inSpanB_iff` / `inKerB_iff`：两条判定的**语义等价定理**（可靠性 + 完备性）。
* `reduceAgainst_add` / `reduceAgainst_smul`：约化算子是**线性**的。
* `reduceAgainst_eq_zero_of_mem_spanL`：约化恰好在行空间上取零。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 约化算子的线性性 -/

/-- 约化把零映到零。 -/
lemma reduceAgainst_zero (D : List (PivRow n)) : reduceAgainst D (0 : Vec n) = 0 := by
  induction D with
  | nil => rfl
  | cons r D ih =>
      rw [reduceAgainst_cons]
      simpa using ih

/-- 约化对加法可加。 -/
lemma reduceAgainst_add (D : List (PivRow n)) :
    ∀ u v : Vec n, reduceAgainst D (u + v) = reduceAgainst D u + reduceAgainst D v := by
  induction D with
  | nil => intro u v; rfl
  | cons r D ih =>
      intro u v
      rw [reduceAgainst_cons, reduceAgainst_cons, reduceAgainst_cons]
      have harg : u + v + ((u + v) r.2) • r.1
          = (u + (u r.2) • r.1) + (v + (v r.2) • r.1) := by
        rw [Pi.add_apply, add_smul]
        ac_rfl
      rw [harg]
      exact ih _ _

/-- 约化对标量齐次。 -/
lemma reduceAgainst_smul (D : List (PivRow n)) :
    ∀ (c : ZMod 2) (v : Vec n), reduceAgainst D (c • v) = c • reduceAgainst D v := by
  induction D with
  | nil => intro c v; rfl
  | cons r D ih =>
      intro c v
      rw [reduceAgainst_cons, reduceAgainst_cons]
      have harg : c • v + ((c • v) r.2) • r.1 = c • (v + (v r.2) • r.1) := by
        rw [Pi.smul_apply, smul_eq_mul, ← smul_smul, smul_add]
      rw [harg]
      exact ih _ _

/-- 约化算子作为线性映射。 -/
def reduceAgainstLin (D : List (PivRow n)) : Vec n →ₗ[ZMod 2] Vec n where
  toFun := reduceAgainst D
  map_add' := reduceAgainst_add D
  map_smul' := reduceAgainst_smul D

/-- **约化在生成元上取零**：互约化的枢轴行集，每一行被自身消去后归零。

这是行消元"幂等性"的精确形态：处理到自己的枢轴列时，该行被整体消掉；
此后再无其它行能污染它的枢轴列（(R2) 保证别的行在该列为 0）。 -/
lemma reduceAgainst_self_mem {D : List (PivRow n)} (hD : IsReduced D) {ri : PivRow n}
    (hri : ri ∈ D) : reduceAgainst D ri.1 = 0 := by
  induction D with
  | nil => exact absurd hri (by simp)
  | cons r D ih =>
      rw [reduceAgainst_cons]
      rcases List.mem_cons.mp hri with h_eq | h_mem
      · rw [h_eq, hD.1 r (List.mem_cons_self ..), one_smul, add_self]
        exact reduceAgainst_zero D
      · by_cases hr : ri = r
        · rw [hr, hD.1 r (List.mem_cons_self ..), one_smul, add_self]
          exact reduceAgainst_zero D
        · have hD' : IsReduced D :=
            ⟨fun rj hrj => hD.1 rj (List.mem_cons_of_mem r hrj),
             fun rj hrj rk hrk hne =>
               hD.2 rj (List.mem_cons_of_mem r hrj) rk (List.mem_cons_of_mem r hrk) hne⟩
          rw [hD.2 ri (List.mem_cons_of_mem r h_mem) r (List.mem_cons_self ..) hr, zero_smul,
            add_zero]
          exact ih hD' h_mem

/-- **约化恰好在行空间上取零**：`D` 互约化时，`reduceAgainst D` 湮灭 `spanL (rowList D)`。

证明是"线性 + 在生成元上取零 ⟹ 在整个张成空间上取零"这一标准论证：
`spanL (rowList D)` 由 `rowList D` 张成，而 `reduceAgainst D` 在该集合上取零，
故 `spanL (rowList D)` 落在 `comap (reduceAgainstLin D) ⊥` 里。 -/
lemma reduceAgainst_eq_zero_of_mem_spanL {D : List (PivRow n)} (hD : IsReduced D) {v : Vec n}
    (hv : v ∈ spanL (rowList D)) : reduceAgainst D v = 0 := by
  have hle : spanL (rowList D) ≤ Submodule.comap (reduceAgainstLin D) ⊥ := by
    rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ rowList D := hx
    obtain ⟨ri, hri, hri_eq⟩ := List.mem_map.mp hx'
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_bot, ← hri_eq]
    exact reduceAgainst_self_mem hD hri
  have hv' : (reduceAgainstLin D) v ∈ (⊥ : Submodule (ZMod 2) (Vec n)) := hle hv
  rw [Submodule.mem_bot] at hv'
  exact hv'

/-! ## 行空间成员判定 -/

/-- **可计算的行空间成员判定**：把 `L` 化成互约化的枢轴行集，再用这套枢轴消去 `v`。

消完得零 ⟺ `v` 在 `L` 的行空间里（`inSpanB_iff`）。整个判定是 `List` 上的
折叠运算，因而**内核可直接归约**——这使"某个向量不是稳定子"成为可以用
`by decide` 一行算出的闭式命题。 -/
def inSpanB (L : List (Vec n)) (v : Vec n) : Bool :=
  decide (reduceAgainst (rowReduce L) v = 0)

/-- **判定可靠性**：`inSpanB` 报真则 `v` 确在行空间里。

由 `add_reduceAgainst_mem`（`v + 约化量` 落在行空间）与约化量为零直接得 `v` 落在行空间。 -/
theorem inSpanB_sound {L : List (Vec n)} {v : Vec n} (h : inSpanB L v = true) :
    v ∈ spanL L := by
  unfold inSpanB at h
  rw [decide_eq_true_eq] at h
  have hmem : v + reduceAgainst (rowReduce L) v ∈ spanL (rowList (rowReduce L)) :=
    add_reduceAgainst_mem (rowReduce L) v
  rw [h, add_zero] at hmem
  rwa [spanL_rowReduce] at hmem

/-- **判定完备性**：`v` 在行空间里则 `inSpanB` 报真。

由 `reduceAgainst_eq_zero_of_mem_spanL`（约化在行空间上取零）与行空间不变即得。 -/
theorem inSpanB_complete {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanB L v = true := by
  unfold inSpanB
  rw [decide_eq_true_eq]
  exact reduceAgainst_eq_zero_of_mem_spanL (isReduced_rowReduce L) (by rwa [spanL_rowReduce])

/-- **成员判定的语义等价**：可计算判定与子空间成员关系逐字一致。

这是把"距离/秩判定"交给内核计算的**唯一入口**：任何用 `decide` 算出的
布尔结论，都能经此定理翻译回 `Submodule` 语言，与 LeanQEC 的既有定理对接。 -/
theorem inSpanB_iff (L : List (Vec n)) (v : Vec n) : inSpanB L v = true ↔ v ∈ spanL L :=
  ⟨inSpanB_sound, inSpanB_complete⟩

/-- **判否形态的语义等价**（下界一侧消费）：报假 ⟺ 不在行空间里。 -/
theorem inSpanB_eq_false_iff (L : List (Vec n)) (v : Vec n) :
    inSpanB L v = false ↔ v ∉ spanL L := by
  constructor
  · intro h hv
    rw [(inSpanB_iff L v).mpr hv] at h
    exact absurd h (by decide)
  · intro h
    cases hb : inSpanB L v with
    | false => rfl
    | true => exact absurd ((inSpanB_iff L v).mp hb) h

/-! ## 核成员判定 -/

/-- **可计算的核成员判定**：与校验矩阵的每一行正交（GF(2) 上即对易）。

与 LeanQEC 的 `mem_ker_iff_dotProd_rows_eq_zero` 同形：核成员
`x ∈ LinearMap.ker M.toLin'` 展开后就是这个逐行合取。 -/
def inKerB {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) : Bool :=
  (List.ofFn fun i : Fin k => decide ((M i) ⬝ᵥ x = 0)).all id

/-- **核判定的语义等价**：`inKerB` 报真 ⟺ `x` 在 LeanQEC 定义的核里。

桥引理是 LeanQEC 自己的 `mem_ker_iff_dotProd_rows_eq_zero`——
于是本包的可计算判定与上游语义**没有中间层**，不需要额外的可信假设。 -/
theorem inKerB_iff {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) :
    inKerB M x = true ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [mem_ker_iff_dotProd_rows_eq_zero]
  unfold inKerB
  rw [List.all_eq_true]
  constructor
  · intro h i
    have hmem : decide ((M i) ⬝ᵥ x = 0) ∈
        List.ofFn (fun i : Fin k => decide ((M i) ⬝ᵥ x = 0)) := by
      rw [List.mem_ofFn]; exact ⟨i, rfl⟩
    simpa using h _ hmem
  · intro h b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, hi⟩ := hb
    rw [← hi]
    simpa using h i

end QECCertificates
