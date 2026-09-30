/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.Basic

/-!
# 可信 GF(2) 行消元（ 第一交付物）

Lean-QEC 把"行消元本身未形式化"列为其最具体的后续工程缺口：
"A verified row-reduction routine would close this remaining preprocessor step."
本模块补上这一步：把校验矩阵的**行简化**做成机器检验的算法，
使该预处理不再需要信任外部脚本。

## 不变量

行消元的状态是一列**枢轴行** `PivRow n = Vec n × Fin n`（行向量 + 它做枢轴的列）。
`IsReduced D` 要求：

* **(R1)** 每一行在自己的枢轴列上取 1；
* **(R2)** 每一行在**别的**行的枢轴列上取 0。

(R2) 是**对称**的——不预设行的先后顺序，因此消元次序无关，
这是下面所有正确性证明能走通的关键。

## 主结果

* `reduceAgainst_apply_piv`：约化后的行在所有枢轴列上取 0。
* `add_reduceAgainst_mem`：`v + reduceAgainst D v` 落在 `D` 的行空间里。
* `spanL_rowReduce`：**行空间不变**——消元后的行空间与原来相同（码没被改动）。
* `isReduced_rowReduce`：输出满足 `IsReduced`。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-- 一个枢轴行：行向量，以及它做枢轴（首非零元）的列。 -/
abbrev PivRow (n : ℕ) := Vec n × Fin n

/-- 取出枢轴行列表的行部分。 -/
def rowList (D : List (PivRow n)) : List (Vec n) := D.map (·.1)

@[simp] lemma rowList_nil : rowList ([] : List (PivRow n)) = [] := rfl
@[simp] lemma rowList_cons (ri : PivRow n) (D : List (PivRow n)) :
    rowList (ri :: D) = ri.1 :: rowList D := rfl
@[simp] lemma rowList_append (D E : List (PivRow n)) :
    rowList (D ++ E) = rowList D ++ rowList E := List.map_append

/-- **互约化不变量**：(R1) 每行在自己枢轴列为 1；(R2) 每行在别的行的枢轴列为 0。 -/
def IsReduced (D : List (PivRow n)) : Prop :=
  (∀ ri ∈ D, ri.1 ri.2 = 1) ∧ (∀ ri ∈ D, ∀ rj ∈ D, ri ≠ rj → ri.1 rj.2 = 0)

lemma isReduced_nil : IsReduced ([] : List (PivRow n)) := ⟨by simp, by simp⟩

/-- (R2) 的直接推论：枢轴列互不相同。 -/
lemma IsReduced.pivot_inj {D : List (PivRow n)} (h : IsReduced D) :
    ∀ ri ∈ D, ∀ rj ∈ D, ri.2 = rj.2 → ri = rj := by
  intro ri hri rj hrj hij
  by_contra hne
  have h1 := h.1 ri hri
  have h2 := h.2 ri hri rj hrj hne
  rw [← hij] at h2
  rw [h1] at h2
  exact one_ne_zero h2

/-! ## 约化：把一行在所有枢轴列上清零 -/

/-- 用 `D` 中的每一行在其枢轴列上消去 `v`。GF(2) 上系数恰为 `v` 在该列的分量。 -/
def reduceAgainst (D : List (PivRow n)) (v : Vec n) : Vec n :=
  D.foldl (fun w ri => w + (w ri.2) • ri.1) v

@[simp] lemma reduceAgainst_nil (v : Vec n) : reduceAgainst ([] : List (PivRow n)) v = v := rfl

lemma reduceAgainst_cons (ri : PivRow n) (D : List (PivRow n)) (v : Vec n) :
    reduceAgainst (ri :: D) v = reduceAgainst D (v + (v ri.2) • ri.1) := by
  simp [reduceAgainst, List.foldl_cons]

/-- 若 `D` 的每一行在列 `q` 上取 0，且 `v q = 0`，则约化后第 `q` 位仍为 0。 -/
lemma reduceAgainst_eq_zero_of_rows_zero {D : List (PivRow n)} {q : Fin n} {v : Vec n}
    (hrows : ∀ ri ∈ D, ri.1 q = 0) (hv : v q = 0) : reduceAgainst D v q = 0 := by
  induction D generalizing v with
  | nil => simpa using hv
  | cons ri D ih =>
      rw [reduceAgainst_cons]
      refine ih ?_ ?_
      · intro rk hrk
        exact hrows rk (List.mem_cons_of_mem ri hrk)
      · rw [Pi.add_apply, Pi.smul_apply, hrows ri (List.mem_cons_self ..), smul_eq_mul, hv,
          mul_zero, add_zero]

/-- **核心引理**：`D` 互约化时，约化后的向量在每个枢轴列上取 0。 -/
lemma reduceAgainst_apply_piv {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    ∀ ri ∈ D, reduceAgainst D v ri.2 = 0 := by
  revert hD
  induction D generalizing v with
  | nil => intro _ ri hri; exact absurd hri (by simp)
  | cons r D ih =>
      intro hD
      have hD' : IsReduced D :=
        ⟨fun ri hri => hD.1 ri (List.mem_cons_of_mem r hri),
         fun ri hri rj hrj hne =>
           hD.2 ri (List.mem_cons_of_mem r hri) rj (List.mem_cons_of_mem r hrj) hne⟩
      rw [reduceAgainst_cons]
      intro ri hri
      rcases List.mem_cons.mp hri with hri_eq | hriD
      · rw [hri_eq]
        by_cases hrD : r ∈ D
        · exact ih _ hD' r hrD
        · refine reduceAgainst_eq_zero_of_rows_zero ?_
            (addSmul_zero_coord v r.1 r.2 (hD.1 r (List.mem_cons_self ..)))
          intro rk hrk
          exact hD.2 rk (List.mem_cons_of_mem r hrk) r (List.mem_cons_self ..)
            (fun h => hrD (h ▸ hrk))
      · exact ih _ hD' ri hriD

/-- **约化量的落点**：`v + reduceAgainst D v` 是 `D` 的行向量的线性组合。 -/
lemma add_reduceAgainst_mem (D : List (PivRow n)) (v : Vec n) :
    v + reduceAgainst D v ∈ spanL (rowList D) := by
  induction D generalizing v with
  | nil => simp
  | cons r D ih =>
      rw [reduceAgainst_cons]
      have hr : r.1 ∈ spanL (rowList (r :: D)) := subset_spanL (by simp)
      have hih : (v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1) ∈ spanL (rowList D) :=
        ih _
      have hih' : (v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1)
          ∈ spanL (rowList (r :: D)) :=
        spanL_mono_of_subset (by intro x hx; exact List.mem_cons_of_mem r.1 hx) hih
      have hmem := Submodule.add_mem _ (Submodule.smul_mem _ (v r.2) hr) hih'
      have key : v + reduceAgainst D (v + (v r.2) • r.1)
          = (v r.2) • r.1 + ((v + (v r.2) • r.1) + reduceAgainst D (v + (v r.2) • r.1)) := by
        rw [← add_assoc]
        congr 1
        exact (add_add_same_right ((v r.2) • r.1) v).symm
      rw [key]
      exact hmem

/-! ## 枢轴选取与插入 -/

lemma support_nonempty {v : Vec n} (h : v ≠ 0) :
    (Finset.univ.filter (fun i => v i ≠ 0)).Nonempty := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  exact ⟨i, by simp [hi]⟩

/-- 首个非零分量的位置（`v ≠ 0` 时有定义）。 -/
def leadIdx (v : Vec n) (h : v ≠ 0) : Fin n :=
  (Finset.univ.filter (fun i => v i ≠ 0)).min' (support_nonempty h)

lemma leadIdx_spec (v : Vec n) (h : v ≠ 0) : v (leadIdx v h) ≠ 0 := by
  unfold leadIdx
  have hm := Finset.min'_mem (Finset.univ.filter (fun i => v i ≠ 0)) (support_nonempty h)
  simpa using hm

lemma leadIdx_eq_one (v : Vec n) (h : v ≠ 0) : v (leadIdx v h) = 1 :=
  eq_one_of_ne_zero (leadIdx_spec v h)

/-- 把新行 `w`（枢轴列 `p`）并入枢轴行集：先让旧行在列 `p` 上消去，再追加 `w`。 -/
def insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D.map (fun ri => (ri.1 + (ri.1 p) • w, ri.2)) ++ [(w, p)]

lemma rowList_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivot D w p) = (rowList D).map (fun r => r + (r p) • w) ++ [w] := by
  simp [rowList, insertPivot, List.map_map, Function.comp_def]

/-- 插入不改变行空间。 -/
lemma spanL_rowList_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    spanL (rowList (insertPivot D w p)) = spanL (rowList D ++ [w]) := by
  rw [rowList_insertPivot]
  exact spanL_map_addSmul_append _ _ _

/-- 插入保持互约化不变量：要求 `w` 在 `D` 的所有枢轴列上取 0、在新枢轴列上取 1。 -/
lemma isReduced_insertPivot {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n} {p : Fin n}
    (hp : w p = 1) (hz : ∀ ri ∈ D, w ri.2 = 0) : IsReduced (insertPivot D w p) := by
  constructor
  · intro rj hrj
    rcases List.mem_append.mp hrj with hmap | hsingle
    · obtain ⟨ri, hri, rfl⟩ := List.mem_map.mp hmap
      change (ri.1 + (ri.1 p) • w) ri.2 = 1
      rw [Pi.add_apply, Pi.smul_apply, hz ri hri, smul_eq_mul, mul_zero, add_zero]
      exact hD.1 ri hri
    · have hw : rj = (w, p) := by simpa using hsingle
      rw [hw]; exact hp
  · intro ri hri rj hrj hne
    rcases List.mem_append.mp hri with hmi | hsi <;> rcases List.mem_append.mp hrj with hmj | hsj
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmi
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmj
      have hab : a.2 ≠ b.2 := by
        intro hcon
        exact hne (by rw [hD.pivot_inj a ha b hb hcon])
      change (a.1 + (a.1 p) • w) b.2 = 0
      rw [Pi.add_apply, Pi.smul_apply, hz b hb, smul_eq_mul, mul_zero, add_zero]
      exact hD.2 a ha b hb (fun h => hab (by rw [h]))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmi
      have hwj : rj = (w, p) := by simpa using hsj
      subst hwj
      change (a.1 + (a.1 p) • w) p = 0
      rw [Pi.add_apply, Pi.smul_apply, hp, smul_eq_mul, mul_one]
      exact CharTwo.add_self_eq_zero (a.1 p)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmj
      have hwi : ri = (w, p) := by simpa using hsi
      subst hwi
      exact hz a ha
    · have hwi : ri = (w, p) := by simpa using hsi
      have hwj : rj = (w, p) := by simpa using hsj
      exact absurd (hwi.trans hwj.symm) hne

/-! ## 主循环 -/

/-- 一步：把 `v` 约化后若不为零，则作为新枢轴行并入。 -/
def step (D : List (PivRow n)) (v : Vec n) : List (PivRow n) :=
  if hw : reduceAgainst D v = 0 then D
  else insertPivot D (reduceAgainst D v) (leadIdx (reduceAgainst D v) hw)

lemma spanL_rowList_step (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (step D v)) = spanL (rowList D ++ [v]) := by
  unfold step
  split
  · rename_i hw
    have hv : v ∈ spanL (rowList D) := by
      have h := add_reduceAgainst_mem D v
      rw [hw, add_zero] at h
      exact h
    have hsup : Submodule.span (ZMod 2) ({v} : Set (Vec n)) ≤ spanL (rowList D) :=
      Submodule.span_le.2 fun x hx => by
        have hx' : x = v := by simpa using hx
        rw [hx']; exact hv
    rw [spanL_append_singleton, sup_eq_left.mpr hsup]
  · rename_i hw
    rw [spanL_rowList_insertPivot]
    exact spanL_append_eq_of_add_mem (add_reduceAgainst_mem D v)

lemma isReduced_step {D : List (PivRow n)} (hD : IsReduced D) (v : Vec n) :
    IsReduced (step D v) := by
  unfold step
  split
  · exact hD
  · rename_i hw
    exact isReduced_insertPivot hD (leadIdx_eq_one (reduceAgainst D v) hw)
      (reduceAgainst_apply_piv hD v)

/-- 从累积状态 `D` 出发把 `rest` 逐行并入。 -/
def rowReduceFrom (D : List (PivRow n)) : List (Vec n) → List (PivRow n)
  | [] => D
  | v :: rest => rowReduceFrom (step D v) rest

@[simp] lemma rowReduceFrom_nil (D : List (PivRow n)) : rowReduceFrom D [] = D := rfl

@[simp] lemma rowReduceFrom_cons (D : List (PivRow n)) (v : Vec n) (rest : List (Vec n)) :
    rowReduceFrom D (v :: rest) = rowReduceFrom (step D v) rest := rfl

lemma spanL_rowList_rowReduceFrom (D : List (PivRow n)) (rest : List (Vec n)) :
    spanL (rowList (rowReduceFrom D rest)) = spanL (rowList D ++ rest) := by
  induction rest generalizing D with
  | nil => simp
  | cons v rest ih =>
      rw [rowReduceFrom_cons, ih]
      have hassoc : rowList D ++ (v :: rest) = (rowList D ++ [v]) ++ rest := by
        rw [List.append_assoc]; rfl
      rw [hassoc, spanL_append, spanL_append, spanL_rowList_step]

lemma isReduced_rowReduceFrom {D : List (PivRow n)} (hD : IsReduced D) (rest : List (Vec n)) :
    IsReduced (rowReduceFrom D rest) := by
  induction rest generalizing D with
  | nil => exact hD
  | cons v rest ih => rw [rowReduceFrom_cons]; exact ih (isReduced_step hD v)

/-- **可信行消元**：把一列行化为互约化的枢轴行集。 -/
def rowReduce (L : List (Vec n)) : List (PivRow n) := rowReduceFrom [] L

/-- **行空间不变**：消元不改变行空间，因而也不改变所定义的码。 -/
theorem spanL_rowReduce (L : List (Vec n)) : spanL (rowList (rowReduce L)) = spanL L := by
  have h := spanL_rowList_rowReduceFrom ([] : List (PivRow n)) L
  simpa [rowReduce] using h

/-- **输出互约化**：消元结果是枢轴行集（每行在自己枢轴列为 1、在别的枢轴列为 0）。 -/
theorem isReduced_rowReduce (L : List (Vec n)) : IsReduced (rowReduce L) :=
  isReduced_rowReduceFrom isReduced_nil L

end QECCertificates
