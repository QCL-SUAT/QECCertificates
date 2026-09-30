/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import Mathlib
import LeanQEC.LinearAlgebra.RowspaceKernel

/-!
# GF(2) 向量代数基元（编码理论层）

本模块是"量子信息基础库 · 编码理论层"的线性代数底座：
把量子纠错码的校验矩阵、稳定子与逻辑算符统一到 GF(2) 向量空间 `Vec n = Fin n → ZMod 2`，
给出后续"可信行消元"与"核基提取"所需的基元。

**对齐口径（申请表 §三 Q3"对齐而非重造"）**：行空间对象直接复用 LeanQEC 的
`Matrix.rowSpace`（其定义为 `Submodule.span (Set.range M)`）；本模块的 `spanL` 是它在
"行列表"一侧的等价写法，桥引理 `Matrix.rowSpace_eq_spanL_ofFn` 把两者接起来——
于是 LeanQEC 已有的行空间定理可直接作用到本包的行列表上。

## 主要定义

* `Vec n`：长度 `n` 的 GF(2) 向量（一个比特串）。
* `spanL L`：一组行所张成的子空间，即行空间。
* `addSmul v r c`：把 `c • r` 加到 `v` 上。GF(2) 上取 `c = v i`、`r i = 1` 即把第 `i` 位清零。

## 主结果

* `addSmul_apply`：逐分量计算式 `(v + c • r) i = v i + c * r i`。
* `addSmul_cancel`：特征 2 下 `(v + c • r) + c • r = v`——行操作可逆。
* `spanL_map_addSmul_append`：对整列行做该操作、再把新行追加进去，行空间不变。
* `Matrix.rowSpace_eq_spanL_ofFn`：与 LeanQEC 行空间表示的桥。
-/

namespace QECCertificates

open scoped BigOperators

/-- 长度 `n` 的 GF(2) 向量。量子纠错码的一个 Pauli 算符在辛表示下就是两个这样的向量。 -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

/-! ## 机器层通用小工具（字面量拼矩阵的模块共用）

`e`、`zeroRows`、`add_eq_zero_iff_eq` 三个定义在本模块（机器层）：它们是**通用工具**
（任何用字面量拼校验矩阵、或用特征 2 的消去律的模块都要用），不属于任何具体码族——
按本仓 `README.md` 的拆分口径，实例层不再各自复制一份。 -/

/-- GF(2) 第 `i` 个坐标的单位向量（`Vec n` 的一组基）。 -/
def e {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

/-- 零行矩阵：经典码在 `min_weight_ker_not_mem_rowspace` 的行空间一侧取它
（`rowSpace = ⊥`），于是该集合化为"核里的非零向量"。 -/
def zeroRows (n : ℕ) : Matrix (Fin 0) (Fin n) (ZMod 2) := fun i => i.elim0

/-- 特征 2 上 `a + b = 0 ↔ a = b`。 -/
lemma add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [← CharTwo.add_self_eq_zero b] at h
    exact add_right_cancel_iff.mp h
  · intro h
    rw [h, CharTwo.add_self_eq_zero]

/-- 支撑集：非零分量所在的位置。 -/
def support (v : Vec n) : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ 0)

@[simp] lemma mem_support {v : Vec n} {i : Fin n} : i ∈ support v ↔ v i ≠ 0 := by
  simp [support]

/-- 码距所用的重量：支撑集大小，与 mathlib/LeanQEC 的 `hammingNorm` 一致。 -/
lemma weight_eq_hammingNorm (v : Vec n) : (support v).card = hammingNorm v := by
  simp [support, hammingNorm]

/-- 特征 2：在 GF(2) 上向量自加为零。 -/
@[simp] lemma add_self (v : Vec n) : v + v = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (v i)

/-- GF(2) 上非零即 1。 -/
lemma eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

/-! ## 行空间 -/

/-- 一组行所张成的子空间（行空间）。生成集取"列表的元素集"，与 `Set.range` 写法可互换
（见 `spanL_ofFn_eq_span_range`）。 -/
def spanL (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) :=
  Submodule.span (ZMod 2) {x | x ∈ L}

lemma mem_spanL {L : List (Vec n)} {x : Vec n} :
    x ∈ spanL L ↔ x ∈ Submodule.span (ZMod 2) {y | y ∈ L} := Iff.rfl

lemma subset_spanL {L : List (Vec n)} {x : Vec n} (h : x ∈ L) : x ∈ spanL L :=
  Submodule.subset_span h

lemma spanL_nil : spanL ([] : List (Vec n)) = ⊥ := by
  have h : {x : Vec n | x ∈ ([] : List (Vec n))} = ∅ := by
    ext x; simp
  rw [spanL, h, Submodule.span_empty]

/-- 追加的行空间是两部分行空间的上确界。 -/
lemma spanL_append (A B : List (Vec n)) : spanL (A ++ B) = spanL A ⊔ spanL B := by
  have h : {x : Vec n | x ∈ A ++ B} = {x | x ∈ A} ∪ {x | x ∈ B} := by
    ext x; simp [List.mem_append]
  rw [spanL, h, Submodule.span_union]; rfl

/-- 单个向量张成的行空间。 -/
lemma spanL_singleton (v : Vec n) : spanL [v] = Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by
  rw [spanL]
  congr 1
  ext x
  change x ∈ [v] ↔ x ∈ ({v} : Set (Vec n))
  simp

/-- 单行版本：追加一行的行空间是原行空间与该行的上确界。 -/
lemma spanL_append_singleton (A : List (Vec n)) (v : Vec n) :
    spanL (A ++ [v]) = spanL A ⊔ Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by
  rw [spanL_append, spanL_singleton]

/-- 行空间关于列表包含单调。 -/
lemma spanL_mono_of_subset {A B : List (Vec n)} (h : A ⊆ B) : spanL A ≤ spanL B :=
  Submodule.span_mono fun _ hx => h hx

/-- 特征 2 下的消去恒等式 `(v + w) + v = w`。 -/
lemma add_add_left_cancel (v w : Vec n) : (v + w) + v = w := by
  rw [add_assoc, add_comm w v, ← add_assoc, add_self, zero_add]

/-- 特征 2 下的消去恒等式 `v + (v + w) = w`。 -/
lemma add_add_same_left (v w : Vec n) : v + (v + w) = w := by
  rw [← add_assoc, add_self, zero_add]

/-- 特征 2 下的消去恒等式 `v + (w + v) = w`。 -/
lemma add_add_same_right (v w : Vec n) : v + (w + v) = w := by
  rw [add_comm w v, add_add_same_left]

/-- 若 `v + w` 落在 `A` 的行空间内，则追加 `w` 与追加 `v` 张成同一行空间。
（消元产生的新行与原行只差一个已在行空间内的向量，故行空间不变。） -/
lemma mem_spanL_append_singleton_of_add_mem {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : w ∈ spanL (A ++ [v]) := by
  have hv : v ∈ spanL (A ++ [v]) := subset_spanL (by simp)
  have hu : v + w ∈ spanL (A ++ [v]) := spanL_mono_of_subset (by intro x hx; simp [hx]) h
  have key : (v + w) + v = w := add_add_left_cancel v w
  exact key ▸ Submodule.add_mem _ hu hv

/-- 由上一条得到行空间相等。 -/
lemma spanL_append_eq_of_add_mem {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : spanL (A ++ [w]) = spanL (A ++ [v]) := by
  have hwv : w ∈ spanL (A ++ [v]) := mem_spanL_append_singleton_of_add_mem h
  have hvw : v ∈ spanL (A ++ [w]) :=
    mem_spanL_append_singleton_of_add_mem (A := A) (v := w) (w := v)
      (by simpa [add_comm] using h)
  refine le_antisymm ?_ ?_
  · rw [spanL_append_singleton]
    refine sup_le (spanL_mono_of_subset (by intro x hx; simp [hx])) ?_
    exact Submodule.span_le.2 fun x hx => by
      have hx' : x = w := by simpa using hx
      rw [hx']; exact hwv
  · rw [spanL_append_singleton]
    refine sup_le (spanL_mono_of_subset (by intro x hx; simp [hx])) ?_
    exact Submodule.span_le.2 fun x hx => by
      have hx' : x = v := by simpa using hx
      rw [hx']; exact hvw

/-- 与 `Set.range` 写法的桥：`List.ofFn f` 的行空间就是 `f` 的值域张成的空间。 -/
lemma spanL_ofFn_eq_span_range {m : ℕ} (f : Fin m → Vec n) :
    spanL (List.ofFn f) = Submodule.span (ZMod 2) (Set.range f) := by
  rw [spanL]
  congr 1
  ext x
  change x ∈ List.ofFn f ↔ x ∈ Set.range f
  rw [List.mem_ofFn, Set.mem_range]

/-- **与 LeanQEC 的桥**：`Matrix.rowSpace M`（即 `Submodule.span (Set.range M)`）
等于 `M` 的行列表的 `spanL`。LeanQEC 的行空间定理由此可直接用于本包的行列表。 -/
theorem Matrix.rowSpace_eq_spanL_ofFn {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rowSpace = spanL (List.ofFn fun i => M i) := by
  change Submodule.span (ZMod 2) (Set.range fun i => M i) = spanL (List.ofFn fun i => M i)
  rw [spanL]
  congr 1
  ext x
  change x ∈ Set.range (fun i => M i) ↔ x ∈ List.ofFn (fun i => M i)
  rw [List.mem_ofFn, Set.mem_range]

/-! ## 初等行操作 -/

/-- 把 `c • r` 加到 `v` 上。GF(2) 上取 `c = v i`、`r i = 1` 时恰好把 `v` 的第 `i` 位清零。 -/
def addSmul (v r : Vec n) (c : ZMod 2) : Vec n := v + c • r

@[simp] lemma addSmul_apply (v r : Vec n) (c : ZMod 2) (i : Fin n) :
    addSmul v r c i = v i + c * r i := by
  simp [addSmul, Pi.add_apply, Pi.smul_apply]

/-- 取 `c = v i` 且 `r i = 1` 时，该操作把第 `i` 位清零。 -/
lemma addSmul_zero_coord (v r : Vec n) (i : Fin n) (hr : r i = 1) :
    addSmul v r (v i) i = 0 := by
  rw [addSmul_apply, hr, mul_one]
  exact CharTwo.add_self_eq_zero (v i)

/-- 特征 2 下行操作可逆：加成再加回来等于没动。 -/
lemma addSmul_cancel (v r : Vec n) (c : ZMod 2) : addSmul v r c + c • r = v := by
  simp only [addSmul]
  rw [add_assoc, add_self, add_zero]

lemma addSmul_mem_span {S : Set (Vec n)} {v r : Vec n} (c : ZMod 2)
    (hv : v ∈ Submodule.span (ZMod 2) S) (hr : r ∈ Submodule.span (ZMod 2) S) :
    addSmul v r c ∈ Submodule.span (ZMod 2) S :=
  Submodule.add_mem _ hv (Submodule.smul_mem _ c hr)

/-! ## 整列行操作保持行空间 -/

/-- **行空间保持（整列版）**：把列表 `A` 的每一行 `r` 换成 `r + f r • w`，再把 `w`
追加到末尾，所得行空间与"`A` 追加 `w`"相同。

这是行消元的正确性骨架：消元只做"把新行按系数加到旧行上"这一种操作，
不改变所张成的子空间，因而也不改变码。 -/
theorem spanL_map_addSmul_append (A : List (Vec n)) (w : Vec n) (f : Vec n → ZMod 2) :
    spanL (A.map (fun r => r + f r • w) ++ [w]) = spanL (A ++ [w]) := by
  have hwL : w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) := subset_spanL (by simp)
  have hwR : w ∈ spanL (A ++ [w]) := subset_spanL (by simp)
  refine le_antisymm ?_ ?_
  · rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ A.map (fun r => r + f r • w) ++ [w] := hx
    rw [List.mem_append, List.mem_map] at hx'
    rcases hx' with ⟨r, hr, rfl⟩ | hx'
    · exact addSmul_mem_span _ (subset_spanL (by simp [hr])) hwR
    · exact subset_spanL (by simp [hx'])
  · rw [spanL, Submodule.span_le]
    intro x hx
    have hx' : x ∈ A ++ [w] := hx
    rw [List.mem_append] at hx'
    rcases hx' with hxA | hx'
    · have h1 : x + f x • w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) :=
        subset_spanL (by simp [List.mem_map_of_mem hxA])
      have h2 : f x • w ∈ spanL (A.map (fun r => r + f r • w) ++ [w]) :=
        Submodule.smul_mem _ _ hwL
      have hmem := Submodule.add_mem _ h1 h2
      simpa [addSmul, add_assoc] using hmem
    · have hxw : x = w := by simpa using hx'
      rw [hxw]; exact hwL

end QECCertificates
