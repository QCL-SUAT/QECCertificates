/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.RankCertificate

/-!
# 只追加的梯队形秩例程（宽度大的矩阵上可用的秩读数）

## 为什么需要它

`rowReduce`（`GF2/RowReduce.lean`）输出**互约化**的枢轴行集：每插一个新枢轴，就对
**所有旧行**在新枢轴列上回代消去（`insertPivot` 的 `D.map`）。后果是**大的新枢轴行 `w`
被复制进每一个旧行元素**，下一轮 `reduceAgainst` 再把这些副本逐个重复遍历，于是项规模
**逐轮相乘**。宽度 24 上 13×13 次 `foldl` × 24 分量本应亚秒，实测却在枢轴数 ≈7 处断崖
（>200 s 不收敛、峰值工作集 >200 GB）；宽度 18 只是勉强，宽度 24 不可用。

本模块给出一条**只追加、不回代**的姊妹例程：新行并入时旧行原样不动。数学上它仍是正确的
**梯队形**——新行在**此前所有**枢轴列上为 0（这一点由 `reduceAgainst` 的折叠过程保证，
见 `reduceAgainst_get_piv_eq_zero`），故枢轴列两两不同；再取**最小**下标即可证各行线性无关。

## 与 `rowReduce` 的关系

`rankEchelon_eq_length_rowReduce`：两者给出同一个数与同一个行空间，故秩即
`rankEchelon`。于是下游的秩/`k` 断言可以**换后端**而不改任何数学；而 `rowReduce` 及其全部
下游定理（规范形唯一性 `GF2/Canonical.lean` 依赖回代消去得到的 RREF）**一字未动**。

## 写法纪律（改前先读）

`stepA` 必须是**独立的 `def`**，主循环必须写成 `List.foldl stepA []`。
把 `if hw : reduceAgainst D v = 0 then … else …` **内联进结构递归**会让 elaborator 卡死
（实测 >3 分钟零输出、单核 3.2 GB 工作集），而同样逻辑拆成独立 `def` 后立刻通过。

## 主结果

* `spanL_rowList_echelonFrom`：行空间不变（码没被改动）。
* `linearIndependent_get_of_echelon`：梯队形的各行线性无关。
* `finrank_spanL_eq_length_echelonFrom` / `rankEchelon_eq_length_rowReduce`：**秩读数**。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 只追加的枢轴插入与主循环 -/

/-- 把一个枢轴行**追加**到枢轴行集：旧行原样不动（与 `insertPivot` 的回代消去相对）。 -/
def insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) : List (PivRow n) :=
  D ++ [(w, p)]

/-- 一步：把 `v` 对本状态约化后若非零，则作为新枢轴行**追加**。 -/
def stepA (D : List (PivRow n)) (v : Vec n) : List (PivRow n) :=
  if hw : reduceAgainst D v = 0 then D
  else insertPivotA D (reduceAgainst D v) (leadIdx (reduceAgainst D v) hw)

/-- 逐行追加得到的梯队形（本模块的主循环）。 -/
def echelonFrom (L : List (Vec n)) : List (PivRow n) := L.foldl stepA []

/-- **秩例程**：只追加的梯队形之行数。 -/
def rankEchelon (L : List (Vec n)) : ℕ := (echelonFrom L).length

/-! ## 行空间不变 -/

lemma rowList_insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivotA D w p) = rowList D ++ [w] := by
  simp [rowList, insertPivotA, List.map_append]

/-- 追加与"追加约化前的原行"张成同一个行空间（约化量落在原行空间里）。 -/
lemma spanL_rowList_stepA (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (stepA D v)) = spanL (rowList D ++ [v]) := by
  unfold stepA
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
    rw [rowList_insertPivotA]
    exact spanL_append_eq_of_add_mem (add_reduceAgainst_mem D v)

/-- 主循环的泛化形式：从 `D` 出发吃 `L`，行空间恰为 `rowList D ++ L`。 -/
lemma spanL_rowList_foldl_stepA (D : List (PivRow n)) (L : List (Vec n)) :
    spanL (rowList (L.foldl stepA D)) = spanL (rowList D ++ L) := by
  induction L generalizing D with
  | nil => simp
  | cons v rest ih =>
      rw [List.foldl_cons, ih (stepA D v)]
      calc spanL (rowList (stepA D v) ++ rest)
          = spanL (rowList (stepA D v)) ⊔ spanL rest := spanL_append _ _
        _ = spanL (rowList D ++ [v]) ⊔ spanL rest := by rw [spanL_rowList_stepA]
        _ = (spanL (rowList D) ⊔ spanL [v]) ⊔ spanL rest := by rw [spanL_append]
        _ = spanL (rowList D) ⊔ (spanL [v] ⊔ spanL rest) := sup_assoc _ _ _
        _ = spanL (rowList D) ⊔ spanL ([v] ++ rest) := by rw [spanL_append]
        _ = spanL (rowList D ++ (v :: rest)) := (spanL_append _ _).symm

/-- **行空间不变**：只追加的梯队形与原行列表张成同一个行空间，因而定义同一个码。 -/
theorem spanL_rowList_echelonFrom (L : List (Vec n)) :
    spanL (rowList (echelonFrom L)) = spanL L := by
  have h := spanL_rowList_foldl_stepA ([] : List (PivRow n)) L
  simpa [echelonFrom] using h

/-! ## 梯队不变量

只追加的梯队形满足两条（比 `IsReduced` 弱：不要求旧行在后继枢轴列上为 0，这正是省掉
回代消去的代价）：

* `EchSelf`：每行在自己枢轴列上取 1；
* `EchPair`：**更靠后**的行在**所有更靠前**的行的枢轴列上取 0。

`EchPair` 是 `reduceAgainst` 折叠过程的产物：处理第 `j` 行时会把已处理行**逐个**在它们自己的
枢轴列上清零，而后续行的添加不会重新污染——因为每加一行都在**此前所有**枢轴列上为 0
（见 `reduceAgainst_get_piv_eq_zero`）。 -/

/-- 每行在自己枢轴列上取 1。 -/
def EchSelf (D : List (PivRow n)) : Prop := ∀ i : Fin D.length, (D.get i).1 (D.get i).2 = 1

/-- 更靠后的行在所有更靠前的行的枢轴列上取 0。 -/
def EchPair (D : List (PivRow n)) : Prop :=
  ∀ i j : Fin D.length, i < j → (D.get j).1 (D.get i).2 = 0

lemma EchSelf.tail {r : PivRow n} {D : List (PivRow n)} (h : EchSelf (r :: D)) : EchSelf D := by
  intro i
  have hh := h i.succ
  simpa [List.get_cons_succ'] using hh

lemma EchPair.tail {r : PivRow n} {D : List (PivRow n)} (h : EchPair (r :: D)) : EchPair D := by
  intro i j hij
  have hh := h i.succ j.succ (by simpa using hij)
  simpa [List.get_cons_succ'] using hh

/-- `EchPair` 的直接推论：头行之后的所有行在头行枢轴列上取 0。 -/
lemma EchPair.head_rows {r : PivRow n} {D : List (PivRow n)} (h : EchPair (r :: D)) :
    ∀ r' ∈ D, r'.1 r.2 = 0 := by
  intro r' hr'
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr'
  have hlt : (0 : Fin (D.length + 1)) < i.succ := by simp
  have hh := h 0 i.succ hlt
  rw [List.get_cons_zero, List.get_cons_succ'] at hh
  rw [← hi]
  exact hh

/-- **核心**：`reduceAgainst` 折叠完之后，累加子在该状态**每一个**枢轴列上取 0。

归纳式把"头行"与"其余"分开：对其余各行用归纳假设（对任意起始向量都成立），
对头行的枢轴列则用"其余各行在该列全为 0 ⟹ 折叠不改动该列"+ 起始向量在该列已归零。 -/
lemma reduceAgainst_get_piv_eq_zero {D : List (PivRow n)} (v : Vec n) (h1 : EchSelf D)
    (h2 : EchPair D) : ∀ i : Fin D.length, (reduceAgainst D v) (D.get i).2 = 0 := by
  induction D generalizing v with
  | nil => intro i; exact i.elim0
  | cons r D ih =>
      rw [reduceAgainst_cons]
      intro i
      revert i
      refine Fin.cases ?_ ?_
      · -- 头行：其余各行在其枢轴列上全为 0，故该列只由起始向量决定
        simp only [List.get_cons_zero]
        refine reduceAgainst_eq_zero_of_rows_zero (hrows := h2.head_rows) ?_
        have hr : r.1 r.2 = 1 := by
          have hh := h1 (0 : Fin (D.length + 1))
          simpa [List.get_cons_zero] using hh
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hr, mul_one]
        exact CharTwo.add_self_eq_zero (v r.2)
      · -- 其余各行：直接用归纳假设（对任意起始向量成立）
        simp only [List.get_cons_succ']
        exact ih _ h1.tail h2.tail

/-! ## 梯队形的各行线性无关 -/

/-- **梯队形各行线性无关**。

取线性组合中**系数非零的最小下标** `j`，在 `j` 行的枢轴列上取值：下标小于 `j` 的项系数为 0、
下标大于 `j` 的行在该列由 `EchPair` 为 0，于是整个组合在该列的取值恰为 `g j ≠ 0`，
与组合为 0 矛盾。 -/
theorem linearIndependent_get_of_echelon {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) :
    LinearIndependent (ZMod 2) (fun i : Fin D.length => (D.get i).1) := by
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hne₀⟩ := hcon
  -- `s` 上系数非零的最小下标
  have ht : (s.filter (fun a => g a ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hne₀⟩⟩
  set j := (s.filter (fun a => g a ≠ 0)).min' ht with hj
  have hjmem : j ∈ s ∧ g j ≠ 0 := Finset.mem_filter.mp (Finset.min'_mem _ ht)
  have hmin : ∀ a ∈ s, g a ≠ 0 → j ≤ a := fun a ha hae =>
    Finset.min'_le _ a (Finset.mem_filter.mpr ⟨ha, hae⟩)
  -- 在 `j` 行的枢轴列上取值
  have hcol := congrFun hsum ((D.get j).2)
  rw [Finset.sum_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
  have hcongr : ∑ a ∈ s, g a * ((D.get a).1 ((D.get j).2))
      = ∑ a ∈ s, g a * (if a = j then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases haj : a = j
    · rw [haj, ite_eq_left rfl, mul_one, h1 j, mul_one]
    · rcases lt_trichotomy j a with hlt | heq | hgt
      · rw [h2 j a hlt, ite_eq_right haj, mul_zero]
      · exact absurd heq.symm haj
      · have hg0 : g a = 0 := by
          by_contra hg
          exact absurd (hmin a ha hg) (not_le.mpr hgt)
        rw [hg0]; simp
  rw [hcongr] at hcol
  have hcollapse : ∑ a ∈ s, g a * (if a = j then (1 : ZMod 2) else 0) = g j := by
    have hh := Finset.sum_eq_single (s := s)
      (f := fun a => g a * (if a = j then (1 : ZMod 2) else 0)) j
      (fun b _ hne => by rw [ite_eq_right hne, mul_zero])
      (fun hnot => absurd hjmem.1 hnot)
    rwa [ite_eq_left rfl, mul_one] at hh
  rw [hcollapse] at hcol
  exact hjmem.2 hcol

/-! ## 不变量在 `stepA` 与主循环下的维护 -/

lemma echSelf_nil : EchSelf ([] : List (PivRow n)) := by intro i; exact i.elim0

lemma echPair_nil : EchPair ([] : List (PivRow n)) := by intro i; exact i.elim0

lemma length_append_singleton (D : List (PivRow n)) (x : PivRow n) :
    (D ++ [x]).length = D.length + 1 := by simp [List.length_append]

/-- `(D ++ [x])` 的第 `i` 个元素（`i` 落在 `D` 内）就是 `D` 的第 `i` 个。

`(D ++ [x]).length` 与 `D.length + 1` 对变量 `D` **不是** defeq，故索引写成显式的
`⟨i.val, _⟩`（而不是 `Fin.cast`），以免在 `Fin` 的层级上做证明搬运。 -/
lemma get_append_singleton_cast (D : List (PivRow n)) (x : PivRow n) (i : Fin D.length) :
    (D ++ [x]).get ⟨i.val, by have h := length_append_singleton D x; have := i.isLt; omega⟩ = D.get i := by
  simp only [List.get_eq_getElem, List.getElem_append_left i.isLt]

/-- `(D ++ [x])` 的末元素是 `x`。 -/
lemma get_append_singleton_last (D : List (PivRow n)) (x : PivRow n) :
    (D ++ [x]).get ⟨D.length, by have h := length_append_singleton D x; omega⟩ = x := by
  simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl D.length),
    Nat.sub_self, List.getElem_cons_zero]

lemma EchSelf_append (D : List (PivRow n)) (x : PivRow n) (hD : EchSelf D)
    (hx : x.1 x.2 = 1) : EchSelf (D ++ [x]) := by
  intro i
  rw [List.get_eq_getElem]
  by_cases h : (i : ℕ) < D.length
  · rw [List.getElem_append_left h]
    simpa [List.get_eq_getElem] using hD ⟨i.val, h⟩
  · have hlast : (D ++ [x])[(i : ℕ)] = x := by
      rw [List.getElem_append_right (by omega : D.length ≤ (i : ℕ))]
      simp [show (i : ℕ) - D.length = 0 from by
        have := length_append_singleton D x; omega]
    rw [hlast]
    exact hx

lemma EchPair_append (D : List (PivRow n)) (x : PivRow n) (hD : EchPair D)
    (hx : ∀ i : Fin D.length, x.1 (D.get i).2 = 0) : EchPair (D ++ [x]) := by
  intro i j hij
  simp only [List.get_eq_getElem]
  by_cases hj : (j : ℕ) < D.length
  · have hi : (i : ℕ) < D.length := by omega
    rw [List.getElem_append_left hj, List.getElem_append_left hi]
    exact hD ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
  · have hjlast : (D ++ [x])[(j : ℕ)] = x := by
      rw [List.getElem_append_right (by omega : D.length ≤ (j : ℕ))]
      simp [show (j : ℕ) - D.length = 0 from by
        have := length_append_singleton D x; omega]
    have hi : (i : ℕ) < D.length := by
      have := length_append_singleton D x; omega
    rw [hjlast, List.getElem_append_left hi]
    simpa [List.get_eq_getElem] using hx ⟨i.val, hi⟩

lemma EchSelf_stepA {D : List (PivRow n)} (h1 : EchSelf D) (v : Vec n) :
    EchSelf (stepA D v) := by
  unfold stepA
  split
  · exact h1
  · rename_i hw
    exact EchSelf_append D _ h1 (leadIdx_eq_one (reduceAgainst D v) hw)

lemma EchPair_stepA {D : List (PivRow n)} (h1 : EchSelf D) (h2 : EchPair D) (v : Vec n) :
    EchPair (stepA D v) := by
  unfold stepA
  split
  · exact h2
  · rename_i hw
    exact EchPair_append D _ h2 fun i => reduceAgainst_get_piv_eq_zero v h1 h2 i

lemma echSelf_echelonFrom_foldl (D : List (PivRow n)) (L : List (Vec n))
    (h1 : EchSelf D) (h2 : EchPair D) :
    EchSelf (L.foldl stepA D) ∧ EchPair (L.foldl stepA D) := by
  induction L generalizing D with
  | nil => exact ⟨h1, h2⟩
  | cons v rest ih =>
      rw [List.foldl_cons]
      exact ih (stepA D v) (EchSelf_stepA h1 v) (EchPair_stepA h1 h2 v)

/-- 只追加的梯队形满足两条不变量。 -/
theorem echelonFrom_ech (L : List (Vec n)) :
    EchSelf (echelonFrom L) ∧ EchPair (echelonFrom L) :=
  echSelf_echelonFrom_foldl [] L echSelf_nil echPair_nil

/-! ## 秩读数 -/

/-- **秩 = 只追加梯队形的行数**。 -/
theorem finrank_spanL_eq_length_echelonFrom (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (echelonFrom L).length := by
  have h := echelonFrom_ech L
  have hcard := finrank_span_eq_card (linearIndependent_get_of_echelon h.1 h.2)
  rw [range_get_eq_rowList] at hcard
  -- `spanL` 的展开与 `Fintype.card (Fin k) = k` 都不是 defeq 级，需显式搬一次
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList (echelonFrom L)))
      = Fintype.card (Fin (echelonFrom L).length) := hcard
  rw [Fintype.card_fin] at hcard'
  rw [← spanL_rowList_echelonFrom L]
  exact hcard'

/-- **桥定理**：只追加的梯队形与 `rowReduce` 给出同一个秩。

两者都是同一个贪婪枢轴计数的输出（行空间相同、行数即秩），故下游的秩/`k` 断言可以
**换后端**而不改数学；`rowReduce` 及其下游（`GF2/Canonical.lean` 的规范形唯一性依赖
回代消去得到的 RREF）一字未动。 -/
theorem rankEchelon_eq_length_rowReduce (L : List (Vec n)) :
    rankEchelon L = (rowReduce L).length := by
  rw [rankEchelon, ← finrank_spanL_eq_length_rowReduce L,
    finrank_spanL_eq_length_echelonFrom L]

/-- 矩阵形式的接口：校验矩阵的秩。 -/
theorem Matrix.rank_eq_rankEchelon {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.rank = rankEchelon (List.ofFn fun i => M i) := by
  rw [Matrix.rank_eq_length_rowReduce, rankEchelon_eq_length_rowReduce]

/-! ## 成员判定的快速后端（`echelonFrom` 代替 `rowReduce`）

`inSpanB`（`GF2/Membership.lean`）用 `rowReduce` 的输出判定行空间成员关系。在**每个候选上
重算一次**的场合（如 `lightCand` 的重量限定枚举），这是数量级的差别：宽度 24 上
`rowReduce` 第 7 行起 >200 s，而 `echelonFrom` 毫秒级。

**关键观察**：成员判定**不需要** `rowReduce` 的**完全约化**（RREF），**只追加的梯队形就够**。
`reduceAgainst` 的"消去枢轴列"论证只用 `EchPair`（后行在先行枢轴列为 0），而 RREF 原本
承担的那一步（"落在行空间里、且在所有枢轴列为 0 的向量必为零"）由**取系数表示的最小下标**补上。 -/

/-- **梯队形下"枢轴列全零 ⟹ 是零"**：`w` 落在 `rowList D` 的张成里，且在 `D` 的**每个**
枢轴列上取 0，则 `w = 0`。

论证：取 `w` 的系数表示 `w = Σ cᵢ rᵢ`，令 `j` 为**最小**的下标使 `cⱼ ≠ 0`。在 `pⱼ` 上取值，
`i > j` 的项由 `EchPair` 归零、`i < j` 的项系数为 0，故 `w pⱼ = cⱼ ≠ 0`，与假设矛盾。
这一条正是 `IsReduced` 的对称条件 (R2) 原本承担的部分。 -/
theorem eq_zero_of_mem_spanL_of_piv_eq_zero {D : List (PivRow n)} (h1 : EchSelf D)
    (h2 : EchPair D) {w : Vec n} (hw : w ∈ spanL (rowList D))
    (h0 : ∀ i : Fin D.length, w (D.get i).2 = 0) : w = 0 := by
  -- 取系数表示 `w = Σ cᵢ rᵢ`（行空间即各行所张成的空间）
  have hspan : spanL (rowList D)
      = Submodule.span (ZMod 2) (Set.range fun i : Fin D.length => (D.get i).1) := by
    rw [spanL, range_get_eq_rowList D]
  have hw' : w ∈ Submodule.span (ZMod 2)
      (Set.range fun i : Fin D.length => (D.get i).1) := by
    rw [← hspan]
    exact hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)
    (v := fun i : Fin D.length => (D.get i).1) (x := w)).mp hw'
  by_contra hw0
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (by rw [← hc]; exact Finset.sum_eq_zero fun i _ => by rw [h i, zero_smul])
  obtain ⟨i₀, hi₀⟩ := hex
  have ht : (Finset.univ.filter (fun a => c a ≠ 0)).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  set j := (Finset.univ.filter (fun a => c a ≠ 0)).min' ht with hj
  have hjne : c j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ ht)).2
  have hmin : ∀ a, c a ≠ 0 → j ≤ a := fun a ha =>
    Finset.min'_le _ a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
  have hcol := congrFun hc ((D.get j).2)

  rw [Finset.sum_apply] at hcol
  simp only [Pi.smul_apply, smul_eq_mul] at hcol
  have hcongr : ∑ i, c i * ((D.get i).1 ((D.get j).2))
      = ∑ i, c i * (if i = j then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · rw [hij, ite_eq_left rfl, mul_one, h1 j, mul_one]
    · rcases lt_trichotomy i j with hlt | heq | hgt
      · -- `i < j`：由最小性 `c i = 0`（注意 `EchPair` 管的是 `j < i` 那一侧）
        have hc0 : c i = 0 := by
          by_contra hc'
          exact absurd (hmin i hc') (not_le.mpr hlt)
        rw [hc0]; simp
      · exact absurd heq hij
      · -- `j < i`：更靠后的行在 `pⱼ` 上取 0
        rw [h2 j i hgt, ite_eq_right hij, mul_zero]
  rw [hcongr] at hcol
  have hcollapse : ∑ i, c i * (if i = j then (1 : ZMod 2) else 0) = c j := by
    have hh := Finset.sum_eq_single (s := Finset.univ)
      (f := fun i => c i * (if i = j then (1 : ZMod 2) else 0)) j
      (fun b _ hne => by rw [ite_eq_right hne, mul_zero])
      (fun hnot => absurd (Finset.mem_univ j) hnot)
    rwa [ite_eq_left rfl, mul_one] at hh
  rw [hcollapse] at hcol
  exact hjne (by rw [hcol, h0 j])

/-- **约化恰好在行空间上取零（梯队形后端）**：`echelonFrom` 的输出湮灭原行列表的张成。

与 `GF2/Membership.lean` 的 `reduceAgainst_eq_zero_of_mem_spanL`（`IsReduced` 版）平行，
但前提只用到 `EchSelf`/`EchPair`；RREF 原本承担的那一步由
`eq_zero_of_mem_spanL_of_piv_eq_zero` 补上。 -/
theorem reduceAgainst_echelonFrom_eq_zero_of_mem_spanL {L : List (Vec n)} {v : Vec n}
    (hv : v ∈ spanL L) : reduceAgainst (echelonFrom L) v = 0 := by
  have hech := echelonFrom_ech L
  have hmem : v + reduceAgainst (echelonFrom L) v ∈ spanL L := by
    have h := add_reduceAgainst_mem (echelonFrom L) v
    rwa [spanL_rowList_echelonFrom] at h
  refine eq_zero_of_mem_spanL_of_piv_eq_zero hech.1 hech.2 ?_
    (reduceAgainst_get_piv_eq_zero v hech.1 hech.2)
  rw [spanL_rowList_echelonFrom]
  have hsplit : (v + reduceAgainst (echelonFrom L) v) + v
      = reduceAgainst (echelonFrom L) v := by
    rw [add_assoc, add_add_same_right]
  rw [← hsplit]
  exact Submodule.add_mem _ hmem hv

/-! ## 可计算成员判定：梯队形后端

与 `GF2/Membership.lean` 的 `inSpanB` 同数学内容、同接口形状，只换归约后端。
在**每个候选上判一次**的场合（`lightCand` 的重量限定枚举，$[[24,3,4]]$ 有 2325 个候选）
这是数量级的差别：宽度 24 上 `rowReduce` 第 7 行起 >200 s 不收敛，而 `echelonFrom` 毫秒级。 -/

/-- **可计算的行空间成员判定（梯队形后端）**。 -/
def inSpanEch (L : List (Vec n)) (v : Vec n) : Bool :=
  decide (reduceAgainst (echelonFrom L) v = 0)

theorem inSpanEch_sound {L : List (Vec n)} {v : Vec n} (h : inSpanEch L v = true) :
    v ∈ spanL L := by
  unfold inSpanEch at h
  rw [decide_eq_true_eq] at h
  have hmem : v + reduceAgainst (echelonFrom L) v ∈ spanL (rowList (echelonFrom L)) :=
    add_reduceAgainst_mem (echelonFrom L) v
  rw [h, add_zero] at hmem
  rwa [spanL_rowList_echelonFrom] at hmem

theorem inSpanEch_complete {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanEch L v = true := by
  unfold inSpanEch
  rw [decide_eq_true_eq]
  exact reduceAgainst_echelonFrom_eq_zero_of_mem_spanL hv

/-- **成员判定的语义等价（梯队形后端）**：与 `inSpanB` 给出同一个布尔值。 -/
theorem inSpanEch_iff (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = true ↔ v ∈ spanL L :=
  ⟨inSpanEch_sound, inSpanEch_complete⟩

/-! ## 显式秩证书

行消元的代价随**宽度**陡增；宽度大到 `rowReduce`/`echelonFrom` 跑不动时，秩仍可以
**核一个证书**得到。两侧各有一个便宜的判据：

* **下界**：给出一列**互异枢轴**的候选行 `D`，每行都落在 `spanL L` 里。若这些行**定义为**
  `L` 行的线性组合（`Submodule.add_mem` 逐项拼），成员关系是代数、与宽度无关；枢轴互异是
  有限判定、可 `decide`。于是 `D.length ≤ dim spanL L`（`length_le_finrank_spanL_of_certificate`）。
* **上界**：给出**冗余生成元**——把 `L` 写成 `A ++ B`，并证明 `B` 的每一行落在 `spanL A` 里，
  则 `dim spanL L ≤ A.length`（`finrank_spanL_append_le_of_mem`）。每条冗余关系是一次
  "某行 = 若干行的和"的等式判定，可 `decide`。

两条都是**逐行/逐关系**的检查，量级与宽度线性；`Codes/BB98Rank.lean` 是宽 98 上的实例
（哪里不能做行消元，见 `Codes/FoldTransversal98.lean` 的模块头）。 -/

/-- **`spanL A` 的维数不超过 `A` 的长度**：`A` 是生成集。 -/
theorem finrank_spanL_le_length (A : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL A) ≤ A.length := by
  have h : spanL A = Submodule.span (ZMod 2) (Set.range fun i : Fin A.length => A.get i) := by
    rw [spanL]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    exact List.mem_iff_get
  rw [h]
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i : Fin A.length => A.get i))
      ≤ (Set.range (fun i : Fin A.length => A.get i)).toFinset.card := finrank_span_le_card _
    _ = Fintype.card ↑(Set.range fun i : Fin A.length => A.get i) := Set.toFinset_card _
    _ ≤ Fintype.card (Fin A.length) := Fintype.card_range_le _
    _ = A.length := Fintype.card_fin _

/-- **生成元冗余给出的秩上界（集合形态）**：若 `L` 的每一行都落在 `spanL A` 里，
则 `dim spanL L ≤ A.length`。`A` 不必是 `L` 的前缀——`spanL` 只看元素集合，
故"在 `L` 里挑出 `head` 个张成整表的行"与"整表由这 `head` 个生成元张成"是一回事。
`BB144` 的校验矩阵前 66 行不满秩（秩 64），只能用这一形态。 -/
theorem finrank_spanL_le_of_mem_of_subset {A L : List (Vec n)}
    (h : ∀ v ∈ L, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL L) ≤ A.length := by
  have hle : spanL L ≤ spanL A := Submodule.span_le.mpr h
  exact le_trans (Submodule.finrank_mono hle) (finrank_spanL_le_length A)

/-- **冗余生成元给出的秩上界（前缀形态）**：把行列表写成 `A ++ B`，若 `B` 的每一行都落在
`spanL A` 里，则整张行列表的维数不超过 `A.length`。 -/
theorem finrank_spanL_append_le_of_mem (A B : List (Vec n))
    (h : ∀ v ∈ B, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL (A ++ B)) ≤ A.length := by
  have hA : ∀ v ∈ A ++ B, v ∈ spanL A := by
    intro v hv
    rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact subset_spanL hv
    · exact h v hv
  exact finrank_spanL_le_of_mem_of_subset hA

/-- **证书给出的秩下界**：`D` 的每一行落在 `spanL L` 里、且 `D` 满足梯队不变量，
则 `D.length ≤ dim spanL L`。 -/
theorem length_le_finrank_spanL_of_certificate {L : List (Vec n)} {D : List (PivRow n)}
    (hsub : ∀ i : Fin D.length, (D.get i).1 ∈ spanL L)
    (h1 : EchSelf D) (h2 : EchPair D) :
    D.length ≤ Module.finrank (ZMod 2) (spanL L) := by
  have hcard := finrank_span_eq_card (linearIndependent_get_of_echelon h1 h2)
  rw [range_get_eq_rowList] at hcard
  -- `spanL` 的展开与 `Fintype.card (Fin k) = k` 都不是 defeq 级，需显式搬一次
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList D)) = Fintype.card (Fin D.length) := hcard
  rw [Fintype.card_fin] at hcard'
  have hle : spanL (rowList D) ≤ spanL L := by
    rw [spanL, Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact hsub i
  calc D.length = Module.finrank (ZMod 2) (spanL (rowList D)) := hcard'.symm
    _ ≤ Module.finrank (ZMod 2) (spanL L) := Submodule.finrank_mono hle

/-- **判否形态（梯队形后端）**：下界一侧消费。 -/
theorem inSpanEch_eq_false_iff (L : List (Vec n)) (v : Vec n) :
    inSpanEch L v = false ↔ v ∉ spanL L := by
  constructor
  · intro h hv
    rw [(inSpanEch_iff L v).mpr hv] at h
    exact absurd h (by decide)
  · intro h
    cases hb : inSpanEch L v with
    | false => rfl
    | true => exact absurd ((inSpanEch_iff L v).mp hb) h

end QECCertificates
