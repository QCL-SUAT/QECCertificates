/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.RankCertificate

/-!
# 规范形唯一性：行空间的消元输出是规范不变量（ 收官）

 交付了可信行消元 `rowReduce`（行空间不变 + 输出互约化）， 证明其行数即秩。
本模块补最后一条：**消元输出是行空间的规范形**——两个行列表张成同一行空间时，
消元输出的**行集合相同**。于是"两个码是否相同"可以由内核直接比较消元输出，
不必展开成 $2^n$ 个向量逐一比对。

## 为什么需要 `IsEchelon`

单靠 `IsReduced` **不足以**定规范形：`[(r, p)]` 对 `r` 的**任意**非零分量列 `p`
都满足互约化不变量（(R2) 在单行时没有约束）。真正被行空间决定的是
**枢轴列 = 该行首个非零列**（`leadIdx`），消元输出恰好满足这一点。
我们把这一条作为结构不变量单列：

`IsEchelon D := IsReduced D ∧ 每行在其枢轴列之前全为零`。

## 证明的骨架

1. **读回**（`readOff`）：`readOff D w = Σ_{ri ∈ D} (w ri.2) • ri.1`。
   `D` 互约化时它是行空间上的**恒等映射**（`readOff_eq_of_mem_spanL`，
   由 `Submodule.span_induction` 证明：它对生成元是恒等、对加法与数乘线性）。
   这条引理把"行空间的元素"翻译成"枢轴列上的取值"，是全部结构断言的入口。
2. **枢轴集合的行空间刻画**（`exists_piv_eq_leadIdx_of_mem_spanL`）：
   行空间中**任一**非零元素的首个非零列必是 `D` 的枢轴列。
   证明即上面的读回逐项计算：取系数非零的枢轴行中枢轴最小者，
   比它大的枢轴行在该列只能取零（`IsEchelon`），比它小的系数为零。
3. **合拢**：两个 echelon 行列表张成同一行空间时，
   上述刻画把两侧的枢轴集合钉成同一个（`hPiv12`/`hPiv21`），
   再用读回 + (R1)/(R2) 把每一行也钉成同一个。

## 主结果

* `readOff_eq_of_mem_spanL`：读回是行空间上的恒等。
* `pivRow_mem_iff_of_spanL_eq`：**规范形唯一性**。
* `isEchelon_rowReduce`、`rowReduce_mem_iff_of_spanL_eq`：
  `rowReduce` 的输出集合只取决于行空间（规范不变量）。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 读回 -/

/-- **读回**：按 `D` 的枢轴行重新组合 `w` 在其枢轴列上的取值。
`D` 互约化时它是行空间上的恒等映射。 -/
def readOff (D : List (PivRow n)) (w : Vec n) : Vec n :=
  ∑ ri ∈ D.toFinset, (w ri.2) • ri.1

@[simp] lemma readOff_nil (w : Vec n) : readOff ([] : List (PivRow n)) w = 0 := by
  simp [readOff]

/-- 逐分量形式：把 smul 展开成标量乘法。 -/
lemma readOff_apply (D : List (PivRow n)) (w : Vec n) (i : Fin n) :
    readOff D w i = ∑ ri ∈ D.toFinset, (w ri.2) * (ri.1 i) := by
  rw [readOff, Finset.sum_apply]
  exact Finset.sum_congr rfl fun ri _ => by rw [Pi.smul_apply, smul_eq_mul]

lemma readOff_add (D : List (PivRow n)) (x y : Vec n) :
    readOff D (x + y) = readOff D x + readOff D y := by
  simp only [readOff]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ri _ => by rw [Pi.add_apply, add_smul]

lemma readOff_smul (D : List (PivRow n)) (c : ZMod 2) (x : Vec n) :
    readOff D (c • x) = c • readOff D x := by
  simp only [readOff]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun ri _ => by
    rw [Pi.smul_apply, smul_eq_mul, smul_smul]

/-- **主引理（读回 = 恒等）**：`D` 互约化时，读回在 `D` 的行空间上是恒等映射。

证明按 `Submodule.span_induction`：生成元上，`ri` 的枢轴列把和式塌成单项
（其余项被 (R2) 杀掉）；零、加法、数乘三情形由 `readOff_add`/`readOff_smul` 给出。 -/
theorem readOff_eq_of_mem_spanL {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) : readOff D w = w := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨ri, hri, hri1⟩ := List.mem_map.mp hx
    rw [← hri1]
    simp only [readOff]
    refine (Finset.sum_eq_single (s := D.toFinset)
      (f := fun rj : PivRow n => (ri.1 rj.2) • rj.1) ri ?_ ?_).trans ?_
    · intro rj hrj hne
      rw [hD.2 ri hri rj (List.mem_toFinset.mp hrj) hne.symm, zero_smul]
    · intro hnot
      exact absurd (List.mem_toFinset.mpr hri) hnot
    · rw [hD.1 ri hri, one_smul]
  · simp only [readOff]
    refine Finset.sum_eq_zero fun ri _ => ?_
    rw [Pi.zero_apply, zero_smul]
  · intro x y _ _ hx hy
    rw [readOff_add, hx, hy]
  · intro c x _ hx
    rw [readOff_smul, hx]

/-- **零化引理**：行空间里的元素若在每个枢轴列上取零，则它是零向量。
（读回的推论——这是"枢轴列上的取值决定一切"的直接形式。） -/
lemma eq_zero_of_mem_spanL_of_piv_zero {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) (h0 : ∀ ri ∈ D, w ri.2 = 0) : w = 0 := by
  rw [← readOff_eq_of_mem_spanL hD hw]
  simp only [readOff]
  exact Finset.sum_eq_zero fun ri hri => by
    rw [h0 ri (List.mem_toFinset.mp hri), zero_smul]

/-! ## echelon 结构：枢轴列是首个非零列 -/

/-- **echelon 互约化**：`IsReduced` + "枢轴列之前全为零"。

第二条把"枢轴列"钉成 `leadIdx`（该行首个非零列）。没有它，
`[(r, p)]`（`p` 取 `r` 的任意非零分量列）都是互约化的，规范形不唯一。 -/
def IsEchelon (D : List (PivRow n)) : Prop :=
  IsReduced D ∧ ∀ ri ∈ D, ∀ i : Fin n, i < ri.2 → ri.1 i = 0

/-- 枢轴列上取 1 的行非零。 -/
lemma ne_zero_of_piv_eq_one {v : Vec n} {p : Fin n} (h : v p = 1) : v ≠ 0 :=
  fun hzero => by rw [hzero, Pi.zero_apply] at h; exact one_ne_zero h.symm

lemma leadIdx_le_of_ne_zero {v : Vec n} (h : v ≠ 0) {i : Fin n} (hi : v i ≠ 0) :
    leadIdx v h ≤ i :=
  Finset.min'_le _ i (by simp [hi])

/-- `leadIdx` 之前的分量全为零。 -/
lemma eq_zero_of_lt_leadIdx {v : Vec n} (h : v ≠ 0) {i : Fin n} (hi : i < leadIdx v h) :
    v i = 0 := by
  by_contra hne
  exact absurd (leadIdx_le_of_ne_zero h hne) (not_le.mpr hi)

/-- echelon 行列表的枢轴列就是该行的 `leadIdx`。 -/
lemma leadIdx_eq_piv_of_isEchelon {D : List (PivRow n)} (h : IsEchelon D) {ri : PivRow n}
    (hri : ri ∈ D) {hne : ri.1 ≠ 0} : leadIdx ri.1 hne = ri.2 := by
  refine le_antisymm ?_ ?_
  · exact leadIdx_le_of_ne_zero hne (by rw [h.1.1 ri hri]; exact one_ne_zero)
  · by_contra hlt
    exact absurd (h.2 ri hri (leadIdx ri.1 hne) (not_le.mp hlt)) (leadIdx_spec ri.1 hne)

/-! ## 枢轴集合的行空间刻画 -/

/-- **主引理（枢轴刻画）**：echelon 行列表张成的行空间里，任一非零元素的
首个非零列必是该列表的某个枢轴列。

这条刻画只用到了行空间本身，因此把"枢轴集合"变成**行空间的不变量**——
规范形唯一性由此落地。 -/
theorem exists_piv_eq_leadIdx_of_mem_spanL {D : List (PivRow n)} (hD : IsEchelon D)
    {w : Vec n} (hw : w ∈ spanL (rowList D)) (hw0 : w ≠ 0) :
    ∃ ri ∈ D, ri.2 = leadIdx w hw0 := by
  have hwr : w = readOff D w := (readOff_eq_of_mem_spanL hD.1 hw).symm
  let S : Finset (PivRow n) := D.toFinset.filter (fun ri => w ri.2 ≠ 0)
  have hSne : S.Nonempty := by
    by_contra hemp
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
    refine hw0 ?_
    rw [hwr]
    simp only [readOff]
    refine Finset.sum_eq_zero fun ri hri => ?_
    by_cases hc : w ri.2 = 0
    · rw [hc, zero_smul]
    · exfalso
      have hmemS : ri ∈ S := Finset.mem_filter.mpr ⟨hri, hc⟩
      rw [hSempty] at hmemS
      exact absurd hmemS (Finset.notMem_empty ri)
  obtain ⟨ri₀, hri₀S, hmin⟩ := Finset.exists_min_image S (fun ri => ri.2) hSne
  have hri₀D : ri₀ ∈ D := List.mem_toFinset.mp (Finset.mem_filter.mp hri₀S).1
  have hcoef : w ri₀.2 ≠ 0 := (Finset.mem_filter.mp hri₀S).2
  -- 支撑中每个位置都在 `ri₀.2` 之后
  have hzero : ∀ i : Fin n, w i ≠ 0 → ri₀.2 ≤ i := by
    intro i hi
    by_contra hlt
    have hlt' : i < ri₀.2 := not_le.mp hlt
    refine hi ?_
    rw [hwr, readOff_apply]
    refine Finset.sum_eq_zero fun ri hri => ?_
    by_cases hc : w ri.2 = 0
    · rw [hc, zero_mul]
    · have hriS : ri ∈ S := Finset.mem_filter.mpr ⟨hri, hc⟩
      rw [hD.2 ri (List.mem_toFinset.mp hri) i
        (lt_of_lt_of_le hlt' (hmin ri hriS)), mul_zero]
  refine ⟨ri₀, hri₀D, ?_⟩
  have hlead : leadIdx w hw0 = ri₀.2 :=
    le_antisymm (leadIdx_le_of_ne_zero hw0 hcoef) (hzero (leadIdx w hw0) (leadIdx_spec w hw0))
  exact hlead.symm

/-! ## 规范形唯一性 -/

/-- **规范形唯一性**：两个 echelon 互约化行列表张成同一行空间 ⟹ 行集合相同。

于是 `rowReduce` 的输出是行空间的**规范不变量**：码相同当且仅当消元输出的
行集合相同（`rowReduce_mem_iff_of_spanL_eq`）。 -/
theorem pivRow_mem_iff_of_spanL_eq {D₁ D₂ : List (PivRow n)} (h₁ : IsEchelon D₁)
    (h₂ : IsEchelon D₂) (hspan : spanL (rowList D₁) = spanL (rowList D₂)) :
    ∀ x : PivRow n, x ∈ D₁ ↔ x ∈ D₂ := by
  -- ① 两侧枢轴集合互相包含：每一行的枢轴列都在对面出现
  have hPiv12 : ∀ ri ∈ D₁, ∃ rj ∈ D₂, rj.2 = ri.2 := by
    intro ri hri
    have hne : ri.1 ≠ 0 := ne_zero_of_piv_eq_one (h₁.1.1 ri hri)
    have hmem : ri.1 ∈ spanL (rowList D₂) :=
      hspan ▸ subset_spanL (List.mem_map_of_mem hri)
    obtain ⟨rj, hrj, hrj2⟩ := exists_piv_eq_leadIdx_of_mem_spanL h₂ hmem hne
    exact ⟨rj, hrj, by rw [hrj2, leadIdx_eq_piv_of_isEchelon h₁ hri (hne := hne)]⟩
  have hPiv21 : ∀ rj ∈ D₂, ∃ ri ∈ D₁, ri.2 = rj.2 := by
    intro rj hrj
    have hne : rj.1 ≠ 0 := ne_zero_of_piv_eq_one (h₂.1.1 rj hrj)
    have hmem : rj.1 ∈ spanL (rowList D₁) :=
      hspan ▸ subset_spanL (List.mem_map_of_mem hrj)
    obtain ⟨ri, hri, hri2⟩ := exists_piv_eq_leadIdx_of_mem_spanL h₁ hmem hne
    exact ⟨ri, hri, by rw [hri2, leadIdx_eq_piv_of_isEchelon h₂ hrj (hne := hne)]⟩
  -- ② 枢轴集合相等（作为列集合）
  have hPivSet : (D₁.map (·.2)).toFinset = (D₂.map (·.2)).toFinset := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro p hp
      rw [List.mem_toFinset, List.mem_map] at hp
      obtain ⟨ri, hri, rfl⟩ := hp
      obtain ⟨rj, hrj, hrj2⟩ := hPiv12 ri hri
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rj, hrj, hrj2⟩)
    · intro p hp
      rw [List.mem_toFinset, List.mem_map] at hp
      obtain ⟨rj, hrj, rfl⟩ := hp
      obtain ⟨ri, hri, hri2⟩ := hPiv21 rj hrj
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨ri, hri, hri2⟩)
  -- ③ 每一行也相同：用对侧的读回表示，再用 (R1)/(R2) 塌成单项
  have hRow : ∀ x ∈ D₁, ∃ rj ∈ D₂, x = rj := by
    intro x hx
    obtain ⟨rj, hrj, hrj2⟩ := hPiv12 x hx
    have hxmem : x.1 ∈ spanL (rowList D₂) := hspan ▸ subset_spanL (List.mem_map_of_mem hx)
    have hrow : x.1 = rj.1 := by
      rw [← readOff_eq_of_mem_spanL h₂.1 hxmem]
      simp only [readOff]
      refine (Finset.sum_eq_single (s := D₂.toFinset)
        (f := fun rk : PivRow n => (x.1 rk.2) • rk.1) rj ?_ ?_).trans ?_
      · intro rk hrk hne
        have hrkD : rk ∈ D₂ := List.mem_toFinset.mp hrk
        -- `rk.2` 也是 `D₁` 的枢轴列，且异于 `x.2`，故 (R2) 杀之
        have hmemP : rk.2 ∈ (D₁.map (·.2)).toFinset := by
          rw [hPivSet]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rk, hrkD, rfl⟩)
        rw [List.mem_toFinset, List.mem_map] at hmemP
        obtain ⟨ri, hri, hri2⟩ := hmemP
        have hne' : ri ≠ x := by
          intro heq
          have hpiv : rk.2 = rj.2 := by rw [← hri2, heq, ← hrj2]
          exact hne (h₂.1.pivot_inj rk hrkD rj hrj hpiv)
        rw [← hri2, h₁.1.2 x hx ri hri hne'.symm, zero_smul]
      · intro hnot
        exact absurd (List.mem_toFinset.mpr hrj) hnot
      · rw [hrj2, h₁.1.1 x hx, one_smul]
    exact ⟨rj, hrj, Prod.ext hrow hrj2.symm⟩
  intro x
  constructor
  · intro hx
    obtain ⟨rj, hrj, rfl⟩ := hRow x hx
    exact hrj
  · intro hx
    -- 对称方向：把上面的论证对调 `D₁`/`D₂`
    obtain ⟨ri, hri, hri2⟩ := hPiv21 x hx
    have hxmem : x.1 ∈ spanL (rowList D₁) := hspan ▸ subset_spanL (List.mem_map_of_mem hx)
    have hrow : x.1 = ri.1 := by
      rw [← readOff_eq_of_mem_spanL h₁.1 hxmem]
      simp only [readOff]
      refine (Finset.sum_eq_single (s := D₁.toFinset)
        (f := fun rk : PivRow n => (x.1 rk.2) • rk.1) ri ?_ ?_).trans ?_
      · intro rk hrk hne
        have hrkD : rk ∈ D₁ := List.mem_toFinset.mp hrk
        have hmemP : rk.2 ∈ (D₂.map (·.2)).toFinset := by
          rw [← hPivSet]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rk, hrkD, rfl⟩)
        rw [List.mem_toFinset, List.mem_map] at hmemP
        obtain ⟨rj, hrj, hrj2⟩ := hmemP
        have hne' : rj ≠ x := by
          intro heq
          have hpiv : rk.2 = ri.2 := by rw [← hrj2, heq, ← hri2]
          exact hne (h₁.1.pivot_inj rk hrkD ri hri hpiv)
        rw [← hrj2, h₂.1.2 x hx rj hrj hne'.symm, zero_smul]
      · intro hnot
        exact absurd (List.mem_toFinset.mpr hri) hnot
      · rw [hri2, h₂.1.1 x hx, one_smul]
    have hxeq : x = ri := Prod.ext hrow hri2.symm
    rw [hxeq]
    exact hri

/-! ## 消元输出的规范不变性 -/

/-- **消元输出是 echelon 互约化行列表**：枢轴列恰是插入时的 `leadIdx`。 -/
theorem isEchelon_rowReduce (L : List (Vec n)) : IsEchelon (rowReduce L) := by
  have key : ∀ (D : List (PivRow n)) (rest : List (Vec n)), IsEchelon D →
      IsEchelon (rowReduceFrom D rest) := by
    intro D rest
    induction rest generalizing D with
    | nil => intro h; exact h
    | cons v rest ih =>
        intro h
        rw [rowReduceFrom_cons]
        refine ih (D := step D v) ?_
        -- 单步：`reduceAgainst` 的结果若非零，其 `leadIdx` 就是新枢轴
        unfold step
        split
        · exact h
        · rename_i hw
          constructor
          · -- IsReduced：先逐行修正旧行，再追加新行（复用既有不变量）
            have hred := isReduced_insertPivot (D := D) (w := reduceAgainst D v)
              (p := leadIdx (reduceAgainst D v) hw) h.1
              (leadIdx_eq_one (reduceAgainst D v) hw) (reduceAgainst_apply_piv h.1 v)
            simpa [insertPivot] using hred
          · -- echelon：新行以 `leadIdx` 为首非零列；旧行的修正不改变其首非零列
            intro ri hri i hi
            rw [insertPivot] at hri
            rcases List.mem_append.mp hri with hmap | hsingle
            · obtain ⟨rk, hrk, rfl⟩ := List.mem_map.mp hmap
              change (rk.1 + (rk.1 (leadIdx (reduceAgainst D v) hw))
                • reduceAgainst D v) i = 0
              rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rcases lt_trichotomy (leadIdx (reduceAgainst D v) hw) rk.2 with hlt | heq | hgt
              · -- 新枢轴在旧枢轴之前：旧行该列为 0，故修正系数为零
                rw [h.2 rk hrk _ hlt, zero_mul, add_zero, h.2 rk hrk i hi]
              · -- 新枢轴恰是旧枢轴：旧行在该列取 1，修正后相消（两侧均为 1）
                rw [heq, h.1.1 rk hrk, one_mul]
                have hi' : i < leadIdx (reduceAgainst D v) hw := by rw [heq]; exact hi
                rw [eq_zero_of_lt_leadIdx hw hi', h.2 rk hrk i hi, add_zero]
              · -- 新枢轴在旧枢轴之后：约化结果在 `leadIdx` 之前全零
                rw [eq_zero_of_lt_leadIdx hw (lt_of_lt_of_le hi hgt.le), mul_zero, add_zero,
                  h.2 rk hrk i hi]
            · have hrw : ri = (reduceAgainst D v, leadIdx (reduceAgainst D v) hw) := by
                simpa using hsingle
              rw [hrw] at hi ⊢
              exact eq_zero_of_lt_leadIdx hw hi
  exact key [] L ⟨isReduced_nil, by simp⟩

/-- **规范不变性（主定理）**：行空间相同的两个行列表，消元输出的行集合相同。

这是"码是否为同一个"在内核里的**可判定判据**：比较消元输出的行集合即可。 -/
theorem rowReduce_mem_iff_of_spanL_eq {L₁ L₂ : List (Vec n)} (h : spanL L₁ = spanL L₂)
    (x : PivRow n) : x ∈ rowReduce L₁ ↔ x ∈ rowReduce L₂ :=
  pivRow_mem_iff_of_spanL_eq (isEchelon_rowReduce L₁) (isEchelon_rowReduce L₂)
    (by rw [spanL_rowReduce, spanL_rowReduce, h]) x

end QECCertificates
