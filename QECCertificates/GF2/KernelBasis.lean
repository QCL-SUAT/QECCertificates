/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.RowReduce

/-!
# 核基提取与完备性（ 第二交付物）

Lean-QEC 的核基（校验矩阵的零空间基）由**外部 Python 脚本**产出，脚本的正确性
不在可信基内——论文自陈其只对"秩与正交性"做事后检验。本模块给出**内核内证明**：从行消元的枢轴结构直接读出一组生成元，并证明

  `ker(H) = span(核生成元)`

两个方向都在 Lean 内核内闭合。有了它，"核基由外部脚本产出"这一步从可信基里消失。

## 机制

行消元输出互约化的枢轴行集 `D`（见 `IsReduced`）。枢轴列是"被占住"的列，
其余列为**自由列**。对每个自由列 `j`，核向量取

  `kerVec D j := e_j + ∑_{r ∈ D} (r_j) · e_{pivot(r)}`

即在 `e_j` 上按各行在 `j` 列的分量补上枢轴方向。正交性来自 (R2)：
每个行在自己枢轴列上取 1、在别的行的枢轴列上取 0，两类贡献恰好相消。

## 主结果

* `kerVec_mem_kerL`：核向量确实落在核里（可靠性方向）。
* `kerL_le_spanL_kerBasis`：核里每个向量都是核生成元的线性组合（**完备性方向**）。
* `kerL_rowReduce`：`ker H = span (kerBasis (rowReduce H))`——两侧合拢。
* `hammingNorm_kerVec_le` / `kerVec_ne_zero` / `exists_light_mem_kerL`：
  **Singleton 型计数**——核非平凡时核里有一个重量 $\le$ 秩 $+1$ 的非零元。
  前沿界的论证（`paper/sm.tex` 的 "the frontier argument"）用到的正是这一步。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-- 单位向量 `e_i`（第 `i` 位为 1，其余为 0）。 -/
def unitVec (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

@[simp] lemma unitVec_apply (i j : Fin n) : unitVec i j = if j = i then 1 else 0 := rfl

/-! ## 单项求和助手（把"按列挑一项"的和塌成单项） -/

/-- `∑ i, u i * (if i = a then 1 else 0) = u a`。 -/
lemma sum_mul_ite_self (u : Vec n) (a : Fin n) :
    ∑ i, u i * (if i = a then (1 : ZMod 2) else 0) = u a := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => u i * (if i = a then (1 : ZMod 2) else 0)) a
    (fun b _ hne => by rw [ite_eq_right (fun h => hne h), mul_zero])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, ite_eq_left rfl, mul_one]

/-- `∑ i, u i * (if a = i then c else 0) = u a * c`。 -/
lemma sum_mul_ite_eq (u : Vec n) (a : Fin n) (c : ZMod 2) :
    ∑ i, u i * (if a = i then c else 0) = u a * c := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => u i * (if a = i then c else 0)) a
    (fun b _ hne => by rw [ite_eq_right (fun h => hne h.symm), mul_zero])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, ite_eq_left rfl]

/-- `∑ i, (if i = a then u i else 0) = u a`。 -/
lemma sum_ite_self (u : Vec n) (a : Fin n) :
    ∑ i, (if i = a then u i else 0) = u a := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun i => if i = a then u i else 0) a
    (fun b _ hne => by rw [ite_eq_right (fun h => hne h)])
    (fun hnot => absurd (Finset.mem_univ a) hnot)
  rw [h, ite_eq_left rfl]

/-! ## 核 -/

/-- 行列表的核：与每一行都正交（GF(2) 点积为零）的向量全体。

这是量子纠错码的**错误空间**的代数刻画：与所有校验行对易的 Pauli 算符。
与 LeanQEC 的 `LinearMap.ker M.toLin'` 通过 `mem_ker_iff_dotProd_rows_eq_zero` 对接。 -/
def kerL (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) where
  carrier := {x | ∀ r ∈ L, r ⬝ᵥ x = 0}
  zero_mem' := by intro r _; simp
  add_mem' := by
    intro x y hx hy r hr
    rw [dotProduct_add, hx r hr, hy r hr, add_zero]
  smul_mem' := by
    intro c x hx r hr
    rw [dotProduct_smul, hx r hr, smul_zero]

@[simp] lemma mem_kerL {L : List (Vec n)} {x : Vec n} :
    x ∈ kerL L ↔ ∀ r ∈ L, r ⬝ᵥ x = 0 := Iff.rfl

/-- 核只依赖行空间：行空间相同的两个行列表给出相同的核。 -/
lemma kerL_eq_of_spanL_eq {A B : List (Vec n)} (h : spanL A = spanL B) : kerL A = kerL B := by
  have key : ∀ {P Q : List (Vec n)}, spanL P ≤ spanL Q → kerL Q ≤ kerL P := by
    intro P Q hPQ x hx
    rw [mem_kerL] at hx ⊢
    intro p hp
    exact Submodule.span_induction
      (fun y hy => hx y hy) (by simp)
      (fun u v _ _ ihu ihv => by rw [add_dotProduct, ihu, ihv, add_zero])
      (fun c u _ ihu => by rw [smul_dotProduct, ihu, smul_zero])
      (hPQ (subset_spanL hp))
  exact le_antisymm (key h.ge) (key h.le)

/-! ## 枢轴列与自由列 -/

/-- 枢轴列集合。 -/
def pivCols (D : List (PivRow n)) : Finset (Fin n) := (D.map (·.2)).toFinset

/-- 自由列：不是任何行的枢轴列的列。 -/
def IsFreeCol (D : List (PivRow n)) (j : Fin n) : Prop := ∀ ri ∈ D, ri.2 ≠ j

lemma mem_pivCols {D : List (PivRow n)} {i : Fin n} :
    i ∈ pivCols D ↔ ∃ ri ∈ D, ri.2 = i := by
  rw [pivCols, List.mem_toFinset, List.mem_map]

/-- (R2) 的配对形式：任一枢轴行在任一枢轴列上的取值是 Kronecker 型的。 -/
lemma IsReduced.row_apply_piv {D : List (PivRow n)} (hD : IsReduced D)
    {ri rj : PivRow n} (hri : ri ∈ D) (hrj : rj ∈ D) :
    ri.1 rj.2 = if ri = rj then 1 else 0 := by
  by_cases h : ri = rj
  · rw [ite_eq_left h, h]; exact hD.1 rj hrj
  · rw [ite_eq_right h]; exact hD.2 ri hri rj hrj h

/-! ## 核向量 -/

/-- 自由列 `j` 对应的核向量：`e_j` 加上由各行在 `j` 列的分量决定的枢轴修正。 -/
def kerVec (D : List (PivRow n)) (j : Fin n) : Vec n :=
  fun i => (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0)

lemma kerVec_apply (D : List (PivRow n)) (j i : Fin n) :
    kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) := rfl

/-- 自由列上核向量就是 `e_j`：修正项全为零。 -/
lemma kerVec_apply_free {D : List (PivRow n)} {j i : Fin n} (hi : IsFreeCol D i) :
    kerVec D j i = if i = j then 1 else 0 := by
  rw [kerVec_apply]
  have hsum : ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) = 0 := by
    refine Finset.sum_eq_zero fun ri hri => ?_
    rw [ite_eq_right (hi ri (List.mem_toFinset.mp hri))]
  rw [hsum, add_zero]

/-- 枢轴列上核向量读出该行的对应分量。 -/
lemma kerVec_apply_piv {D : List (PivRow n)} (hD : IsReduced D) {j : Fin n} {rk : PivRow n}
    (hrk : rk ∈ D) :
    kerVec D j rk.2 = (if rk.2 = j then 1 else 0) + rk.1 j := by
  rw [kerVec_apply]
  congr 1
  have hsingle : ∑ ri ∈ D.toFinset, (if ri.2 = rk.2 then ri.1 j else 0) = rk.1 j := by
    have h := Finset.sum_eq_single (s := D.toFinset)
      (f := fun ri => if ri.2 = rk.2 then ri.1 j else 0) rk
      (fun b hb hne => by
        rw [ite_eq_right]
        intro hcon
        exact hne (hD.pivot_inj b (List.mem_toFinset.mp hb) rk hrk hcon))
      (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
    rwa [ite_eq_left rfl] at h
  exact hsingle

/-- **可靠性方向**：核向量确实落在这组行的核里。

证明是两个求和的对消：把 `rk` 与核向量的点积展开成双重和、交换求和次序，
再用 (R1)/(R2) 的 Kronecker 形式把内层和塌成单项。 -/
lemma kerVec_mem_kerL {D : List (PivRow n)} (hD : IsReduced D) (j : Fin n) :
    kerVec D j ∈ kerL (rowList D) := by
  rw [mem_kerL]
  intro r hr
  obtain ⟨rk, hrk, rfl⟩ := List.mem_map.mp hr
  rw [dotProduct]
  have hexp : ∀ i : Fin n, kerVec D j i
      = (if i = j then 1 else 0) + ∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0) :=
    fun i => kerVec_apply D j i
  simp only [hexp]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i, rk.1 i * (if i = j then (1 : ZMod 2) else 0) = rk.1 j :=
    sum_mul_ite_self rk.1 j
  have h2 : ∑ i, rk.1 i * (∑ ri ∈ D.toFinset, (if ri.2 = i then ri.1 j else 0)) = rk.1 j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ ri ∈ D.toFinset,
        ∑ i, rk.1 i * (if ri.2 = i then ri.1 j else 0) = rk.1 ri.2 * ri.1 j :=
      fun ri _ => sum_mul_ite_eq rk.1 ri.2 (ri.1 j)
    rw [Finset.sum_congr rfl hinner]
    have hsingle : ∑ b ∈ D.toFinset, rk.1 b.2 * b.1 j = rk.1 rk.2 * rk.1 j :=
      Finset.sum_eq_single (s := D.toFinset) (f := fun b => rk.1 b.2 * b.1 j) rk
        (fun b hb hne => by
          rw [hD.2 rk hrk b (List.mem_toFinset.mp hb) (fun h => hne h.symm), zero_mul])
        (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
    rw [hsingle, hD.1 rk hrk, one_mul]
  rw [h1, h2]
  exact CharTwo.add_self_eq_zero (rk.1 j)

/-! ## Singleton 型计数：核向量有多轻 -/

/-- **核向量非零**：自由列上它就是 `e_j`，故不可能是零向量。 -/
theorem kerVec_ne_zero {D : List (PivRow n)} {j : Fin n} (hj : IsFreeCol D j) :
    kerVec D j ≠ 0 := by
  intro hzero
  have h1 : kerVec D j j = 1 := by rw [kerVec_apply_free hj, ite_eq_left rfl]
  rw [hzero] at h1
  simp only [Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- **Singleton 型计数**：核向量的支撑落在 $\{j\}\cup$ 枢轴列里，故重量至多 $1+\#D$。

这条对**任意**列 `j` 成立（自由与否都一样）：`kerVec D j` 只在 `j` 与枢轴列上可能
非零，其余列都是自由列、按 `kerVec_apply_free` 取零；而枢轴列恰有 `#D` 个，
`#D` 就是秩。配上 `kerVec_ne_zero`，"核非平凡 $\Rightarrow$ 存在重量 $\le\rho+1$
的非零核向量"就成了一条定理，而不是一句解析断言。 -/
theorem hammingNorm_kerVec_le (D : List (PivRow n)) (j : Fin n) :
    hammingNorm (kerVec D j) ≤ D.length + 1 := by
  rw [← weight_eq_hammingNorm]
  calc (support (kerVec D j)).card
      ≤ (insert j (pivCols D)).card := Finset.card_le_card (fun i hi => ?_)
    _ ≤ (pivCols D).card + 1 := Finset.card_insert_le j (pivCols D)
    _ ≤ D.length + 1 := by
        have h := List.toFinset_card_le (D.map (·.2))
        simp only [pivCols, List.length_map] at h ⊢
        omega
  rw [support, Finset.mem_filter] at hi
  obtain ⟨-, hne⟩ := hi
  rw [Finset.mem_insert, mem_pivCols]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hij, hnot⟩ := hcon
  have hfree : IsFreeCol D i := fun ri hri hcon2 => hnot ⟨ri, hri, hcon2⟩
  rw [kerVec_apply_free hfree, ite_eq_right hij] at hne
  exact hne rfl

/-! ## 核生成元 -/

/-- 核生成元：每个自由列给出一个核向量。（自由列恰有 `n − #D` 个，
故这组生成元的个数就是核的维数——见 `kerL_rowReduce` 的完备性。） -/
def kerBasis (D : List (PivRow n)) : List (Vec n) :=
  ((List.finRange n).filter (fun j => decide (j ∉ pivCols D))).map (kerVec D)

lemma mem_kerBasis {D : List (PivRow n)} {x : Vec n} :
    x ∈ kerBasis D ↔ ∃ j, j ∉ pivCols D ∧ kerVec D j = x := by
  simp only [kerBasis, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, of_decide_eq_true hj, rfl⟩
  · rintro ⟨j, hjp, rfl⟩
    exact ⟨j, decide_eq_true hjp, rfl⟩

/-! ## 完备性 -/

/-- 支在枢轴列上的向量可按枢轴列重构。 -/
lemma eq_sum_of_piv_support {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) :
    ∀ m, z m = ∑ rl ∈ D.toFinset, (if rl.2 = m then z rl.2 else 0) := by
  intro m
  by_cases hm : ∃ rl ∈ D, rl.2 = m
  · obtain ⟨rl, hrl, rfl⟩ := hm
    have hsingle : ∑ b ∈ D.toFinset, (if b.2 = rl.2 then z b.2 else 0) = z rl.2 := by
      have h := Finset.sum_eq_single (s := D.toFinset)
        (f := fun b => if b.2 = rl.2 then z b.2 else 0) rl
        (fun b hb hne => by
          rw [ite_eq_right]
          intro hcon
          exact hne (hD.pivot_inj b (List.mem_toFinset.mp hb) rl hrl hcon))
        (fun hnot => absurd (List.mem_toFinset.mpr hrl) hnot)
      rwa [ite_eq_left rfl] at h
    rw [hsingle]
  · have hz0 : z m = 0 := hz m (fun ri hri hcon => hm ⟨ri, hri, hcon⟩)
    have hsum0 : ∑ b ∈ D.toFinset, (if b.2 = m then z b.2 else 0) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [ite_eq_right]
      intro hcon
      exact hm ⟨b, List.mem_toFinset.mp hb, hcon⟩
    rw [hz0, hsum0]

/-- **枢轴列上的分量决定一切**：支在枢轴列上且在核里的向量必为零。 -/
lemma eq_zero_of_piv_support {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) (hzker : ∀ ri ∈ D, ri.1 ⬝ᵥ z = 0) :
    z = 0 := by
  have hzsum := eq_sum_of_piv_support hD hz
  funext m
  by_cases hm : ∃ rk ∈ D, rk.2 = m
  · obtain ⟨rk, hrk, rfl⟩ := hm
    have hdot : rk.1 ⬝ᵥ z = z rk.2 := by
      rw [dotProduct]
      have step1 : ∑ i, rk.1 i * z i
          = ∑ i, rk.1 i * (∑ rl ∈ D.toFinset, (if rl.2 = i then z rl.2 else 0)) :=
        Finset.sum_congr rfl fun i _ => by rw [hzsum i]
      rw [step1]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner : ∀ rl ∈ D.toFinset,
          ∑ x, rk.1 x * (if rl.2 = x then z rl.2 else 0) = rk.1 rl.2 * z rl.2 :=
        fun rl _ => sum_mul_ite_eq rk.1 rl.2 (z rl.2)
      rw [Finset.sum_congr rfl hinner]
      have hsingle : ∑ b ∈ D.toFinset, rk.1 b.2 * z b.2 = rk.1 rk.2 * z rk.2 :=
        Finset.sum_eq_single (s := D.toFinset) (f := fun b => rk.1 b.2 * z b.2) rk
          (fun b hb hne => by
            rw [hD.2 rk hrk b (List.mem_toFinset.mp hb) (fun h => hne h.symm), zero_mul])
          (fun hnot => absurd (List.mem_toFinset.mpr hrk) hnot)
      rw [hsingle, hD.1 rk hrk, one_mul]
    rw [← hdot]
    exact hzker rk hrk
  · exact hz m (fun ri hri hcon => hm ⟨ri, hri, hcon⟩)

/-- **完备性方向**：核里每个向量都是核生成元的线性组合。 -/
lemma kerL_le_spanL_kerBasis {D : List (PivRow n)} (hD : IsReduced D) :
    kerL (rowList D) ≤ spanL (kerBasis D) := by
  intro x hx
  rw [mem_kerL] at hx
  set y := ∑ j ∈ Finset.univ.filter (fun j => j ∉ pivCols D), x j • kerVec D j with hy
  have hy_mem : y ∈ spanL (kerBasis D) := by
    rw [hy]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (subset_spanL ?_)
    rw [mem_kerBasis]
    exact ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩
  have hy_ker : y ∈ kerL (rowList D) := by
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (kerVec_mem_kerL hD j)
  have hxy_ker : ∀ rk ∈ D, rk.1 ⬝ᵥ (x + y) = 0 := by
    intro rk hrk
    have h1 : rk.1 ⬝ᵥ x = 0 := hx rk.1 (List.mem_map_of_mem hrk)
    have h2 : rk.1 ⬝ᵥ y = 0 := by
      rw [mem_kerL] at hy_ker; exact hy_ker rk.1 (List.mem_map_of_mem hrk)
    rw [dotProduct_add, h1, h2, add_zero]
  have hxy_free : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → (x + y) i = 0 := by
    intro i hi
    have hiF : i ∈ Finset.univ.filter (fun j => j ∉ pivCols D) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, by
        rw [mem_pivCols]
        rintro ⟨ri, hri, hcon⟩
        exact hi ri hri hcon⟩
    have hyi : y i = x i := by
      rw [hy, Finset.sum_apply]
      have hsingle : ∑ j ∈ Finset.univ.filter (fun j => j ∉ pivCols D),
            (x j • kerVec D j) i = (x i • kerVec D i) i :=
        Finset.sum_eq_single (s := Finset.univ.filter (fun j => j ∉ pivCols D))
          (f := fun j => (x j • kerVec D j) i) i
          (fun b _ hne => by
            rw [Pi.smul_apply, kerVec_apply_free hi, ite_eq_right (fun h => hne h.symm),
              smul_zero])
          (fun hnot => absurd hiF hnot)
      rw [hsingle, Pi.smul_apply, kerVec_apply_free hi, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    rw [Pi.add_apply, hyi]
    exact CharTwo.add_self_eq_zero (x i)
  have hzero : x + y = 0 := eq_zero_of_piv_support hD hxy_free hxy_ker
  have hxy : x = y := by
    have h := add_add_same_left x y
    rw [hzero, add_zero] at h
    exact h
  rw [hxy]
  exact hy_mem

/-! ## 与原始码的合拢 -/

/-- **主定理**：核 = 核生成元张成的空间。行列表先经可信行消元，
核生成元直接从消元输出的枢轴结构读出——整条链在内核内闭合。 -/
theorem kerL_rowReduce (L : List (Vec n)) :
    kerL L = spanL (kerBasis (rowReduce L)) := by
  rw [← kerL_eq_of_spanL_eq (spanL_rowReduce L)]
  refine le_antisymm (kerL_le_spanL_kerBasis (isReduced_rowReduce L)) ?_
  refine Submodule.span_le.2 fun x hx => ?_
  have hx' : x ∈ kerBasis (rowReduce L) := hx
  rw [mem_kerBasis] at hx'
  obtain ⟨j, -, rfl⟩ := hx'
  exact kerVec_mem_kerL (isReduced_rowReduce L) j

/-- **前沿界论证那一步的行列表形态**：只要 `rowReduce L` 还剩自由列（即核非平凡），
`L` 的核里就有一个重量 $\le 1+\#(rowReduce L)$ 的非零元。

$\#(rowReduce L)$ 就是 $L$ 的秩，故这是"秩 $\rho$ 的矩阵有重量 $\le\rho+1$ 的非零
核向量"的完整陈述：存在性走 `kerL_rowReduce` 的完备性方向，非零与重量界走上面两条。 -/
theorem exists_light_mem_kerL (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    ∃ v ∈ kerL L, v ≠ 0 ∧ hammingNorm v ≤ (rowReduce L).length + 1 := by
  refine ⟨kerVec (rowReduce L) j, ?_, kerVec_ne_zero hj, hammingNorm_kerVec_le _ _⟩
  rw [kerL_rowReduce]
  refine subset_spanL (mem_kerBasis.mpr ⟨j, fun hmem => ?_, rfl⟩)
  obtain ⟨ri, hri, hcon⟩ := mem_pivCols.mp hmem
  exact hj ri hri hcon

/-- **带下标的形态**：自由列 `j` 给出的核向量，同时在核里、重量 $\le$ 秩 $+1$、
且在 `j` 位取 $1$。

"在 `j` 位取 1"这一条是前沿界论证里必需的：HGP 的见证构造要求种子核向量在某个下标上
非零（`xwLeft` 的 `s a₀ = 1`）。 -/
theorem exists_light_mem_kerL_apply (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    kerVec (rowReduce L) j ∈ kerL L
      ∧ hammingNorm (kerVec (rowReduce L) j) ≤ (rowReduce L).length + 1
      ∧ kerVec (rowReduce L) j j = 1 := by
  refine ⟨?_, hammingNorm_kerVec_le _ _, ?_⟩
  · rw [kerL_rowReduce]
    refine subset_spanL (mem_kerBasis.mpr ⟨j, fun hmem => ?_, rfl⟩)
    obtain ⟨ri, hri, hcon⟩ := mem_pivCols.mp hmem
    exact hj ri hri hcon
  · rw [kerVec_apply_free hj, ite_eq_left rfl]

/-! ## 与 LeanQEC 矩阵接口的合拢 -/

/-- 校验**矩阵**的核（LeanQEC 的 `LinearMap.ker M.toLin'`）与行列表的核一致。
这条桥让 LeanQEC 已有的行空间定理直接作用到本模块的 `kerL` 上。 -/
theorem LinearMap.ker_eq_kerL_ofFn {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = kerL (List.ofFn fun i => M i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_kerL]
    rw [mem_ker_iff_dotProd_rows_eq_zero] at hx
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hx i
  · intro x hx
    rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    exact (mem_kerL.mp hx) (M i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- **对外主定理（LeanQEC 接口版）**：校验矩阵 `M` 的核空间等于核生成元张成的空间。
核生成元由可信行消元从 `M` 的行列表直接读出，全过程在内核内闭合。 -/
theorem LinearMap.ker_eq_spanL_kerBasis_ofFn {m : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = spanL (kerBasis (rowReduce (List.ofFn fun i => M i))) := by
  rw [LinearMap.ker_eq_kerL_ofFn, kerL_rowReduce]

end QECCertificates
