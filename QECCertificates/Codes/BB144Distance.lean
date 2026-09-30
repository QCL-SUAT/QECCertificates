/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB144Witness
import QECCertificates.Codes.DistanceLabel
import LeanQEC.Stabilizer.BB
import LeanQEC.Stabilizer.CSS
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Distance

/-!
# BB $[[144,12,12]]$：下界 $d\ge12$ 的内核内证明（走 QECLean 的 Gross 形式化）

这是 `Codes/BB144Witness.lean` 的**另一半**。那一片给的是**上界** $d_X,d_Z\le12$
（显式重量-12 逻辑算符、三事实内核 `by decide`）；本片给**下界** $d_X,d_Z\ge12$，
两侧合拢得 $d_X=d_Z=12$——全程在内核内，零 `native_decide`、零 `bv_decide`，
也不碰 Lean-QEC 那条 3.26 GB olean 的路线。

## 证据形态

下界不是"求解器说 UNSAT"，而是**逐码解析证明**的搬运：QECLean 在其同调形式化里
闭合了该码的链级距离（`gross_chain_distance_eq_12`，无条件给出），本模块把它的
链级量——`cycles`、`boundaries`、`chainWeight`——与本库的 GF(2) 语言对起来：
`LE_X`/`LE_Z` 的逐行恒等式、核的对应、行空间的对应、重量的一致。于是
"链级距离 $=12$" 直接给出 `min_weight_ker_not_mem_rowspace` 上的两条界。

**对照**：Lean-QEC 的同一下界走 SAT/位爆破（`bv_decide`），定理带 `_native` 公理、
所在模块 olean 3.26 GB；本模块的两条定理只依赖三条标准公理，审计见根文件。

## 索引约定与**尚未合拢的一里**

`LE_X`/`LE_Z` 与 Lean-QEC 的 `BB144_X_mat`/`BB144_Z_mat` 是同一个码；`e144` 是两者
之间的索引双射（列序块在前：`e144 c = (e72 (c % 72), c / 72)`）。

本片给出的是**对 `LE_X`/`LE_Z` 的下界**。`Codes/BB144Witness.lean` 用的是同一组矩阵
的另一种写法（72 条字面行），它的上界由该模块给出。两者由 `Codes/BB144Literal.lean`
的矩阵同一性（`bb144Hx_eq_LE_X`、`bb144Hz_eq_LE_Z`）接上，于是"本库字面矩阵的
$d=12$"在本库自己的矩阵上闭环。那条同一性**不是**能顺手带过的计算：直接对整条
72×144 等式做 `by decide`，在 8000000 心跳下仍超时（`LE_X` 的条目要展开 QECLean 的
群环多项式）；该模块改走逐行桥接，把判定拆成可归约的片段才过。
-/

namespace QECCertificates.BB144Distance

-- 本模块要在字面 72×144 矩阵上做内核判定，心跳与递归深都要放宽（同 BB144Witness）
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Quantum.Stabilizer.Homological.BB

def idxZ (i : Fin (12*6)) : ZMod 12 × ZMod 6 :=
  (((finProdFinEquiv.symm i).1.val : ZMod 12), ((finProdFinEquiv.symm i).2.val : ZMod 6))

theorem idxZ_fst_val (i : Fin (12*6)) : (idxZ i).1.val = (finProdFinEquiv.symm i).1.val := by
  simp only [idxZ, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (finProdFinEquiv.symm i).1.isLt

theorem idxZ_snd_val (i : Fin (12*6)) : (idxZ i).2.val = (finProdFinEquiv.symm i).2.val := by
  simp only [idxZ, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (finProdFinEquiv.symm i).2.isLt

theorem val_add_natCast (a : ZMod 12) (k : ℕ) :
    (a + (k : ZMod 12)).val = (a.val + k) % 12 := by
  rw [ZMod.val_add, ZMod.val_natCast]
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (ZMod.val_lt a)]

theorem idxZ_add_iff (k : ℕ) (i j : Fin (12*6)) :
    (idxZ j = idxZ i + ((k : ZMod 12), (0 : ZMod 6)))
      ↔ ((↑(finProdFinEquiv.symm i).1 + k) % 12 = ↑(finProdFinEquiv.symm j).1
         ∧ (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : (idxZ j).1 = (idxZ i).1 + (k : ZMod 12) := by rw [h]; rfl
      have h1v : (idxZ j).1.val = ((idxZ i).1 + (k : ZMod 12)).val := congrArg ZMod.val h1
      rw [idxZ_fst_val, val_add_natCast, idxZ_fst_val] at h1v
      exact h1v.symm
    · have h2 : (idxZ j).2 = (idxZ i).2 + (0 : ZMod 6) := by rw [h]; rfl
      have h2v : (idxZ j).2.val = ((idxZ i).2 + (0 : ZMod 6)).val := congrArg ZMod.val h2
      rw [idxZ_snd_val, add_zero, idxZ_snd_val] at h2v
      exact (Fin.ext h2v).symm
  · intro h
    obtain ⟨ha, hb⟩ := h
    apply Prod.ext
    · show (idxZ j).1 = (idxZ i).1 + (k : ZMod 12)
      apply ZMod.val_injective 12
      rw [idxZ_fst_val, val_add_natCast, idxZ_fst_val]
      exact ha.symm
    · show (idxZ j).2 = (idxZ i).2 + (0 : ZMod 6)
      apply ZMod.val_injective 6
      rw [idxZ_snd_val, add_zero, idxZ_snd_val]
      exact congrArg Fin.val hb.symm

set_option linter.unusedSimpArgs false in
theorem x_entry (k : ℕ) (i j : Fin (12*6)) :
    x 12 6 k i j = (if idxZ j = idxZ i + ((k : ZMod 12), (0 : ZMod 6)) then 1 else 0) := by
  simp only [x, Matrix.kronecker_fin, Matrix.reindex_apply, Matrix.submatrix_apply,
             Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, cyclic_shift]
  by_cases h : idxZ j = idxZ i + ((k : ZMod 12), (0 : ZMod 6))
  · obtain ⟨ha, hb⟩ := (idxZ_add_iff k i j).mp h
    rw [ite_eq_left ha, ite_eq_left hb, one_mul, ite_eq_left h]
  · rw [ite_eq_right h]
    by_cases ha : (↑(finProdFinEquiv.symm i).1 + k) % 12 = ↑(finProdFinEquiv.symm j).1
    · by_cases hb : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2
      · exact absurd ((idxZ_add_iff k i j).mpr ⟨ha, hb⟩) h
      · rw [ite_eq_left ha, ite_eq_right hb, mul_zero]
    · rw [ite_eq_right ha, zero_mul]

theorem val_add_natCast6 (a : ZMod 6) (k : ℕ) :
    (a + (k : ZMod 6)).val = (a.val + k) % 6 := by
  rw [ZMod.val_add, ZMod.val_natCast]
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (ZMod.val_lt a)]

theorem idxZ_add_iff_y (k : ℕ) (i j : Fin (12*6)) :
    (idxZ j = idxZ i + ((0 : ZMod 12), (k : ZMod 6)))
      ↔ ((finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
         ∧ (↑(finProdFinEquiv.symm i).2 + k) % 6 = ↑(finProdFinEquiv.symm j).2) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : (idxZ j).1 = (idxZ i).1 + (0 : ZMod 12) := by rw [h]; rfl
      have h1v : (idxZ j).1.val = ((idxZ i).1 + (0 : ZMod 12)).val := congrArg ZMod.val h1
      rw [idxZ_fst_val, add_zero, idxZ_fst_val] at h1v
      exact (Fin.ext h1v).symm
    · have h2 : (idxZ j).2 = (idxZ i).2 + (k : ZMod 6) := by rw [h]; rfl
      have h2v : (idxZ j).2.val = ((idxZ i).2 + (k : ZMod 6)).val := congrArg ZMod.val h2
      rw [idxZ_snd_val, val_add_natCast6, idxZ_snd_val] at h2v
      exact h2v.symm
  · intro h
    obtain ⟨ha, hb⟩ := h
    apply Prod.ext
    · show (idxZ j).1 = (idxZ i).1 + (0 : ZMod 12)
      apply ZMod.val_injective 12
      rw [idxZ_fst_val, add_zero, idxZ_fst_val]
      exact congrArg Fin.val ha.symm
    · show (idxZ j).2 = (idxZ i).2 + (k : ZMod 6)
      apply ZMod.val_injective 6
      rw [idxZ_snd_val, val_add_natCast6, idxZ_snd_val]
      exact hb.symm

set_option linter.unusedSimpArgs false in
theorem y_entry (k : ℕ) (i j : Fin (12*6)) :
    y 12 6 k i j = (if idxZ j = idxZ i + ((0 : ZMod 12), (k : ZMod 6)) then 1 else 0) := by
  simp only [y, Matrix.kronecker_fin, Matrix.reindex_apply, Matrix.submatrix_apply,
             Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, cyclic_shift]
  by_cases h : idxZ j = idxZ i + ((0 : ZMod 12), (k : ZMod 6))
  · obtain ⟨ha, hb⟩ := (idxZ_add_iff_y k i j).mp h
    rw [ite_eq_left ha, ite_eq_left hb, mul_one, ite_eq_left h]
  · rw [ite_eq_right h]
    by_cases hb : (↑(finProdFinEquiv.symm i).2 + k) % 6 = ↑(finProdFinEquiv.symm j).2
    · by_cases ha : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
      · exact absurd ((idxZ_add_iff_y k i j).mpr ⟨ha, hb⟩) h
      · rw [ite_eq_right ha, zero_mul]
    · rw [ite_eq_right hb, mul_zero]

/-! ## The monomial support of `grossA` / `grossB`, in Finset form -/

theorem grossA_support_eq :
    (Finset.univ.filter (fun g : GrossGroup => grossA g = 1))
      = ({(3, 0), (0, 1), (0, 2)} : Finset GrossGroup) := by decide

theorem grossB_support_eq :
    (Finset.univ.filter (fun g : GrossGroup => grossB g = 1))
      = ({(0, 3), (1, 0), (2, 0)} : Finset GrossGroup) := by decide

theorem grossA_mem_iff (g : GrossGroup) :
    g ∈ ({(3, 0), (0, 1), (0, 2)} : Finset GrossGroup) ↔ grossA g = 1 := by
  have h1 : g ∈ ({(3, 0), (0, 1), (0, 2)} : Finset GrossGroup)
      ↔ g ∈ Finset.univ.filter (fun g : GrossGroup => grossA g = 1) := by
    rw [grossA_support_eq]
  rw [h1, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ g, h⟩⟩

theorem grossA_eq_indicator (g : GrossGroup) :
    grossA g = (if g ∈ ({(3, 0), (0, 1), (0, 2)} : Finset GrossGroup) then 1 else 0) := by
  by_cases h : g ∈ ({(3, 0), (0, 1), (0, 2)} : Finset GrossGroup)
  · rw [ite_eq_left h]; exact grossA_mem_iff g |>.mp h
  · rw [ite_eq_right h]
    have hne : grossA g ≠ 1 := fun h1 => h ((grossA_mem_iff g).mpr h1)
    have hv : (grossA g).val = 0 ∨ (grossA g).val = 1 := by
      have := ZMod.val_lt (grossA g); omega
    rcases hv with hv | hv
    · exact ZMod.val_injective 2 (by rw [hv]; rfl)
    · exact absurd (ZMod.val_injective 2 (by rw [hv]; rfl)) hne

/-! ## T3: the parity-check matrices *are* the group-algebra convolutions -/

theorem mem_support_iff (i j : Fin (12*6)) :
    (idxZ j - idxZ i) ∈ ({(3, 0), (0, 1), (0, 2)} : Finset GrossGroup)
      ↔ idxZ j = idxZ i + (3, 0) ∨ idxZ j = idxZ i + (0, 1) ∨ idxZ j = idxZ i + (0, 2) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · left; rw [← h]; abel
    · right; left; rw [← h]; abel
    · right; right; rw [← h]; abel
  · rintro (h | h | h)
    · left; rw [h]; abel
    · right; left; rw [h]; abel
    · right; right; rw [h]; abel

theorem BB144_A_entry (i j : Fin (12*6)) :
    BB3_matrix 12 6 (true, 3) (false, 1) (false, 2) i j = grossA (idxZ j - idxZ i) := by
  rw [show BB3_matrix 12 6 (true, 3) (false, 1) (false, 2)
        = x 12 6 3 + y 12 6 1 + y 12 6 2 from rfl]
  simp only [Matrix.add_apply, x_entry, y_entry]
  rw [grossA_eq_indicator, if_congr (mem_support_iff i j) rfl rfl]
  have key : ∀ (a b c : Prop) [Decidable a] [Decidable b] [Decidable c],
      ¬ (a ∧ b) → ¬ (a ∧ c) → ¬ (b ∧ c) →
      ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) : ZMod 2)
        = (if a ∨ b ∨ c then 1 else 0) := by
    intro a b c _ _ _ hab hac hbc
    by_cases ha : a
    · have hb' : ¬ b := fun h => hab ⟨ha, h⟩
      have hc' : ¬ c := fun h => hac ⟨ha, h⟩
      simp [ha, hb', hc']
    · by_cases hb : b
      · have hc' : ¬ c := fun h => hbc ⟨hb, h⟩
        simp [ha, hb, hc']
      · by_cases hcc : c <;> simp [ha, hb, hcc]
  have h12 : ¬ ((idxZ j = idxZ i + (((3 : ℕ) : ZMod 12), ((0 : ℕ) : ZMod 6)))
              ∧ (idxZ j = idxZ i + (((0 : ℕ) : ZMod 12), ((1 : ℕ) : ZMod 6)))) := by
    rintro ⟨e1, e2⟩
    rw [e1] at e2
    exact absurd (add_left_cancel e2) (by decide)
  have h13 : ¬ ((idxZ j = idxZ i + (((3 : ℕ) : ZMod 12), ((0 : ℕ) : ZMod 6)))
              ∧ (idxZ j = idxZ i + (((0 : ℕ) : ZMod 12), ((2 : ℕ) : ZMod 6)))) := by
    rintro ⟨e1, e3⟩
    rw [e1] at e3
    exact absurd (add_left_cancel e3) (by decide)
  have h23 : ¬ ((idxZ j = idxZ i + (((0 : ℕ) : ZMod 12), ((1 : ℕ) : ZMod 6)))
              ∧ (idxZ j = idxZ i + (((0 : ℕ) : ZMod 12), ((2 : ℕ) : ZMod 6)))) := by
    rintro ⟨e2, e3⟩
    rw [e2] at e3
    exact absurd (add_left_cancel e3) (by decide)
  exact key _ _ _ h12 h13 h23

theorem grossB_mem_iff (g : GrossGroup) :
    g ∈ ({(0, 3), (1, 0), (2, 0)} : Finset GrossGroup) ↔ grossB g = 1 := by
  have h1 : g ∈ ({(0, 3), (1, 0), (2, 0)} : Finset GrossGroup)
      ↔ g ∈ Finset.univ.filter (fun g : GrossGroup => grossB g = 1) := by
    rw [grossB_support_eq]
  rw [h1, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ g, h⟩⟩

theorem grossB_eq_indicator (g : GrossGroup) :
    grossB g = (if g ∈ ({(0, 3), (1, 0), (2, 0)} : Finset GrossGroup) then 1 else 0) := by
  by_cases h : g ∈ ({(0, 3), (1, 0), (2, 0)} : Finset GrossGroup)
  · rw [ite_eq_left h]; exact grossB_mem_iff g |>.mp h
  · rw [ite_eq_right h]
    have hne : grossB g ≠ 1 := fun h1 => h ((grossB_mem_iff g).mpr h1)
    have hv : (grossB g).val = 0 ∨ (grossB g).val = 1 := by
      have := ZMod.val_lt (grossB g); omega
    rcases hv with hv | hv
    · exact ZMod.val_injective 2 (by rw [hv]; rfl)
    · exact absurd (ZMod.val_injective 2 (by rw [hv]; rfl)) hne

theorem mem_support_iff_B (i j : Fin (12*6)) :
    (idxZ j - idxZ i) ∈ ({(0, 3), (1, 0), (2, 0)} : Finset GrossGroup)
      ↔ idxZ j = idxZ i + (0, 3) ∨ idxZ j = idxZ i + (1, 0) ∨ idxZ j = idxZ i + (2, 0) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · left; rw [← h]; abel
    · right; left; rw [← h]; abel
    · right; right; rw [← h]; abel
  · rintro (h | h | h)
    · left; rw [h]; abel
    · right; left; rw [h]; abel
    · right; right; rw [h]; abel

theorem BB144_B_entry (i j : Fin (12*6)) :
    BB3_matrix 12 6 (false, 3) (true, 1) (true, 2) i j = grossB (idxZ j - idxZ i) := by
  rw [show BB3_matrix 12 6 (false, 3) (true, 1) (true, 2)
        = y 12 6 3 + x 12 6 1 + x 12 6 2 from rfl]
  simp only [Matrix.add_apply, y_entry, x_entry]
  rw [grossB_eq_indicator, if_congr (mem_support_iff_B i j) rfl rfl]
  have key : ∀ (a b c : Prop) [Decidable a] [Decidable b] [Decidable c],
      ¬ (a ∧ b) → ¬ (a ∧ c) → ¬ (b ∧ c) →
      ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) : ZMod 2)
        = (if a ∨ b ∨ c then 1 else 0) := by
    intro a b c _ _ _ hab hac hbc
    by_cases ha : a
    · have hb' : ¬ b := fun h => hab ⟨ha, h⟩
      have hc' : ¬ c := fun h => hac ⟨ha, h⟩
      simp [ha, hb', hc']
    · by_cases hb : b
      · have hc' : ¬ c := fun h => hbc ⟨hb, h⟩
        simp [ha, hb, hc']
      · by_cases hcc : c <;> simp [ha, hb, hcc]
  have h12 : ¬ ((idxZ j = idxZ i + (((0 : ℕ) : ZMod 12), ((3 : ℕ) : ZMod 6)))
              ∧ (idxZ j = idxZ i + (((1 : ℕ) : ZMod 12), ((0 : ℕ) : ZMod 6)))) := by
    rintro ⟨e1, e2⟩
    rw [e1] at e2
    exact absurd (add_left_cancel e2) (by decide)
  have h13 : ¬ ((idxZ j = idxZ i + (((0 : ℕ) : ZMod 12), ((3 : ℕ) : ZMod 6)))
              ∧ (idxZ j = idxZ i + (((2 : ℕ) : ZMod 12), ((0 : ℕ) : ZMod 6)))) := by
    rintro ⟨e1, e3⟩
    rw [e1] at e3
    exact absurd (add_left_cancel e3) (by decide)
  have h23 : ¬ ((idxZ j = idxZ i + (((1 : ℕ) : ZMod 12), ((0 : ℕ) : ZMod 6)))
              ∧ (idxZ j = idxZ i + (((2 : ℕ) : ZMod 12), ((0 : ℕ) : ZMod 6)))) := by
    rintro ⟨e2, e3⟩
    rw [e2] at e3
    exact absurd (add_left_cancel e3) (by decide)
  exact key _ _ _ h12 h13 h23



/-! # T4 — the two distance definitions agree

QECLean's distance theorem is about Pauli *group elements*; Lean-QEC's is about
binary vectors and `min_weight_ker_not_mem_rowspace`.  The transport is:

* identify `Fin 144 ≃ GrossGroup × Fin 2` and `Fin (12*6) ≃ GrossGroup` (T4.1);
* show Lean-QEC's parity-check matrices **are** QECLean's boundary maps under
  that identification (T4.2), hence `ker (LE_Z) = cycles` and
  `LE_X.rowSpace = boundaries` (T4.3);
* conclude that every vector counted by `min_weight_ker_not_mem_rowspace` is the
  binary shadow of a nontrivial logical Pauli operator of the same weight
  (T4.4), so QECLean's `HasCodeDistance grossStabilizerCode 12` bounds it (T4.5).

Nothing here uses `bv_decide`, `native_decide` or the 3.26 GB `BB144` olean. -/

set_option maxRecDepth 8192

open Quantum.Stabilizer.Homological

/-! ## T4.0  Lean-QEC's parity-check matrices, restated

`LeanQEC/Stabilizer/Examples/BB/BB144.lean` writes

    def BB144_A := let l := 12; let m := 6; BB3_matrix l m (true,3) (false,1) (false,2)
    def BB144_X_mat := BB144_A.hstack_fin BB144_B
    def BB144_Z_mat := BB144_B.transpose.hstack_fin BB144_A.transpose

which is definitionally `LE_A`/`LE_B`/`LE_X`/`LE_Z` below.  We restate them
instead of importing `BB144.lean`, whose 3.26 GB olean and four real-time-SAT
`bv_decide` sites are exactly what this transport replaces. -/

abbrev LE_A : Matrix (Fin (12*6)) (Fin (12*6)) (ZMod 2) :=
  BB3_matrix 12 6 (true, 3) (false, 1) (false, 2)

abbrev LE_B : Matrix (Fin (12*6)) (Fin (12*6)) (ZMod 2) :=
  BB3_matrix 12 6 (false, 3) (true, 1) (true, 2)

abbrev LE_X : Matrix (Fin (12*6)) (Fin 144) (ZMod 2) := LE_A.hstack_fin LE_B

abbrev LE_Z : Matrix (Fin (12*6)) (Fin 144) (ZMod 2) :=
  LE_B.transpose.hstack_fin LE_A.transpose

theorem LE_A_apply (i j : Fin (12*6)) : LE_A i j = grossA (idxZ j - idxZ i) :=
  BB144_A_entry i j

theorem LE_B_apply (i j : Fin (12*6)) : LE_B i j = grossB (idxZ j - idxZ i) :=
  BB144_B_entry i j

/-! ## T4.1  Index bridges

`ZMod 12` is `Fin 12` by definition, and `ZMod.finEquiv 12` is `RingEquiv.refl`,
so `e72` below really is `idxZ`; the `_val` helpers keep the kernel honest. -/

theorem finEquiv12_val (k : Fin 12) : (ZMod.finEquiv 12 k).val = k.val := by
  revert k; decide

theorem finEquiv6_val (k : Fin 6) : (ZMod.finEquiv 6 k).val = k.val := by
  revert k; decide

/-- `Fin (12*6) ≃ Z₁₂ × Z₆` — the same bijection `idxZ` is. -/
noncomputable def e72 : Fin (12*6) ≃ GrossGroup :=
  (finProdFinEquiv.symm).trans
    (Equiv.prodCongr (ZMod.finEquiv 12).toEquiv (ZMod.finEquiv 6).toEquiv)

theorem e72_apply (i : Fin (12*6)) : e72 i = idxZ i := by
  revert i; decide

/-- `Fin 144 ≃ Z₁₂ × Z₆ × Fin 2`, block first: qubit `c` sits in block
`c / 72` at group element `e72 (c % 72)` (`0` = the `A`-block, `1` = `B`). -/
noncomputable def e144 : Fin 144 ≃ GrossGroup × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 72)).symm.trans
    ((Equiv.prodComm (Fin 2) (Fin 72)).trans
      (Equiv.prodCongr e72 (Equiv.refl (Fin 2))))

theorem e144_symm_apply (g : GrossGroup) (b : Fin 2) :
    e144.symm (g, b) = finProdFinEquiv (b, e72.symm g) := rfl

theorem e144_symm_zero (g : GrossGroup) :
    e144.symm (g, 0) = Fin.castAdd 72 (e72.symm g) :=
  Fin.ext (by simp [e144_symm_apply, finProdFinEquiv])

theorem e144_symm_one (g : GrossGroup) :
    e144.symm (g, 1) = Fin.natAdd 72 (e72.symm g) :=
  Fin.ext (by simp [e144_symm_apply, finProdFinEquiv])

/-! ## T4.2  The parity-check matrices are the boundary maps

`LE_Z` is QECLean's `∂₁` and `LE_X` its `∂₂ᵀ`, once `Fin 144` is read as
`GrossGroup × Fin 2` through `e144` (block first) and `Fin (12*6)` as
`GrossGroup` through `e72`.  Both assertions are entrywise evaluations of
`grossA`/`grossB`, so they follow from T2/T3 (`LE_A_apply`/`LE_B_apply`).

`b1`/`b2` below are `rfl`-equal to `grossComplex.boundary1/2`; they only exist
to pin the index types to `GrossGroup × Fin 2` / `GrossGroup`, which makes the
sum lemmas fire. -/

noncomputable def b1 : (GrossGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (GrossGroup → ZMod 2) :=
  grossComplex.boundary1

noncomputable def b2 : (GrossGroup → ZMod 2) →ₗ[ZMod 2] (GrossGroup × Fin 2 → ZMod 2) :=
  grossComplex.boundary2

theorem b1_apply (c : GrossGroup × Fin 2 → ZMod 2) :
    b1 c = bbBoundary1Fn grossA grossB c := rfl

theorem b2_apply (f : GrossGroup → ZMod 2) :
    b2 f = bbBoundary2Fn grossA grossB f := rfl

/-- Qubit reindexing: `Fin 144 → ZMod 2` to `GrossGroup × Fin 2 → ZMod 2`. -/
noncomputable def psi (v : Fin 144 → ZMod 2) : GrossGroup × Fin 2 → ZMod 2 :=
  fun p => v (e144.symm p)

/-- Row reindexing: `Fin (12*6) → ZMod 2` to `GrossGroup → ZMod 2`. -/
noncomputable def psi0 (v : Fin (12*6) → ZMod 2) : GrossGroup → ZMod 2 :=
  fun g => v (e72.symm g)

/-- The inverse row reindexing: `GrossGroup → ZMod 2` to `Fin (12*6) → ZMod 2`. -/
noncomputable def psi0inv (w : GrossGroup → ZMod 2) : Fin (12*6) → ZMod 2 :=
  fun g => w (e72 g)

theorem psi_injective : Function.Injective psi := by
  intro a b h
  funext c
  have := congrFun h (e144 c)
  simpa [psi] using this

/-- A vector is the sum of its own values times the coordinate vectors. -/
theorem sum_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ZMod 2) :
    (∑ p, w p • (Pi.single p 1 : ι → ZMod 2)) = w := by
  funext q
  rw [Finset.sum_apply, Finset.sum_eq_single q]
  · simp
  · intro p _ hp
    simp only [Pi.smul_apply, Pi.single_apply, ite_eq_right (Ne.symm hp), smul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem boundary1_eq_sum (w : GrossGroup × Fin 2 → ZMod 2) (g : GrossGroup) :
    b1 w g = ∑ p, b1 (Pi.single p 1) g * w p := by
  conv_lhs => rw [← sum_smul_single w]
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)

theorem boundary2_eq_sum (f : GrossGroup → ZMod 2) (p : GrossGroup × Fin 2) :
    b2 f p = ∑ k, b2 (Pi.single k 1) p * f k := by
  conv_lhs => rw [← sum_smul_single f]
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-! ### The two evaluations of the boundary maps on coordinate vectors -/

theorem boundary1_single_zero (g g' : GrossGroup) :
    b1 (Pi.single (g', 0) 1) g = grossB (g - g') := by
  rw [b1_apply]
  simp only [bbBoundary1Fn, leftHalf, rightHalf, conv_apply]
  have hR : (∑ x, grossA x * (Pi.single (g', 0) 1 : GrossGroup × Fin 2 → ZMod 2) (g - x, 1))
      = 0 := by
    rw [Finset.sum_eq_zero]
    intro x _
    have hne : ¬ (((g - x, 1) : GrossGroup × Fin 2) = (g', 0)) := by
      intro hc
      have h2 : (1 : Fin 2) = 0 := congrArg Prod.snd hc
      exact absurd h2 (by decide)
    rw [Pi.single_apply, ite_eq_right hne, mul_zero]
  have hL : (∑ x, grossB x * (Pi.single (g', 0) 1 : GrossGroup × Fin 2 → ZMod 2) (g - x, 0))
      = grossB (g - g') := by
    rw [Finset.sum_eq_single (g - g')]
    · have hgg : g - (g - g') = g' := by abel
      have hpos : (((g - (g - g'), 0)) : GrossGroup × Fin 2) = (g', 0) := by rw [hgg]
      rw [Pi.single_apply, ite_eq_left hpos, mul_one]
    · intro x _ hx
      have hne : ¬ (((g - x, 0) : GrossGroup × Fin 2) = (g', 0)) := by
        intro hc
        have h1 : g - x = g' := congrArg Prod.fst hc
        exact hx (by rw [← h1]; abel)
      rw [Pi.single_apply, ite_eq_right hne, mul_zero]
    · intro hx; exact absurd (Finset.mem_univ (g - g')) hx
  rw [hL, hR, add_zero]

theorem boundary1_single_one (g g' : GrossGroup) :
    b1 (Pi.single (g', 1) 1) g = grossA (g - g') := by
  rw [b1_apply]
  simp only [bbBoundary1Fn, leftHalf, rightHalf, conv_apply]
  have hL : (∑ x, grossB x * (Pi.single (g', 1) 1 : GrossGroup × Fin 2 → ZMod 2) (g - x, 0))
      = 0 := by
    rw [Finset.sum_eq_zero]
    intro x _
    have hne : ¬ (((g - x, 0) : GrossGroup × Fin 2) = (g', 1)) := by
      intro hc
      have h2 : (0 : Fin 2) = 1 := congrArg Prod.snd hc
      exact absurd h2 (by decide)
    rw [Pi.single_apply, ite_eq_right hne, mul_zero]
  have hR : (∑ x, grossA x * (Pi.single (g', 1) 1 : GrossGroup × Fin 2 → ZMod 2) (g - x, 1))
      = grossA (g - g') := by
    rw [Finset.sum_eq_single (g - g')]
    · have hgg : g - (g - g') = g' := by abel
      have hpos : (((g - (g - g'), 1)) : GrossGroup × Fin 2) = (g', 1) := by rw [hgg]
      rw [Pi.single_apply, ite_eq_left hpos, mul_one]
    · intro x _ hx
      have hne : ¬ (((g - x, 1) : GrossGroup × Fin 2) = (g', 1)) := by
        intro hc
        have h1 : g - x = g' := congrArg Prod.fst hc
        exact hx (by rw [← h1]; abel)
      rw [Pi.single_apply, ite_eq_right hne, mul_zero]
    · intro hx; exact absurd (Finset.mem_univ (g - g')) hx
  rw [hL, hR, zero_add]

theorem boundary2_single_zero (k h : GrossGroup) :
    b2 (Pi.single k 1) (h, 0) = grossA (h - k) := by
  rw [b2_apply]
  simp only [bbBoundary2Fn, ite_true, conv_apply]
  rw [Finset.sum_eq_single (h - k)]
  · have hhh : h - (h - k) = k := by abel
    rw [Pi.single_apply, ite_eq_left hhh, mul_one]
  · intro x _ hx
    have hne : h - x ≠ k := fun hc => hx (by rw [← hc]; abel)
    rw [Pi.single_apply, ite_eq_right hne, mul_zero]
  · intro hx; exact absurd (Finset.mem_univ (h - k)) hx

theorem boundary2_single_one (k h : GrossGroup) :
    b2 (Pi.single k 1) (h, 1) = grossB (h - k) := by
  rw [b2_apply]
  simp only [bbBoundary2Fn, conv_apply]
  rw [ite_eq_right (by decide : ¬ ((1 : Fin 2) = 0))]
  rw [Finset.sum_eq_single (h - k)]
  · have hhh : h - (h - k) = k := by abel
    rw [Pi.single_apply, ite_eq_left hhh, mul_one]
  · intro x _ hx
    have hne : h - x ≠ k := fun hc => hx (by rw [← hc]; abel)
    rw [Pi.single_apply, ite_eq_right hne, mul_zero]
  · intro hx; exact absurd (Finset.mem_univ (h - k)) hx

/-! ### The two entrywise matrix evaluations -/

theorem LE_Z_entry_zero (g : Fin (12*6)) (h : GrossGroup) :
    LE_Z g (e144.symm (h, 0)) = grossB (e72 g - h) := by
  have h1 : idxZ (e72.symm h) = h := by
    rw [← e72_apply (e72.symm h), Equiv.apply_symm_apply]
  have h2 : idxZ g = e72 g := (e72_apply g).symm
  rw [e144_symm_zero]
  unfold LE_Z Matrix.hstack_fin
  rw [Fin.addCases_left, Matrix.transpose_apply, LE_B_apply, h1, h2]

theorem LE_Z_entry_one (g : Fin (12*6)) (h : GrossGroup) :
    LE_Z g (e144.symm (h, 1)) = grossA (e72 g - h) := by
  have h1 : idxZ (e72.symm h) = h := by
    rw [← e72_apply (e72.symm h), Equiv.apply_symm_apply]
  have h2 : idxZ g = e72 g := (e72_apply g).symm
  rw [e144_symm_one]
  unfold LE_Z Matrix.hstack_fin
  rw [Fin.addCases_right, Matrix.transpose_apply, LE_A_apply, h1, h2]

theorem LE_X_entry_zero (g : Fin (12*6)) (h : GrossGroup) :
    LE_X g (e144.symm (h, 0)) = grossA (h - e72 g) := by
  have h1 : idxZ (e72.symm h) = h := by
    rw [← e72_apply (e72.symm h), Equiv.apply_symm_apply]
  have h2 : idxZ g = e72 g := (e72_apply g).symm
  rw [e144_symm_zero]
  unfold LE_X Matrix.hstack_fin
  rw [Fin.addCases_left, LE_A_apply, h1, h2]

theorem LE_X_entry_one (g : Fin (12*6)) (h : GrossGroup) :
    LE_X g (e144.symm (h, 1)) = grossB (h - e72 g) := by
  have h1 : idxZ (e72.symm h) = h := by
    rw [← e72_apply (e72.symm h), Equiv.apply_symm_apply]
  have h2 : idxZ g = e72 g := (e72_apply g).symm
  rw [e144_symm_one]
  unfold LE_X Matrix.hstack_fin
  rw [Fin.addCases_right, LE_B_apply, h1, h2]

/-! ## T4.3  The two identifications

`LE_Z`'s kernel is QECLean's cycle space and `LE_X`'s row space is its boundary
space.  Both are read off the entrywise evaluations of T4.2. -/

theorem b1_eq : b1 = grossComplex.boundary1 := rfl
theorem b2_eq : b2 = grossComplex.boundary2 := rfl

/-- `psi` as a `ZMod 2`-linear equivalence. -/
noncomputable def psiLin : (Fin 144 → ZMod 2) ≃ₗ[ZMod 2] (GrossGroup × Fin 2 → ZMod 2) where
  toFun := psi
  invFun := fun w => fun c => w (e144 c)
  left_inv := by intro v; funext c; simp [psi]
  right_inv := by intro w; funext p; simp [psi]
  map_add' := by intro a b; funext p; simp [psi]
  map_smul' := by intro a b; funext p; simp [psi]

theorem psiLin_apply (v : Fin 144 → ZMod 2) : psiLin v = psi v := rfl

/-- The two entries of the `LE_Z = ∂₁` identity, packaged. -/
theorem LE_Z_entry (g : Fin (12*6)) (p : GrossGroup × Fin 2) :
    LE_Z g (e144.symm p) = b1 (Pi.single p 1) (e72 g) := by
  obtain ⟨h, b⟩ := p
  fin_cases b <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [LE_Z_entry_zero, boundary1_single_zero]
  · rw [LE_Z_entry_one, boundary1_single_one]

/-- The two entries of the `LE_X = ∂₂ᵀ` identity, packaged. -/
theorem LE_X_entry (g : Fin (12*6)) (p : GrossGroup × Fin 2) :
    LE_X g (e144.symm p) = b2 (Pi.single (e72 g) 1) p := by
  obtain ⟨h, b⟩ := p
  fin_cases b <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [LE_X_entry_zero, boundary2_single_zero]
  · rw [LE_X_entry_one, boundary2_single_one]

/-- `LE_Z.mulVec` *is* `∂₁` after reindexing. -/
theorem LE_Z_mulVec (v : Fin 144 → ZMod 2) :
    LE_Z.mulVec v = psi0inv (b1 (psi v)) := by
  funext g
  rw [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_equiv e144 (fun c => LE_Z g c * v c)
        (fun p => LE_Z g (e144.symm p) * v (e144.symm p))
        (fun c => by rw [Equiv.symm_apply_apply])]
  rw [psi0inv, boundary1_eq_sum (psi v) (e72 g)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [LE_Z_entry]
  exact congrArg (fun z => b1 (Pi.single p 1) (e72 g) * z) rfl

/-- Every row of `LE_X` is `∂₂` applied to the corresponding coordinate vector. -/
theorem LE_X_row (g : Fin (12*6)) :
    psiLin (LE_X g) = b2 (Pi.single (e72 g) 1) := by
  funext p
  change psi (LE_X g) p = b2 (Pi.single (e72 g) 1) p
  rw [psi]
  exact LE_X_entry g p

/-- `LE_Z`'s kernel is the cycle space. -/
theorem LE_Z_ker_iff (v : Fin 144 → ZMod 2) : LE_Z.mulVec v = 0 ↔ b1 (psi v) = 0 := by
  rw [LE_Z_mulVec v]
  constructor
  · intro h
    funext g
    have := congrFun h (e72.symm g)
    simpa [psi0inv] using this
  · intro h
    funext g
    have := congrFun h (e72 g)
    simpa [psi0inv] using this

theorem LE_Z_ker_cycles (v : Fin 144 → ZMod 2) :
    LE_Z.mulVec v = 0 ↔ psi v ∈ grossComplex.cycles := by
  rw [LE_Z_ker_iff]
  exact (HomologicalCode.mem_cycles_iff grossComplex (psi v)).symm

/-- The direction the distance bound needs: a boundary is a combination of rows
of `LE_X`. -/
theorem mem_rowSpace_of_mem_boundaries (v : Fin 144 → ZMod 2)
    (h : psi v ∈ grossComplex.boundaries) : v ∈ LE_X.rowSpace := by
  have h' : psi v ∈ b2.range := h
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp h'
  have hf' : b2 f = psiLin v := hf
  rw [Matrix.rowSpace]
  have hsum : b2 f = ∑ k, f k • b2 (Pi.single k 1) := by
    funext p
    rw [boundary2_eq_sum f p]
    exact (Finset.sum_congr rfl (fun k _ => mul_comm _ _)).symm
  have hv : v = ∑ k, f k • (LE_X (e72.symm k)) := by
    apply psiLin.injective
    rw [← hf', map_sum, hsum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, LE_X_row, Equiv.apply_symm_apply]
  rw [hv]
  refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span (Set.mem_range_self (e72.symm k))

/-! ## T4.4  The weight dictionary and the bound -/

set_option maxRecDepth 4096 in
theorem chainWeight_psi (v : Fin 144 → ZMod 2) :
    grossComplex.chainWeight (psi v) = hammingNorm v := by
  classical
  have hL : grossComplex.chainWeight (psi v)
      = (Finset.univ.filter (fun p : GrossGroup × Fin 2 => psi v p ≠ 0)).card := rfl
  have hR : hammingNorm v = (Finset.univ.filter (fun c : Fin 144 => v c ≠ 0)).card := rfl
  rw [hL, hR]
  refine Finset.card_bij (fun p _ => e144.symm p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rwa [psi] at hp
  · intro p₁ _ p₂ _ h
    exact e144.symm.injective h
  · intro c hc
    refine ⟨e144 c, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rwa [psi, Equiv.symm_apply_apply]

set_option maxRecDepth 4096 in
theorem hammingNorm_eq_zero_iff (v : Fin 144 → ZMod 2) : hammingNorm v = 0 ↔ v = 0 := by
  classical
  have hR : hammingNorm v = (Finset.univ.filter (fun c : Fin 144 => v c ≠ 0)).card := rfl
  rw [hR, Finset.card_eq_zero]
  constructor
  · intro h
    funext i
    by_contra hi
    have : i ∈ Finset.univ.filter (fun c : Fin 144 => v c ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [h] at this
    exact absurd this (by simp)
  · intro h; subst h
    simp

set_option maxHeartbeats 2000000 in
/-- **QECLean's chain-level Gross distance, unconditional.**  This is the
interface the binary-vector transport consumes: it speaks about
`ZMod 2`-valued `C₁`-chains directly, so no Pauli-group element ever has to be
built.  Its two inputs are discharged upstream. -/
theorem gross_chain_distance_eq_12 :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 :=
  gross_chain_distance_eq_12_of_engine
    LightStab.lightStabilizerClassification_holds LightStab.mimBound_holds

set_option maxHeartbeats 2000000 in
/-- **The transport.**  Every vector that `min_weight_ker_not_mem_rowspace`
counts is the binary shadow of a minimum-weight logical chain, whose weight
QECLean bounds by 12. -/
theorem twelve_le_hammingNorm (v : Fin 144 → ZMod 2)
    (hker : LE_Z.mulVec v = 0) (hrow : v ∉ LE_X.rowSpace) :
    12 ≤ hammingNorm v := by
  have hcyc : psi v ∈ grossComplex.cycles := (LE_Z_ker_cycles v).mp hker
  have hbnd : psi v ∉ grossComplex.boundaries :=
    fun h => hrow (mem_rowSpace_of_mem_boundaries v h)
  have hmem : grossComplex.chainWeight (psi v) ∈
      {w : ℕ | ∃ u : GrossGroup × Fin 2 → ZMod 2,
        u ∈ grossComplex.cycles ∧ u ∉ grossComplex.boundaries ∧
        grossComplex.chainWeight u = w} :=
    ⟨psi v, hcyc, hbnd, rfl⟩
  have h := gross_chain_distance_eq_12.2 hmem
  rwa [chainWeight_psi v] at h

/-! ## T4.5  The Z-side

`LE_X`'s kernel is the dual cycle space (`ker ∂₂ᵀ`) and `LE_Z`'s row space is the
dual boundary space (`im ∂₁ᵀ`).  Together with QECLean's chain-level `d_X = d_Z`
(`bb_cycle_bound_iff_dual_bound`) this gives the second half of the bound.

`b0`/`b0d` are `∂₁ᵀ`/`∂₂ᵀ` with the index types pinned, for the same reason
`b1`/`b2` exist. -/

noncomputable def b0 : (GrossGroup → ZMod 2) →ₗ[ZMod 2] (GrossGroup × Fin 2 → ZMod 2) :=
  grossComplex.cutMap

noncomputable def b0d : (GrossGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (GrossGroup → ZMod 2) :=
  grossComplex.dualBoundary

theorem b0_apply (s : GrossGroup → ZMod 2) (p : GrossGroup × Fin 2) :
    b0 s p = ∑ v : GrossGroup, s v * b1 (Pi.single p 1) v := rfl

theorem b0d_apply (c : GrossGroup × Fin 2 → ZMod 2) (f : GrossGroup) :
    b0d c f = ∑ e : GrossGroup × Fin 2, c e * b2 (Pi.single f 1) e := rfl

/-- `LE_X.mulVec` *is* `∂₂ᵀ` after reindexing. -/
theorem LE_X_mulVec (v : Fin 144 → ZMod 2) :
    LE_X.mulVec v = fun g => b0d (psi v) (e72 g) := by
  funext g
  rw [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_equiv e144 (fun c => LE_X g c * v c)
        (fun p => LE_X g (e144.symm p) * v (e144.symm p))
        (fun c => by rw [Equiv.symm_apply_apply])]
  rw [b0d_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [LE_X_entry, psi]
  exact mul_comm _ _

/-- `LE_X`'s kernel is the dual cycle space. -/
theorem LE_X_ker_dualCycles (v : Fin 144 → ZMod 2) :
    LE_X.mulVec v = 0 ↔ b0d (psi v) = 0 := by
  rw [LE_X_mulVec v]
  constructor
  · intro h
    funext f
    obtain ⟨g, rfl⟩ := e72.surjective f
    exact congrFun h g
  · intro h
    funext g
    exact congrFun h (e72 g)

theorem LE_X_ker_dualCycles' (v : Fin 144 → ZMod 2) :
    LE_X.mulVec v = 0 ↔ psi v ∈ grossComplex.dualCycles :=
  (LE_X_ker_dualCycles v).trans Iff.rfl

/-- Every row of `LE_Z` is `cutMap` applied to the corresponding coordinate vector. -/
theorem LE_Z_row (g : Fin (12*6)) :
    psiLin (LE_Z g) = b0 (Pi.single (e72 g) 1) := by
  funext p
  change psi (LE_Z g) p = b0 (Pi.single (e72 g) 1) p
  rw [psi, LE_Z_entry, b0_apply]
  rw [Finset.sum_eq_single (e72 g)]
  · simp
  · intro x _ hx
    rw [Pi.single_apply, ite_eq_right hx, zero_mul]
  · intro hx; exact absurd (Finset.mem_univ (e72 g)) hx

/-- `∂₁ᵀ` is the sum of its values on the coordinate vectors. -/
theorem b0_eq_sum (s : GrossGroup → ZMod 2) :
    b0 s = ∑ k, s k • b0 (Pi.single k 1) := by
  conv_lhs => rw [← sum_smul_single s]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [map_smul])

/-- A dual boundary is a combination of rows of `LE_Z`. -/
theorem mem_rowSpace_of_mem_dualBoundaries (v : Fin 144 → ZMod 2)
    (h : psi v ∈ grossComplex.dualBoundaries) : v ∈ LE_Z.rowSpace := by
  have h' : psi v ∈ b0.range := h
  obtain ⟨s, hs⟩ := (LinearMap.mem_range).mp h'
  have hs' : b0 s = psiLin v := hs
  rw [Matrix.rowSpace]
  have hv : v = ∑ k, s k • (LE_Z (e72.symm k)) := by
    apply psiLin.injective
    rw [← hs', b0_eq_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, LE_Z_row, Equiv.apply_symm_apply]
  rw [hv]
  refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span (Set.mem_range_self (e72.symm k))

/-- Chain-level bound transfer through the dual (QECLean's `d_X = d_Z`). -/
theorem dual_bound_of_primal (K : ℕ)
    (hX : ∀ c ∈ grossComplex.cycles, c ∉ grossComplex.boundaries →
      K ≤ grossComplex.chainWeight c) :
    ∀ c ∈ grossComplex.dualCycles, c ∉ grossComplex.dualBoundaries →
      K ≤ grossComplex.chainWeight c :=
  (bb_cycle_bound_iff_dual_bound (G := GrossGroup) grossA grossB K).mp hX

set_option maxHeartbeats 2000000 in
/-- The Z-side transport. -/
theorem twelve_le_hammingNorm_dual (v : Fin 144 → ZMod 2)
    (hker : LE_X.mulVec v = 0) (hrow : v ∉ LE_Z.rowSpace) :
    12 ≤ hammingNorm v := by
  have hdc : psi v ∈ grossComplex.dualCycles := (LE_X_ker_dualCycles' v).mp hker
  have hdb : psi v ∉ grossComplex.dualBoundaries :=
    fun h => hrow (mem_rowSpace_of_mem_dualBoundaries v h)
  have hX : ∀ c ∈ grossComplex.cycles, c ∉ grossComplex.boundaries →
      12 ≤ grossComplex.chainWeight c := fun c hc hb =>
    gross_chain_distance_eq_12.2
      (show grossComplex.chainWeight c ∈
        {w : ℕ | ∃ u : GrossGroup × Fin 2 → ZMod 2,
          u ∈ grossComplex.cycles ∧ u ∉ grossComplex.boundaries ∧
          grossComplex.chainWeight u = w} from ⟨c, hc, hb, rfl⟩)
  have h := dual_bound_of_primal 12 hX (psi v) hdc hdb
  rwa [chainWeight_psi v] at h

/-! ## T4.6  The read-out: the two `min_weight_ker_not_mem_rowspace` bounds -/

set_option maxHeartbeats 2000000 in
/-- `LE_Z`'s kernel minus `LE_X`'s row space — Lean-QEC's `CSS_pair.dX`. -/
theorem BB144_dX_ge_12 : 12 ≤ min_weight_ker_not_mem_rowspace LE_Z LE_X := by
  unfold min_weight_ker_not_mem_rowspace
  extract_lets undetectable_errors
  rcases h : (Finset.image hammingNorm undetectable_errors.toFinset).min with _ | m
  · simp
  simp only
  apply Finset.mem_of_min at h
  simp only [Finset.mem_image] at h
  obtain ⟨v, hv, rfl⟩ := h
  rw [Set.mem_toFinset] at hv
  obtain ⟨hker, hrow⟩ := hv
  exact twelve_le_hammingNorm v (show LE_Z.mulVec v = 0 from hker) hrow

set_option maxHeartbeats 2000000 in
/-- `LE_X`'s kernel minus `LE_Z`'s row space — Lean-QEC's `CSS_pair.dZ`. -/
theorem BB144_dZ_ge_12 : 12 ≤ min_weight_ker_not_mem_rowspace LE_X LE_Z := by
  unfold min_weight_ker_not_mem_rowspace
  extract_lets undetectable_errors
  rcases h : (Finset.image hammingNorm undetectable_errors.toFinset).min with _ | m
  · simp
  simp only
  apply Finset.mem_of_min at h
  simp only [Finset.mem_image] at h
  obtain ⟨v, hv, rfl⟩ := h
  rw [Set.mem_toFinset] at hv
  obtain ⟨hker, hrow⟩ := hv
  exact twelve_le_hammingNorm_dual v (show LE_X.mulVec v = 0 from hker) hrow

/-- **The `[[144,12,12]]` Gross code's distance lower bound, from QECLean's
Gross formalization.**  For any `CSS_pair` whose check matrices are precisely
`BB144_X_mat`/`BB144_Z_mat`, the binary-symplectic distance is at least 12 — with
no `bv_decide`, no `native_decide` and no 3.26 GB olean. -/
theorem BB144_toBSM_distance_ge_12 (C : CSS_pair 144 72 72)
    (hX : C.H₁ = LE_X) (hZ : C.H₂ = LE_Z) :
    12 ≤ C.toBSM.distance (Nat.add_pos_left C.nt₁ 72) := by
  rw [CSS.toBSM_dist_eq]
  change 12 ≤ min (min_weight_ker_not_mem_rowspace C.H₂ C.H₁)
    (min_weight_ker_not_mem_rowspace C.H₁ C.H₂)
  rw [hX, hZ]
  exact le_min BB144_dX_ge_12 BB144_dZ_ge_12

/-! ## T5  本库字面矩阵的**上界**（下界见上，对 `LE_X` / `LE_Z`）

`Codes/BB144Witness.lean` 用 72 条字面行写同一组矩阵，其重量-12 见证给出上界。
这里把两条上界也用 `Codes/DistanceLabel.lean` 的具名标签写出来，便于与下界对照：
`libDX` 以 X 型校验作核、`libDZ` 以 Z 型校验作核。

**这一里已补齐**：下界（`BB144_dX_ge_12` / `BB144_dZ_ge_12`）是对 `LE_X` / `LE_Z` 证的，
搬到本库字面矩阵所需的 $72\times144$ 矩阵同一性由 `Codes/BB144Literal.lean` 给出
（`bb144Hx_eq_LE_X` / `bb144Hz_eq_LE_Z`），本模块下面两条 `_eq_12` 正是经它们运输。
那条同一性走**逐条目** `fin_cases`：整条一次 `by decide` 在 8000000 心跳下不收敛。 -/

open QECCertificates
open QECCertificates (libDX libDZ)

/-- **上界**：重量-12 的显式逻辑算符给出 `libDX ≤ 12`。

三件事分开写（`have` 里各自的期望类型是确定的），最后再拼——直接内联会让
`minWeight_le_of_witness` 的隐式参数留成元变量。 -/
theorem bb144_libDX_le_12 : libDX bb144Hx bb144Hz ≤ 12 := by
  have hker : bb144XW ∈ LinearMap.ker bb144Hx.toLin' :=
    mem_ker_of_inKerB bb144Hx (v := bb144XW) (by decide)
  have hnot : bb144XW ∉ bb144Hz.rowSpace :=
    not_mem_rowSpace_of_dualCheck bb144Hz (w := bb144ZW) (by decide) (by decide)
  have hw : hammingNorm bb144XW = 12 := by decide
  exact minWeight_le_of_witness bb144Hx bb144Hz hker hnot hw

/-- **上界**：对称的一侧。 -/
theorem bb144_libDZ_le_12 : libDZ bb144Hx bb144Hz ≤ 12 := by
  have hker : bb144ZW ∈ LinearMap.ker bb144Hz.toLin' :=
    mem_ker_of_inKerB bb144Hz (v := bb144ZW) (by decide)
  have hnot : bb144ZW ∉ bb144Hx.rowSpace :=
    not_mem_rowSpace_of_dualCheck bb144Hx (w := bb144XW) (by decide) (by decide)
  have hw : hammingNorm bb144ZW = 12 := by decide
  exact minWeight_le_of_witness bb144Hz bb144Hx hker hnot hw

end QECCertificates.BB144Distance
