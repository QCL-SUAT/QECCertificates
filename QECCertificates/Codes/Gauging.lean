/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.RankCertificate
import QECCertificates.GF2.Canonical
import QECCertificates.GF2.HGPCompression

/-!
# gauging 两分量的形式化陈述（表示层）

本模块的交付物是 **"gauging 两分量（空间型 / 时间型）的形式化陈述"**。
本模块把两个分量的**表示层内容**落成定理，口径与预研探针逐条对齐
（`tools/probeA/probeB_gauging.py`、`probeB_gauging_e2e.py`、`probeB_time.py`
及其沉积 JSON）：

## 一、空间型分量：测一个逻辑 = 变形码（`probeB_gauging.py`）

把 X 型逻辑算符 $\ell$ 提升为稳定子（"测 $\ell$"），变形码的校验是

$$H_X' = \begin{pmatrix}H_X\\ \hline \ell\end{pmatrix},\qquad H_Z' = H_Z .$$

* `deformX_css`：**CSS 相容性保持**——$\ell \perp H_Z$ 各行 ⟹ $H_X'H_Z'^\top = 0$。
* `finrank_deformX` / `deformX_k`：**维数定律**——$\ell \notin \mathrm{row}\,H_X$ 时
  $k$ 恰减一（对应预研 $[[90,8,10]] \to [[90,7,10]]$ 的 $k:8\to7$）。

## 二、W–Y 提升：Gauss 律之积 = 顶点算子之积（`probeB_gauging_e2e.py`）

曲线 gauging 的恒等式 $L = \prod_v A_v$ 在表示层是**纯组合事实**：
辅助图（无自环）上每个边量子比特恰有两个端点，故 Gauss 算符
$A_v = X_v\prod_{e\ni v}X_e$ 之积中所有边算符成对相消：

`gauss_prod_eq_vertex_prod`：$\sum_v A_v = \sum_v X_v$（GF(2) 向量等式）。

这是 `probeB_gauging_e2e` 里 `L = Π_v A_v` 与"维度 4→3"的表示层内容。

## 三、时间型分量：最小不可探测重量 = 重复轮数（`probeB_time.py`）

时间型 gauging 的链是"相邻轮校验" $e_i + e_{i+1}$（$i=0..T-2$）：

* `timeLike_eq_of_repCheck`：与所有时间校验正交 ⟹ 逐轮取值相同；
* `timeLike_weight_eq`：非零 ⟹ 取值全一 ⟹ 重量恰为轮数 $T = S+1$。

于是"最小不可探测重量 = 重复轮数"在表示层成为定理（下界与上界同一行给出）。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {n : ℕ}

/-! ## 一、空间型分量：变形码 -/

/-- **空间型 gauging**：把 X 型算符 `ell` 提升为稳定子——X 校验追加一行 `ell`，
Z 校验不变（表示层）。 -/
def deformXRows (L : List (Vec n)) (ell : Vec n) : List (Vec n) := L ++ [ell]

/-- **CSS 相容性在变形下保持**：`ell` 与 Z 校验各行正交是关键前提
（这正是"`ell` 是 X 型逻辑算符"的判据）。 -/
theorem deformX_css {Hx Hz : List (Vec n)} {ell : Vec n}
    (hell : ∀ r ∈ Hz, ell ⬝ᵥ r = 0) (hcss : ∀ a ∈ Hx, ∀ b ∈ Hz, a ⬝ᵥ b = 0) :
    ∀ a ∈ deformXRows Hx ell, ∀ b ∈ Hz, a ⬝ᵥ b = 0 := by
  intro a ha b hb
  rcases List.mem_append.mp ha with ha' | ha'
  · exact hcss a ha' b hb
  · have heq : a = ell := by simpa using ha'
    rw [heq]
    exact hell b hb

/-- 追加一个不在行空间中的向量，维数恰增一。 -/
theorem finrank_spanL_append_singleton_of_not_mem {L : List (Vec n)} {ell : Vec n}
    (h : ell ∉ spanL L) :
    Module.finrank (ZMod 2) (spanL (L ++ [ell])) = Module.finrank (ZMod 2) (spanL L) + 1 := by
  rw [spanL_append_singleton L ell]
  have hbot : spanL L ⊓ Submodule.span (ZMod 2) ({ell} : Set (Vec n)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx2' : x = 0 ∨ x = ell := by
      have hmem : x ∈ Submodule.span (ZMod 2) ({ell} : Set (Vec n)) := hx2
      refine Submodule.span_induction (p := fun y _ => y = 0 ∨ y = ell) ?_ ?_ ?_ ?_ hmem
      · intro y hy
        exact Or.inr (by simpa using hy)
      · exact Or.inl rfl
      · intro a b _ _ ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by rw [zero_add])
        · exact Or.inr (by rw [add_zero])
        · exact Or.inl (by rw [add_self])
      · intro c a _ ha
        rcases ha with rfl | rfl
        · exact Or.inl (by rw [smul_zero])
        · by_cases hc : c = 0
          · exact Or.inl (by rw [hc, zero_smul])
          · exact Or.inr (by rw [eq_one_of_ne_zero hc, one_smul])
    rcases hx2' with rfl | rfl
    · rfl
    · exact absurd hx1 h
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (V := Vec n)
    (s := spanL L) (t := Submodule.span (ZMod 2) ({ell} : Set (Vec n)))
  rw [hbot, finrank_bot, add_zero] at hdim
  rw [hdim]
  congr 1
  exact finrank_span_singleton (K := ZMod 2) (by rintro rfl; exact h (Submodule.zero_mem _))

/-- **变形码的秩定理**：`ell ∉ row H_X` 时 X 秩恰增一（`rowReduce` 读数下）。 -/
theorem deformX_rowReduce_length {L : List (Vec n)} {ell : Vec n} (h : ell ∉ spanL L) :
    (rowReduce (L ++ [ell])).length = (rowReduce L).length + 1 := by
  have h1 := finrank_spanL_eq_length_rowReduce (L ++ [ell])
  have h2 := finrank_spanL_eq_length_rowReduce L
  have h3 := finrank_spanL_append_singleton_of_not_mem (n := n) h
  omega

/-- **空间型 gauging 的维数定律**：把非平凡 X 型逻辑提升为稳定子，逻辑位数恰减一
（$k = n - \mathrm{rank}\,H_X - \mathrm{rank}\,H_Z$，与预研 $k:8\to7$ 对齐）。 -/
theorem deformX_k {Lx Lz : List (Vec n)} {ell : Vec n} (h : ell ∉ spanL Lx) :
    n - (rowReduce (Lx ++ [ell])).length - (rowReduce Lz).length
      = (n - (rowReduce Lx).length - (rowReduce Lz).length) - 1 := by
  have hlen := deformX_rowReduce_length (n := n) h
  have hle := length_rowReduce_le Lx
  rw [hlen]
  omega

/-! ## 二、W–Y 提升：Gauss 律之积 = 顶点算子之积 -/

/-- **Gauss 算符**：顶点 `v` 的星——$X_v\prod_{e\ni v}X_e$（辅助图上的表示层向量）。

量子比特编号：`Sum.inl v` = 顶点量子比特，`Sum.inr e` = 边量子比特。 -/
def gaussOp {k m : ℕ} (ends : Fin m → Fin k × Fin k) (v : Fin k) : (Fin k ⊕ Fin m) → ZMod 2 :=
  Sum.elim (fun w => if w = v then 1 else 0)
    (fun e => if (ends e).1 = v ∨ (ends e).2 = v then 1 else 0)

/-- **顶点算子**：$X_v$（只作用在顶点量子比特上）。 -/
def vertexOp {k m : ℕ} (v : Fin k) : (Fin k ⊕ Fin m) → ZMod 2 :=
  Sum.elim (fun w => if w = v then 1 else 0) (fun _ => 0)

/-- **W–Y 提升恒等式**：无自环辅助图上，所有 Gauss 算符之积 = 所有顶点算子之积
（边算符成对相消：每条边恰有两个端点）。对应预研的 $L = \prod_v A_v$。 -/
theorem gauss_prod_eq_vertex_prod {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) :
    (∑ v : Fin k, gaussOp ends v) = ∑ v : Fin k, vertexOp v := by
  funext i
  have hsingle : ∀ a : Fin k, (∑ v : Fin k, (if a = v then (1 : ZMod 2) else 0)) = 1 := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [ite_eq_left rfl]
    · intro b _ hb
      rw [ite_eq_right (fun h : a = b => hb h.symm)]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rcases i with w | e
  · simp only [Finset.sum_apply, gaussOp, vertexOp, Sum.elim_inl]
  · simp only [Finset.sum_apply, gaussOp, vertexOp, Sum.elim_inr]
    have hor : ∀ v : Fin k,
        (if (ends e).1 = v ∨ (ends e).2 = v then (1 : ZMod 2) else 0)
          = (if (ends e).1 = v then 1 else 0) + (if (ends e).2 = v then 1 else 0) := by
      intro v
      by_cases h1 : (ends e).1 = v
      · have h2 : ¬((ends e).2 = v) := fun h2 => hloop e (h1.trans h2.symm)
        rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right h2, add_zero]
      · by_cases h2 : (ends e).2 = v
        · rw [ite_eq_right h1, ite_eq_left (Or.inr h2), ite_eq_left h2, zero_add]
        · rw [ite_eq_right (fun h => h.elim h1 h2), ite_eq_right h1, ite_eq_right h2,
            add_zero]
    rw [Finset.sum_congr rfl fun v _ => hor v, Finset.sum_add_distrib,
      hsingle (ends e).1, hsingle (ends e).2, Finset.sum_const_zero]
    exact CharTwo.add_self_eq_zero 1

/-! ## 三、时间型分量：最小不可探测重量 = 重复轮数 -/

/-- **时间型链的相邻对校验**：第 `i` 对是 `e_i + e_{i+1}`（数据比特 = `Fin (S+1)`）。 -/
def repCheck (S : ℕ) (i : Fin S) : Vec (S + 1) :=
  unitVec (Fin.castSucc i) + unitVec i.succ

/-- `unitVec i` 与 `x` 的点积就是 `x i`。 -/
lemma unitVec_dot {n : ℕ} (i : Fin n) (x : Vec n) : unitVec i ⬝ᵥ x = x i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · rw [unitVec, ite_eq_left rfl, one_mul]
  · intro b _ hb
    rw [unitVec, ite_eq_right (fun h : b = i => hb h), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **时间型分量（下界方向）**：与所有时间校验正交的向量，逐轮取值相同
——时间型链上"跨全部轮次"的算符是唯一的不可探测方向。 -/
theorem timeLike_eq_of_repCheck {S : ℕ} {x : Vec (S + 1)}
    (h : ∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) : ∀ i j : Fin (S + 1), x i = x j := by
  have hstep : ∀ i : Fin S, x (Fin.castSucc i) = x i.succ := by
    intro i
    have hi := h i
    rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot] at hi
    exact (add_eq_zero_iff_eq _ _).mp hi
  have key : ∀ i : Fin (S + 1), x i = x 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih => rw [← hstep j]; exact ih
  intro i j
  rw [key i, key j]

/-- **时间型分量（精确值）**：与所有时间校验正交的**非零**向量取值全一，
重量恰为重复轮数 `T = S+1`——"最小不可探测重量 = 重复轮数"在表示层成立。 -/
theorem timeLike_weight_eq {S : ℕ} {x : Vec (S + 1)}
    (h : ∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) (hx : x ≠ 0) :
    hammingNorm x = S + 1 := by
  have hzeroOfNeOne : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  have hall : ∀ i : Fin (S + 1), x i = 1 := by
    intro i
    by_contra hne
    refine hx (funext fun j => ?_)
    rw [← timeLike_eq_of_repCheck h i j]
    exact hzeroOfNeOne (x i) hne
  have hfilter : (Finset.univ.filter (fun i : Fin (S + 1) => x i ≠ 0)) = Finset.univ := by
    refine Finset.filter_true_of_mem fun i _ => ?_
    rw [hall i]
    exact one_ne_zero
  show (Finset.univ.filter (fun i : Fin (S + 1) => x i ≠ 0)).card = S + 1
  rw [hfilter, Finset.card_univ, Fintype.card_fin]

end QECCertificates
