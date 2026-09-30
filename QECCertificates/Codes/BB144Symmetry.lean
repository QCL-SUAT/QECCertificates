/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB144Literal
import QECCertificates.Codes.BB144Rank
import QECCertificates.Codes.FoldTransversal

/-!
# BB $[[144,12,12]]$ 的**平移对称性**（对称性破缺路线的第一步）

## 这一支要什么

`tools/bb144_server/bb144_sb.py` 在 BB144 的 SAT 编码上加字典序轨道代表约束，
实测把自家证书的加法步数压到四到七分之一。那条路线的**可靠性**（破缺后的 UNSAT
⟹ 原命题）要靠一件事：平移群 $G=Z_{12}\times Z_6$ 的每个元素诱导物理比特的一个置换，
它**同时**保持

* 重量（$x$ 的支撑被搬运，重量逐字不变）；
* $\mathrm{rowsp}(H_X)$ 与 $\mathrm{rowsp}(H_Z)$（故 $\ker H_X$、$\ker H_Z$ 不变）；
* 配对 $x\cdot w$（故"非平凡"这一条也不变）。

三件事都保住之后，$(x,w)\mapsto(g\cdot x,\,g\cdot w)$ 才是编码的一个**对称作用**，
"每个轨道取字典序最小元"才有意义。本模块把这三条在内核里证掉。

## 与既有模块的分工：本模块几乎不重证

`Codes/FoldTransversal.lean` 已经把这三件事的**一般形态**证完了，而且是对**任意**
比特置换陈述的：`hammingNorm_permVec`（保重量）、`dotProduct_permVec`（保配对）、
`permVec_mem_spanL_iff`（保行空间，需行列表在两个方向下自映射）、
`inKerB_permVec`（保核成员）。故本模块**唯一的**新内容是一件事：
**平移置换把每条校验行映成一条校验行**（`permVec_bb144Trans_hxRow` 一族），
其余全是把上面那批一般引理实例化。

## 为什么走符号路线

CLAUDE.md §一 记着：144 宽的字面矩阵点积的内核归约约 5 分钟、峰值数 GB，
`Codes/BB144Literal` 的 olean 有 90 MB。故**不**对 $72\times144$ 的矩阵做 `by decide`，
而是用 `Codes/BB144Distance.lean` 已备好的**逐条目**引理
`LE_X_entry_zero/one`、`LE_Z_entry_zero/one`（它们把条目写成群环单项式
`grossA (h - e₇₂ g)` 的形式），在**群元素**层面做重标号。平移把列 $(h,b)$ 送到
$(h-t,b)$，于是

$$\big(\text{第 }k\text{ 行}\big)(h-t,\,b)\;=\;\mathrm{gross}\big(h-t-e_g k\big)
\;=\;\mathrm{gross}\big(h-(e_g k+t)\big)\;=\;\big(\text{第 }e_g^{-1}(e_g k+t)\text{ 行}\big)(h,\,b),$$

即**第 $k$ 行搬到了第 $e_g^{-1}(e_g k+t)$ 行**——一条纯代数恒等式，无枚举。

**两侧的索引是同一个**（`e₇₂⁻¹(e₇₂ k + t)`），即便 X 侧的条目是 `h - e₇₂ k`、
Z 侧是 `e₇₂ k - h`：两处的 `t` 都落在被减数那一侧。这一步本轮先写错过一次
（Z 侧误记成 `-t`），故两处都留了 `abel` 收尾而不是靠眼看。

## 可信基

全程只有 `by decide` 于**群层面的小等式**（`Fin 2` 的二值拆分），零 `sorry`、
零自定义公理、零 `native_decide`。
-/

namespace QECCertificates

open QECCertificates.BB144Distance

open _root_.Matrix

-- `GrossGroup`（`= ZMod 12 × ZMod 6`）、`grossA`/`grossB` 都在上游 QEC 的命名空间里
open Quantum.Stabilizer.Homological.BB

/-- `Fin 2` 只有两个元素。写成具名引理是为了让下面的分支拿到**字面量** `0`/`1`：
`fin_cases` 给的是 `(fun i => i) ⟨0, ⋯⟩` 这种未 beta 归约的形状，而
`LE_X_entry_zero` 的式子左边是字面 `0`，`rw` 按语法匹配会失配。 -/
theorem fin2_eq_zero_or_one (b : Fin 2) : b = 0 ∨ b = 1 := by
  revert b; decide

/-- **平移置换**：把物理比特 `c`（经 `e144` 读作 `(群元素, 块)`）的群元素平移 `t`，块不动。

这正是 `bb144_sb.py` 里 `translation_perms` 生成的那 72 个置换——那里按 `Fin 144`
的十进制下标写，这里按码的群结构写，两者是同一个置换。 -/
noncomputable def bb144Trans (t : GrossGroup) : Equiv.Perm (Fin 144) where
  toFun c := e144.symm ((e144 c).1 + t, (e144 c).2)
  invFun c := e144.symm ((e144 c).1 - t, (e144 c).2)
  left_inv c := by
    dsimp only
    simp only [Equiv.apply_symm_apply]
    have h : ((e144 c).1 + t - t, (e144 c).2) = e144 c := by simp
    rw [h, Equiv.symm_apply_apply]
  right_inv c := by
    dsimp only
    simp only [Equiv.apply_symm_apply]
    have h : ((e144 c).1 - t + t, (e144 c).2) = e144 c := by simp
    rw [h, Equiv.symm_apply_apply]

/-- 平移置换的逆就是反向平移。这条让"行列表在两个方向下自映射"只证一次。 -/
theorem bb144Trans_symm_eq (t : GrossGroup) : (bb144Trans t).symm = bb144Trans (-t) := by
  apply Equiv.ext
  intro c
  simp only [bb144Trans, Equiv.coe_fn_mk, Equiv.symm_mk, sub_eq_add_neg]

/-- 平移置换作用在**列**上的显式形态：`(h,b) ↦ (h+t,b)`。 -/
theorem bb144Trans_apply (t g : GrossGroup) (b : Fin 2) :
    bb144Trans t (e144.symm (g, b)) = e144.symm (g + t, b) := by
  simp only [bb144Trans, Equiv.coe_fn_mk, Equiv.apply_symm_apply]

/-- 逆置换作用在**列**上的显式形态：`(h,b) ↦ (h-t,b)`。核成员与行空间用的是这一支
（`permVec π v i = v (π.symm i)`）。 -/
theorem bb144Trans_symm_apply (t g : GrossGroup) (b : Fin 2) :
    (bb144Trans t).symm (e144.symm (g, b)) = e144.symm (g - t, b) := by
  simp only [bb144Trans, Equiv.coe_fn_mk, Equiv.symm_mk, Equiv.apply_symm_apply]

/-! ## 一、核心：平移把第 `k` 行搬到第 `e₇₂⁻¹(e₇₂ k + t)` 行

按块拆成两条（`b = 0` / `b = 1`）再合起来：拆开之后列的第二个分量是**字面量**，
`LE_X_entry_zero`/`LE_X_entry_one` 才能按语法匹配上。 -/

theorem permVec_bb144Trans_hxRow_apply_zero (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HxRow k) (e144.symm (g, 0))
      = bb144HxRow (e72.symm (e72 k + t)) (e144.symm (g, 0)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HxRow, bb144HxRow, bb144Hx_eq_LE_X,
      LE_X_entry_zero, LE_X_entry_zero, Equiv.apply_symm_apply]
  congr 1
  abel

theorem permVec_bb144Trans_hxRow_apply_one (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HxRow k) (e144.symm (g, 1))
      = bb144HxRow (e72.symm (e72 k + t)) (e144.symm (g, 1)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HxRow, bb144HxRow, bb144Hx_eq_LE_X,
      LE_X_entry_one, LE_X_entry_one, Equiv.apply_symm_apply]
  congr 1
  abel

/-- **逐条目的核心恒等式**（X 侧）。 -/
theorem permVec_bb144Trans_hxRow_apply (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) (b : Fin 2) :
    permVec (bb144Trans t) (bb144HxRow k) (e144.symm (g, b))
      = bb144HxRow (e72.symm (e72 k + t)) (e144.symm (g, b)) := by
  rcases fin2_eq_zero_or_one b with rfl | rfl
  · exact permVec_bb144Trans_hxRow_apply_zero t k g
  · exact permVec_bb144Trans_hxRow_apply_one t k g

/-- **核心恒等式的函数形态**：第 `k` 行搬到第 `e₇₂⁻¹(e₇₂ k + t)` 行（X 侧）。 -/
theorem permVec_bb144Trans_hxRow (t : GrossGroup) (k : Fin (12 * 6)) :
    permVec (bb144Trans t) (bb144HxRow k)
      = bb144HxRow (e72.symm (e72 k + t)) := by
  funext c
  conv_lhs => rw [← Equiv.symm_apply_apply e144 c]
  conv_rhs => rw [← Equiv.symm_apply_apply e144 c]
  exact permVec_bb144Trans_hxRow_apply t k (e144 c).1 (e144 c).2

theorem permVec_bb144Trans_hzRow_apply_zero (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HzRow k) (e144.symm (g, 0))
      = bb144HzRow (e72.symm (e72 k + t)) (e144.symm (g, 0)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HzRow, bb144HzRow, bb144Hz_eq_LE_Z,
      LE_Z_entry_zero, LE_Z_entry_zero, Equiv.apply_symm_apply]
  congr 1
  abel

theorem permVec_bb144Trans_hzRow_apply_one (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HzRow k) (e144.symm (g, 1))
      = bb144HzRow (e72.symm (e72 k + t)) (e144.symm (g, 1)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HzRow, bb144HzRow, bb144Hz_eq_LE_Z,
      LE_Z_entry_one, LE_Z_entry_one, Equiv.apply_symm_apply]
  congr 1
  abel

/-- **逐条目的核心恒等式**（Z 侧）。注意 `LE_Z` 的条目是 `e₇₂ g - h`（与 X 侧差一个
符号），故重排走的是另一条路——同一件事，代数式不同，不共用证文。 -/
theorem permVec_bb144Trans_hzRow_apply (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) (b : Fin 2) :
    permVec (bb144Trans t) (bb144HzRow k) (e144.symm (g, b))
      = bb144HzRow (e72.symm (e72 k + t)) (e144.symm (g, b)) := by
  rcases fin2_eq_zero_or_one b with rfl | rfl
  · exact permVec_bb144Trans_hzRow_apply_zero t k g
  · exact permVec_bb144Trans_hzRow_apply_one t k g

/-- **核心恒等式的函数形态**（Z 侧）。 -/
theorem permVec_bb144Trans_hzRow (t : GrossGroup) (k : Fin (12 * 6)) :
    permVec (bb144Trans t) (bb144HzRow k)
      = bb144HzRow (e72.symm (e72 k + t)) := by
  funext c
  conv_lhs => rw [← Equiv.symm_apply_apply e144 c]
  conv_rhs => rw [← Equiv.symm_apply_apply e144 c]
  exact permVec_bb144Trans_hzRow_apply t k (e144 c).1 (e144 c).2

/-! ## 二、行列表自映射（两个方向）

`permVec_mem_spanL_iff` 要的是 `∀ r ∈ L, permVec π r ∈ L` **与**
`∀ r ∈ L, permVec π.symm r ∈ L`——两个方向都要：反方向用来证"像落在行空间里
⟹ 原像也落在"，而那正是"像仍是**非平凡**算符"的一半。 -/

theorem bb144_permVec_hxRow_mem (t : GrossGroup) {r : Vec 144} (hr : r ∈ bb144Rx) :
    permVec (bb144Trans t) r ∈ bb144Rx := by
  rw [bb144Rx, List.mem_ofFn] at hr ⊢
  obtain ⟨k, rfl⟩ := hr
  exact ⟨e72.symm (e72 k + t), (permVec_bb144Trans_hxRow t k).symm⟩

theorem bb144_permVec_hzRow_mem (t : GrossGroup) {r : Vec 144} (hr : r ∈ bb144Rz) :
    permVec (bb144Trans t) r ∈ bb144Rz := by
  rw [bb144Rz, List.mem_ofFn] at hr ⊢
  obtain ⟨k, rfl⟩ := hr
  exact ⟨e72.symm (e72 k + t), (permVec_bb144Trans_hzRow t k).symm⟩

/-! ## 三、三条断言

群元素 `t` 的平移置换保重量、保两侧行空间、保配对。三条都是把
`Codes/FoldTransversal.lean` 的一般引理实例化——**没有一行新的数学**。 -/

/-- **保重量**：平移不改变 `v` 的 Hamming 重量。 -/
theorem bb144Trans_hammingNorm (t : GrossGroup) (v : Vec 144) :
    hammingNorm (permVec (bb144Trans t) v) = hammingNorm v :=
  hammingNorm_permVec _ _

/-- **保配对**：平移不改变 $x\cdot w$。 -/
theorem bb144Trans_dotProduct (t : GrossGroup) (v w : Vec 144) :
    (permVec (bb144Trans t) v) ⬝ᵥ (permVec (bb144Trans t) w) = v ⬝ᵥ w :=
  dotProduct_permVec _ _ _

/-- **保 X 侧行空间**：平移是码的自同构（X 侧）。 -/
theorem bb144Trans_preserves_spanL_x (t : GrossGroup) {v : Vec 144}
    (hv : v ∈ spanL bb144Rx) : permVec (bb144Trans t) v ∈ spanL bb144Rx :=
  permVec_mem_spanL _ (fun _ hr => subset_spanL (bb144_permVec_hxRow_mem t hr)) hv

/-- **保 Z 侧行空间**：平移是码的自同构（Z 侧）。 -/
theorem bb144Trans_preserves_spanL_z (t : GrossGroup) {v : Vec 144}
    (hv : v ∈ spanL bb144Rz) : permVec (bb144Trans t) v ∈ spanL bb144Rz :=
  permVec_mem_spanL _ (fun _ hr => subset_spanL (bb144_permVec_hzRow_mem t hr)) hv

/-- **行空间成员关系双向不变**（X 侧）：像落在行空间里 ⟺ 原像落在行空间里。
反方向由 `t ↦ -t` 给出（`bb144Trans_symm_eq`）。 -/
theorem bb144Trans_mem_spanL_iff_x (t : GrossGroup) {v : Vec 144} :
    permVec (bb144Trans t) v ∈ spanL bb144Rx ↔ v ∈ spanL bb144Rx :=
  permVec_mem_spanL_iff _ (fun _ hr => bb144_permVec_hxRow_mem t hr)
    (fun r hr => by
      rw [bb144Trans_symm_eq]
      exact bb144_permVec_hxRow_mem (-t) hr)

/-- **行空间成员关系双向不变**（Z 侧）。 -/
theorem bb144Trans_mem_spanL_iff_z (t : GrossGroup) {v : Vec 144} :
    permVec (bb144Trans t) v ∈ spanL bb144Rz ↔ v ∈ spanL bb144Rz :=
  permVec_mem_spanL_iff _ (fun _ hr => bb144_permVec_hzRow_mem t hr)
    (fun r hr => by
      rw [bb144Trans_symm_eq]
      exact bb144_permVec_hzRow_mem (-t) hr)

/-! ## 四、群结构：72 元

`bb144_sb.py` 按 $Z_{12}\times Z_6$ 取 72 个平移（`--perms all`），或只取两个生成元
（`--perms gens`）。两者在本模块里都是同一个 `bb144Trans t` 的实例——工具侧那一步
只是**挑了几个 `t`**，不涉及新的数学。 -/

/-- 平移置换的复合仍是平移置换（`bb144Trans s ≫ bb144Trans t = bb144Trans (s+t)`）。
这是"群恰为 72 个平移"那句的代数内容。 -/
theorem bb144Trans_trans (s t : GrossGroup) :
    (bb144Trans s).trans (bb144Trans t) = bb144Trans (s + t) := by
  apply Equiv.ext
  intro c
  simp only [Equiv.trans_apply, bb144Trans, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
             add_assoc]

end QECCertificates
