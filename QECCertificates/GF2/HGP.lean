/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.Basic

/-!
# 超图积（HGP）校验矩阵的张量分解（ 第一片）

Tillich–Zémor 超图积把两个经典码 $C_1, C_2$（校验矩阵 $H_1 : r_1 \times n_1$、
$H_2 : r_2 \times n_2$）粘成一个量子码，量子比特数为 $n_1 n_2 + r_1 r_2$，
两类校验为分块张量形式：

$$H_X = [\,H_1 \otimes I_{n_2} \;\middle|\; I_{r_1} \otimes H_2^\top\,],\qquad
H_Z = [\,I_{n_1} \otimes H_2 \;\middle|\; H_1^\top \otimes I_{r_2}\,].$$

本模块给出这一构造的**逐条目定义**（`hgpHX` / `hgpHZ`）与第一条结构定理：

* `hgp_orthogonal`：$H_X H_Z^\top = 0$——CSS 相容条件对**任意**输入 $H_1, H_2$
  成立，证明是纯代数的（两个分块各贡献一个 $H_1 \otimes H_2^\top$，
  在 GF(2) 上相加为零），**不含任何枚举**。

这是 （张量分解归约）的第一片；"转置码下界"（$d \ge \min(d_1, d_2)$ 的
张量论证）与秩/维数的张量公式仍 ⬜。实例锚点（3-圈 → $3\times3$ 环面码
$[[18,2,3]]$）见 `Codes/HGPAnchor.lean`。

## 索引约定

* 行、列都是**乘积 / 直和类型**（不拍平成 `Fin`），让结构定理零换标：
  `hgpHX` 的行是 `Fin r₁ × Fin n₂`，`hgpHZ` 的行是 `Fin n₁ × Fin r₂`，
  两者共享列空间 `(Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)`。
* 拍平到 `Fin`（锚点实例化）交给 `Matrix.reindex` 做。
-/

namespace QECCertificates

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-! ## 构造 -/

/-- **HGP 的 X 型校验** $H_X = [H_1 \otimes I_{n_2} \mid I_{r_1} \otimes H_2^\top]$。

行 `(i, j) : r₁ × n₂`；列左半 `(a, b) : n₁ × n₂` 上取 $H_1\, i\,a \cdot [j = b]$，
右半 `(s, t) : r₁ × r₂` 上取 $[i = s] \cdot H_2\, t\, j$（即 $H_2^\top$ 的 $(j, t)$ 元）。 -/
def hgpHX (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    Matrix (Fin r₁ × Fin n₂) ((Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun ab => H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0))
    (fun st => (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) c

/-- **HGP 的 Z 型校验** $H_Z = [I_{n_1} \otimes H_2 \mid H_1^\top \otimes I_{r_2}]$。

行 `(a, d) : n₁ × r₂`；列左半上取 $[a = a'] \cdot H_2\, d\, b$，
右半上取 $H_1\, s\, a \cdot [d = t]$。 -/
def hgpHZ (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    Matrix (Fin n₁ × Fin r₂) ((Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun ab => (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2)
    (fun st => H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0)) c

/-- 四个分块的逐条目刻画（`rfl` 级）。 -/
theorem hgpHX_inl (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin r₁ × Fin n₂) (ab : Fin n₁ × Fin n₂) :
    hgpHX H₁ H₂ x (Sum.inl ab) = H₁ x.1 ab.1 * (if x.2 = ab.2 then 1 else 0) := rfl

theorem hgpHX_inr (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin r₁ × Fin n₂) (st : Fin r₁ × Fin r₂) :
    hgpHX H₁ H₂ x (Sum.inr st) = (if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2 := rfl

theorem hgpHZ_inl (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (ab : Fin n₁ × Fin n₂) :
    hgpHZ H₁ H₂ x (Sum.inl ab) = (if x.1 = ab.1 then 1 else 0) * H₂ x.2 ab.2 := rfl

theorem hgpHZ_inr (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (x : Fin n₁ × Fin r₂) (st : Fin r₁ × Fin r₂) :
    hgpHZ H₁ H₂ x (Sum.inr st) = H₁ st.1 x.1 * (if x.2 = st.2 then 1 else 0) := rfl

/-! ## 结构定理：CSS 相容 -/

/-- **HGP 的 CSS 相容性（结构定理）**：$H_X H_Z^\top = 0$，对任意 $H_1, H_2$ 成立。

两个分块的贡献分别是 $(H_1 \otimes I)(I \otimes H_2)^\top = H_1 \otimes H_2^\top$
与 $(I \otimes H_2^\top)(H_1^\top \otimes I)^\top = H_1 \otimes H_2^\top$——
同一矩阵加自身，在 GF(2) 上为零。证明里的两个 `Finset.sum_eq_single`
就是这条张量等式在逐条目层面的形态：每个乘积 $H_1\, i\, a \cdot H_2\, d\, j$
恰在左半由 $(a, j)$、右半由 $(i, d)$ 各贡献一次。 -/
theorem hgp_orthogonal (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    hgpHX H₁ H₂ * (hgpHZ H₁ H₂).transpose = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    hgpHX_inl, hgpHX_inr, hgpHZ_inl, hgpHZ_inr]
  -- 左半：单点 (y.1, x.2)
  have keyL : (∑ p : Fin n₁ × Fin n₂,
        (H₁ x.1 p.1 * (if x.2 = p.2 then 1 else 0)) * ((if y.1 = p.1 then 1 else 0) * H₂ y.2 p.2))
      = H₁ x.1 y.1 * H₂ y.2 x.2 := by
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n₁ × Fin n₂)))
      (f := fun p => (H₁ x.1 p.1 * (if x.2 = p.2 then 1 else 0)) *
        ((if y.1 = p.1 then 1 else 0) * H₂ y.2 p.2)) (y.1, x.2) ?_ ?_).trans ?_
    · intro p _ hp
      by_cases h₁ : y.1 = p.1
      · by_cases h₂ : x.2 = p.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hp
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (y.1, x.2)) h
    · simp
  -- 右半：单点 (x.1, y.2)
  have keyR : (∑ st : Fin r₁ × Fin r₂,
        ((if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) * (H₁ st.1 y.1 * (if y.2 = st.2 then 1 else 0)))
      = H₂ y.2 x.2 * H₁ x.1 y.1 := by
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin r₁ × Fin r₂)))
      (f := fun st => ((if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) *
        (H₁ st.1 y.1 * (if y.2 = st.2 then 1 else 0))) (x.1, y.2) ?_ ?_).trans ?_
    · intro st _ hst
      by_cases h₁ : x.1 = st.1
      · by_cases h₂ : y.2 = st.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hst
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (x.1, y.2)) h
    · simp
  rw [keyL, keyR]
  have hcomm : H₂ y.2 x.2 * H₁ x.1 y.1 = H₁ x.1 y.1 * H₂ y.2 x.2 := mul_comm _ _
  rw [hcomm]
  exact CharTwo.add_self_eq_zero _

end QECCertificates
