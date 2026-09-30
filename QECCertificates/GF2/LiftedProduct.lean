/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.HGP

/-!
# 提升乘积（lifted product）：群代数上的 HGP 与它对 HGP 的退化

**文献定义**（逐条注明出处）：

* Panteleev–Kalachev, *Asymptotically Good Quantum and Locally Testable Classical LDPC
  Codes*, STOC 2022（arXiv:2111.03654v2），**Appendix B, Eq. (13)**（PDF 第 48 页）：
  给定有限群 $G$（$|G| = \ell$）与群代数 $R = \mathbb{F}_2[G]$ 上的两个种子矩阵
  $A \in R^{m_A \times n_A}$、$B \in R^{m_B \times n_B}$，把每个元素 $r \in R$ 换成它的
  **正则表示的 $\ell \times \ell$ 矩阵**后再做 HGP 的分块张量：

  $$H_X = \bigl[\,\widehat A \otimes I_{m_B} \;\bigm|\; I_{m_A} \otimes \widehat B\,\bigr],\qquad
    H_Z = \bigl[\,I_{n_A} \otimes \widehat B^{\top} \;\bigm|\; \widehat A^{\top} \otimes I_{n_B}\,\bigr].$$

  这就是 **lifted product** $\mathrm{LP}(A, B)$；$m_A = n_A = m_B = n_B = 1$ 时它退化为
  **双块群代数码（2BGA）**——文献原话见 Lin–Pryadko, *Quantum two-block group algebra
  codes*, PRA **109**, 022407 (2024), **p. 6**（"2BGA codes are a degenerate case of LP
  codes with both matrices of dimension 1 x 1"）。

* 群代数元 $a = \sum_g a_g\, g$ 的两个正则表示（Lin–Pryadko, 同上, **p. 5, Eq. (36)**）：

  $$[L(a)]_{\sigma,\tau} = \sum_g a_g\,\delta_{g\tau,\sigma} = a(\sigma\tau^{-1}),\qquad
    [R(b)]_{\sigma,\tau} = \sum_g b_g\,\delta_{\tau g,\sigma} = b(\tau^{-1}\sigma).$$

  $L(a)$ 是"左乘 $x \mapsto a\,x$"的矩阵、$R(b)$ 是"右乘 $x \mapsto x\,b$"的矩阵；
  本模块写作 `leftMulMat a` / `rightMulMat b`。

## 本模块的贡献

1. **`leftMulMat_mul_rightMulMat`**：两个正则表示**逐元素对易**（$L(a)R(b) = R(b)L(a)$）。
   这是 LP 的 CSS 相容性的全部内容——HGP 的 `hgp_orthogonal` 用的是两个 Kronecker 因子的
   转置配对，而 LP 用的是"两个正则表示对易"。证明是两次置换重指标
   （$\rho \mapsto \tau^{-1}\rho$ 与 $\rho \mapsto \rho^{-1}\sigma$）加一次乘法交换。
2. **`lp_orthogonal`**：一般种子下 $H_X H_Z^{\top} = 0$（**结构定理**，对任意 $A, B$ 成立，
   无枚举）。它把 `hgp_orthogonal` 的"逐条目"论证抬到"每个分块是一对群代数元"的层面。
3. **2BGA（1 x 1 种子）**：`lp2HX` / `lp2HZ` 与 `lp2_orthogonal`——即文献 `LP[a, b]`。
4. **与 HGP 的关系**（`lpExpandR_liftConst` 等四条 + `lp_trivialGroup_eq_hgp`）：
   种子取**常值群代数元**（即来自 $\mathbb{F}_2 \subset \mathbb{F}_2[G]$，在这里写作
   `liftConst M`）时，$\widehat A = A \otimes I_\ell$，于是 LP 的校验矩阵按群指标
   **块对角**，每一块恰是 $\mathrm{HGP}(A, B^{\top})$：
   $$H^{\mathrm{LP}}_X\bigl((i,s),\gamma\bigr)\bigl((j,t),\gamma\bigr)
     = \bigl[\mathrm{HGP}(A,B^{\top})\bigr]_{(i,s)(j,t)}.$$
   取 $\ell = 1$（`Subsingleton G`）即得 `lp_trivialGroup_eq_hgp`：
   **平凡群上 LP 逐条目就是 HGP**。这与文献的说法一致（Panteleev–Kalachev, p. 8：
   "$R = \mathbb{F}_q$ 时 lifted product 等价于 product construction"，而 $\ell = 1$ 的
   群代数就是 $\mathbb{F}_q$ 本身）。

## 约定说明（与文献的镜像关系）

本文的 $H_X$ 把**左乘**矩阵给第一个种子、**右乘**矩阵给第二个（与 2BGA 论文 Eq. (36)
一致，锚点实例按此复现文献表格）；Panteleev–Kalachev 的 $\widehat A / \widehat B$ 把右正则
表示给了第一个种子。两套约定互为镜像：本文的 $\mathrm{LP}(A,B)$ 与 PK 的
$\mathrm{LP}(B,A)$ 只差**两个 qubit 块的交换**（一个置换），故码参数相同。

## 索引约定

行/列都是**乘积类型 + 群指标**（不拍平成 `Fin`），让结构定理零换标：

* $H_X$ 的行：`(Fin m_A x Fin m_B) x G`；$H_Z$ 的行：`(Fin n_A x Fin n_B) x G`；
* 两者的列都是 `((Fin n_A x Fin m_B) x G) (+) ((Fin m_A x Fin n_B) x G)`。

拍平到 `Fin`（实例化）交给 `Matrix.reindex` 做——见 `Codes/LPAnchor.lean`。
-/

namespace QECCertificates

open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## 一、群代数元的两个正则表示 -/

/-- 群代数元 `a : G → ZMod 2` 的**左乘矩阵**：线性算子 `x ↦ a * x` 在基 `G` 下的矩阵。

逐条目：`(leftMulMat a) σ τ = a (σ * τ⁻¹)`（Lin–Pryadko Eq. (36) 的 `L(a)`）。 -/
def leftMulMat (a : G → ZMod 2) : Matrix G G (ZMod 2) := fun σ τ => a (σ * τ⁻¹)

/-- 群代数元 `b : G → ZMod 2` 的**右乘矩阵**：线性算子 `x ↦ x * b` 在基 `G` 下的矩阵。

逐条目：`(rightMulMat b) σ τ = b (τ⁻¹ * σ)`（Lin–Pryadko Eq. (36) 的 `R(b)`）。 -/
def rightMulMat (b : G → ZMod 2) : Matrix G G (ZMod 2) := fun σ τ => b (τ⁻¹ * σ)

/-- 左平移置换 `x ↦ g * x`（重指标用）。 -/
def mulLeftEquiv (g : G) : G ≃ G where
  toFun x := g * x
  invFun x := g⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

/-- 反向右平移置换 `x ↦ x⁻¹ * g`（重指标用）。 -/
def invMulEquiv (g : G) : G ≃ G where
  toFun x := x⁻¹ * g
  invFun y := g * y⁻¹
  left_inv x := by simp
  right_inv y := by simp

/-- `σ * τ⁻¹ = 1 ↔ σ = τ`（常值种子的两条引理共用）。 -/
theorem mul_inv_eq_one_iff (σ τ : G) : σ * τ⁻¹ = 1 ↔ σ = τ := by
  constructor
  · intro h
    have h2 : σ * τ⁻¹ * τ = 1 * τ := by rw [h]
    rwa [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h2
  · intro h; rw [h, mul_inv_cancel]

/-- `τ⁻¹ * σ = 1 ↔ σ = τ`。 -/
theorem inv_mul_eq_one_iff (σ τ : G) : τ⁻¹ * σ = 1 ↔ σ = τ := by
  constructor
  · intro h
    have h2 : τ * (τ⁻¹ * σ) = τ * 1 := by rw [h]
    rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
  · intro h; rw [h, inv_mul_cancel]

/-- **两个正则表示逐元素对易**：`L(a) * R(b) = R(b) * L(a)`。

这是 LP 的 CSS 相容性的全部内容（`lp_orthogonal` 只调用它）。逐条目看两侧都等于
$\sum_\mu a(\sigma\mu^{-1}\tau^{-1})\,b(\mu)$：左边经 $\rho \mapsto \tau^{-1}\rho$
重指标、右边经 $\rho \mapsto \rho^{-1}\sigma$ 重指标，最后差一次乘法交换。 -/
theorem leftMulMat_mul_rightMulMat [Fintype G] (a b : G → ZMod 2) :
    leftMulMat a * rightMulMat b = rightMulMat b * leftMulMat a := by
  ext σ τ
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : (∑ ρ, leftMulMat a σ ρ * rightMulMat b ρ τ)
      = ∑ μ, a (σ * μ⁻¹ * τ⁻¹) * b μ := by
    refine Fintype.sum_equiv (mulLeftEquiv τ).symm
      (fun ρ => leftMulMat a σ ρ * rightMulMat b ρ τ)
      (fun μ => a (σ * μ⁻¹ * τ⁻¹) * b μ) ?_
    intro x
    have hx : ((mulLeftEquiv τ).symm) x = τ⁻¹ * x := rfl
    rw [hx]
    simp only [leftMulMat, rightMulMat]
    congr 1
    group
  have hR : (∑ ρ, rightMulMat b σ ρ * leftMulMat a ρ τ)
      = ∑ μ, a (σ * μ⁻¹ * τ⁻¹) * b μ := by
    refine Fintype.sum_equiv (invMulEquiv σ)
      (fun ρ => rightMulMat b σ ρ * leftMulMat a ρ τ)
      (fun μ => a (σ * μ⁻¹ * τ⁻¹) * b μ) ?_
    intro x
    have hx : (invMulEquiv σ) x = x⁻¹ * σ := rfl
    rw [hx]
    simp only [leftMulMat, rightMulMat]
    rw [mul_comm (b (x⁻¹ * σ)) (a (x * τ⁻¹))]
    congr 1
    group
  rw [hL, hR]

/-! ## 二、一般种子的 lifted product -/

/-- 种子矩阵的**右正则块展开**：`A` 的第 `(i,j)` 个群代数元换成它的左乘矩阵
（即 `A` 在右正则表示下的 $\ell \times \ell$ 块）。 -/
def lpExpandR {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2)) :
    Matrix (Fin mA × G) (Fin nA × G) (ZMod 2) :=
  fun x y => A x.1 y.1 (x.2 * y.2⁻¹)

/-- 种子矩阵的**左正则块展开**：`B` 的第 `(s,t)` 个群代数元换成它的右乘矩阵。 -/
def lpExpandL {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix (Fin mB × G) (Fin nB × G) (ZMod 2) :=
  fun x y => B x.1 y.1 (y.2⁻¹ * x.2)

theorem lpExpandR_apply {mA nA : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (i : Fin mA) (σ : G) (j : Fin nA) (τ : G) :
    lpExpandR A (i, σ) (j, τ) = leftMulMat (A i j) σ τ := rfl

theorem lpExpandL_apply {mB nB : ℕ} (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (s : Fin mB) (σ : G) (t : Fin nB) (τ : G) :
    lpExpandL B (s, σ) (t, τ) = rightMulMat (B s t) σ τ := rfl

/-- **lifted product 的 X 型校验**
$H_X = [\widehat A \otimes I_{m_B} \mid I_{m_A} \otimes \widehat B]$。

行 `((i,s),σ)`；左半列 `((j,s'),τ)` 取 $\widehat A\,(i,\sigma)(j,\tau)\cdot[s=s']$，
右半列 `((i',t'),τ)` 取 $[i=i']\cdot \widehat B\,(s,\sigma)(t',\tau)$。 -/
def lpHX {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix ((Fin mA × Fin mB) × G)
      (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun y => lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0))
    (fun y => (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2)) c

/-- **lifted product 的 Z 型校验**
$H_Z = [I_{n_A} \otimes \widehat B^{\top} \mid \widehat A^{\top} \otimes I_{n_B}]$。

行 `((j,t),σ)`；左半列 `((j',s'),τ)` 取 $[j=j']\cdot \widehat B\,(s',\tau)(t,\sigma)$
（即块转置后的 $\widehat B$），右半列 `((i',t'),τ)` 取
$\widehat A\,(i',\tau)(j,\sigma)\cdot[t=t']$。 -/
def lpHZ {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    Matrix ((Fin nA × Fin nB) × G)
      (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G)) (ZMod 2) :=
  fun x c => Sum.elim
    (fun y => (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2))
    (fun y => lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0)) c

/-- 四个分块的逐条目刻画（`rfl` 级）。 -/
theorem lpHX_inl {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX A B x (Sum.inl y)
      = lpExpandR A (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0) := rfl

theorem lpHX_inr {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX A B x (Sum.inr y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (y.1.2, y.2) := rfl

theorem lpHZ_inl {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ A B x (Sum.inl y)
      = (if x.1.1 = y.1.1 then 1 else 0) * lpExpandL B (y.1.2, y.2) (x.1.2, x.2) := rfl

theorem lpHZ_inr {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ A B x (Sum.inr y)
      = lpExpandR A (y.1.1, y.2) (x.1.1, x.2) * (if x.1.2 = y.1.2 then 1 else 0) := rfl

/-! ## 三、结构定理：lifted product 的 CSS 相容性 -/

/-- **lifted product 的 CSS 相容性**：$H_X H_Z^{\top} = 0$，对**任意**种子 $A, B$ 成立。

逐条目：左右两个分块各塌缩成一次求和（`Finset.sum_eq_single` 消掉 Kronecker 的
$\delta$ 因子），两个被加项分别是 $(L(A_{ij})\cdot R(B_{st}))(\sigma,\sigma')$ 与
$(R(B_{st})\cdot L(A_{ij}))(\sigma,\sigma')$，由 `leftMulMat_mul_rightMulMat` 相等，
在 $\mathbb{F}_2$ 上相加为零。**不含任何枚举**。 -/
theorem lp_orthogonal [Fintype G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    lpHX A B * (lpHZ A B).transpose = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    lpHX_inl, lpHX_inr, lpHZ_inl, lpHZ_inr]
  have hL : (∑ p : (Fin nA × Fin mB) × G,
        (lpExpandR A (x.1.1, x.2) (p.1.1, p.2) * (if x.1.2 = p.1.2 then 1 else 0)) *
          ((if y.1.1 = p.1.1 then 1 else 0) * lpExpandL B (p.1.2, p.2) (y.1.2, y.2)))
      = ∑ τ : G, leftMulMat (A x.1.1 y.1.1) x.2 τ * rightMulMat (B x.1.2 y.1.2) τ y.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin nA × Fin mB)))
      (f := fun q : Fin nA × Fin mB =>
        (lpExpandR A (x.1.1, x.2) (q.1, τ) * (if x.1.2 = q.2 then 1 else 0)) *
          ((if y.1.1 = q.1 then 1 else 0) * lpExpandL B (q.2, τ) (y.1.2, y.2)))
      (y.1.1, x.1.2) ?_ ?_).trans ?_
    · intro q _ hq
      by_cases h₁ : y.1.1 = q.1
      · by_cases h₂ : x.1.2 = q.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hq
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (y.1.1, x.1.2)) h
    · simp [lpExpandR_apply, lpExpandL_apply]
  have hR : (∑ q : (Fin mA × Fin nB) × G,
        ((if x.1.1 = q.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (q.1.2, q.2)) *
          (lpExpandR A (q.1.1, q.2) (y.1.1, y.2) * (if y.1.2 = q.1.2 then 1 else 0)))
      = ∑ τ : G, rightMulMat (B x.1.2 y.1.2) x.2 τ * leftMulMat (A x.1.1 y.1.1) τ y.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin mA × Fin nB)))
      (f := fun q : Fin mA × Fin nB =>
        ((if x.1.1 = q.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (q.2, τ)) *
          (lpExpandR A (q.1, τ) (y.1.1, y.2) * (if y.1.2 = q.2 then 1 else 0)))
      (x.1.1, y.1.2) ?_ ?_).trans ?_
    · intro q _ hq
      by_cases h₁ : x.1.1 = q.1
      · by_cases h₂ : y.1.2 = q.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hq
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (x.1.1, y.1.2)) h
    · simp [lpExpandR_apply, lpExpandL_apply]
  rw [hL, hR, ← Matrix.mul_apply, ← Matrix.mul_apply, leftMulMat_mul_rightMulMat]
  exact CharTwo.add_self_eq_zero _

/-! ## 四、2BGA：1 x 1 种子的 lifted product（文献 `LP[a, b]`） -/

/-- **2BGA 的 X 型校验** $H_X = [L(a) \mid R(b)]$（Lin–Pryadko Eq. (16)）。 -/
def lp2HX (a b : G → ZMod 2) : Matrix G (G ⊕ G) (ZMod 2) :=
  fun σ c => Sum.elim (fun τ => leftMulMat a σ τ) (fun τ => rightMulMat b σ τ) c

/-- **2BGA 的 Z 型校验** $H_Z = [R(b)^{\top} \mid L(a)^{\top}]$（Lin–Pryadko Eq. (16)：
$H_Z^{\top} = \binom{B}{-A}$，在 $\mathbb{F}_2$ 上负号消失）。 -/
def lp2HZ (a b : G → ZMod 2) : Matrix G (G ⊕ G) (ZMod 2) :=
  fun σ c => Sum.elim (fun τ => rightMulMat b τ σ) (fun τ => leftMulMat a τ σ) c

theorem lp2HX_inl (a b : G → ZMod 2) (σ τ : G) :
    lp2HX a b σ (Sum.inl τ) = leftMulMat a σ τ := rfl

theorem lp2HX_inr (a b : G → ZMod 2) (σ τ : G) :
    lp2HX a b σ (Sum.inr τ) = rightMulMat b σ τ := rfl

theorem lp2HZ_inl (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inl τ) = rightMulMat b τ σ := rfl

theorem lp2HZ_inr (a b : G → ZMod 2) (σ τ : G) :
    lp2HZ a b σ (Sum.inr τ) = leftMulMat a τ σ := rfl

/-- **2BGA 的 CSS 相容性**：$H_X H_Z^{\top} = L(a)R(b) + R(b)L(a) = 0$。 -/
theorem lp2_orthogonal [Fintype G] (a b : G → ZMod 2) :
    lp2HX a b * (lp2HZ a b).transpose = 0 := by
  ext σ σ'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    lp2HX_inl, lp2HX_inr, lp2HZ_inl, lp2HZ_inr]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, leftMulMat_mul_rightMulMat]
  exact CharTwo.add_self_eq_zero _

/-! ## 五、长度与维数的可复用引理 -/

omit [Group G] in
/-- **LP 的量子比特数**：$\ell\,(n_A m_B + m_A n_B)$。 -/
theorem lp_qubit_count [Fintype G] {mA nA mB nB : ℕ} :
    Fintype.card (((Fin nA × Fin mB) × G) ⊕ ((Fin mA × Fin nB) × G))
      = (nA * mB + mA * nB) * Fintype.card G := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  ring

omit [Group G] in
/-- LP 的 X 型校验行数：$m_A m_B \ell$。 -/
theorem lp_row_count_X [Fintype G] {mA mB : ℕ} :
    Fintype.card ((Fin mA × Fin mB) × G) = mA * mB * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

omit [Group G] in
/-- LP 的 Z 型校验行数：$n_A n_B \ell$。 -/
theorem lp_row_count_Z [Fintype G] {nA nB : ℕ} :
    Fintype.card ((Fin nA × Fin nB) × G) = nA * nB * Fintype.card G := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

omit [Group G] in
/-- **2BGA 的码长**：$n = 2\ell$（两个 $\ell$ 块的直和）。 -/
theorem lp2_qubit_count [Fintype G] : Fintype.card (G ⊕ G) = 2 * Fintype.card G := by
  rw [Fintype.card_sum]
  ring

/-! ## 六、与 HGP 的关系：常值种子 ⟹ 每一个群纤维都是 HGP -/

/-- 把 $\mathbb{F}_2$ 上的矩阵**提升**为常值群代数元矩阵（即 $\mathbb{F}_2 \subset \mathbb{F}_2[G]$
的像：只支撑在单位元上）。 -/
def liftConst [DecidableEq G] {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix (Fin m) (Fin n) (G → ZMod 2) :=
  fun i j g => M i j * (if g = 1 then 1 else 0)

/-- 常值种子下右正则块展开退化为 $A \otimes I_\ell$：
$\widehat A\,(i,\sigma)(j,\tau) = A_{ij}\cdot[\sigma = \tau]$。 -/
theorem lpExpandR_liftConst [DecidableEq G] {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (i : Fin m) (σ : G) (j : Fin n) (τ : G) :
    lpExpandR (liftConst A) (i, σ) (j, τ) = A i j * (if σ = τ then 1 else 0) := by
  simp only [lpExpandR, liftConst]
  by_cases h : σ = τ
  · rw [ite_eq_left ((mul_inv_eq_one_iff σ τ).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((mul_inv_eq_one_iff σ τ).mp hc)), ite_eq_right h]

/-- 常值种子下左正则块展开退化为 $B \otimes I_\ell$。 -/
theorem lpExpandL_liftConst [DecidableEq G] {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (s : Fin m) (σ : G) (t : Fin n) (τ : G) :
    lpExpandL (liftConst B) (s, σ) (t, τ) = B s t * (if σ = τ then 1 else 0) := by
  simp only [lpExpandL, liftConst]
  by_cases h : σ = τ
  · rw [ite_eq_left ((inv_mul_eq_one_iff σ τ).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((inv_mul_eq_one_iff σ τ).mp hc)), ite_eq_right h]

/-- **LP 的 X 型校验在常值种子下按群指标块对角，每块是 HGP**（左块）。 -/
theorem lpHX_liftConst_inl [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHX A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHX_inl, lpExpandR_liftConst, hgpHX_inl]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h]

theorem lpHX_liftConst_inr [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHX A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHX_inr, lpExpandL_liftConst, hgpHX_inr, Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h]

theorem lpHZ_liftConst_inl [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHZ A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHZ_inl, lpExpandL_liftConst, hgpHZ_inl, Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem lpHZ_liftConst_inr [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHZ A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHZ_inr, lpExpandR_liftConst, hgpHZ_inr]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, Ne.symm h]

/-- **平凡群（$\ell = 1$）时 LP 逐条目就是 HGP**（$X$ 侧）。

$\ell = 1$ 时群指标只有一个元素（`Subsingleton G`），$\delta_{\sigma\tau}$ 恒为 $1$，
于是 `lpHX_liftConst_inl` 里的因子消失。这正是文献所说的"$R = \mathbb{F}_q$ 时 lifted
product 等价于 product construction"（Panteleev–Kalachev, p. 8）。 -/
theorem lp_trivialGroup_eq_hgp [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (i : Fin mA) (s : Fin mB) (j : Fin nA) (t : Fin mB) :
    lpHX (liftConst A) (liftConst B) ((i, s), (1 : G)) (Sum.inl ((j, t), (1 : G)))
      = hgpHX A B.transpose (i, s) (Sum.inl (j, t)) := by
  rw [lpHX_liftConst_inl, ite_eq_left rfl, mul_one]

/-- **平凡群（$\ell = 1$）时 LP 逐条目就是 HGP**（$Z$ 侧）。 -/
theorem lp_trivialGroup_eq_hgp_Z [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (j : Fin nA) (t : Fin nB) (j' : Fin nA) (s : Fin mB) :
    lpHZ (liftConst A) (liftConst B) ((j, t), (1 : G)) (Sum.inl ((j', s), (1 : G)))
      = hgpHZ A B.transpose (j, t) (Sum.inl (j', s)) := by
  rw [lpHZ_liftConst_inl, ite_eq_left rfl, mul_one]

end QECCertificates
