/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB18Anchor
import QECCertificates.GF2.RankEchelon

/-!
# 折叠横截门（fold-transversal gates）：BB $[[18,4,4]]$ 的内核实例

覆盖面缺口在这一侧：现有交付物覆盖**码侧**（维数、距离、分离条件），
本模块补上**门侧**——把"容错逻辑门"做成内核机器检验的实例。

来源文献：J. N. Eberhardt, V. Steffan,
*Logical Operators and Fold-Transversal Gates of Bivariate Bicycle Codes*,
IEEE Trans. Inf. Theory **71**, 1140–1152 (2025)（arXiv:2407.03973）。
本模块用到的事实与其出处（页码/编号按 arXiv v1 排版）：

* **BB 码是群代数码**：`C(c,d)` 的比特是 $\mathbb Z_\ell\times\mathbb Z_m$ 的
  "水平/垂直"两份拷贝，$X_h=\prod_{g\in\operatorname{supp}c}X_{(hg^{-1})_h}
  \prod_{g\in\operatorname{supp}d}X_{(hg^{-1})_v}$，$Z_h$ 对偶（§3.1 式 (5)，p. 7；§4.1，p. 10）。
* **自同构 → swap 型门**：$G$ 中元素 $t$ 的乘法给出码自同构，得到门
  $\mathrm{SWAP}_\phi=\prod_g(\mathrm{SWAP}_{g_h,\phi(g_h)}\mathrm{SWAP}_{g_v,\phi(g_v)})$，
  且它总是逻辑门（§3.3 Theorem 3.2，p. 9；§4.3"we always obtain the swap-gates
  $\mathrm{SWAP}_x,\mathrm{SWAP}_y$"，p. 13）。
* **标准 ZX-对偶 → Hadamard 型门**：$\tau_0$ 交换 $X$-校验与 $Z$-校验，在比特上把
  $g_h$ 送到 $(g^{-1})_v$、$g_v$ 送到 $(g^{-1})_h$（§3.2 `σ` 与 `τ_0 t`，p. 8；
  §3.4 Theorem 3.3，p. 9；§4.3"another fold-transversal gate arises from the
  ZX-duality $\tau_0$"，p. 13）。
* **相位型（CZ）门**：需要一个群自同构 $\omega$ 满足 $\omega^2=\mathrm{id}$ 且
  **$\omega(c)=d$**（在 $R=\mathbb F_2[G]$ 里），此时
  $\tau_0\omega(g_h)=(\omega(g)^{-1})_h$、$\tau_0\omega(g_v)=(\omega(g)^{-1})_v$，
  对应的 CZ 门是逻辑门（§3.5 Theorem 3.4，pp. 9–10）。
  论文对 BB 码给出的**充分条件**是 Definition 4.9 的 `symmetric`
  （$\ell=m$ 且 $c(x,y)=d(y,x)$，p. 13），此时取 $\omega$ 为换轴 $x\leftrightarrow y$ 即可。

  **本条对 BB18 的适用性需要点明（不属于论文原话）**：BB18 **不满足** Definition 4.9
  （$d(y,x)=1+y^2+x^2=d\neq c$），但它满足 §3.5 的**一般前提**——取
  $\omega=(\text{换轴})\circ\iota$（$\iota:g\mapsto g^{-1}$，同 §3.2）时
  $\omega^2=\mathrm{id}$、$\omega(x)=y^{-1}$、$\omega(y)=x^{-1}$ 且
  $\omega(c)=1+y^{-1}+x^{-1}=1+y^2+x^2=d$。故 **§3.5 Theorem 3.4 覆盖 BB18，
  而 §4.3 那句（对 symmetric 码）不直接覆盖**。
  下面 `bb18FoldCz` 就是 $\tau_0\omega$ 在物理比特上的诱导置换；它是**码自同构**
  这件事由 `bb18_foldCz_rows_x`/`bb18_foldCz_rows_z` 内核复核——
  该结论独立于上述代数细节的对错。

## 本模块的 BB18 参数（从 `Codes/BB18Anchor.lean` 的矩阵逐条重算）

$\ell=m=3$，$c=1+x+y$，$d=1+x^2+y^2$，$H_X=[A\mid B]$、$H_Z=[B^{tr}\mid A^{tr}]$
（$A=\rho(c)$、$B=\rho(d)$，§4.1 Remark 4.2，p. 11）。本码有 $H_X=H_Z$
（因 $d=\iota(c)$，$\iota$ 是 §3.2 的反极点 $g\mapsto g^{-1}$），故它同时是
"自对偶"的 CSS 码——下文每条陈述都按**两侧**校验列表写，不靠这个巧合。

## 三条机器检验的断言

1. `bb18_foldCz_rows` 一族：**折叠置换把每条校验行仍映为校验行**（自同构 / ZX-对偶）；
   推论 `…_preserves_spanL` 把它升到行空间层面。
2. `bb18_foldCz_log0` 一族：**诱导的逻辑作用**——四个显式逻辑算符基在折叠下的像，
   连同把像拉回逻辑基的**显式稳定子修正**（逐条 `by decide`）。
3. `bb18_foldCz_logical` 一族：**折叠把逻辑算符映成同重量的逻辑算符**（距离不降的结构性内容）。

第 3 条另有一条**一般形态**（`permVec_preserves_undetectable`，任意码、任意比特置换；
BB18 专用版 `bb18Log_permVec_undetectable`）：核成员关系与行空间成员关系在置换下的
不变性（`inKerB_permVec` / `permVec_mem_spanL_iff`，基础是点积的重标号引理
`dotProduct_permVec`）把"像仍是不可探测的**非平凡**算符"做成结构定理，
四条 `bb18_*_undetectable` 是它的实例。有了这条结构定理，"像仍是不可探测的非平凡算符"
不再是一项未做的事，故下面"未做的部分"不列它。

**可信基**：全程只有 `by decide`（内核归约），零 `sorry`、零自定义公理、零 `native_decide`。

## 第二路对账

`tools/check_fold_transversal.py` 用**另一条算路**（纯 Python 位运算、不做行消元、
不共用本模块任何代码）把上面每一条断言重算了一遍：四个置换的像、四个基算符的
核成员/非行空间成员/重量、配对矩阵、模行空间的无关性、16 条折叠作用、
以及折叠像的不可探测性与重量——共 90 条断言，全部一致。
两个校验矩阵由该脚本**从 `Codes/BB18Anchor.lean` 现读**（单一数据源，避免两处漂移）。

## 未做的部分（如实标注）

* **`#print axioms` 实测输出**：门侧 56 条断言已进根模块的审计区（含一般结构引理与
  断言 3 的一般形态），全量构建实测均恰为
  `[propext, Classical.choice, Quot.sound]`。
* **`SWAP_x`/`SWAP_y` 生成的群**：文献对 [[98,8,12]] 给出 $C_2\times\mathrm{Sp}_2(\mathbb F_{2^3})$；
  本模块只做到"门是逻辑门 + 它实现的具体逻辑置换"，没有算生成群的阶。
-/

namespace QECCertificates

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、物理比特置换对向量的搬运 -/

/-- 置换 `π` 对 GF(2) 向量的**推进**：`(permVec π v) i = v (π⁻¹ i)`。

即把支撑集整体搬到 `π` 的像上。折叠横截门在算符层面的作用就是这个搬运：
单比特门（H、S）只乘相位，`SWAP`/`CZ` 把支撑沿置换的轨道搬运
（§3.3–§3.5）。 -/
def permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) : Vec n := fun i => v (π.symm i)

@[simp] lemma permVec_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) (i : Fin n) :
    permVec π v i = v (π.symm i) := rfl

/-- 支撑集按 `π` 搬运到像上。 -/
theorem support_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    support (permVec π v) = (support v).image π := by
  ext i
  simp only [mem_support, Finset.mem_image]
  constructor
  · intro h
    exact ⟨π.symm i, h, π.apply_symm_apply i⟩
  · rintro ⟨j, hj, rfl⟩
    simpa [permVec] using hj

/-- **重量保持**：置换不改变 Hamming 重量。

这是"折叠不降低有效距离"的第一半：任何算符的重量在折叠前后**逐字相同**，
故折叠不可能把重码字变轻。 -/
theorem hammingNorm_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    hammingNorm (permVec π v) = hammingNorm v := by
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm, support_permVec]
  exact Finset.card_image_of_injective _ π.injective

/-- **行空间保持**：若 `π` 把行列表 `L` 的每一行仍留在 `L` 的行空间里，
则它保持整个行空间。

这就是"置换是码的自同构"的**行空间形态**：稳定子生成元映到生成元的组合
⟹ 整个稳定子群映到自身。证明沿 `Submodule.span_induction` 走
（`permVec` 逐分量线性，三条线性性都是逐点 `rfl`）。 -/
theorem permVec_mem_spanL {n : ℕ} (π : Equiv.Perm (Fin n)) {L : List (Vec n)}
    (h : ∀ r ∈ L, permVec π r ∈ spanL L) {v : Vec n} (hv : v ∈ spanL L) :
    permVec π v ∈ spanL L := by
  refine Submodule.span_induction (p := fun x _ => permVec π x ∈ spanL L) ?_ ?_ ?_ ?_ hv
  · intro r hr
    exact h r hr
  · have h0 : permVec π (0 : Vec n) = 0 := by funext i; simp [permVec]
    rw [h0]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    have hadd : permVec π (x + y) = permVec π x + permVec π y := by
      funext i; simp [permVec, Pi.add_apply]
    rw [hadd]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    have hsmul : permVec π (c • x) = c • permVec π x := by
      funext i; simp [permVec, Pi.smul_apply]
    rw [hsmul]
    exact Submodule.smul_mem _ _ hx

/-! ### 点积、核与行空间在置换下的不变性

折叠横截门在算符层面的作用是**支撑搬运** `permVec π`。要证"它把不可探测算符映成
不可探测算符"，需要两件事在置换下不变：**核成员关系**（与校验行逐行配对为零）与
**行空间成员关系**（不在稳定子群里）。前者由点积的置换不变性给出，后者由
`permVec_mem_spanL` 的双向补全给出——两条都是对**任意**置换陈述的结构定理，
不依赖任何具体的码或 `decide`。 -/

/-- `permVec` 是 `Vec n` 上的群作用：先用 `π` 搬运、再用 `π⁻¹` 搬回，等于没动。 -/
@[simp] lemma permVec_symm_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    permVec π.symm (permVec π v) = v := by
  funext i; simp [permVec]

/-- 上一条的对偶方向。 -/
@[simp] lemma permVec_permVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    permVec π (permVec π.symm v) = v := by
  funext i; simp [permVec]

/-- **点积在置换下的不变性**：同时搬运两个因子不改变 GF(2) 点积。

`⬝ᵥ` 是逐分量乘积之和，而置换只是把求和指标重标号（`Equiv.sum_comp`），
故这是"求和与指标命名无关"的直接推论。它也是核成员在置换下不变的**全部代数内容**：
`x` 与校验行 `r` 的配对，等于搬运后的 `x` 与搬运后的 `r` 的配对。 -/
theorem dotProduct_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v w : Vec n) :
    (permVec π v) ⬝ᵥ (permVec π w) = v ⬝ᵥ w := by
  rw [dotProduct, dotProduct]
  simp only [permVec_apply]
  exact Equiv.sum_comp π.symm (fun j => v j * w j)

/-- **点积的重标号形态（单侧）**：只搬运右因子，等价于用 `π⁻¹` 搬运左因子。

核成员判定 `inKerB M x` 是"`M` 的每一行与 `x` 配对为零"；把 `x` 换成本模块关心的
`permVec π x` 之后，配对变成 `M i ⬝ᵥ permVec π x = (permVec π⁻¹ (M i)) ⬝ᵥ x`，
于是"像仍在核里"归约为"`π⁻¹` 把校验行仍映成校验行"。 -/
theorem dotProduct_permVec_left {n : ℕ} (π : Equiv.Perm (Fin n)) (a b : Vec n) :
    a ⬝ᵥ (permVec π b) = (permVec π.symm a) ⬝ᵥ b := by
  rw [dotProduct, dotProduct]
  simp only [permVec_apply, Equiv.symm_symm]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp π (fun i => a i * b (π.symm i))).symm

/-- **行空间在置换下的不变性（双向）**：若行列表 `L` 在 `π` 与其逆下都不变，
则 `π` 保持 `L` 的行空间。

一个方向（`v ∈ spanL L → permVec π v ∈ spanL L`）就是 `permVec_mem_spanL`；
反方向对 `π⁻¹` 用同一命题、再用 `permVec π.symm (permVec π v) = v` 收回。
两个方向都要：断言 3 的"像仍是**非平凡**算符"用的正是反方向——若像落在行空间里，
原像也落在行空间里，与"原像非平凡"矛盾。 -/
theorem permVec_mem_spanL_iff {n : ℕ} (π : Equiv.Perm (Fin n)) {L : List (Vec n)}
    (h : ∀ r ∈ L, permVec π r ∈ L) (h' : ∀ r ∈ L, permVec π.symm r ∈ L) {v : Vec n} :
    permVec π v ∈ spanL L ↔ v ∈ spanL L := by
  constructor
  · intro hv
    have hmem : permVec π.symm (permVec π v) ∈ spanL L :=
      permVec_mem_spanL π.symm (fun r hr => subset_spanL (h' r hr)) hv
    rwa [permVec_symm_permVec] at hmem
  · intro hv
    exact permVec_mem_spanL π (fun r hr => subset_spanL (h r hr)) hv

/-- **核成员在置换下的不变性**：若 `π⁻¹` 把 `M` 的每一行仍映为 `M` 的某一行，
则 `π` 把 `M` 的核映到自身。

证明是 `dotProduct_permVec_left` 加一句重标号：`M i ⬝ᵥ permVec π x` 等于
`permVec π⁻¹ (M i) ⬝ᵥ x`，而后者（按假设）是某一行 `M j` 与 `x` 的配对，已知为零。 -/
theorem inKerB_permVec {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (π : Equiv.Perm (Fin n)) (h : ∀ i, permVec π.symm (M i) ∈ List.ofFn M)
    {x : Vec n} (hx : inKerB M x = true) : inKerB M (permVec π x) = true := by
  unfold inKerB at hx ⊢
  rw [List.all_eq_true] at hx ⊢
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (h i)
  have hleft : (M i) ⬝ᵥ (permVec π x) = (M j) ⬝ᵥ x := by
    rw [dotProduct_permVec_left, ← hj]
  rw [hleft]
  exact hx _ (by rw [List.mem_ofFn]; exact ⟨j, rfl⟩)

/-- **断言 3 的一般形态（任意码、任意置换）**：设比特置换 `π` 把校验矩阵 `M` 的行
（经 `π⁻¹`）与行列表 `L`（连同 `π` 与其逆）都映到自身，则它把"相对 `M` 不可探测、
且不在 `L` 的行空间里"的算符映成**同重量、同性质**的算符。

这就是"横截门不降低有效距离"的一般内容：不可探测性由 `inKerB_permVec` 给出、
非平凡性（不在稳定子群里）由 `permVec_mem_spanL_iff` 的反方向给出、重量由
`hammingNorm_permVec` 给出——三条都**不是**逐算符计算。 -/
theorem permVec_preserves_undetectable {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (L : List (Vec n)) (π : Equiv.Perm (Fin n))
    (hM : ∀ i, permVec π.symm (M i) ∈ List.ofFn M)
    (hL : ∀ r ∈ L, permVec π r ∈ L) (hL' : ∀ r ∈ L, permVec π.symm r ∈ L)
    {x : Vec n} (hk : inKerB M x = true) (hs : inSpanEch L x = false) :
    inKerB M (permVec π x) = true ∧ inSpanEch L (permVec π x) = false ∧
      hammingNorm (permVec π x) = hammingNorm x :=
  ⟨inKerB_permVec M π hM hk,
   by
     rw [inSpanEch_eq_false_iff] at hs ⊢
     exact fun hcon => hs ((permVec_mem_spanL_iff π hL hL').mp hcon),
   hammingNorm_permVec π x⟩

/-! ## 二、BB18 的四个折叠置换

比特编号约定：`q < 9` 是 $h$ 块（群元素索引 `3i+j` 即 $x^iy^j$），`q ≥ 9` 是
$v$ 块（同一索引）。四个置换都是 `Fin 18` 上的具体置换，双向映射都显式给出，
故 `decide` 可直接归约（不用 `Function.invFun`，那会挡住归约）。 -/

/-- **相位型（CZ）折叠 $\tau_0\omega$**：$\omega(x)=y^{-1},\omega(y)=x^{-1}$，
在每块内把 $x^iy^j$ 送到 $x^jy^i$——即格点沿对角线的镜像（§3.5 p. 9、§4.3 p. 13）。
它是对合，固定点 $i=j$（§3.5 的 $G_0$；其余比特两两成对，各配一个 CZ）。

对 BB18：$c=1+x+y$、$d=1+x^2+y^2$，而 $\omega(c)=1+y^{-1}+x^{-1}=1+y^2+x^2=d$
满足 §3.5 的前提（$\omega^2=\mathrm{id}$ 直接可验）。 -/
def bb18FoldCz : Equiv.Perm (Fin 18) where
  toFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 12, 15, 10, 13, 16, 11, 14, 17]
  invFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 12, 15, 10, 13, 16, 11, 14, 17]
  left_inv := by decide
  right_inv := by decide

/-- **Hadamard 型折叠 $\tau_0$**：$g_h\mapsto(g^{-1})_v$、$g_v\mapsto(g^{-1})_h$
（§3.2 p. 8、§3.4 Theorem 3.3 p. 9）。无固定比特：9 对 $(g_h,(g^{-1})_v)$。 -/
def bb18FoldH : Equiv.Perm (Fin 18) where
  toFun := ![9, 11, 10, 15, 17, 16, 12, 14, 13, 0, 2, 1, 6, 8, 7, 3, 5, 4]
  invFun := ![9, 11, 10, 15, 17, 16, 12, 14, 13, 0, 2, 1, 6, 8, 7, 3, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- **swap 型门 $\mathrm{SWAP}_x$**：$G$ 上乘以 $x$（§3.3 Theorem 3.2 p. 9、
§4.3 p. 13）。三阶元，6 个 3-循环。 -/
def bb18ShiftX : Equiv.Perm (Fin 18) where
  toFun := ![3, 4, 5, 6, 7, 8, 0, 1, 2, 12, 13, 14, 15, 16, 17, 9, 10, 11]
  invFun := ![6, 7, 8, 0, 1, 2, 3, 4, 5, 15, 16, 17, 9, 10, 11, 12, 13, 14]
  left_inv := by decide
  right_inv := by decide

/-- **swap 型门 $\mathrm{SWAP}_y$**：$G$ 上乘以 $y$。 -/
def bb18ShiftY : Equiv.Perm (Fin 18) where
  toFun := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 16, 17, 15]
  invFun := ![2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13, 17, 15, 16]
  left_inv := by decide
  right_inv := by decide

/-! ## 三、断言 1：折叠置换是码的自同构（把校验生成元映到生成元）

用"行列表的自映射"而不是 `inSpanB`：对 $n=18$ 的宽行列表，前者是逐元素比较、
后者内部要跑行消元（本库实测差一个量级）。行列表自映射**强于**行空间保持，
正是任务要求的"把每个稳定子生成元映到同一个稳定子群的一个生成元"。 -/

/-- 字符串列上"逐行映到目标列表"的成员提取（`List.all` 形态，`by decide` 可归约）。 -/
theorem mem_of_list_all {α : Type*} [DecidableEq α] {f : α → α} {L M : List α} {r : α}
    (h : L.all (fun u => decide (f u ∈ M)) = true) (hr : r ∈ L) : f r ∈ M := by
  rw [List.all_eq_true] at h
  simpa using h r hr

/-- 自映射升级到行空间层面。 -/
theorem mem_spanL_of_list_all {n : ℕ} {f : Vec n → Vec n} {L M : List (Vec n)} {r : Vec n}
    (h : L.all (fun u => decide (f u ∈ M)) = true) (hr : r ∈ L) : f r ∈ spanL M :=
  subset_spanL (mem_of_list_all h hr)

/-- 由"行列表在 `π⁻¹` 下不变"给出 `inKerB_permVec` 所需的假设（`List.all` 形态 ⟹ `∀ i` 形态）。

行集不变的 `List.all` 表述（`by decide` 可归约）与一般引理所需的 `∀ i` 表述之间的桥。 -/
lemma kerRows_of_list_all {n k : ℕ} {M : Matrix (Fin k) (Fin n) (ZMod 2)}
    {L : List (Vec n)} {π : Equiv.Perm (Fin n)} (hM : List.ofFn M = L)
    (h : L.all (fun r => decide (permVec π.symm r ∈ L)) = true) :
    ∀ i, permVec π.symm (M i) ∈ List.ofFn M := by
  intro i
  rw [hM]
  exact mem_of_list_all h (by rw [← hM]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)

-- CZ 折叠：X 校验行 ↦ X 校验行
theorem bb18_foldCz_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18FoldCz r ∈ bb18Rx)) = true := by decide

-- CZ 折叠：Z 校验行 ↦ Z 校验行
theorem bb18_foldCz_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18FoldCz r ∈ bb18Rz)) = true := by decide

-- Hadamard 折叠：X 校验行 ↦ Z 校验行（ZX-对偶，交换两侧）
theorem bb18_foldH_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18FoldH r ∈ bb18Rz)) = true := by decide

-- Hadamard 折叠：Z 校验行 ↦ X 校验行
theorem bb18_foldH_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18FoldH r ∈ bb18Rx)) = true := by decide

-- swap 型（x 方向平移）
theorem bb18_shiftX_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18ShiftX r ∈ bb18Rx)) = true := by decide

theorem bb18_shiftX_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18ShiftX r ∈ bb18Rz)) = true := by decide

-- swap 型（y 方向平移）
theorem bb18_shiftY_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18ShiftY r ∈ bb18Rx)) = true := by decide

theorem bb18_shiftY_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18ShiftY r ∈ bb18Rz)) = true := by decide

/-- **逆置换方向的同一组事实**：上面八条只用到置换的"正向"，而核与行空间的
不变性（`inKerB_permVec` / `permVec_mem_spanL_iff`）需要**逆置换**也保持行集——
下面四条补上这一半。对合（`bb18FoldCz`、`bb18FoldH`）下它与正向是同一个置换，
三阶元（`bb18ShiftX`、`bb18ShiftY`）下则是 `π² = π⁻¹`。

陈述写在 `bb18Rz` 上：本码 $H_X = H_Z$（`bb18Rx` 与 `bb18Rz` 是同一个字面量列表），
故同一条事实对两侧行列表都成立。 -/

theorem bb18_foldCz_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18FoldCz.symm r ∈ bb18Rz)) = true := by decide

theorem bb18_foldH_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18FoldH.symm r ∈ bb18Rz)) = true := by decide

theorem bb18_shiftX_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18ShiftX.symm r ∈ bb18Rz)) = true := by decide

theorem bb18_shiftY_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18ShiftY.symm r ∈ bb18Rz)) = true := by decide

/-- **CZ 折叠保持 X 行空间**（自同构，X 侧）。 -/
theorem bb18_foldCz_preserves_spanL_x {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18FoldCz v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldCz_rows_x hr) hv

/-- **CZ 折叠保持 Z 行空间**（自同构，Z 侧）。 -/
theorem bb18_foldCz_preserves_spanL_z {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18FoldCz v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldCz_rows_z hr) hv

/-- **Hadamard 折叠把 X 行空间送到 Z 行空间**（ZX-对偶，§3.2：$\tau_0$ 交换两侧）。 -/
theorem bb18_foldH_maps_spanL_xz {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18FoldH v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldH_rows_x hr) hv

/-- **Hadamard 折叠把 Z 行空间送到 X 行空间**。 -/
theorem bb18_foldH_maps_spanL_zx {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18FoldH v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldH_rows_z hr) hv

/-- **swap 型门保持 X 行空间**（§3.3 Theorem 3.2）。 -/
theorem bb18_shiftX_preserves_spanL_x {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18ShiftX v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftX_rows_x hr) hv

theorem bb18_shiftX_preserves_spanL_z {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18ShiftX v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftX_rows_z hr) hv

theorem bb18_shiftY_preserves_spanL_x {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18ShiftY v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftY_rows_x hr) hv

theorem bb18_shiftY_preserves_spanL_z {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18ShiftY v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftY_rows_z hr) hv

/-! ## 四、断言 2：诱导的逻辑作用

逻辑空间是商 $\ker H_Z/\operatorname{rowspace}H_X$，维数 $k=4$
（`bb18_k`：$18-7-7=4$）。下面给出**四个显式逻辑算符**作为它的一组基，
每个配一个**对偶见证**（在 $\ker H_X$ 里、与该算符配对为 1）：

| 基算符 | 支撑 | 对偶见证 | 支撑 |
|---|---|---|---|
| $L_0$ | `{4,13,14,16}` | $D_0$ | `{2,12,13,14,16,17}` |
| $L_1$ | `{3,12,13,15}` | $D_1$ | `{0,12,13,14,15,17}` |
| $L_2$ | `{0,2,15,16}` | $D_2$ | `{9,11,12,13,16,17}` |
| $L_3$ | `{0,1,16,17}` | $D_3$ | `{10,11,12,14,15,16}` |

四者都是重量 4（= 码距）。"它是逻辑算符"只由两条**逐行配对**的断言给出
（`mem_ker_of_inKerB` + `not_mem_rowSpace_of_dualCheck`），**不跑行消元**；
模行空间的独立性由 `rankEchelon` 的秩断言给出（秩从 7 升到 11）。

**诚实说明**：这组基是**有限搜索**的产物（在 $\ker H_X$ 的 128 个行空间陪集里逐类
取最小重量代表，再选一组配对为单位阵的四元组）。搜索只用来**找**数，不用来**证**——
上表的每条性质都由下面的 `by decide` 在内核里重新算过。 -/

/-- 逻辑算符基 $L_0$。 -/
def bb18Log0 : Vec 18 := e 4 + e 13 + e 14 + e 16

/-- 逻辑算符基 $L_1$。 -/
def bb18Log1 : Vec 18 := e 3 + e 12 + e 13 + e 15

/-- 逻辑算符基 $L_2$。 -/
def bb18Log2 : Vec 18 := e 0 + e 2 + e 15 + e 16

/-- 逻辑算符基 $L_3$。 -/
def bb18Log3 : Vec 18 := e 0 + e 1 + e 16 + e 17

/-- 四个逻辑基算符的向量形式（紧凑陈述用）。 -/
def bb18Log : Fin 4 → Vec 18 := ![bb18Log0, bb18Log1, bb18Log2, bb18Log3]

/-- $L_0$ 的对偶见证。 -/
def bb18Dual0 : Vec 18 := e 2 + e 12 + e 13 + e 14 + e 16 + e 17

/-- $L_1$ 的对偶见证。 -/
def bb18Dual1 : Vec 18 := e 0 + e 12 + e 13 + e 14 + e 15 + e 17

/-- $L_2$ 的对偶见证。 -/
def bb18Dual2 : Vec 18 := e 9 + e 11 + e 12 + e 13 + e 16 + e 17

/-- $L_3$ 的对偶见证。 -/
def bb18Dual3 : Vec 18 := e 10 + e 11 + e 12 + e 14 + e 15 + e 16

/-- 校验行的部分和（GF(2) 上就是异或）。逻辑算符在折叠下的像 = 逻辑组合 + 稳定子和，
稳定子和用它写出（行号取自 `Codes/BB18Anchor.lean` 的 `bb18Hx` 行表）。 -/
def rowSum (s : List (Fin 9)) : Vec 18 := (s.map (fun j => bb18Hx j)).sum

/-- $L_0$ 是逻辑算符：在 $\ker H_Z$ 里、不在 $H_X$ 的行空间里。 -/
theorem bb18Log0_logical :
    bb18Log0 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log0 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual0) (by decide) (by decide)⟩

/-- $L_1$ 是逻辑算符。 -/
theorem bb18Log1_logical :
    bb18Log1 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log1 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual1) (by decide) (by decide)⟩

/-- $L_2$ 是逻辑算符。 -/
theorem bb18Log2_logical :
    bb18Log2 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log2 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual2) (by decide) (by decide)⟩

/-- $L_3$ 是逻辑算符。 -/
theorem bb18Log3_logical :
    bb18Log3 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log3 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual3) (by decide) (by decide)⟩

/-- **四个类模行空间线性无关**：与校验行合起来秩为 $7+4=11=\dim\ker H_Z$，
故它们恰是逻辑空间的一组基（`bb18_k` 给出的 $k=4$ 在此被显式实现）。 -/
theorem bb18_logical_independent :
    rankEchelon (bb18Rx ++ [bb18Log0, bb18Log1, bb18Log2, bb18Log3]) = 11 := by decide

/-! ### 折叠在逻辑基上的诱导作用

每条断言把**像**拉回逻辑基：`θ(L_i) + (稳定子修正) = 行和`。
右边的行和落在 $\operatorname{rowspace}H_X$ 里，故断言逐字就是
"$\theta$ 把逻辑类 $[L_i]$ 送到 $[\,\sum_j c_j L_j\,]$"——
这就是这个门实现的逻辑门。 -/

/-- **CZ 折叠在 $L_0$ 上是恒等**（$L_0$ 是折叠的不动点：支撑 `{4,13,14,16}` 全在
$i=j$ 的固定轨道上）。 -/
theorem bb18_foldCz_log0 : permVec bb18FoldCz bb18Log0 = bb18Log0 := by decide

/-- **CZ 折叠：$[L_1]\mapsto[L_0+L_1]$**。 -/
theorem bb18_foldCz_log1 :
    permVec bb18FoldCz bb18Log1 + bb18Log0 + bb18Log1 = rowSum [4, 5, 7] := by decide

/-- **CZ 折叠：$[L_2]\mapsto[L_0+L_2]$**。 -/
theorem bb18_foldCz_log2 :
    permVec bb18FoldCz bb18Log2 + bb18Log0 + bb18Log2 = rowSum [2, 4, 6] := by decide

/-- **CZ 折叠：$[L_3]\mapsto[L_1+L_2+L_3]$**。 -/
theorem bb18_foldCz_log3 :
    permVec bb18FoldCz bb18Log3 + bb18Log1 + bb18Log2 + bb18Log3 = rowSum [6, 7, 8] :=
  by decide

/-- **Hadamard 折叠：$[L_0]\mapsto[L_0+L_1+L_2]$**（该门交换 X/Z 两侧，§3.4）。 -/
theorem bb18_foldH_log0 :
    permVec bb18FoldH bb18Log0 + bb18Log0 + bb18Log1 + bb18Log2 = rowSum [2, 4, 5] :=
  by decide

/-- **Hadamard 折叠：$[L_1]\mapsto[L_1+L_3]$**。 -/
theorem bb18_foldH_log1 :
    permVec bb18FoldH bb18Log1 + bb18Log1 + bb18Log3 = rowSum [6, 7] := by decide

/-- **Hadamard 折叠：$[L_2]\mapsto[L_2+L_3]$**。 -/
theorem bb18_foldH_log2 :
    permVec bb18FoldH bb18Log2 + bb18Log2 + bb18Log3 = rowSum [0, 2] := by decide

/-- **Hadamard 折叠：$[L_3]\mapsto[L_3]$**（差一个稳定子）。 -/
theorem bb18_foldH_log3 :
    permVec bb18FoldH bb18Log3 + bb18Log3 = rowSum [1, 2] := by decide

/-- **swap 型门 $\mathrm{SWAP}_x$：$[L_0]\mapsto[L_1]$**。 -/
theorem bb18_shiftX_log0 :
    permVec bb18ShiftX bb18Log0 + bb18Log1 = rowSum [0, 1, 2, 4] := by decide

/-- **$\mathrm{SWAP}_x$：$[L_1]\mapsto[L_0+L_1]$**。 -/
theorem bb18_shiftX_log1 :
    permVec bb18ShiftX bb18Log1 + bb18Log0 + bb18Log1 = rowSum [3] := by decide

/-- **$\mathrm{SWAP}_x$：$[L_2]\mapsto[L_2+L_3]$**。 -/
theorem bb18_shiftX_log2 :
    permVec bb18ShiftX bb18Log2 + bb18Log2 + bb18Log3 = rowSum [0, 2] := by decide

/-- **$\mathrm{SWAP}_x$：$[L_3]\mapsto[L_2]$**。 -/
theorem bb18_shiftX_log3 :
    permVec bb18ShiftX bb18Log3 + bb18Log2 = rowSum [0, 1] := by decide

/-- **swap 型门 $\mathrm{SWAP}_y$：$[L_0]\mapsto[L_0+L_1]$**。 -/
theorem bb18_shiftY_log0 :
    permVec bb18ShiftY bb18Log0 + bb18Log0 + bb18Log1 = rowSum [0, 1, 2] := by decide

/-- **$\mathrm{SWAP}_y$：$[L_1]\mapsto[L_0]$**（无稳定子修正）。 -/
theorem bb18_shiftY_log1 : permVec bb18ShiftY bb18Log1 = bb18Log0 := by decide

/-- **$\mathrm{SWAP}_y$：$[L_2]\mapsto[L_3]$**（无稳定子修正）。 -/
theorem bb18_shiftY_log2 : permVec bb18ShiftY bb18Log2 = bb18Log3 := by decide

/-- **$\mathrm{SWAP}_y$：$[L_3]\mapsto[L_2+L_3]$**（无稳定子修正）。 -/
theorem bb18_shiftY_log3 :
    permVec bb18ShiftY bb18Log3 + bb18Log2 + bb18Log3 = 0 := by decide

/-! ## 五、断言 3：距离不降

"折叠不降低有效距离"的两条实际依据是

1. **重量逐字保持**（`hammingNorm_permVec`）：置换不改变任何算符的 Hamming 重量，
   故它既不能把重的逻辑算符变轻、也不能把轻的变重；
2. **校验生成元在折叠下仍是校验生成元**（§三），故核与行空间都被保持——
   折叠把"不可探测非平凡算符"的集合映到自身。

合起来：折叠前后"逻辑算符的最低重量"是同一个数。下面把第 1 条对四个折叠逐条落实，
并把四个折叠下四个基算符的"仍是不可探测算符且重量仍为 4"机检。

**第 2 条是一般定理**：`inKerB` 与 `spanL` 在置换下的**一般**不变性
（`inKerB_permVec` / `permVec_mem_spanL_iff`，由点积的重标号引理 `dotProduct_permVec`
推出）把"像仍是不可探测算符"从逐算符实例抬成结构定理
`permVec_preserves_undetectable`（任意码、任意置换）及其 BB18 实例
`bb18Log_permVec_undetectable`。下面四条 `_undetectable` 即该定理的应用：
`decide` 只剩"`bb18Log i` 本身是重量 4 的逻辑算符"这三条已算事实，
核保持 / 行空间保持 / 重量保持不再逐算符重算。

**口径说明（诚实标注）**：对码的自同构而言"码距 = 4 在折叠前后相同"是重言式——
本模块不复述它，交付的是上面前两条（它们是"横截门不动有效距离"的实质内容）
+ 上述一般定理与它的四条实例。 -/

/-- CZ 折叠逐算符保持重量。 -/
theorem bb18_foldCz_weight (v : Vec 18) :
    hammingNorm (permVec bb18FoldCz v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- Hadamard 折叠逐算符保持重量。 -/
theorem bb18_foldH_weight (v : Vec 18) :
    hammingNorm (permVec bb18FoldH v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- $\mathrm{SWAP}_x$ 逐算符保持重量。 -/
theorem bb18_shiftX_weight (v : Vec 18) :
    hammingNorm (permVec bb18ShiftX v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- $\mathrm{SWAP}_y$ 逐算符保持重量。 -/
theorem bb18_shiftY_weight (v : Vec 18) :
    hammingNorm (permVec bb18ShiftY v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- **BB18 的断言 3（对任意自同构置换成立）**：设比特置换 `π` 保持两块校验的行集
（`π⁻¹` 把 `bb18Hz` 的每一行仍映为它的一行）与 X 行列表 `bb18Rx`（`π` 与 `π⁻¹` 都映到自身），
则四个逻辑基算符在 `π` 下的像仍是**同重量 4 的不可探测非平凡算符**。

结构部分由 `permVec_preserves_undetectable` 一次性给出，`decide` 只剩
"`bb18Log i` 本身是重量 4 的逻辑算符"这一条已算事实。 -/
theorem bb18Log_permVec_undetectable (π : Equiv.Perm (Fin 18))
    (hM : ∀ i : Fin 9, permVec π.symm (bb18Hz i) ∈ List.ofFn (bb18Hz))
    (hL : ∀ r ∈ bb18Rx, permVec π r ∈ bb18Rx)
    (hL' : ∀ r ∈ bb18Rx, permVec π.symm r ∈ bb18Rx)
    (i : Fin 4) :
    inKerB bb18Hz (permVec π (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec π (bb18Log i)) = false ∧
    hammingNorm (permVec π (bb18Log i)) = 4 := by
  obtain ⟨h1, h2, h3⟩ := permVec_preserves_undetectable bb18Hz bb18Rx π hM hL hL'
    (x := bb18Log i) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  exact ⟨h1, h2, by rw [h3]; fin_cases i <;> decide⟩

/-- **CZ 折叠把逻辑基算符映成不可探测非平凡算符，且重量仍为 4**（一般定理的实例）。

`inKerB` 一侧是与全部 $Z$ 校验逐行配对为零、`inSpanEch … = false` 一侧是不在
$H_X$ 的行空间里、最后一条是重量——后三条（结构部分）来自
`bb18Log_permVec_undetectable`，与码距 4 相合。 -/
theorem bb18_foldCz_undetectable (i : Fin 4) :
    inKerB bb18Hz (permVec bb18FoldCz (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec bb18FoldCz (bb18Log i)) = false ∧
    hammingNorm (permVec bb18FoldCz (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18FoldCz
    (kerRows_of_list_all bb18_ofFn_z bb18_foldCz_rows_symm)
    (fun _ hr => mem_of_list_all bb18_foldCz_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_foldCz_rows_symm hr) i

/-- **Hadamard 折叠（ZX-对偶）把逻辑基算符映成不可探测非平凡算符，重量仍为 4**。

注意两侧的**互换**：$\tau_0$ 把 $X$-校验送到 $Z$-校验（§3.2），故像落在
$\ker H_X$ 里、且不在 $H_Z$ 的行空间里——这正是 §3.2 Remark 3.1
"$\tau_0$ 交换逻辑 $Z$-算符与 $X$-算符"的机检形态。
（本码 $H_X = H_Z$、`bb18Rx` 与 `bb18Rz` 是同一个字面量列表，故一般定理的 `bb18Hz`/`bb18Rx`
版本在此可以定义地等同地复用。） -/
theorem bb18_foldH_undetectable (i : Fin 4) :
    inKerB bb18Hx (permVec bb18FoldH (bb18Log i)) = true ∧
    inSpanEch bb18Rz (permVec bb18FoldH (bb18Log i)) = false ∧
    hammingNorm (permVec bb18FoldH (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18FoldH
    (kerRows_of_list_all bb18_ofFn_x bb18_foldH_rows_symm)
    (fun _ hr => mem_of_list_all bb18_foldH_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_foldH_rows_symm hr) i

/-- **$\mathrm{SWAP}_x$ 把逻辑基算符映成不可探测非平凡算符，重量仍为 4**（一般定理的实例）。 -/
theorem bb18_shiftX_undetectable (i : Fin 4) :
    inKerB bb18Hz (permVec bb18ShiftX (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec bb18ShiftX (bb18Log i)) = false ∧
    hammingNorm (permVec bb18ShiftX (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18ShiftX
    (kerRows_of_list_all bb18_ofFn_z bb18_shiftX_rows_symm)
    (fun _ hr => mem_of_list_all bb18_shiftX_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_shiftX_rows_symm hr) i

/-- **$\mathrm{SWAP}_y$ 把逻辑基算符映成不可探测非平凡算符，重量仍为 4**（一般定理的实例）。 -/
theorem bb18_shiftY_undetectable (i : Fin 4) :
    inKerB bb18Hz (permVec bb18ShiftY (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec bb18ShiftY (bb18Log i)) = false ∧
    hammingNorm (permVec bb18ShiftY (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18ShiftY
    (kerRows_of_list_all bb18_ofFn_z bb18_shiftY_rows_symm)
    (fun _ hr => mem_of_list_all bb18_shiftY_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_shiftY_rows_symm hr) i

end QECCertificates
