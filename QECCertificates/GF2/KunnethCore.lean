/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.HGPCleaningDual

/-!
# 子空间张量交：`{X : 列 ⊆ U ∧ 行 ⊆ W}` 的维数（ 收官）

维数张量公式 $k = k_1k_2 + k_1^\top k_2^\top$ 的全部难度集中在下述事实：
**列落在 $U$ 中、行落在 $W$ 中的矩阵构成的空间，维数恰为 $\dim U\cdot\dim W$**
（“子空间张量交”的维数计数，即 $U\otimes W$ 的维数）。

本模块把它一次性证成（`finrank_colsRows`），路线是**显式等价**而非维数论证：

* 取 $U$ 的一组基 $u$ 与 `Fin a → Vec p` 上的**坐标读回**线性映射 $L$
  （独立族的左逆，`exists_leftInverse_of_linearIndependent`）；
* 系数展开 `vee`（$a\times s$ 系数 ↦ $p\times s$ 矩阵）与坐标提取 `wedge`
  （$p\times s$ 矩阵 ↦ $a\times s$ 系数）互为逆；
* 关键一步：**行条件在 `wedge` 下不变**——`wedge` 把“行都在 $W$ 中”翻译成
  “行都在 $W$ 中”，于是 $\{列\subseteq U,\ 行\subseteq W\}\cong \{\text{行}\subseteq W\}$，
  而后者同构于 `Fin a → W`，维数 $a\cdot\dim W$。

前两条辅助事实（列空间 / 行空间的维数）是 `finrank_colsSub` / `finrank_rowsSub`。

## 索引约定

矩阵一律写成**乘积索引** `VMat p s = Fin p × Fin s → ZMod 2`（与 `hgpHX` 的行类型一致），
不拍平成 `Fin`——结构定理因此零换标。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {p q r s a b : ℕ}

/-! ## 一、乘积索引矩阵与两个"约束子空间" -/

/-- 乘积索引矩阵：行 `Fin p`、列 `Fin s`。 -/
abbrev VMat (p s : ℕ) := Fin p × Fin s → ZMod 2

/-- 第 `j` 列（作为 `Vec p`）。 -/
def colOf {p s : ℕ} (X : VMat p s) (j : Fin s) : Vec p := fun i => X (i, j)

/-- 第 `i` 行（作为 `Vec s`）。 -/
def rowOf {p s : ℕ} (X : VMat p s) (i : Fin p) : Vec s := fun j => X (i, j)

@[simp] lemma colOf_apply {X : VMat p s} {j : Fin s} {i : Fin p} : colOf X j i = X (i, j) := rfl

@[simp] lemma rowOf_apply {X : VMat p s} {i : Fin p} {j : Fin s} : rowOf X i j = X (i, j) := rfl

@[simp] lemma colOf_add {X Y : VMat p s} {j : Fin s} : colOf (X + Y) j = colOf X j + colOf Y j := rfl

@[simp] lemma colOf_smul {c : ZMod 2} {X : VMat p s} {j : Fin s} :
    colOf (c • X) j = c • colOf X j := rfl

@[simp] lemma rowOf_add {X Y : VMat p s} {i : Fin p} : rowOf (X + Y) i = rowOf X i + rowOf Y i := rfl

@[simp] lemma rowOf_smul {c : ZMod 2} {X : VMat p s} {i : Fin p} :
    rowOf (c • X) i = c • rowOf X i := rfl

/-- **列约束子空间**：所有列都落在 `U` 中的矩阵。 -/
def colsSub (U : Submodule (ZMod 2) (Vec p)) : Submodule (ZMod 2) (VMat p s) where
  carrier := {X | ∀ j, colOf X j ∈ U}
  zero_mem' := fun j => U.zero_mem
  add_mem' := fun {X Y} hX hY => fun j => by
    rw [colOf_add]; exact U.add_mem (hX j) (hY j)
  smul_mem' := fun c {X} hX => fun j => by
    rw [colOf_smul]; exact U.smul_mem c (hX j)

/-- **行约束子空间**：所有行都落在 `W` 中的矩阵。 -/
def rowsSub (W : Submodule (ZMod 2) (Vec s)) : Submodule (ZMod 2) (VMat p s) where
  carrier := {X | ∀ i, rowOf X i ∈ W}
  zero_mem' := fun i => W.zero_mem
  add_mem' := fun {X Y} hX hY => fun i => by
    rw [rowOf_add]; exact W.add_mem (hX i) (hY i)
  smul_mem' := fun c {X} hX => fun i => by
    rw [rowOf_smul]; exact W.smul_mem c (hX i)

@[simp] lemma mem_colsSub {U : Submodule (ZMod 2) (Vec p)} {X : VMat p s} :
    X ∈ colsSub U ↔ ∀ j, colOf X j ∈ U :=
  ⟨fun h => h, fun h => h⟩

@[simp] lemma mem_rowsSub {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} :
    X ∈ rowsSub W ↔ ∀ i, rowOf X i ∈ W :=
  ⟨fun h => h, fun h => h⟩

/-! ## 二、列约束 / 行约束空间的维数 -/

/-- 列都在 `U` 中的矩阵与 `Fin s → U` 的显式线性等价（按列读）。 -/
noncomputable def colsSubEquiv (U : Submodule (ZMod 2) (Vec p)) :
    ↥(colsSub (s := s) U) ≃ₗ[ZMod 2] (Fin s → U) where
  toFun X := fun j => ⟨colOf X.1 j, X.2 j⟩
  invFun f := ⟨fun ij => (f ij.2).1 ij.1, fun j => (f j).2⟩
  left_inv X := by ext ⟨i, j⟩; rfl
  right_inv f := by ext j i; rfl
  map_add' X Y := by ext j i; rfl
  map_smul' c X := by ext j i; rfl

/-- 行都在 `W` 中的矩阵与 `Fin p → W` 的显式线性等价（按行读）。 -/
noncomputable def rowsSubEquiv (W : Submodule (ZMod 2) (Vec s)) :
    ↥(rowsSub (p := p) (s := s) W) ≃ₗ[ZMod 2] (Fin p → W) where
  toFun X := fun i => ⟨rowOf X.1 i, X.2 i⟩
  invFun f := ⟨fun ij => (f ij.1).1 ij.2, fun i => (f i).2⟩
  left_inv X := by ext ⟨i, j⟩; rfl
  right_inv f := by ext i j; rfl
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl

/-- **列约束空间的维数**：$\dim\{X : \mathrm{col}\,X\subseteq U\} = s\cdot\dim U$。 -/
theorem finrank_colsSub (U : Submodule (ZMod 2) (Vec p)) :
    Module.finrank (ZMod 2) (colsSub (s := s) U) = s * Module.finrank (ZMod 2) U := by
  rw [(colsSubEquiv (s := s) U).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp

/-- **行约束空间的维数**：$\dim\{X : \mathrm{row}\,X\subseteq W\} = p\cdot\dim W$。 -/
theorem finrank_rowsSub (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) (rowsSub (p := p) W) = p * Module.finrank (ZMod 2) W := by
  rw [(rowsSubEquiv (p := p) W).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp

/-! ## 三、独立族的坐标读回（左逆） -/

/-- 线性映射在标准基下的矩阵表示：`L x = Σ_i x_i · L(e_i)`。 -/
lemma linearMap_apply_eq_sum_single (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (x : Vec p) :
    L x = fun k => ∑ i, x i * L (Pi.single i (1 : ZMod 2)) k := by
  conv_lhs => rw [show x = ∑ i, x i • (Pi.single i (1 : ZMod 2)) from by
    funext j
    simp [Pi.single_apply]]
  funext k
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]

/-- **独立族的左逆**：`u : Fin a → Vec p` 线性无关时，存在线性映射 `L` 把任意
组合 $\sum_k c_k u_k$ 读回系数 $c$。

构造：组合映射 $\varphi(c)=\sum_k c_k u_k$ 由无关性单射，取其在全空间上的左逆
（`LinearMap.exists_leftInverse_of_injective`，向量空间上任一单射线性映射都有左逆）。 -/
theorem exists_leftInverse_of_linearIndependent {u : Fin a → Vec p}
    (hu : LinearIndependent (ZMod 2) u) :
    ∃ L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2), ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c := by
  classical
  let φ : (Fin a → ZMod 2) →ₗ[ZMod 2] Vec p :=
    { toFun := fun c => ∑ k, c k • u k
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply,
          smul_eq_mul] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext k
    exact Fintype.linearIndependent_iff.mp hu c hc k
  obtain ⟨L, hL⟩ := φ.exists_leftInverse_of_injective hker
  exact ⟨L, fun c => LinearMap.congr_fun hL c⟩

/-! ## 四、系数展开 `vee` 与坐标提取 `wedge` -/

/-- **系数展开**：把 `a×s` 的系数矩阵按 `U` 的基向量展开成 `p×s` 矩阵
（第 `j` 列 = $\sum_k C_{kj}u_k$）。 -/
noncomputable def vee (u : Fin a → Vec p) : VMat a s →ₗ[ZMod 2] VMat p s where
  toFun C := fun ij => ∑ k, C (k, ij.2) * u k ij.1
  map_add' C D := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c C := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- **坐标提取**：用左逆 `L` 把 `p×s` 矩阵的每一列读成系数。 -/
noncomputable def wedge (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) : VMat p s →ₗ[ZMod 2] VMat a s where
  toFun X := fun kj => L (colOf X kj.2) kj.1
  map_add' X Y := by
    ext ⟨k, j⟩
    simp only [Pi.add_apply, colOf_add, map_add, Pi.add_apply]
  map_smul' c X := by
    ext ⟨k, j⟩
    simp only [Pi.smul_apply, colOf_smul, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

@[simp] lemma vee_apply (u : Fin a → Vec p) (C : VMat a s) (i : Fin p) (j : Fin s) :
    vee u C (i, j) = ∑ k, C (k, j) * u k i := rfl

@[simp] lemma wedge_apply (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (X : VMat p s)
    (k : Fin a) (j : Fin s) : wedge L X (k, j) = L (colOf X j) k := rfl

/-- `wedge` 之后 `vee` 还原（在列约束空间上）：`vee` 是 `wedge` 的左逆。 -/
lemma vee_wedge_of_coords {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {U : Submodule (ZMod 2) (Vec p)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s} (hX : ∀ j, colOf X j ∈ U) :
    vee u (wedge L X) = X := by
  ext ⟨i, j⟩
  simp only [vee_apply, wedge_apply]
  have h := congrFun (hcoords (colOf X j) (hX j)) i
  simpa using h

/-- `vee` 之后 `wedge` 还原（处处）：`vee` 是 `wedge` 的右逆。 -/
lemma wedge_vee {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    (hleft : ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c) (C : VMat a s) :
    wedge L (vee u C) = C := by
  ext ⟨k, j⟩
  simp only [wedge_apply]
  have hcol : colOf (vee u C) j = ∑ k', C (k', j) • u k' := by
    funext i
    rw [colOf_apply, vee_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul]
  rw [hcol, hleft]

/-! ## 五、行条件在 `wedge` 下的对应 -/

/-- **行条件前推**：`X` 的行都在 `W` 中 ⟹ `wedge L X` 的行都在 `W` 中
（把 `L` 的矩阵表示 `L x = Σ_i x_i · L(e_i)` 代进 `wedge` 的逐行和式）。 -/
lemma rowOf_wedge_mem {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} (hX : ∀ i, rowOf X i ∈ W) :
    ∀ k, rowOf (wedge L X) k ∈ W := by
  intro k
  have hrow : rowOf (wedge L X) k = ∑ i : Fin p, (L (Pi.single i (1 : ZMod 2)) k) • rowOf X i := by
    funext j
    rw [rowOf_apply, wedge_apply, linearMap_apply_eq_sum_single L (colOf X j)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply, colOf_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hrow]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i)

/-- **行条件回推**：`wedge L X` 的行都在 `W` 且 `X` 的列都在 `U` 中 ⟹ `X` 的行都在 `W` 中
（用 `vee_wedge_of_coords` 把 `X` 的行写成 `wedge L X` 的行的组合）。 -/
lemma rowOf_mem_of_wedge_rowOf_mem {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {U : Submodule (ZMod 2) (Vec p)} {W : Submodule (ZMod 2) (Vec s)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s}
    (hX : ∀ j, colOf X j ∈ U) (hY : ∀ k, rowOf (wedge L X) k ∈ W) :
    ∀ i, rowOf X i ∈ W := by
  intro i
  have hrow : rowOf X i = ∑ k, (u k i) • rowOf (wedge L X) k := by
    funext j
    have h := congrFun (vee_wedge_of_coords hcoords hX) (i, j)
    simp only [vee_apply, wedge_apply, rowOf_apply] at h ⊢
    rw [← h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hrow]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hY k)

/-! ## 六、主定理：子空间张量交的维数 -/

/-- **子空间张量交的维数**：列落在 `U` 中、行落在 `W` 中的矩阵空间，维数恰为
$\dim U\cdot\dim W$。

这是维数张量公式 $k=k_1k_2+k_1^\top k_2^\top$ 的**唯一**非平凡维数输入
（$U\otimes W$ 的维数在矩阵语言下的形态）。证明走显式等价：

$$\{X:\mathrm{col}\,X\subseteq U,\ \mathrm{row}\,X\subseteq W\}\;\cong\;\mathrm{Fin}\,a\to W,
\qquad a=\dim U,$$

前向 = 坐标提取 `wedge` 后取行，反向 = 用系数行的 `W`-组合做 `vee`。 -/
theorem finrank_colsRows (U : Submodule (ZMod 2) (Vec p)) (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W)
      = Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) W := by
  classical
  -- `U` 的基与左逆坐标
  let bu : Module.Basis (Fin (Module.finrank (ZMod 2) U)) (ZMod 2) U := Module.finBasis (ZMod 2) U
  let u : Fin (Module.finrank (ZMod 2) U) → Vec p := fun k => (bu k : Vec p)
  have hu : LinearIndependent (ZMod 2) u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcU : (∑ k, c k • bu k : U) = 0 := by
      apply Subtype.ext
      simpa [u] using hc
    intro k
    exact Fintype.linearIndependent_iff.mp bu.linearIndependent c hcU k
  obtain ⟨L, hL⟩ := exists_leftInverse_of_linearIndependent hu
  -- 坐标读回：`U` 中向量由 `L` 的取值还原
  have hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x := by
    intro x hx
    have hspan : x ∈ Submodule.span (ZMod 2) (Set.range u) := by
      have h1 : (⟨x, hx⟩ : U) ∈ Submodule.span (ZMod 2) (Set.range bu) := by
        rw [bu.span_eq]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := bu)
          (x := (⟨x, hx⟩ : U))).mp h1
      refine (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := u) (x := x)).mpr ⟨c, ?_⟩
      have hval := congrArg (fun y : U => (y : Vec p)) hc
      simpa [u] using hval
    obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank (ZMod 2) U) → ZMod 2, ∑ i, c i • u i = x :=
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := u) (x := x)).mp hspan
    rw [← hc, hL c]
  -- 反向映射的两个约束条件
  have hcolW : ∀ f : Fin (Module.finrank (ZMod 2) U) → W,
      ∀ j, colOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) j ∈ U := by
    intro f j
    have hfun : colOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) j
        = ∑ k, (((f k : W) : Vec s) j) • u k := by
      funext i
      rw [colOf_apply, vee_apply, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (show u k ∈ U from (bu k).2)
  have hrowW : ∀ f : Fin (Module.finrank (ZMod 2) U) → W,
      ∀ i, rowOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) i ∈ W := by
    intro f i
    refine rowOf_mem_of_wedge_rowOf_mem hcoords (fun j => hcolW f j) (fun k => ?_) i
    rw [wedge_vee hL]
    exact (f k).2
  -- 显式线性等价：`{列 ⊆ U, 行 ⊆ W} ≃ (Fin a → W)`
  have he : ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W) ≃ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) U) → W) :=
    { toFun := fun X => fun k =>
        ⟨rowOf (wedge L X.1) k, rowOf_wedge_mem (X := X.1) (fun i => X.2.2 i) k⟩
      invFun := fun f => ⟨vee u (fun kj => ((f kj.1 : W) : Vec s) kj.2), hcolW f, hrowW f⟩
      left_inv := by
        intro X
        apply Subtype.ext
        exact vee_wedge_of_coords hcoords (fun j => X.2.1 j)
      right_inv := by
        intro f
        funext k
        apply Subtype.ext
        funext j
        simpa using congrFun (wedge_vee (s := s) hL
          (fun kj => ((f kj.1 : W) : Vec s) kj.2)) (k, j)
      map_add' := by
        intro X Y
        funext k
        apply Subtype.ext
        funext j
        change wedge L (X.1 + Y.1) (k, j) = wedge L X.1 (k, j) + wedge L Y.1 (k, j)
        rw [map_add, Pi.add_apply]
      map_smul' := by
        intro c X
        funext k
        apply Subtype.ext
        funext j
        change wedge L (c • X.1) (k, j) = c * wedge L X.1 (k, j)
        rw [map_smul, Pi.smul_apply, smul_eq_mul] }
  rw [he.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp

end QECCertificates
