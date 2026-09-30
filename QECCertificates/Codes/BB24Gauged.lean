/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB18Anchor
import QECCertificates.Codes.Gauging
import QECCertificates.GF2.RankEchelon

/-!
# BB 族 gauging 实例：$[[18,4,4]]$ 经 $K_4$ 辅助图 $\to$ $[[24,3,4]]$（ 真实例）

本模块是 **gauging 真实例**：把 BB $[[18,4,4]]$ 的一个重量-4 X 型逻辑算符
$L$ 提升为稳定子，辅助图取 $K_4$（顶点 = $L$ 的 4 个支撑比特），测得

$$[[18,4,4]] \;\longrightarrow\; [[24,3,4]],$$

即 $k$ 恰减一而距离保持。这正是 `Codes/Gauging.lean` 三条表示层定理
（`deformX_css` 相容性保持、`gauss_prod_eq_vertex_prod` 的 $L=\prod_v A_v$、
`deformX_k` 维数恰减一）在同一实例上的**落地**；也是"空间型 gauging 的
最小非平凡真实例"。

## 构造（与 `tools/probeA/probeB_gauging_e2e.py` 逐行一致）

* 辅助图 $K_4$：4 个顶点是 $L$ 的支撑比特，6 条边各配一个辅助比特（编号 $18..23$）；
* Gauss 律 $A_v = X_v\prod_{e\ni v} X_e$（$v \in V$）——其乘积
  $\prod_v A_v$ 在辅助比特上成对相消，**恰等于 $L$**；
* X 校验 = 原 $H_X$（9 行）+ $A_v$（4 行）；
* Z 校验 = 原 Z 行与 $L$ 的相交集在 $K_4$ 内配对成边后追加辅助比特（9 行）
  + $K_4$ 生成 cycle 基上的 flux $B_p$（3 行）。

## 主结果（全部内核 `by decide`）

* `bb24_k`：$24-11-10=3$——**维数恰减一**（对照 `deformX_k`）；
* `bb24_dx` / `bb24_dz`：两侧码距**恰为 4**（下界：重量限定候选列表为空——
  走 List 形态入口 `eq_minWeight_of_lightCand_nil`，绕开 `List.toFinset` 的 O(N²) 去重；
  上界：显式重量-4 见证 + 对偶见证配对 1）。

## 与数值侧的关系

预研 `probeB_gauging_e2e_result.json` 以 MaxSAT + MILP + 暴力三路给出同一组读数
（$n=24$、$k=3$、$d=4$、`css_orthogonal`、`L_equals_prod_A`）。

## gauging 步本身（$\S$四/$\S$五，2026-09-28 补）

$\S$一–$\S$三 的两张校验矩阵是**字面矩阵**；$\S$四 把"基码 + $L$ + $K_4$ $\to$ gauged
矩阵"的**生成过程**搬进内核：Gauss 律 $A_v$、配对边（T-join）、flux 圈基全部由
$K_4$ 的顶点/边/圈数据**构造**出来，构造矩阵与字面矩阵逐分量相等（`bb24HxC_eq` /
`bb24HzC_eq`）。结构定理落在三件事上：**Gauss 律之和 = 被测逻辑算符**（`bb24_gauss_sum`，
辅助位成对相消）、**测掉的逻辑进入校验行空间**（`bb24L_mem_rowSpace`——"把 $L$ 提升
为校验"在行空间层的字面含义）、**维数降一走定理路线**（`bb18_gauged_drop`，
`deformX_k` 的实例化，假设由内核判定）。于是"gauging 步本身数值检查"这句话从
本实例的边界清单上消失：从基码到变形码的全链都在内核里。
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 校验矩阵（由行列表组装） -/

/-- gauged 码的 X 型校验 $H_X'$（原 $H_X$ 9 行 + Gauss 律 $A_v$ 4 行）。 -/
def bb24Hx : Matrix (Fin 13) (Fin 24) (ZMod 2) :=
  Matrix.of ![
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 24),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 24),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 24),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 24),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 24),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 24),
    (e 0 + e 18 + e 19 + e 20 : Vec 24),
    (e 2 + e 18 + e 21 + e 22 : Vec 24),
    (e 6 + e 19 + e 21 + e 23 : Vec 24),
    (e 9 + e 20 + e 22 + e 23 : Vec 24)]

/-- gauged 码的 Z 型校验 $H_Z'$（变形 Z 校验 9 行 + flux 3 行）。 -/
def bb24Hz : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  Matrix.of ![
    (e 0 + e 1 + e 3 + e 9 + e 11 + e 15 + e 20 : Vec 24),
    (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 + e 22 : Vec 24),
    (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 + e 18 : Vec 24),
    (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 + e 23 : Vec 24),
    (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
    (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
    (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 + e 19 : Vec 24),
    (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
    (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 + e 21 : Vec 24),
    (e 18 + e 19 + e 21 : Vec 24),
    (e 18 + e 20 + e 21 + e 23 : Vec 24),
    (e 21 + e 22 + e 23 : Vec 24)]

/-- X 校验的行列表（字面量，与 `bb24Hx` 逐行相同；`bb24_ofFn_x` 把两者钉在一起）。 -/
def bb24Rx : List (Vec 24) :=
  [(e 0 + e 1 + e 3 + e 9 + e 11 + e 15 : Vec 24),
   (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 : Vec 24),
   (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 : Vec 24),
   (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 : Vec 24),
   (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
   (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
   (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 : Vec 24),
   (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
   (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 : Vec 24),
   (e 0 + e 18 + e 19 + e 20 : Vec 24),
   (e 2 + e 18 + e 21 + e 22 : Vec 24),
   (e 6 + e 19 + e 21 + e 23 : Vec 24),
   (e 9 + e 20 + e 22 + e 23 : Vec 24)]

/-- Z 校验的行列表（字面量，与 `bb24Hz` 逐行相同）。 -/
def bb24Rz : List (Vec 24) :=
  [(e 0 + e 1 + e 3 + e 9 + e 11 + e 15 + e 20 : Vec 24),
   (e 1 + e 2 + e 4 + e 9 + e 10 + e 16 + e 22 : Vec 24),
   (e 0 + e 2 + e 5 + e 10 + e 11 + e 17 + e 18 : Vec 24),
   (e 3 + e 4 + e 6 + e 9 + e 12 + e 14 + e 23 : Vec 24),
   (e 4 + e 5 + e 7 + e 10 + e 12 + e 13 : Vec 24),
   (e 3 + e 5 + e 8 + e 11 + e 13 + e 14 : Vec 24),
   (e 0 + e 6 + e 7 + e 12 + e 15 + e 17 + e 19 : Vec 24),
   (e 1 + e 7 + e 8 + e 13 + e 15 + e 16 : Vec 24),
   (e 2 + e 6 + e 8 + e 14 + e 16 + e 17 + e 21 : Vec 24),
   (e 18 + e 19 + e 21 : Vec 24),
   (e 18 + e 20 + e 21 + e 23 : Vec 24),
   (e 21 + e 22 + e 23 : Vec 24)]

/-- X 型见证：重量 4 的 X 逻辑算符（$\in \ker H_X'$）。 -/
def bb24XW : Vec 24 := (e 3 + e 4 + e 10 + e 11 : Vec 24)

/-- Z 型见证：重量 4 的 Z 逻辑算符（$\in \ker H_Z'$）。 -/
def bb24ZW : Vec 24 := (e 0 + e 1 + e 7 + e 10 : Vec 24)

/-- `bb24XW` 的对偶见证：$\in \ker H_Z'$、与 `bb24XW` 配对为 1。 -/
def bb24XWdual : Vec 24 := (e 1 + e 2 + e 3 + e 5 + e 6 + e 7 : Vec 24)

/-- `bb24ZW` 的对偶见证：$\in \ker H_X'$、与 `bb24ZW` 配对为 1。 -/
def bb24ZWdual : Vec 24 := (e 3 + e 4 + e 10 + e 11 : Vec 24)

/-! ## 行列表桥接（矩阵即由行列表组装，这里只是把 `List.ofFn` 形态钉住） -/

theorem bb24_ofFn_x : List.ofFn (fun i => bb24Hx i) = bb24Rx := by decide
theorem bb24_ofFn_z : List.ofFn (fun i => bb24Hz i) = bb24Rz := by decide

/-! ## 维数：$k$ 恰减一 -/

/-- **[[24,3,4]] 的维数**：$24 - 11 - 10 = 3$（对照基码 $[[18,4,4]]$ 的 $k=4$）。

归约走 `GF2/RankEchelon.lean` 的**只追加梯队形** `rankEchelon`：它的枢轴行不做回代消去，
因而不会把新枢轴行复制进每一条旧行（`rowReduce` 的代价正是由此在宽 24 上逐轮相乘，
第 7 行起 >200 s 不收敛）。桥定理 `rankEchelon_eq_length_rowReduce` 保证两种归约给出
**同一个秩**，所以本定理的**陈述仍写成 `rowReduce` 形态**，与其余 `_k` 定理逐字可比——
换掉的只是求值路径，不是数学内容。归约量降到毫秒级后不再需要逐定理的心跳预算。 -/
theorem bb24_k : 24 - (rowReduce (List.ofFn fun i => bb24Hx i)).length
    - (rowReduce (List.ofFn fun i => bb24Hz i)).length = 3 := by
  rw [bb24_ofFn_x, bb24_ofFn_z]
  simp only [← rankEchelon_eq_length_rowReduce]
  decide

/-! ## 距离：两侧恰为 4（下界走**梯队形后端**）

`GF2/LowerBound.lean` 的 `lightCand` 用 `inSpanB`，而 `inSpanB` 内部跑 `rowReduce`：
宽度 24 上这是**每个候选 >200 s** 量级，2325 个候选不可能过下去（实测 80 GB 未收敛）。

这里把**同一个候选集**搬到 `inSpanEch`（`GF2/RankEchelon.lean` 的梯队形后端，毫秒级）上，
并在本文件内证明"候选为空 ⟹ 距离下界"（镜像 `lowerHyp_of_lightCand_nil` 的编排）。
**核心模块 `GF2/LowerBound.lean` 一字未动。** -/

/-- BB24 的轻算符判定（梯队形后端）：重量非零、与 `M₁` 对易、且不在 `M₂` 的行空间里。 -/
abbrev bb24Light {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (v : Vec 24) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧ inSpanEch (List.ofFn fun i => M₂ i) v = false

/-- BB24 的轻算符候选集：重量 $\le 3$（即 $< d = 4$）的那些。 -/
def bb24LightCand {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2)) :
    List (Vec 24) :=
  (lightVecs 24 3).filter (fun v => decide (bb24Light M₁ M₂ v))

/-- **下界证书（X 侧）**：候选列表为空。 -/
theorem bb24_lightCand_x : bb24LightCand bb24Hx bb24Hz = [] := by decide

/-- **下界证书（Z 侧）**：候选列表为空。 -/
theorem bb24_lightCand_z : bb24LightCand bb24Hz bb24Hx = [] := by decide

/-- **下界假设**（镜像 `lowerHyp_of_lightCand_nil`）：候选为空 ⟹ 距离 $\ge 4$。 -/
theorem bb24_lowerHyp {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (h : bb24LightCand M₁ M₂ = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → 4 ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < 4 := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.rowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs 24 (4 - 1) := by
    refine mem_lightVecs 24 (4 - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ bb24LightCand M₁ M₂ := by
    unfold bb24LightCand
    rw [List.mem_filter]
    refine ⟨hcov, ?_⟩
    rw [decide_eq_true_eq]
    exact ⟨hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanEch_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem

/-- **X 侧码距 = 4**（下界候选列表为空 + 上界重量-4 见证 + 对偶见证配对 1）。

下界：`bb24LightCand bb24Hx bb24Hz = []`（梯队形后端，`by decide`）；
上界：显式重量-4 逻辑算符 `bb24XW`。

（下界走 `echelonFrom` 后端：候选集判定是毫秒级，不读宽矩阵的秩——
`inSpanB` 的 `rowReduce` 后端每候选一次宽矩阵消元，实测 80 GB 未收敛。） -/
theorem bb24_dx : min_weight_ker_not_mem_rowspace bb24Hx bb24Hz = 4 :=
  eq_minWeight_of_bounds bb24Hx bb24Hz (by decide) (E := bb24XW)
    (mem_ker_of_inKerB bb24Hx (by decide))
    (not_mem_rowSpace_of_dualCheck bb24Hz (w := bb24XWdual) (by decide) (by decide))
    (by decide)
    (bb24_lowerHyp bb24Hx bb24Hz bb24_lightCand_x)

/-- **Z 侧码距 = 4**（同 X 侧：下界走梯队形后端的候选集）。 -/
theorem bb24_dz : min_weight_ker_not_mem_rowspace bb24Hz bb24Hx = 4 :=
  eq_minWeight_of_bounds bb24Hz bb24Hx (by decide) (E := bb24ZW)
    (mem_ker_of_inKerB bb24Hz (by decide))
    (not_mem_rowSpace_of_dualCheck bb24Hx (w := bb24ZWdual) (by decide) (by decide))
    (by decide)
    (bb24_lowerHyp bb24Hz bb24Hx bb24_lightCand_z)

/-! ## 四、gauging 步的构造（从 bb18L 与 K4 生成两张校验矩阵） -/

/-- 被测的重量-4 X 型逻辑算符（支撑 $\{0,2,6,9\}$）。 -/
def bb18L : Vec 18 := e 0 + e 2 + e 6 + e 9

/-- K4 的四个顶点 = `bb18L` 的支撑比特。 -/
def k4Vert : Fin 4 → Fin 18 := ![(0 : Fin 18), 2, 6, 9]

/-- K4 的六条边（顶点对枚举）。 -/
def k4Ends : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- 每条边的辅助比特槽位（18..23）。 -/
def k4EdgeSlot : Fin 6 → Fin 24 := ![18, 19, 20, 21, 22, 23]

/-- 18 位数据向量零填充进 24 位（辅助位补零）。 -/
def bb24Pad (v : Vec 18) : Vec 24 :=
  fun j => if h : j.val < 18 then v ⟨j.val, h⟩ else 0

/-- Gauss 律 $A_v = X_v\prod_{e\ni v}X_e$（行向量形态：顶点位 + 关联边的辅助位）。 -/
def bb24Av (v : Fin 4) : Vec 24 :=
  bb24Pad (e (k4Vert v)) + ∑ f : Fin 6,
    (if (k4Ends f).1 = v ∨ (k4Ends f).2 = v then e (k4EdgeSlot f) else 0)

/-- 基码 Z 行的配对边：行 $i$ 与 $\mathrm{supp}(L)$ 的交集恰为一条边的端点对
（`none` = 交集为空）。 -/
def bb24MuZ : Fin 9 → Option (Fin 6) :=
  ![some 2, some 4, some 0, some 5, none, none, some 1, none, some 3]

/-- 变形 Z 行 = 基码行（零填充）⊕ 配对边。 -/
def bb24DzRow (i : Fin 9) : Vec 24 :=
  bb24Pad (bb18Hz i) + match bb24MuZ i with
    | some f => e (k4EdgeSlot f)
    | none => 0

/-- K4 的圈基（三条 flux 检查的边集）。 -/
def k4Cycles : Fin 3 → List (Fin 6) := ![[0, 1, 3], [0, 2, 3, 5], [3, 4, 5]]

/-- flux 检查 $B_p$ = 圈上各边的辅助位之和。 -/
def bb24Bp (p : Fin 3) : Vec 24 :=
  (k4Cycles p).foldr (fun f acc => e (k4EdgeSlot f) + acc) 0

/-- **构造的 X 校验矩阵**：基码 9 行（零填充）+ Gauss 律 4 行。 -/
def bb24HxC : Matrix (Fin 13) (Fin 24) (ZMod 2) := Matrix.of
  ![bb24Pad (bb18Hx 0), bb24Pad (bb18Hx 1), bb24Pad (bb18Hx 2), bb24Pad (bb18Hx 3),
    bb24Pad (bb18Hx 4), bb24Pad (bb18Hx 5), bb24Pad (bb18Hx 6), bb24Pad (bb18Hx 7),
    bb24Pad (bb18Hx 8), bb24Av 0, bb24Av 1, bb24Av 2, bb24Av 3]

/-- **构造的 Z 校验矩阵**：变形 Z 行 9 + flux 3。 -/
def bb24HzC : Matrix (Fin 12) (Fin 24) (ZMod 2) := Matrix.of
  ![bb24DzRow 0, bb24DzRow 1, bb24DzRow 2, bb24DzRow 3, bb24DzRow 4, bb24DzRow 5,
    bb24DzRow 6, bb24DzRow 7, bb24DzRow 8, bb24Bp 0, bb24Bp 1, bb24Bp 2]

/-- **被测的确实是一个逻辑算符**：在核里、不在行空间里，重量恰为 4。 -/
theorem bb18L_logical :
    inKerB bb18Hz bb18L = true ∧ inSpanB bb18Rx bb18L = false ∧ hammingNorm bb18L = 4 := by
  decide

/-- **Gauss 律之和 = 被测逻辑算符**（辅助位成对相消，顶点位留下 $L$）。 -/
theorem bb24_gauss_sum : ∑ v : Fin 4, bb24Av v = bb24Pad bb18L := by
  decide

/-- **构造即字面矩阵（X 侧）**。 -/
theorem bb24HxC_eq : bb24HxC = bb24Hx := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- **构造即字面矩阵（Z 侧）**。 -/
theorem bb24HzC_eq : bb24HzC = bb24Hz := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## 五、结构定理 -/

/-- **测掉的逻辑进入校验行空间**：$L$（零填充）是 gauged 码 X 校验的行组合——
四条 Gauss 律之和。gauging"把逻辑算符提升为校验"在行空间层的字面含义。 -/
theorem bb24L_mem_rowSpace : bb24Pad bb18L ∈ bb24Hx.rowSpace := by
  rw [Matrix.rowSpace_eq_spanL_ofFn, bb24_ofFn_x]
  have h1 : bb24Pad bb18L ∈ spanL [bb24Av 0, bb24Av 1, bb24Av 2, bb24Av 3] := by
    rw [← bb24_gauss_sum]
    refine Submodule.sum_mem _ fun v _ => subset_spanL ?_
    fin_cases v <;> decide
  have hsub : spanL [bb24Av 0, bb24Av 1, bb24Av 2, bb24Av 3] ≤ spanL bb24Rx := by
    refine spanL_mono_of_subset ?_
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | h4
    · decide
    · decide
    · decide
    · rcases h4 with rfl | hnil
      · decide
      · exact nomatch hnil
  exact hsub h1

/-- **配对边确实配对**：有配对边的行，其与 $\mathrm{supp}(L)$ 的交集恰为该边两端点；
无配对边的行交集为空。 -/
theorem bb24_deformZ_matching (i : Fin 9) (f : Fin 6) (h : bb24MuZ i = some f) :
    ∀ b : Fin 18, bb18Hz i b * bb18L b = 1 ↔
      b = k4Vert (k4Ends f).1 ∨ b = k4Vert (k4Ends f).2 := by
  fin_cases i <;> fin_cases f <;> first
    | exact absurd h (by decide)
    | decide

theorem bb24_deformZ_none (i : Fin 9) (h : bb24MuZ i = none) :
    ∀ b : Fin 18, bb18Hz i b * bb18L b = 0 := by
  fin_cases i <;> first
    | exact absurd h (by decide)
    | decide

/-- **flux 与每条 Gauss 律对易**：每个圈在每个顶点的度都是偶数。 -/
theorem bb24_flux_commute : ∀ (p : Fin 3) (v : Fin 4), bb24Bp p ⬝ᵥ bb24Av v = 0 := by
  decide

/-- **构造出的码是 CSS 码**：两套校验逐行正交。 -/
theorem bb24_orth : ∀ i j, bb24Hx i ⬝ᵥ bb24Hz j = 0 := by
  decide

/-- **表示层的维数降（定理路线）**：把 $L$ 追加进基码 X 行列表，
$k$ 恰降一——`deformX_k` 的实例化，假设由内核判定。 -/
theorem bb18_gauged_drop :
    18 - (rowReduce (bb18Rx ++ [bb18L])).length - (rowReduce bb18Rz).length
      = (18 - (rowReduce bb18Rx).length - (rowReduce bb18Rz).length) - 1 :=
  deformX_k ((inSpanB_eq_false_iff bb18Rx bb18L).mp bb18L_logical.2.1)

/-- **gauged 表示层的 $k=3$**：降一落在基码 $k=4$ 上。 -/
theorem bb18_gauged_k :
    18 - (rowReduce (bb18Rx ++ [bb18L])).length - (rowReduce bb18Rz).length = 3 := by
  have h4 := bb18_k
  rw [bb18_ofFn_x, bb18_ofFn_z] at h4
  have h := bb18_gauged_drop
  omega


end QECCertificates
