/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.Separation
import QECCertificates.Codes.CaseMatrix
import QECCertificates.Codes.BoundaryCollapse

/-!
#  实例：C1 的**双侧反例**（失效侧 / 保距侧）

两个实例都来自最小的环面码族 `toricHx`/`toricHz`（$[[8,2,2]]$，`Codes/CaseMatrix.lean`）。
取定被测 X 逻辑 $L$ 与辅助图 $G$ 后，按 W–Y gauging 构造变形码：

* 数据位 $0..7$ 与原 X 校验 `toricHx` 保留；
* 辅助图顶点 = `supp L`，每条边一个 ancilla（数据位数 $8$ 起编号）；
* Gauss 律 $A_v = X_v\prod_{e\ni v}X_e$ 加入 X 校验；
* 变形 Z 行 = 原 Z 行按各行匹配补上 $Z_e$ + 生成树弦基上的 flux 行。

**本模块的断言全部由内核 `by decide` 复核**（宽度 11 / 14 的小矩阵）：

| 实例 | 辅助图 | C1 | 变形码的两侧距离 | 结论 |
|---|---|---|---|---|
| `sepFail*` | 路径（连通、$h<1$） | ✗ | X 侧 $5$、Z 侧 $1$ | C1 **不可再弱**（失效侧） |
| `sepKeep*` | 连通稀疏图（$h<1$） | ✗ | X 侧 $3$、Z 侧 $2$ | C1 非必要（保距侧） |

**两个实例的两侧距离都不相等**，所以四个数各自成定理（§四），正文引用时按侧具名。
只报一个数会把"有重量 2 的见证"读成"该变形码的距离是 2"，而 Z 侧是 2、X 侧是 3。
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、失效侧：辅助图 $P_4$（违反 C1），变形码出现重量 1 的逻辑 -/

/-- 失效侧变形码的 X 校验（8 行 / 11 比特）（矩阵形态，`inKerB`/`lightSet` 吃矩阵）。 -/
def sepFailHxM : Matrix (Fin 8) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 1 + e 4 + e 6 : Vec 11),
    (0 + e 0 + e 1 + e 5 + e 7 : Vec 11),
    (0 + e 2 + e 3 + e 4 + e 6 : Vec 11),
    (0 + e 2 + e 3 + e 5 + e 7 : Vec 11),
    (0 + e 0 + e 8 + e 9 : Vec 11),
    (0 + e 2 + e 8 : Vec 11),
    (0 + e 4 + e 9 + e 10 : Vec 11),
    (0 + e 5 + e 10 : Vec 11)]

/-- 同一组校验的行列表形态（`inSpanB` 吃行列表）。 -/
def sepFailHx : List (Vec 11) :=
  List.ofFn sepFailHxM

/-- 失效侧变形码的 Z 校验（4 行 / 11 比特）（矩阵形态，`inKerB`/`lightSet` 吃矩阵）。 -/
def sepFailHzM : Matrix (Fin 4) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 2 + e 4 + e 5 + e 8 + e 10 : Vec 11),
    (0 + e 1 + e 3 + e 4 + e 5 + e 10 : Vec 11),
    (0 + e 0 + e 2 + e 6 + e 7 + e 8 : Vec 11),
    (0 + e 1 + e 3 + e 6 + e 7 : Vec 11)]

/-- 同一组校验的行列表形态（`inSpanB` 吃行列表）。 -/
def sepFailHz : List (Vec 11) :=
  List.ofFn sepFailHzM

-- Fail: N=11 V=[0, 2, 4, 5] edges=[(0, 2), (0, 4), (4, 5)] 匹配=[(0, 2), (2,), (0,), ()] C1=False 违反割=([0, 2], 1)
-- 重量 1 的 ker(Hx)：[]；重量 1 的 ker(Hz)：[(9,)]
-- 重量 2 的 ker(Hx)：[]；重量 2 的 ker(Hz)：[(0, 2), (0, 8)]

/-- 保距侧变形码的 X 校验（10 行 / 14 比特）（矩阵形态，`inKerB`/`lightSet` 吃矩阵）。 -/
def sepKeepHxM : Matrix (Fin 10) (Fin 14) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 1 + e 4 + e 6 : Vec 14),
    (0 + e 0 + e 1 + e 5 + e 7 : Vec 14),
    (0 + e 2 + e 3 + e 4 + e 6 : Vec 14),
    (0 + e 2 + e 3 + e 5 + e 7 : Vec 14),
    (0 + e 0 + e 8 + e 9 + e 10 + e 11 : Vec 14),
    (0 + e 1 + e 8 + e 12 : Vec 14),
    (0 + e 2 + e 9 : Vec 14),
    (0 + e 3 + e 10 + e 12 : Vec 14),
    (0 + e 4 + e 11 + e 13 : Vec 14),
    (0 + e 5 + e 13 : Vec 14)]

/-- 同一组校验的行列表形态（`inSpanB` 吃行列表）。 -/
def sepKeepHx : List (Vec 14) :=
  List.ofFn sepKeepHxM

/-- 保距侧变形码的 Z 校验（5 行 / 14 比特）（矩阵形态，`inKerB`/`lightSet` 吃矩阵）。 -/
def sepKeepHzM : Matrix (Fin 5) (Fin 14) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 2 + e 4 + e 5 + e 9 + e 13 : Vec 14),
    (0 + e 1 + e 3 + e 4 + e 5 + e 12 + e 13 : Vec 14),
    (0 + e 0 + e 2 + e 6 + e 7 + e 9 : Vec 14),
    (0 + e 1 + e 3 + e 6 + e 7 + e 12 : Vec 14),
    (0 + e 8 + e 10 + e 12 : Vec 14)]

/-- 同一组校验的行列表形态（`inSpanB` 吃行列表）。 -/
def sepKeepHz : List (Vec 14) :=
  List.ofFn sepKeepHzM

-- Keep: N=14 V=[0, 1, 2, 3, 4, 5] edges=[(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (4, 5)] 匹配=[(1, 5), (4, 5), (1,), (4,)] C1=False 违反割=([4, 5], 1)
-- 重量 1 的 ker(Hx)：[]；重量 1 的 ker(Hz)：[(11,)]
-- 重量 2 的 ker(Hx)：[]；重量 2 的 ker(Hz)：[(0, 2), (0, 9)]

/-! ## 三、内核断言：C1 双侧反例

两条断言链各自闭合：

* **失效侧**：辅助图（4 顶点路径）违反 C1 ⟹ 变形码存在**重量 1** 的逻辑算符
  ⟹ 变形距离 $1 < d = 2$：C1 不可再弱。
* **保距侧**：辅助图（6 顶点连通稀疏图）违反 C1 ⟹ 变形码**没有重量 ≤ 1 的逻辑**
  且有重量 2 的见证 ⟹ 变形距离 $= d = 2$：C1 非必要。

两条结论用的都是**见证所在的那一侧**（$h$ 与距离的对照在两侧同时成立）；两侧的具体
数值见 §四，它们不相等。
-/

/-- **失效侧（C1 判定）**：辅助图是 4 顶点上的路径 ⟹ 膨胀 $<1$。 -/
theorem sepFail_not_C1 :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (2, 3)] : List (Fin 4 × Fin 4)) := by decide

/-- **失效侧（见证）**：变形码存在重量 1 的逻辑算符（比特 9）——
与所有 X 校验正交、且不在 Z 校验的行空间中。 -/
theorem sepFail_lightLogical :
    ∃ v : Vec 11, v ≠ 0 ∧ inKerB sepFailHzM v = true ∧ inSpanB sepFailHx v = false ∧
      hammingNorm v = 1 :=
  ⟨(e 9 : Vec 11), by decide, by decide, by decide, by decide⟩

/-- **失效侧（结论）**：C1 违反 + 变形码存在重量 1 的逻辑 + 基码距离 2
⟹ 变形距离 $1 < 2 = d$：**C1 不可再弱**。 -/
theorem sepFail_summary :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (2, 3)] : List (Fin 4 × Fin 4)) ∧
      (∃ v : Vec 11, v ≠ 0 ∧ inKerB sepFailHzM v = true ∧ inSpanB sepFailHx v = false ∧
        hammingNorm v = 1) ∧
      min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  ⟨sepFail_not_C1, sepFail_lightLogical, toric_dx⟩

/-- **保距侧（C1 判定）**：6 顶点连通稀疏图（割 $\{4,5\}$ 处膨胀 $<1$）。 -/
theorem sepKeep_not_C1 :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (4, 5)] :
      List (Fin 6 × Fin 6)) := by decide

/-- **保距侧（下界）**：变形码没有重量 $\le1$ 的逻辑算符（两侧都查；
候选由重量限定枚举给出，15 个/侧）。 -/
theorem sepKeep_no_lightLogical :
    (lightSet sepKeepHxM sepKeepHzM 2).card = 0 ∧
      (lightSet sepKeepHzM sepKeepHxM 2).card = 0 := by decide

/-- **保距侧（上界）**：变形码有重量 2 的逻辑算符（比特对 $\{0,2\}$）——
与下界合起来给出变形距离 $= 2 = d$：**C1 非必要**。 -/
theorem sepKeep_lightLogical_two :
    ∃ v : Vec 14, v ≠ 0 ∧ inKerB sepKeepHzM v = true ∧ inSpanB sepKeepHx v = false ∧
      hammingNorm v = 2 :=
  ⟨(e 0 + e 2 : Vec 14), by decide, by decide, by decide, by decide⟩

/-- **保距侧（结论）**：C1 违反 + 变形码距离仍 $= d = 2$ ⟹ **C1 不是必要条件**
（与失效侧合起来给出 C1 边界的双侧刻画：$h<1$ 时距离可保可失，
$\min(h,1)\cdot d$ 的界在 $h<1$ 时确实只能给到 $<d$）。 -/
theorem sepKeep_summary :
    ¬ HasExpansionOne ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (4, 5)] :
        List (Fin 6 × Fin 6)) ∧
      (lightSet sepKeepHxM sepKeepHzM 2).card = 0 ∧
      (lightSet sepKeepHzM sepKeepHxM 2).card = 0 ∧
      min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  ⟨sepKeep_not_C1, sepKeep_no_lightLogical.1, sepKeep_no_lightLogical.2, toric_dx⟩

/-! ## 四、两侧距离：两个 C1 见证都是**两侧不等**的变形码

C1 的双侧性由这两个变形码承担，而它们的 X 侧与 Z 侧距离**不相等**。本库的
`Codes/DistanceLabel.lean` 给每个两侧相等的实例留了一条 `_dx_eq_dz`，
**唯独这两个没有**——那一条在这里证不出来。

所以四个数各自成定理，正文引用时按侧具名。只报一个数会把"有重量 2 的见证"
读成"该变形码的距离是 2"，而 Z 侧是 2、X 侧是 3。 -/

/-- **失效侧 X 距离 $=5$**（以 `sepFailHxM` 作核）：下界是重量 $\le4$ 的候选集为空，
上界是比特 $\{0,1,4,6,9\}$ 的重量-5 逻辑算符。 -/
theorem sepFail_dx : min_weight_ker_not_mem_rowspace sepFailHxM sepFailHzM = 5 :=
  eq_minWeight_of_decide (d := 5) sepFailHxM sepFailHzM (by decide) (by decide)
    (E := (e 0 + e 1 + e 4 + e 6 + e 9 : Vec 11))
    (mem_ker_of_inKerB sepFailHxM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepFailHzM (by decide))
    (by decide)

/-- **失效侧 Z 距离 $=1$**（以 `sepFailHzM` 作核）：见证是比特 9；重量 1 已是下限。 -/
theorem sepFail_dz : min_weight_ker_not_mem_rowspace sepFailHzM sepFailHxM = 1 :=
  eq_minWeight_of_decide (d := 1) sepFailHzM sepFailHxM (by decide) (by decide)
    (E := (e 9 : Vec 11))
    (mem_ker_of_inKerB sepFailHzM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepFailHxM (by decide))
    (by decide)

/-- **保距侧 X 距离 $=3$**（以 `sepKeepHxM` 作核）：下界是重量 $\le2$ 的候选集为空，
上界是比特 $\{0,1,8\}$ 的重量-3 逻辑算符。 -/
theorem sepKeep_dx : min_weight_ker_not_mem_rowspace sepKeepHxM sepKeepHzM = 3 :=
  eq_minWeight_of_decide (d := 3) sepKeepHxM sepKeepHzM (by decide) (by decide)
    (E := (e 0 + e 1 + e 8 : Vec 14))
    (mem_ker_of_inKerB sepKeepHxM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepKeepHzM (by decide))
    (by decide)

/-- **保距侧 Z 距离 $=2$**（以 `sepKeepHzM` 作核）：见证是比特对 $\{0,2\}$，
下界即 `sepKeep_no_lightLogical` 的 Z 侧那一半。 -/
theorem sepKeep_dz : min_weight_ker_not_mem_rowspace sepKeepHzM sepKeepHxM = 2 :=
  eq_minWeight_of_decide (d := 2) sepKeepHzM sepKeepHxM (by decide)
    sepKeep_no_lightLogical.2
    (E := (e 0 + e 2 : Vec 14))
    (mem_ker_of_inKerB sepKeepHzM (by decide))
    (not_mem_rowSpace_of_inSpanB_false sepKeepHxM (by decide))
    (by decide)

/-- **失效侧两侧不等**：$5 \ne 1$。 -/
theorem sepFail_dx_ne_dz :
    min_weight_ker_not_mem_rowspace sepFailHxM sepFailHzM ≠
      min_weight_ker_not_mem_rowspace sepFailHzM sepFailHxM := by
  rw [sepFail_dx, sepFail_dz]
  decide

/-- **保距侧两侧不等**：$3 \ne 2$。 -/
theorem sepKeep_dx_ne_dz :
    min_weight_ker_not_mem_rowspace sepKeepHxM sepKeepHzM ≠
      min_weight_ker_not_mem_rowspace sepKeepHzM sepKeepHxM := by
  rw [sepKeep_dx, sepKeep_dz]
  decide

/-! ## 五、失效侧的**机制引理**：零列 ⟹ 距离 1

上面两个实例的"重量 1 逻辑算符"此前是**逐例 `by decide`** 读出来的。本节把它提成
**一般引理**：变形 Z 校验矩阵里**某一列恒零**（那条 ancilla 不被任何 Z 行看见），
而它的单位向量又不在 X 校验的行空间里——则 Z 侧距离 $\le 1$，
配上"零向量不是逻辑算符"即**恰为 $1$**。

这条引理就是 `sepFail` 的机制本身：辅助图的**路径**上，边 $(0,4)$ 落在**任何**有效匹配
之外（把它配掉会剩下 $2$ 与 $5$，而 $2$–$5$ 不是路径的边），于是 ancilla $9$ 的列恒零。
**引理与码无关**：给定矩阵，判据只有两条——列零、不在行空间。 -/

/-- **零列判据**：Z 校验矩阵的某一列恒零 ⟹ 单位向量在该侧的核里。 -/
theorem inKerB_e_of_zero_column {m₁ n : ℕ} (Hz : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (q : Fin n) (hcol : ∀ i, Hz i q = 0) : inKerB Hz (e q) = true := by
  rw [inKerB_iff, mem_ker_iff_dotProd_rows_eq_zero]
  intro i
  rw [dot_e (Hz i) q, hcol i]

/-- **失效侧机制（一般形态）**：Z 校验矩阵的某一列恒零、且该单位向量不在 X 校验的行空间里
⟹ Z 侧距离 $\le 1$。

证明只用一条 witness：那个单位向量**自己**就是重量 $1$ 的不可探测非平凡算符
（`minWeight_le_of_witness`，比逐例 `by decide` 便宜一个量级，且**与码的规模无关**）。 -/
theorem minWeight_le_one_of_zero_column {m₁ m₂ n : ℕ}
    (Hz : Matrix (Fin m₁) (Fin n) (ZMod 2)) (Hx : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (q : Fin n) (hcol : ∀ i, Hz i q = 0) (hnot : e q ∉ Hx.rowSpace) :
    min_weight_ker_not_mem_rowspace Hz Hx ≤ 1 :=
  minWeight_le_of_witness Hz Hx (mem_ker_of_inKerB Hz (inKerB_e_of_zero_column Hz q hcol))
    hnot (hammingNorm_e q)



/-- **失效侧的结构复现**：ancilla $9$（辅助图的边 $(0,4)$）的 Z 列恒零，
   故距离 $\le 1$ 由机制引理直接给出——**不再逐例枚举整个轻算符集合**。

   为什么 $(0,4)$ 的列恒零：变形 Z 行 = 原 Z 行 ＋ 该行在其支撑上的**匹配**，
   而 $\{0,2,4,5\}$ 在这个路径上**只有一种**完美匹配 $\{(0,2),(4,5)\}$
   （把 $0$ 配给 $4$ 会剩下 $2$ 与 $5$，而 $2$–$5$ 不是路径的边），
   于是 $(0,4)$ 落在**任何**行的匹配之外。 -/
theorem sepFail_dist_le_one_structural :
    min_weight_ker_not_mem_rowspace sepFailHzM sepFailHxM ≤ 1 :=
  minWeight_le_one_of_zero_column sepFailHzM sepFailHxM 9
    (by decide) (not_mem_rowSpace_of_inSpanB_false sepFailHxM (by decide))

/-- 同一条结构复现的另一半：那一列**确实**恒零（把上面那条的假设单独留成定理，
   供正文按"零列"这条判据引用）。 -/
theorem sepFail_ancilla_nine_column_zero : ∀ i : Fin 4, sepFailHzM i 9 = 0 := by decide

/-! ## 六、**同一个逻辑上的第二条路径**：C1 不决定结果

上面两个见证用的是**两个不同的**被测逻辑（支撑 $4$ 个顶点与 $6$ 个顶点），所以它们的差别
同时落在 C1 与别处。本节补上**同码、同逻辑**的第二条路径——与失效侧 `sepFail` **共用同一个
被测 X 逻辑**（支撑都是 $\{0,2,4,5\}$），**只换辅助图的连法**：

| | 辅助图 | C1 | Z 侧距离 |
|---|---|---|---|
| `sepFail*` | 路径 $0$–$2$–$4$–$5$ | ✗ | $1$ |
| `sepKeepPath*` | 路径 $0$–$4$–$5$–$2$ | ✗ | $2$ |

**两张图都是 $P_4$**，故 C1 的取值相同（都违反）——**而距离不同**。
于是"失效即塌"**不能**由 C1 单独决定：在同一个码、同一个逻辑、同一个 C1 取值下，
两种结局都出现。决定它的是**匹配**：失效侧那条路径上，边 $(0,4)$ 落在**任何**行的匹配之外
（$\{0,2,4,5\}$ 在该图上只有一种完美匹配），于是 ancilla $9$ 的 Z 列恒零
（`minWeight_le_one_of_zero_column`）。 -/

/-- 保距侧（同逻辑）变形码的 X 校验（8 行 / 11 比特）。 -/
def sepKeepPathHxM : Matrix (Fin 8) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 1 + e 4 + e 6 : Vec 11),
    (0 + e 0 + e 1 + e 5 + e 7 : Vec 11),
    (0 + e 2 + e 3 + e 4 + e 6 : Vec 11),
    (0 + e 2 + e 3 + e 5 + e 7 : Vec 11),
    (0 + e 0 + e 8 : Vec 11),
    (0 + e 2 + e 9 : Vec 11),
    (0 + e 4 + e 8 + e 10 : Vec 11),
    (0 + e 5 + e 9 + e 10 : Vec 11)]

/-- 同一组校验的行列表形态。 -/
def sepKeepPathHx : List (Vec 11) := List.ofFn sepKeepPathHxM

/-- 保距侧（同逻辑）变形码的 Z 校验（4 行 / 11 比特）。 -/
def sepKeepPathHzM : Matrix (Fin 4) (Fin 11) (ZMod 2) :=
  Matrix.of ![(0 + e 0 + e 2 + e 4 + e 5 + e 8 + e 9 : Vec 11),
    (0 + e 1 + e 3 + e 4 + e 5 + e 10 : Vec 11),
    (0 + e 0 + e 2 + e 6 + e 7 : Vec 11),
    (0 + e 1 + e 3 + e 6 + e 7 : Vec 11)]

/-- 同一组校验的行列表形态。 -/
def sepKeepPathHz : List (Vec 11) := List.ofFn sepKeepPathHzM

/-- **保距侧（C1 判定）**：路径 $0$–$4$–$5$–$2$ 同样违反 C1。 -/
theorem sepKeepPath_not_C1 :
    ¬ HasExpansionOne ([(0, 4), (2, 5), (4, 5)] : List (Fin 4 × Fin 4)) := by decide

/-- **保距侧（下界）**：变形码没有重量 $\le 1$ 的逻辑算符（两侧都查）。 -/
theorem sepKeepPath_no_lightLogical :
    (lightSet sepKeepPathHxM sepKeepPathHzM 2).card = 0 ∧
      (lightSet sepKeepPathHzM sepKeepPathHxM 2).card = 0 := by decide

/-- **保距侧（上界）**：变形码有重量 $2$ 的逻辑算符。 -/
theorem sepKeepPath_lightLogical_two :
    ∃ v : Vec 11, v ≠ 0 ∧ inKerB sepKeepPathHzM v = true ∧
      inSpanB sepKeepPathHx v = false ∧ hammingNorm v = 2 :=
  ⟨(e 0 + e 2 : Vec 11), by decide, by decide, by decide, by decide⟩

/-- **保距侧（结论）**：C1 违反，而变形码的 Z 侧距离仍为 $2=d$。 -/
theorem sepKeepPath_summary :
    ¬ HasExpansionOne ([(0, 4), (2, 5), (4, 5)] : List (Fin 4 × Fin 4)) ∧
      (lightSet sepKeepPathHxM sepKeepPathHzM 2).card = 0 ∧
      (lightSet sepKeepPathHzM sepKeepPathHxM 2).card = 0 ∧
      min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  ⟨sepKeepPath_not_C1, sepKeepPath_no_lightLogical.1,
   sepKeepPath_no_lightLogical.2, toric_dx⟩


/-! ## 七、**对照实例**：一个两侧校验各自独立的码

上面两个见证都落在 C4 之外——局部探测器来自**码本身**（环面码四条 X 校验线性相关，乘积是恒等）。
本节的对照是 `[[9,1,3]]` Shor 码：**8 个稳定子生成元（6 个 Z 型 + 2 个 X 型）两两独立**，
故 C4 在它上面成立，它不是"带局部关系"的码。
（这解答了"本仓手上有没有两侧独立的码"：**没建在它上面的实例，但码本身有**。） -/

/-- `[[9,1,3]]` Shor 码的 6 条 Z 型稳定子与 2 条 X 型稳定子（0 基比特编号）。 -/
def shorGenerators : List (Vec 9) :=
  [ (e 0 + e 1 : Vec 9), (e 1 + e 2 : Vec 9), (e 3 + e 4 : Vec 9),
    (e 4 + e 5 : Vec 9), (e 6 + e 7 : Vec 9), (e 7 + e 8 : Vec 9),
    (e 0 + e 1 + e 2 + e 3 + e 4 + e 5 : Vec 9),
    (e 3 + e 4 + e 5 + e 6 + e 7 + e 8 : Vec 9) ]

/-- **对照：两两独立**——每一个生成元都不在其余的行空间里。 -/
theorem shor_generators_independent :
    ∀ r ∈ shorGenerators, inSpanB (shorGenerators.erase r) r = false := by decide


end QECCertificates
