/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.CaseMatrix

/-!
# Bacon–Shor $[[9,1,3]]$：**子系统码**的结构与距离（内核内）

这是本包那条时间轴工作的**表示层地基**：横向测量 Bacon–Shor 的逻辑算符之前，
先要把这个码作为**子系统码**在内核内落地——规范生成元、中心（稳定子）、
裸逻辑、逻辑位数与距离。

## 与稳定子码的两点不同

1. **规范生成元不必两两对易**。这里 X 型取水平边（$X_iX_j$，同一行相邻两比特，
   共 6 条）、Z 型取垂直边（$Z_iZ_j$，同一列相邻两行，共 6 条）；一条水平边与一条
   垂直边若共用一个比特就反对易——实测这样的对恰有 16 对。**这正是"子系统"的含义**：
   规范自由度不是稳定子。所以本模块**不**要求 $H_XH_Z^\top=0$（那是稳定子码的条件）。
2. **计数用 Pauli 群的维数**，不是向量空间的秩。$X$ 型与 $Z$ 型生成元是两个独立的
   辛方向，故 $\operatorname{rank}(\text{gauge}) = r_X + r_Z$（这里 $6+6$），
   而不是把它们当同一批 $F_2^9$ 向量去求秩（那样得 8，会算错 $k$）。
   计数公式：$c = c_X + c_Z$ 为中心秩、$g = (r_X + r_Z - c)/2$ 为规范位数、
   $k = n - c - g$。本模块把 $r_X$、$r_Z$、$c_X$、$c_Z$ **逐条在内核内算出**
   （$6,6,2,2$），于是 $g = 4$、$k = 9-4-4 = 1$。

## 已落地的断言（n = 9，全部 `by decide`）

* `bst_rX` / `bst_rZ`：规范生成元的秩，各为 6；
* `bst_centerX_rank` / `bst_centerZ_rank`：**中心**的秩，各为 2——
  中心的 X 型元素是"相邻两列的全 X 之积"（重量 6），Z 型是"相邻两行的全 Z 之积"，
  实现上是把 $2^9$ 个向量按"在本型规范群内、且与另一型全部生成元对易"筛一遍再求秩；
* `bstSX_mem_ker` / `bstSX_mem_gauge`：X 型稳定子（相邻两列，重量 6）既在另一型的核里
  又在规范群里——所以它是稳定子，不是逻辑；
* `bstXW_mem_ker` / `bstXW_not_mem_gauge`：重量-3 的**裸逻辑**（单列的全 X）在核里、
  不在规范群里；
* `bst_dX` / `bst_dZ`：两侧距离**恰为 3**（下界走重量限定枚举、上界走显式见证）。
  **命名口径的一条例外，写在名字旁边免得后人踩**：这两个名字里的 `bst_dX` 读法是
  **教科书口径**（核取 `bstHz`），而本库其余实例的 `_dx` 一律是 `libDX` 口径（核取
  `Hx`，见 `Codes/DistanceLabel.lean` 的具名约定）——此处两侧同为 3，故数值无差别、
  论文的"两侧读数在本文每个实例上一致"也不受影响。**新写实例时不要照抄这两个名字**，
  要用 `libDX`/`textbookDX` 具名写清是哪一侧。

## 与文献的口径

文献里的 Bacon–Shor $[[9,1,3]]$ 用 $d\times d$ 阵列、$(d-1)\times(d-1)$ 个"面"作
规范生成元；这里用的是**边**算符，两者给出同一个码（本模块的 $k$ 与 $d$ 与文献一致）。
选边算符是因为它让"中心"直接由相邻行/列的整条线生成，证明更短。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、规范生成元（3×3 阵列，比特编号 $q = 3r + c$） -/

/-- **X 型规范生成元**：水平边 $X_iX_j$（同一行相邻两列），6 条。 -/
def bstHx : Matrix (Fin 6) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 3 + e 4, e 4 + e 5, e 6 + e 7, e 7 + e 8]

/-- **Z 型规范生成元**：垂直边 $Z_iZ_j$（同一列相邻两行），6 条。 -/
def bstHz : Matrix (Fin 6) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 3, e 3 + e 6, e 1 + e 4, e 4 + e 7, e 2 + e 5, e 5 + e 8]

/-- 规范生成元的秩（X 型），6。 -/
theorem bst_rX : (rowReduce (List.ofFn fun i => bstHx i)).length = 6 := by decide

/-- 规范生成元的秩（Z 型），6。 -/
theorem bst_rZ : (rowReduce (List.ofFn fun i => bstHz i)).length = 6 := by decide

/-! ## 二、中心（= 稳定子）的秩

中心定义为"在本型规范群里、且与另一型**全部**生成元对易"的元素。
$n = 9$ 时全空间只有 $2^9$ 个向量，直接筛一遍再求秩，比走子模语言短得多。 -/

/-- 中心的 X 型部分：在本型规范群里、与每条 Z 型生成元对易的**非零**向量。 -/
def bstCenterX : List (Vec 9) :=
  (lightVecs 9 9).filter (fun v => decide (
    v ≠ 0 ∧ inSpanB (List.ofFn fun i => bstHx i) v = true ∧
      (List.ofFn fun i => bstHz i).all (fun z => decide (z ⬝ᵥ v = 0))))

/-- 中心的 Z 型部分。 -/
def bstCenterZ : List (Vec 9) :=
  (lightVecs 9 9).filter (fun v => decide (
    v ≠ 0 ∧ inSpanB (List.ofFn fun i => bstHz i) v = true ∧
      (List.ofFn fun i => bstHx i).all (fun z => decide (z ⬝ᵥ v = 0))))

/-- **中心的秩（X 型）= 2**。 -/
theorem bst_centerX_rank : (rowReduce bstCenterX).length = 2 := by decide

/-- **中心的秩（Z 型）= 2**。 -/
theorem bst_centerZ_rank : (rowReduce bstCenterZ).length = 2 := by decide

/-- **计数**：$c = c_X + c_Z = 4$、$g = (r_X+r_Z-c)/2 = 4$、$k = n - c - g = 1$。

左端的每一项都由上面四条内核断言给出（$r_X = r_Z = 6$ 见 `bst_rX`/`bst_rZ`，
$c_X = c_Z = 2$ 见 `bst_centerX_rank`/`bst_centerZ_rank`），故这条是把**已机器检验的
输入**代进公式的算术，而不是一个独立的声明。 -/
theorem bst_k : 9 - (2 + 2) - ((6 + 6 - (2 + 2)) / 2) = 1 := by decide

/-! ## 三、稳定子与裸逻辑 -/

/-- X 型稳定子：相邻两列的全 X 之积（重量 6）。 -/
def bstSX : Vec 9 := e 0 + e 3 + e 6 + e 1 + e 4 + e 7

/-- Z 型稳定子：相邻两行的全 Z 之积（重量 6）。 -/
def bstSZ : Vec 9 := e 0 + e 1 + e 2 + e 3 + e 4 + e 5

/-- X 型裸逻辑的见证：**单列的全 X**（重量 3）。 -/
def bstXW : Vec 9 := e 0 + e 3 + e 6

/-- Z 型裸逻辑的见证：单行的全 Z（重量 3）。 -/
def bstZW : Vec 9 := e 0 + e 1 + e 2

/-- 稳定子与另一型的每条生成元对易（故它落在中心里）。 -/
theorem bstSX_mem_ker : bstHz *ᵥ bstSX = 0 := by decide

/-- 稳定子**在规范群里**——这正是它做不成逻辑的原因。 -/
theorem bstSX_mem_gauge : inSpanB (List.ofFn fun i => bstHx i) bstSX = true := by decide

/-- 裸逻辑与另一型的每条生成元对易。 -/
theorem bstXW_mem_ker : bstHz *ᵥ bstXW = 0 := by decide

/-- 裸逻辑**不在**规范群里。 -/
theorem bstXW_not_mem_gauge : inSpanB (List.ofFn fun i => bstHx i) bstXW = false := by decide

/-! ## 四、两侧距离 $= 3$ -/

/-- **X 型距离**：$\min\{\mathrm{wt}(v) : v\in\ker H_Z,\ v\notin\mathrm{row}\,H_X\} = 3$。

下界走重量限定枚举（重量 $\le2$ 的候选集为空），上界走显式见证 `bstXW`。 -/
theorem bst_dX : min_weight_ker_not_mem_rowspace bstHz bstHx = 3 :=
  eq_minWeight_of_decide (d := 3) bstHz bstHx (by decide) (by decide) (E := bstXW)
    (mem_ker_of_inKerB bstHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false bstHx (by decide))
    (by decide)

/-- **Z 型距离**：对称的一侧。 -/
theorem bst_dZ : min_weight_ker_not_mem_rowspace bstHx bstHz = 3 :=
  eq_minWeight_of_decide (d := 3) bstHx bstHz (by decide) (by decide) (E := bstZW)
    (mem_ker_of_inKerB bstHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false bstHz (by decide))
    (by decide)

end QECCertificates
