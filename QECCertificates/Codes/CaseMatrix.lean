/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/

import QECCertificates.GF2.LowerBound

/-!
# 案例矩阵：码参数的机器检验断言（端到端）

目标是"**≥ 3 个码族、≥ 10 组码参数**机器检验"。
本模块逐条落实：每个码给出

* **校验矩阵的显式定义**（可计算的具体数据，不是抽象存在性）；
* **维数 `k`**：`n - Σ rank(校验)`，秩由 `rowReduce` 的行数给出（ 的秩证书）；
* **上下界**：下界由 `lightSet` 为空（`by decide`，内核自己枚举全 Pauli 空间）给出，
  上界由一个**显式低重量逻辑算符**给出——`eq_minWeight_of_decide` 两侧一夹，
  即得"码距**恰好**等于 $d$"。

**可信基**：全程只有 `by decide`（内核算），没有 SAT、没有 `native_decide`、
没有自定义公理。

## 三类码的统一接口

| 码类 | `M₁`（提供核） | `M₂`（提供行空间） | 重量 |
|---|---|---|---|
| 经典线性码 | 校验矩阵 `H` | 零行矩阵（`rowSpace = ⊥`） | 非零码字重量 |
| CSS 码 | 一侧校验 | 另一侧校验 | 逻辑算符重量 |
| 一般稳定子码 | 生成元的**辛换位** | 生成元本身 | Pauli 重量 |

## 独立核对

每组参数都由一条独立算路的脚本用暴力枚举复算过一遍（双路对账：脚本只做 GF(2)
位运算，与内核归约完全独立）。**那条脚本不在本仓**——它在姊妹开发里，
路径相对那个仓的根为 `tools/verify_codes.py`（补充材料的 `Numbers` 一段按同一口径
写清了这件事）。
-/

namespace QECCertificates

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000


/-- 辛向量对的拼接：`z` 放前 `n` 位、`x` 放后 `n` 位。

**刻意用 `if`-lambda 而不是 `Fin.append`**：`Fin.append` 的消去规则在内核归约下会被
`Fin.cast`/`Fin.natAdd` 的证明搬运卡住，使 `by decide` 无法归约（实测报
"reduction got stuck"）；写成显式分支后逐坐标归约畅通。 -/
def zx {n : ℕ} (z x : Vec n) : Vec (n + n) :=
  fun i => if h : (i : ℕ) < n then z ⟨i, h⟩ else x ⟨(i : ℕ) - n, by omega⟩

/-- 5 比特情形的辛拼接（把长度参数钉成 5，免得 `?n + ?n = 10` 影响 elaboration）。 -/
abbrev zx5 (z x : Vec 5) : Vec 10 := zx z x

/-! ## 一、重复码族 $[n,1,n]$ -/

/-- $[3,1,3]$ 重复码的校验矩阵。 -/
def rep3H : Matrix (Fin 2) (Fin 3) (ZMod 2) := Matrix.of ![e 0 + e 1, e 1 + e 2]

/-- 全 1 向量（重复码唯一的非零码字）。 -/
def rep3W : Vec 3 := e 0 + e 1 + e 2

theorem rep3_k : 3 - (rowReduce (List.ofFn fun i => rep3H i)).length = 1 := by decide

/-- $[3,1,3]$：码距恰好为 3。 -/
theorem rep3_d : min_weight_ker_not_mem_rowspace rep3H (zeroRows 3) = 3 :=
  eq_minWeight_of_decide (d := 3) rep3H (zeroRows 3) (by decide) (by decide) (E := rep3W)
    (mem_ker_of_inKerB rep3H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 3) (by decide))
    (by decide)

/-- $[5,1,5]$ 重复码的校验矩阵。 -/
def rep5H : Matrix (Fin 4) (Fin 5) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 2 + e 3, e 3 + e 4]

def rep5W : Vec 5 := e 0 + e 1 + e 2 + e 3 + e 4

theorem rep5_k : 5 - (rowReduce (List.ofFn fun i => rep5H i)).length = 1 := by decide

theorem rep5_d : min_weight_ker_not_mem_rowspace rep5H (zeroRows 5) = 5 :=
  eq_minWeight_of_decide (d := 5) rep5H (zeroRows 5) (by decide) (by decide) (E := rep5W)
    (mem_ker_of_inKerB rep5H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 5) (by decide))
    (by decide)

/-- $[7,1,7]$ 重复码的校验矩阵。 -/
def rep7H : Matrix (Fin 6) (Fin 7) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 2 + e 3, e 3 + e 4, e 4 + e 5, e 5 + e 6]

def rep7W : Vec 7 := e 0 + e 1 + e 2 + e 3 + e 4 + e 5 + e 6

theorem rep7_k : 7 - (rowReduce (List.ofFn fun i => rep7H i)).length = 1 := by decide

theorem rep7_d : min_weight_ker_not_mem_rowspace rep7H (zeroRows 7) = 7 :=
  eq_minWeight_of_decide (d := 7) rep7H (zeroRows 7) (by decide) (by decide) (E := rep7W)
    (mem_ker_of_inKerB rep7H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 7) (by decide))
    (by decide)

/-! ## 二、经典 Hamming 码族

校验矩阵的列是位置编号（1 起）的二进制写法；这正是"任意两列线性无关、
但存在三列线性相关"的构造，故最小距离恰为 3。 -/

/-- $[7,4,3]$ Hamming 码的校验矩阵（列 = 1…7 的二进制）。 -/
def ham7H : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 4 + e 6, e 1 + e 2 + e 5 + e 6, e 3 + e 4 + e 5 + e 6]

/-- 重量 3 的码字（1…3 号列之和为零）。 -/
def ham7W : Vec 7 := e 0 + e 1 + e 2

theorem ham7_k : 7 - (rowReduce (List.ofFn fun i => ham7H i)).length = 4 := by decide

theorem ham7_d : min_weight_ker_not_mem_rowspace ham7H (zeroRows 7) = 3 :=
  eq_minWeight_of_decide (d := 3) ham7H (zeroRows 7) (by decide) (by decide) (E := ham7W)
    (mem_ker_of_inKerB ham7H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 7) (by decide))
    (by decide)

/-- $[15,11,3]$ Hamming 码的校验矩阵（列 = 1…15 的二进制）。

$n = 15$ 是重量限定枚举的**第一个报捷点**：全空间枚举下这条
超过三分钟未完成，改用 `lightVecs 15 2`（121 个候选而不是 32768 个）后秒级通过。 -/
def ham15H : Matrix (Fin 4) (Fin 15) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 4 + e 6 + e 8 + e 10 + e 12 + e 14,
              e 1 + e 2 + e 5 + e 6 + e 9 + e 10 + e 13 + e 14,
              e 3 + e 4 + e 5 + e 6 + e 11 + e 12 + e 13 + e 14,
              e 7 + e 8 + e 9 + e 10 + e 11 + e 12 + e 13 + e 14]

def ham15W : Vec 15 := e 0 + e 1 + e 2

theorem ham15_k : 15 - (rowReduce (List.ofFn fun i => ham15H i)).length = 11 := by decide

theorem ham15_d : min_weight_ker_not_mem_rowspace ham15H (zeroRows 15) = 3 :=
  eq_minWeight_of_decide (d := 3) ham15H (zeroRows 15) (by decide) (by decide) (E := ham15W)
    (mem_ker_of_inKerB ham15H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 15) (by decide))
    (by decide)

/-! ## 三、Steane 码 $[[7,1,3]]$（量子 Hamming）

$H_X = H_Z = $ Hamming $[7,4,3]$ 的校验矩阵。两侧同矩阵时
`dX = f(H₂,H₁)` 与 `dZ = f(H₁,H₂)` 是同一个数。 -/

def steaneHx : Matrix (Fin 3) (Fin 7) (ZMod 2) := ham7H

def steaneHz : Matrix (Fin 3) (Fin 7) (ZMod 2) := ham7H

/-- 重量 3 的逻辑算符（X 型与 Z 型共用同一个见证：Steane 码的 X/Z 对称性）。 -/
def steaneW : Vec 7 := e 0 + e 1 + e 2

theorem steane_k : 7 - (rowReduce (List.ofFn fun i => steaneHx i)).length
    - (rowReduce (List.ofFn fun i => steaneHz i)).length = 1 := by decide

theorem steane_dx : min_weight_ker_not_mem_rowspace steaneHx steaneHz = 3 :=
  eq_minWeight_of_decide (d := 3) steaneHx steaneHz (by decide) (by decide) (E := steaneW)
    (mem_ker_of_inKerB steaneHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false steaneHz (by decide))
    (by decide)

theorem steane_dz : min_weight_ker_not_mem_rowspace steaneHz steaneHx = 3 :=
  eq_minWeight_of_decide (d := 3) steaneHz steaneHx (by decide) (by decide) (E := steaneW)
    (mem_ker_of_inKerB steaneHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false steaneHx (by decide))
    (by decide)

/-! ## 四、Shor 码 $[[9,1,3]]$（三级级联）

9 个比特分 3 块。Z 型校验：块内相邻比特的 `ZZ`（6 条）；
X 型校验：整块的 `XXXXXX`（首两块、后两块，共 2 条）。 -/

def shorHx : Matrix (Fin 2) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 1 + e 2 + e 3 + e 4 + e 5, e 3 + e 4 + e 5 + e 6 + e 7 + e 8]

def shorHz : Matrix (Fin 6) (Fin 9) (ZMod 2) :=
  Matrix.of ![e 0 + e 1, e 1 + e 2, e 3 + e 4, e 4 + e 5, e 6 + e 7, e 7 + e 8]

/-- `dX` 的见证：每块取一个比特（"跨块"算符），重量 3。 -/
def shorXW : Vec 9 := e 0 + e 3 + e 6

/-- `dZ` 的见证：整块翻转，重量 3。 -/
def shorZW : Vec 9 := e 0 + e 1 + e 2

theorem shor_k : 9 - (rowReduce (List.ofFn fun i => shorHx i)).length
    - (rowReduce (List.ofFn fun i => shorHz i)).length = 1 := by decide

theorem shor_dx : min_weight_ker_not_mem_rowspace shorHx shorHz = 3 :=
  eq_minWeight_of_decide (d := 3) shorHx shorHz (by decide) (by decide) (E := shorXW)
    (mem_ker_of_inKerB shorHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false shorHz (by decide))
    (by decide)

theorem shor_dz : min_weight_ker_not_mem_rowspace shorHz shorHx = 3 :=
  eq_minWeight_of_decide (d := 3) shorHz shorHx (by decide) (by decide) (E := shorZW)
    (mem_ker_of_inKerB shorHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false shorHx (by decide))
    (by decide)

/-! ## 五、$[[4,2,2]]$ 码

$H_X = H_Z = (1,1,1,1)$：唯一的校验是全体宇称，故码字重量必为偶数；
重量 2 的码字（如 `e₀+e₁`）不是校验本身，故距离恰为 2。 -/

def fourHx : Matrix (Fin 1) (Fin 4) (ZMod 2) := Matrix.of ![e 0 + e 1 + e 2 + e 3]

def fourHz : Matrix (Fin 1) (Fin 4) (ZMod 2) := Matrix.of ![e 0 + e 1 + e 2 + e 3]

def fourW : Vec 4 := e 0 + e 1

theorem four_k : 4 - (rowReduce (List.ofFn fun i => fourHx i)).length
    - (rowReduce (List.ofFn fun i => fourHz i)).length = 2 := by decide

theorem four_dx : min_weight_ker_not_mem_rowspace fourHx fourHz = 2 :=
  eq_minWeight_of_decide (d := 2) fourHx fourHz (by decide) (by decide) (E := fourW)
    (mem_ker_of_inKerB fourHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false fourHz (by decide))
    (by decide)

theorem four_dz : min_weight_ker_not_mem_rowspace fourHz fourHx = 2 :=
  eq_minWeight_of_decide (d := 2) fourHz fourHx (by decide) (by decide) (E := fourW)
    (mem_ker_of_inKerB fourHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false fourHx (by decide))
    (by decide)

/-! ## 六、环面码 $[[8,2,2]]$（$2\times 2$ 环面，拓扑码族）

8 条边（4 横 4 纵），顶点星算符为 X 型、面算符为 Z 型，各 4 条。
$2\times2$ 环面上横/纵桁架成对平行，故最短非平凡回路长度为 2。 -/

def toricHz : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 4 + e 5, e 1 + e 3 + e 4 + e 5,
              e 0 + e 2 + e 6 + e 7, e 1 + e 3 + e 6 + e 7]

def toricHx : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  Matrix.of ![e 0 + e 1 + e 4 + e 6, e 0 + e 1 + e 5 + e 7,
              e 2 + e 3 + e 4 + e 6, e 2 + e 3 + e 5 + e 7]

/-- 一对平行边构成的非平凡回路。 -/
def toricXW : Vec 8 := e 0 + e 1

/-- 另一方向的平行边对。 -/
def toricZW : Vec 8 := e 0 + e 2

theorem toric_k : 8 - (rowReduce (List.ofFn fun i => toricHx i)).length
    - (rowReduce (List.ofFn fun i => toricHz i)).length = 2 := by decide

theorem toric_dx : min_weight_ker_not_mem_rowspace toricHx toricHz = 2 :=
  eq_minWeight_of_decide (d := 2) toricHx toricHz (by decide) (by decide) (E := toricXW)
    (mem_ker_of_inKerB toricHx (by decide))
    (not_mem_rowSpace_of_inSpanB_false toricHz (by decide))
    (by decide)

theorem toric_dz : min_weight_ker_not_mem_rowspace toricHz toricHx = 2 :=
  eq_minWeight_of_decide (d := 2) toricHz toricHx (by decide) (by decide) (E := toricZW)
    (mem_ker_of_inKerB toricHz (by decide))
    (not_mem_rowSpace_of_inSpanB_false toricHx (by decide))
    (by decide)

/-- **环面码 $[[18,2,3]]$**（$3\\times 3$ 环面，拓扑码族）：18 条边。

$n = 18$ 是重量限定枚举推进到的**前沿**——全空间枚举
（$2^{18} = 262144$）不可行，而 `lightVecs 18 2` 只有 172 个候选。 -/
def toric3Hz : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of ![e 0 + e 3 + e 9 + e 10, e 1 + e 4 + e 10 + e 11, e 2 + e 5 + e 9 + e 11,
              e 3 + e 6 + e 12 + e 13, e 4 + e 7 + e 13 + e 14, e 5 + e 8 + e 12 + e 14,
              e 0 + e 6 + e 15 + e 16, e 1 + e 7 + e 16 + e 17, e 2 + e 8 + e 15 + e 17]

def toric3Hx : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of ![e 0 + e 2 + e 9 + e 15, e 0 + e 1 + e 10 + e 16, e 1 + e 2 + e 11 + e 17,
              e 3 + e 5 + e 9 + e 12, e 3 + e 4 + e 10 + e 13, e 4 + e 5 + e 11 + e 14,
              e 6 + e 8 + e 12 + e 15, e 6 + e 7 + e 13 + e 16, e 7 + e 8 + e 14 + e 17]

/-- `toric3Hz` 的行列表形态。

**为什么需要它**：`rowReduce` 在宽 18 矩阵上的内核归约代价主要来自
`Matrix.of`/`List.ofFn` 的索引层——同一消元在纯 `List` 形态下约 95 秒完成，
在 `Matrix.of ![…]` + `ofFn` 层下 5 分钟仍烧穿心跳预算。`k` 的秩断言因此
改走"行列表 + 桥接等式"（`toric3_ofFn_hz`/`toric3_ofFn_hx` + `toric3_k`）。 -/
def toric3Rz : List (Vec 18) :=
  [e 0 + e 3 + e 9 + e 10, e 1 + e 4 + e 10 + e 11, e 2 + e 5 + e 9 + e 11,
   e 3 + e 6 + e 12 + e 13, e 4 + e 7 + e 13 + e 14, e 5 + e 8 + e 12 + e 14,
   e 0 + e 6 + e 15 + e 16, e 1 + e 7 + e 16 + e 17, e 2 + e 8 + e 15 + e 17]

/-- `toric3Hx` 的行列表形态（同上）。 -/
def toric3Rx : List (Vec 18) :=
  [e 0 + e 2 + e 9 + e 15, e 0 + e 1 + e 10 + e 16, e 1 + e 2 + e 11 + e 17,
   e 3 + e 5 + e 9 + e 12, e 3 + e 4 + e 10 + e 13, e 4 + e 5 + e 11 + e 14,
   e 6 + e 8 + e 12 + e 15, e 6 + e 7 + e 13 + e 16, e 7 + e 8 + e 14 + e 17]

/-- 行列表与矩阵形态逐行一致（纯索引比对，内核毫秒级）。

**括号不可省**：`fun i => toric3Hz i = toric3Rz` 的 lambda 体会计较到整个等式。 -/
theorem toric3_ofFn_hz : (List.ofFn fun i => toric3Hz i) = toric3Rz := by decide

/-- 同上（`Hx` 侧）。 -/
theorem toric3_ofFn_hx : (List.ofFn fun i => toric3Hx i) = toric3Rx := by decide

set_option maxHeartbeats 40000000 in
/-- **维数 $k = 2$**：$18 - \operatorname{rank}(H_x) - \operatorname{rank}(H_z)$，两侧秩都是 8
（每条边恰属两个面，9 行校验相加为零，且任意 8 行独立）。

先 `rw` 桥接等式把 `List.ofFn` 层换成纯行列表，再 `decide`——
纯 `List` 形态约 95 秒，比直接在 `ofFn` 形态上 `decide`（5 分钟超时）快 3 倍以上；
心跳逐定理放宽到 40M（模块默认 8M 不够）。 -/
theorem toric3_k : 18 - (rowReduce (List.ofFn fun i => toric3Hx i)).length
    - (rowReduce (List.ofFn fun i => toric3Hz i)).length = 2 := by
  rw [toric3_ofFn_hx, toric3_ofFn_hz]
  decide

/-- 绕环面一周的短路（3 条边）。 -/
def toric3XW : Vec 18 := e 0 + e 1 + e 2

/-- 另一方向的短路。 -/
def toric3ZW : Vec 18 := e 0 + e 3 + e 6

theorem toric3_dx : min_weight_ker_not_mem_rowspace toric3Hx toric3Hz = 3 :=
  eq_minWeight_of_decide (d := 3) toric3Hx toric3Hz (by decide) (by decide) (E := toric3XW)
    (mem_ker_of_inKerB toric3Hx (by decide))
    (not_mem_rowSpace_of_dualCheck toric3Hz (w := toric3ZW) (by decide) (by decide))
    (by decide)

theorem toric3_dz : min_weight_ker_not_mem_rowspace toric3Hz toric3Hx = 3 :=
  eq_minWeight_of_decide (d := 3) toric3Hz toric3Hx (by decide) (by decide) (E := toric3ZW)
    (mem_ker_of_inKerB toric3Hz (by decide))
    (not_mem_rowSpace_of_dualCheck toric3Hx (w := toric3XW) (by decide) (by decide))
    (by decide)

/-! ## 七、$[[5,1,3]]$ 完美码（非 CSS，走辛层）

$[[5,1,3]]$ 是唯一能纠正单比特错误的非退化 5 比特码，且**不是 CSS 码**——
它必须走一般的辛表示。编码方式：生成元写成 `(Z 半, X 半)` 拼接的 10 位向量 `g`，
法向条件 `⟨g, v⟩ = 0` 等价于"`v` 与 `J g` 正交"，其中 `J` 交换两半；
于是 `d = f(J 的行矩阵, 生成元矩阵)`，`k = n − rank(G)`。

生成元（标准形式）：
`X Z Z X I`、`I X Z Z X`、`X I X Z Z`、`Z X I X Z`。 -/

/-- 生成元矩阵：第 `i` 行 = `zx (Z 半) (X 半)`。 -/
def p5G : Matrix (Fin 4) (Fin 10) (ZMod 2) :=
  Matrix.of ![zx5 (e 1 + e 2) (e 0 + e 3),
              zx5 (e 2 + e 3) (e 1 + e 4),
              zx5 (e 3 + e 4) (e 0 + e 2),
              zx5 (e 0 + e 4) (e 1 + e 3)]

/-- 辛换位矩阵：第 `i` 行 = 生成元 `i` 交换两半（`Z 半` 与 `X 半` 对调）。 -/
def p5J : Matrix (Fin 4) (Fin 10) (ZMod 2) :=
  Matrix.of ![zx5 (e 0 + e 3) (e 1 + e 2),
              zx5 (e 1 + e 4) (e 2 + e 3),
              zx5 (e 0 + e 2) (e 3 + e 4),
              zx5 (e 1 + e 3) (e 0 + e 4)]

/-- 重量 3 的逻辑算符（`Z` 半重量 2、`X` 半重量 1）。 -/
def p5W : Vec 10 := zx5 (e 1 + e 4) (e 0)

/-- **生成元两两对易**：`J` 的每一行与 `G` 的每一行正交（辛对易 = 普通正交）。 -/
theorem p5_pairwise_commute : ∀ i j : Fin 4, (p5J i) ⬝ᵥ (p5G j) = 0 := by decide

/-- $k = n - \operatorname{rank}(G)$：4 个独立生成元 ⟹ 1 个逻辑比特。 -/
theorem p5_k : 5 - (rowReduce (List.ofFn fun i => p5G i)).length = 1 := by decide

/-- $[[5,1,3]]$：码距恰好为 3。 -/
theorem p5_d : min_weight_ker_not_mem_rowspace p5J p5G = 3 :=
  eq_minWeight_of_decide (d := 3) p5J p5G (by decide) (by decide) (E := p5W)
    (mem_ker_of_inKerB p5J (by decide))
    (not_mem_rowSpace_of_inSpanB_false p5G (by decide))
    (by decide)

/-! ## 案例矩阵汇总

| 码 | $n$ | $k$ | $d$ | 族 |
|---|---|---|---|---|
| `rep3_d` | 3 | 1 | 3 | 重复码 |
| `rep5_d` | 5 | 1 | 5 | 重复码 |
| `rep7_d` | 7 | 1 | 7 | 重复码 |
| `ham7_d` | 7 | 4 | 3 | 经典 Hamming |
| `ham15_d` | 15 | 11 | 3 | 经典 Hamming |
| `steane_dx`/`steane_dz` | 7 | 1 | 3 | 量子 Hamming（CSS） |
| `shor_dx`/`shor_dz` | 9 | 1 | 3 | 级联（CSS） |
| `four_dx`/`four_dz` | 4 | 2 | 2 | 小 CSS |
| `toric_dx`/`toric_dz` | 8 | 2 | 2 | 拓扑（$2\times2$ 环面） |
| `toric3_k`/`toric3_dx`/`toric3_dz` | 18 | 2 | 3 | 拓扑（$3\times3$ 环面） |
| `p5_d` | 5 | 1 | 3 | 完美码（非 CSS） |

共 **7 个码族、16 组码参数**。

$3\times3$ 环面码（$n = 18$）的**全参数** $[[18,2,3]]$ 均已机器检验。宽矩阵上有两条
工程路线缺一不可：**码距上界**走**对偶见证**（`not_mem_rowSpace_of_dualCheck`，
零行消元，把整文件从 304 s 压到 16 s）；**秩/`k`** 走**行列表桥接**
（`Matrix.of`/`List.ofFn` 索引层下 5 分钟超时，纯 `List` 形态约 95 s）。 -/

end QECCertificates
