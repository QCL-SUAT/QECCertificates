/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.CaseMatrix
import QECCertificates.GF2.HGPCompression

/-!
# BB gauging 测量线路的时间型探测码：$|V| = 4$ 条 Gauss 律、$T = 4 = d$ 轮

`Codes/BB24Gauged.lean` 给了 BB $[[18,4,4]]$ 经 $K_4$ 辅助图 gauging 得 $[[24,3,4]]$
的**空间型**实例（$k$ 减一、距离保持）。本模块补它的**线路侧**对偶：把 gauging
**测量线路**的时间型（时空）故障距离算成一个具名、可复算、在内核内判出数值的实例
——与 `Codes/TimeLikeInstance.lean` 的 Bacon–Shor 探测码同形、同一条归约链
（`tools/timelike_server/timelike_sat.py` → `cadical` → `Reflect/LRATDataCircuit.lean`
→ `Reflect/FaithfulCircuit.lean`）。

## 这是 BB gauging 测量线路的哪一部分

gauging 测量 $L$ 的做法是：把 $L$ 分解成 $|V|$ 条 **Gauss 律**
$A_v = X_v\prod_{e \ni v}X_e$（$K_4$ 辅助图，顶点 = $L$ 的 4 个支撑比特），
**每条律各用一个辅助比特测一次**，再把 $|V|$ 个结果相乘得到 $L$ 的读出
（$\prod_v A_v = L$，边比特成对相消，见 `Codes/Gauging.lean` 的
`gauss_prod_eq_vertex_prod`）。本模块取的就是**这一步**：被重复测量的是这 4 条律。

* 校验数 $m = |V| = 4$——由 gauging 结构定死（$K_4$ 的 4 个顶点），不是自由参数；
* 轮数 $T = 4 = d$——$d$ 是 gauged 码 $[[24,3,4]]$ 的码距（`Codes/BB24Gauged.lean`
  的 `bb24_dx` / `bb24_dz`）。取 $T = d$ 使**时间型分量恰为 $d$**，于是与空间型
  分量一起给出"两分量都 $\ge d$"——这正是 `Codes/BaconShorMeasurement.lean` 里
  $T = d = 3$ 那一档的同一件事。

于是 $N = mT = 16$ 个比特、$m(T-1) = 12$ 条探测器，最小不可探测重量 $= T = 4 = d$。

## 主结果

* `bbGauge44_d`：$\min\{\mathrm{wt}(f) : Hf = 0,\ f \neq 0\} = 4$——**两向夹逼**：
  下界走族级定理（见下），上界走显式见证 `bbGauge44W`（第一条律连续 4 轮报错）；
* `bbGauge44_le_weight_of_ker`：下界的**族级定理路线**——核里每个块常值 ⟹ 至少一条律
  的时间轴全非零 ⟹ 该切片重量恰为 $4$ ⟹ 单射拉回给出 $4 \le \mathrm{wt}(f)$，**全程无枚举**；
* `bbGauge44_lightSet_zero`：同一条下界的**第二路证书**（重量限定枚举，候选
  $\sum_{k \le 3}\binom{16}{k} = 697$ 个，`by decide`）——本包"同一断言两条算路"的口径；
* `bbGauge44_ker_slice_const`：**复用族级定理的地方**——把每条律的 4 轮取成切片
  `Vec 4`，逐行正交即得 `Codes/Gauging.lean` 的 `timeLike_eq_of_repCheck` 的前提，
  族级定理直接给出常值性；
* `bbGauge44Checks_rows` / `bbGauge44Checks_prod`：4 条 Gauss 律**逐字钉在**
  `Codes/BB24Gauged.lean` 的 `bb24Hx` 第 $9..12$ 行上，且其乘积恰是 4 个顶点比特的
  指示向量（$L = \prod_v A_v$）——有了这两条，"被重复测量的 4 个算符"才真的是
  gauging 的那 4 条律。

## 诚实边界（本模块**没有**做的事）

1. **没有复现完整规模的线路**：本模块只编码 gauging 测量那一步的 $|V| = 4$ 条 Gauss 律
   的重复测量，**不是**整个 gauged 码 $[[24,3,4]]$ 的 13 条 X 校验 / 12 条 Z 校验的
   完整综合征提取循环。后者若照搬会得到 $m \approx 13$、$N \approx 52$ 的 CNF，
   其内核回放规模超出本包预算（`Codes/BB24Gauged.lean` 的记录：宽 24 上的
   `inSpanB`/`rowReduce` 后端起第 7 行即不收敛）——这一取舍与理由写在
   `tools/timelike_server/timelike_sat.py` 的模块头与 `Reflect/LRATDataCircuit.lean`
   的 `bbgauge44` 档说明里。**这是简化，不是完整线路。**
2. **没有做通用门级线路演算**：本模块的时型结构是"同一校验在相邻两轮的**报告结果**
   之奇偶"这一**现象学**模型（与 `Codes/MeasurementProtocol.lean` 同口径），
   **不含**门级位置（不是逐门电路级仿真），也不含轮内的空间型校验
   （轮内 $\prod_v \sigma_{v,t}$ 那条 Gauss 律乘积是**空间**型分量，属于另一个分量）。
3. **没有把 4 条律与 `Codes/Gauging.lean` 的 `gaussOp` 在索引层桥接**：
   `gaussOp` 用的是 $\mathrm{Fin}\,k \oplus \mathrm{Fin}\,m$ 编号，本模块用的是
   `Codes/BB24Gauged.lean` 的 24 比特编号；两者的**公式**相同、**内容**由
   `bbGauge44Checks_rows` / `bbGauge44Checks_prod` 在 24 比特编号下逐条验明，
   但两个编号之间的形式化桥接没有做。
4. **时间型分量的下界只对"探测器全静默且非零"这一档**：与
   `Codes/TimeLikeInstance.lean` 同口径（`zeroRows`），**不是**
   `Codes/MeasurementProtocol.lean` 里带逻辑泛函 $w \cdot f = 1$ 的 `IsUndetectedFault`
   那一支——这里没有 $w$（gauging 测量的读出是 4 个结果的乘积，在时型链上不构成
   另一条约束）。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 一、被重复测量的 4 条 Gauss 律（钉在 `Codes/BB24Gauged.lean` 上） -/

/-- $K_4$ 的顶点：被提升为稳定子的重量-4 X 型逻辑 $L$ 的 4 个支撑比特
（在 `Codes/BB24Gauged.lean` 的 24 比特编号里，次序为 $K_4$ 的顶点序）。 -/
def bbGauge44Vert : Fin 4 → Fin 24 := ![0, 2, 6, 9]

/-- **4 条 Gauss 律** $A_v = X_v\prod_{e \ni v}X_e$（$K_4$ 辅助图：顶点比特 = `bbGauge44Vert v`，
3 条关联边各配一个辅助比特，编号 $18..23$）。

逐字写法与 `Codes/BB24Gauged.lean` 的 `bb24Hx` 第 $9..12$ 行相同——
`bbGauge44Checks_rows` 把这件事钉成定理。 -/
def bbGauge44Star : Fin 4 → Vec 24 :=
  ![ (e 0 + e 18 + e 19 + e 20 : Vec 24),
     (e 2 + e 18 + e 21 + e 22 : Vec 24),
     (e 6 + e 19 + e 21 + e 23 : Vec 24),
     (e 9 + e 20 + e 22 + e 23 : Vec 24) ]

/-- 4 条 Gauss 律的行列表（gauging 测量每一轮要测的 4 个算符）。 -/
def bbGauge44Checks : List (Vec 24) := List.ofFn bbGauge44Star

/-- **逐字钉在 gauged 码的 X 校验上**：这 4 条律就是 `Codes/BB24Gauged.lean` 的
`bb24Hx` 第 $9..12$ 行——gauging 时追加在原始 $H_X$ 之后的那 4 行。 -/
theorem bbGauge44Checks_rows :
    bbGauge44Checks = (List.ofFn (fun i : Fin 13 => bb24Hx i)).drop 9 := by decide

/-- 每条 Gauss 律的重量恰为 $4 = 1$（顶点）$+\ 3$（$K_4$ 上该顶点的度）。 -/
theorem bbGauge44Star_weight (v : Fin 4) : hammingNorm (bbGauge44Star v) = 4 := by
  fin_cases v <;> decide

/-- **$L = \prod_v A_v$**（`Codes/Gauging.lean` 的 `gauss_prod_eq_vertex_prod` 的实例）：
6 条边比特各出现在两条律里、成对相消，于是 4 条律之和恰是 4 个顶点比特的
指示向量——即被 gauging 提升为稳定子的那个重量-4 逻辑 $L$。

故"把 $|V|$ 条律的读出相乘"确实得到 $L$ 的读出：本模块的 4 条律不是随便挑的 4 个算符。 -/
theorem bbGauge44Checks_prod :
    (∑ v : Fin 4, bbGauge44Star v) = ∑ v : Fin 4, e (bbGauge44Vert v) := by decide

/-! ## 二、时间型探测码（$|V| = 4$ 条律、$T = 4$ 轮） -/

/-- **时间型探测码的校验矩阵**：$12$ 行、$16$ 列。

比特编号 $4v + t$（第 `v` 条 Gauss 律在第 `t` 轮的**报告结果**），
第 $(v,t)$ 行是**同一条律相邻两轮**的一对 $e_{4v+t} + e_{4v+t+1}$——两条相邻轮的
报告结果应当一致，故探测器是它们的奇偶。行序按 $(v,t)$ 字典序。 -/
def bbGauge44H : Matrix (Fin 12) (Fin 16) (ZMod 2) :=
  Matrix.of ![
    e 0 + e 1,   e 1 + e 2,   e 2 + e 3,
    e 4 + e 5,   e 5 + e 6,   e 6 + e 7,
    e 8 + e 9,   e 9 + e 10,  e 10 + e 11,
    e 12 + e 13, e 13 + e 14, e 14 + e 15
  ]

/-- 见证：**第一条 Gauss 律连续 4 轮报告出错**，重量 $4 = T$。

它在核里，且是核里重量最小的非零向量——时间型分量"不可探测时长 = 轮数"的显式算符
（一条律的读出被翻转 $\Rightarrow$ 逻辑读出 $\prod_v$ 被翻转，而所有探测器静默）。 -/
def bbGauge44W : Vec 16 := e 0 + e 1 + e 2 + e 3

/-! ## 三、见证三事实 -/

/-- 在核里：$H w = 0$（每条律的相邻轮读数一致）。 -/
theorem bbGauge44_witness_mem_ker : bbGauge44H *ᵥ bbGauge44W = 0 := by decide

/-- 非零。 -/
theorem bbGauge44_witness_ne_zero : bbGauge44W ≠ 0 := by decide

/-- 重量恰为轮数 $T = 4$。 -/
theorem bbGauge44_witness_weight : hammingNorm bbGauge44W = 4 := by decide

/-- **4 条律各有自己的最小不可探测方向**：每条律的四轮全错都是核向量，
故最小重量的实现有 $|V| = 4$ 个（下界不是靠某个偶然向量撑起来的）。 -/
theorem bbGauge44_block_witnesses :
    (bbGauge44H *ᵥ (e 0 + e 1 + e 2 + e 3 : Vec 16) = 0 ∧
     bbGauge44H *ᵥ (e 4 + e 5 + e 6 + e 7 : Vec 16) = 0 ∧
     bbGauge44H *ᵥ (e 8 + e 9 + e 10 + e 11 : Vec 16) = 0 ∧
     bbGauge44H *ᵥ (e 12 + e 13 + e 14 + e 15 : Vec 16) = 0) := by decide

/-! ## 四、块的索引与切片（复用族级定理的桥） -/

/-- 第 `v` 条律、第 `t` 轮的比特编号：$4v + t$。 -/
def bbGauge44Blk (v : Fin 4) (t : Fin 4) : Fin 16 :=
  ⟨4 * v.val + t.val, by have := v.isLt; have := t.isLt; omega⟩

/-- 第 `(v,i)` 个探测器的行号：$3v + i$。 -/
def bbGauge44RowIdx (v : Fin 4) (i : Fin 3) : Fin 12 :=
  ⟨3 * v.val + i.val, by have := v.isLt; have := i.isLt; omega⟩

/-- 第 `(v,i)` 行的第一个非零列：第 `v` 条律的第 `i` 轮。 -/
def bbGauge44RowL (v : Fin 4) (i : Fin 3) : Fin 16 := bbGauge44Blk v (Fin.castSucc i)

/-- 第 `(v,i)` 行的第二个非零列：第 `v` 条律的第 `i+1` 轮。 -/
def bbGauge44RowR (v : Fin 4) (i : Fin 3) : Fin 16 := bbGauge44Blk v (Fin.succ i)

/-- **第 `v` 条律的时间轴切片**：把 4 轮取值取成 `Vec 4`——
族级定理 `timeLike_eq_of_repCheck` 作用的对象。 -/
def bbGauge44Slice (v : Fin 4) (f : Vec 16) : Vec 4 :=
  fun t => f (bbGauge44Blk v t)

/-- 第 `v` 条律的时间轴是单射（4 个轮次落在 4 个互不相同的比特上）。 -/
theorem bbGauge44Blk_injective (v : Fin 4) : Function.Injective (bbGauge44Blk v) := by
  intro a b h
  have h' : 4 * v.val + a.val = 4 * v.val + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- 校验矩阵的每一行确实是"同一条律相邻两轮"的一对。 -/
theorem bbGauge44H_row (v : Fin 4) (i : Fin 3) :
    bbGauge44H (bbGauge44RowIdx v i)
      = (e (bbGauge44RowL v i) + e (bbGauge44RowR v i) : Vec 16) := by
  fin_cases v <;> fin_cases i <;> decide

/-- 支持集上的点积把 `e i` 读成第 `i` 个分量（`e` 与 `unitVec` 是同一个定义，
故直接搬运 `Codes/Gauging.lean` 的 `unitVec_dot`）。 -/
theorem e_dot {n : ℕ} (i : Fin n) (x : Vec n) : e i ⬝ᵥ x = x i := by
  have h : e i = unitVec i := rfl
  rw [h]
  exact unitVec_dot i x

/-- 逐行正交（`inKerB` 展开成"每一行的点积为零"）。 -/
theorem inKerB_dot_row {k n : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) {f : Vec n}
    (h : inKerB M f = true) (i : Fin k) : M i ⬝ᵥ f = 0 := by
  unfold inKerB at h
  rw [List.all_eq_true] at h
  have hmem : decide (M i ⬝ᵥ f = 0) ∈
      List.ofFn (fun i : Fin k => decide (M i ⬝ᵥ f = 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  simpa using h _ hmem

/-- 探测器"静默"给出块内的相邻轮等式（第 `i` 轮与第 `i+1` 轮读数相同）。 -/
theorem bbGauge44_ker_row_eq {f : Vec 16} (hf : inKerB bbGauge44H f = true)
    (v : Fin 4) (i : Fin 3) :
    f (bbGauge44RowL v i) = f (bbGauge44RowR v i) := by
  have hrow := inKerB_dot_row bbGauge44H hf (bbGauge44RowIdx v i)
  rw [bbGauge44H_row, add_dotProduct, e_dot, e_dot] at hrow
  exact (add_eq_zero_iff_eq _ _).mp hrow

/-- 每个比特都在某条律的时间轴上（$4v + t$ 遍历 $0..15$）。 -/
theorem bbGauge44Blk_surjective :
    ∀ j : Fin 16, ∃ v : Fin 4, ∃ t : Fin 4, j = bbGauge44Blk v t := by
  decide

/-! ## 五、核刻画：把族级定理逐块用上 -/

/-- **核里的向量在每条 Gauss 律的时间轴上取常值**——这是 `Codes/Gauging.lean` 的
族级定理 `timeLike_eq_of_repCheck` 的**块形式**：把第 `v` 条律的 4 轮取成切片
`bbGauge44Slice v f : Vec 4`，逐行正交给出 `repCheck 3 i ⬝ᵥ slice = 0`（相邻轮相等），
族级定理即给出"逐轮取值相同"。

有了它，本实例的下界不再依赖枚举，而是**同一条族级定理**——`Codes/TimeLikeInstance.lean`
的枚举下界与这里互为对账。 -/
theorem bbGauge44_ker_slice_const {f : Vec 16} (hf : inKerB bbGauge44H f = true)
    (v : Fin 4) : ∀ i j : Fin 4, bbGauge44Slice v f i = bbGauge44Slice v f j := by
  refine timeLike_eq_of_repCheck (S := 3) (x := bbGauge44Slice v f) ?_
  intro i
  have hL : bbGauge44Slice v f (Fin.castSucc i) = f (bbGauge44RowL v i) := rfl
  have hR : bbGauge44Slice v f (Fin.succ i) = f (bbGauge44RowR v i) := rfl
  have hrow : f (bbGauge44RowL v i) = f (bbGauge44RowR v i) := bbGauge44_ker_row_eq hf v i
  rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot, hL, hR, hrow]
  exact CharTwo.add_self_eq_zero _

/-- **下界（族级定理路线）**：核里的非零向量重量至少 $T = 4$。

证明只走结构：核里每个块常值 ⟹ 至少一条律的时间轴全非零（否则 $f = 0$）
⟹ 该切片的重量恰为 $4$（`timeLike_weight_eq`）⟹ 由单射拉回重量不超过全向量重量
（`hammingNorm_le_of_injective`）得 $4 \le \mathrm{wt}(f)$。**全程无枚举。** -/
theorem bbGauge44_le_weight_of_ker {f : Vec 16} (hf : inKerB bbGauge44H f = true)
    (hne : f ≠ 0) : 4 ≤ hammingNorm f := by
  have hex : ∃ v : Fin 4, bbGauge44Slice v f ≠ 0 := by
    by_contra h
    push Not at h
    refine hne (funext fun j => ?_)
    obtain ⟨v, t, rfl⟩ := bbGauge44Blk_surjective j
    exact congrFun (h v) t
  obtain ⟨v, hv⟩ := hex
  have hker : ∀ i : Fin 3, repCheck 3 i ⬝ᵥ bbGauge44Slice v f = 0 := by
    intro i
    have hL : bbGauge44Slice v f (Fin.castSucc i) = f (bbGauge44RowL v i) := rfl
    have hR : bbGauge44Slice v f (Fin.succ i) = f (bbGauge44RowR v i) := rfl
    have hrow : f (bbGauge44RowL v i) = f (bbGauge44RowR v i) := bbGauge44_ker_row_eq hf v i
    rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot, hL, hR, hrow]
    exact CharTwo.add_self_eq_zero _
  have hwt : hammingNorm (bbGauge44Slice v f) = 4 := timeLike_weight_eq hker hv
  calc (4 : ℕ) = hammingNorm (bbGauge44Slice v f) := hwt.symm
    _ ≤ hammingNorm f :=
        hammingNorm_le_of_injective (bbGauge44Blk v) (bbGauge44Blk_injective v) f

/-! ## 六、最小不可探测重量 = 轮数 = 码距（两向夹逼） -/

/-- **主断言**：$|V| = 4$ 条 Gauss 律、$T = 4$ 轮的 gauging 测量线路，
最小不可探测时空重量恰为 $4$。

下界走第五节（族级定理，无枚举），上界走显式见证 `bbGauge44W`。 -/
theorem bbGauge44_d : min_weight_ker_not_mem_rowspace bbGauge44H (zeroRows 16) = 4 :=
  eq_minWeight_of_bounds bbGauge44H (zeroRows 16) (by decide) (E := bbGauge44W)
    (mem_ker_of_inKerB bbGauge44H (by decide))
    (not_mem_rowSpace_of_inSpanB_false (zeroRows 16) (by decide))
    (by decide)
    (fun E hker hnot =>
      bbGauge44_le_weight_of_ker ((inKerB_iff bbGauge44H E).mpr hker)
        (fun h0 => hnot (h0 ▸ (zeroRows 16).rowSpace.zero_mem)))

/-- **同一条下界的第二路证书**：重量 $\le 3$ 的候选集为空（重量限定枚举，
$\sum_{k \le 3}\binom{16}{k} = 697$ 个候选，`by decide`）。

与 `bbGauge44_le_weight_of_ker` 的族级定理路线是**两条独立的算路**——本包
"同一断言两条算路"的口径；第三条独立的算路（$2^{16}$ 全空间枚举）在
`tools/timelike_server/verify_timelike.py` 的 Python 侧。 -/
theorem bbGauge44_lightSet_zero : (lightSet bbGauge44H (zeroRows 16) 4).card = 0 := by decide

/-- **时间型分量 = 码距**：$4$ 既是这个测量线路的时间型故障距离，也是 gauged 码
$[[24,3,4]]$ 的码距（`Codes/BB24Gauged.lean` 的 `bb24_dx`）。

取 $T = d$ 轮即得"时间型分量 $\ge d$"，构成 `Codes/BB24Gauged.lean` 那边
空间型实例（$d = 4$ 保持）的线路侧对偶。 -/
theorem bbGauge44_d_eq_codeDistance :
    min_weight_ker_not_mem_rowspace bbGauge44H (zeroRows 16)
      = min_weight_ker_not_mem_rowspace bb24Hx bb24Hz := by
  rw [bbGauge44_d, bb24_dx]

end QECCertificates
