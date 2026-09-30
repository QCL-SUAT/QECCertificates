/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.LRATData

/-!
# 编码忠实性：内核回放的那份 CNF 就是编码器的输出

`Reflect/Encode.lean` 在核内证明了那条编码（`tools/bb144_server/validate_encoding.py`
的 `build_pair`）的**可靠性**：任何满足赋值都给出

* `x` 的重量 ≤ `k`（`cntS` 数真值位）；
* `x` 在核侧行表的核里、`w` 在配对侧行表的核里；
* `x.w = 1`——由它就排除了 `x` 落在配对侧行空间里（行空间 ⊆ (ker)⊥）。

本模块把**两端接起来**：`gen_lrat_lean.py` 搬进内核的那四份 CNF，逐字等于
`buildPair` 作用在同一批行表上的输出（`by decide`，四条等式）。于是

    ¬ Satisfiable <实例>CNF   （LRAT 回放，见 LRATData）
  ＋ <实例>CNF = buildPair <行表>   （本模块）
  ⟹ ¬ Satisfiable (buildPair <行表>)

**方向说明（必须说准）**：`Reflect/Encode.lean` 的 `buildPair_sat` 证的是

    Satisfiable (buildPair <行表>)  ⟹  存在带对偶见证的轻逻辑算符

即"满足赋值 ⟹ 有轻逻辑算符"（等价地，"没有轻逻辑 ⟹ 不可满足"）。而从上面那条
`¬ Satisfiable` 走到"不存在轻逻辑算符"，需要的是它的**反向**：

    存在轻逻辑算符  ⟹  Satisfiable (buildPair <行表>)

即编码不过度约束。这一条**由 `Reflect/Complete.lean` 给出**：把 Tseitin 链、乘积块与
顺序计数器的辅助变量取值构造出来，四段串接成 `buildPair_complete`。于是本模块与
`Reflect.Complete` 合起来给出的是"**可满足 ⟺ 存在轻逻辑算符**"，而它与 LRAT 回放
合起来就使一个不可满足判决**直接给出距离下界**。$[[144,12,12]]$ 的下界另有独立路线
（`Codes/BB144Distance.lean` 走 QECLean 的 Gross 形式化），不依赖这一条。
-/

namespace QECCertificates.LRAT

set_option maxRecDepth 1000000

set_option maxHeartbeats 8000000

/-! ## 四个被回放实例的行表

来源与 `tools/gen_lrat_lean.py` 的 `instances()` 逐字一致：`probeA_engine` 的
`rep_code` / `steane_code` / `cycle`（环面），`tools/bb144_server/test_encoding` 的
`bb18_rows`。行是**列索引表**。 -/

/-- 重复码 $[7,1,7]$ 的核侧行表（6 条奇偶校验）。 -/
def rep7Ker : List (List Nat) := [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6]]

/-- 重复码的配对侧为空（该实例只问"核里的非零向量"）。 -/
def rep7Pair : List (List Nat) := []

/-- Steane $[[7,1,3]]$ 的核侧（Z 型校验）。 -/
def steaneKer : List (List Nat) :=
  [[0, 2, 4, 6], [1, 2, 5, 6], [3, 4, 5, 6]]

/-- Steane 的配对侧（X 型校验）。 -/
def steanePair : List (List Nat) :=
  [[0, 2, 4, 6], [1, 2, 5, 6], [3, 4, 5, 6]]

/-- 环面 $[[18,2,3]]$（三圈矩阵的 HGP）的核侧。 -/
def hgp_toric3Ker : List (List Nat) :=
  [[0, 1, 9, 15], [1, 2, 10, 16], [0, 2, 11, 17],
   [3, 4, 9, 12], [4, 5, 10, 13], [3, 5, 11, 14],
   [6, 7, 12, 15], [7, 8, 13, 16], [6, 8, 14, 17]]

/-- 环面 $[[18,2,3]]$ 的配对侧。 -/
def hgp_toric3Pair : List (List Nat) :=
  [[0, 3, 9, 11], [1, 4, 9, 10], [2, 5, 10, 11],
   [3, 6, 12, 14], [4, 7, 12, 13], [5, 8, 13, 14],
   [0, 6, 15, 17], [1, 7, 15, 16], [2, 8, 16, 17]]

/-- 双变量自行车 $[[18,4,4]]$ 的核侧。 -/
def bb18_lb3Ker : List (List Nat) :=
  [[0, 1, 3, 9, 11, 15], [1, 2, 4, 9, 10, 16], [0, 2, 5, 10, 11, 17],
   [3, 4, 6, 9, 12, 14], [4, 5, 7, 10, 12, 13], [3, 5, 8, 11, 13, 14],
   [0, 6, 7, 12, 15, 17], [1, 7, 8, 13, 15, 16], [2, 6, 8, 14, 16, 17]]

/-- 双变量自行车 $[[18,4,4]]$ 的配对侧。 -/
def bb18_lb3Pair : List (List Nat) :=
  [[0, 1, 3, 9, 11, 15], [1, 2, 4, 9, 10, 16], [0, 2, 5, 10, 11, 17],
   [3, 4, 6, 9, 12, 14], [4, 5, 7, 10, 12, 13], [3, 5, 8, 11, 13, 14],
   [0, 6, 7, 12, 15, 17], [1, 7, 8, 13, 15, 16], [2, 6, 8, 14, 16, 17]]

/-! ## 四条同一性（核内 `decide`） -/

/-- 回放用的重复码 CNF 就是编码器的输出。 -/
theorem rep7_eq : buildPair rep7Ker rep7Pair 7 6 = rep7CNF := by decide

/-- Steane 实例同理。 -/
theorem steane_eq : buildPair steaneKer steanePair 7 2 = steaneCNF := by decide

/-- 环面 $[[18,2,3]]$ 实例同理。 -/
theorem hgp_toric3_eq : buildPair hgp_toric3Ker hgp_toric3Pair 18 2 = hgp_toric3CNF := by decide

/-- 双变量自行车 $[[18,4,4]]$ 实例同理。 -/
theorem bb18_lb3_eq : buildPair bb18_lb3Ker bb18_lb3Pair 18 3 = bb18_lb3CNF := by decide

/-! ## 两端的合成：任何满足赋值都给出一组"轻逻辑算符 + 对偶见证" -/

/-- 重复码实例：满足 `rep7CNF` 的赋值给出重量 ≤ 6 的核向量与配对见证。 -/
theorem rep7_certified {σ : Assign} (h : SatFormula σ rep7CNF) :
    cntS σ (List.range 7) ≤ 6 ∧
    (∀ r ∈ rep7Ker, dotS σ r = false) ∧
    (∀ r ∈ rep7Pair, dotS (fun t => σ (7 + t)) r = false) ∧
    dotS (fun t => σ t && σ (7 + t)) (List.range 7) = true := by
  rw [← rep7_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-- Steane 实例。 -/
theorem steane_certified {σ : Assign} (h : SatFormula σ steaneCNF) :
    cntS σ (List.range 7) ≤ 2 ∧
    (∀ r ∈ steaneKer, dotS σ r = false) ∧
    (∀ r ∈ steanePair, dotS (fun t => σ (7 + t)) r = false) ∧
    dotS (fun t => σ t && σ (7 + t)) (List.range 7) = true := by
  rw [← steane_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-- 环面 $[[18,2,3]]$ 实例。 -/
theorem hgp_toric3_certified {σ : Assign} (h : SatFormula σ hgp_toric3CNF) :
    cntS σ (List.range 18) ≤ 2 ∧
    (∀ r ∈ hgp_toric3Ker, dotS σ r = false) ∧
    (∀ r ∈ hgp_toric3Pair, dotS (fun t => σ (18 + t)) r = false) ∧
    dotS (fun t => σ t && σ (18 + t)) (List.range 18) = true := by
  rw [← hgp_toric3_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-- 双变量自行车 $[[18,4,4]]$ 实例。 -/
theorem bb18_lb3_certified {σ : Assign} (h : SatFormula σ bb18_lb3CNF) :
    cntS σ (List.range 18) ≤ 3 ∧
    (∀ r ∈ bb18_lb3Ker, dotS σ r = false) ∧
    (∀ r ∈ bb18_lb3Pair, dotS (fun t => σ (18 + t)) r = false) ∧
    dotS (fun t => σ t && σ (18 + t)) (List.range 18) = true := by
  rw [← bb18_lb3_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

end QECCertificates.LRAT
