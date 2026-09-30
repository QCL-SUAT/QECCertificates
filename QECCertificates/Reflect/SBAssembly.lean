/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.LexLeader

/-!
# 破缺 CNF 的装配：`buildPair` ＋ `lexClauses`

`tools/bb144_server/bb144_sb.py` 产出的破缺 CNF 是**两段的拼接**：基础对编码
（`Reflect/Encode.lean` 的 `buildPair`）＋ 逐群元的词典序比较器块
（`Reflect/LexLeader.lean` 的 `lexClauses`），比较器的辅助变量紧接基础段的变量号之后分配。
本模块把这条装配写成 Lean 的定义 `sbCNF`，并给出它的**可靠性**：

    `SatFormula σ (sbCNF base key imgs c)`
      ⟹  `SatFormula σ base`  ∧  每个群元 `img ∈ imgs` 的 `LexLeOver key img σ`

## 与工具的两个对应

* **辅助变量编号**。工具的 `lex_leader` 每处理一个群元就新分配 `n - 1` 个变量
  （`n = len(key)`；`e 0` 是常量真、不占变量），下一个群元从上一块的末尾接着走。
  `sbBlocks` 的累加参数 `c + (key.length - 1)` 就是这件事。
* **子句条数**。实测量得**每群元 `6n - 6` 条**（沉积 `paper/data/bb144_sb.json` 的
  `sb_clauses_per_elem`：$n = 144$ 给 $858$，$n = 288$ 给 $1722$）。
  下面的 `lexClauses_length` / `sbBlocks_length` 把这条算术证成定理——
  工具的读数与 Lean 的移植落在**同一个式子**上。这不是巧合：`lexClauses` 是
  `lex_leader` 的逐字移植，把四族的条数加起来正是 $4 + 5(n-2) + 1 + (n-1)$。

## 本模块**不做**的那一步（如实标注）

工具的 CNF 是 **Python 拼出来的字节串**；本模块给的是**装配的数学**，
不是"那份字节串等于本定义"。后者要按 `Reflect/Faithful.lean` 的办法把实例 CNF
转录成字面量再 `by decide`（该模块对四个小档做的就是这件事），属另一件事。
**两者都接上，A4 的回放才算闭合**；本模块是其中的前一环，且是**与实例无关**的那一环。
-/

namespace QECCertificates.LRAT

/-! ## 四族的条数（逐族，供上面的算术引用） -/

theorem lexHead_length (key img : List Nat) (c : Nat) : (lexHead key img c).length = 4 := by
  simp [lexHead]

theorem lexStep_length (key img : List Nat) (c i : Nat) : (lexStep key img c i).length = 5 := by
  simp [lexStep]

theorem lexOrder_length (key img : List Nat) : (lexOrder key img).length = 1 := by
  simp [lexOrder]

theorem lexConstraint_length (key img : List Nat) (c i : Nat) :
    (lexConstraint key img c i).length = 1 := by
  simp [lexConstraint]

/-- `flatMap` 到**常条数**的族上：长度等于元素个数乘该常数。 -/
theorem length_flatMap_const {α β : Type*} (f : α → List β) (l : List α) (m : Nat)
    (h : ∀ a, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, h a, ih]
      ring

/-- **比较器的条数**：一族 4 条、一族 $5(n-2)$ 条、一族 1 条、一族 $n-1$ 条，
合计 $6n - 6$——正是沉积里 `sb_clauses_per_elem` 的那个数。 -/
theorem lexClauses_length {key : List Nat} (h2 : 2 ≤ key.length) (img : List Nat) (c : Nat) :
    (lexClauses key img c).length = 6 * key.length - 6 := by
  have hs : ((List.range' 2 (key.length - 2)).flatMap (lexStep key img c)).length
      = (key.length - 2) * 5 := by
    rw [length_flatMap_const (lexStep key img c) _ 5 (fun i => lexStep_length key img c i),
      List.length_range']
  have hc : ((List.range' 1 (key.length - 1)).flatMap (lexConstraint key img c)).length
      = (key.length - 1) * 1 := by
    rw [length_flatMap_const (lexConstraint key img c) _ 1
        (fun i => lexConstraint_length key img c i),
      List.length_range']
  simp only [lexClauses, List.length_append, lexHead_length, lexOrder_length, hs, hc]
  omega

/-! ## 装配 -/

/-- **逐群元的比较器块**：辅助变量号从 `c` 起，每块占 `key.length - 1` 个，下一块接着走。

与工具的对应见模块头。空列表给空 CNF（`--perms` 只挑非单位元，故单位元不在 `imgs` 里）。 -/
def sbBlocks (key : List Nat) : List (List Nat) → Nat → CNF
  | [], _ => []
  | img :: rest, c => lexClauses key img c ++ sbBlocks key rest (c + (key.length - 1))

/-- **破缺 CNF**：基础段 `base` 接上逐群元的比较器块。

工具的调用形态是 `build_from(...)` 得到 `base` 与其变量数 `c`，再对每个群元追加一块；
本定义把"块"与"累加变量号"两件事都显式写出来。 -/
def sbCNF (base : CNF) (key : List Nat) (imgs : List (List Nat)) (c : Nat) : CNF :=
  base ++ sbBlocks key imgs c

theorem sbBlocks_length {key : List Nat} (h2 : 2 ≤ key.length)
    (imgs : List (List Nat)) (c : Nat) :
    (sbBlocks key imgs c).length = imgs.length * (6 * key.length - 6) := by
  induction imgs generalizing c with
  | nil => simp [sbBlocks]
  | cons img rest ih =>
      have hA : 6 * key.length - 6 = 6 * (key.length - 1) := by omega
      simp only [sbBlocks, List.length_append, lexClauses_length h2, List.length_cons]
      rw [ih, hA]
      ring

/-- **装配的条数**：基础段加上每群元 $6n - 6$ 条。

两个 `--perms` 档的读数由此可核：`gens`（2 个生成元、$n = 144$）给基础段 $+\,1716$，
与沉积的 $12238 - 10522 = 1716$ 逐位相同。 -/
theorem sbCNF_length (base : CNF) {key : List Nat} (h2 : 2 ≤ key.length)
    (imgs : List (List Nat)) (c : Nat) :
    (sbCNF base key imgs c).length = base.length + imgs.length * (6 * key.length - 6) := by
  simp [sbCNF, List.length_append, sbBlocks_length h2]

/-! ## 可靠性 -/

/-- 单步：**头与尾是真正的定理变量**，不是归纳的 case 绑定。

这样写是有原因的：`induction … with | cons …` 里，若陈述中的假设也用 `img` 当绑定名
（这里 `hlen` 就是），Lean 会把 case 的头/尾降成**不可及名**（`head✝`/`tail✝`），
`intro` 之后便引用不到。把头和尾提成定理变量，整段就与"case 绑定叫什么"无关了。 -/
theorem sbBlocks_sat_cons {σ : Assign} {key : List Nat} (hd : List Nat) (tl : List (List Nat))
    {c : Nat}
    (hlen : ∀ img ∈ hd :: tl, img.length = key.length)
    (ihh : (∀ img ∈ tl, img.length = key.length) →
        ∀ c, SatFormula σ (sbBlocks key tl c) → ∀ img ∈ tl, LexLeOver key img σ)
    (h : SatFormula σ (sbBlocks key (hd :: tl) c)) :
    ∀ img ∈ hd :: tl, LexLeOver key img σ := by
  intro w hw
  have h' : SatFormula σ (lexClauses key hd c)
      ∧ SatFormula σ (sbBlocks key tl (c + (key.length - 1))) := by
    rw [sbBlocks] at h
    exact satFormula_append.mp h
  rcases List.mem_cons.mp hw with hEq | hmem
  · -- 头那一支：`hEq : w = hd`。**不能用 `subst`**——它会把 `hd` 从上下文里消掉，
    -- 后面再引用就报 "unknown identifier"；`rw` 只改目标、留着 `hd`。
    rw [hEq]
    exact lexClauses_sat (hlen hd (by simp)) h'.1
  · exact ihh (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
      (c + (key.length - 1)) h'.2 w hmem

/-- **每个比较器块都给出它那条词典序断言**。归纳即可：块与块之间只差累加的变量号，
而 `lexClauses_sat` 对**任何**起点 `c` 成立，故累加不影响结论。 -/
theorem sbBlocks_sat {σ : Assign} {key : List Nat} {imgs : List (List Nat)}
    (hlen : ∀ img ∈ imgs, img.length = key.length) :
    ∀ c, SatFormula σ (sbBlocks key imgs c) → ∀ img ∈ imgs, LexLeOver key img σ := by
  induction imgs with
  | nil => intro c h img himg; simp at himg
  | cons =>
      -- `| cons =>` 的头/尾/归纳假设是不可及名，`rename_i` 按位置取出即可；
      -- 头在**任何 `intro` 之前**交给 `sbBlocks_sat_cons`，故不受其影响。
      rename_i hd tl ihh
      intro c
      exact sbBlocks_sat_cons hd tl hlen ihh

/-- **破缺 CNF 的可靠性**（本模块的主定理）：满足破缺编码的赋值，
同时满足基础段与每一条破缺约束。

这就是"破缺 CNF ＝ `buildPair` ＋ `lexClauses`"这条装配在**语义侧**的兑现——
它把两半的可靠性（`Encode.lean` 与 `LexLeader.lean`）拼成一条。 -/
theorem sbCNF_sat {σ : Assign} {base : CNF} {key : List Nat} {imgs : List (List Nat)} {c : Nat}
    (hlen : ∀ img ∈ imgs, img.length = key.length)
    (h : SatFormula σ (sbCNF base key imgs c)) :
    SatFormula σ base ∧ ∀ img ∈ imgs, LexLeOver key img σ := by
  have h' : SatFormula σ base ∧ SatFormula σ (sbBlocks key imgs c) := by
    rw [sbCNF] at h
    exact satFormula_append.mp h
  exact ⟨h'.1, sbBlocks_sat hlen c h'.2⟩

/-- **破缺编码的忠实性（全链）**：满足破缺 CNF 的赋值给出

* 原编码的模型，即经 `buildPair_sat` 翻出的轻逻辑算符（重量 ≤ `k`、两侧核、
  配对为 1——最后两条一起排除了它落在行空间里）；
* 每一条破缺约束的词典序断言（经 `LexLeader.lexClauses_sat` 翻出）。

把 `LexLeOver` 再喂给 `Reflect/SymmetryBreak.lean` 的轨道引理，
就得到"存在**轨道最小**的轻逻辑算符"——即破缺**没有把解切光**。 -/
theorem sbCNF_buildPair_sat {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    {key : List Nat} {imgs : List (List Nat)} {c : Nat}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hlen : ∀ img ∈ imgs, img.length = key.length)
    (h : SatFormula σ (sbCNF (buildPair Rker Rpair n k) key imgs c)) :
    (cntS σ (List.range n) ≤ k ∧
      (∀ r ∈ Rker, dotS σ r = false) ∧
      (∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false) ∧
      dotS (fun t => σ t && σ (n + t)) (List.range n) = true) ∧
    (∀ img ∈ imgs, LexLeOver key img σ) := by
  obtain ⟨hbase, hcmp⟩ := sbCNF_sat hlen h
  exact ⟨buildPair_sat hn hne₁ hne₂ hbase, hcmp⟩

end QECCertificates.LRAT
