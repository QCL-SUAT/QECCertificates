/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.LRAT
import QECCertificates.Reflect.SymmetryBreak

/-!
# 词典序比较器子句的可靠性（A3 的 CNF 层）

`Reflect/SymmetryBreak.lean` 证的是**语义**：若破缺谓词可满足则原谓词可满足。
要把工具生成的那份 **CNF** 接上，还差一条：

    `SatFormula σ (lexClauses key img c)  ⟹  key ≤_lex img`

本模块给出它——把 `tools/bb144_server/bb144_sb.py` 的 `lex_leader` 逐字移植成 Lean 的
子句生成器 `lexClauses`，并证明**每条子句都被满足 ⟹ 比较器断言的词典序成立**。

## 编码回顾（与工具的 `lex_leader` 一一对应）

设比较向量有 `n` 位，`key i` 是第 `i` 位的变量号、`img i` 是它在 `g·v` 下的取值来源
（工具那边传的是置换的**逆**，于是 `img i` 正是 `(g·v)_i`）。辅助变量 `e i`（`1 ≤ i`）断言
"前 `i` 位相等"，`e 0` 是常量真、不分配变量。子句四族：

| 族 | 条数 | 子句 |
|---|---|---|
| `lexHead` | 4 | 定义 `e 1 ↔ (key 0 ↔ img 0)` |
| `lexStep i`（`2 ≤ i < n`） | 5 | 定义 `e i ↔ (e (i-1) ∧ (key (i-1) ↔ img (i-1)))` |
| `lexOrder` | 1 | `¬key 0 ∨ img 0`（`i = 0` 处没有 `e`） |
| `lexConstraint i`（`1 ≤ i < n`） | 1 | `¬e i ∨ ¬key i ∨ img i` |

四条/五条的那两族合起来**恰好**定义 `e`（不多不少），这正是"编码不过紧"的地方；
`Reflect/SymmetryBreak.lean` 的 `⟸` 半边要的就是它。末族禁止"前缀相等且 `key i = 1,
img i = 0`"，即禁止 `key >_lex img` 的唯一形状。

## 结论的形态

`LexLe v w` 写成"存在使 `v >_lex w` 的那种位置不存在"：

    ∀ i, (前缀相等) → v i = true → w i = true

它与族 3/4 的子句逐字对应，因此证明是**顺着子句走**而不是顺着序关系走。
-/

namespace QECCertificates.LRAT

/-! ## 文字量与词典序 -/

/-- 正文字面量（变量取真）。 -/
def pos (v : Nat) : Lit := (v, true)

/-- 负文字面量（变量取假）。 -/
def neg (v : Nat) : Lit := (v, false)

/-- 比较器辅助变量 `e i`（`i ≥ 1`）的变量号；`e 0` 是常量真、不分配。 -/
def eVar (c i : Nat) : Nat := c + (i - 1)

/-- 向量 `v` 的第 `i` 位；越界取 `0`（调用方带界，故不触发）。 -/
def idx (v : List Nat) (i : Nat) : Nat := v.getD i 0

/-- **词典序 `≤`**：不存在"前缀相等、`v` 为真而 `w` 为假"的位置。

用这个形态而不是递归定义，是因为它与 `lexConstraint` 的子句逐字对应——
证明顺着子句走。 -/
def LexLe (v w : List Bool) : Prop :=
  ∀ i, (∀ j, j < i → v.getD j false = w.getD j false) →
    v.getD i false = true → w.getD i false = true

/-! ## 逐族的子句（与 `lex_leader` 逐字对应） -/

/-- 族 1：定义 `e 1 ↔ (key 0 ↔ img 0)`（4 条）。 -/
def lexHead (key img : List Nat) (c : Nat) : CNF :=
  [[neg (eVar c 1), neg (idx key 0), pos (idx img 0)],
   [neg (eVar c 1), pos (idx key 0), neg (idx img 0)],
   [neg (idx key 0), neg (idx img 0), pos (eVar c 1)],
   [pos (idx key 0), pos (idx img 0), pos (eVar c 1)]]

/-- 族 2：定义 `e i ↔ (e (i-1) ∧ (key (i-1) ↔ img (i-1)))`（5 条）。 -/
def lexStep (key img : List Nat) (c i : Nat) : CNF :=
  [[neg (eVar c i), pos (eVar c (i - 1))],
   [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))],
   [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))],
   [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)), pos (eVar c i)],
   [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)), pos (eVar c i)]]

/-- 族 3：`¬key 0 ∨ img 0`。 -/
def lexOrder (key img : List Nat) : CNF :=
  [[neg (idx key 0), pos (idx img 0)]]

/-- 族 4：`¬e i ∨ ¬key i ∨ img i`。 -/
def lexConstraint (key img : List Nat) (c i : Nat) : CNF :=
  [[neg (eVar c i), neg (idx key i), pos (idx img i)]]

/-- **比较器的全部子句**（`lex_leader` 的逐字移植）。 -/
def lexClauses (key img : List Nat) (c : Nat) : CNF :=
  lexHead key img c
  ++ (List.range' 2 (key.length - 2)).flatMap (lexStep key img c)
  ++ lexOrder key img
  ++ (List.range' 1 (key.length - 1)).flatMap (lexConstraint key img c)

/-! ## 两个组合子句的小引理

族 1 与族 2 的从句都是"定义某个 `e` 等于一个布尔组合"。先把这两种组合抽成引理，
后面归纳时就不必反复展开子句。 -/

/-- 把 `SatClause` 在三个字面量上的展开写成布尔析取，后面的引理都从这里起步。 -/
theorem satClause_three {σ : Assign} {x y z : Nat} {sx sy sz : Bool}
    (h : SatClause σ [(x, sx), (y, sy), (z, sz)]) :
    σ x = sx ∨ σ y = sy ∨ σ z = sz := by
  simpa [SatClause] using h

/-- 四字面量同上。 -/
theorem satClause_four {σ : Assign} {w x y z : Nat} {sw sx sy sz : Bool}
    (h : SatClause σ [(w, sw), (x, sx), (y, sy), (z, sz)]) :
    σ w = sw ∨ σ x = sx ∨ σ y = sy ∨ σ z = sz := by
  simpa [SatClause] using h

/-- 单字面量同上。 -/
theorem satClause_one {σ : Assign} {x : Nat} {sx : Bool}
    (h : SatClause σ [(x, sx)]) : σ x = sx := by
  simpa [SatClause] using h

/-- 双字面量同上。 -/
theorem satClause_two {σ : Assign} {x y : Nat} {sx sy : Bool}
    (h : SatClause σ [(x, sx), (y, sy)]) : σ x = sx ∨ σ y = sy := by
  simpa [SatClause] using h

/-- **族 1 的可靠性**：四条子句合起来恰好定义 `e ↔ (a ↔ b)`。 -/
theorem head_iff {σ : Assign} {a b e : Nat}
    (h1 : SatClause σ [neg e, neg a, pos b])
    (h2 : SatClause σ [neg e, pos a, neg b])
    (h3 : SatClause σ [neg a, neg b, pos e])
    (h4 : SatClause σ [pos a, pos b, pos e]) :
    σ e = true ↔ σ a = σ b := by
  rcases satClause_three (σ := σ) h1 with h | h | h <;>
  rcases satClause_three (σ := σ) h2 with h' | h' | h' <;>
  rcases satClause_three (σ := σ) h3 with h'' | h'' | h'' <;>
  rcases satClause_three (σ := σ) h4 with h''' | h''' | h''' <;>
  simp_all [neg, pos]

/-- **族 2 的可靠性**：五条子句合起来恰好定义 `e ↔ (e' ∧ (a ↔ b))`。 -/
theorem step_iff {σ : Assign} {a b e e' : Nat}
    (h1 : SatClause σ [neg e, pos e'])
    (h2 : SatClause σ [neg e, neg a, pos b])
    (h3 : SatClause σ [neg e, pos a, neg b])
    (h4 : SatClause σ [neg e', neg a, neg b, pos e])
    (h5 : SatClause σ [neg e', pos a, pos b, pos e]) :
    σ e = true ↔ (σ e' = true ∧ σ a = σ b) := by
  rcases satClause_two (σ := σ) h1 with h | h <;>
  rcases satClause_three (σ := σ) h2 with h' | h' | h' <;>
  rcases satClause_three (σ := σ) h3 with h'' | h'' | h'' <;>
  rcases satClause_four (σ := σ) h4 with h₄ | h₄ | h₄ | h₄ <;>
  rcases satClause_four (σ := σ) h5 with h₅ | h₅ | h₅ | h₅ <;>
  simp_all [neg, pos]


/-! ## 族的成员关系：具体子句确实在 `lexClauses` 里

`lexClauses` 是四族的连接，故"某条具体子句在它里面"是纯列表运算，`simp` 可判。 -/

variable {σ : Assign} {key img : List Nat} {c : Nat}

theorem mem_head {C : Clause} (h : C ∈ lexHead key img c) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

theorem mem_step {C : Clause} {i : Nat} (hi : i ∈ List.range' 2 (key.length - 2))
    (h : C ∈ lexStep key img c i) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨i, hi, h⟩))

theorem mem_order {C : Clause} (h : C ∈ lexOrder key img) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append]
  exact Or.inl (Or.inr h)

theorem mem_constraint {C : Clause} {i : Nat} (hi : i ∈ List.range' 1 (key.length - 1))
    (h : C ∈ lexConstraint key img c i) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨i, hi, h⟩

/-! ## 核心：`e i` 恰好是前 `i` 位相等的指示 -/

/-- 族 1 与族 2 是 `e` 的**定义式**（两个方向都齐全），故 `e` 的取值被唯一确定。
本引理把它写成一串：**若前 `i` 位相等则 `e i` 为真，且 `e i` 为真则前 `i` 位相等**。 -/
theorem eVar_spec (h : SatFormula σ (lexClauses key img c)) :
    ∀ i, 1 ≤ i → i < key.length →
      (σ (eVar c i) = true ↔ ∀ j, j < i → σ (idx key j) = σ (idx img j)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h1 hlt
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · -- i = 1：族 1 的四条
      have hi1 : i = 1 := by omega
      subst hi1
      have c₁ : SatClause σ [neg (eVar c 1), neg (idx key 0), pos (idx img 0)] :=
        h [neg (eVar c 1), neg (idx key 0), pos (idx img 0)] (mem_head (by simp [lexHead]) : [neg (eVar c 1), neg (idx key 0), pos (idx img 0)] ∈ lexClauses key img c)
      have c₂ : SatClause σ [neg (eVar c 1), pos (idx key 0), neg (idx img 0)] :=
        h [neg (eVar c 1), pos (idx key 0), neg (idx img 0)] (mem_head (by simp [lexHead]) : [neg (eVar c 1), pos (idx key 0), neg (idx img 0)] ∈ lexClauses key img c)
      have c₃ : SatClause σ [neg (idx key 0), neg (idx img 0), pos (eVar c 1)] :=
        h [neg (idx key 0), neg (idx img 0), pos (eVar c 1)] (mem_head (by simp [lexHead]) : [neg (idx key 0), neg (idx img 0), pos (eVar c 1)] ∈ lexClauses key img c)
      have c₄ : SatClause σ [pos (idx key 0), pos (idx img 0), pos (eVar c 1)] :=
        h [pos (idx key 0), pos (idx img 0), pos (eVar c 1)] (mem_head (by simp [lexHead]) : [pos (idx key 0), pos (idx img 0), pos (eVar c 1)] ∈ lexClauses key img c)
      refine (head_iff c₁ c₂ c₃ c₄).trans ?_
      constructor
      · intro heq j hj
        have : j = 0 := by omega
        subst this
        exact heq
      · intro hall
        exact hall 0 (by omega)
    · -- i ≥ 2：族 2 的五条 + 归纳假设
      have hi1 : 1 ≤ i - 1 := by omega
      have hlt' : i - 1 < key.length := by omega
      have hprev := ih (i - 1) (by omega) hi1 hlt'
      have s₁ : SatClause σ [neg (eVar c i), pos (eVar c (i - 1))] :=
        h [neg (eVar c i), pos (eVar c (i - 1))] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c i), pos (eVar c (i - 1))] ∈ lexClauses key img c)
      have s₂ : SatClause σ [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))] :=
        h [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))] ∈ lexClauses key img c)
      have s₃ : SatClause σ [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))] :=
        h [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))] ∈ lexClauses key img c)
      have s₄ : SatClause σ [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)),
                             pos (eVar c i)] :=
        h [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)),
                             pos (eVar c i)] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)),
                             pos (eVar c i)] ∈ lexClauses key img c)
      have s₅ : SatClause σ [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)),
                             pos (eVar c i)] :=
        h [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)),
                             pos (eVar c i)] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)),
                             pos (eVar c i)] ∈ lexClauses key img c)
      rw [step_iff s₁ s₂ s₃ s₄ s₅, hprev]
      constructor
      · rintro ⟨hpre, hlast⟩ j hj
        rcases Nat.lt_or_ge j (i - 1) with hltj | hgej
        · exact hpre j hltj
        · have : j = i - 1 := by omega
          subst this
          exact hlast
      · intro hall
        refine ⟨fun j hj => hall j (by omega), hall (i - 1) (by omega)⟩

/-! ## 主定理：比较器子句全被满足 ⟹ 词典序成立 -/

/-- **比较器断言的词典序形态**，写成与 `lexConstraint` 的子句逐字对应的形式：
不存在"前缀相等、`key i` 为真而 `img i` 为假"的位置。

用 `idx` 而不是 `List.map`：子句里出现的就是 `idx key i`，两边用同一种写法，
`i = 0` 那一格（没有 `e` 可用）才不必绕道 `List.getD` 与 `List.map` 的换算。 -/
def LexLeOver (key img : List Nat) (σ : Assign) : Prop :=
  ∀ i, i < key.length → (∀ j, j < i → σ (idx key j) = σ (idx img j)) →
    σ (idx key i) = true → σ (idx img i) = true

/-- **`lexClauses` 的可靠性**（A3 的 CNF 层）：每条子句都被满足，则比较向量在自己的
像之下**字典序不增**。

证明只做两件事：族 4 在 `i ≥ 1` 上给出"前缀相等且 `key i` 为真 ⟹ `img i` 为真"，
族 3 补上 `i = 0` 那一格；前缀相等这个前提由 `eVar_spec` 从 `e` 的取值翻译过来。 -/
theorem lexClauses_sat (himg : img.length = key.length)
    (h : SatFormula σ (lexClauses key img c)) : LexLeOver key img σ := by
  intro i hlt hpre hkey
  by_cases hi0 : i = 0
  · subst hi0
    have c₀ : SatClause σ [neg (idx key 0), pos (idx img 0)] :=
      h _ (mem_order (key := key) (img := img) (by simp [lexOrder]))
    rcases satClause_two (σ := σ) c₀ with h' | h'
    · exact absurd (h' ▸ hkey) (by simp)
    · exact h'
  · have hi1 : 1 ≤ i := by omega
    have hev := (eVar_spec (σ := σ) (key := key) (img := img) (c := c) h i hi1 hlt).mpr hpre
    have c₂ : SatClause σ [neg (eVar c i), neg (idx key i), pos (idx img i)] :=
      h _ (mem_constraint (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 1, by omega, by omega⟩)
            (by simp [lexConstraint]))
    rcases satClause_three (σ := σ) c₂ with h' | h' | h'
    · exact absurd (h' ▸ hev) (by simp)
    · exact absurd (h' ▸ hkey) (by simp)
    · exact h'

end QECCertificates.LRAT
