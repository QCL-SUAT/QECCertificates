/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.LRAT

/-!
# 编码忠实性：CNF 的模型就是轻逻辑算符

`Reflect/LRAT.lean` 把"内核复算通过"变成"该 CNF 不可满足"，`Reflect/LRATData.lean`
则把本包流水线（`tools/bb144_server` 的编码器 + cadical 的 LRAT）的产物搬进内核。
但这两步合起来给的仍是**关于 CNF 的**命题。本模块补上把它们翻成**码级**命题的那一环。

编码器断言的是（见 `tools/bb144_server/validate_encoding.py` 的模块说明）

    exists x, w  with  x in ker(Hker),  w in ker(Hpair),  x.w = 1,  wt(x) <= k

三部分各由一类子句实现，本模块对每一类给出**可靠性**（"子句全被满足 ⟹ 该条语义成立"）：

| 部件 | 子句 | 可靠性 |
|---|---|---|
| `xorChain` | Tseitin 链 + 一条定值子句 | `dotS σ xs = want`（`dotS` 是支持集上的 GF(2) 点积） |
| `atMostK` | 顺序计数器（Sinz） | `cntS σ xs ≤ k` |

乘积变量（三条子句的 Tseitin 合取）在同文件后续段落给出。
"`x` 不在 `Hpair` 的行空间里"由 `x.w = 1` 与 `w ∈ ker(Hpair)` 给出：若
`x = Σ c_r r` 是行的组合，则 `x.w = Σ c_r (r.w) = 0`，与 `x.w = 1` 矛盾。
这一步只用**行空间 ⊆ (ker)⊥** 这半边——不需要反向的 `(ker)⊥ ⊆ row`。
-/

namespace QECCertificates.LRAT

/-! ## 支持集上的 GF(2) 点积与支撑大小 -/

/-- 支持集 `s` 上的 GF(2) 点积 `Σ_{j ∈ s} σ j`（以 `Bool` 的异或为加法）。 -/
def dotS (σ : Assign) : List Nat → Bool
  | [] => false
  | j :: s => σ j ^^ dotS σ s

@[simp] theorem dotS_nil (σ : Assign) : dotS σ [] = false := rfl

@[simp] theorem dotS_cons (σ : Assign) (j : Nat) (s : List Nat) :
    dotS σ (j :: s) = (σ j ^^ dotS σ s) := rfl

/-- 拼接律：点积在支持集拼接下相加。 -/
theorem dotS_append (σ : Assign) (s t : List Nat) :
    dotS σ (s ++ t) = (dotS σ s ^^ dotS σ t) := by
  induction s with
  | nil => simp
  | cons j s ih => simp only [List.cons_append, dotS_cons, ih]; rw [Bool.xor_assoc]

/-- 支撑大小：`σ` 取真值的变量个数。 -/
def cntS (σ : Assign) (l : List Nat) : Nat := (l.filter (fun t => σ t)).length

@[simp] theorem cntS_nil (σ : Assign) : cntS σ [] = 0 := rfl

theorem cntS_append (σ : Assign) (l₁ l₂ : List Nat) :
    cntS σ (l₁ ++ l₂) = cntS σ l₁ + cntS σ l₂ := by
  simp [cntS, List.filter_append]

theorem cntS_singleton_true (σ : Assign) (x : Nat) (h : σ x = true) : cntS σ [x] = 1 := by
  simp [cntS, h]

theorem cntS_singleton_false (σ : Assign) (x : Nat) (h : σ x = false) : cntS σ [x] = 0 := by
  simp [cntS, h]

theorem cntS_le_length (σ : Assign) (l : List Nat) : cntS σ l ≤ l.length :=
  List.length_filter_le _ _

/-! ## 通用子句引理 -/

/-- 二元子句的语义。 -/
theorem sat_two {σ : Assign} {a b : Lit} (h : SatClause σ [a, b]) :
    σ a.1 = a.2 ∨ σ b.1 = b.2 := by
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact Or.inl hv
  · exact Or.inr hv

/-- 三元子句的语义。 -/
theorem sat_three {σ : Assign} {a b c : Lit} (h : SatClause σ [a, b, c]) :
    σ a.1 = a.2 ∨ σ b.1 = b.2 ∨ σ c.1 = c.2 := by
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr hv)

/-! ## Tseitin 链：`Σ xs = want` -/

/-- Tseitin 一步的四条子句，钉住 `nxt = cur ⊕ x`。

四条子句的极性不能写反：把前两条的 `nxt` 去掉否定，链算的就不是异或而是同或，
UNSAT 与物理断言脱钩（`tools/bb144_server/test_encoding.py` 的小例自检专防这个）。 -/
def xorStepClauses (cur x nxt : Nat) : List Clause :=
  [[(cur, false), (x, false), (nxt, false)],
   [(cur, false), (x, true), (nxt, true)],
   [(cur, true), (x, false), (nxt, true)],
   [(cur, true), (x, true), (nxt, false)]]

/-- 一步的可靠性：四条子句全真 ⟹ `nxt` 取 `cur ⊕ x`。 -/
theorem xorStep_sat {σ : Assign} {cur x nxt : Nat}
    (h : ∀ C ∈ xorStepClauses cur x nxt, SatClause σ C) :
    σ nxt = (σ cur ^^ σ x) := by
  have h1 : SatClause σ [(cur, false), (x, false), (nxt, false)] :=
    h _ (by simp [xorStepClauses])
  have h2 : SatClause σ [(cur, false), (x, true), (nxt, true)] :=
    h _ (by simp [xorStepClauses])
  have h3 : SatClause σ [(cur, true), (x, false), (nxt, true)] :=
    h _ (by simp [xorStepClauses])
  have h4 : SatClause σ [(cur, true), (x, true), (nxt, false)] :=
    h _ (by simp [xorStepClauses])
  have k1 : σ cur = false ∨ σ x = false ∨ σ nxt = false := sat_three h1
  have k2 : σ cur = false ∨ σ x = true ∨ σ nxt = true := sat_three h2
  have k3 : σ cur = true ∨ σ x = false ∨ σ nxt = true := sat_three h3
  have k4 : σ cur = true ∨ σ x = true ∨ σ nxt = false := sat_three h4
  by_cases hc : σ cur = true <;> by_cases hx : σ x = true <;> simp_all

/-- 链：从 `cur` 出发依次异或 `rest` 的每个变量，新变量编号从 `c` 起连续分配。

最后一条子句（`rest` 走完时）把链的结果钉成 `want`。 -/
def xorChainAux : List Nat → Bool → Nat → Nat → List Clause × Nat
  | [], want, cur, c => ([[(cur, want)]], c)
  | x :: rest, want, cur, c =>
      let (tl, c') := xorChainAux rest want c (c + 1)
      (xorStepClauses cur x c ++ tl, c')

/-- 链的可靠性：子句全真 ⟹ `dotS σ (cur :: rest) = want`。 -/
theorem xorChainAux_sat : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    (∀ C ∈ (xorChainAux rest want cur c).1, SatClause σ C) →
    dotS σ (cur :: rest) = want := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c σ h
      have hc : SatClause σ [(cur, want)] := h _ (by simp [xorChainAux])
      obtain ⟨l, hl, hv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      obtain rfl : l = (cur, want) := hl
      simp only [dotS_cons, dotS_nil]
      rw [hv]
      cases want <;> rfl
  | cons x rest ih =>
      intro want cur c σ h
      have hstep : ∀ C ∈ xorStepClauses cur x c, SatClause σ C :=
        fun C hC => h C (List.mem_append_left _ hC)
      have htl : ∀ C ∈ (xorChainAux rest want c (c + 1)).1, SatClause σ C :=
        fun C hC => h C (List.mem_append_right _ hC)
      have hnxt : σ c = (σ cur ^^ σ x) := xorStep_sat hstep
      have hIH : dotS σ (c :: rest) = want := ih want c (c + 1) σ htl
      simp only [dotS_cons] at hIH ⊢
      rw [hnxt] at hIH
      rw [← hIH, Bool.xor_assoc]

/-- 完整链（`xs` 非空；空表只可能来自空支持集，此时**不发子句**——
编码器不会产生空支持集，发一条 `[-start]` 反而会凭空造出约束）。 -/
def xorChain (xs : List Nat) (want : Bool) (start : Nat) : List Clause × Nat :=
  match xs with
  | [] => ([], start)
  | x₀ :: rest => xorChainAux rest want x₀ start

/-- 链的可靠性（非空形态）。 -/
theorem xorChain_sat {σ : Assign} {x₀ : Nat} {rest : List Nat} {want : Bool} {start : Nat}
    (h : ∀ C ∈ (xorChainAux rest want x₀ start).1, SatClause σ C) :
    dotS σ (x₀ :: rest) = want :=
  xorChainAux_sat rest want x₀ start σ h

/-- 链的可靠性（对任意非空变量表；`prodVars` 这类定义不句法可约时用它）。 -/
theorem xorChain_sat' {σ : Assign} {xs : List Nat} {want : Bool} {start : Nat}
    (hne : xs ≠ []) (h : ∀ C ∈ (xorChain xs want start).1, SatClause σ C) :
    dotS σ xs = want := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ rest => exact xorChain_sat h

/-! ## 顺序计数器：`wt ≤ k` -/

/-- 槽位约定：`s i j` 是"前 `i` 个变量里至少有 `j` 个为真"的变量号；`none` 表示该槽位是
**常量**（`j = 0` 时恒真，`j > min i (k+1)` 时恒假）。

`tools/bb144_server/bb144_sat.py` 的 `at_most_k` 用 `0` 表示这两种常量槽，且必须在写出
子句前消去——`0` 在 DIMACS 里是子句终止符，写出去会把一条子句劈成两条。 -/
def SlotOK (s : Nat → Nat → Option Nat) (k : Nat) : Prop :=
  ∀ i j, s i j = none ↔ ¬(1 ≤ j ∧ j ≤ min i (k+1))

theorem SlotOK.some_of {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k+1)) : ∃ v, s i j = some v := by
  have hne : s i j ≠ none := fun h => (hok i j).mp h ⟨h1, h2⟩
  cases h : s i j with
  | none => exact absurd h hne
  | some v => exact ⟨v, rfl⟩

theorem SlotOK.none_of {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h : ¬(1 ≤ j ∧ j ≤ min i (k+1))) : s i j = none := (hok i j).mpr h

/-- 槽位 `(i,j)` 的三到四条子句，逐字照抄编码器；`none` 槽位按常量消去（恒假/恒真）。 -/
def slotClauses (s : Nat → Nat → Option Nat) (i j x : Nat) : List Clause :=
  match s (i - 1) j, s (i - 1) (j - 1), s i j with
  | some a, some b, some si =>
      [[(a, false), (si, true)],
       [(b, false), (x, false), (si, true)],
       [(si, false), (a, true), (x, true)],
       [(si, false), (a, true), (b, true)]]
  | some a, none, some si =>
      [[(a, false), (si, true)],
       [(x, false), (si, true)],
       [(si, false), (a, true), (x, true)]]
  | none, some b, some si =>
      [[(b, false), (x, false), (si, true)],
       [(si, false), (x, true)],
       [(si, false), (b, true)]]
  | none, none, some si =>
      [[(x, false), (si, true)],
       [(si, false), (x, true)]]
  | _, _, none => []

/-- 第 `i` 行（处理变量 `x`）的全部子句，按 `j = 1..min i (k+1)` 展开。 -/
def rowClauses (s : Nat → Nat → Option Nat) (k i x : Nat) : List Clause :=
  (List.range (min i (k+1))).flatMap (fun j' => slotClauses s i (j' + 1) x)

/-- 顺序计数器：`pre` 是已处理的变量（槽位编号靠它的长度算），`suf` 是剩余的。
`k+1 ≤ pre.length` 时（即走到末行）再发一条把 `s n (k+1)` 钉成假的子句。 -/
def atMostKAux (s : Nat → Nat → Option Nat) (k : Nat) (pre suf : List Nat) : List Clause :=
  match suf with
  | [] =>
      if k + 1 ≤ pre.length then
        (match s pre.length (k+1) with
         | some v => [[(v, false)]]
         | none => [])
      else []
  | x :: rest => rowClauses s k (pre.length + 1) x ++ atMostKAux s k (pre ++ [x]) rest

/-- 计数器的全部子句（从空前缀起步）。 -/
def atMostK (s : Nat → Nat → Option Nat) (k : Nat) (xs : List Nat) : List Clause :=
  atMostKAux s k [] xs

/-- 行子句的成员判定：`1 ≤ j ≤ min i (k+1)` 时槽位 `(i,j)` 的子句都在第 `i` 行里。 -/
theorem mem_rowClauses {s : Nat → Nat → Option Nat} {k i j x : Nat} {C : Clause}
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k+1)) (hC : C ∈ slotClauses s i j x) :
    C ∈ rowClauses s k i x := by
  refine List.mem_flatMap.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  have : j - 1 + 1 = j := by omega
  rwa [this]

/-- **计数器的可靠性**：子句全被满足 ⟹ 真值变量个数 ≤ `k`。

不变量：前 `i` 个变量里至少有 `j` 个为真 ⟹ 槽位 `(i,j)` 为真。归纳沿变量表走
（`pre` 是已处理的前缀、`suf` 是剩余的），故步进只需 `List.filter_append`，
不需要 `List.take` 的下标搬运。 -/
theorem atMostKAux_sat {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) :
    ∀ (pre suf : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k+1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) →
      cntS σ (pre ++ suf) ≤ k := by
  intro pre suf hinv0 hcl0
  have aux : ∀ (suf pre : List Nat),
      (∀ j, 1 ≤ j → j ≤ min pre.length (k+1) → j ≤ cntS σ pre →
        ∃ v, s pre.length j = some v ∧ σ v = true) →
      (∀ C ∈ atMostKAux s k pre suf, SatClause σ C) → cntS σ (pre ++ suf) ≤ k := by
    intro suf
    induction suf with
    | nil =>
      intro pre hinv hcl
      by_cases hk : k + 1 ≤ pre.length
      · obtain ⟨v, hsv⟩ := hok.some_of (i := pre.length) (j := k + 1)
          (by omega) (by simp [Nat.min_eq_right hk])
        have hmem : [(v, false)] ∈ atMostKAux s k pre [] := by
          simp only [atMostKAux, ite_eq_left hk, hsv]
          exact List.mem_singleton_self _
        obtain ⟨l, hl, hv⟩ := hcl _ hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        obtain rfl : l = (v, false) := hl
        by_contra hle
        have hge : k + 1 ≤ cntS σ pre := by
          simp only [List.append_nil] at hle
          omega
        obtain ⟨v', hsv', hv'⟩ := hinv (k + 1) (by omega)
          (by simp [Nat.min_eq_right hk]) hge
        rw [hsv] at hsv'
        injection hsv' with hvv
        rw [← hvv] at hv'
        exact absurd hv' (by simp [hv])
      · have hpre : pre.length ≤ k := by omega
        simp only [List.append_nil]
        exact le_trans (cntS_le_length σ pre) hpre
    | cons x rest ih =>
      intro pre hinv hcl
      have hrow : ∀ C ∈ rowClauses s k (pre.length + 1) x, SatClause σ C :=
        fun C hC => hcl C (List.mem_append_left _ hC)
      have htl : ∀ C ∈ atMostKAux s k (pre ++ [x]) rest, SatClause σ C :=
        fun C hC => hcl C (List.mem_append_right _ hC)
      have hlen : (pre ++ [x]).length = pre.length + 1 := by simp
      have hcl_pre : cntS σ pre ≤ pre.length := cntS_le_length σ pre
      have hinv' : ∀ j, 1 ≤ j → j ≤ min (pre ++ [x]).length (k+1) →
          j ≤ cntS σ (pre ++ [x]) → ∃ v, s (pre ++ [x]).length j = some v ∧ σ v = true := by
        intro j hj1 hj2 hj3
        rw [hlen] at hj2
        rw [cntS_append] at hj3
        obtain ⟨w, hsw⟩ := hok.some_of (i := pre.length + 1) (j := j) hj1 hj2
        have hswA : s (pre ++ [x]).length j = some w := by rw [hlen]; exact hsw
        cases hx : σ x
        · -- 第 x 个变量为假：至少 j 个真全落在前缀里
          rw [cntS_singleton_false σ x hx, Nat.add_zero] at hj3
          obtain ⟨v, hsv, hv⟩ := hinv j hj1 (by omega) hj3
          have hmem : [(v, false), (w, true)] ∈ slotClauses s (pre.length + 1) j x := by
            by_cases hb : ∃ u, s pre.length (j - 1) = some u
            · obtain ⟨u, hu⟩ := hb
              simp [slotClauses, hsv, hsw, hu]
            · have hu : s pre.length (j - 1) = none := by
                cases h : s pre.length (j - 1) with
                | none => rfl
                | some u => exact absurd ⟨u, h⟩ hb
              simp [slotClauses, hsv, hsw, hu]
          rcases sat_two (hrow _ (mem_rowClauses hj1 hj2 hmem)) with h | h
          · rw [hv] at h; exact absurd h (by simp)
          · exact ⟨w, hswA, h⟩
        · -- 第 x 个变量为真：分 j = 1 与 j ≥ 2
          rw [cntS_singleton_true σ x hx] at hj3
          by_cases hj : j = 1
          · subst hj
            have hb : s pre.length 0 = none := hok.none_of (i := pre.length) (j := 0) (by simp)
            have hmem : [(x, false), (w, true)] ∈ slotClauses s (pre.length + 1) 1 x := by
              by_cases ha : ∃ u, s pre.length 1 = some u
              · obtain ⟨u, hu⟩ := ha
                simp [slotClauses, hu, hb, hsw]
              · have hu : s pre.length 1 = none := by
                  cases h : s pre.length 1 with
                  | none => rfl
                  | some u => exact absurd ⟨u, h⟩ ha
                simp [slotClauses, hu, hb, hsw]
            rcases sat_two (hrow _ (mem_rowClauses (by omega) hj2 hmem)) with h | h
            · rw [hx] at h; exact absurd h (by simp)
            · exact ⟨w, hswA, h⟩
          · have hj2' : 2 ≤ j := by omega
            obtain ⟨v, hsv, hv⟩ := hinv (j - 1) (by omega) (by omega) (by omega)
            have hmem : [(v, false), (x, false), (w, true)] ∈
                slotClauses s (pre.length + 1) j x := by
              by_cases ha : ∃ u, s pre.length j = some u
              · obtain ⟨u, hu⟩ := ha
                simp [slotClauses, hu, hsv, hsw]
              · have hu : s pre.length j = none := by
                  cases h : s pre.length j with
                  | none => rfl
                  | some u => exact absurd ⟨u, h⟩ ha
                simp [slotClauses, hu, hsv, hsw]
            rcases sat_three (hrow _ (mem_rowClauses (by omega) hj2 hmem)) with h | h | h
            · rw [hv] at h; exact absurd h (by simp)
            · rw [hx] at h; exact absurd h (by simp)
            · exact ⟨w, hswA, h⟩
      have hgoal : (pre ++ x :: rest) = (pre ++ [x]) ++ rest := by
        rw [List.append_assoc, List.singleton_append]
      rw [hgoal]
      exact ih (pre ++ [x]) hinv' htl
  exact aux suf pre hinv0 hcl0

/-- **计数器的可靠性（无前缀形态）**：`∃ σ` 满足全部子句 ⟹ 真值变量个数 ≤ `k`。 -/
theorem atMostK_sat {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) {xs : List Nat}
    (h : ∀ C ∈ atMostK s k xs, SatClause σ C) :
    cntS σ xs ≤ k := by
  have hinv0 : ∀ j, 1 ≤ j → j ≤ min ([] : List Nat).length (k+1) →
      j ≤ cntS σ ([] : List Nat) → ∃ v, s ([] : List Nat).length j = some v ∧ σ v = true := by
    intro j hj1 hj2 _
    simp only [List.length_nil, Nat.min_eq_left (Nat.zero_le _), Nat.le_zero] at hj2
    omega
  have := atMostKAux_sat hok (pre := []) (suf := xs) hinv0 h
  simpa using this

/-! ## 组装：对照 `tools/bb144_server/validate_encoding.py` 的 `build_pair` -/

theorem satFormula_append {σ : Assign} {A B : CNF} :
    SatFormula σ (A ++ B) ↔ SatFormula σ A ∧ SatFormula σ B := by
  constructor
  · intro h
    exact ⟨fun C hC => h C (List.mem_append_left _ hC),
      fun C hC => h C (List.mem_append_right _ hC)⟩
  · rintro ⟨hA, hB⟩ C hC
    rcases List.mem_append.mp hC with h | h
    · exact hA C h
    · exact hB C h

/-- `SatFormula` 是 `def`，隐式透明度下不自动展开——要 `∀ C ∈ F` 形态时用它。 -/
theorem SatFormula.forall {σ : Assign} {F : CNF} (h : SatFormula σ F) :
    ∀ C ∈ F, SatClause σ C := h

theorem dotS_map (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    dotS σ (l.map f) = dotS (fun t => σ (f t)) l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.map_cons, dotS_cons, ih]

theorem dotS_congr {σ τ : Assign} {l : List Nat} (h : ∀ j ∈ l, σ j = τ j) :
    dotS σ l = dotS τ l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      have hj : σ j = τ j := h j (List.mem_cons_self ..)
      have hl : ∀ t ∈ l, σ t = τ t := fun t ht => h t (List.mem_cons_of_mem _ ht)
      simp only [dotS_cons, hj, ih hl]

/-- 支撑大小在映射下的不变式（把"变量号表"换成"按列索引的赋值函数"）。 -/
theorem cntS_map (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    cntS σ (l.map f) = cntS (fun t => σ (f t)) l := by
  simp only [cntS, List.filter_map, List.length_map, Function.comp_def]

/-- 乘积变量块：`a_j ↔ x_j ∧ w_j`，每个三条子句。 -/
def prodClauses (c n : Nat) : List Clause :=
  (List.range n).flatMap (fun j =>
    [[(c + j, false), (j, true)],
     [(c + j, false), (n + j, true)],
     [(c + j, true), (j, false), (n + j, false)]])

/-- 乘积块的三条子句 ⟹ `a = x ∧ w`。 -/
theorem prod_sat {σ : Assign} {a x w : Nat}
    (h1 : SatClause σ [(a, false), (x, true)])
    (h2 : SatClause σ [(a, false), (w, true)])
    (h3 : SatClause σ [(a, true), (x, false), (w, false)]) :
    σ a = (σ x && σ w) := by
  have k1 : σ a = false ∨ σ x = true := sat_two h1
  have k2 : σ a = false ∨ σ w = true := sat_two h2
  have k3 : σ a = true ∨ σ x = false ∨ σ w = false := sat_three h3
  by_cases ha : σ a = true
  · have hx : σ x = true := by
      rcases k1 with h | h
      · exact absurd h (by simp [ha])
      · exact h
    have hw : σ w = true := by
      rcases k2 with h | h
      · exact absurd h (by simp [ha])
      · exact h
    simp [ha, hx, hw]
  · have ha' : σ a = false := by
      cases hh : σ a with
      | false => rfl
      | true => exact absurd hh ha
    rcases k3 with h | h | h
    · exact absurd (ha' ▸ h) (by simp)
    · simp [ha', h]
    · simp [ha', h]

/-- 乘积块全部被满足 ⟹ 每个乘积变量取合取值。 -/
theorem prodClauses_sat {σ : Assign} {c n : Nat}
    (h : ∀ C ∈ prodClauses c n, SatClause σ C) :
    ∀ j < n, σ (c + j) = (σ j && σ (n + j)) := by
  intro j hj
  have mem : ∀ C ∈ [[(c + j, false), (j, true)],
      [(c + j, false), (n + j, true)],
      [(c + j, true), (j, false), (n + j, false)]], C ∈ prodClauses c n := by
    intro C hC
    refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    exact hC
  exact prod_sat (h _ (mem _ (by simp)))
    (h _ (mem _ (by simp))) (h _ (mem _ (by simp)))

/-- 一串 `xorChain`（一行一条），返回（子句，下一个变量号）。 -/
def chainsFrom (f : Nat → Nat) : List (List Nat) → Nat → List Clause × Nat
  | [], c => ([], c)
  | r :: rest, c =>
      let (cl, c') := xorChain (r.map f) false c
      let (cl', c'') := chainsFrom f rest c'
      (cl ++ cl', c'')

theorem chainsFrom_sat {σ : Assign} {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ c, (∀ C ∈ (chainsFrom f rows c).1, SatClause σ C) →
      ∀ r ∈ rows, dotS (fun t => σ (f t)) r = false := by
  induction rows with
  | nil => intro c h r hr; exact absurd hr (List.not_mem_nil)
  | cons r₀ rest ih =>
      intro c h r hr
      rcases List.mem_cons.mp hr with hmem | hr
      · -- 本条行：把 `xorChain` 的可靠性搬过来
        rw [hmem]
        have hcl : ∀ C ∈ (xorChain (r₀.map f) false c).1, SatClause σ C :=
          fun C hC => h C (by simp only [chainsFrom]; exact List.mem_append_left _ hC)
        obtain ⟨x₀, rest₀, hx₀⟩ : ∃ x₀ rest₀, r₀.map f = x₀ :: rest₀ := by
          cases hm : r₀.map f with
          | nil => exact absurd (List.map_eq_nil_iff.mp hm) (hne r₀ (List.mem_cons_self ..))
          | cons x₀ rest₀ => exact ⟨x₀, rest₀, rfl⟩
        have hcl' : ∀ C ∈ (xorChainAux rest₀ false x₀ c).1, SatClause σ C := by
          rw [hx₀] at hcl
          simpa only [xorChain] using hcl
        have hsat : dotS σ (x₀ :: rest₀) = false :=
          xorChain_sat (want := false) (start := c) hcl'
        simpa only [← hx₀, dotS_map σ f r₀] using hsat
      · -- 其余行：递归部分的计数器就是本条链之后的值
        set c' := (xorChain (r₀.map f) false c).2 with hc'
        have hrest : ∀ C ∈ (chainsFrom f rest c').1, SatClause σ C := by
          intro C hC
          have hmem2 : C ∈ (chainsFrom f (r₀ :: rest) c).1 := by
            simp only [chainsFrom]
            exact List.mem_append_right _ (hc' ▸ hC)
          exact h C hmem2
        exact ih (fun r' hr' => hne r' (List.mem_cons_of_mem _ hr')) c' hrest r hr

/-- 槽位基址：第 `i` 行之前已分配的槽位数（与编码器的行优先分配顺序一致）。 -/
def slotBase (k i : Nat) : Nat := ((List.range i).map (fun i' => min i' (k+1))).sum

/-- 顺序计数器的槽位变量号（`none` = 常量槽）。 -/
def slotVar (c k i j : Nat) : Option Nat :=
  if 1 ≤ j ∧ j ≤ min i (k+1) then some (c + slotBase k i + (j - 1)) else none

theorem slotVar_ok (c k : Nat) : SlotOK (slotVar c k) k := by
  intro i j
  by_cases h : 1 ≤ j ∧ j ≤ min i (k+1) <;> simp [slotVar, h]

/-- 核约束段（`x` 的行，变量号 = 列 + 1），以及它之后的计数器。 -/
def kerClauses (Rker : List (List Nat)) (n : Nat) : List Clause :=
  (chainsFrom (fun j => j) Rker (2 * n)).1

def c1Of (Rker : List (List Nat)) (n : Nat) : Nat :=
  (chainsFrom (fun j => j) Rker (2 * n)).2

/-- 配对约束段（`w` 的行，变量号 = `n + 列 + 1`）。 -/
def pairClauses (Rker Rpair : List (List Nat)) (n : Nat) : List Clause :=
  (chainsFrom (fun j => n + j) Rpair (c1Of Rker n)).1

def c2Of (Rker Rpair : List (List Nat)) (n : Nat) : Nat :=
  (chainsFrom (fun j => n + j) Rpair (c1Of Rker n)).2

/-- 乘积变量段与 `x·w = 1` 那条链。 -/
def prodVars (Rker Rpair : List (List Nat)) (n : Nat) : List Nat :=
  (List.range n).map (fun j => c2Of Rker Rpair n + j)

def xwClauses (Rker Rpair : List (List Nat)) (n : Nat) : List Clause :=
  (xorChain (prodVars Rker Rpair n) true (c2Of Rker Rpair n + n)).1

def c3Of (Rker Rpair : List (List Nat)) (n : Nat) : Nat :=
  (xorChain (prodVars Rker Rpair n) true (c2Of Rker Rpair n + n)).2

/-- **本包流水线用的那份编码**，逐字照抄 `validate_encoding.build_pair`。

行给成**列索引表**（`to_masks` 之前的形态）：`x_j ↔ 变量 j+1`、`w_j ↔ 变量 n+j+1`。
组装顺序也必须逐字一致，否则实例同一性（`by decide`）对不上。 -/
def buildPair (Rker Rpair : List (List Nat)) (n k : Nat) : CNF :=
  ((kerClauses Rker n ++ pairClauses Rker Rpair n) ++
    (prodClauses (c2Of Rker Rpair n) n ++ xwClauses Rker Rpair n)) ++
  atMostK (slotVar (c3Of Rker Rpair n) k) k (List.range n)

/-- **编码忠实性（可靠性方向）**：任何满足赋值都给出

* 重量 ≤ `k` 的 `x`（`cntS` 数真值位）；
* `x` 在 `Rker` 的核里、`w` 在 `Rpair` 的核里；
* `x.w = 1`（逐点合取再异或）。

配合 `x.w = 1`，第三、四条使 `x` 不可能落在 `Rpair` 的行空间里（行空间 ⊆ (ker)⊥），
即 `x` 是一个**轻逻辑算符**。 -/
theorem buildPair_sat {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (h : SatFormula σ (buildPair Rker Rpair n k)) :
    cntS σ (List.range n) ≤ k ∧
    (∀ r ∈ Rker, dotS σ r = false) ∧
    (∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false) ∧
    dotS (fun t => σ t && σ (n + t)) (List.range n) = true := by
  unfold buildPair at h
  obtain ⟨hHead, hE⟩ := satFormula_append.mp h
  obtain ⟨hAB, hCD⟩ := satFormula_append.mp hHead
  obtain ⟨hA, hB⟩ := satFormula_append.mp hAB
  obtain ⟨hC, hD⟩ := satFormula_append.mp hCD
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 重量约束
    exact atMostK_sat (s := slotVar (c3Of Rker Rpair n) k) (slotVar_ok _ k)
      (SatFormula.forall hE)
  · -- 核约束
    unfold kerClauses at hA
    exact chainsFrom_sat hne₁ (2 * n) (SatFormula.forall hA)
  · -- 配对约束
    unfold pairClauses at hB
    exact chainsFrom_sat hne₂ (c1Of Rker n) (SatFormula.forall hB)
  · -- `x·w = 1`
    unfold xwClauses at hD
    have hne_prod : prodVars Rker Rpair n ≠ [] := by
      intro h0
      have hlen := congrArg List.length h0
      simp [prodVars, List.length_map, List.length_range] at hlen
      omega
    have hxw : dotS σ (prodVars Rker Rpair n) = true :=
      xorChain_sat' hne_prod (SatFormula.forall hD)
    rw [prodVars, dotS_map] at hxw
    rw [← hxw]
    apply dotS_congr
    intro j hj
    exact (prodClauses_sat (SatFormula.forall hC) j (List.mem_range.mp hj)).symm

end QECCertificates.LRAT
