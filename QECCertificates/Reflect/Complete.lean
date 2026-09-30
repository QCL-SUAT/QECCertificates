/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.Encode

/-!
# 编码忠实性：完备性方向

`Reflect/Encode.lean` 给出的是**可靠性**：子句全被满足 $\\Longrightarrow$ 语义条件成立。
那一条足以把"求解器说不可满足"翻成"没有轻逻辑算符"吗？不能。缺的是反方向——
**编码不会过度约束**：只要语义条件成立，就**存在**一份辅助变量赋值使全部子句为真。
两者合起来才是 `可满足 ⟺ 轻逻辑算符存在`，而 `UNSAT ⟹ 距离下界` 正是这条等价的前推。

本模块补齐反方向。四个部件各给一条**构造性**引理：

| 部件 | 构造 |
|---|---|
| `xorChain` | 辅助变量取**前缀奇偶**：计数器 `c + i` 处取 `acc ⊕ σ x₀ ⊕ ⋯ ⊕ σ xᵢ` |
| `prodClauses` | 乘积变量取 `σ x ∧ σ w` |
| `atMostK` | 槽位 `(i,j)` 取"前 `i` 个变量里至少有 `j` 个为真" |
| `buildPair` | 四段串接，见 `buildPair_complete` |

## 为什么构造要写成"逐段串接"而不是一个整体函数

编码器的辅助变量号是**顺序分配**的（`c1Of`/`c2Of`/`c3Of` 由前一段的出口决定），
逐段构造对上这个顺序就不必做 `c1Of = 2n + Σ(|r| - 1)` 这类计数算术。
串接的接口是 `chainAssign` 的两条性质：**在计数器以下与输入一致**、
**在计数器以上只读本段**，于是后一段赋值在前一段的地盘上原样保留。

## 口径

"轻逻辑算符"在本模块仍只是**语义条件**（重量、两侧核、配对为 1）；
把它翻成码级命题的那一步在 `Reflect/Encode.lean` 的模块说明里已说清，
两侧共用同一套条件，故等价的合成不需要新的搬运。
-/

namespace QECCertificates.LRAT

open scoped BigOperators

/-! ## 一、Tseitin 链的完备性 -/

/-- 链的填充值：`rest` 从计数器 `c` 起依次分配辅助变量，`acc` 是**进入本段时累加器的取值**。

`t = c` 取 `acc ⊕ σ x₀`，`t = c + i` 取 `acc ⊕ σ x₀ ⊕ ⋯ ⊕ σ xⱼ`（`j` 为第 `i` 个）；
落在分配区间之外取 `false`（那些变量号本就不该被引用）。

注意它**不读 `t < c` 处的 `σ`**：这是串接时"后一段不覆盖前一段"的来源。 -/
def chainFill (σ : Assign) : List Nat → Bool → Nat → Nat → Bool
  | [], _, _, _ => false
  | x :: rest, acc, c, t =>
      if t = c then (acc ^^ σ x)
      else chainFill σ rest (acc ^^ σ x) (c + 1) t

theorem chainFill_nil (σ : Assign) (acc : Bool) (c t : Nat) :
    chainFill σ [] acc c t = false := rfl

theorem chainFill_cons (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat) :
    chainFill σ (x :: rest) acc c t =
      (if t = c then (acc ^^ σ x) else chainFill σ rest (acc ^^ σ x) (c + 1) t) := rfl

/-- 计数器处的填充值就是本步的异或。 -/
theorem chainFill_self (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat) :
    chainFill σ (x :: rest) acc c c = (acc ^^ σ x) := by
  rw [chainFill_cons, ite_eq_left rfl]

/-- 跨过计数器一步：`c` 之后的部分就是"累加器已更新、计数器加一"的那条链。 -/
theorem chainFill_succ (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat)
    (h : t ≠ c) :
    chainFill σ (x :: rest) acc c t = chainFill σ rest (acc ^^ σ x) (c + 1) t := by
  rw [chainFill_cons, ite_eq_right h]

/-- 计数器以下不读输入：填充值恒为 `false`。 -/
theorem chainFill_eq_false_of_lt (σ : Assign) (rest : List Nat) (acc : Bool) (c : Nat) :
    ∀ t, t < c → chainFill σ rest acc c t = false := by
  induction rest generalizing acc c with
  | nil => intro t _; rfl
  | cons x rest ih =>
      intro t ht
      rw [chainFill_succ σ x rest acc c t (by omega)]
      exact ih (acc ^^ σ x) (c + 1) t (by omega)

/-- 填充值只读 `rest` 的元素与初始累加器——串接时的相容性就靠这条。 -/
theorem chainFill_congr {σ σ' : Assign} (rest : List Nat) (acc acc' : Bool) (c : Nat)
    (hacc : acc = acc') (h : ∀ t ∈ rest, σ t = σ' t) :
    ∀ t, chainFill σ rest acc c t = chainFill σ' rest acc' c t := by
  subst hacc
  induction rest generalizing acc c with
  | nil => intro t; rfl
  | cons x rest ih =>
      intro t
      have hx : σ x = σ' x := h x (List.mem_cons_self ..)
      have hrest : ∀ t' ∈ rest, σ t' = σ' t' := fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      rw [chainFill_cons σ x rest acc c t, chainFill_cons σ' x rest acc c t, hx]
      by_cases ht : t = c
      · rw [ite_eq_left ht, ite_eq_left ht]
      · rw [ite_eq_right ht, ite_eq_right ht]
        exact ih (acc ^^ σ' x) (c + 1) hrest t

/-- 链的完整赋值：计数器 `c` 以下保持 `σ`，以上取链的填充值。 -/
def chainAssign (σ : Assign) (rest : List Nat) (acc : Bool) (c : Nat) : Assign :=
  fun t => if t < c then σ t else chainFill σ rest acc c t

theorem chainAssign_of_lt {σ : Assign} {rest : List Nat} {acc : Bool} {c t : Nat}
    (h : t < c) : chainAssign σ rest acc c t = σ t := by
  simp only [chainAssign, h, ite_true]

/-- 跨过计数器一步（`chainAssign` 版）。 -/
theorem chainAssign_succ (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat)
    (h : c < t) :
    chainAssign σ (x :: rest) acc c t = chainAssign σ rest (acc ^^ σ x) (c + 1) t := by
  have h1 : ¬ t < c := by omega
  have h2 : ¬ t = c := by omega
  have h3 : ¬ t < c + 1 := by omega
  simp only [chainAssign, h1, h3, ite_false]
  rw [chainFill_succ σ x rest acc c t h2]

/-- 计数器处 `chainAssign` 的取值。 -/
theorem chainAssign_self (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat) :
    chainAssign σ (x :: rest) acc c c = (acc ^^ σ x) := by
  simp only [chainAssign, Nat.lt_irrefl, ite_false]
  exact chainFill_self σ x rest acc c

/-- `chainAssign` 的相容性：以下按 `hlt` 一致、`rest` 上按 `h` 一致，则两个赋值相等。 -/
theorem chainAssign_congr {σ σ' : Assign} {rest : List Nat} {acc acc' : Bool} {c : Nat}
    (hacc : acc = acc') (hlt : ∀ t, t < c → σ t = σ' t) (h : ∀ t ∈ rest, σ t = σ' t) :
    ∀ t, chainAssign σ rest acc c t = chainAssign σ' rest acc' c t := by
  intro t
  by_cases ht : t < c
  · rw [chainAssign_of_lt ht, chainAssign_of_lt ht, hlt t ht]
  · have h1 : ¬ t < c := ht
    simp only [chainAssign, h1, ite_false]
    exact chainFill_congr rest acc acc' c hacc h t

/-- 把一段链的赋值**接着**喂给它的尾段，得到的是同一个赋值——串接引理。

注意 `t = c` 处两者恰好一致（左边取新累加器 `acc ⊕ σ x`、右边取 `chainFill` 在计数器处的值），
这正是 `chainFill` 不读计数器以下的原因。 -/
theorem chainAssign_tail (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat)
    (hrest : ∀ t ∈ rest, t < c) :
    ∀ t, chainAssign (chainAssign σ (x :: rest) acc c) rest
          (chainAssign σ (x :: rest) acc c c) (c + 1) t
        = chainAssign σ (x :: rest) acc c t := by
  intro t
  by_cases ht : t < c + 1
  · rw [chainAssign_of_lt ht]
  · have ht1 : ¬ t < c + 1 := ht
    have htc : ¬ t < c := by omega
    have hne : t ≠ c := by omega
    simp only [chainAssign, ht1, htc, ite_false]
    rw [chainFill_succ σ x rest acc c t hne]
    exact chainFill_congr rest (chainAssign σ (x :: rest) acc c c) (acc ^^ σ x) (c + 1)
      (chainAssign_self σ x rest acc c)
      (fun t' ht' => chainAssign_of_lt (hrest t' ht')) t

/-- **一步的完备性**：值满足异或关系，则四条子句全真。 -/
theorem xorStepClauses_sat_of {τ : Assign} {cur x nxt : Nat}
    (h : τ nxt = (τ cur ^^ τ x)) :
    ∀ C ∈ xorStepClauses cur x nxt, SatClause τ C := by
  intro C hC
  simp only [xorStepClauses, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    simp only [SatClause, List.mem_cons, List.not_mem_nil, or_false] <;>
    (cases hv : τ cur <;> cases hw : τ x <;> simp_all)

/-- **链的完备性**：语义条件成立、且链读到的输入变量都在计数器 `c` 以下时，
`chainAssign` 满足链的全部子句。 -/
theorem xorChainAux_complete : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    cur < c → (∀ t ∈ rest, t < c) → dotS σ (cur :: rest) = want →
    ∀ C ∈ (xorChainAux rest want cur c).1, SatClause (chainAssign σ rest (σ cur) c) C := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c σ hcur _ hd C hC
      simp only [xorChainAux, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl
      refine ⟨(cur, want), List.mem_cons_self .., ?_⟩
      have hcw : σ cur = want := by
        simpa only [dotS_cons, dotS_nil, Bool.xor_false] using hd
      rw [chainAssign_of_lt hcur, hcw]
  | cons x rest ih =>
      intro want cur c σ hcur hrest hd
      have hx : x < c := hrest x (List.mem_cons_self ..)
      have hrest' : ∀ t ∈ rest, t < c + 1 := fun t ht => by
        have h := hrest t (List.mem_cons_of_mem _ ht); omega
      have hc1 : c < c + 1 := by omega
      -- 步子句
      have hstep : ∀ C ∈ xorStepClauses cur x c,
          SatClause (chainAssign σ (x :: rest) (σ cur) c) C := by
        refine xorStepClauses_sat_of ?_
        rw [chainAssign_self, chainAssign_of_lt hcur, chainAssign_of_lt hx]
      -- 尾子句：把赋值原样交给尾段（`chainAssign_tail`），再用归纳假设
      have hd' : dotS (chainAssign σ (x :: rest) (σ cur) c) (c :: rest) = want := by
        rw [dotS_cons, chainAssign_self]
        have hcongr : dotS (chainAssign σ (x :: rest) (σ cur) c) rest = dotS σ rest :=
          dotS_congr (fun t ht => chainAssign_of_lt (hrest t (List.mem_cons_of_mem _ ht)))
        rw [hcongr]
        rw [dotS_cons, dotS_cons] at hd
        rw [← hd, Bool.xor_assoc]
      have htail : ∀ C ∈ (xorChainAux rest want c (c + 1)).1,
          SatClause (chainAssign σ (x :: rest) (σ cur) c) C := by
        have htail' := ih want c (c + 1) (chainAssign σ (x :: rest) (σ cur) c) hc1 hrest' hd'
        intro C hC
        have h2 := htail' C hC
        -- 出现位置是**函数**而不是逐点应用，故先把 `∀ t` 形式收成函数等式再改写
        have hfun : chainAssign (chainAssign σ (x :: rest) (σ cur) c) rest
              (chainAssign σ (x :: rest) (σ cur) c c) (c + 1)
            = chainAssign σ (x :: rest) (σ cur) c :=
          funext (chainAssign_tail σ x rest (σ cur) c
            (fun t ht => hrest t (List.mem_cons_of_mem _ ht)))
        rwa [hfun] at h2
      intro C hC
      simp only [xorChainAux, List.mem_append] at hC
      rcases hC with hC | hC
      · exact hstep C hC
      · exact htail C hC

/-! ## 二、串接：一行一条链

`chainsFrom` 把每条行做成一条链、首尾相接地分配变量号。完备性要**逐段串接**：
后一段赋值必须在前一段的地盘上原样保留，接口就是 `chainAssign` 的"计数器以下与输入一致"。

为此需要两条记账引理：链的**出口计数器**（新变量号恰好走到 `c + rest.length`）
与链子句的**变量上界**（都落在出口计数器以下）。 -/

/-- 链的出口计数器：每处理一个变量分配一个号。 -/
theorem xorChainAux_snd : ∀ (rest : List Nat) (want : Bool) (cur c : Nat),
    (xorChainAux rest want cur c).2 = c + rest.length := by
  intro rest
  induction rest with
  | nil => intro want cur c; rfl
  | cons x rest ih =>
      intro want cur c
      simp only [xorChainAux, List.length_cons]
      rw [ih]
      omega

/-- 一步子句里的变量只可能是三个位置之一。 -/
theorem xorStepClauses_vars {cur x nxt : Nat} {C : Clause}
    (hC : C ∈ xorStepClauses cur x nxt) :
    ∀ l ∈ C, l.1 = cur ∨ l.1 = x ∨ l.1 = nxt := by
  simp only [xorStepClauses, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;>
    (intro l hl
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
     rcases hl with rfl | rfl | rfl <;> simp)

/-- 链子句的变量上界：都落在出口计数器以下。 -/
theorem xorChainAux_vars_lt : ∀ (rest : List Nat) (want : Bool) (cur c : Nat),
    cur < c → (∀ t ∈ rest, t < c) →
    ∀ C ∈ (xorChainAux rest want cur c).1, ∀ l ∈ C, l.1 < c + rest.length := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c hcur _ C hC l hl
      simp only [xorChainAux, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl
      simpa using hcur
  | cons x rest ih =>
      intro want cur c hcur hrest C hC l hl
      have hx : x < c := hrest x (List.mem_cons_self ..)
      have hrest' : ∀ t ∈ rest, t < c + 1 := fun t ht => by
        have := hrest t (List.mem_cons_of_mem _ ht); omega
      simp only [xorChainAux, List.mem_append] at hC
      simp only [List.length_cons]
      rcases hC with hC | hC
      · rcases xorStepClauses_vars hC l hl with h | h | h <;> omega
      · have h2 := ih want c (c + 1) (by omega) hrest' C hC l hl
        omega

/-- 链子句在"计数器以下一致"的赋值之间传递。 -/
theorem satClause_of_agree {σ τ : Assign} {C : Clause} {c : Nat}
    (h : ∀ t, t < c → τ t = σ t) (hvars : ∀ l ∈ C, l.1 < c) (hC : SatClause σ C) :
    SatClause τ C := by
  obtain ⟨l, hl, hv⟩ := hC
  exact ⟨l, hl, by rw [h l.1 (hvars l hl), hv]⟩

/-- **一串链的完备性**：每行的点积都为 `false` 时，存在一份赋值同时满足全部链子句，
且在计数器 `c` 以下与输入一致。 -/
theorem chainsFrom_complete {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ (c : Nat) (σ : Assign), (∀ r ∈ rows, ∀ t ∈ r, f t < c) →
      (∀ r ∈ rows, dotS (fun t => σ (f t)) r = false) →
      ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
        ∀ C ∈ (chainsFrom f rows c).1, SatClause τ C := by
  induction rows with
  | nil =>
      intro c σ _ _
      exact ⟨σ, fun _ _ => rfl, fun C hC => absurd hC (by simp [chainsFrom])⟩
  | cons r₀ rest ih =>
      intro c σ hlt hdot
      have hr₀ : r₀ ≠ [] := hne r₀ (List.mem_cons_self ..)
      have hrest_ne : ∀ r ∈ rest, r ≠ [] := fun r hr => hne r (List.mem_cons_of_mem _ hr)
      have hmap_ne : r₀.map f ≠ [] := fun h0 => hr₀ (List.map_eq_nil_iff.mp h0)
      obtain ⟨x₀, t, hmap⟩ : ∃ x₀ t, r₀.map f = x₀ :: t := by
        cases hm : r₀.map f with
        | nil => exact absurd hm hmap_ne
        | cons x₀ t => exact ⟨x₀, t, rfl⟩
      have hchain : xorChain (r₀.map f) false c = xorChainAux t false x₀ c := by
        simp only [xorChain, hmap]
      have hc' : (xorChain (r₀.map f) false c).2 = c + t.length := by
        rw [hchain, xorChainAux_snd]
      have hx₀ : x₀ < c := by
        obtain ⟨s, hs, hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_self ..)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s hs
      have ht : ∀ s ∈ t, s < c := by
        intro s hs
        obtain ⟨s', hs', hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_of_mem _ hs)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s' hs'
      have hdott : dotS σ (x₀ :: t) = false := by
        have h := hdot r₀ (List.mem_cons_self ..)
        rw [← dotS_map σ f r₀, hmap] at h
        exact h
      have hhead := xorChainAux_complete t false x₀ c σ hx₀ ht hdott
      have hlt' : ∀ r ∈ rest, ∀ s ∈ r, f s < c + t.length := by
        intro r hr s hs
        have := hlt r (List.mem_cons_of_mem _ hr) s hs
        omega
      have hdot' : ∀ r ∈ rest, dotS (fun s => chainAssign σ t (σ x₀) c (f s)) r = false := by
        intro r hr
        have h := hdot r (List.mem_cons_of_mem _ hr)
        have hfs : ∀ s ∈ r, f s < c := hlt r (List.mem_cons_of_mem _ hr)
        have hcongr : dotS (fun s => chainAssign σ t (σ x₀) c (f s)) r
            = dotS (fun s => σ (f s)) r :=
          dotS_congr (fun s hs => chainAssign_of_lt (hfs s hs))
        rw [hcongr]
        exact h
      obtain ⟨τ, hagree, hcl⟩ :=
        ih hrest_ne (c + t.length) (chainAssign σ t (σ x₀) c) hlt' hdot'
      refine ⟨τ, ?_, ?_⟩
      · intro s hs
        rw [hagree s (by omega : s < c + t.length), chainAssign_of_lt hs]
      · intro C hC
        simp only [chainsFrom, List.mem_append] at hC
        rcases hC with hC | hC
        · rw [hchain] at hC
          exact satClause_of_agree hagree
            (xorChainAux_vars_lt t false x₀ c hx₀ ht C hC) (hhead C hC)
        · rw [hc'] at hC
          exact hcl C hC

/-! ## 三、乘积块的完备性

`prodClauses c n` 用变量 `c + j` 承载 `x_j ∧ w_j`（`x_j` 是变量 `j`、`w_j` 是变量 `n + j`）。
完备性是把 `c + j` 直接赋成合取值。 -/

/-- 乘积块的赋值：`c..c+n-1` 段取逐点合取，其余原样。 -/
def prodFill (σ : Assign) (c n : Nat) : Assign :=
  fun t => if c ≤ t ∧ t < c + n then (σ (t - c) && σ (n + (t - c))) else σ t

/-- 乘积变量处的取值就是两个因子的合取。 -/
theorem prodFill_at (σ : Assign) (c n j : Nat) (hj : j < n) :
    prodFill σ c n (c + j) = (σ j && σ (n + j)) := by
  have hsub : (c + j) - c = j := by omega
  simp only [prodFill, hsub]
  rw [ite_eq_left (by omega : c ≤ c + j ∧ c + j < c + n)]

/-- 乘积块三条子句的语义：合取关系成立则三条全真。 -/
theorem prodClauses_three_sat {τ : Assign} {a x w : Nat}
    (h : τ a = (τ x && τ w)) :
    ∀ C ∈ ([[(a, false), (x, true)], [(a, false), (w, true)],
            [(a, true), (x, false), (w, false)]] : CNF), SatClause τ C := by
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl <;>
    simp only [SatClause, List.mem_cons, List.not_mem_nil, or_false] <;>
    (cases hx : τ x <;> cases hw : τ w <;> simp_all)

/-- 乘积块不碰输入变量（`c` 在它们之上）。 -/
theorem prodFill_of_lt {σ : Assign} {c n t : Nat} (h : t < c) :
    prodFill σ c n t = σ t := by
  simp only [prodFill]
  rw [ite_eq_right (by omega : ¬ (c ≤ t ∧ t < c + n))]

/-- **乘积块的完备性**。 -/
theorem prodClauses_complete {c n : Nat} {σ : Assign} (hc : 2 * n ≤ c) :
    ∀ C ∈ prodClauses c n, SatClause (prodFill σ c n) C := by
  intro C hC
  simp only [prodClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨j, hj, hCj⟩ := hC
  refine prodClauses_three_sat ?_ C hCj
  rw [prodFill_at σ c n j hj,
    show prodFill σ c n j = σ j from prodFill_of_lt (by omega),
    show prodFill σ c n (n + j) = σ (n + j) from prodFill_of_lt (by omega)]

/-! ## 四、顺序计数器（Sinz）的完备性

`atMostK` 的可靠性是"子句全真 ⟹ 真值个数 ≤ `k`"（`Reflect/Encode.lean`）。反方向要把
**槽位 `(i,j)` 赋成"前 `i` 个变量里至少有 `j` 个为真"**，逐行验证四条子句。

三件前置：`slotBase` 的递推（第 `i+1` 行之前比第 `i` 行之前多出第 `i` 行的 `min i (k+1)` 个槽位）、
`slotVar` 的取值刻画、以及把子句判据从 `Bool` 桥回命题的几条小引理。 -/

/-- 第 `i+1` 行之前比第 `i` 行之前多出第 `i` 行的 `min i (k+1)` 个槽位。 -/
theorem slotBase_succ (k i : Nat) : slotBase k (i + 1) = slotBase k i + min i (k + 1) := by
  simp only [slotBase, List.range_succ, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- 槽位基址单调。 -/
theorem slotBase_mono (k : Nat) {i i' : Nat} (h : i ≤ i') : slotBase k i ≤ slotBase k i' := by
  induction i', h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih => rw [slotBase_succ]; exact le_trans ih (Nat.le_add_right _ _)

/-- `slotBase` 的"前一索引"形式，前提出现在索引自身上。 -/
theorem slotBase_pred {k i : Nat} (hi : 1 ≤ i) :
    slotBase k i = slotBase k (i - 1) + min (i - 1) (k + 1) := by
  have h := slotBase_succ k (i - 1)
  rwa [show i - 1 + 1 = i from by omega] at h

/-- `slotVar` 在有效槽位上取确定值。 -/
theorem slotVar_of_le {c k i j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) :
    slotVar c k i j = some (c + slotBase k i + (j - 1)) := by
  rw [slotVar, ite_eq_left ⟨h1, h2⟩]

/-- `slotVar` 在无效槽位上取 `none`。 -/
theorem slotVar_eq_none {c k i j : Nat} (h : ¬ (1 ≤ j ∧ j ≤ min i (k + 1))) :
    slotVar c k i j = none := by
  rw [slotVar, ite_eq_right h]

/-! ### 子句级的 Bool 桥

四条子句的语义都是"某个 Bool 蕴含另一个"，故把判据写成"值的蕴含"即可，
不必在每一处重复拆 `decide`。 -/

theorem decide_imp {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    decide P = true → decide Q = true := fun hp => by
  have := h (of_decide_eq_true hp)
  simp only [decide_eq_true_eq]; exact this

theorem decide_imp2 {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (h : P → Q → R) : decide P = true → decide Q = true → decide R = true := by
  intro hp hq
  have := h (of_decide_eq_true hp) (of_decide_eq_true hq)
  simp only [decide_eq_true_eq]; exact this

/-- 二元子句 `¬p ∨ q`：由 `bp = true → bq = true` 给出。 -/
theorem sat_two_of_imp {τ : Assign} {p q : Nat} {bp bq : Bool}
    (hp : τ p = bp) (hq : τ q = bq) (h : bp = true → bq = true) :
    SatClause τ [(p, false), (q, true)] := by
  cases bp with
  | false => exact ⟨(p, false), by simp, by rw [hp]⟩
  | true => exact ⟨(q, true), by simp, by rw [hq]; exact h rfl⟩

/-- 三元子句 `¬a ∨ ¬x ∨ s`：由 `(a ∧ x) → s` 给出。 -/
theorem sat_three_of_imp {τ : Assign} {a x s : Nat} {ba bx bs : Bool}
    (ha : τ a = ba) (hx : τ x = bx) (hs : τ s = bs)
    (h : ba = true → bx = true → bs = true) :
    SatClause τ [(a, false), (x, false), (s, true)] := by
  cases ba with
  | false => exact ⟨(a, false), by simp, by rw [ha]⟩
  | true =>
      cases bx with
      | false => exact ⟨(x, false), by simp, by rw [hx]⟩
      | true => exact ⟨(s, true), by simp, by rw [hs]; exact h rfl rfl⟩

/-- 三元子句 `¬s ∨ a ∨ x`：由 `(s ∧ ¬a) → x` 给出。 -/
theorem sat_three_of_imp2 {τ : Assign} {s a x : Nat} {bs ba bx : Bool}
    (hs : τ s = bs) (ha : τ a = ba) (hx : τ x = bx)
    (h : bs = true → ba = false → bx = true) :
    SatClause τ [(s, false), (a, true), (x, true)] := by
  cases bs with
  | false => exact ⟨(s, false), by simp, by rw [hs]⟩
  | true =>
      cases ba with
      | false => exact ⟨(x, true), by simp, by rw [hx]; exact h rfl rfl⟩
      | true => exact ⟨(a, true), by simp, by rw [ha]⟩

/-- 三元子句 `¬s ∨ a ∨ b`：由 `(s ∧ ¬a) → b` 给出。 -/
theorem sat_three_of_imp3 {τ : Assign} {s a b : Nat} {bs ba bb : Bool}
    (hs : τ s = bs) (ha : τ a = ba) (hb : τ b = bb)
    (h : bs = true → ba = false → bb = true) :
    SatClause τ [(s, false), (a, true), (b, true)] := by
  cases bs with
  | false => exact ⟨(s, false), by simp, by rw [hs]⟩
  | true =>
      cases ba with
      | false => exact ⟨(b, true), by simp, by rw [hb]; exact h rfl rfl⟩
      | true => exact ⟨(a, true), by simp, by rw [ha]⟩

/-! ### `slotClauses` 的四个分支写成显式等式

`slotClauses` 的 `match` 的 scrutinee 是三个 `Option` 值。直接对目标里的槽位做 `rw`
改不动它（槽位是**函数参数**），所以先把"三个取值"写成假设、再让 `match` 降下来。 -/

theorem slotClauses_eq_some_some {s : Nat → Nat → Option Nat} {i j x a b si : Nat}
    (ha : s (i - 1) j = some a) (hb : s (i - 1) (j - 1) = some b) (hs : s i j = some si) :
    slotClauses s i j x =
      [[(a, false), (si, true)], [(b, false), (x, false), (si, true)],
       [(si, false), (a, true), (x, true)], [(si, false), (a, true), (b, true)]] := by
  simp only [slotClauses, ha, hb, hs]

theorem slotClauses_eq_some_none {s : Nat → Nat → Option Nat} {i j x a si : Nat}
    (ha : s (i - 1) j = some a) (hb : s (i - 1) (j - 1) = none) (hs : s i j = some si) :
    slotClauses s i j x =
      [[(a, false), (si, true)], [(x, false), (si, true)],
       [(si, false), (a, true), (x, true)]] := by
  simp only [slotClauses, ha, hb, hs]

theorem slotClauses_eq_none_some {s : Nat → Nat → Option Nat} {i j x b si : Nat}
    (ha : s (i - 1) j = none) (hb : s (i - 1) (j - 1) = some b) (hs : s i j = some si) :
    slotClauses s i j x =
      [[(b, false), (x, false), (si, true)], [(si, false), (x, true)],
       [(si, false), (b, true)]] := by
  simp only [slotClauses, ha, hb, hs]

theorem slotClauses_eq_none_none {s : Nat → Nat → Option Nat} {i j x si : Nat}
    (ha : s (i - 1) j = none) (hb : s (i - 1) (j - 1) = none) (hs : s i j = some si) :
    slotClauses s i j x = [[(x, false), (si, true)], [(si, false), (x, true)]] := by
  simp only [slotClauses, ha, hb, hs]

/-! ### 一行的完备性

第 `i` 行处理第 `i` 个变量，槽位 `(i,j)` 的取值由"前 `i` 个变量里至少有 `j` 个为真"定。
`cnt'` 是前 `i-1` 个变量的真值个数、`cnt` 是前 `i` 个的、`bx` 是第 `i` 个变量的取值；
`hprev`/`hcur` 把上一行与这一行的槽位取值写成假设，于是本条只做 `Bool` 层面的验证。

四个情形的分界是"上一行的槽位 `(i-1,j)`、`(i-1,j-1)` 是否有效"，即 `slotClauses`
那个 `match` 的分支条件。 -/

theorem rowClauses_complete {c k i cnt' cnt : Nat} {x : Nat} {τ : Assign} {bx : Bool}
    (hx : τ x = bx) (hcnt : cnt = cnt' + (if bx then 1 else 0))
    (hmin : cnt' ≤ min (i - 1) (k + 1))
    (hprev : ∀ j, 1 ≤ j → j ≤ min (i - 1) (k + 1) →
      τ (c + slotBase k (i - 1) + (j - 1)) = decide (j ≤ cnt'))
    (hcur : ∀ j, 1 ≤ j → j ≤ min i (k + 1) →
      τ (c + slotBase k i + (j - 1)) = decide (j ≤ cnt)) :
    ∀ C ∈ rowClauses (slotVar c k) k i x, SatClause τ C := by
  have hif : (if bx then 1 else 0) ≤ 1 := by cases bx <;> simp
  have hle : cnt' ≤ cnt := by omega
  have hle1 : cnt ≤ cnt' + 1 := by omega
  have hbx1 : bx = true → cnt = cnt' + 1 := by intro h; rw [hcnt, h]; simp
  have hbx0 : bx = false → cnt = cnt' := by intro h; rw [hcnt, h]; simp
  have ofT {P : Prop} [Decidable P] (h : decide P = true) : P := of_decide_eq_true h
  have ofF {P : Prop} [Decidable P] (h : decide P = false) : ¬ P := of_decide_eq_false h
  intro C hC
  simp only [rowClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨j', hj', hCj⟩ := hC
  set j := j' + 1 with hjdef
  have hj1 : 1 ≤ j := by omega
  have hj2 : j ≤ min i (k + 1) := by omega
  have hva := hcur j hj1 hj2
  by_cases hA : 1 ≤ j ∧ j ≤ min (i - 1) (k + 1)
  · by_cases hB : 1 ≤ j - 1 ∧ j - 1 ≤ min (i - 1) (k + 1)
    · -- 两个槽位都有效
      have ha := hprev j hA.1 hA.2
      have hb := hprev (j - 1) hB.1 hB.2
      rw [slotClauses_eq_some_some (slotVar_of_le hA.1 hA.2) (slotVar_of_le hB.1 hB.2)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl | rfl | rfl
      · exact sat_two_of_imp ha hva (decide_imp fun h => le_trans h hle)
      · refine sat_three_of_imp hb hx hva fun h1 h2 => ?_
        have h1' := ofT h1
        have h2' := hbx1 h2
        simp only [decide_eq_true_eq]
        omega
      · exact sat_three_of_imp2 hva ha hx fun hs ha' => by
          have h1 := ofT hs
          have h2 := ofF ha'
          by_contra hbf
          have hb0 : bx = false := by
            cases bx with
            | false => rfl
            | true => exact absurd rfl hbf
          rw [hbx0 hb0] at h1
          omega
      · exact sat_three_of_imp3 hva ha hb fun hs ha' => by
          have h1 := ofT hs
          have h2 := ofF ha'
          simp only [decide_eq_true_eq]
          omega
    · -- `(i-1, j-1)` 无效：此时 `j = 1`
      have ha := hprev j hA.1 hA.2
      have hj1' : j = 1 := by
        by_contra h
        exact hB ⟨by omega, by omega⟩
      rw [slotClauses_eq_some_none (slotVar_of_le hA.1 hA.2) (slotVar_eq_none hB)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl | rfl
      · exact sat_two_of_imp ha hva (decide_imp fun h => le_trans h hle)
      · exact sat_two_of_imp hx hva fun hxT => by
          simp only [decide_eq_true_eq]
          rw [hbx1 hxT] at *
          omega
      · exact sat_three_of_imp2 hva ha hx fun hs ha' => by
          have h1 := ofT hs
          have h2 := ofF ha'
          by_contra hbf
          have hb0 : bx = false := by
            cases bx with
            | false => rfl
            | true => exact absurd rfl hbf
          rw [hbx0 hb0] at h1
          omega
  · -- `(i-1, j)` 无效
    have hjA : min (i - 1) (k + 1) < j := by
      by_contra hle'
      exact hA ⟨hj1, by omega⟩
    by_cases hB : 1 ≤ j - 1 ∧ j - 1 ≤ min (i - 1) (k + 1)
    · -- 上一行的 `j-1` 槽位有效
      have hb := hprev (j - 1) hB.1 hB.2
      rw [slotClauses_eq_none_some (slotVar_eq_none hA) (slotVar_of_le hB.1 hB.2)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl | rfl
      · refine sat_three_of_imp hb hx hva fun h1 h2 => ?_
        have h1' := ofT h1
        have h2' := hbx1 h2
        simp only [decide_eq_true_eq]
        omega
      · exact sat_two_of_imp hva hx fun hs => by
          have h1 := ofT hs
          by_contra hbf
          have hb0 : bx = false := by
            cases bx with
            | false => rfl
            | true => exact absurd rfl hbf
          rw [hbx0 hb0] at h1
          omega
      · exact sat_two_of_imp hva hb fun hs => by
          have h1 := ofT hs
          simp only [decide_eq_true_eq]
          omega
    · -- 两个都无效：此时 `i = 1`、`j = 1`、`cnt' = 0`
      have hj1' : j = 1 := by
        by_contra h
        refine hB ⟨by omega, ?_⟩
        omega
      have hmin0 : min (i - 1) (k + 1) = 0 := by
        by_contra h
        exact hA ⟨hj1, by omega⟩
      have hcnt0' : cnt' = 0 := le_antisymm (hmin0 ▸ hmin) (Nat.zero_le _)
      rw [slotClauses_eq_none_none (slotVar_eq_none hA) (slotVar_eq_none hB)
        (slotVar_of_le hj1 hj2)] at hCj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
      rcases hCj with rfl | rfl
      · exact sat_two_of_imp hx hva fun hxT => by
          simp only [decide_eq_true_eq]
          rw [hbx1 hxT, hcnt0']
          omega
      · exact sat_two_of_imp hva hx fun hs => by
          have h1 := ofT hs
          rw [hj1'] at h1
          cases bx with
          | false =>
              rw [hbx0 rfl, hcnt0'] at h1
              exact absurd h1 (by omega)
          | true => rfl

/-! ### 逐行填充与主定理

把第 `i` 行的槽位块写进赋值。**块的边界由 `slotBase` 定死**：第 `i` 行占
`[c + slotBase k i, c + slotBase k (i+1))`，而 `slotBase k (i+1) = slotBase k i + min i (k+1)`
（`slotBase_succ`）说明两块**首尾相接、互不重叠**。归纳里"后面几行不动前面已填好的槽位"
就是这一条，它把逐段构造串起来而**不需要**从变量号反解行号。 -/

/-- 把第 `i` 行的槽位块写进赋值：块内取"前 `i` 个变量里至少有 `j` 个为真"，块外原样保留。 -/
def rowFill (τ : Assign) (c k i cnt : Nat) : Assign :=
  fun t => if c + slotBase k i ≤ t ∧ t < c + slotBase k i + min i (k + 1) then
      decide ((t - (c + slotBase k i)) + 1 ≤ cnt)
    else τ t

/-- 块内第 `j` 个槽位的取值。 -/
theorem rowFill_at {τ : Assign} {c k i cnt j : Nat} (hj : j < min i (k + 1)) :
    rowFill τ c k i cnt (c + slotBase k i + j) = decide (j + 1 ≤ cnt) := by
  have hsub : c + slotBase k i + j - (c + slotBase k i) = j := by omega
  simp only [rowFill, hsub]
  rw [ite_eq_left (by omega : c + slotBase k i ≤ c + slotBase k i + j ∧
    c + slotBase k i + j < c + slotBase k i + min i (k + 1))]

/-- 块外原样保留。 -/
theorem rowFill_of_notMem {τ : Assign} {c k i cnt t : Nat}
    (h : ¬ (c + slotBase k i ≤ t ∧ t < c + slotBase k i + min i (k + 1))) :
    rowFill τ c k i cnt t = τ t := by
  simp only [rowFill]
  rw [ite_eq_right h]

/-- 填第 `i` 行不动第 `i-1` 行的块（两块首尾相接、不重叠）。 -/
theorem rowFill_prev {τ : Assign} {c k i cnt j : Nat} (hi : 1 ≤ i)
    (hj : j < min (i - 1) (k + 1)) :
    rowFill τ c k i cnt (c + slotBase k (i - 1) + j) = τ (c + slotBase k (i - 1) + j) := by
  refine rowFill_of_notMem ?_
  rintro ⟨h1, h2⟩
  rw [slotBase_pred hi] at h1
  omega

/-- **顺序计数器的完备性**：真值个数 ≤ `k` 时，存在赋值满足全部计数器子句，
且在输入变量上与给定赋值一致。

归纳沿 `atMostKAux` 的遍历走（`pre` 是已处理的前缀、`suf` 是剩余的），
每步把该行的槽位块写进赋值。返回的赋值有两个性质供外层使用：**在
`c + slotBase k (pre.length + 1)` 以下与原赋值一致**（前几行填好的槽位没被后面覆盖），
以及**最后一行的槽位取值刻画**（下一步要用它当 `hprev`）。 -/
theorem atMostK_complete {k c : Nat} {xs : List Nat} {σ : Assign}
    (hc : ∀ t ∈ xs, t < c) (hcnt : cntS σ xs ≤ k) :
    ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
      ∀ C ∈ atMostK (slotVar c k) k xs, SatClause τ C := by
  have aux : ∀ (suf pre : List Nat) (τ : Assign),
      (∀ t ∈ pre ++ suf, τ t = σ t) →
      (∀ t ∈ pre ++ suf, t < c) →
      (∀ j, 1 ≤ j → j ≤ min pre.length (k + 1) →
        τ (c + slotBase k pre.length + (j - 1)) = decide (j ≤ cntS σ pre)) →
      cntS σ (pre ++ suf) ≤ k →
      ∃ τ' : Assign,
        (∀ t, t < c + slotBase k (pre.length + 1) → τ' t = τ t) ∧
        (∀ j, 1 ≤ j → j ≤ min (pre ++ suf).length (k + 1) →
          τ' (c + slotBase k (pre ++ suf).length + (j - 1))
            = decide (j ≤ cntS σ (pre ++ suf))) ∧
        ∀ C ∈ atMostKAux (slotVar c k) k pre suf, SatClause τ' C := by
    intro suf
    induction suf with
    | nil =>
        intro pre τ _ _ hprev hk
        have hkpre : cntS σ pre ≤ k := by simpa using hk
        refine ⟨τ, fun _ _ => rfl, ?_, ?_⟩
        · intro j hj1 hj2
          simp only [List.append_nil] at hj2 ⊢
          exact hprev j hj1 hj2
        · intro C hC
          by_cases hk' : k + 1 ≤ pre.length
          · -- 末端把槽位 `(pre.length, k+1)` 钉成假
            have hsome : slotVar c k pre.length (k + 1)
                = some (c + slotBase k pre.length + (k + 1 - 1)) :=
              slotVar_of_le (by omega) (by simp [Nat.min_eq_right hk'])
            simp only [atMostKAux, ite_eq_left hk', hsome] at hC
            rw [List.mem_singleton] at hC
            rw [hC]
            refine ⟨(c + slotBase k pre.length + (k + 1 - 1), false),
              List.mem_singleton_self _, ?_⟩
            have hv := hprev (k + 1) (by omega) (by simp [Nat.min_eq_right hk'])
            rw [hv]
            have : ¬ (k + 1 ≤ cntS σ pre) := by omega
            simp [this]
          · simp only [atMostKAux, ite_eq_right hk'] at hC
            exact absurd hC (by simp)
    | cons x rest ih =>
        intro pre τ hagree hcc hprev hk
        set i := pre.length + 1 with hidef
        have hi : 1 ≤ i := by omega
        have hlen : (pre ++ [x]).length = i := by simp [hidef]
        have hxlt : x < c := hcc x (List.mem_append_right _ (List.mem_cons_self ..))
        have hxl : τ x = σ x := hagree x (List.mem_append_right _ (List.mem_cons_self ..))
        -- 计数分解与行的界
        have hdecomp : cntS σ (pre ++ (x :: rest)) = cntS σ (pre ++ [x]) + cntS σ rest := by
          rw [show pre ++ (x :: rest) = (pre ++ [x]) ++ rest from by simp]
          exact cntS_append σ (pre ++ [x]) rest
        have hcx : cntS σ (pre ++ [x]) = cntS σ pre + (if σ x then 1 else 0) := by
          rw [cntS_append]
          by_cases h : σ x
          · rw [cntS_singleton_true σ x h]
            simp [h]
          · have hf : σ x = false := by simpa using h
            rw [cntS_singleton_false σ x hf, hf]
            simp
        have hcτ : cntS σ (pre ++ [x]) = cntS σ pre + (if τ x then 1 else 0) := by
          rw [hcx, hxl]
        have hmin : cntS σ pre ≤ min (i - 1) (k + 1) := by
          refine le_min (cntS_le_length σ pre) ?_
          have h1 : cntS σ pre ≤ cntS σ (pre ++ [x]) := by
            rw [cntS_append]; exact Nat.le_add_right _ _
          have h2 : cntS σ (pre ++ [x]) ≤ cntS σ (pre ++ (x :: rest)) := by
            rw [hdecomp]; exact Nat.le_add_right _ _
          omega
        have hpre' : ∀ j, 1 ≤ j → j ≤ min (i - 1) (k + 1) →
            τ (c + slotBase k (i - 1) + (j - 1)) = decide (j ≤ cntS σ pre) := by
          intro j hj1 hj2
          rw [show i - 1 = pre.length from by omega]
          exact hprev j hj1 hj2
        -- 先填第 `i` 行，再递归
        have hpre'' : ∀ j, 1 ≤ j → j ≤ min (pre ++ [x]).length (k + 1) →
            rowFill τ c k i (cntS σ (pre ++ [x]))
              (c + slotBase k (pre ++ [x]).length + (j - 1))
              = decide (j ≤ cntS σ (pre ++ [x])) := by
          intro j hj1 hj2
          rw [hlen]
          have h := rowFill_at (τ := τ) (c := c) (k := k) (i := i)
            (cnt := cntS σ (pre ++ [x])) (j := j - 1) (by omega)
          rwa [show j - 1 + 1 = j from by omega] at h
        have happ : (pre ++ [x]) ++ rest = pre ++ (x :: rest) := by simp
        have hagree' : ∀ t ∈ (pre ++ [x]) ++ rest,
            rowFill τ c k i (cntS σ (pre ++ [x])) t = σ t := by
          intro t ht
          rw [happ] at ht
          rcases List.mem_append.mp ht with ht | ht
          · rw [rowFill_of_notMem ?_]
            exact hagree t (List.mem_append_left _ ht)
            intro ⟨h1, _⟩
            have := hcc t (List.mem_append_left _ ht)
            omega
          · rcases List.mem_cons.mp ht with rfl | ht
            · rw [rowFill_of_notMem ?_]
              exact hxl
              intro ⟨h1, _⟩
              omega
            · rw [rowFill_of_notMem ?_]
              exact hagree t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
              intro ⟨h1, _⟩
              have := hcc t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
              omega
        have hcc' : ∀ t ∈ (pre ++ [x]) ++ rest, t < c := by
          intro t ht
          rw [happ] at ht
          exact hcc t ht
        have hk' : cntS σ ((pre ++ [x]) ++ rest) ≤ k := by
          rw [happ]; exact hk
        obtain ⟨τ'', hag, hfin, hcl⟩ :=
          ih (pre ++ [x]) (rowFill τ c k i (cntS σ (pre ++ [x]))) hagree' hcc' hpre'' hk'
        -- 与 `τ''` 的一致性：`τ''` 与 `rowFill` 在下一行之前一致
        have hbound : ∀ t, t < c + slotBase k i → t < c + slotBase k ((pre ++ [x]).length + 1) := by
          intro t ht
          rw [hlen]
          exact lt_of_lt_of_le ht (Nat.add_le_add_left (slotBase_mono k (Nat.le_succ i)) c)
        have hbound' : ∀ t, t < c + slotBase k (i + 1) →
            t < c + slotBase k ((pre ++ [x]).length + 1) := by
          intro t ht
          rw [hlen]
          exact ht
        refine ⟨τ'', ?_, ?_, ?_⟩
        · -- `τ''` 与 `τ` 在 `c + slotBase k i` 以下一致
          intro t ht
          rw [hag t (hbound t ht)]
          exact rowFill_of_notMem (by
            rintro ⟨h1, _⟩
            omega)
        · intro j hj1 hj2
          rw [← happ] at hj2 ⊢
          exact hfin j hj1 hj2
        · -- 本行的子句：把行引理直接用在 `τ''` 上（槽位取值从 `rowFill` 搬过来）
          have hpre''' : ∀ j, 1 ≤ j → j ≤ min (i - 1) (k + 1) →
              τ'' (c + slotBase k (i - 1) + (j - 1)) = decide (j ≤ cntS σ pre) := by
            intro j hj1 hj2
            have hlt : c + slotBase k (i - 1) + (j - 1) < c + slotBase k i := by
              rw [slotBase_pred hi]; omega
            rw [hag _ (hbound _ hlt)]
            rw [rowFill_prev hi (by omega)]
            exact hpre' j hj1 hj2
          have hcur''' : ∀ j, 1 ≤ j → j ≤ min i (k + 1) →
              τ'' (c + slotBase k i + (j - 1)) = decide (j ≤ cntS σ (pre ++ [x])) := by
            intro j hj1 hj2
            have hlt : c + slotBase k i + (j - 1) < c + slotBase k (i + 1) := by
              rw [slotBase_succ k i]
              omega
            rw [hag _ (hbound' _ hlt)]
            simpa [hlen] using hpre'' j hj1 (by rw [hlen]; exact hj2)
          have hx'' : τ'' x = τ x := by
            rw [hag x (hbound x (by omega))]
            exact rowFill_of_notMem (by rintro ⟨h1, _⟩; omega)
          have hrow := rowClauses_complete (c := c) (k := k) (i := i)
            (cnt' := cntS σ pre) (cnt := cntS σ (pre ++ [x])) (x := x)
            (τ := τ'') (bx := τ x) hx'' hcτ hmin hpre''' hcur'''
          intro C hC
          simp only [atMostKAux, List.mem_append] at hC
          rcases hC with hC | hC
          · exact hrow C hC
          · exact hcl C hC
  -- 空前缀起步：`aux` 的第一个性质给出"在 `c` 以下与原赋值一致"，而输入变量都在 `c` 以下
  have hprev0 : ∀ j, 1 ≤ j → j ≤ min ([] : List Nat).length (k + 1) →
      σ (c + slotBase k ([] : List Nat).length + (j - 1)) = decide (j ≤ cntS σ []) := by
    intro j hj1 hj2
    simp only [List.length_nil, Nat.min_eq_left (Nat.zero_le _), Nat.le_zero] at hj2
    omega
  obtain ⟨τ, hag, _, hcl⟩ :=
    aux xs [] σ (by simp) (by simpa using hc) hprev0 (by simpa using hcnt)
  refine ⟨τ, ?_, ?_⟩
  · intro t ht
    have h0 : slotBase k 1 = 0 := by simp [slotBase]
    exact hag t (by rw [List.length_nil, Nat.zero_add, h0, Nat.add_zero]; exact ht)
  · simpa only [atMostK] using hcl

/-! ## 五、组装：`buildPair` 的完备性

四段的赋值逐段串接。装配要把"某一段的子句由它那一段的赋值满足"搬到**最终**赋值上，
靠两条：**计数器只会变大**（后一段的门槛不低于前一段），以及**每段子句的变量都在自己的
出口计数器以下**。

`buildPair` 的分段与计数器（`Reflect/Encode.lean`）：核约束在 `2n` 起、配对约束在 `c1Of` 起、
乘积块在 `c2Of` 起、`x·w` 那条链在 `c2Of + n` 起、计数器在 `c3Of` 起。 -/

/-- 链的出口计数器只增不减。 -/
theorem xorChain_snd_ge (xs : List Nat) (w : Bool) (c : Nat) :
    c ≤ (xorChain xs w c).2 := by
  cases xs with
  | nil => simp [xorChain]
  | cons x₀ t =>
      have h := xorChainAux_snd t w x₀ c
      simp only [xorChain, h]
      omega

/-- 一串链的出口计数器只增不减。 -/
theorem chainsFrom_snd_ge {f : Nat → Nat} : ∀ (rows : List (List Nat)) (c : Nat),
    c ≤ (chainsFrom f rows c).2 := by
  intro rows
  induction rows with
  | nil => intro c; simp [chainsFrom]
  | cons r₀ rest ih =>
      intro c
      have h := ih ((xorChain (r₀.map f) false c).2)
      have h2 := xorChain_snd_ge (r₀.map f) false c
      simp only [chainsFrom]
      omega

/-- 一串链的子句变量都在**本段的**出口计数器以下。 -/
theorem chainsFrom_vars_lt {f : Nat → Nat} {rows : List (List Nat)} {c : Nat}
    (hne : ∀ r ∈ rows, r ≠ [])
    (hlt : ∀ r ∈ rows, ∀ t ∈ r, f t < c) :
    ∀ C ∈ (chainsFrom f rows c).1, ∀ l ∈ C, l.1 < (chainsFrom f rows c).2 := by
  induction rows generalizing c with
  | nil => intro C hC; simp only [chainsFrom, List.not_mem_nil] at hC
  | cons r₀ rest ih =>
      intro C hC
      have hr₀ : r₀ ≠ [] := hne r₀ (List.mem_cons_self ..)
      have hmap_ne : r₀.map f ≠ [] := fun h0 => hr₀ (List.map_eq_nil_iff.mp h0)
      obtain ⟨x₀, t, hmap⟩ : ∃ x₀ t, r₀.map f = x₀ :: t := by
        cases hm : r₀.map f with
        | nil => exact absurd hm hmap_ne
        | cons x₀ t => exact ⟨x₀, t, rfl⟩
      have hchain : xorChain (r₀.map f) false c = xorChainAux t false x₀ c := by
        simp only [xorChain, hmap]
      have hc' : (xorChain (r₀.map f) false c).2 = c + t.length := by
        rw [hchain, xorChainAux_snd]
      have hx₀ : x₀ < c := by
        obtain ⟨s, hs, hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_self ..)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s hs
      have ht : ∀ s ∈ t, s < c := by
        intro s hs
        obtain ⟨s', hs', hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_of_mem _ hs)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s' hs'
      have hc'' : (xorChainAux t false x₀ c).2 = c + t.length := by
        rw [← hchain]; exact hc'
      simp only [chainsFrom, List.mem_append] at hC
      rcases hC with hC | hC
      · rw [hchain] at hC
        intro l hl
        have h1 := xorChainAux_vars_lt t false x₀ c hx₀ ht C hC l hl
        exact lt_of_lt_of_le h1 (by
          have h2 := chainsFrom_snd_ge (f := f) rest ((xorChain (r₀.map f) false c).2)
          simp only [chainsFrom]
          omega)
      · intro l hl
        have := ih (fun r hr => hne r (List.mem_cons_of_mem _ hr)) (fun r hr s hs =>
          lt_of_lt_of_le (hlt r (List.mem_cons_of_mem _ hr) s hs) (xorChain_snd_ge _ false c))
          C hC l hl
        simpa only [chainsFrom] using this

/-- 乘积块子句的变量都在 `c + n` 以下（`n ≤ c` 时输入变量也在其内）。 -/
theorem prodClauses_vars_lt {c n : Nat} (hc : n ≤ c) :
    ∀ C ∈ prodClauses c n, ∀ l ∈ C, l.1 < c + n := by
  intro C hC l hl
  simp only [prodClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨j, hj, hCj⟩ := hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hCj
  rcases hCj with hCj | hCj | hCj <;> rw [hCj] at hl <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
     rcases hl with rfl | rfl | rfl <;> omega)

/-- 一条链的子句变量都在本段的出口计数器以下。 -/
theorem xorChain_vars_lt {xs : List Nat} {w : Bool} {c : Nat} (hne : xs ≠ [])
    (hlt : ∀ t ∈ xs, t < c) :
    ∀ C ∈ (xorChain xs w c).1, ∀ l ∈ C, l.1 < (xorChain xs w c).2 := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ t =>
      have hx₀ : x₀ < c := hlt x₀ (List.mem_cons_self ..)
      have ht : ∀ s ∈ t, s < c := fun s hs => hlt s (List.mem_cons_of_mem _ hs)
      have h := xorChainAux_snd t w x₀ c
      simp only [xorChain, h]
      exact xorChainAux_vars_lt t w x₀ c hx₀ ht

/-- 子句集在"门槛以下一致"的赋值之间传递。 -/
theorem satFormula_of_agree {σ τ : Assign} {F : CNF} {c : Nat}
    (h : ∀ t, t < c → τ t = σ t) (hF : ∀ C ∈ F, ∀ l ∈ C, l.1 < c)
    (hσ : SatFormula σ F) : SatFormula τ F :=
  fun C hC => satClause_of_agree h (hF C hC) (hσ C hC)

/-- "在 `c` 以下一致"可传递，门槛可降。 -/
theorem agree_le_trans {σ τ υ : Assign} {a b : Nat}
    (h1 : ∀ t, t < b → τ t = σ t) (h2 : ∀ t, t < a → υ t = τ t) (h : a ≤ b) :
    ∀ t, t < a → υ t = σ t :=
  fun t ht => by rw [h2 t ht, h1 t (lt_of_lt_of_le ht h)]

/-- 单条链的完备性（非空形态）。 -/
theorem xorChain_complete {xs : List Nat} {w : Bool} {c : Nat} {σ : Assign}
    (hne : xs ≠ []) (hlt : ∀ t ∈ xs, t < c) (h : dotS σ xs = w) :
    ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
      ∀ C ∈ (xorChain xs w c).1, SatClause τ C := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ t =>
      have hx₀ : x₀ < c := hlt x₀ (List.mem_cons_self ..)
      have ht : ∀ s ∈ t, s < c := fun s hs => hlt s (List.mem_cons_of_mem _ hs)
      exact ⟨chainAssign σ t (σ x₀) c, fun _ hu => chainAssign_of_lt hu,
        fun C hC => by
          simp only [xorChain] at hC
          exact xorChainAux_complete t w x₀ c σ hx₀ ht h C hC⟩

/-- **`buildPair` 的完备性**：语义四条件成立时，编码是可满足的。

与 `Reflect/Encode.lean` 的 `buildPair_sat`（可靠性）合成
**"存在轻逻辑算符 ⟺ 编码可满足"**；再配上 `Reflect/LRAT.lean` 的可靠性定理，
一个不可满足判决就**直接给出距离下界**——两个方向由此都在内核里。 -/
theorem buildPair_complete {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hcol₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hcol₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hwt : cntS σ (List.range n) ≤ k)
    (hker : ∀ r ∈ Rker, dotS σ r = false)
    (hpair : ∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false)
    (hxw : dotS (fun t => σ t && σ (n + t)) (List.range n) = true) :
    ∃ τ : Assign, SatFormula τ (buildPair Rker Rpair n k) := by
  -- 各段计数器只增不减
  have hge1 : 2 * n ≤ c1Of Rker n := chainsFrom_snd_ge Rker (2 * n)
  have hge2 : c1Of Rker n ≤ c2Of Rker Rpair n := chainsFrom_snd_ge Rpair (c1Of Rker n)
  have hge3 : c2Of Rker Rpair n + n ≤ c3Of Rker Rpair n := xorChain_snd_ge _ true _
  -- 第一段：核约束
  have hlt₁ : ∀ r ∈ Rker, ∀ t ∈ r, (fun j => j) t < 2 * n := fun r hr t ht => by
    have := hcol₁ r hr t ht
    change t < 2 * n
    omega
  obtain ⟨τ₁, hag₁, hcl₁⟩ :=
    chainsFrom_complete hne₁ (2 * n) σ hlt₁ (fun r hr => hker r hr)
  -- 第二段：配对约束
  have hlt₂ : ∀ r ∈ Rpair, ∀ t ∈ r, (fun j => n + j) t < c1Of Rker n := fun r hr t ht => by
    have := hcol₂ r hr t ht
    change n + t < c1Of Rker n
    omega
  have hdot₂ : ∀ r ∈ Rpair, dotS (fun t => τ₁ (n + t)) r = false := by
    intro r hr
    have h := hpair r hr
    have hcongr : dotS (fun t => τ₁ (n + t)) r = dotS (fun t => σ (n + t)) r :=
      dotS_congr (fun t ht => hag₁ (n + t) (by have := hcol₂ r hr t ht; omega))
    rwa [hcongr]
  obtain ⟨τ₂, hag₂, hcl₂⟩ := chainsFrom_complete hne₂ (c1Of Rker n) τ₁ hlt₂ hdot₂
  -- 第三段：乘积块
  have hprod : 2 * n ≤ c2Of Rker Rpair n := le_trans hge1 hge2
  have hcl₃ : ∀ C ∈ prodClauses (c2Of Rker Rpair n) n,
      SatClause (prodFill τ₂ (c2Of Rker Rpair n) n) C :=
    prodClauses_complete hprod
  have hag₃ : ∀ t, t < c2Of Rker Rpair n →
      prodFill τ₂ (c2Of Rker Rpair n) n t = τ₂ t :=
    fun _ ht => prodFill_of_lt ht
  -- 第四段：`x·w = 1` 那条链
  have hprodvars_ne : prodVars Rker Rpair n ≠ [] := by
    intro h0
    have hlen := congrArg List.length h0
    simp [prodVars, List.length_map, List.length_range] at hlen
    omega
  have hlt₄ : ∀ t ∈ prodVars Rker Rpair n, t < c2Of Rker Rpair n + n := by
    intro t ht
    simp only [prodVars, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    omega
  have hdot₄ : dotS (prodFill τ₂ (c2Of Rker Rpair n) n) (prodVars Rker Rpair n) = true := by
    have hmap : dotS (prodFill τ₂ (c2Of Rker Rpair n) n) (prodVars Rker Rpair n)
        = dotS (fun j => prodFill τ₂ (c2Of Rker Rpair n) n (c2Of Rker Rpair n + j))
            (List.range n) := by
      simp only [prodVars, dotS_map]
    rw [hmap]
    have hcongr : dotS (fun j => prodFill τ₂ (c2Of Rker Rpair n) n (c2Of Rker Rpair n + j))
          (List.range n)
        = dotS (fun j => σ j && σ (n + j)) (List.range n) := by
      refine dotS_congr (fun j hj => ?_)
      rw [prodFill_at _ _ _ j (List.mem_range.mp hj)]
      have hjn : j < n := List.mem_range.mp hj
      have hj2 : τ₂ j = σ j := by
        rw [hag₂ j (by omega)]
        exact hag₁ j (by omega)
      have hj3 : τ₂ (n + j) = σ (n + j) := by
        rw [hag₂ (n + j) (by omega)]
        exact hag₁ (n + j) (by omega)
      rw [hj2, hj3]
    rw [hcongr]
    exact hxw
  obtain ⟨τ₄, hag₄, hcl₄⟩ := xorChain_complete hprodvars_ne hlt₄ hdot₄
  -- 第五段：计数器的赋值（`τ₄` 与 `σ` 在输入上一致，故重量条件直接搬过来）
  have hagree₄ : ∀ t, t < 2 * n → τ₄ t = σ t := by
    intro t ht
    rw [hag₄ t (by omega), hag₃ t (by omega), hag₂ t (by omega)]
    exact hag₁ t ht
  have hwt₄ : cntS τ₄ (List.range n) ≤ k := by
    have hcongr : cntS τ₄ (List.range n) = cntS σ (List.range n) := by
      refine congrArg List.length ?_
      apply List.filter_congr
      intro a ha
      exact hagree₄ a (by have := List.mem_range.mp ha; omega)
    rw [hcongr]
    exact hwt
  have hlt₅ : ∀ t ∈ List.range n, t < c3Of Rker Rpair n := fun t ht => by
    have := List.mem_range.mp ht
    omega
  obtain ⟨τ₅, hag₅, hcl₅⟩ := atMostK_complete (k := k) (c := c3Of Rker Rpair n)
    (xs := List.range n) (σ := τ₄) hlt₅ hwt₄
  -- 最终赋值：各段门槛以下一致
  have e54 : ∀ t, t < c2Of Rker Rpair n + n → τ₅ t = τ₄ t :=
    fun t ht => hag₅ t (le_trans ht hge3)
  have e53 : ∀ t, t < c2Of Rker Rpair n + n →
      τ₅ t = prodFill τ₂ (c2Of Rker Rpair n) n t := by
    intro t ht
    rw [e54 t ht]
    exact hag₄ t ht
  have e52 : ∀ t, t < c2Of Rker Rpair n → τ₅ t = τ₂ t := by
    intro t ht
    rw [e53 t (by omega)]
    exact hag₃ t ht
  have e51 : ∀ t, t < c1Of Rker n → τ₅ t = τ₁ t := by
    intro t ht
    rw [e52 t (lt_of_lt_of_le ht hge2)]
    exact hag₂ t ht
  -- 五段各自成立
  have hSeg1 : SatFormula τ₅ (kerClauses Rker n) := by
    refine satFormula_of_agree e51 ?_ hcl₁
    intro C hC l hl
    exact chainsFrom_vars_lt hne₁ hlt₁ C hC l hl
  have hSeg2 : SatFormula τ₅ (pairClauses Rker Rpair n) := by
    refine satFormula_of_agree e52 ?_ hcl₂
    intro C hC l hl
    exact chainsFrom_vars_lt hne₂ hlt₂ C hC l hl
  have hSeg3 : SatFormula τ₅ (prodClauses (c2Of Rker Rpair n) n) := by
    refine satFormula_of_agree e53 ?_ hcl₃
    intro C hC l hl
    exact prodClauses_vars_lt (by omega) C hC l hl
  have hSeg4 : SatFormula τ₅ (xwClauses Rker Rpair n) := by
    refine satFormula_of_agree hag₅ ?_ hcl₄
    intro C hC l hl
    exact xorChain_vars_lt hprodvars_ne hlt₄ C hC l hl
  refine ⟨τ₅, ?_⟩
  rw [buildPair]
  exact satFormula_append.mpr
    ⟨satFormula_append.mpr ⟨satFormula_append.mpr ⟨hSeg1, hSeg2⟩,
      satFormula_append.mpr ⟨hSeg3, hSeg4⟩⟩, hcl₅⟩

end QECCertificates.LRAT
