/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import Mathlib

/-!
# LRAT 证书的内核检查器与可靠性定理

外部 SAT 求解器只**出证据**，证据在**内核内**复核——这是本库对"外部求解器的输出
不进可信基"那条红线的落地。本模块把这件事做成定理，而不是靠"检查器说 OK"：

* `rupCheck db C hints`：子句 `C` 相对数据库 `db` 是否 RUP（把 `C` 取反，
  沿 `hints` 的单元传播导出冲突）；
* `checkSteps db steps`：LRAT 的逐条核对（子句号必须连续、每条必须 RUP、
  导出空子句即成功）；
* **`rupAux_sound` / `checkSteps_sound` / `unsat_of_checkSteps`**：核对通过 ⟹
  该 CNF **不可满足**。三条的 `#print axioms` 恰为标准三公理，**不含求解器、
  不含 `native_decide`、不含任何自定义公理**。

数据（真实的 CNF 与 LRAT 证书）落在 `Reflect/LRATData.lean`，由
`tools/gen_lrat_lean.py` 从 `tools/bb144_server` 的编码器产物逐字节翻译而来。

## 为什么这条可靠性定理才是重点

"某证书通过了我写的检查器"是一句关于**程序**的话；"该 CNF 不可满足"是一句关于
**数学**的话。把前者变成后者，靠的正是 `checkSteps_sound`——于是这份证书从
**求解器产物**升格为**内核定理**，而检查器本身（约两百行）也一并进了可信基。

## 表示

字面量是 `Nat × Bool`（变量号 0-based、极性），部分赋值是**已赋真的字面量表**——
这样"单元传播"就是列表追加，"传播出冲突"就是"某条 hint 子句的字面量全为假"，
全部是内核可归约的计算。

**子句库是接口，不是 `Array`。** `ClauseDB` 只要求四个操作（取、长度、追加、建库）
与三条定律，且定律**只取可靠性真正消费的那一半**——`checkAux_sound` 要的是
"追加后库里的每条要么是新的、要么原来就在"，反方向用不到，故不必立
（少掉的那半边正是平衡树实例需要"键 < 下标"那条难证不变量的地方）。
`ClauseDB.array` 是**与开接口之前逐字相同**的实例，下游不受影响。

**为什么开这条缝**（本库实测）：`Array` 在**内核里**的
`push` 与 `get?` 都**线性于下标**，故 `rupCheck` 每步的库访问按步序增长、全证书是
关于步数的**平方**；换成平衡树是对数。按归约次数实测 $N = 200 \to 400$：
`Array` 40,803 → 161,603（3.96×），`Std.TreeMap` 4,757 → 11,066（2.33×，理论 2.26×）；
外推到回放的 570,883 步，两者相差约 9,400 倍。

**第二个实例已落地**：`ClauseDB.tree` 用 `Std.TreeMap`（键 = 子句号减一，`push` 追加在
`size` 处），内核里每次取/插是 $O(\log n)$。它在**同一份真证书**上与 `array` 给出同一个
判定——`checkStepsWith ClauseDB.tree rep7CNF rep7Proof = true` 由 `decide` 关闭——
而 36 步那一档上归约数已约为 `array` 的一半（13k 对 28.6k）；外推到 570,883 步，
两者相差约 9,400 倍。
**一处 Std 上的坑值得记**：空树上 `Const.get? ∅ i = none` 那条引理虽是 `@[simp]`，
但 `∅.inner` 与引理里的 `∅` **不按语法匹配**，`rw` 不触发、`simp only [该引理]` 也不动它；
**裸 `simp`（defeq 匹配）才行**。
-/

namespace QECCertificates.LRAT

abbrev Lit := Nat × Bool
abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assign := Nat → Bool
abbrev PAssign := List Lit

def litNeg (l : Lit) : Lit := (l.1, !l.2)

/-- 一条子句被赋值满足。 -/
def SatClause (σ : Assign) (C : Clause) : Prop := ∃ l ∈ C, σ l.1 = l.2

/-- 一个 CNF 被赋值满足。 -/
def SatFormula (σ : Assign) (F : CNF) : Prop := ∀ C ∈ F, SatClause σ C

/-- 该 CNF 可满足。 -/
def Satisfiable (F : CNF) : Prop := ∃ σ, SatFormula σ F

/-- 部分赋值 `a` 与完全赋值 `σ` 一致。 -/
def agrees (σ : Assign) (a : PAssign) : Prop := ∀ l ∈ a, σ l.1 = l.2

/-- 该字面量在当前部分赋值下**未被赋值**（其否定也不在赋值里）。 -/
def litFree (a : PAssign) (l : Lit) : Bool := !(decide (litNeg l ∈ a))

/-! ## 一、扫描一条子句 -/

def scanAux (a : PAssign) (fr : List Lit) : Clause → List Lit
  | [] => fr
  | l :: rest => if litFree a l then scanAux a (l :: fr) rest else scanAux a fr rest

/-- 扫描一条子句：返回它在当前赋值下的**自由字面量**表（未被赋值的）。
为空即"全假"（冲突），单元即"恰好一个自由"（单元步）。 -/
def scan (a : PAssign) (D : Clause) : List Lit := scanAux a [] D

theorem scanAux_spec (a : PAssign) (D : Clause) (fr : List Lit) :
    ∃ tail : List Lit,
      scanAux a fr D = tail ++ fr ∧
        (∀ l ∈ tail, l ∈ D ∧ litFree a l = true) ∧
        (∀ l ∈ D, litFree a l = true → l ∈ tail) := by
  induction D generalizing fr with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons l rest ih =>
      by_cases hf : litFree a l = true
      · rw [scanAux, ite_eq_left hf]
        obtain ⟨tail, h1, h2, h3⟩ := ih (l :: fr)
        refine ⟨tail ++ [l], ?_, ?_, ?_⟩
        · rw [h1, List.append_assoc, List.singleton_append]
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact ⟨List.mem_cons_of_mem _ (h2 x hx).1, (h2 x hx).2⟩
          · rw [List.mem_singleton] at hx
            subst hx
            exact ⟨by simp, hf⟩
        · intro x hx hx'
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_append_right _ (by simp)
          · exact List.mem_append_left _ (h3 x hx hx')
      · rw [scanAux, ite_eq_right hf]
        obtain ⟨tail, h1, h2, h3⟩ := ih fr
        exact ⟨tail, h1, fun x hx => ⟨List.mem_cons_of_mem _ (h2 x hx).1, (h2 x hx).2⟩,
          fun x hx hx' => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd hx' hf
            · exact h3 x hx hx'⟩

/-- `scan a D = []` ⟹ `D` 的每个字面量在当前赋值下都为假。 -/
theorem scan_nil {a : PAssign} {D : Clause} (h : scan a D = []) :
    ∀ l ∈ D, litFree a l = false := by
  obtain ⟨tail, h1, _, h3⟩ := scanAux_spec a D []
  have htail : tail = [] := by simpa [scan, h1] using h
  intro l hl
  by_cases hf : litFree a l = true
  · exact absurd (by rw [htail] at h3; exact h3 l hl hf) (by simp)
  · simpa using hf

/-- `scan a D = [l]` ⟹ `l ∈ D`，且 `D` 的其他字面量都为假。 -/
theorem scan_singleton {a : PAssign} {D : Clause} {l : Lit} (h : scan a D = [l]) :
    l ∈ D ∧ ∀ l' ∈ D, l' ≠ l → litFree a l' = false := by
  obtain ⟨tail, h1, h2, h3⟩ := scanAux_spec a D []
  have htail : tail = [l] := by simpa [scan, h1] using h
  refine ⟨(h2 l (by rw [htail]; simp)).1, ?_⟩
  intro l' hl' hne
  by_cases hf : litFree a l' = true
  · have hmem := h3 l' hl' hf
    rw [htail] at hmem
    exact absurd (List.mem_singleton.mp hmem) hne
  · simpa using hf

/-- 若一个字面量在当前赋值下"非自由"，则它的否定已被赋值。 -/
theorem litFree_eq_false {a : PAssign} {l : Lit} (h : litFree a l = false)
    {σ : Assign} (hσ : agrees σ a) : σ l.1 = !l.2 := by
  have hmem : litNeg l ∈ a := by
    by_contra hc
    simp [litFree, hc] at h
  have := hσ _ hmem
  simpa [litNeg] using this

private theorem bool_not_self (b : Bool) : (!b : Bool) = b → False := by
  cases b <;> simp

/-! ## 二、子句库的接口

内核回放只用到库的**四个操作**（取、长度、追加、建库）与**三条定律**。把表示法换掉
（`Array` → 平衡树）因此是一次**实例化**，而不是一次承重模块重证。

**为什么开这条缝**（本库实测）：`Array` 在**内核里**的
`push` 与 `get?` 都**线性于下标**，故 `rupCheck` 每步的库访问按步序增长、全证书是
关于步数的平方；换成平衡树是对数。按**归约次数**（确定性、无启动噪声）实测
$N = 200 \to 400$：`Array` 40,803 → 161,603（3.96×），`Std.TreeMap` 4,757 → 11,066
（2.33×，理论 2.26×）；外推到回放的 570,883 步，两者相差约 9,400 倍。 -/

/-- **子句库的接口**：`rupCheck`/`checkAux` 只用到这四个操作与三条定律。 -/
structure ClauseDB (Carrier : Type) where
  get? : Carrier → Nat → Option Clause
  size : Carrier → Nat
  push : Carrier → Clause → Carrier
  Mem : Carrier → Clause → Prop
  /-- 取到的子句一定在库里。 -/
  get?_mem : ∀ {d i C}, get? d i = some C → Mem d C
  /-- 追加一条后，库里的每条**要么是新的这条、要么原来就在**。
  **只要可靠性的那一半**——`checkAux_sound` 只消费这个方向，而少掉的那一半
  （`C' = C ∨ Mem d C' → Mem (push d C) C'`）正是平衡树实例需要"键 < size"那条
  不变量的地方。按**用得到的强度**立法，两个实例都干净。 -/
  push_mem : ∀ {d C C'}, Mem (push d C) C' → C' = C ∨ Mem d C'
  /-- 由 CNF 建库。 -/
  ofCNF : CNF → Carrier
  /-- 初始库里的每条**都来自**那个 CNF（同样只要用得到的那一半）。 -/
  ofCNF_mem : ∀ {F C}, Mem (ofCNF F) C → C ∈ F

namespace ClauseDB

/-- `Array` 版：**与开接口之前逐字相同的表示法**，下游 `LRATData` 用的就是它。 -/
def array : ClauseDB (Array Clause) where
  get? := fun d i => d[i]?
  size := Array.size
  push := Array.push
  Mem := fun d C => C ∈ d
  get?_mem := by
    intro d i C h
    rw [Array.mem_def]
    exact List.mem_of_getElem? (by simpa using h)
  push_mem := by
    intro d C C' h
    rw [Array.mem_push] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  ofCNF := List.toArray
  ofCNF_mem := by
    intro F C h
    exact (List.mem_toArray).mp h

/-- 树版库的成员关系：`C` 是某个键下的值。
**提成独立的 `def`**：在字面量内部写 `Mem` 会解析成结构的投影 `ClauseDB.Mem`
（它以结构本身作第一参数），于是 `Mem d C` 期望的第一个参数是 `ClauseDB`。 -/
def treeMem (d : Std.TreeMap Nat Clause compare) (C : Clause) : Prop := ∃ i, d.get? i = some C

/-- **平衡树版**：内核里每次取/插是 $O(\log n)$，故全证书是对数级累加而不是 `Array`
的平方级累加。键是**子句号减一**（0-based），`push` 追加在 `size` 处。 -/
def tree : ClauseDB (Std.TreeMap Nat Clause compare) where
  get? := fun d i => d.get? i
  size := fun d => Std.TreeMap.size d
  push := fun (d : Std.TreeMap Nat Clause compare) C =>
    Std.TreeMap.insert d (Std.TreeMap.size d) C
  Mem := treeMem
  get?_mem := fun h => ⟨_, h⟩
  push_mem := by
    intro d C C' h
    obtain ⟨i, hi⟩ := h
    simp only [Std.TreeMap.get?, Std.TreeMap.insert] at hi
    rw [Std.DTreeMap.Const.get?_insert] at hi
    split at hi
    · exact Or.inl (Option.some.inj hi).symm
    · exact Or.inr ⟨i, hi⟩
  ofCNF := fun F =>
    F.foldl (fun (d : Std.TreeMap Nat Clause compare) C =>
      Std.TreeMap.insert d (Std.TreeMap.size d) C) ∅
  ofCNF_mem := by
    intro F C h
    -- 归纳要对**累加器**泛化（折叠的中间态不是空树）
    have key : ∀ (l : List Clause) (acc : Std.TreeMap Nat Clause compare),
        treeMem (l.foldl (fun (d : Std.TreeMap Nat Clause compare) C =>
          Std.TreeMap.insert d (Std.TreeMap.size d) C) acc) C
          → C ∈ l ∨ treeMem acc C := by
      intro l
      induction l with
      | nil =>
          intro acc h
          exact Or.inr h
      | cons D ds ih =>
          intro acc h
          rw [List.foldl_cons] at h
          rcases ih _ h with hmem | hmem
          · exact Or.inl (List.mem_cons_of_mem _ hmem)
          · obtain ⟨i, hi⟩ := hmem
            simp only [Std.TreeMap.get?, Std.TreeMap.insert] at hi
            rw [Std.DTreeMap.Const.get?_insert] at hi
            split at hi
            · exact Or.inl (by simp [Option.some.inj hi])
            · exact Or.inr ⟨i, hi⟩
    rcases key F ∅ h with hmem | hmem
    · exact hmem
    · -- 空树取不到任何值：`Const.get?_emptyc` 是 `@[simp]`，故用 `simp`（defeq 匹配）
      obtain ⟨i, hi⟩ := hmem
      simp at hi

end ClauseDB

/-- 沿 hint 序列做单元传播。`h` 是 1-based 的子句号。 -/
def rupAux {K : Type} (D : ClauseDB K) (d : K) (a : PAssign) : List Nat → Bool
  | [] => false
  | h :: rest =>
      match D.get? d (h - 1) with
      | none => false
      | some E =>
          match scan a E with
          | [] => true
          | [l] => rupAux D d (l :: a) rest
          | _ => false

/-- 子句 `C` 相对数据库 `d` 是 RUP 的：把 `C` 取反后沿 `hints` 传播出冲突。 -/
def rupCheck {K : Type} (D : ClauseDB K) (d : K) (C : Clause) (hints : List Nat) : Bool :=
  rupAux D d (C.map litNeg) hints

/-- **RUP 的可靠性**：若沿 hints 传播出冲突，则任何满足 hints 所指子句的赋值必满足 `C`。 -/
theorem rupAux_sound {K : Type} (D : ClauseDB K) {σ : Assign} {d : K} :
    ∀ (hints : List Nat) (a : PAssign), agrees σ a →
      (∀ h ∈ hints, ∀ E, D.get? d (h - 1) = some E → SatClause σ E) →
      rupAux D d a hints = true → False := by
  intro hints
  induction hints with
  | nil =>
      intro a _ _ hr
      simp [rupAux] at hr
  | cons h rest ih =>
      intro a ha hsat hr
      rw [rupAux] at hr
      cases hE : D.get? d (h - 1) with
      | none =>
          rw [hE] at hr
          simp at hr
      | some E =>
          rw [hE] at hr
          dsimp only at hr
          have hsatE : SatClause σ E := hsat h (by simp) E hE
          cases hs : scan a E with
          | nil =>
              rw [hs] at hr
              obtain ⟨l, hl, hsatl⟩ := hsatE
              have h1 : σ l.1 = (!l.2 : Bool) := litFree_eq_false (scan_nil hs l hl) ha
              exact bool_not_self l.2 (h1.symm.trans hsatl)
          | cons x xs =>
              cases xs with
              | nil =>
                  rw [hs] at hr
                  have hx : σ x.1 = x.2 := by
                    obtain ⟨l', hl', hsatl'⟩ := hsatE
                    by_cases hne : l' = x
                    · rw [hne] at hsatl'
                      exact hsatl'
                    · have hlf : litFree a l' = false := (scan_singleton hs).2 l' hl' hne
                      have h1 : σ l'.1 = (!l'.2 : Bool) := litFree_eq_false hlf ha
                      exact absurd (h1.symm.trans hsatl') (bool_not_self l'.2)
                  exact ih (x :: a)
                    (fun l hl => by
                      rcases List.mem_cons.mp hl with rfl | hl
                      · exact hx
                      · exact ha l hl)
                    (fun h' hh' E' hE' => hsat h' (List.mem_cons_of_mem _ hh') E' hE') hr
              | cons y ys =>
                  rw [hs] at hr
                  simp at hr

/-! ## 三、证书的核对层 -/

/-- LRAT 的一步：`id` 是 LRAT 给出的子句号（原始子句为 `1..m`，引理从 `m+1` 起连续）。 -/
structure LStep where
  id : Nat
  clause : Clause
  hints : List Nat

/-- 逐条核对：子句号必须连续（`D.size d + 1`），每条子句必须 RUP；导出空子句即成功。 -/
def checkAux {K : Type} (D : ClauseDB K) (d : K) : List LStep → Bool
  | [] => false
  | s :: rest =>
      if s.id = D.size d + 1 ∧ rupCheck D d s.clause s.hints then
        s.clause.isEmpty || checkAux D (D.push d s.clause) rest
      else false

/-- **按给定表示法核对**：CNF 先经 `D.ofCNF` 建库，再逐条核。 -/
def checkStepsWith {K : Type} (D : ClauseDB K) (F : CNF) (steps : List LStep) : Bool :=
  checkAux D (D.ofCNF F) steps

/-- 入口（**与开接口之前逐字相同的签名**）：用 `Array` 库，故下游两个数据模块不受影响。 -/
abbrev checkSteps (F : CNF) (steps : List LStep) : Bool := checkStepsWith ClauseDB.array F steps

/-- **核对器的可靠性（核心）**：`checkAux` 返回真 ⟹ `σ` 不满足数据库。 -/
theorem checkAux_sound {K : Type} (D : ClauseDB K) {σ : Assign} :
    ∀ (d : K) (steps : List LStep), (∀ C, D.Mem d C → SatClause σ C) →
      checkAux D d steps = true → False := by
  intro d steps
  induction steps generalizing d with
  | nil => intro _ h; simp [checkAux] at h
  | cons s rest ih =>
      intro hdb h
      rw [checkAux] at h
      by_cases hcond : s.id = D.size d + 1 ∧ rupCheck D d s.clause s.hints
      · rw [ite_eq_left hcond] at h
        have hrup : rupCheck D d s.clause s.hints = true := hcond.2
        have hsat : SatClause σ s.clause := by
          by_contra hc
          simp only [SatClause, not_exists, not_and] at hc
          refine rupAux_sound D (d := d) (σ := σ) s.hints (s.clause.map litNeg) ?_ ?_ hrup
          · intro l hl
            rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
            have hne : ¬(σ l₀.1 = l₀.2) := hc l₀ hl₀
            simp only [litNeg]
            cases h1 : σ l₀.1 <;> cases h2 : l₀.2 <;> simp_all
          · intro _ _ E hE
            exact hdb E (D.get?_mem hE)
        rcases Bool.or_eq_true_iff.mp h with hemp | hrest
        · rw [List.isEmpty_iff.mp hemp] at hsat
          obtain ⟨l, hl, _⟩ := hsat
          simp at hl
        · exact ih (D.push d s.clause) (fun C hC => by
            rcases D.push_mem hC with hEq | hC
            · subst hEq
              exact hsat
            · exact hdb C hC) hrest
      · rw [ite_eq_right hcond] at h
        simp at h

/-- **主定理（入口）**：内核核对通过 ⟹ 该 CNF 不可满足。 -/
theorem checkSteps_sound {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := by
  rintro ⟨σ, hσ⟩
  exact checkAux_sound ClauseDB.array (ClauseDB.array.ofCNF F) steps
    (fun C hC => hσ C (ClauseDB.array.ofCNF_mem hC)) h

/-- 生成器使用的入口（与 `checkSteps_sound` 同一内容，证明项形态）。 -/
theorem unsat_of_checkSteps {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := checkSteps_sound h




end QECCertificates.LRAT
