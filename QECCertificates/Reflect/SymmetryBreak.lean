/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.BB144Symmetry

/-!
# 对称性破缺的忠实性：破缺后不可满足 ⟹ 原命题不可满足

`tools/bb144_server/bb144_sb.py` 把一条 CNF 加上"字典序轨道代表"约束后再交给求解器。
那条路线要的方向是

    破缺后的 CNF 不可满足  ⟹  原 CNF 不可满足

本模块证它的**语义核心**，并把核心实例化到 BB $[[144,12,12]]$ 的平移群上。

## 核心：轨道提升引理

设 `G` 是 `α` 上的一族置换（**只要求有限、且含恒等**，不需要是子群），`≤` 是 `α` 上的
全序，`P` 是在 `G` 下**不变**的谓词。定义破缺谓词

    OrbitMin G P a  :=  P a ∧ ∀ g ∈ G, a ≤ g a

则 **`∃ a, OrbitMin G P a` ⟺ `∃ a, P a`**（`orbitMin_iff_exists`）。两个方向：

* `⟸`：取 `a` 满足 `P`，在**它的轨道**里取 `≤`-最小元 `m`。`m` 是某个 `g a`，故由不变性
  `P m` 成立；又对任何 `h ∈ G`，`h m` 仍在同一轨道里，故 `m ≤ h m`。于是 `m` 满足破缺谓词。
* `⟹`：破缺谓词本来就蕴含 `P`。

**方向就是路线要的那一条**：把 `⟹` 取逆否，得"不存在破缺解 ⟹ 不存在原解"。而 `⟸` 半边
（每轨道留得住一个代表元）正是**过紧**的失效模式所在——破缺编码若多切掉东西，缺的就是这一
半边。故两条都证，不省。

**为什么"含恒等"是必需的**：`⟸` 要用"`P a` 的 `a` 确实在它自己的轨道里"。

## 与 CNF 层的关系（本模块**不做**的那一步，如实标注）

本模块说的是**语义**：`P` 是一个 `Prop`，`OrbitMin` 是它的约束形态。要把
`tools/bb144_server/bb144_sb.py` 生成的**那一份 CNF**接上，还需要

    SatFormula τ (破缺 CNF)  ⟹  ∃ a, OrbitMin G P a

即"CNF 的可满足赋值经 `x`/`w` 投影后给出破缺语义解"——它由 `Reflect/Encode.lean` 的
`buildPair_sat` 那一套（Tseitin 链、乘积块、顺序计数器的可靠性）加上词典序比较器子句的
可靠性拼成。**那一步不在本模块**：本模块交付的是它的语义前提与轨道引理，`Reflect/` 里
faithfulness 那一族的下一个模块接它。
-/

namespace QECCertificates

open scoped BigOperators

-- `GrossGroup`（`= ZMod 12 × ZMod 6`）在上游 QEC 的命名空间里
open Quantum.Stabilizer.Homological.BB

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `a` 在 `G` 下的**轨道**：所有 `g a`（`g ∈ G`）组成的有限集。

用 `Finset.univ.filter` 而不是 `G.image`：前者的描述与"轨道是 `α` 的有限子集"这一
事实逐字对应，且不需要 `Equiv.Perm α` 上的 `DecidableEq`。 -/
def orbitOf (G : Finset (Equiv.Perm α)) (a : α) : Finset α :=
  Finset.univ.filter (fun b => ∃ g ∈ G, g a = b)

theorem mem_orbitOf {G : Finset (Equiv.Perm α)} {a b : α} :
    b ∈ orbitOf G a ↔ ∃ g ∈ G, g a = b := by
  simp [orbitOf]

/-- 含恒等时 `a` 在自己的轨道里——`⟸` 半边靠的就是这一条。 -/
theorem self_mem_orbitOf (G : Finset (Equiv.Perm α)) (h1 : 1 ∈ G) (a : α) :
    a ∈ orbitOf G a :=
  mem_orbitOf.mpr ⟨1, h1, rfl⟩

/-- **轨道提升引理**：有限轨道里有最小元。

证明只用"轨道有限且非空"——不需要 `G` 是子群，也不需要 `G` 含恒等（非空性由调用方给）。
这是本模块唯一用到 `LinearOrder` 的地方。 -/
theorem exists_min_orbitOf [LinearOrder α] (G : Finset (Equiv.Perm α)) {a : α}
    (hne : (orbitOf G a).Nonempty) :
    ∃ m ∈ orbitOf G a, ∀ b ∈ orbitOf G a, m ≤ b :=
  let ⟨m, hm, hmin⟩ := Finset.exists_min_image (orbitOf G a) id hne
  ⟨m, hm, fun b hb => hmin b hb⟩

/-- `P` 在 `G` 下不变。 -/
def IsInvariant (G : Finset (Equiv.Perm α)) (P : α → Prop) : Prop :=
  ∀ g ∈ G, ∀ a, P (g a) ↔ P a

/-- **破缺谓词**：`P` 成立，且 `a` 在自己的轨道里 `≤`-最小。

这正是 `bb144_sb.py` 每加一条字典序约束所断言的语义形态；工具对**每个** `g ≠ e` 各加一条，
故这里对 `∀ g ∈ G` 全取。 -/
def OrbitMin [LE α] (G : Finset (Equiv.Perm α)) (P : α → Prop) (a : α) : Prop :=
  P a ∧ ∀ g ∈ G, a ≤ g a

/-- **忠实性（本模块的主定理）**：破缺谓词可满足 ⟺ 原谓词可满足。

`⟸` 是本模块的内容（取轨道最小元）；`⟹` 平凡。**两边都证**：`⟹` 是路线要的方向
（逆否即"破缺不可满足 ⟹ 原不可满足"），而 `⟸` 排除**过紧**——它断言每轨道至少留得住
一个代表元，破缺不会把解切光。 -/
theorem orbitMin_iff_exists [LinearOrder α] (G : Finset (Equiv.Perm α)) (h1 : 1 ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, h * g ∈ G) (P : α → Prop) (hP : IsInvariant G P) :
    (∃ a, OrbitMin G P a) ↔ (∃ a, P a) := by
  constructor
  · rintro ⟨a, ha, _⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, hmin⟩ :=
      exists_min_orbitOf G ⟨a, self_mem_orbitOf G h1 a⟩
    obtain ⟨g, hg, hga⟩ := mem_orbitOf.mp hm
    have hPm : P m := by
      rw [← hga]
      exact (hP g hg a).mpr ha
    refine ⟨m, hPm, fun h hh => ?_⟩
    exact hmin (h m) (mem_orbitOf.mpr ⟨h * g, hmul g hg h hh, by rw [← hga]; rfl⟩)

/-- **路线要的方向，取逆否**：破缺谓词不可满足 ⟹ 原谓词不可满足。

写成这一形态是为了与工具侧的用法逐字对应（求解器报 UNSAT，结论落到原命题上）。 -/
theorem not_exists_of_not_exists_orbitMin [LinearOrder α] (G : Finset (Equiv.Perm α))
    (h1 : 1 ∈ G) (hmul : ∀ g ∈ G, ∀ h ∈ G, h * g ∈ G) (P : α → Prop)
    (hP : IsInvariant G P) :
    ¬ (∃ a, OrbitMin G P a) → ¬ (∃ a, P a) :=
  fun h => h ∘ (orbitMin_iff_exists G h1 hmul P hP).mpr

/-! ## 实例化：BB $[[144,12,12]]$ 的平移群与"轻逻辑算符"谓词

`Codes/BB144Symmetry.lean` 给的三条（保重量、保两侧行空间、保配对）合起来就是
"这套作用把逻辑算符映成逻辑算符"——即本模块要求的 `IsInvariant`。下面的 `bb144Group`
取 72 个平移（工具 `--perms all` 那一档），`1 ∈ G` 由 `(0,0)` 那一项给出。 -/

open QECCertificates.BB144Distance

/-- BB144 的平移群，写成置换的有限集（工具 `--perms all` 的 72 个）。 -/
noncomputable def bb144Group : Finset (Equiv.Perm (Fin 144)) :=
  Finset.univ.image fun t : GrossGroup => bb144Trans t

/-- 群里有恒等——`⟸` 半边的前提。 -/
theorem bb144Group_one_mem : (1 : Equiv.Perm (Fin 144)) ∈ bb144Group := by
  refine Finset.mem_image.mpr ⟨(0 : GrossGroup), Finset.mem_univ 0, ?_⟩
  ext c
  simp [bb144Trans]

/-- **不变性**：平移把逻辑算符映成逻辑算符。

四条假设逐条对应 `(x, w)` 对上的逻辑算符定义——`x` 在 `H_X` 的核里、`w` 在 `H_Z` 的核里、
配对为 1、以及重量上界。前三条由 `Codes/BB144Symmetry.lean` 的三条给出；重量那一条由
`bb144Trans_hammingNorm` 给出。 -/
theorem bb144_isLogical_invariant (t : GrossGroup) (v w : Vec 144)
    (hv : inKerB bb144Hx v = true) (hw : inKerB bb144Hz w = true)
    (hpair : v ⬝ᵥ w = 1) (hwt : hammingNorm v ≤ 11) :
    inKerB bb144Hx (permVec (bb144Trans t) v) = true ∧
    inKerB bb144Hz (permVec (bb144Trans t) w) = true ∧
    (permVec (bb144Trans t) v) ⬝ᵥ (permVec (bb144Trans t) w) = 1 ∧
    hammingNorm (permVec (bb144Trans t) v) ≤ 11 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- x 在核里：置换保核（`inKerB_permVec`），假设是「逆置换把校验行映成校验行」
    exact inKerB_permVec bb144Hx (bb144Trans t)
      (fun i => by
        rw [bb144Trans_symm_eq]
        exact bb144_permVec_hxRow_mem (-t) (List.mem_ofFn.mpr ⟨i, rfl⟩)) hv
  · exact inKerB_permVec bb144Hz (bb144Trans t)
      (fun i => by
        rw [bb144Trans_symm_eq]
        exact bb144_permVec_hzRow_mem (-t) (List.mem_ofFn.mpr ⟨i, rfl⟩)) hw
  · rw [bb144Trans_dotProduct]
    exact hpair
  · rw [bb144Trans_hammingNorm]
    exact hwt

end QECCertificates
