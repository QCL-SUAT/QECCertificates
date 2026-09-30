/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.GF2.KernelBasis

/-!
# 算符代数层（算符树）与判定层（GF(2) 辛表示）的翻译定理（Q3）

指南点名要求"为算符代数层建**算符树中间表示**（把 Pauli 与逻辑算符的表达式写成树形），
并与判定层的 GF(2) 辛表示之间给出**机器检验的翻译定理**——算符代数走树、
距离与秩判定走向量，两套表示各司其职又互相衔接"。本模块是该要求的第一条落地。

## 两层表示

| 层 | 对象 | 运算 |
|---|---|---|
| 算符代数层（树） | `PauliExpr n`：叶 ="在第 `i` 位放单点 Pauli"，节点 = 乘法 | `PauliExpr.mul` |
| 判定层（向量） | `Vec n × Vec n`：`(Z 侧, X 侧)` 两个 GF(2) 向量 | 逐位加 |

翻译 `toSymp` 把树求值成 Pauli 字再取辛编码；**主定理说它是乘法同态**：

  `toSymp (mul a b) = toSymp a + toSymp b`.

第二条翻译定理是**对易判据**：算符层"对易"（反对易站点数为偶数）
等价于判定层辛内积为零。这条判据是稳定子码一切结构断言的入口。

## 为什么两层都要

* 树层贴近**表达式**：逻辑算符、稳定子生成元、线路中间结果天然是表达式，
  在树上做重写（合并同类项、消去 `P·P = 1`）不需要展开成 $2^n$ 维向量；
* 向量层贴近**判定**：对易、秩、距离都是 GF(2) 上的线性代数，向量层可直接调用
  `QECCertificates.GF2` 的整套机器。

## 主结果

* `Pauli.symp_mul`：单点乘法 ↔ 辛编码相加。
* `Pauli.anti_eq_symp`：单点反对易指示 = 单点辛内积。
* `toSymp_mul` / `toSymp_one`：**翻译是乘法同态**。
* `commutesWord_iff_symplectic` / `commutes_iff_symplectic`：**对易判据（字版与树版）**。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 单点 Pauli -/

/-- 单量子比特 Pauli 算符（模去相位；相位不进辛表示）。 -/
inductive Pauli where
  | I | X | Y | Z
  deriving DecidableEq, Repr

instance : Fintype Pauli where
  elems := {.I, .X, .Y, .Z}
  complete := by intro p; cases p <;> simp

namespace Pauli

/-- 模去相位的 Pauli 乘法（Pauli 群横模 $\{\pm1,\pm i\}$ 后的群运算）。 -/
def mul : Pauli → Pauli → Pauli
  | .I, q => q
  | p, .I => p
  | .X, .X => .I
  | .X, .Y => .Z
  | .X, .Z => .Y
  | .Y, .X => .Z
  | .Y, .Y => .I
  | .Y, .Z => .X
  | .Z, .X => .Y
  | .Z, .Y => .X
  | .Z, .Z => .I

/-- **辛编码**：`(Z 分量, X 分量)`。$I\mapsto(0,0)$、$X\mapsto(0,1)$、
$Z\mapsto(1,0)$、$Y\mapsto(1,1)$。 -/
def symp : Pauli → ZMod 2 × ZMod 2
  | .I => (0, 0)
  | .X => (0, 1)
  | .Y => (1, 1)
  | .Z => (1, 0)

/-- **单点反对易指示**：非恒等且两者不同 ⟹ 1（反对易），否则 0（对易）。

按物理定义直接给出（$X,Y,Z$ 两两反对易），不借助辛编码——
下文的 `anti_eq_symp` 才是"它与辛内积一致"的机器检验定理。 -/
def anti : Pauli → Pauli → ZMod 2
  | .I, _ => 0
  | _, .I => 0
  | .X, .X => 0
  | .Y, .Y => 0
  | .Z, .Z => 0
  | _, _ => 1

@[simp] lemma mul_I_left (p : Pauli) : mul .I p = p := by cases p <;> rfl
@[simp] lemma mul_I_right (p : Pauli) : mul p .I = p := by cases p <;> rfl
@[simp] lemma mul_self (p : Pauli) : mul p p = .I := by cases p <;> rfl
lemma mul_comm (p q : Pauli) : mul p q = mul q p := by fin_cases p <;> fin_cases q <;> rfl
lemma mul_assoc (p q r : Pauli) : mul (mul p q) r = mul p (mul q r) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> rfl

/-- **翻译定理（单点）**：单点乘法过去就是辛编码逐位相加。 -/
lemma symp_mul (p q : Pauli) : symp (mul p q) = symp p + symp q := by
  fin_cases p <;> fin_cases q <;> decide

@[simp] lemma anti_self (p : Pauli) : anti p p = 0 := by cases p <;> rfl
lemma anti_comm (p q : Pauli) : anti p q = anti q p := by fin_cases p <;> fin_cases q <;> decide

/-- **翻译定理（单点对易判据）**：反对易指示恰好等于单点辛内积
`(z_p x_q + z_q x_p)`。 -/
lemma anti_eq_symp (p q : Pauli) :
    anti p q = (symp p).1 * (symp q).2 + (symp q).1 * (symp p).2 := by
  fin_cases p <;> fin_cases q <;> decide

end Pauli

/-! ## Pauli 字（判定层的对象） -/

/-- Pauli 字：每个位置放一个单点 Pauli。这是辛表示的原像。 -/
abbrev PauliWord (n : ℕ) := Fin n → Pauli

/-- **判定层的辛向量对**：`(Z 侧, X 侧)`。 -/
def sympWord (w : PauliWord n) : Vec n × Vec n :=
  ((fun i => (Pauli.symp (w i)).1), (fun i => (Pauli.symp (w i)).2))

@[simp] lemma sympWord_fst (w : PauliWord n) : (sympWord w).1 = fun i => (Pauli.symp (w i)).1 := rfl
@[simp] lemma sympWord_snd (w : PauliWord n) : (sympWord w).2 = fun i => (Pauli.symp (w i)).2 := rfl

/-- **算符层对易**：反对易的站点数为偶数（GF(2) 上求和为零）。 -/
def commutesWord (u v : PauliWord n) : Prop := (∑ i, Pauli.anti (u i) (v i)) = 0

lemma commutesWord_symm {u v : PauliWord n} (h : commutesWord u v) : commutesWord v u := by
  rw [commutesWord] at h ⊢
  have hswap : (∑ i, Pauli.anti (v i) (u i)) = (∑ i, Pauli.anti (u i) (v i)) :=
    Finset.sum_congr rfl fun i _ => Pauli.anti_comm (v i) (u i)
  rw [hswap]; exact h

/-- 每个 Pauli 字与自己对易（辛形式是交错的）。 -/
@[simp] lemma commutesWord_self (u : PauliWord n) : commutesWord u u := by
  rw [commutesWord]
  exact Finset.sum_eq_zero fun i _ => Pauli.anti_self (u i)

/-- **对易判据（字版）**：算符层对易 ⟺ 判定层辛内积为零。

证明是把单点对应 `anti_eq_symp` 逐点搬过来再拆和——
两层的"对易"是同一个 GF(2) 二次型的两个写法。 -/
theorem commutesWord_iff_symplectic (u v : PauliWord n) :
    commutesWord u v ↔
      (sympWord u).1 ⬝ᵥ (sympWord v).2 + (sympWord v).1 ⬝ᵥ (sympWord u).2 = 0 := by
  rw [commutesWord]
  have hcongr : ∑ i, Pauli.anti (u i) (v i)
      = ∑ i, ((sympWord u).1 i * (sympWord v).2 i + (sympWord v).1 i * (sympWord u).2 i) :=
    Finset.sum_congr rfl fun i _ => Pauli.anti_eq_symp (u i) (v i)
  rw [hcongr, Finset.sum_add_distrib]
  rw [show (∑ i, (sympWord u).1 i * (sympWord v).2 i)
        = (sympWord u).1 ⬝ᵥ (sympWord v).2 from rfl,
      show (∑ i, (sympWord v).1 i * (sympWord u).2 i)
        = (sympWord v).1 ⬝ᵥ (sympWord u).2 from rfl]

/-! ## 算符树（算符代数层的对象） -/

/-- **算符树**：叶是"在第 `i` 位放单点 Pauli"，节点是乘法，另有显式单位。

这是指南点名的"算符代数层中间表示"：表达式在树上做重写
（合并、消去 $P\cdot P = 1$）不必展开成 $2^n$ 维向量。 -/
inductive PauliExpr (n : ℕ) where
  /-- 在第 `i` 位放单点 Pauli `p`。 -/
  | atom (i : Fin n) (p : Pauli)
  /-- 单位算符。 -/
  | one
  /-- 乘法节点。 -/
  | mul (a b : PauliExpr n)

namespace PauliExpr

/-- 树求值：叶展开为"单位向量上的单点 Pauli"，乘法节点逐位相乘。 -/
def eval : PauliExpr n → PauliWord n
  | .atom i p => fun j => if j = i then p else .I
  | .one => fun _ => .I
  | .mul a b => fun i => Pauli.mul (eval a i) (eval b i)

/-- **两层之间的翻译**：算符树 → GF(2) 辛向量对。 -/
def toSymp (e : PauliExpr n) : Vec n × Vec n := sympWord (eval e)

@[simp] lemma eval_one : eval (.one : PauliExpr n) = fun _ => Pauli.I := rfl

@[simp] lemma eval_mul (a b : PauliExpr n) :
    eval (.mul a b) = fun i => Pauli.mul (eval a i) (eval b i) := rfl

@[simp] lemma toSymp_one : toSymp (.one : PauliExpr n) = 0 := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [toSymp, sympWord, Pauli.symp]

/-- **主翻译定理（乘法同态）**：算符树上的乘法，翻译过去就是辛向量的逐位加。

这正是"两套表示互相衔接"的内容：树层的结构运算（乘法）在判定层是线性的，
于是树上的表达式可以整体翻译到向量层，交给 `QECCertificates.GF2` 的线性代数机器。 -/
theorem toSymp_mul (a b : PauliExpr n) : toSymp (.mul a b) = toSymp a + toSymp b := by
  refine Prod.ext ?_ ?_ <;>
    · funext i
      simp only [toSymp, sympWord, eval_mul, Prod.fst_add, Prod.snd_add, Pi.add_apply,
        Pauli.symp_mul, Prod.fst_add, Prod.snd_add]

/-- 叶子的翻译：只有第 `i` 位非零。 -/
lemma toSymp_atom (i : Fin n) (p : Pauli) :
    toSymp (.atom i p)
      = ((fun j => if j = i then (Pauli.symp p).1 else 0),
         (fun j => if j = i then (Pauli.symp p).2 else 0)) := by
  refine Prod.ext ?_ ?_ <;> funext j <;>
    · simp only [toSymp, sympWord, eval]
      by_cases h : j = i <;> simp [h, Pauli.symp]

/-- **算符层对易（树版）**：把两棵树各自求值后按字判对易。 -/
def commutes (a b : PauliExpr n) : Prop := commutesWord (eval a) (eval b)

/-- **对易翻译定理（树版）**：树层对易 ⟺ 判定层辛内积为零。

这是本模块对外的**主判据**：稳定子码的一切结构断言（元素属于稳定子群、
逻辑算符与稳定子对易、码距候选与校验对易）都归约到它。 -/
theorem commutes_iff_symplectic (a b : PauliExpr n) :
    commutes a b ↔ (toSymp a).1 ⬝ᵥ (toSymp b).2 + (toSymp b).1 ⬝ᵥ (toSymp a).2 = 0 :=
  commutesWord_iff_symplectic (eval a) (eval b)

end PauliExpr

end QECCertificates
