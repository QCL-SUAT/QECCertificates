/-
本模块：边界约定承重的**族级**形态。
-/
import QECCertificates.GF2.Basic

/-!
# 删掉边界探测器，距离对**任何**码都塌到 $1$（族级形态）

论文 §V 的 C3 那条现在是**实例**（Bacon–Shor、$20$ 个槽位）。本模块把它升成**族级**：
**机制根本不看码**——一处数据故障放在第 $0$ 轮，数据错误**持续**到所有后续轮，
于是各轮 syndrome 恒等，相邻轮比较**全部**静默；边界探测器一删，再没有东西看得见它，
而读出在**每一轮**都是 $1$。

模型是那个全协议模型的**比较层抽象**：$T+1$ 轮、每轮一个数据故障向量、
校验矩阵任意、读出泛函任意，探测器只取**相邻轮比较**（边界探测器正是被删掉的那一个）。

**主定理**：`boundaryRemoved_distance_eq_one`——对**任何** `n`、任何校验矩阵 `H`、
任何读出 `w`、任何轮数 `T`，同时满足"比较全静默"与"每轮读出为 $1$"的故障，
其时空重量的最小值**恰为 $1$**。

证明里 `H` 一次也没被真正用到，这正是结论强的地方：**塌落与码无关**，
它是"故障可以持续"这一建模事实的推论。故 C1 与 C2 是码的性质，C3 不是。
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {n m : ℕ}

/-- 逐轮故障：`T + 1` 轮，每轮一个数据故障向量。 -/
abbrev RoundFault (T n : ℕ) := Fin (T + 1) → Vec n

/-- **累积故障**：第 `t` 轮结束时数据上还挂着的错误——第 `s ≤ t` 轮的故障都还在。 -/
def cum {T n : ℕ} (f : RoundFault T n) (t : Fin (T + 1)) : Vec n :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin (T + 1) => s ≤ t), f s

/-- 时空重量 = 各轮重量之和（每一处故障位置计一次）。 -/
def faultWeight {T n : ℕ} (f : RoundFault T n) : ℕ := ∑ t, hammingNorm (f t)

/-- **相邻轮比较全静默**：每一对相邻轮的 syndrome 相等。 -/
def ComparisonsSilent {T n m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (f : RoundFault T n) : Prop :=
  ∀ t : Fin T, H *ᵥ cum f t.castSucc = H *ᵥ cum f t.succ

/-- 第 `t` 轮的读出：读出泛函作用在**累积**故障上。 -/
def readout {T n : ℕ} (w : Vec n) (f : RoundFault T n) (t : Fin (T + 1)) : ZMod 2 :=
  w ⬝ᵥ cum f t

/-- 见证：只在第 $0$ 轮放一个 `e j`，其余轮全零。 -/
def witFault {T n : ℕ} (j : Fin n) : RoundFault T n :=
  fun t => if t = 0 then e j else 0

/-! ## 一、两条基向量引理 -/

/-- `e j` 的支撑恰是单点集。 -/
lemma support_e {n : ℕ} (j : Fin n) : support (e j) = {j} := by
  ext i
  simp [support, e]

/-- `e j` 的重量是 $1$。 -/
lemma hammingNorm_e {n : ℕ} (j : Fin n) : hammingNorm (e j) = 1 := by
  rw [← weight_eq_hammingNorm, support_e]
  simp

/-! ## 二、见证的三条读数 -/

/-- 见证的累积恒为 `e j`：故障在第 $0$ 轮放下，之后**一直在**。 -/
lemma cum_witFault {T n : ℕ} (j : Fin n) (t : Fin (T + 1)) :
    cum (witFault (T := T) j) t = e j := by
  classical
  unfold cum witFault
  rw [Finset.sum_eq_single (0 : Fin (T + 1))]
  · simp
  · intro s _ hs
    simp [hs]
  · intro h
    exact absurd (Finset.mem_filter.mpr
      ⟨Finset.mem_univ (0 : Fin (T + 1)), Fin.zero_le t⟩) h

/-- `w ⬝ᵥ e j = w j`。 -/
lemma dot_e {n : ℕ} (w : Vec n) (j : Fin n) : w ⬝ᵥ e j = w j := by
  classical
  rw [dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [e]
  · intro b _ hb
    simp [e, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- 见证让**任何**校验矩阵的相邻轮比较全静默：各轮 syndrome 恒等。 -/
theorem comparisonsSilent_witFault {T : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (j : Fin n) : ComparisonsSilent H (witFault (T := T) j) := by
  intro t
  rw [cum_witFault, cum_witFault]

/-- 见证在**每一轮**的读出都是 `w j`。 -/
lemma readout_witFault {T : ℕ} (w : Vec n) (j : Fin n) (t : Fin (T + 1)) :
    readout w (witFault (T := T) j) t = w j := by
  unfold readout
  rw [cum_witFault, dot_e]

/-- 见证的时空重量恰为 $1$——只在第 $0$ 轮有一处非零。 -/
lemma faultWeight_witFault {T : ℕ} (j : Fin n) :
    faultWeight (witFault (T := T) (n := n) j) = 1 := by
  classical
  unfold faultWeight witFault
  rw [Finset.sum_eq_single (0 : Fin (T + 1))]
  · simp [hammingNorm_e]
  · intro s _ hs
    simp [hs]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (T + 1))) h

/-! ## 三、上界：见证

**只要读出泛函在某处读到 $1$，见证就在那里**——不需要它是逻辑算符，
也不需要任何关于码距的假设（`H` 完全不出现）。 -/

/-- **上界（族级）**：任何非零读出、任何校验矩阵、任何轮数，
都存在重量恰为 $1$ 的比较静默故障，且每一轮读出都是 $1$。 -/
theorem boundaryRemoved_witness {T : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) (j : Fin n) (hj : w j = 1) :
    ∃ f : RoundFault T n, ComparisonsSilent H f ∧ (∀ t, readout w f t = 1) ∧
      faultWeight f = 1 :=
  ⟨witFault j, comparisonsSilent_witFault H j,
   fun _ => by rw [readout_witFault, hj], faultWeight_witFault j⟩

/-! ## 四、下界：重量不可能为 $0$ -/

/-- **下界（族级）**：每一轮读出都是 $1$ 的故障，重量至少 $1$——
零故障的每一轮读出都是 $0$。 -/
theorem one_le_faultWeight_of_readout {T : ℕ} {w : Vec n} {f : RoundFault T n}
    (hf : ∀ t, readout w f t = 1) : 1 ≤ faultWeight f := by
  by_contra hlt
  have hzero : faultWeight f = 0 := by omega
  have hround : ∀ t : Fin (T + 1), f t = 0 := fun t =>
    hammingNorm_eq_zero.mp (Finset.sum_eq_zero_iff.mp hzero t (Finset.mem_univ t))
  have hcum : cum f 0 = 0 := by
    unfold cum
    exact Finset.sum_eq_zero fun s _ => hround s
  have h1 : w ⬝ᵥ (0 : Vec n) = 1 := by
    have h := hf 0
    unfold readout at h
    rwa [hcum] at h
  simp at h1

/-! ## 五、主定理 -/

/-- **删掉边界探测器之后，故障距离恰为 $1$——对任何码、任何轮数。**

两向都给出：一个重量 $1$ 的见证，以及"没有重量 $0$ 的"。于是那个最小值**恰**是 $1$，
且它与 `H` 无关——这正是 C3 与 C1、C2 的区别：后两者是码的性质，C3 是
"故障被读成累积"这一建模事实的推论。 -/
theorem boundaryRemoved_distance_eq_one {T : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) (j : Fin n) (hj : w j = 1) :
    (∃ f : RoundFault T n, ComparisonsSilent H f ∧ (∀ t, readout w f t = 1) ∧
        faultWeight f = 1) ∧
      (∀ f : RoundFault T n, ComparisonsSilent H f → (∀ t, readout w f t = 1) →
        1 ≤ faultWeight f) :=
  ⟨boundaryRemoved_witness H w j hj,
   fun _ _ hf => one_le_faultWeight_of_readout hf⟩

end QECCertificates
