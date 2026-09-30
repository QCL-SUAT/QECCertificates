/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Reflect.Faithful
import QECCertificates.Reflect.Complete
import QECCertificates.Codes.BB18Anchor
import QECCertificates.GF2.HGPCleaning

/-!
# 证书即下界：把内核回放接成一条码距定理

`Reflect/LRATData.lean` 把本包流水线（`tools/bb144_server` 的编码器加 cadical 的 LRAT）
的产物搬进内核，`Reflect/LRAT.lean` 把它变成 `¬ Satisfiable <CNF>`；`Reflect/Encode.lean`
与 `Reflect/Complete.lean` 又证明该 CNF 可满足**当且仅当**它的语义四条件成立。三段各自
成立，但在本模块之前从未接起来：`_unsat` 那几条定理的消费者只有根文件的审计行，
它们是展品而不是承重件。

本模块补的正是那最后一接。语义四条件里

* `∀ r ∈ Rker, dotS σ r = false` 是"`σ` 的前 `n` 位读出的码向量在核里"，
* `∀ r ∈ Rpair, dotS (fun t => σ (n+t)) r = false` 是"配对向量在核里"，
* `dotS (fun t => σ t && σ (n+t)) (range n) = true` 是"两者配对为 1"，
* `cntS σ (range n) ≤ k` 是"重量不超过 `k`"，

于是"不存在满足赋值"与"该码不存在重量 `≤ k` 的逻辑算符"是同一句话。把两边读法
（`Assign` 的指示读法与 `Vec n`）桥起来，证书回放就**直接给出距离下界**：对 BB
$[[18,4,4]]$ 得到 `4 ≤ d`，与 `Codes/BB18Anchor.lean` 由枚举得到的 `bb18_dx` 是
**两条独立路线**给出的同一个数。这是"证书是验证的单位"这句话的可执行含义。

**边界**：本模块只桥接 BB18 一档；其余三档（rep7 / Steane / 环面 $[[18,2,3]]$）形式相同。
-/

namespace QECCertificates.LRAT

/-! ## 两种读法：赋值 ↔ 码向量 -/

/-- 赋值的前 `n` 位读成码向量：`σ` 为真处取 1，否则取 0。 -/
def vecOf (σ : Assign) (n : ℕ) : Vec n := fun i => if σ i.val then 1 else 0

/-- 支持列表读成码向量：`r` 中列出的位置取 1，否则取 0。 -/
def rowOf (n : ℕ) (r : List Nat) : Vec n := fun i => if i.val ∈ r then 1 else 0

/-- `vecOf` 的非零判定：第 `i` 位非零当且仅当 `σ` 在该位取真。 -/
theorem vecOf_apply_ne_zero {σ : Assign} {n : ℕ} {i : Fin n} :
    vecOf σ n i ≠ 0 ↔ σ i.val = true := by
  unfold vecOf
  cases h : σ i.val <;> simp_all

/-! ## 桥一：支撑大小恰是计数 -/

/-- `vecOf` 的支撑集大小恰是赋值的计数——两种读法给出同一个重量。 -/
theorem support_vecOf_card (σ : Assign) (n : ℕ) :
    (support (vecOf σ n)).card = cntS σ (List.range n) := by
  have h1 : (support (vecOf σ n)).card
      = ∑ t ∈ Finset.range n, if σ t = true then (1 : ℕ) else 0 := by
    rw [support, Finset.card_filter]
    have h : (∑ i : Fin n, if vecOf σ n i ≠ 0 then (1 : ℕ) else 0)
        = ∑ i : Fin n, if σ i.val = true then (1 : ℕ) else 0 :=
      Finset.sum_congr rfl fun i _ => by
        by_cases hv : vecOf σ n i ≠ 0
        · have ht : σ i.val = true := vecOf_apply_ne_zero.mp hv
          simp [hv, ht]
        · have ht : ¬ (σ i.val = true) := fun hc => hv (vecOf_apply_ne_zero.mpr hc)
          simp [hv, ht]
    rw [h]
    exact Fin.sum_univ_eq_sum_range (fun t => if σ t = true then (1 : ℕ) else 0) n
  have h2 : cntS σ (List.range n)
      = ∑ t ∈ Finset.range n, if σ t = true then (1 : ℕ) else 0 := by
    unfold cntS
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter σ List.nodup_range),
      List.toFinset_filter, List.toFinset_range]
    exact Finset.card_filter (fun t => σ t = true) (Finset.range n)
  rw [h1, h2]

/-! ## 桥二：支持列表上的异或点积与 `dotProduct` -/

/-- `cntS` 的递推（本版 `List.filter` 的谓词是 `Bool`）。 -/
theorem cntS_cons (σ : Assign) (j : Nat) (s : List Nat) :
    cntS σ (j :: s) = (if σ j then 1 else 0) + cntS σ s := by
  unfold cntS
  cases h : σ j <;> simp [h, Nat.add_comm]

/-- 加一翻转奇偶性。 -/
theorem even_one_add (m : ℕ) : Even (1 + m) ↔ ¬ Even m := by
  rw [Nat.add_comm 1 m, Nat.even_add_one]

/-- `dotS` 就是奇偶性：异或点积为假当且仅当真值个数为偶数。

这一步不需要支持列表无重复——异或与计数各自按重数计。 -/
theorem dotS_eq_false_iff_even (σ : Assign) (r : List Nat) :
    dotS σ r = false ↔ Even (cntS σ r) := by
  induction r with
  | nil => simp
  | cons j s ih =>
    rw [dotS_cons, cntS_cons]
    cases h : σ j <;> cases hb : dotS σ s <;> simp_all [even_one_add]

/-- `ℕ` 到 `ZMod 2` 的像为零当且仅当该数偶。 -/
theorem natCast_zmod2_eq_zero_iff_even (c : ℕ) : ((c : ZMod 2) = 0) ↔ Even c := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.even_iff]

/-- 乘积展开：`rowOf` 与 `vecOf` 的逐项乘积是指示函数。 -/
theorem dotProduct_rowOf_vecOf (σ : Assign) (n : ℕ) (r : List Nat) :
    (rowOf n r) ⬝ᵥ (vecOf σ n)
      = ∑ i : Fin n, (if (i : ℕ) ∈ r then (if σ i.val then (1 : ZMod 2) else 0) else 0) := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [rowOf, vecOf]
    by_cases h : (i : ℕ) ∈ r <;> simp [h]

/-- 指示和就是计数：支持列表上的指示函数之和等于赋值的计数。

`hrn`（无重复）在这里才用到——`dotS` 按重数计，而 `Finset` 不。 -/
theorem sum_indicator_eq_cntS (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    (∑ i : Fin n, (if (i : ℕ) ∈ r then (if σ i.val then (1 : ZMod 2) else 0) else 0))
      = ((cntS σ r : ℕ) : ZMod 2) := by
  have hcard : {t ∈ r.toFinset | σ t = true}.card = cntS σ r := by
    have h1 : (r.toFinset.filter (fun t => σ t = true)).card
        = (r.filter σ).toFinset.card := by
      rw [List.toFinset_filter]
    have h2 : (r.filter σ).toFinset.card = (r.filter σ).length :=
      List.toFinset_card_of_nodup (List.Nodup.filter σ hrn)
    unfold cntS
    exact h1.trans h2
  simp only [← List.mem_toFinset]
  rw [Fin.sum_univ_eq_sum_range
      (fun t => if t ∈ r.toFinset then (if σ t then (1 : ZMod 2) else 0) else 0) n]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.range n).filter (fun t => t ∈ r.toFinset) = r.toFinset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hr t h, h⟩⟩
  rw [hfilt, Finset.sum_boole, hcard]

/-- **桥二**：`dotS` 报假当且仅当读出的向量与支持向量正交。

`hr` 要求支持列表的下标落在码长内（编码器的产物满足），`hrn` 要求无重复。 -/
theorem dotS_eq_false_iff_dotProduct (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    dotS σ r = false ↔ (rowOf n r) ⬝ᵥ (vecOf σ n) = 0 := by
  rw [dotS_eq_false_iff_even, ← natCast_zmod2_eq_zero_iff_even,
    ← sum_indicator_eq_cntS σ hr hrn, dotProduct_rowOf_vecOf]

/-! ## `ZMod 2` 的两点算术 -/

/-- `ZMod 2` 上非零即一。 -/
theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hv : x.val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero x).mp h0)
  have hlt : x.val < 2 := ZMod.val_lt x
  have h1 : x.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val x, h1]
  norm_num

/-- `ZMod 2` 的元素就是它自己的一比特指示。 -/
theorem zmod2_indicator (x : ZMod 2) : (if decide (x = 1) then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · have h0 : x = 0 := by
      by_contra hne
      exact h (zmod2_eq_one_of_ne_zero hne)
    rw [h0]
    simp

/-! ## 由"核向量 + 配对见证"造出满足赋值 -/

/-- 把前 `n` 位的核向量与后 `n` 位的配对见证拼成一个赋值。

第二位起用 `t < 2n` 划界，越界处取假——`Assign` 是 `ℕ → Bool`，必须是全函数。 -/
def certAssign (n : ℕ) (E w : Vec n) : Assign := fun t =>
  if h : t < n then decide (E ⟨t, h⟩ = 1)
  else if h2 : t < 2 * n then decide (w ⟨t - n, by omega⟩ = 1)
  else false

theorem certAssign_lt {n : ℕ} (E w : Vec n) {t : ℕ} (ht : t < n) :
    certAssign n E w t = decide (E ⟨t, ht⟩ = 1) := by
  unfold certAssign
  rw [dite_eq_left ht]

theorem certAssign_mid {n : ℕ} (E w : Vec n) {t : ℕ} (h1 : ¬ t < n) (h2 : t < 2 * n) :
    certAssign n E w t = decide (w ⟨t - n, by omega⟩ = 1) := by
  unfold certAssign
  rw [dite_eq_right h1, dite_eq_left h2]

/-- 赋值的前 `n` 位读回核向量本身。 -/
theorem vecOf_certAssign {n : ℕ} (E w : Vec n) : vecOf (certAssign n E w) n = E := by
  funext i
  rw [vecOf, certAssign_lt E w i.isLt]
  exact zmod2_indicator (E i)

/-- 赋值的后 `n` 位读回配对见证。 -/
theorem vecOf_certAssign_shift {n : ℕ} (E w : Vec n) :
    vecOf (fun t => certAssign n E w (n + t)) n = w := by
  funext i
  have h1 : ¬ n + i.val < n := by omega
  have h2 : n + i.val < 2 * n := by omega
  have hfin : (⟨n + i.val - n, by omega⟩ : Fin n) = i :=
    Fin.ext (by change n + i.val - n = i.val; omega)
  rw [vecOf, certAssign_mid E w h1 h2, hfin]
  exact zmod2_indicator (w i)

/-- 逐位与的读法：`vecOf` 把 `&&` 送到 `ZMod 2` 的乘法。 -/
theorem vecOf_and {n : ℕ} (a b : Assign) :
    vecOf (fun t => a t && b t) n = fun i => vecOf a n i * vecOf b n i := by
  funext i
  unfold vecOf
  by_cases ha : a i.val = true <;> by_cases hb : b i.val = true <;> simp [ha, hb]

/-- 全 1 支持列表读出的就是全 1 向量。 -/
theorem rowOf_range (n : ℕ) : rowOf n (List.range n) = fun _ : Fin n => 1 := by
  funext i
  rw [rowOf, ite_eq_left (List.mem_range.mpr i.isLt)]
/-! ## 一般形态：回放判决 ⟹ 码级下界

四档实例共用的骨架。把编码器侧的输入（`Rker`/`Rpair` 支持列表、`n`、`k`）、码层对象
（`M₁`/`M₂`）以及两者之间的行对应与三条组合事实都收成前提，结论就是码级命题。 -/

/-- `List.all` 形式的界转成逐条形式。`∀ r ∈ L, …` 不是内核能直接判定的量词形态，
故编码器侧的三条事实先以 `all` 写出、再经此转成定理前提。 -/
theorem all_of_mem_bounds {n : ℕ} {L : List (List Nat)}
    (h : (L.all fun r => r.all fun t => decide (t < n)) = true) :
    ∀ r ∈ L, ∀ t ∈ r, t < n := by
  intro r hr t ht
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h r hr) t ht)

/-- 同上，转成"支持列表无重复"。 -/
theorem all_of_mem_nodup {L : List (List Nat)}
    (h : (L.all fun r => decide r.Nodup) = true) : ∀ r ∈ L, r.Nodup :=
  fun r hr => of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- 同上，转成"支持列表非空"。 -/
theorem all_of_mem_ne_nil {L : List (List Nat)}
    (h : (L.all fun r => decide (r ≠ [])) = true) : ∀ r ∈ L, r ≠ [] :=
  fun r hr => of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- **证书即下界（一般形态）**：若编码器在 `(Rker, Rpair, n, k)` 上产出的公式不可满足，
则对应的码不存在重量 $\le k$ 的逻辑算符。

这是本模块存在的理由：`_unsat` 那几条定理在此之前是**关于 CNF 的**孤立命题，
本定理与四档实例把它们接成**关于码的**命题。 -/
theorem no_light_logical_of_unsat {n k : ℕ} {Rker Rpair : List (List Nat)}
    {m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {F : CNF}
    (hF : buildPair Rker Rpair n k = F) (hunsat : ¬ Satisfiable F) (hn : 0 < n)
    (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hb₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hb₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hd₁ : ∀ r ∈ Rker, r.Nodup) (hd₂ : ∀ r ∈ Rpair, r.Nodup)
    (hrow₁ : Rker.map (rowOf n) = List.ofFn fun i => M₁ i)
    (hrow₂ : Rpair.map (rowOf n) = List.ofFn fun i => M₂ i) :
    ¬ ∃ E : Vec n, (support E).card ≤ k ∧ E ∈ (Matrix.toLin' M₁).ker
      ∧ E ∉ M₂.rowSpace := by
  rintro ⟨E, hw, hker, hrow⟩
  -- 一、分离引理取出配对见证
  have hspan : E ∉ spanL (List.ofFn fun i => M₂ i) := by
    rw [← Matrix.rowSpace_eq_spanL_ofFn]
    exact hrow
  obtain ⟨w, hwmv, hwdot⟩ := exists_ker_dot_ne_zero_of_not_mem M₂ hspan
  have hwdot1 : E ⬝ᵥ w = 1 := zmod2_eq_one_of_ne_zero hwdot
  -- 二、两侧逐行正交
  have hrowE : ∀ i, (M₁ i) ⬝ᵥ E = 0 := (mem_ker_iff_dotProd_rows_eq_zero M₁ E).mp hker
  have hmemker : w ∈ (Matrix.toLin' M₂).ker := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact hwmv
  have hroww : ∀ i, (M₂ i) ⬝ᵥ w = 0 := (mem_ker_iff_dotProd_rows_eq_zero M₂ w).mp hmemker
  -- 三、重量
  have hwt : cntS (certAssign n E w) (List.range n) ≤ k := by
    rw [← support_vecOf_card (certAssign n E w) n, vecOf_certAssign E w]
    exact hw
  -- 四、核侧
  have hkerS : ∀ r ∈ Rker, dotS (certAssign n E w) r = false := by
    intro r hr
    rw [dotS_eq_false_iff_dotProduct (certAssign n E w) (hb₁ r hr) (hd₁ r hr),
      vecOf_certAssign E w]
    have hmem : rowOf n r ∈ List.ofFn (fun i => M₁ i) := by
      rw [← hrow₁]
      exact List.mem_map_of_mem hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
    rw [← hi]
    exact hrowE i
  -- 五、配对侧
  have hpairS : ∀ r ∈ Rpair, dotS (fun t => certAssign n E w (n + t)) r = false := by
    intro r hr
    rw [dotS_eq_false_iff_dotProduct (fun t => certAssign n E w (n + t))
      (hb₂ r hr) (hd₂ r hr), vecOf_certAssign_shift E w]
    have hmem : rowOf n r ∈ List.ofFn (fun i => M₂ i) := by
      rw [← hrow₂]
      exact List.mem_map_of_mem hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
    rw [← hi]
    exact hroww i
  -- 六、配对为 1
  have hxwS : dotS (fun t => certAssign n E w t && certAssign n E w (n + t))
      (List.range n) = true := by
    have hne : dotS (fun t => certAssign n E w t && certAssign n E w (n + t))
        (List.range n) ≠ false := by
      intro hf
      have h0 := (dotS_eq_false_iff_dotProduct _
        (fun t ht => List.mem_range.mp ht) List.nodup_range).mp hf
      rw [rowOf_range, vecOf_and, vecOf_certAssign E w, vecOf_certAssign_shift E w,
        dotProduct] at h0
      simp only [one_mul] at h0
      rw [← dotProduct, hwdot1] at h0
      exact one_ne_zero h0
    cases h : dotS (fun t => certAssign n E w t && certAssign n E w (n + t))
        (List.range n) <;> simp_all
  -- 七、与不可满足判决矛盾
  obtain ⟨τ, hτ⟩ := buildPair_complete (Rker := Rker) (Rpair := Rpair) (n := n) (k := k)
    (σ := certAssign n E w) hn hne₁ hne₂ hb₁ hb₂ hwt hkerS hpairS hxwS
  exact hunsat ⟨τ, by rwa [hF] at hτ⟩

/-! ## 四档实例

三档（rep7 / Steane / BB18）的码层对象就是库里已有的校验矩阵；环面那一档的
**量子比特编号与 `Codes/CaseMatrix.lean` 的 `toric3Hz`/`toric3Hx` 不同**
（见 `hgp_toric3Ker_rows_ne_toric3Hx`，由 `decide` 判否确认），故它用编码器自己的行表
定义码层对象——它是**编码器所编码的那个码**的距离陈述，不是对 `toric3_dx` 的复算。 -/

/-- 重复码 $[7,1,7]$：核里没有重量 $\le 6$ 的非零向量。 -/
theorem rep7_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 7, (support E).card ≤ 6 ∧ E ∈ (Matrix.toLin' rep7H).ker
      ∧ E ∉ (zeroRows 7).rowSpace :=
  no_light_logical_of_unsat rep7H (zeroRows 7) rep7_eq rep7_unsat (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

/-- Steane $[[7,1,3]]$：没有重量 $\le 2$ 的逻辑算符。 -/
theorem steane_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 7, (support E).card ≤ 2 ∧ E ∈ (Matrix.toLin' steaneHz).ker
      ∧ E ∉ steaneHx.rowSpace :=
  no_light_logical_of_unsat steaneHz steaneHx steane_eq steane_unsat (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

/-- 环面 $[[18,2,3]]$ 的核侧，编码器的量子比特编号（`hgp_toric3Ker` 的每一行读成码向量）。 -/
def toric3CertKer : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of fun i => rowOf 18 (hgp_toric3Ker.get i)

/-- 环面 $[[18,2,3]]$ 的配对侧，编码器的量子比特编号。 -/
def toric3CertPair : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of fun i => rowOf 18 (hgp_toric3Pair.get i)

/-- 编码器侧的环面行表与库里的 `toric3Hx` **不是**逐行相同的：两侧量子比特编号不同。
（这是一条机器判定的事实，不是脚注；它划定了下面那条定理的证据边界。） -/
theorem hgp_toric3Ker_rows_ne_toric3Hx :
    hgp_toric3Ker.map (rowOf 18) ≠ List.ofFn (fun i => toric3Hx i) := by decide

/-- 环面 $[[18,2,3]]$（编码器编号）：没有重量 $\le 2$ 的逻辑算符。 -/
theorem hgp_toric3_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 18, (support E).card ≤ 2 ∧ E ∈ (Matrix.toLin' toric3CertKer).ker
      ∧ E ∉ toric3CertPair.rowSpace :=
  no_light_logical_of_unsat toric3CertKer toric3CertPair hgp_toric3_eq hgp_toric3_unsat
    (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

/-- 双变量自行车 $[[18,4,4]]$：没有重量 $\le 3$ 的逻辑算符。

终点与 `Codes/BB18Anchor.lean` 由重量限定枚举得到的 `bb18_dx = 4` 是同一个数，
故两条独立路线（证书回放 与 枚举）在内核内对上，而第一条不含任何枚举。 -/
theorem bb18_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 18, (support E).card ≤ 3 ∧ E ∈ (Matrix.toLin' bb18Hx).ker
      ∧ E ∉ bb18Hz.rowSpace :=
  no_light_logical_of_unsat bb18Hx bb18Hz bb18_lb3_eq bb18_lb3_unsat (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

end QECCertificates.LRAT
