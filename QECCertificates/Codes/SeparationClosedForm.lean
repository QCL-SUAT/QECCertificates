/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/
import QECCertificates.Codes.MeasurementProtocol

/-!
# 分离条件的闭式（C1 免判定：完全图族的膨胀定理）

本包的卖点定在**闭式**：判定定理 `separation_judgment` 目前是
"**假设** C1–C2 成立 ⟹ 两分量都 $\ge d$"，要成为科学结论必须在具体码族上把假设
**验证掉**。该节同时点明了成本落在哪一句：

> 估计 3–6 周，取决于是否能在环面族上把 C1 的辅助图取成标准图从而**免判定**。

本模块把这一句做掉。**取辅助图为完全图 $K_m$，则 C1 对一切 $m$ 成立且零枚举**——
于是 C1 从假设清单里消失，闭式只剩下空间界（W–Y Lemma 2，本侧不重证；本库对"引用的外部引理"口径一致：只搬运、不重证）与 C2（轮数 $\ge d$，取 $T=d$ 即满足）。

## 一、为什么是完全图

$K_m$ 的割大小有闭式：割过 $S$ 的边恰是"两端一个在 $S$、一个在 $S^{\mathsf c}$"的
无序对，故 $\mathrm{cut}(S)=|S|\cdot|S^{\mathsf c}|$。于是

$$\min\bigl(|S|,\ m-|S|\bigr)\ \le\ m-|S|\ =\ |S^{\mathsf c}|\ \le\ \mathrm{cut}(S),$$

中间那一步是本模块的计数引理 `cutSize_completeEdges_ge_compl`：
**任取 $a\in S$，从 $a$ 连向 $S^{\mathsf c}$ 的 $|S^{\mathsf c}|$ 条边两两不同、
且全都割过去**——不需要把割大小算精确，一条单点估计就够。
这一步是这一整个模块的实质：它把"对每个 $m$ 逐个判定膨胀"换成了"对一切 $m$ 一次证明"。

## 二、C1 的数值形态

判定定理里的 C1 是数值形态 $\eta\ge1$（`separation_judgment` 的 `hC1`），
而图上的 C1 是可计算谓词 `HasExpansionOne`。两者的桥是 `c1Witness`：
图有膨胀时取 $1$、否则取 $0$——于是 `one_le_c1Witness` 把
"图有膨胀"这一**可计算判定**接到判定定理的数值假设上，中间不留散文。

## 三、闭式

`separation_closed`：有膨胀的辅助图 $+$ 轮数 $\ge d$ $\Longrightarrow$ 两分量都 $\ge d$——
**C1 与 C2 都已是定理而不是假设**。`toric_family_separation_closed` 把它实例化到
环面族：$d=m$（`Codes/HGPToricFamily.lean` 的族级 $[[2m^2,2,m]]$）、
$T=m$（C2 由 `le_refl` 满足）、辅助图 $K_m$（C1 由 `expansionOne_complete_gen` 满足）。

## 四、还剩什么

空间分量的**精确值**与 W–Y Lemma 2 本身的机器检验仍缺——本模块只把它们从
"假设"里孤立出来，没有消掉。这是 §2.2 那条估计里剩余的部分。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 一、完全图的边表与割大小 -/

/-- **完全图 $K_m$ 的边表**：全体无序对 $\{a,b\}$，取 $a<b$ 的代表。

用 `List` 而非 `Finset` 是为了直接喂给 `HasExpansionOne`（它按边表定义割大小）。 -/
def completeEdges (m : ℕ) : List (Fin m × Fin m) :=
  (List.finRange m).flatMap (fun a =>
    ((List.finRange m).filter (fun b => decide (a < b))).map (fun b => (a, b)))

/-- **边表的成员刻画**：`(a,b)` 在完全图里 $\iff a<b$。 -/
theorem mem_completeEdges {m : ℕ} {p : Fin m × Fin m} :
    p ∈ completeEdges m ↔ p.1 < p.2 := by
  rw [completeEdges, List.mem_flatMap]
  constructor
  · rintro ⟨a, -, hb⟩
    rw [List.mem_map] at hb
    obtain ⟨b, hbf, rfl⟩ := hb
    exact of_decide_eq_true (List.mem_filter.mp hbf).2
  · intro h
    refine ⟨p.1, List.mem_finRange p.1, ?_⟩
    rw [List.mem_map]
    exact ⟨p.2, List.mem_filter.mpr ⟨List.mem_finRange p.2, decide_eq_true h⟩, rfl⟩

/-- **计数引理（本模块的实质）**：$S$ 非空时，从任一 $a\in S$ 连向 $S^{\mathsf c}$ 的
$|S^{\mathsf c}|$ 条边两两不同、且全都割过 $S$——故割大小 $\ge|S^{\mathsf c}|$。

只证**下界**而不算精确值：单点估计足够推出膨胀，且省掉一次双射计数。 -/
theorem cutSize_completeEdges_ge_compl {m : ℕ} {S : Finset (Fin m)} (hne : S.Nonempty) :
    Sᶜ.card ≤ cutSize (completeEdges m) S := by
  obtain ⟨a, ha⟩ := hne
  -- 每条边取 $a<b$ 的代表，使 `f` 单射
  let f : Fin m → Fin m × Fin m := fun b => if a < b then (a, b) else (b, a)
  have hf_inj : Function.Injective f := by
    intro b₁ b₂ h
    have h1 : (f b₁).1 = (f b₂).1 := congrArg Prod.fst h
    have h2 : (f b₁).2 = (f b₂).2 := congrArg Prod.snd h
    by_cases c₁ : a < b₁ <;> by_cases c₂ : a < b₂ <;>
      simp only [f, c₁, c₂, ite_true, ite_false] at h1 h2
    · exact h2
    · exact h2.trans h1
    · exact h1.trans h2
    · exact h1
  have hcard : ((Sᶜ).image f).card = Sᶜ.card := Finset.card_image_of_injective _ hf_inj
  have hsub : (Sᶜ).image f ⊆
      (List.filter (fun e : Fin m × Fin m => decide (e.1 ∈ S) != decide (e.2 ∈ S))
        (completeEdges m)).toFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨b, hb, rfl⟩ := he
    have hbnot : b ∉ S := Finset.mem_compl.mp hb
    have hane : a ≠ b := fun h => hbnot (h ▸ ha)
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨mem_completeEdges.mpr ?_, ?_⟩
    · by_cases c : a < b
      · simp [f, c]
      · have hba : b < a := lt_of_le_of_ne (le_of_not_gt c) (Ne.symm hane)
        simpa [f, c] using hba
    · by_cases c : a < b <;> simp only [f, c, ite_true, ite_false] <;>
        rw [decide_eq_true ha, decide_eq_false hbnot] <;> rfl
  calc Sᶜ.card = ((Sᶜ).image f).card := hcard.symm
    _ ≤ (List.filter (fun e : Fin m × Fin m => decide (e.1 ∈ S) != decide (e.2 ∈ S))
          (completeEdges m)).toFinset.card := Finset.card_le_card hsub
    _ ≤ (List.filter (fun e : Fin m × Fin m => decide (e.1 ∈ S) != decide (e.2 ∈ S))
          (completeEdges m)).length := List.toFinset_card_le _
    _ = cutSize (completeEdges m) S := rfl

/-- **C1 免判定（完全图族）**：对**一切** $m$，$K_m$ 的膨胀 $\ge1$。

证明只有两步：$S$ 空时平凡；$S$ 非空时取 $a\in S$，由 `cutSize_completeEdges_ge_compl`
得 $\mathrm{cut}\ge|S^{\mathsf c}|=m-|S|\ge\min(|S|,m-|S|)$。

这正是要落实的那一句——**把辅助图取成标准图，从而免判定**：
判定定理的假设清单里 C1 从此可以在整个族上一次性消掉，而不是逐 $m$ 判定。 -/
theorem expansionOne_complete_gen (m : ℕ) : HasExpansionOne (completeEdges m) := by
  intro S
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [cutSize]
  · have hle : m - S.card ≤ cutSize (completeEdges m) S := by
      have h := cutSize_completeEdges_ge_compl (m := m) hne
      rwa [Finset.card_compl, Fintype.card_fin] at h
    exact le_trans (min_le_right _ _) hle

/-! ## 二、C1 的数值形态与判定定理的接线 -/

/-- **C1 的数值形态**：图有膨胀时取 $\eta=1$、否则取 $0$。

判定定理 `separation_judgment` 的 C1 是数值假设 $1\le\eta$，而图上的 C1 是
可计算谓词 `HasExpansionOne`——本定义是两者之间**唯一的**桥，于是没有散文缺口。 -/
def c1Witness {k : ℕ} (edges : List (Fin k × Fin k)) : ℕ :=
  if HasExpansionOne edges then 1 else 0

/-- **桥**：图有膨胀 $\Longrightarrow$ 数值形态满足 $1\le\eta$（故 $\min(\eta,1)=1$）。 -/
theorem one_le_c1Witness {k : ℕ} {edges : List (Fin k × Fin k)}
    (h : HasExpansionOne edges) : 1 ≤ c1Witness edges := by
  unfold c1Witness
  rw [ite_eq_left h]

/-- **分离闭式**：辅助图有膨胀（C1）且轮数 $\ge d$（C2）$\Longrightarrow$ 两分量都 $\ge d$。

与 `separation_judgment` 的差别是：那一条的 C1 与 C2 是**假设**，本条的 C1 由
辅助图的膨胀**判定**给出、C2 由轮数给出——故本条的假设清单里只剩空间界的数值形态
$hSpace$（W–Y Lemma 2，本侧不重证）与时间分量的上界 $hTime$（本库 `timeLike_weight_eq`）。 -/
theorem separation_closed {k : ℕ} {edges : List (Fin k × Fin k)} {d T spaceDist timeDist : ℕ}
    (hexp : HasExpansionOne edges) (hC2 : d ≤ T)
    (hSpace : min (c1Witness edges) 1 * d ≤ spaceDist) (hTime : T ≤ timeDist) :
    d ≤ min spaceDist timeDist :=
  separation_judgment (one_le_c1Witness hexp) hC2 hSpace hTime

/-! ## 三、环面族上的闭式 -/

/-- **环面族的分离闭式**：对任意 $m$，HGP($m$-圈,$m$-圈) 的 $d=m$
（`Codes/HGPToricFamily.lean` 的族级 $[[2m^2,2,m]]$，零枚举），
辅助图取 $K_m$、轮数取 $T=m$，则两分量都 $\ge m$：

* C1：`expansionOne_complete_gen m`——**对一切 $m$ 已证**；
* C2：`le_refl m`——轮数取到距离本身就满足。

于是"假设 C1–C2"在这条族上消失了。 -/
theorem toric_family_separation_closed {m : ℕ} {spaceDist timeDist : ℕ}
    (hSpace : min (c1Witness (completeEdges m)) 1 * m ≤ spaceDist) (hTime : m ≤ timeDist) :
    m ≤ min spaceDist timeDist :=
  separation_closed (expansionOne_complete_gen m) (le_refl m) hSpace hTime

/-- **小实例对拍**：$m=4$ 时 `completeEdges 4` 的数值形态确为 $1$——
与 `Codes/Separation.lean` 的字面量版本 `expansionOne_complete`（$K_4$）一致。 -/
theorem c1Witness_completeEdges_four : c1Witness (completeEdges 4) = 1 := by decide

/-- **割大小闭式的对拍**：$m=4$ 上逐子集核出 $\mathrm{cut}(S)=|S|\,(m-|S|)$——
本模块正文只证了 $\ge|S^{\mathsf c}|$ 的一侧，这条说明那条下界在 $m=4$ 上是**紧的**
（不是把割大小估小后换来的弱结论）。 -/
theorem cutSize_completeEdges_exact_four :
    ∀ S : Finset (Fin 4), cutSize (completeEdges 4) S = S.card * (4 - S.card) := by
  decide

/-- **两条路的对拍**：字面量边表与 `completeEdges` 在 $m=4$ 上给出同一个膨胀判定
（前者是 `Codes/Separation.lean` 的既有实例，后者是本模块的族形态）。 -/
theorem completeEdges_four_agrees :
    HasExpansionOne ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4))
      ∧ HasExpansionOne (completeEdges 4) :=
  ⟨expansionOne_complete, expansionOne_complete_gen 4⟩

/-! ## 四、与测量协议层的接线 -/

/-- **时间轴分量在族上取到 $d$**：测一个逻辑算符 `v`、逐比特横向测量时，
单轮没有轮内校验（`bare_noLightFault`：单轮距离 $=1$），故 $T$ 轮协议的时空故障
距离恰为 $T$（`le_spacetimeWeight` $+$ `spacetimeWeight_witness`）。
环面族取重量 $m$ 的逻辑与 $T=m$，即时间轴分量 $=m=d$——**对任意 $v$ 成立**，
不依赖逻辑的支撑结构。 -/
theorem family_time_component {v : Vec n} {T : ℕ} {f : SpacetimeFault T n}
    (hker : ∀ t, inKerB (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) (f t) = true)
    (hlog : ∀ t, v ⬝ᵥ f t = 1) : T ≤ spacetimeWeight f := by
  simpa using le_spacetimeWeight (bare_noLightFault v) hker hlog

end QECCertificates
