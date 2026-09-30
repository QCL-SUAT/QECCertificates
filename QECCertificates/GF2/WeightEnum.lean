/-
Copyright (c) 2026 The QECCertificates Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QECCertificates Authors
-/

import QECCertificates.GF2.Basic

/-!
# 按重量限定的向量枚举：把搜索空间从 $2^n$ 压到 $\sum_{k\le w}\binom nk$
（ 规模化 + 证书复杂度）

用全空间枚举（`Finset.univ : Finset (Vec n)`）做下界证书：覆盖性由
`Finset.mem_univ` 免费提供，代价却是 $2^n$。
实测 $n \le 9$ 秒级、$n = 15$ 超过三分钟，方法卡在 $n \approx 12$。

本模块换一条路：**只枚举重量 $\le w$ 的向量**。下界只需检查"重量 $< d$"的算符，
取 $w = d - 1$ 即可——于是

* 候选空间从 $2^n$ 掉到 $\sum_{k \le w}\binom nk$（定 $d$ 时是 $n$ 的 $d-1$ 次多项式）；
* $n = 15$、$d = 3$：$2^{15} = 32768 \to \binom{15}{\le 2} = 121$（**270 倍**）。

代价是**枚举覆盖性不再是免费的**——本模块的主要定理
`mem_lightVecs` 就是这条覆盖性引理，`length_lightVecs` 给出**精确计数**，
合起来即"距离判定证书的归约规模恰为 $\sum_{k<d}\binom nk$"这条复杂度刻画。

## 构造

枚举与重量用**同一个递归**定义，于是覆盖性可以顺着结构归纳证出来：

```
wtRec : 末位为零不计、非零计 1，前缀递归
lightVecs (n+1) (w+1) = (lightVecs n (w+1)).map (末位补 0)
                      ++ (lightVecs n w).map (末位补 1)
```

`lightVecs` **不重不漏**：长度恰为 $\sum_{k\le w}\binom nk$。

## 主结果

* `mem_lightVecs`：**覆盖性**——重量 $\le w$ 的向量必在枚举里。
* `wtRec_eq_hammingNorm`：`wtRec` 与标准 `hammingNorm` 一致（对外接口的桥）。
* `length_lightVecs`：**精确计数**——枚举长度 $= \sum_{k \le w}\binom nk$。
-/

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## 末位补坐标 -/

/-- "末位补坐标"：前 `n` 位取 `u`、第 `n+1` 位取 `b`。

**刻意写成显式 `if` 分支而不是 `Fin.snoc`**：与 `Fin.append` 同族的理由——
`if` 分支在内核归约下逐坐标畅通，`by decide` 能算。 -/
def snocV {n : ℕ} (u : Vec n) (b : ZMod 2) : Vec (n + 1) :=
  fun i => if h : (i : ℕ) < n then u ⟨i, h⟩ else b

@[simp] lemma snocV_castSucc {u : Vec n} {b : ZMod 2} (i : Fin n) :
    snocV u b i.castSucc = u i := by
  simp only [snocV]
  rw [dite_eq_left (show ((i.castSucc : Fin (n + 1)) : ℕ) < n from i.isLt)]
  exact congrArg u (Fin.ext rfl)

@[simp] lemma castSuccEmb_apply (i : Fin n) : Fin.castSuccEmb i = i.castSucc := rfl

@[simp] lemma snocV_last {u : Vec n} {b : ZMod 2} : snocV u b (Fin.last n) = b := by
  simp only [snocV]
  rw [dite_eq_right (show ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n from by simp)]

/-- 零向量的"末位补零"仍是零向量。 -/
@[simp] lemma snocV_zero_zero : snocV (0 : Vec n) (0 : ZMod 2) = 0 := by
  funext i
  by_cases h : (i : ℕ) < n
  · rw [snocV, dite_eq_left h]; rfl
  · rw [snocV, dite_eq_right h]; rfl

/-- 任何 `n+1` 位向量都由"前缀 + 末位"重建。 -/
lemma snocV_prefix_last (v : Vec (n + 1)) :
    snocV (fun i : Fin n => v i.castSucc) (v (Fin.last n)) = v := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
  · rw [hj, snocV_castSucc]
  · rw [hj, snocV_last]

/-! ## 递归重量与枚举 -/

/-- **递归重量**：与 `lightVecs` 同构的定义，让覆盖性证明能顺着结构归纳。

末位非零计 1、末位为零不计，前缀递归——与 `hammingNorm` 一致（`wtRec_eq_hammingNorm`）。 -/
def wtRec : (n : ℕ) → Vec n → ℕ
  | 0, _ => 0
  | n + 1, v => wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1)

@[simp] lemma wtRec_zero (v : Vec 0) : wtRec 0 v = 0 := by rw [wtRec.eq_1]

lemma wtRec_succ (v : Vec (n + 1)) :
    wtRec (n + 1) v
      = wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1) := by
  rw [wtRec.eq_2]

/-- **重量 $\le w$ 的向量全体**（可计算枚举，不重不漏）。

递归：$n+1$ 位的向量按末位分两类——末位为零的由 $n$ 位上重量 $\le w+1$ 的补零得到，
末位为 1 的由 $n$ 位上重量 $\le w$ 的补 1 得到。 -/
def lightVecs : (n w : ℕ) → List (Vec n)
  | 0, _ => [0]
  | _ + 1, 0 => [0]
  | n + 1, w + 1 =>
      (lightVecs n (w + 1)).map (fun u => snocV u 0) ++ (lightVecs n w).map (fun u => snocV u 1)

@[simp] lemma lightVecs_nil (w : ℕ) : lightVecs 0 w = [0] := by rw [lightVecs.eq_1]

lemma lightVecs_zero (n : ℕ) : lightVecs n 0 = [0] := by
  cases n with
  | zero => rw [lightVecs.eq_1]
  | succ n => rw [lightVecs.eq_2]

lemma lightVecs_succ_succ (n w : ℕ) :
    lightVecs (n + 1) (w + 1) = (lightVecs n (w + 1)).map (fun u => snocV u 0)
      ++ (lightVecs n w).map (fun u => snocV u 1) := by
  rw [lightVecs.eq_3]

/-! ## 重量为零即零向量 -/

theorem wtRec_eq_zero_iff (v : Vec n) : wtRec n v = 0 ↔ v = 0 := by
  induction n with
  | zero =>
      refine ⟨fun _ => ?_, fun _ => by simp⟩
      funext i
      exact i.elim0
  | succ n ih =>
      rw [wtRec_succ]
      constructor
      · intro h
        have hb : v (Fin.last n) = 0 := by
          by_contra hb
          rw [ite_eq_right hb] at h
          omega
        rw [ite_eq_left hb, add_zero] at h
        have hpre : (fun i : Fin n => v i.castSucc) = 0 := (ih _).mp h
        rw [← snocV_prefix_last v, hb, hpre, snocV_zero_zero]
      · intro h
        rw [h]
        simp only [Pi.zero_apply, ite_true, add_zero]
        exact (ih 0).mpr rfl

/-! ## 覆盖性 -/

/-- **覆盖性**：重量 $\le w$ 的向量必在 `lightVecs n w` 里。

证明顺着 `lightVecs` 的递归结构归纳：看末位。末位非零时前缀重量必须 $\le w$，
末位为零时前缀重量只需 $\le w+1$——两种情形各自落进对应的那一半枚举。 -/
theorem mem_lightVecs : ∀ (n w : ℕ) (v : Vec n), wtRec n v ≤ w → v ∈ lightVecs n w := by
  intro n
  induction n with
  | zero =>
      intro w v _
      rw [lightVecs_nil]
      simp only [List.mem_singleton]
      funext i
      exact i.elim0
  | succ n ih =>
      intro w v hv
      cases w with
      | zero =>
          have hv0 : v = 0 := (wtRec_eq_zero_iff v).mp (Nat.le_zero.mp hv)
          rw [hv0, lightVecs_zero]; simp
      | succ w =>
          rw [← snocV_prefix_last v, lightVecs_succ_succ]
          rw [wtRec_succ] at hv
          by_cases hb : v (Fin.last n) = 0
          · rw [hb] at hv ⊢
            rw [ite_eq_left rfl] at hv
            refine List.mem_append_left _ ?_
            rw [List.mem_map]
            exact ⟨fun i : Fin n => v i.castSucc, ih (w + 1) _ hv, rfl⟩
          · rw [ite_eq_right hb] at hv
            have hb1 : v (Fin.last n) = 1 := eq_one_of_ne_zero hb
            rw [hb1]
            refine List.mem_append_right _ ?_
            rw [List.mem_map]
            exact ⟨fun i : Fin n => v i.castSucc, ih w _ (by omega), rfl⟩

/-! ## 与标准重量的桥 -/

/-- **可靠性**：`lightVecs` 里只有重量 $\le w$ 的向量——覆盖性 `mem_lightVecs` 的另一半。

有了这一条，"候选集为空"才在两个方向上都闭：覆盖性说漏掉的都会被抓，
可靠性说留下的都确实轻。 -/
theorem wt_le_of_mem_lightVecs : ∀ (n w : ℕ) (v : Vec n), v ∈ lightVecs n w → wtRec n v ≤ w := by
  intro n
  induction n with
  | zero =>
      intro w v hv
      rw [lightVecs_nil, List.mem_singleton] at hv
      subst hv
      have h0 : wtRec 0 (0 : Vec 0) = 0 := wtRec_zero 0
      rw [h0]
      omega
  | succ n ih =>
      intro w v hv
      cases w with
      | zero =>
          rw [lightVecs_zero, List.mem_singleton] at hv
          subst hv
          have h0 : wtRec (n + 1) (0 : Vec (n + 1)) = 0 :=
            (wtRec_eq_zero_iff (0 : Vec (n + 1))).mpr rfl
          rw [h0]
      | succ w =>
          rw [lightVecs_succ_succ, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [List.mem_map] at hv
            obtain ⟨u, hu, huv⟩ := hv
            subst huv
            have h := ih (w + 1) u hu
            have heq : wtRec (n + 1) (snocV u 0) = wtRec n u := by
              rw [wtRec_succ, snocV_last]
              simp
            rw [heq]
            omega
          · rw [List.mem_map] at hv
            obtain ⟨u, hu, huv⟩ := hv
            subst huv
            have h := ih w u hu
            have heq : wtRec (n + 1) (snocV u 1) = wtRec n u + 1 := by
              rw [wtRec_succ, snocV_last]
              simp
            rw [heq]
            omega


/-- `wtRec` 就是支撑集大小（与 `support`/`hammingNorm` 一致）。 -/
theorem wtRec_eq_card_support (v : Vec n) : wtRec n v = (support v).card := by
  induction n with
  | zero => simp [wtRec, support]
  | succ n ih =>
      rw [wtRec_succ, ih]
      have hsupp : support v =
          (support (fun i : Fin n => v i.castSucc)).map Fin.castSuccEmb
            ∪ (if v (Fin.last n) = 0 then ∅ else {Fin.last n}) := by
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
        · rw [hj, mem_support]
          by_cases hb : v (Fin.last n) = 0 <;>
            simp [support, castSuccEmb_apply, hb, Fin.castSucc_inj, Fin.castSucc_ne_last]
        · rw [hj, mem_support]
          by_cases hb : v (Fin.last n) = 0 <;>
            simp [support, castSuccEmb_apply, hb, Fin.castSucc_ne_last]
      rw [hsupp, Finset.card_union_of_disjoint, Finset.card_map]
      · by_cases hb : v (Fin.last n) = 0 <;> simp [hb]
      · rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_map] at ha
        obtain ⟨j, _, hj⟩ := ha
        rw [← hj] at hb
        by_cases h0 : v (Fin.last n) = 0
        · simp [h0] at hb
        · simp only [h0, ite_false, Finset.mem_singleton] at hb
          exact Fin.castSucc_ne_last j hb

/-- `wtRec` 与标准 `hammingNorm` 一致（对外接口的桥）。 -/
theorem wtRec_eq_hammingNorm (v : Vec n) : wtRec n v = hammingNorm v := by
  rw [wtRec_eq_card_support, weight_eq_hammingNorm]

/-! ## 精确计数（证书复杂度） -/

/-- **枚举长度的精确计数**：`lightVecs n w` 恰有 $\sum_{k \le w}\binom nk$ 个元素。

这就是"距离判定证书复杂度"的可见内容：由于下界只需检查
重量 $< d$ 的算符，取 $w = d-1$ 后**候选空间恰为 $\sum_{k<d}\binom nk$**——
定 $d$ 时是 $n$ 的 $d-1$ 次多项式，而不是全空间的 $2^n$。 -/
theorem length_lightVecs : ∀ (n w : ℕ),
    (lightVecs n w).length = ∑ k ∈ Finset.range (w + 1), n.choose k := by
  intro n
  induction n with
  | zero =>
      intro w
      rw [lightVecs_nil]
      rw [Finset.sum_eq_single 0]
      · exact Nat.choose_self 0
      · intro b _ hb
        exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos w)) h
  | succ n ih =>
      intro w
      cases w with
      | zero =>
          rw [lightVecs_zero, Finset.sum_range_one, Nat.choose_zero_right]
          rfl
      | succ w =>
          rw [lightVecs_succ_succ, List.length_append, List.length_map, List.length_map,
            ih (w + 1), ih w]
          rw [Finset.sum_range_succ' (fun j => (n + 1).choose j) (w + 1)]
          rw [Finset.sum_congr rfl (fun j _ => Nat.choose_succ_succ n j), Finset.sum_add_distrib]
          rw [Finset.sum_range_succ' (fun j => n.choose j) (w + 1)]
          rw [Finset.sum_range_succ (fun j => n.choose j) w]
          rw [Nat.choose_zero_right n, Nat.choose_zero_right (n + 1)]
          ring

end QECCertificates
