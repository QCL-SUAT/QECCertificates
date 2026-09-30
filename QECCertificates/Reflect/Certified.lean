/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Reflect.Faithful
import QECCertificates.Reflect.Complete
import QECCertificates.Codes.BB18Anchor
import QECCertificates.GF2.HGPCleaning

/-!
# The certificate is the lower bound: replaying the kernel check into a code-distance theorem

`Reflect/LRATData.lean` moves the output of this package's pipeline (an external encoder together
with the LRAT proof of a SAT solver) into the kernel, and `Reflect/LRAT.lean` turns it into
`¬ Satisfiable <CNF>`; `Reflect/Encode.lean` and `Reflect/Complete.lean` then prove that this CNF
is satisfiable **if and only if** its four semantic conditions hold. Each of the three pieces holds
on its own, but until this module they had never been connected: the only consumers of the `_unsat`
theorems were the audit lines of the root file, which made them exhibits rather than load-bearing
results.

This module supplies exactly that last connection. Among the four semantic conditions,

* `∀ r ∈ Rker, dotS σ r = false` says that the code vector read from the first `n` bits of `σ`
  lies in the kernel,
* `∀ r ∈ Rpair, dotS (fun t => σ (n+t)) r = false` says that the pairing vector lies in the
  kernel,
* `dotS (fun t => σ t && σ (n+t)) (range n) = true` says that the two pair to 1,
* `cntS σ (range n) ≤ k` says that the weight is at most `k`,

so "no satisfying assignment exists" and "this code has no logical operator of weight `≤ k`" are
the same statement. Bridging the two readings (the indicator reading on `Assign` and `Vec n`), the
certificate replay **gives a distance lower bound directly**: for BB $[[18,4,4]]$ it yields
`4 ≤ d`, the same number that `bb18_dx` of `Codes/BB18Anchor.lean` obtains by enumeration, from
**two independent routes**. This is the executable meaning of "the certificate is the unit of
verification".

**Boundary**: this module bridges only the BB18 case; the other three (rep7, Steane and the toric
$[[18,2,3]]$) have the same shape.
-/

namespace QECCertificates.LRAT

/-! ## The two readings: assignments and code vectors -/

/-- The first `n` bits of an assignment read as a code vector: 1 where `σ` is true and 0 otherwise. -/
def vecOf (σ : Assign) (n : ℕ) : Vec n := fun i => if σ i.val then 1 else 0

/-- A support list read as a code vector: 1 at the positions listed in `r` and 0 otherwise. -/
def rowOf (n : ℕ) (r : List Nat) : Vec n := fun i => if i.val ∈ r then 1 else 0

/-- Nonzeroness for `vecOf`: entry `i` is nonzero if and only if `σ` is true there. -/
theorem vecOf_apply_ne_zero {σ : Assign} {n : ℕ} {i : Fin n} :
    vecOf σ n i ≠ 0 ↔ σ i.val = true := by
  unfold vecOf
  cases h : σ i.val <;> simp_all

/-! ## Bridge 1: the support size is exactly the count -/

/-- The support size of `vecOf` is exactly the count of the assignment: the two readings give the same
weight. -/
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

/-! ## Bridge 2: XOR dot products over a support list and `dotProduct` -/

/-- The recursion for `cntS` (in this version the predicate of `List.filter` is `Bool`). -/
theorem cntS_cons (σ : Assign) (j : Nat) (s : List Nat) :
    cntS σ (j :: s) = (if σ j then 1 else 0) + cntS σ s := by
  unfold cntS
  cases h : σ j <;> simp [h, Nat.add_comm]

/-- Adding one flips parity. -/
theorem even_one_add (m : ℕ) : Even (1 + m) ↔ ¬ Even m := by
  rw [Nat.add_comm 1 m, Nat.even_add_one]

/-- `dotS` is parity: the XOR dot product is false if and only if the number of true entries is even.

This step does not need the support list to have no duplicates, since the XOR and the count each
take multiplicities into account. -/
theorem dotS_eq_false_iff_even (σ : Assign) (r : List Nat) :
    dotS σ r = false ↔ Even (cntS σ r) := by
  induction r with
  | nil => simp
  | cons j s ih =>
    rw [dotS_cons, cntS_cons]
    cases h : σ j <;> cases hb : dotS σ s <;> simp_all [even_one_add]

/-- A natural number `c : ℕ` has image zero in `ZMod 2` if and only if `c` is even. -/
theorem natCast_zmod2_eq_zero_iff_even (c : ℕ) : ((c : ZMod 2) = 0) ↔ Even c := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.even_iff]

/-- Expansion of the product: the entrywise product of `rowOf` and `vecOf` is an indicator function. -/
theorem dotProduct_rowOf_vecOf (σ : Assign) (n : ℕ) (r : List Nat) :
    (rowOf n r) ⬝ᵥ (vecOf σ n)
      = ∑ i : Fin n, (if (i : ℕ) ∈ r then (if σ i.val then (1 : ZMod 2) else 0) else 0) := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [rowOf, vecOf]
    by_cases h : (i : ℕ) ∈ r <;> simp [h]

/-- The sum of indicators is the count: summing the indicator function over a support list equals the
count of the assignment.

This is where `hrn` (no duplicates) is used: `dotS` counts multiplicities, while `Finset` does
not. -/
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

/-- **Bridge 2**: `dotS` reports false if and only if the vector read out is orthogonal to the support
vector.

`hr` requires the indices of the support list to lie within the code length (the encoder's output
satisfies this) and `hrn` requires no duplicates. -/
theorem dotS_eq_false_iff_dotProduct (σ : Assign) {n : ℕ} {r : List Nat}
    (hr : ∀ t ∈ r, t < n) (hrn : r.Nodup) :
    dotS σ r = false ↔ (rowOf n r) ⬝ᵥ (vecOf σ n) = 0 := by
  rw [dotS_eq_false_iff_even, ← natCast_zmod2_eq_zero_iff_even,
    ← sum_indicator_eq_cntS σ hr hrn, dotProduct_rowOf_vecOf]

/-! ## Two facts about arithmetic in `ZMod 2` -/

/-- In `ZMod 2` everything nonzero is one. -/
theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hv : x.val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero x).mp h0)
  have hlt : x.val < 2 := ZMod.val_lt x
  have h1 : x.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val x, h1]
  norm_num

/-- An element of `ZMod 2` is its own one-bit indicator. -/
theorem zmod2_indicator (x : ZMod 2) : (if decide (x = 1) then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · have h0 : x = 0 := by
      by_contra hne
      exact h (zmod2_eq_one_of_ne_zero hne)
    rw [h0]
    simp

/-! ## Building a satisfying assignment from a kernel vector and a pairing witness -/

/-- Concatenate a kernel vector in the first `n` bits and a pairing witness in the next `n` bits into
one assignment.

From the second block on the bound `t < 2n` is used, and positions beyond it are false, since
`Assign` is `ℕ → Bool` and must be a total function. -/
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

/-- The first `n` bits of the assignment read back as the kernel vector itself. -/
theorem vecOf_certAssign {n : ℕ} (E w : Vec n) : vecOf (certAssign n E w) n = E := by
  funext i
  rw [vecOf, certAssign_lt E w i.isLt]
  exact zmod2_indicator (E i)

/-- The next `n` bits of the assignment read back as the pairing witness. -/
theorem vecOf_certAssign_shift {n : ℕ} (E w : Vec n) :
    vecOf (fun t => certAssign n E w (n + t)) n = w := by
  funext i
  have h1 : ¬ n + i.val < n := by omega
  have h2 : n + i.val < 2 * n := by omega
  have hfin : (⟨n + i.val - n, by omega⟩ : Fin n) = i :=
    Fin.ext (by change n + i.val - n = i.val; omega)
  rw [vecOf, certAssign_mid E w h1 h2, hfin]
  exact zmod2_indicator (w i)

/-- The reading of bitwise conjunction: `vecOf` sends `&&` to multiplication in `ZMod 2`. -/
theorem vecOf_and {n : ℕ} (a b : Assign) :
    vecOf (fun t => a t && b t) n = fun i => vecOf a n i * vecOf b n i := by
  funext i
  unfold vecOf
  by_cases ha : a i.val = true <;> by_cases hb : b i.val = true <;> simp [ha, hb]

/-- The all-ones support list reads out as the all-ones vector. -/
theorem rowOf_range (n : ℕ) : rowOf n (List.range n) = fun _ : Fin n => 1 := by
  funext i
  rw [rowOf, ite_eq_left (List.mem_range.mpr i.isLt)]
/-! ## General form: a replay verdict implies a code-level lower bound

The skeleton shared by the four instances. The encoder-side input (the `Rker`/`Rpair` support
lists, `n`, `k`), the code-level objects (`M₁`/`M₂`), the row correspondence between them and three
assembly facts are all taken as hypotheses, and the conclusion is a code-level proposition. -/

/-- Turn a bound in `List.all` form into a pointwise form. The quantifier shape `∀ r ∈ L, …` is not one
the kernel can decide directly, so the three encoder-side facts are first written with `all` and
then converted into theorem hypotheses here. -/
theorem all_of_mem_bounds {n : ℕ} {L : List (List Nat)}
    (h : (L.all fun r => r.all fun t => decide (t < n)) = true) :
    ∀ r ∈ L, ∀ t ∈ r, t < n := by
  intro r hr t ht
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h r hr) t ht)

/-- As above, converting to "the support lists have no duplicates". -/
theorem all_of_mem_nodup {L : List (List Nat)}
    (h : (L.all fun r => decide r.Nodup) = true) : ∀ r ∈ L, r.Nodup :=
  fun r hr => of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- As above, converting to "the support lists are nonempty". -/
theorem all_of_mem_ne_nil {L : List (List Nat)}
    (h : (L.all fun r => decide (r ≠ [])) = true) : ∀ r ∈ L, r ≠ [] :=
  fun r hr => of_decide_eq_true (List.all_eq_true.mp h r hr)

/-- **The certificate is the lower bound (general form)**: if the formula produced by the encoder at
`(Rker, Rpair, n, k)` is unsatisfiable, then the corresponding code has no logical operator of
weight $\le k$.

This is why the module exists: before this theorem and the four instances, the `_unsat` theorems
were isolated statements **about the CNF**, and together they become statements **about the
code**. -/
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

/-! ## The four instances

For three of them (rep7, Steane and BB18) the code-level objects are parity-check matrices that
already exist in this library; the toric case has a **different qubit numbering from
`toric3Hz`/`toric3Hx` of `Codes/CaseMatrix.lean`** (see `hgp_toric3Ker_rows_ne_toric3Hx`,
confirmed by `decide` returning false), so it defines the code-level objects from the encoder's own
row list. It is a distance statement about **the code the encoder encodes**, not a recomputation of
`toric3_dx`. -/

/-- The repetition code $[7,1,7]$: the kernel contains no nonzero vector of weight $\le 6$. -/
theorem rep7_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 7, (support E).card ≤ 6 ∧ E ∈ (Matrix.toLin' rep7H).ker
      ∧ E ∉ (zeroRows 7).rowSpace :=
  no_light_logical_of_unsat rep7H (zeroRows 7) rep7_eq rep7_unsat (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

/-- Steane $[[7,1,3]]$: no logical operator of weight $\le 2$. -/
theorem steane_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 7, (support E).card ≤ 2 ∧ E ∈ (Matrix.toLin' steaneHz).ker
      ∧ E ∉ steaneHx.rowSpace :=
  no_light_logical_of_unsat steaneHz steaneHx steane_eq steane_unsat (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

/-- The kernel side of the toric $[[18,2,3]]$ in the encoder's qubit numbering (each row of
`hgp_toric3Ker` read as a code vector). -/
def toric3CertKer : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of fun i => rowOf 18 (hgp_toric3Ker.get i)

/-- The pairing side of the toric $[[18,2,3]]$ in the encoder's qubit numbering. -/
def toric3CertPair : Matrix (Fin 9) (Fin 18) (ZMod 2) :=
  Matrix.of fun i => rowOf 18 (hgp_toric3Pair.get i)

/-- The encoder-side toric row list and `toric3Hx` of this library are **not** the same row by row:
the two sides use different qubit numberings. (This is a machine-decided fact rather than a
footnote; it delimits the evidence available for the theorem below.) -/
theorem hgp_toric3Ker_rows_ne_toric3Hx :
    hgp_toric3Ker.map (rowOf 18) ≠ List.ofFn (fun i => toric3Hx i) := by decide

/-- The toric $[[18,2,3]]$ in the encoder's numbering: no logical operator of weight $\le 2$. -/
theorem hgp_toric3_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 18, (support E).card ≤ 2 ∧ E ∈ (Matrix.toLin' toric3CertKer).ker
      ∧ E ∉ toric3CertPair.rowSpace :=
  no_light_logical_of_unsat toric3CertKer toric3CertPair hgp_toric3_eq hgp_toric3_unsat
    (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

/-- The bivariate bicycle code $[[18,4,4]]$: no logical operator of weight $\le 3$.

The endpoint is the same number as `bb18_dx = 4`, obtained in `Codes/BB18Anchor.lean` by a
weight-bounded enumeration, so the two independent routes (certificate replay and enumeration)
agree inside the kernel, while the first contains no enumeration at all. -/
theorem bb18_no_light_logical_of_certificate :
    ¬ ∃ E : Vec 18, (support E).card ≤ 3 ∧ E ∈ (Matrix.toLin' bb18Hx).ker
      ∧ E ∉ bb18Hz.rowSpace :=
  no_light_logical_of_unsat bb18Hx bb18Hz bb18_lb3_eq bb18_lb3_unsat (by decide)
    (all_of_mem_ne_nil (by decide)) (all_of_mem_ne_nil (by decide))
    (all_of_mem_bounds (by decide)) (all_of_mem_bounds (by decide))
    (all_of_mem_nodup (by decide)) (all_of_mem_nodup (by decide))
    (by decide) (by decide)

end QECCertificates.LRAT
