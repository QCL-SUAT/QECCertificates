/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

import QECCertificates.GF2.LowerBound

/-!
# The size of the distance certificate: an explicit polynomial bound and its sharpness

`GF2/LowerBound` lands the two visible properties of the distance-decision certificate:
**coverage** (every vector of weight $\le d-1$ lies in the candidate set, so "absent from
the candidates" means "does not exist at all") and **count** (the candidate set has length
at most $\sum_{k<d}\binom nk$). This module carries the count to the form the development's
targets require:

* **an explicit polynomial upper bound** (`lightCand_length_le_poly`):
  $\#\{\text{candidates}\}\le d\cdot n^{\,d-1}$. For fixed $d$ this is a polynomial of
  degree $d-1$ in $n$, not the $2^n$ of the full space. Every step of the bound uses only
  $\binom nk\le n^k$, independently of any solver.
* **sharpness** (`lightCand_zero_rows_length`, `lightCand_length_bound_sharp`): for an
  unstructured code (both check matrices have no rows) the undetectable predicate
  degenerates to "nonzero weight", the candidate set is exactly the weight-bounded
  enumeration with the zero vector removed, and its length is exactly
  $\sum_{k<d}\binom nk-1$. Hence **any** bound $B$ holding uniformly over all check
  matrices must satisfy $\sum_{k<d}\binom nk-1\le B$: the binomial bound of `GF2/LowerBound`
  and the true maximum differ by a single zero vector, and the bound cannot be lowered
  (`no_uniform_bound_le_sum_sub_two`).

## The three technical lemmas supplied for sharpness

* `nodup_lightVecs`: the weight-bounded enumeration has no repeats. The two halves of the
  recursion end in a last coordinate of 0 and of 1 respectively, hence are disjoint;
  "exactly one fewer" rests on this lemma.
* `inKerB_zero_rows`: with no check rows the kernel test is vacuously true (the universal
  quantifier over `Fin 0` is empty).
* `inSpanB_nil_iff`: `inSpanB` of the empty row list is equivalent to "the vector is zero"
  (`rowReduce [] = []` and `reduceAgainst [] v = v`).

Ported from the certificate-code-parameters development, where this module is
`QuantumCodeCertificates.GF2.CertSize`; the proofs are unchanged and only the namespace
differs.
-/

open QECCertificates

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## The enumeration has no repeats -/

/-- "Append a last coordinate" is injective once the last coordinate is fixed: the prefix
is determined by the whole. -/
lemma snocV_inj {u u' : Vec n} {b : ZMod 2} (h : snocV u b = snocV u' b) : u = u' := by
  funext i
  have h2 := congrFun h i.castSucc
  simpa using h2

/-- **The weight-bounded enumeration has no repeats**: `lightVecs n w` has no duplicate
element.

The induction is on `n` (the statement is written `∀ w, …`, because the two halves of the
recursion use different `w`). The recursive step uses `List.nodup_append`: each half is a
`List.map`, with injectivity from `snocV_inj`; disjointness is read off the last coordinate,
which is constantly 0 in one half and constantly 1 in the other. -/
theorem nodup_lightVecs (n : ℕ) : ∀ w : ℕ, (lightVecs n w).Nodup := by
  induction n with
  | zero => intro w; rw [lightVecs_nil]; simp
  | succ n ih =>
      intro w
      cases w with
      | zero => rw [lightVecs_zero]; simp
      | succ w =>
          rw [lightVecs_succ_succ, List.nodup_append]
          refine ⟨?_, ?_, ?_⟩
          · exact (ih (w + 1)).map (fun _ _ h => snocV_inj h)
          · exact (ih w).map (fun _ _ h => snocV_inj h)
          · intro a ha b hb
            obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
            obtain ⟨u', _, rfl⟩ := List.mem_map.mp hb
            intro hab
            have hlast := congrFun hab (Fin.last n)
            rw [snocV_last, snocV_last] at hlast
            exact absurd hlast (zero_ne_one : (0 : ZMod 2) ≠ 1)

/-- The zero vector always lies in the weight-bounded enumeration: its weight is 0, which
qualifies it for every `w`. -/
lemma zero_mem_lightVecs (n w : ℕ) : (0 : Vec n) ∈ lightVecs n w := by
  refine mem_lightVecs n w 0 ?_
  have h : wtRec n (0 : Vec n) = 0 := (wtRec_eq_zero_iff 0).mpr rfl
  omega

/-! ## Two degenerations on the empty check matrix -/

/-- With no check rows the kernel test is vacuously true: the universal quantifier over
`Fin 0` is empty. -/
@[simp] lemma inKerB_zero_rows (v : Vec n) :
    inKerB (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) v = true := by
  simp [inKerB]

/-- `inSpanB` of the empty row list is equivalent to "the vector is zero".
(`rowReduce [] = []` and `reduceAgainst [] v = v` are both definitional equations.) -/
lemma inSpanB_nil_iff (v : Vec n) : inSpanB [] v = true ↔ v = 0 := by
  unfold inSpanB
  rw [decide_eq_true_iff]
  simp [rowReduce]

/-- The false form: `inSpanB` of the empty row list is `false` iff the vector is nonzero. -/
lemma inSpanB_nil_eq_false_iff (v : Vec n) : inSpanB [] v = false ↔ v ≠ 0 := by
  constructor
  · intro h hv
    rw [(inSpanB_nil_iff v).mpr hv] at h
    exact absurd h (by decide)
  · intro hv
    cases h : inSpanB [] v with
    | false => rfl
    | true => exact absurd ((inSpanB_nil_iff v).mp h) hv

/-- Positive weight iff the vector is nonzero. -/
lemma hammingNorm_pos_iff {v : Vec n} : 0 < hammingNorm v ↔ v ≠ 0 := by
  rw [Nat.pos_iff_ne_zero]
  exact not_congr hammingNorm_eq_zero

/-! ## The candidate set on an unstructured code -/

/-- **On an unstructured code the undetectable predicate degenerates to "nonzero weight"**.

When both check matrices have no rows: the kernel test is vacuously true
(`inKerB_zero_rows`), the row-space test degenerates to "the vector is zero"
(`inSpanB_nil_eq_false_iff`), and of the three conjuncts only "nonzero" survives. -/
lemma isLightUndetectable_zero_rows_iff (v : Vec n) :
    IsLightUndetectable (0 : Matrix (Fin 0) (Fin n) (ZMod 2))
      (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) v ↔ v ≠ 0 := by
  change (0 < hammingNorm v
      ∧ inKerB (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) v = true
      ∧ inSpanB (List.ofFn fun i : Fin 0 =>
          (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) i) v = false) ↔ v ≠ 0
  rw [hammingNorm_pos_iff]
  constructor
  · rintro ⟨-, -, h⟩
    rw [List.ofFn_zero] at h
    exact (inSpanB_nil_eq_false_iff v).mp h
  · intro hv
    refine ⟨hv, inKerB_zero_rows v, ?_⟩
    rw [List.ofFn_zero]
    exact (inSpanB_nil_eq_false_iff v).mpr hv

/-- The candidate set of an unstructured code is the weight-bounded enumeration with the
zero vector removed. -/
lemma lightCand_zero_rows_eq_filter (d : ℕ) :
    lightCand (0 : Matrix (Fin 0) (Fin n) (ZMod 2))
        (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) d
      = (lightVecs n (d - 1)).filter (fun v => decide (v ≠ 0)) := by
  unfold lightCand
  refine List.filter_congr (fun v _ => ?_)
  rw [decide_eq_decide]
  exact isLightUndetectable_zero_rows_iff v

/-! ## Sharpness: the unstructured code attains the binomial count exactly -/

/-- **Sharpness (attainment)**: the unstructured code pins the candidate-set length to
exactly $\sum_{k<d}\binom nk-1$.

The accounting is stepwise: no repeats (`nodup_lightVecs`) make the length equal the
cardinality of its `Finset`; the "nonzero" filter is the removal of the zero vector from
the `Finset` (`Finset.filter_ne'`); removing an element drops the cardinality by one
(`Finset.card_erase_of_mem`, the zero vector always lying in the enumeration,
`zero_mem_lightVecs`); and the exact count (`length_lightVecs`) closes it.

Together with `lightCand_length_le` this says the binomial bound and the true maximum
differ by a single zero vector. -/
theorem lightCand_zero_rows_length {d : ℕ} (hd : 1 ≤ d) :
    (lightCand (0 : Matrix (Fin 0) (Fin n) (ZMod 2))
        (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) d).length
      = (∑ k ∈ Finset.range d, n.choose k) - 1 := by
  rw [lightCand_zero_rows_eq_filter]
  have hnodup : (lightVecs n (d - 1)).Nodup := nodup_lightVecs n (d - 1)
  have h0 : (0 : Vec n) ∈ lightVecs n (d - 1) := zero_mem_lightVecs n (d - 1)
  have hA : ((lightVecs n (d - 1)).filter (fun v => decide (v ≠ 0))).toFinset
      = (lightVecs n (d - 1)).toFinset.erase (0 : Vec n) := by
    rw [List.toFinset_filter]
    have hEq : ({x ∈ (lightVecs n (d - 1)).toFinset | decide (x ≠ 0) = true}
          : Finset (Vec n))
        = {x ∈ (lightVecs n (d - 1)).toFinset | x ≠ 0} := by
      refine Finset.filter_congr (fun x _ => ?_)
      exact decide_eq_true_iff
    rw [hEq, Finset.filter_ne']
  calc ((lightVecs n (d - 1)).filter (fun v => decide (v ≠ 0))).length
      = (((lightVecs n (d - 1)).filter (fun v => decide (v ≠ 0))).toFinset.card) :=
        (List.toFinset_card_of_nodup (hnodup.filter _)).symm
    _ = ((lightVecs n (d - 1)).toFinset.erase (0 : Vec n)).card := by rw [hA]
    _ = (lightVecs n (d - 1)).toFinset.card - 1 :=
        Finset.card_erase_of_mem (List.mem_toFinset.mpr h0)
    _ = (lightVecs n (d - 1)).length - 1 := by
        rw [List.toFinset_card_of_nodup hnodup]
    _ = (∑ k ∈ Finset.range d, n.choose k) - 1 := by
        rw [length_lightVecs, show d - 1 + 1 = d from by omega]

/-- The `Finset` form of sharpness (the `lightSet` side). -/
theorem lightSet_zero_rows_card {d : ℕ} (hd : 1 ≤ d) :
    (lightSet (0 : Matrix (Fin 0) (Fin n) (ZMod 2))
        (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) d).card
      = (∑ k ∈ Finset.range d, n.choose k) - 1 := by
  have hnd : (lightCand (0 : Matrix (Fin 0) (Fin n) (ZMod 2))
        (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) d).Nodup := by
    rw [lightCand_zero_rows_eq_filter]
    exact (nodup_lightVecs n (d - 1)).filter _
  rw [lightSet, List.toFinset_card_of_nodup hnd, lightCand_zero_rows_length hd]

/-- **The quantitative form of sharpness**: any bound `B` holding uniformly over all check
matrices cannot be below $\sum_{k<d}\binom nk-1$. -/
theorem lightCand_length_bound_sharp {d : ℕ} (hd : 1 ≤ d) {B : ℕ}
    (hB : ∀ (m₁ m₂ : ℕ) (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
      (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)), (lightCand M₁ M₂ d).length ≤ B) :
    (∑ k ∈ Finset.range d, n.choose k) - 1 ≤ B :=
  (le_of_eq (lightCand_zero_rows_length (n := n) hd).symm).trans
    (hB 0 0 (0 : Matrix (Fin 0) (Fin n) (ZMod 2))
      (0 : Matrix (Fin 0) (Fin n) (ZMod 2)))

/-- **The bound cannot be lowered**: no uniform bound `B` is strictly below
$\sum_{k<d}\binom nk-1$. -/
theorem no_uniform_bound_lt_sum_sub_one {d : ℕ} (hd : 1 ≤ d) {B : ℕ}
    (hB : ∀ (m₁ m₂ : ℕ) (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
      (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)), (lightCand M₁ M₂ d).length ≤ B) :
    ¬ (B < (∑ k ∈ Finset.range d, n.choose k) - 1) :=
  not_lt_of_ge (lightCand_length_bound_sharp (n := n) hd hB)

/-- The binomial count is at least 2 (for $n\ge1$, $d\ge2$).
This is the condition under which the `- 2` form below is non-degenerate: the truncated
subtraction of `Nat` turns "$\le\sum-2$" into a vacuously true proposition when the count
is $<2$ (for instance at $d=1$ the count is 1 and $\sum-2=0$, while "candidate length
$\le0$" does hold for every instance). -/
lemma two_le_sum_choose {d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) :
    2 ≤ ∑ k ∈ Finset.range d, n.choose k := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range d := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
  have hle : (∑ k ∈ ({0, 1} : Finset ℕ), n.choose k)
      ≤ ∑ k ∈ Finset.range d, n.choose k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), Nat.choose_zero_right,
    Nat.choose_one_right] at hle
  omega

/-- **No uniform bound of the form $\bigl(\sum_{k<d}\binom nk\bigr)-2$ exists**: lowering
the binomial bound of `lightCand_length_le` by more than one misses the single instance of
the unstructured code.

The non-degeneracy hypothesis `2 ≤ ∑_{k<d}\binom nk` is supplied by `two_le_sum_choose` for
$n\ge1$, $d\ge2$; without it the proposition is false (see the note on `two_le_sum_choose`).
This is not a technical assumption: being two below the count is what requires the count to
be at least 2. -/
theorem no_uniform_bound_le_sum_sub_two {d : ℕ}
    (hsum : 2 ≤ ∑ k ∈ Finset.range d, n.choose k) :
    ¬ ∃ B : ℕ, B ≤ (∑ k ∈ Finset.range d, n.choose k) - 2 ∧
      (∀ (m₁ m₂ : ℕ) (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
        (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)), (lightCand M₁ M₂ d).length ≤ B) := by
  have hd : 1 ≤ d := by
    by_contra h
    have h0 : d = 0 := by omega
    rw [h0, Finset.range_zero, Finset.sum_empty] at hsum
    omega
  rintro ⟨B, hBle, hB⟩
  have hsharp := lightCand_length_bound_sharp (n := n) hd hB
  omega

/-- The subtraction-free form of the same statement (unconditional for every `d ≥ 1`):
no uniform bound `B` satisfies `B + 2 ≤ ∑_{k<d}\binom nk`.
When the count is $\ge2$ it is equivalent to `no_uniform_bound_le_sum_sub_two`, and when
the count is $<2$ the proposition is vacuously true; this is the cleanest rendering of "two
below". -/
theorem no_uniform_bound_two_below_sum {d : ℕ} (hd : 1 ≤ d) :
    ¬ ∃ B : ℕ, B + 2 ≤ ∑ k ∈ Finset.range d, n.choose k ∧
      (∀ (m₁ m₂ : ℕ) (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
        (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)), (lightCand M₁ M₂ d).length ≤ B) := by
  rintro ⟨B, hBtwo, hB⟩
  have hsharp := lightCand_length_bound_sharp (n := n) hd hB
  omega

/-- **Certificate complexity: the upper bound and sharpness (conjunction form)**.

The first half is `lightCand_length_le`; the second says the bound cannot be lowered
further, the unstructured code attaining it minus one exactly. Together they are the
solver-free explicit upper bound and its sharpness the development calls for. -/
theorem certificate_size_sum_sharp {d : ℕ} (hd : 1 ≤ d) :
    (∀ (m₁ m₂ : ℕ) (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
      (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)),
        (lightCand M₁ M₂ d).length ≤ ∑ k ∈ Finset.range d, n.choose k) ∧
    (∃ (m₁ m₂ : ℕ) (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
      (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)),
        (lightCand M₁ M₂ d).length = (∑ k ∈ Finset.range d, n.choose k) - 1) :=
  ⟨fun _ _ M₁ M₂ => lightCand_length_le M₁ M₂ hd,
   ⟨0, 0, 0, 0, lightCand_zero_rows_length hd⟩⟩

/-! ## The polynomial-form upper bound -/

/-- **The polynomial upper bound on the candidate size**:
`(lightCand M₁ M₂ d).length ≤ d · n^(d-1)`.

Enlarge the binomial bound of `lightCand_length_le` term by term: `n.choose k ≤ n^k`
(`Nat.choose_le_pow`), and `k ≤ d-1` together with `n ≥ 1` gives `n^k ≤ n^(d-1)`
(`Nat.pow_le_pow_right`); the whole sum is then covered by `d` copies of the single term
`n^(d-1)`.

**The degree is visible**: for fixed `d` this is a polynomial of degree $d-1$ in $n$, an
exponential factor below $2^n$; and the exponent $d-1$ cannot be dropped, since
`lightCand_length_bound_sharp` shows the binomial version is already sharp to within a
single zero vector. -/
theorem lightCand_length_le_poly {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (lightCand M₁ M₂ d).length ≤ d * n ^ (d - 1) := by
  refine (lightCand_length_le M₁ M₂ hd).trans ?_
  calc ∑ k ∈ Finset.range d, n.choose k
      ≤ ∑ _k ∈ Finset.range d, n ^ (d - 1) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k ≤ d - 1 := by
          have := Finset.mem_range.mp hk
          omega
        exact (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn hk')
    _ = d * n ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_range]
        simp

end QECCertificates
