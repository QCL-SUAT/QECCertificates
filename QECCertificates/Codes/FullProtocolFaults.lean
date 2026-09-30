/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BaconShorMeasurement

/-!
# The fault model of the full protocol: data, ancilla and measurement errors (Bacon–Shor instance)

The model in `Codes/MeasurementProtocol.lean` contains only **measurement errors**, that is,
flipped reported outcomes. For **transversal measurement** (measuring a logical operator bit by
bit, with the readout being the product) that is enough: data errors and measurement errors are
indistinguishable in the outcome. But once a check is measured through an **ancilla**, the two
kinds separate, and **the price of the separation is a halved distance**. That is exactly the
circuit-level hook error.

This module widens the model to three kinds and computes the numbers on Bacon–Shor:

| fault | symbol | what it flips |
|---|---|---|
| **data error** | `d` | **persists across rounds**: it flips the checks containing it, and the readout of every round |
| **measurement error** | `μ` | **affects its own round only**: it flips that round's checks and readout |
| **ancilla error** | `g` | **flips that round's check outcomes only**, leaving the data alone |

Over $T$ rounds: the cumulative data error is $f_t=\sum_{s\le t}d_s$; the syndrome is
$\sigma_t=H(f_t+\mu_t)+g_t$; the detectors are $D_0=\sigma_0$ (the **boundary**: the initial
state lies in the code space) and $D_t=\sigma_t+\sigma_{t-1}$; the readout of round $t$ is
$w\cdot(f_t+\mu_t)$; the logical fault occurs $\iff$ the readout is flipped in a **majority of
rounds**.

## The three results computed inside the kernel (each corroborated by an independent Python implementation of the same route)

1. **Single-round distance $=2=\lceil d/2\rceil$** (`bsHook_T1_distance_eq_two`): one data error
   $d=e_q$ ($q$ in the logical support) together with one ancilla error $g=Hd$. The two cancel
   in the syndrome, yet the data error remains. **With measurement errors alone the distance is
   $3=d$** (`bsSingleRound_noLightFault`, see `Codes/BaconShorMeasurement.lean`): **the ancilla
   error is that half distance.**
2. **Recovery from two rounds on** (`bsHook_T2_no_light` / `bsHook_T3_no_light`): with the
   boundary check added, faults of weight $\le2$ no longer exist over $T\ge2$ rounds, because a
   data error persists across rounds and shows up in the second round. **The mechanism itself
   holds for any number of rounds** (`bsDetectorsOK_syndrome_eq_zero`): the boundary detector
   first pins down the first round's syndrome, and the comparison of consecutive rounds then
   propagates it to zero round by round, so persistence has nowhere to hide from the second
   round on. The two `decide` results above are readings of this mechanism at $T=2,3$.
3. **The boundary check cannot be dropped** (`noBoundary_light_of_any_rounds`, **for any number
   of rounds**): once $D_0$ is removed, a data error that occurs only in round $0$ stays on the
   data from round $0$ on, every round then has exactly the same syndrome, the comparison of
   consecutive rounds sees no difference, and every round's readout is flipped. The weight is
   exactly $1$. This turns the **C3** criterion (the first round's stabilizer measurement is
   perfect) into a number, and it is a **theorem for all $T\ge1$**, not an enumeration over $T$;
   `bsHook_noBoundary_weight_one` is its reading at $T=1$.

4. **The two halves of C3 are not two separate things** (`c3_both_ends_agree`): the C3 criterion
   reads "both the first and the last round are taken to be perfect", while the third item above
   turns only the **first-round** half into a detector. Section 6 adds the **last-round** half and
   proves that the two are mutually derivable: the first round plus the comparison of consecutive
   rounds implies that every syndrome is zero (`bsDetectorsOK_closed_of_firstEnd`), and
   **conversely** the last round plus the same comparison also pins every syndrome to zero
   (`bsDetectorsOK_firstEnd_syndrome_eq_zero`, by backward induction). Adding the last-round half
   **does not change the candidate set** (`hookCandClosed_eq`), so the two halves give the same
   distance. What is genuinely indispensable is that **at least one end** be perfect: with neither
   end, item 3 has already driven the distance down to $1$.

**Convention**: the model is still **phenomenological** (each fault location flips an outcome or
propagates into one) and is not a gate-by-gate circuit-level simulation; the **propagation** of
an ancilla error into the data, which is the other half of a hook error, appears here as the
pattern "an ancilla error paired with a data error". Expanding the gate-level locations one by
one is the next step.

**Both ends of C3 are modelled** (Section 6): the statement "both the first and the last round are
taken to be perfect" is, in this module, two propositions that are **mutually derivable**, rather
than one modelled and one left blank.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. Representation layer: the three fault kinds and the detectors -/

/-!
The number of fault locations per round is $20$: $9$ data qubits ($0..8$), $9$ measurement
locations ($9..17$) and $2$ check ancillas ($18,19$). A fault pattern is written
`Vec (T * 20)`, and **its Hamming weight is the number of faults**.
-/

/-- The data error of round `t` (it persists across rounds). -/
def dataErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 20 + i.val, by have := i.isLt; have := t.isLt; omega⟩

/-- The measurement error of round `t` (it affects that round only). -/
def measErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 20 + 9 + i.val, by have := i.isLt; have := t.isLt; omega⟩

/-- The ancilla error of round `t` (it flips that round's check outcomes only). -/
def ancErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 2 :=
  fun c => f ⟨t.val * 20 + 18 + c.val, by have := c.isLt; have := t.isLt; omega⟩

/-- The **cumulative data error** up to round `t` (data errors persist across rounds, which is exactly where the time axis comes from). -/
def cumErr {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 9 :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val ≤ t.val), dataErr f s

/-- The syndrome of round `t`: data and measurement errors are both visible in the outcomes, while an ancilla error only alters a check. -/
def bsSyndrome {T : ℕ} (f : Vec (T * 20)) (t : Fin T) : Vec 2 :=
  bsStabChecks *ᵥ (cumErr f t + measErr f t) + ancErr f t

variable {T : ℕ}

/--
**The detectors**: the initial-state boundary $D_0=\sigma_0$ together with the comparison of
consecutive rounds $D_t=\sigma_t+\sigma_{t-1}$.

The boundary clause is physical: the code starts the protocol inside the code space (syndrome
zero), so a nonzero syndrome in the first round has already been noticed.
-/
abbrev bsDetectorsOK (f : Vec (T * 20)) : Prop :=
  (∀ t : Fin T, t.val = 0 → bsSyndrome f t = 0) ∧
    (∀ t u : Fin T, u.val = t.val + 1 → bsSyndrome f t = bsSyndrome f u)

/-- The detectors **without the boundary clause** (used to quantify the role of C3). -/
abbrev bsDetectorsOK_noBoundary (f : Vec (T * 20)) : Prop :=
  ∀ t u : Fin T, u.val = t.val + 1 → bsSyndrome f t = bsSyndrome f u

/--
**The recovery mechanism (for any $T$)**: the boundary detector together with the comparison
of consecutive rounds pins every syndrome to zero at once.

$D_0=\sigma_0$ settles the first round, and $D_t=\sigma_t+\sigma_{t-1}$ then propagates it round
by round, so persistence of a fault has nowhere to hide from the second round on. This is exactly
the mechanism behind recovery for $T\ge2$: a persistent data error is not caught by the checks of
**some single round**, but by the constraint that two consecutive rounds must agree.

This is a theorem for any number of rounds, not an enumeration over $T$: the four `decide` results
such as `bsHook_T2_no_light` above are readings of the mechanism at particular round counts.
-/
theorem bsDetectorsOK_syndrome_eq_zero {f : Vec (T * 20)}
    (h : bsDetectorsOK f) (t : Fin T) : bsSyndrome f t = 0 := by
  obtain ⟨hb, hs⟩ := h
  have key : ∀ k, ∀ t : Fin T, t.val = k → bsSyndrome f t = 0 := by
    intro k
    induction k with
    | zero => intro t ht; exact hb t ht
    | succ k ih =>
      intro t ht
      have hk : k < T := by have := t.isLt; omega
      have hstep : bsSyndrome f ⟨k, hk⟩ = bsSyndrome f t :=
        hs ⟨k, hk⟩ t (by omega)
      rw [← hstep]
      exact ih ⟨k, hk⟩ rfl
  exact key t.val t rfl

/-- The logical value read out in round `t` (the product of the three outcomes on the logical support). -/
def bsReadout (f : Vec (T * 20)) (t : Fin T) : ZMod 2 :=
  bstXW ⬝ᵥ (cumErr f t + measErr f t)

/-- **The logical fault**: the readout is flipped in a majority of rounds (which is what the $T$ repetitions are for). -/
abbrev bsLogicalFault (f : Vec (T * 20)) : Prop :=
  T < 2 * (Finset.univ.filter (fun t : Fin T => bsReadout f t = 1)).card

/--
**The candidates for an undetectable logical fault of weight $\le s$ under the full protocol**
(the same shape as `lightCand` in this library: an enumeration limited by weight, where **the fault
weight is the Hamming weight of the vector**).
-/
def hookCand (T s : ℕ) : List (Vec (T * 20)) :=
  (lightVecs (T * 20) s).filter
    (fun f => decide (bsDetectorsOK f ∧ bsLogicalFault f))

/-! ## 2. One round: the hook error, and the distance $2=\lceil d/2\rceil$ -/

/--
**The witness (a hook error)**: one data error (bit $0$ of the logical support, that is, the
vertex of column $0$) together with one ancilla error (the check $S_{01}$). The data error flips
the outcome of $S_{01}$ and the ancilla error flips it back, so the syndrome is zero, while the
data error stays on the data and flips the readout.

Numbering the 20 locations of a round, this is "location $0$ plus location $18$".
-/
def hookW1 : Vec (1 * 20) :=
  (e ⟨0, by omega⟩ : Vec (1 * 20)) + (e ⟨18, by omega⟩ : Vec (1 * 20))

/-- The three facts about the witness: all detectors are zero (the boundary included), the logical value is flipped, and the weight is exactly $2$. -/
theorem bsHook_T1_witness :
    bsDetectorsOK hookW1 ∧ bsLogicalFault hookW1 ∧ hammingNorm hookW1 = 2 :=
  ⟨by decide, by decide, by decide⟩

/-- **The single-round lower bound**: a fault of weight $\le1$ cannot be both undetectable and logic-flipping. -/
theorem bsHook_T1_no_light_one : hookCand 1 1 = [] := by decide

/--
**The single-round fault distance is $2$** (squeezed from both sides).

Compare the model with measurement errors alone, where the single-round distance is $3=d$
(`bsSingleRound_noLightFault`). **The ancilla error halves the distance**: that is the content of
the hook error, and it quantifies the overestimate one gets by computing the distance in the
measurement-error-only model.
-/
theorem bsHook_T1_distance_eq_two :
    (hookCand 1 1 = []) ∧
      (∃ f : Vec (1 * 20),
        bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 2) :=
  ⟨bsHook_T1_no_light_one, hookW1, bsHook_T1_witness.1, bsHook_T1_witness.2.1,
    bsHook_T1_witness.2.2⟩

/-! ## 3. Recovery from two rounds on: a data error persists across rounds and shows up in the second -/

/-- **$T=2$: faults of weight $\le2$ no longer exist**; the boundary check plus the second round catch the hook. -/
theorem bsHook_T2_no_light : hookCand 2 2 = [] := by decide

/-- **$T=3$: the same**. -/
theorem bsHook_T3_no_light : hookCand 3 2 = [] := by decide

-- **注意 `set_option ... in` 必须写在 docstring 之前**：写在 docstring 与 `theorem` 之间时，
-- docstring 会挂到 `set_option` 上，报 `unexpected token 'set_option'; expected 'lemma'`。
set_option maxHeartbeats 40000000 in
/--
**$T=4$: again there is no escape of weight $\le2$**.

The most expensive of the four $T$: the candidate set is a filter of `lightVecs 80 2`
($1+80+\binom{80}{2}=3241$ items), so the heartbeat budget is set per theorem (the module-level
8M is not enough; 40M passes, in about 5 minutes 40 seconds).
-/
theorem bsHook_T4_no_light : hookCand 4 2 = [] := by decide

/--
**The optimal escape pattern after recovery**: take a weight-3 logical operator of the code (a
single row that is all $X$, that is `bstZW` of `Codes/BaconShor.lean`) as a data error that
**persists from round $0$ on**. It meets every check in an even number of positions, so every
syndrome is zero and every round has the same readout, flipped.

This is the half that cannot be escaped: once the hook is caught in the second round, the cheapest
escape falls back to a **spacelike** logical error of weight $3=d$. The weight-3 escape found by
the independent implementation of the same route is exactly this one.
-/
def hookW3 (T : ℕ) : Vec ((T + 1) * 20) :=
  (e ⟨0, by omega⟩ : Vec ((T + 1) * 20)) + e ⟨1, by omega⟩ + e ⟨2, by omega⟩

/-- The three facts about this weight-3 witness in the two-round protocol. -/
theorem bsHook_twoRounds_witness :
    bsDetectorsOK (hookW3 1) ∧ bsLogicalFault (hookW3 1) ∧ hammingNorm (hookW3 1) = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- The same in the three-round protocol. -/
theorem bsHook_threeRounds_witness :
    bsDetectorsOK (hookW3 2) ∧ bsLogicalFault (hookW3 2) ∧ hammingNorm (hookW3 2) = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- The same in the four-round protocol (`hookW3 3 : Vec (4 * 20)`). -/
theorem bsHook_fourRounds_witness :
    bsDetectorsOK (hookW3 3) ∧ bsLogicalFault (hookW3 3) ∧ hammingNorm (hookW3 3) = 3 :=
  ⟨by decide, by decide, by decide⟩

/--
**The fault distance at $T=2$ is exactly $3=d$** (squeezed from both sides): no escape of
weight $\le2$ exists, and one of weight $3$ has an explicit witness. **The hook is caught and the
escape falls back to spacelike.**
-/
theorem bsHook_T2_distance_eq_three :
    (hookCand 2 2 = []) ∧
      (∃ f : Vec (2 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3) :=
  ⟨bsHook_T2_no_light, hookW3 1, bsHook_twoRounds_witness.1,
    bsHook_twoRounds_witness.2.1, bsHook_twoRounds_witness.2.2⟩

/-- **The fault distance at $T=3$ is likewise exactly $3=d$**. -/
theorem bsHook_T3_distance_eq_three :
    (hookCand 3 2 = []) ∧
      (∃ f : Vec (3 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3) :=
  ⟨bsHook_T3_no_light, hookW3 2, bsHook_threeRounds_witness.1,
    bsHook_threeRounds_witness.2.1, bsHook_threeRounds_witness.2.2⟩

/-- **The fault distance at $T=4$ is likewise exactly $3=d$**: the four-round reading is the fourth point of the full-protocol curve of Figure 2. -/
theorem bsHook_T4_distance_eq_three :
    (hookCand 4 2 = []) ∧
      (∃ f : Vec (4 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3) :=
  ⟨bsHook_T4_no_light, hookW3 3, bsHook_fourRounds_witness.1,
    bsHook_fourRounds_witness.2.1, bsHook_fourRounds_witness.2.2⟩

/-! ## 4. The boundary check cannot be dropped (quantifying the C3 criterion) -/

/--
**Once the boundary detector is dropped, a data error of weight $1$ is already undetectable**: it
shifts the syndromes of all rounds together, the comparison of consecutive rounds sees no
difference at all, and the readout is flipped, so the distance collapses to $1$.

This quantifies the **C3** criterion (the first round's stabilizer measurement is perfect): C3 is
not a technical convention, it is what supports the fact that the time axis has a reference from
the first round on.

**Note that at $T=1$ it is vacuous**: there are no consecutive rounds, so the conjunction
"consecutive rounds agree" holds trivially, and the statement only says that with no detector at
all a fault of weight 1 gets away. The substance is in `noBoundary_light_of_any_rounds`, which
holds for any number of rounds.
-/
theorem bsHook_noBoundary_weight_one :
    ∃ f : Vec (1 * 20),
      bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1 :=
  ⟨(e ⟨0, by omega⟩ : Vec (1 * 20)), by decide, by decide, by decide⟩

/-!
## 5. The boundary check cannot be dropped: the statement that holds for **any number of rounds**

The `bsHook_noBoundary_weight_one` of the previous section is the $T=1$ instance, and at $T=1$ the
conjunction "consecutive rounds agree" is empty, so it verifies nothing at all. The statement below
is the substance of "the boundary check cannot be dropped".
-/

/--
The witness used after dropping the boundary detector: **a single data error occurring only in
round 0** (location 0, that is, bit 0 of the logical support). Data errors accumulate in `cumErr`,
so it stays on the data from round 0 on, and every round therefore has exactly the same syndrome.
-/
def noBoundW (T : ℕ) (h : 0 < T) : Vec (T * 20) :=
  e ⟨0, by omega⟩

private lemma ne_zero_index {T : ℕ} {k : ℕ} (hk : k ≠ 0) (h : k < T * 20) :
    (⟨k, h⟩ : Fin (T * 20)) ≠ (⟨0, by omega⟩ : Fin (T * 20)) := by
  intro hcon
  exact hk (by have := congrArg Fin.val hcon; simp only at this; exact this)

private lemma noBoundW_dataErr_zero {T : ℕ} (h : 0 < T) {s : Fin T} (hs : s.val ≠ 0) :
    dataErr (noBoundW T h) s = 0 := by
  funext i
  simp only [dataErr, noBoundW, e]
  have hne := ne_zero_index (T := T) (k := s.val * 20 + i.val)
    (by omega) (by have := i.isLt; have := s.isLt; omega)
  rw [ite_eq_right hne]
  rfl

private lemma noBoundW_dataErr_self {T : ℕ} (h : 0 < T) :
    dataErr (noBoundW T h) ⟨0, h⟩ = (e ⟨0, by norm_num⟩ : Vec 9) := by
  funext i
  simp only [dataErr, noBoundW, e]
  by_cases hi : i.val = 0
  · have h1 : (⟨0 * 20 + i.val, by omega⟩ : Fin (T * 20)) = ⟨0, by omega⟩ := by
      apply Fin.ext; simp only; omega
    have h2 : i = (⟨0, by norm_num⟩ : Fin 9) := by
      apply Fin.ext; simp only; omega
    rw [ite_eq_left h1, ite_eq_left h2]
  · have h1 := ne_zero_index (T := T) (k := 0 * 20 + i.val)
      (by omega) (by omega)
    have h2 : ¬ (i = (⟨0, by norm_num⟩ : Fin 9)) := by
      intro hcon; exact hi (by have := congrArg Fin.val hcon; simp only at this; omega)
    rw [ite_eq_right h1, ite_eq_right h2]

private lemma noBoundW_cumErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    cumErr (noBoundW T h) t = (e ⟨0, by norm_num⟩ : Vec 9) := by
  rw [cumErr, Finset.sum_filter]
  have hsingle : (Finset.sum Finset.univ (fun s : Fin T =>
      if s.val ≤ t.val then dataErr (noBoundW T h) s else 0))
      = dataErr (noBoundW T h) ⟨0, h⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin T)))
      (f := fun s : Fin T => if s.val ≤ t.val then dataErr (noBoundW T h) s else 0)
      ⟨0, h⟩ ?_ ?_
    · intro b _ hb
      by_cases hle : b.val ≤ t.val
      · rw [ite_eq_left hle]
        exact noBoundW_dataErr_zero h (fun hz => hb (Fin.ext hz))
      · rw [ite_eq_right hle]
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, h⟩ : Fin T)) hnot
  rw [hsingle]
  exact noBoundW_dataErr_self h

private lemma noBoundW_measErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    measErr (noBoundW T h) t = 0 := by
  funext i
  simp only [measErr, noBoundW, e]
  have hne := ne_zero_index (T := T) (k := t.val * 20 + 9 + i.val)
    (by omega) (by have := i.isLt; have := t.isLt; omega)
  rw [ite_eq_right hne]
  rfl

private lemma noBoundW_ancErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    ancErr (noBoundW T h) t = 0 := by
  funext c
  simp only [ancErr, noBoundW, e]
  have hne := ne_zero_index (T := T) (k := t.val * 20 + 18 + c.val)
    (by omega) (by have := c.isLt; have := t.isLt; omega)
  rw [ite_eq_right hne]
  rfl

private lemma noBoundW_syndrome {T : ℕ} (h : 0 < T) (t : Fin T) :
    bsSyndrome (noBoundW T h) t = bsSyndrome (noBoundW T h) ⟨0, h⟩ := by
  simp only [bsSyndrome, noBoundW_cumErr h t, noBoundW_cumErr h ⟨0, h⟩,
    noBoundW_measErr h t, noBoundW_measErr h ⟨0, h⟩,
    noBoundW_ancErr h t, noBoundW_ancErr h ⟨0, h⟩]

private lemma bstXW_dot_e0 : bstXW ⬝ᵥ (e ⟨0, by norm_num⟩ : Vec 9) = 1 := by decide

private lemma noBoundW_readout {T : ℕ} (h : 0 < T) (t : Fin T) :
    bsReadout (noBoundW T h) t = 1 := by
  simp only [bsReadout, noBoundW_cumErr h t, noBoundW_measErr h t, add_zero]
  exact bstXW_dot_e0

private lemma noBoundW_weight {T : ℕ} (h : 0 < T) :
    hammingNorm (noBoundW T h) = 1 := by
  rw [← weight_eq_hammingNorm]
  have hsingle : support (noBoundW T h) = {⟨0, by omega⟩} := by
    ext j
    rw [mem_support, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      exact hj (by simp [noBoundW, e, hne])
    · intro hj
      rw [hj]
      simp [noBoundW, e]
  rw [hsingle, Finset.card_singleton]

/--
**Once the boundary detector is dropped, an undetectable logical fault of weight 1 exists for any
number of rounds**.

Its relation to `bsHook_noBoundary_weight_one`: that one is the $T=1$ instance, and at $T=1$ the
conjunction "consecutive rounds agree" is empty, so it verifies nothing at all. This statement is
the substance of "the boundary check cannot be dropped": the witness flips the readout in **every
round**, while all rounds have exactly the same syndrome.
-/
theorem noBoundary_light_of_any_rounds {T : ℕ} (h : 0 < T) :
    ∃ f : Vec (T * 20),
      bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1 := by
  refine ⟨noBoundW T h, ?_, ?_, noBoundW_weight h⟩
  · intro t u _
    rw [noBoundW_syndrome h t, noBoundW_syndrome h u]
  · have hall : ∀ t : Fin T, bsReadout (noBoundW T h) t = 1 := noBoundW_readout h
    have hfilter : (Finset.univ.filter
        (fun t : Fin T => bsReadout (noBoundW T h) t = 1)) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun t _ => hall t)
    rw [bsLogicalFault, hfilter, Finset.card_univ, Fintype.card_fin]
    omega

/--
**Summary of the comparison**: the three numbers side by side: $2$ in one round, back to at least
the boundary value from two rounds on, and a collapse to $1$ for **any number of rounds** once the
boundary is dropped.

The last item is `noBoundary_light_of_any_rounds` (for all $T\ge1$), not the vacuous $T=1$ instance;
both are kept, because the $T=1$ one is its reading.
-/
theorem bsHook_summary :
    (hookCand 1 1 = []) ∧ (hookCand 2 2 = []) ∧ (hookCand 3 2 = []) ∧
      (hookCand 4 2 = []) ∧
      (∃ f : Vec (1 * 20),
        bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1) ∧
      (∀ T : ℕ, 0 < T → ∃ f : Vec (T * 20),
        bsDetectorsOK_noBoundary f ∧ bsLogicalFault f ∧ hammingNorm f = 1) :=
  ⟨bsHook_T1_no_light_one, bsHook_T2_no_light, bsHook_T3_no_light, bsHook_T4_no_light,
    bsHook_noBoundary_weight_one, fun _ hT => noBoundary_light_of_any_rounds hT⟩

/-!
## 6. The two halves of C3: the perfection of **either end** settles the whole time axis

The C3 criterion is read as a **boundary condition**: "both the first and the last round are taken
to be perfect". This module turns the **first-round** half into a detector, $D_0=\sigma_0$, on the
grounds that the code starts the protocol inside the code space. The **last-round** half says that
after the final round the code is still in the code space, so the last round's syndrome is zero as
well.

This section proves that the two halves are **not two independent things** in the model, but the
two ends of one chain:

* the first round plus the comparison of consecutive rounds implies that all syndromes are zero
  (the mechanism already established in Section 1), so the last-round clause is **entailed**;
* **the converse holds as well**: the last round plus the comparison of consecutive rounds also
  pins all syndromes to zero (backward induction, see below).

Hence "this module models only the first-round half of C3" is **no longer a gap**: the two halves
are mutually derivable, and **the two sides give elementwise the same candidate set**, so the two
halves of C3 give the same distance. What is genuinely indispensable is "at least one end is
perfect": with neither end, `noBoundary_light_of_any_rounds` has already driven the distance down to
1.
-/

/-- The detectors with **both boundaries written out** (the first round $D_0=\sigma_0$ and the last round $\sigma_{T-1}=0$). -/
abbrev bsDetectorsOK_closed (f : Vec (T * 20)) : Prop :=
  bsDetectorsOK f ∧ ∀ t : Fin T, t.val + 1 = T → bsSyndrome f t = 0

/-- The detectors with **the last-round end only** (the comparison of consecutive rounds plus $\sigma_{T-1}=0$, without the first-round $D_0$). -/
abbrev bsDetectorsOK_terminal (f : Vec (T * 20)) : Prop :=
  (∀ t u : Fin T, u.val = t.val + 1 → bsSyndrome f t = bsSyndrome f u) ∧
    ∀ t : Fin T, t.val + 1 = T → bsSyndrome f t = 0

/-- **The last-round end is entailed by the first-round end** (a direct corollary of the mechanism of Section 1). -/
theorem bsDetectorsOK_closed_of_firstEnd {f : Vec (T * 20)}
    (h : bsDetectorsOK f) : bsDetectorsOK_closed f :=
  ⟨h, fun t _ => bsDetectorsOK_syndrome_eq_zero h t⟩

/-- **The first-round end is entailed by the last-round end** (backward induction: the last round is pinned to zero first, and the comparison of consecutive rounds then carries it backwards). -/
theorem bsDetectorsOK_firstEnd_syndrome_eq_zero {f : Vec (T * 20)}
    (h : bsDetectorsOK_terminal f) (t : Fin T) : bsSyndrome f t = 0 := by
  obtain ⟨hs, hterm⟩ := h
  have key : ∀ k, ∀ t : Fin T, t.val + k = T - 1 → bsSyndrome f t = 0 := by
    intro k
    induction k with
    | zero =>
      intro t ht
      exact hterm t (by omega)
    | succ k ih =>
      intro t ht
      have hlt : t.val + 1 < T := by omega
      rw [hs t ⟨t.val + 1, hlt⟩ rfl]
      exact ih ⟨t.val + 1, hlt⟩ (by simp only; omega)
  exact key (T - 1 - t.val) t (by omega)

/--
**The two ends are equivalent**: the last-round end together with the comparison of consecutive
rounds gives the same zero-syndrome conclusion as the first-round end together with the same
comparison (the two theorems mirror each other).
-/
theorem bsDetectorsOK_syndrome_eq_zero_of_terminal {f : Vec (T * 20)}
    (h : bsDetectorsOK_terminal f) (t : Fin T) : bsSyndrome f t = 0 :=
  bsDetectorsOK_firstEnd_syndrome_eq_zero h t

/-- The same weight-limited enumeration, using the detector set with **both boundaries**. -/
def hookCandClosed (T s : ℕ) : List (Vec (T * 20)) :=
  (lightVecs (T * 20) s).filter
    (fun f => decide (bsDetectorsOK_closed f ∧ bsLogicalFault f))

-- 不设 `hookCandTerminal`（用末轮那端的探测器集做的同一个枚举）：它不会被使用，而
-- "两端给出同一个候选集"这件事**已经**由 `hookCandClosed_eq` 证了
-- （closed 与首端逐元素相同，配 `bsDetectorsOK_firstEnd_syndrome_eq_zero` 把末端
-- 也算进来）。留一个没有定理支撑的镜像定义，比不留更容易被误读成"那一侧也证过"。
/--
**Both boundaries do not change the candidate set**: adding the last-round half to the detector set
leaves the weight-limited candidate set elementwise the same (so the two halves of C3 give the same
distance).
-/
theorem hookCandClosed_eq (T s : ℕ) : hookCandClosed T s = hookCand T s := by
  unfold hookCandClosed hookCand
  refine List.filter_congr fun f _ => ?_
  congr 1
  exact propext
    ⟨fun h => ⟨h.1.1, h.2⟩,
     fun h => ⟨bsDetectorsOK_closed_of_firstEnd h.1, h.2⟩⟩

/--
**The verdict on the two halves of C3**: in the statement "both the first and the last round are
taken to be perfect", **either end** already settles the syndrome of the whole time axis to zero in
this model, and writing both ends down does not change the candidate set. Hence "only the
first-round half is modelled" is not a gap: the last-round half is issued by the half that is
modelled.
-/
theorem c3_both_ends_agree (T s : ℕ) :
    hookCandClosed T s = hookCand T s ∧
      (∀ f : Vec (T * 20), bsDetectorsOK_terminal f →
        ∀ t : Fin T, bsSyndrome f t = 0) :=
  ⟨hookCandClosed_eq T s, fun _ h => bsDetectorsOK_firstEnd_syndrome_eq_zero h⟩

/-!
## 7. Universal recovery: for $T\ge2$, "no escape of weight $\le2$" holds for every number of rounds

The `bsHook_T2_no_light` / `bsHook_T3_no_light` / `bsHook_T4_no_light` of Section 3 are three
`decide` readings at individual $T$. This section raises the "blocking" to a **theorem**: it is
proved directly for $T\ge4$, the `decide` results are reused for $T=2,3$, and together they hold for
all $T\ge2$. This mirrors the collapse of Section 5 (`noBoundary_light_of_any_rounds`): **the side
that removes a detector holds for all $T$, and the side that blocks escapes holds for all $T$ as
well**.

The argument has three steps, each readable in one line:

1. **An untouched round has readout zero.** A fault of weight $\le2$ occupies at most two rounds; on
   a round $t$ that is not touched, $\mu_t=\gamma_t=0$, so $\sigma_t=H\cdot\mathrm{cum}_t$, and the
   mechanism theorem (Section 1) has already pinned $\sigma_t$ to zero, that is, **the cumulative
   data error lies in the kernel**. Its weight is at most the fault weight $\le2$, which is less
   than the single-round distance $3$ (`bsSingleRound_noLightFault`), so the readout functional
   vanishes.
2. **The flipped rounds are contained in the touched rounds**, and the number of touched rounds is
   at most the fault weight $\le2$ (each touched round occupies at least one nonzero slot).
3. **The majority is not enough**: $T<2\times\text{flipped rounds}\le4$, contradicting $T\ge4$.

Step 1 is exactly why a hook error has to drag along an ancilla error: a purely data error lighter
than $3$ is either excluded by the kernel or cannot move the readout at all.
-/

/-- **The touched rounds**: the rounds in which the fault support lies (the slot number divided by $20$). -/
def touchedRounds {T : ℕ} (f : Vec (T * 20)) : Finset (Fin T) :=
  (support f).image (fun j => ⟨j.val / 20, by have := j.isLt; omega⟩)

/-- **The number of touched rounds is at most the fault weight**: each touched round occupies at least one nonzero slot. -/
theorem card_touchedRounds_le {T : ℕ} (f : Vec (T * 20)) :
    (touchedRounds f).card ≤ hammingNorm f := by
  rw [touchedRounds, ← weight_eq_hammingNorm]
  exact Finset.card_image_le

/--
**The weight of the cumulative data error is at most the fault weight**: every nonzero coordinate
of the kernel support comes from a nonzero data slot (if the sum is zero then each term is zero, and
picking one nonzero term gives an injection).
-/
theorem wt_cumErr_le {T : ℕ} (f : Vec (T * 20)) (t : Fin T) :
    hammingNorm (cumErr f t) ≤ hammingNorm f := by
  classical
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm]
  have hex : ∀ i : Fin 9, ∃ s : Fin T, s.val ≤ t.val ∧
      (i ∈ support (cumErr f t) → f ⟨s.val * 20 + i.val,
        by have := s.isLt; have := i.isLt; omega⟩ ≠ 0) := by
    intro i
    by_cases hi : i ∈ support (cumErr f t)
    · by_contra hcon
      push Not at hcon
      have hz : cumErr f t i = 0 := by
        rw [cumErr]
        simp only [dataErr, Finset.sum_apply]
        refine Finset.sum_eq_zero fun s hsm => ?_
        by_cases hs : s.val ≤ t.val
        · exact (hcon s hs).2
        · exact absurd (Finset.mem_filter.mp hsm).2 hs
      exact (mem_support.mp hi) hz
    · exact ⟨t, le_refl _, fun h => absurd h hi⟩
  choose φ hφ using hex
  have hbnd : ∀ i : Fin 9, (φ i).val * 20 + i.val < T * 20 := by
    intro i
    have h1 := (φ i).isLt
    have h2 := i.isLt
    omega
  refine Finset.card_le_card_of_injOn
    (f := fun i : Fin 9 => ⟨(φ i).val * 20 + i.val, hbnd i⟩) ?_ ?_
  · intro i hi
    exact mem_support.mpr ((hφ i).2 (Finset.mem_coe.mp hi))
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    have hfa := (φ a).isLt
    have hfb := (φ b).isLt
    have ha := a.isLt
    have hb := b.isLt
    exact Fin.val_injective (by omega)

/-- On an untouched round, all of that round's slots are zero. -/
private lemma slot_zero_of_untouched {T : ℕ} {f : Vec (T * 20)} {t : Fin T}
    (hnt : t ∉ touchedRounds f) (k : ℕ) (hk : k < 20) :
    f ⟨t.val * 20 + k, by have := t.isLt; omega⟩ = 0 := by
  by_contra hne
  have ht := t.isLt
  refine hnt (Finset.mem_image.mpr ⟨⟨t.val * 20 + k, by omega⟩,
    mem_support.mpr hne, by
      exact Fin.ext (show (t.val * 20 + k) / 20 = t.val by omega)⟩)

/-- On an untouched round, both the measurement error and the ancilla error are zero. -/
private lemma untouched_parts {T : ℕ} {f : Vec (T * 20)} {t : Fin T}
    (hnt : t ∉ touchedRounds f) :
    measErr f t = 0 ∧ ancErr f t = 0 := by
  constructor
  · funext c
    have hc := c.isLt
    have ht := t.isLt
    have h0 := slot_zero_of_untouched hnt (9 + c.val) (by omega)
    have hconv : (⟨t.val * 20 + 9 + c.val, by omega⟩ : Fin (T * 20))
        = ⟨t.val * 20 + (9 + c.val), by omega⟩ :=
      Fin.ext (show t.val * 20 + 9 + c.val = t.val * 20 + (9 + c.val) by omega)
    rw [measErr, hconv]
    exact h0
  · funext c
    have hc := c.isLt
    have ht := t.isLt
    have h0 := slot_zero_of_untouched hnt (18 + c.val) (by omega)
    have hconv : (⟨t.val * 20 + 18 + c.val, by omega⟩ : Fin (T * 20))
        = ⟨t.val * 20 + (18 + c.val), by omega⟩ :=
      Fin.ext (show t.val * 20 + 18 + c.val = t.val * 20 + (18 + c.val) by omega)
    rw [ancErr, hconv]
    exact h0

/--
**Step 1**: an untouched round has readout zero, because the cumulative data error lies in the
kernel with weight $<3$ while the single-round distance is exactly $3$, so the readout functional
vanishes.
-/
private lemma readout_eq_zero_of_untouched {T : ℕ} {f : Vec (T * 20)}
    (hdet : bsDetectorsOK f) (hw : hammingNorm f ≤ 2) {t : Fin T}
    (hnt : t ∉ touchedRounds f) : bsReadout f t = 0 := by
  obtain ⟨hμ, hγ⟩ := untouched_parts hnt
  have hσ := bsDetectorsOK_syndrome_eq_zero hdet t
  rw [bsSyndrome, hμ, hγ, add_zero, add_zero] at hσ
  have hker : inKerB bsStabChecks (cumErr f t) = true := by
    rw [inKerB_iff, mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    have hi : (bsStabChecks *ᵥ cumErr f t) i = 0 := congrFun hσ i
    simpa [Matrix.mulVec] using hi
  have hwt : hammingNorm (cumErr f t) ≤ 2 := le_trans (wt_cumErr_le f t) hw
  show bstXW ⬝ᵥ (cumErr f t + measErr f t) = 0
  rw [hμ, add_zero]
  have h01 : bstXW ⬝ᵥ cumErr f t = 0 ∨ bstXW ⬝ᵥ cumErr f t = 1 := by
    have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact hx _
  rcases h01 with h0 | h1
  · exact h0
  · exact absurd (bsSingleRound_noLightFault (cumErr f t) ⟨hker, h1⟩) (by omega)

/--
**Universal recovery (lower-bound side)**: over $T\ge4$ rounds, a fault of weight $\le2$ cannot be
both undetectable and logic-flipping.
-/
theorem bsHook_no_light_of_four_le {T : ℕ} (hT : 4 ≤ T) {f : Vec (T * 20)}
    (hw : hammingNorm f ≤ 2) (hdet : bsDetectorsOK f) : ¬ bsLogicalFault f := by
  intro hlog
  have hsub : (Finset.univ.filter (fun t : Fin T => bsReadout f t = 1))
      ⊆ touchedRounds f := by
    intro t ht
    by_contra hnt
    have h0 := readout_eq_zero_of_untouched hdet hw hnt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h0] at ht
    exact absurd ht (by decide)
  have hcard := Finset.card_le_card hsub
  have h2 := le_trans hcard (le_trans (card_touchedRounds_le f) hw)
  rw [bsLogicalFault] at hlog
  omega

/--
**Universal recovery**: for all $T\ge2$, no undetectable logical fault of weight $\le2$ exists
($T=2,3$ are the existing `decide` results, $T\ge4$ is the theorem above).
-/
theorem bsHook_no_light_universal {T : ℕ} (hT : 2 ≤ T) : hookCand T 2 = [] := by
  rcases (show T = 2 ∨ T = 3 ∨ 4 ≤ T by omega) with rfl | rfl | h4
  · exact bsHook_T2_no_light
  · exact bsHook_T3_no_light
  · refine (List.filter_eq_nil_iff).mpr fun f hf => ?_
    have hw : hammingNorm f ≤ 2 := by
      have hwt := wt_le_of_mem_lightVecs (T * 20) 2 f hf
      rwa [wtRec_eq_hammingNorm] at hwt
    simp only [decide_eq_true_eq]
    intro hp
    obtain ⟨hdet, hlog⟩ := hp
    exact bsHook_no_light_of_four_le h4 hw hdet hlog

/--
**The spacelike escape (for every number of rounds)**: take the all-$X$ single row of the code
(equal to the bare Z-type logical operator `bstZW`, of weight $3$) as a data error persisting from
round $0$ on. It meets every within-round check in an even number of positions, so all syndromes are
zero and every round's readout is $1$. Written as a slot-indicator vector: the first three slots
(data bits $0,1,2$ of round $0$).
-/
def hookW3gen (T : ℕ) : Vec (T * 20) :=
  fun j => if j.val = 0 ∨ j.val = 1 ∨ j.val = 2 then 1 else 0

/-- Coordinate by coordinate, `bstZW` is this three-slot indicator (a closed form, proved directly by `decide`). -/
private theorem bstZW_apply : ∀ i : Fin 9,
    bstZW i = if i.val = 0 ∨ i.val = 1 ∨ i.val = 2 then (1 : ZMod 2) else 0 := by decide

private lemma hookW3gen_dataErr_zero {T : ℕ} {s : Fin T} (hs : s.val ≠ 0) :
    dataErr (hookW3gen T) s = 0 := by
  funext i
  show (if s.val * 20 + i.val = 0 ∨ s.val * 20 + i.val = 1 ∨ s.val * 20 + i.val = 2
      then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3gen_dataErr_self {T : ℕ} (h : 0 < T) :
    dataErr (hookW3gen T) ⟨0, h⟩ = bstZW := by
  funext i
  show (if (0 : ℕ) * 20 + i.val = 0 ∨ 0 * 20 + i.val = 1 ∨ 0 * 20 + i.val = 2
      then (1 : ZMod 2) else 0) = bstZW i
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [bstZW_apply]

private lemma hookW3gen_cumErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    cumErr (hookW3gen T) t = bstZW := by
  rw [cumErr, Finset.sum_filter]
  have hsingle : ∑ s ∈ Finset.univ, (if s.val ≤ t.val then dataErr (hookW3gen T) s else 0)
      = dataErr (hookW3gen T) ⟨0, h⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin T)))
      (f := fun s : Fin T => if s.val ≤ t.val then dataErr (hookW3gen T) s else 0)
      ⟨0, h⟩ ?_ ?_
    · intro b _ hb
      by_cases hle : b.val ≤ t.val
      · rw [ite_eq_left hle]
        exact hookW3gen_dataErr_zero (fun hz => hb (Fin.ext hz))
      · rw [ite_eq_right hle]
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, h⟩ : Fin T)) hnot
  rw [hsingle]
  exact hookW3gen_dataErr_self h

private lemma hookW3gen_measErr {T : ℕ} (t : Fin T) :
    measErr (hookW3gen T) t = 0 := by
  funext c
  show (if t.val * 20 + 9 + c.val = 0 ∨ t.val * 20 + 9 + c.val = 1 ∨
      t.val * 20 + 9 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3gen_ancErr {T : ℕ} (t : Fin T) :
    ancErr (hookW3gen T) t = 0 := by
  funext c
  show (if t.val * 20 + 18 + c.val = 0 ∨ t.val * 20 + 18 + c.val = 1 ∨
      t.val * 20 + 18 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

/-- `inKerB` reporting true means the matrix-vector product is zero (the backward bridge used on the `readout` side). -/
private lemma mulVec_eq_zero_of_inKerB {k : ℕ} (M : Matrix (Fin k) (Fin 9) (ZMod 2))
    {x : Vec 9} (h : inKerB M x = true) : M *ᵥ x = 0 := by
  funext i
  have hrows : ∀ i, (M i) ⬝ᵥ x = 0 := by
    have hker := (inKerB_iff M x).mp h
    rwa [mem_ker_iff_dotProd_rows_eq_zero] at hker
  simpa [Matrix.mulVec] using hrows i

/-- **The spacelike escape exists for every number of rounds**: all detectors are zero, every round's readout is flipped, and the weight is exactly $3$. -/
theorem hookW3gen_witness {T : ℕ} (h : 0 < T) :
    bsDetectorsOK (hookW3gen T) ∧ bsLogicalFault (hookW3gen T) ∧
      hammingNorm (hookW3gen T) = 3 := by
  have hσ : ∀ t : Fin T, bsSyndrome (hookW3gen T) t = 0 := by
    intro t
    rw [bsSyndrome, hookW3gen_cumErr h t, hookW3gen_measErr, hookW3gen_ancErr, add_zero,
      add_zero]
    exact mulVec_eq_zero_of_inKerB bsStabChecks bsSingleRound_witness.1
  have hread : ∀ t : Fin T, bsReadout (hookW3gen T) t = 1 := by
    intro t
    rw [bsReadout, hookW3gen_cumErr h t, hookW3gen_measErr, add_zero]
    exact bsSingleRound_witness.2.1
  refine ⟨⟨fun t _ => hσ t, fun t u _ => by rw [hσ t, hσ u]⟩, ?_, ?_⟩
  · have hfil : (Finset.univ.filter (fun t : Fin T => bsReadout (hookW3gen T) t = 1))
        = Finset.univ :=
      Finset.filter_eq_self.mpr (fun t _ => hread t)
    rw [bsLogicalFault, hfil, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [← weight_eq_hammingNorm]
    have hsupp : support (hookW3gen T) = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
      ext j
      rw [mem_support]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2
      · have hv : hookW3gen T j = 1 := by simp [hookW3gen, hc]
        rw [hv]
        constructor
        · intro _
          rcases hc with h0 | h1 | h2
          · left; exact Fin.ext h0
          · right; left; exact Fin.ext h1
          · right; right; exact Fin.ext h2
        · intro _
          exact one_ne_zero
      · have hv : hookW3gen T j = 0 := by simp [hookW3gen, hc]
        rw [hv]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hmem
          rcases hmem with h0 | h1 | h2
          · exact absurd (Or.inl (congrArg Fin.val h0)) hc
          · exact absurd (Or.inr (Or.inl (congrArg Fin.val h1))) hc
          · exact absurd (Or.inr (Or.inr (congrArg Fin.val h2))) hc
    rw [hsupp]
    simp

/--
**The full form of universal recovery**: for all $T\ge2$, the fault distance of the full protocol
is exactly $3=d$, because no escape of weight $\le2$ exists (the universal theorem) and a spacelike
escape of weight $3$ always exists (the universal witness).
-/
theorem bsHook_distance_eq_three_universal {T : ℕ} (hT : 2 ≤ T) :
    hookCand T 2 = [] ∧
      ∃ f : Vec (T * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 3 := by
  have hpos : 0 < T := by omega
  have hw := hookW3gen_witness hpos
  exact ⟨bsHook_no_light_universal hT, hookW3gen T, hw.1, hw.2.1, hw.2.2⟩


/-!
## 8. The protocol-level price of C4: duplicating a check row raises, not lowers, the distance

One boundary remains beyond Section 7: the zero-price theorem of C4 is a **code-level** statement
(the kernel and the row space are unchanged), and what copying a duplicate check into the
**protocol** does to the spacetime distance was not among the claims. This section supplies a
general theorem in one direction and one instance reading:

* **The general direction (Section 8.2)**: duplicating the check row $0$ (three checks, $21$ slots
  per round) **never adds** an escape under any weight bound: an escape that does not exist in the
  prototype does not exist in the duplicated version either. The mechanism is a **projection map**:
  dropping the third ancilla slot leaves the first two kinds of error and the readout pointwise
  unchanged, makes the detector condition a subset (the prototype only looks at the syndromes of the
  first two checks), and can only lower or preserve the weight.
* **The instance reading (Section 8.3)**: at one round the distance **rises** from $2$ to $3$,
  because the hook pair "data error plus ancilla error" must now conceal both identical checks and
  therefore costs two ancilla errors. From two rounds on the distance is $3$ again (the general
  result supplies the lower bound, and the spacelike escape the upper bound).

Together: **a duplicated check row is just as free at the protocol level, and even more robust**,
which completes the Section 5 sentence "the price for the code is zero" into "no loss for the code
and for the protocol".
-/

/-- **The duplicated checks**: X-type stabilizer $0$ copied once ($3 \times 9$). -/
def dupChecks : Matrix (Fin 3) (Fin 9) (ZMod 2) := Matrix.of ![bstSX, bsCol12, bstSX]

/-- The number of slots per round in the duplicated model: $9$ data plus $9$ measurement plus $3$ ancilla. -/
def dupDataErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 21 + i.val, by have := i.isLt; have := t.isLt; omega⟩

def dupMeasErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 9 :=
  fun i => f ⟨t.val * 21 + 9 + i.val, by have := i.isLt; have := t.isLt; omega⟩

def dupAncErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 3 :=
  fun c => f ⟨t.val * 21 + 18 + c.val, by have := c.isLt; have := t.isLt; omega⟩

def dupCumErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 9 :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val ≤ t.val), dupDataErr f s

def dupSyndrome {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : Vec 3 :=
  dupChecks *ᵥ (dupCumErr f t + dupMeasErr f t) + dupAncErr f t

abbrev dupDetectorsOK {T : ℕ} (f : Vec (T * 21)) : Prop :=
  (∀ t : Fin T, t.val = 0 → dupSyndrome f t = 0) ∧
    (∀ t u : Fin T, u.val = t.val + 1 → dupSyndrome f t = dupSyndrome f u)

def dupReadout {T : ℕ} (f : Vec (T * 21)) (t : Fin T) : ZMod 2 :=
  bstXW ⬝ᵥ (dupCumErr f t + dupMeasErr f t)

abbrev dupLogicalFault {T : ℕ} (f : Vec (T * 21)) : Prop :=
  T < 2 * (Finset.univ.filter (fun t : Fin T => dupReadout f t = 1)).card

def hookCandDup (T s : ℕ) : List (Vec (T * 21)) :=
  (lightVecs (T * 21) s).filter
    (fun f => decide (dupDetectorsOK f ∧ dupLogicalFault f))

/-! ### The projection map: dropping the third ancilla slot -/

/--
**The projection**: copies the values of slots $0$..$19$ of each round back into the $20$-slot
model unchanged (slot $20$ is discarded). The slot number $j=t\cdot20+k$ ($k<20$) maps to
$t\cdot21+k$: the same round, the same offset.
-/
def dupDrop {T : ℕ} (f : Vec (T * 21)) : Vec (T * 20) :=
  fun j => f ⟨j.val / 20 * 21 + j.val % 20, by have := j.isLt; omega⟩

private lemma dupDrop_dataErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    dataErr (dupDrop f) t = dupDataErr f t := by
  funext i
  have hi := i.isLt
  have ht := t.isLt
  show f ⟨(t.val * 20 + i.val) / 20 * 21 + (t.val * 20 + i.val) % 20, by omega⟩
    = f ⟨t.val * 21 + i.val, by omega⟩
  have hval : (t.val * 20 + i.val) / 20 * 21 + (t.val * 20 + i.val) % 20
    = t.val * 21 + i.val := by omega
  exact congrArg f (Fin.ext hval)

private lemma dupDrop_measErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    measErr (dupDrop f) t = dupMeasErr f t := by
  funext c
  have hc := c.isLt
  have ht := t.isLt
  show f ⟨((t.val * 20) + 9 + c.val) / 20 * 21 + ((t.val * 20) + 9 + c.val) % 20, by omega⟩
    = f ⟨t.val * 21 + 9 + c.val, by omega⟩
  have hval : ((t.val * 20) + 9 + c.val) / 20 * 21 + ((t.val * 20) + 9 + c.val) % 20
    = t.val * 21 + 9 + c.val := by omega
  exact congrArg f (Fin.ext hval)

private lemma dupDrop_ancErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) (c : Fin 2) :
    ancErr (dupDrop f) t c = dupAncErr f t ⟨c.val, by omega⟩ := by
  have hc := c.isLt
  have ht := t.isLt
  show f ⟨((t.val * 20) + 18 + c.val) / 20 * 21 + ((t.val * 20) + 18 + c.val) % 20, by omega⟩
    = f ⟨t.val * 21 + 18 + c.val, by omega⟩
  have hval : ((t.val * 20) + 18 + c.val) / 20 * 21 + ((t.val * 20) + 18 + c.val) % 20
    = t.val * 21 + 18 + c.val := by omega
  exact congrArg f (Fin.ext hval)

private lemma dupDrop_cumErr {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    cumErr (dupDrop f) t = dupCumErr f t := by
  rw [cumErr, dupCumErr]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dupDrop_dataErr]

/-- **The readout is unchanged**: the projection does not move the data and measurement slots, and the readout only looks at those. -/
private lemma dupDrop_readout {T : ℕ} (f : Vec (T * 21)) (t : Fin T) :
    bsReadout (dupDrop f) t = dupReadout f t := by
  show bstXW ⬝ᵥ (cumErr (dupDrop f) t + measErr (dupDrop f) t)
    = bstXW ⬝ᵥ (dupCumErr f t + dupMeasErr f t)
  rw [dupDrop_cumErr, dupDrop_measErr]

/-- **The weight can only drop**: the projection discards one slot. -/
private lemma dupDrop_weight {T : ℕ} (f : Vec (T * 21)) :
    hammingNorm (dupDrop f) ≤ hammingNorm f := by
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm]
  refine Finset.card_le_card_of_injOn
    (f := fun j : Fin (T * 20) => ⟨j.val / 20 * 21 + j.val % 20, by
      have := j.isLt; omega⟩) ?_ ?_
  · intro j hj
    refine Finset.mem_coe.mpr (mem_support.mpr ?_)
    have hv : dupDrop f j ≠ 0 := mem_support.mp (Finset.mem_coe.mp hj)
    exact hv
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    exact Fin.val_injective (by
      have ha := a.isLt
      have hb := b.isLt
      have hae := Nat.div_add_mod (a.val) 20
      have hbe := Nat.div_add_mod (b.val) 20
      omega)

/-- **The first two checks have componentwise identical syndromes** (the duplicated row sits at index $2$ and the projection does not read it). -/
private lemma dupDrop_syndrome {T : ℕ} (f : Vec (T * 21)) (t : Fin T) (c : Fin 2) :
    bsSyndrome (dupDrop f) t c = dupSyndrome f t ⟨c.val, by omega⟩ := by
  show bsStabChecks c ⬝ᵥ (cumErr (dupDrop f) t + measErr (dupDrop f) t)
      + ancErr (dupDrop f) t c
    = dupChecks ⟨c.val, by omega⟩ ⬝ᵥ (dupCumErr f t + dupMeasErr f t)
      + dupAncErr f t ⟨c.val, by omega⟩
  rw [dupDrop_cumErr, dupDrop_measErr, dupDrop_ancErr]
  fin_cases c <;> rfl

/-- **The detector condition is a subset**: the prototype only looks at the first two checks, so the duplicated version's condition implies the prototype's. -/
private lemma dupDrop_detectors {T : ℕ} {f : Vec (T * 21)} (h : dupDetectorsOK f) :
    bsDetectorsOK (dupDrop f) := by
  obtain ⟨hb, hs⟩ := h
  constructor
  · intro t ht
    funext c
    have h0 := hb t ht
    rw [dupDrop_syndrome f t c]
    exact congrFun h0 _
  · intro t u htu
    funext c
    have hcmp := hs t u htu
    have hc := congrFun hcmp (⟨c.val, by omega⟩ : Fin 3)
    simp only [dupDrop_syndrome f t c, dupDrop_syndrome f u c]
    exact hc

/-- **The logical flip is unchanged**: the readouts agree round by round, hence so do the majority votes. -/
private lemma dupDrop_logical {T : ℕ} {f : Vec (T * 21)} (h : dupLogicalFault f) :
    bsLogicalFault (dupDrop f) := by
  have hfil : (Finset.univ.filter (fun t : Fin T => bsReadout (dupDrop f) t = 1))
      = Finset.univ.filter (fun t : Fin T => dupReadout f t = 1) := by
    refine Finset.filter_congr fun t _ => ?_
    rw [dupDrop_readout]
  rw [bsLogicalFault, hfil]
  exact h

/--
**The protocol-level price of C4 (the general direction)**: an escape under a given weight bound
that does not exist in the prototype does not exist in the duplicated version either, so duplicating
a check row **does not lower** the fault distance of the protocol.
-/
theorem hookCandDup_no_light_of {T s : ℕ} (h : hookCand T s = []) :
    hookCandDup T s = [] := by
  refine (List.filter_eq_nil_iff).mpr fun f hf hp => ?_
  have hw20 : hammingNorm (dupDrop f) ≤ s :=
    le_trans (dupDrop_weight f) (by
      have hw := wt_le_of_mem_lightVecs (T * 21) s f hf
      rwa [wtRec_eq_hammingNorm] at hw)
  have hmem : dupDrop f ∈ hookCand T s := by
    refine (List.mem_filter).mpr ⟨mem_lightVecs (T * 20) s (dupDrop f) ?_, ?_⟩
    · rw [wtRec_eq_hammingNorm]
      exact hw20
    · simp only [decide_eq_true_eq]
      exact ⟨dupDrop_detectors (of_decide_eq_true hp).1,
             dupDrop_logical (of_decide_eq_true hp).2⟩
  rw [h] at hmem
  exact absurd hmem (by simp)

/-! ### The instance reading -/

/--
**The single-round hook witness of the duplicated version**: a data error (location $0$) together
with **two** ancilla errors (locations $18$ and $20$, one for the original row and one for the
duplicate).
-/
def dupW1 : Vec (1 * 21) :=
  fun j => if j.val = 0 ∨ j.val = 18 ∨ j.val = 20 then 1 else 0

/-- The three facts about the witness: all detectors are zero, the logical value is flipped, and the weight is exactly $3$. -/
theorem dupHook_T1_witness :
    dupDetectorsOK dupW1 ∧ dupLogicalFault dupW1 ∧ hammingNorm dupW1 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **$T=1$: the duplicated version has no escape of weight $\le2$**, because the hook must conceal both identical checks at once. -/
theorem hookCandDup_T1_no_light_two : hookCandDup 1 2 = [] := by decide

/--
**The distance of the duplicated version at $T=1$ is exactly $3$** (above the prototype's $2$): the
duplicated check row raises the price of the hook from one ancilla error to two, and the single-round
distance returns to the code distance.
-/
theorem hookCandDup_T1_distance_eq_three :
    hookCandDup 1 2 = [] ∧
      ∃ f : Vec (1 * 21), dupDetectorsOK f ∧ dupLogicalFault f ∧ hammingNorm f = 3 :=
  ⟨hookCandDup_T1_no_light_two, dupW1, dupHook_T1_witness.1, dupHook_T1_witness.2.1,
    dupHook_T1_witness.2.2⟩

/-- **The spacelike escape (duplicated version, for every number of rounds)**: the same pattern as the prototype, on data slots $0,1,2$. -/
def hookW3Dup (T : ℕ) : Vec (T * 21) :=
  fun j => if j.val = 0 ∨ j.val = 1 ∨ j.val = 2 then 1 else 0

private theorem bstZW_apply' : ∀ i : Fin 9,
    bstZW i = if i.val = 0 ∨ i.val = 1 ∨ i.val = 2 then (1 : ZMod 2) else 0 := by decide

private lemma hookW3Dup_dataErr_zero {T : ℕ} {s : Fin T} (hs : s.val ≠ 0) :
    dupDataErr (hookW3Dup T) s = 0 := by
  funext i
  show (if s.val * 21 + i.val = 0 ∨ s.val * 21 + i.val = 1 ∨ s.val * 21 + i.val = 2
      then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3Dup_dataErr_self {T : ℕ} (h : 0 < T) :
    dupDataErr (hookW3Dup T) ⟨0, h⟩ = bstZW := by
  funext i
  show (if (0 : ℕ) * 21 + i.val = 0 ∨ 0 * 21 + i.val = 1 ∨ 0 * 21 + i.val = 2
      then (1 : ZMod 2) else 0) = bstZW i
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [bstZW_apply']

private lemma hookW3Dup_cumErr {T : ℕ} (h : 0 < T) (t : Fin T) :
    dupCumErr (hookW3Dup T) t = bstZW := by
  rw [dupCumErr, Finset.sum_filter]
  have hsingle : ∑ s ∈ Finset.univ, (if s.val ≤ t.val then dupDataErr (hookW3Dup T) s else 0)
      = dupDataErr (hookW3Dup T) ⟨0, h⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin T)))
      (f := fun s : Fin T => if s.val ≤ t.val then dupDataErr (hookW3Dup T) s else 0)
      ⟨0, h⟩ ?_ ?_
    · intro b _ hb
      by_cases hle : b.val ≤ t.val
      · rw [ite_eq_left hle]
        exact hookW3Dup_dataErr_zero (fun hz => hb (Fin.ext hz))
      · rw [ite_eq_right hle]
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, h⟩ : Fin T)) hnot
  rw [hsingle]
  exact hookW3Dup_dataErr_self h

private lemma hookW3Dup_measErr {T : ℕ} (t : Fin T) :
    dupMeasErr (hookW3Dup T) t = 0 := by
  funext c
  show (if t.val * 21 + 9 + c.val = 0 ∨ t.val * 21 + 9 + c.val = 1 ∨
      t.val * 21 + 9 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

private lemma hookW3Dup_ancErr {T : ℕ} (t : Fin T) :
    dupAncErr (hookW3Dup T) t = 0 := by
  funext c
  show (if t.val * 21 + 18 + c.val = 0 ∨ t.val * 21 + 18 + c.val = 1 ∨
      t.val * 21 + 18 + c.val = 2 then (1 : ZMod 2) else 0) = 0
  split
  · next h => exact absurd h (by omega)
  · rfl

/--
**The spacelike escape of the duplicated version exists for every number of rounds** (the same
pattern as the prototype: all syndromes zero, every round flipped, weight $3$).
-/
theorem hookW3Dup_witness {T : ℕ} (h : 0 < T) :
    dupDetectorsOK (hookW3Dup T) ∧ dupLogicalFault (hookW3Dup T) ∧
      hammingNorm (hookW3Dup T) = 3 := by
  have hker : dupChecks *ᵥ bstZW = 0 := by decide
  have hσ : ∀ t : Fin T, dupSyndrome (hookW3Dup T) t = 0 := by
    intro t
    rw [dupSyndrome, hookW3Dup_cumErr h t, hookW3Dup_measErr, hookW3Dup_ancErr, add_zero,
      add_zero]
    exact hker
  have hread : ∀ t : Fin T, dupReadout (hookW3Dup T) t = 1 := by
    intro t
    rw [dupReadout, hookW3Dup_cumErr h t, hookW3Dup_measErr, add_zero]
    exact bsSingleRound_witness.2.1
  refine ⟨⟨fun t _ => hσ t, fun t u _ => by rw [hσ t, hσ u]⟩, ?_, ?_⟩
  · have hfil : (Finset.univ.filter (fun t : Fin T => dupReadout (hookW3Dup T) t = 1))
        = Finset.univ :=
      Finset.filter_eq_self.mpr (fun t _ => hread t)
    rw [dupLogicalFault, hfil, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [← weight_eq_hammingNorm]
    have hsupp : support (hookW3Dup T) = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
      ext j
      rw [mem_support]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2
      · have hv : hookW3Dup T j = 1 := by simp [hookW3Dup, hc]
        rw [hv]
        constructor
        · intro _
          rcases hc with h0 | h1 | h2
          · left; exact Fin.ext h0
          · right; left; exact Fin.ext h1
          · right; right; exact Fin.ext h2
        · intro _
          exact one_ne_zero
      · have hv : hookW3Dup T j = 0 := by simp [hookW3Dup, hc]
        rw [hv]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hmem
          rcases hmem with h0 | h1 | h2
          · exact absurd (Or.inl (congrArg Fin.val h0)) hc
          · exact absurd (Or.inr (Or.inl (congrArg Fin.val h1))) hc
          · exact absurd (Or.inr (Or.inr (congrArg Fin.val h2))) hc
    rw [hsupp]
    simp

/--
**The full verdict on the protocol-level price of C4**: duplicating a check row adds no escape under
any weight bound (the general theorem); the single-round reading rises from $2$ to $3$; and from two
rounds on the distance is $3$ again.
-/
theorem c4_dup_price_verdict {T : ℕ} (hT : 2 ≤ T) :
    hookCandDup T 2 = [] ∧
      ∃ f : Vec (T * 21), dupDetectorsOK f ∧ dupLogicalFault f ∧ hammingNorm f = 3 := by
  have hpos : 0 < T := by omega
  have hw := hookW3Dup_witness hpos
  exact ⟨hookCandDup_no_light_of (bsHook_no_light_universal hT), hookW3Dup T, hw.1, hw.2.1,
    hw.2.2⟩

/-!
## 9. The single-round closed form: the distance at T=1 is min{wt(y)+wt(Hy) : w·y=1}

The `bsHook_T1_distance_eq_two` of Section 2 is a `decide` reading item by item. This section raises
it to a **closed form**: the full-protocol distance at one round is given by a quantity that depends
on single-round data only:

$$\min\{\,\mathrm{wt}(y)+\mathrm{wt}(Hy)\;:\;w\cdot y=1\,\}.$$

How to read it: in one round a fault $(d,\mu,\gamma)$ is undetectable $\iff$ $\gamma=H(d+\mu)$, and
the readout is flipped $\iff$ $w\cdot(d+\mu)=1$. After merging $y:=d+\mu$, the cost is exactly "the
weight of $y$ itself plus the weight spent on ancilla errors that cancel the syndrome". The hook is
$y=e_0$: one data position and one ancilla position.
-/

/-- **A definitional bridge**: at T=1 the values of the three fault kinds are the values of the corresponding slots (`rfl` level). -/
private lemma dataErr_apply (f : Vec (1 * 20)) (i : Fin 9) :
    dataErr f ⟨0, by omega⟩ i = f ⟨0 * 20 + i.val, by have := i.isLt; omega⟩ := rfl

private lemma measErr_apply (f : Vec (1 * 20)) (i : Fin 9) :
    measErr f ⟨0, by omega⟩ i = f ⟨0 * 20 + 9 + i.val, by have := i.isLt; omega⟩ := rfl

private lemma ancErr_apply (f : Vec (1 * 20)) (c : Fin 2) :
    ancErr f ⟨0, by omega⟩ c = f ⟨0 * 20 + 18 + c.val, by have := c.isLt; omega⟩ := rfl

/-- `hammingNorm` is subadditive: the union of the supports is a superset. -/
private lemma hammingNorm_add_le {n : ℕ} (x y : Vec n) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  classical
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm, ← weight_eq_hammingNorm]
  have hsub : support (x + y) ⊆ support x ∪ support y := by
    intro i hi
    simp only [support, Finset.mem_filter, Finset.mem_union] at hi ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hv : (x + y) i = x i + y i := rfl
    rw [h1 (Finset.mem_univ i), h2 (Finset.mem_univ i)] at hv
    rw [hv] at hi
    simp at hi
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- The cumulative error at T=1 equals the data error of round $0$ (only the term $s=0$ survives the filter). -/
private lemma cumErr_T1 (f : Vec (1 * 20)) :
    cumErr f ⟨0, by omega⟩ = dataErr f ⟨0, by omega⟩ := by
  rw [cumErr, Finset.sum_filter]
  have hsingle : ∑ s ∈ Finset.univ, (if s.val ≤ 0 then dataErr f s else 0)
      = dataErr f ⟨0, by omega⟩ := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin 1)))
      (f := fun s : Fin 1 => if s.val ≤ 0 then dataErr f s else 0)
      ⟨0, by omega⟩ ?_ ?_
    · intro b _ hb
      have hbl : b.val = 0 := by have := b.isLt; omega
      exact absurd (Fin.ext hbl) hb
    · intro hnot
      exact absurd (Finset.mem_univ (⟨0, by omega⟩ : Fin 1)) hnot
  rw [hsingle]

/-- The single-round detector condition holds if and only if the ancilla error is exactly the syndrome. -/
private lemma syndrome_of_T1 {f : Vec (1 * 20)} (h : bsDetectorsOK f) :
    ancErr f ⟨0, by omega⟩ = bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩
      + measErr f ⟨0, by omega⟩) := by
  have h0 := h.1 ⟨0, by omega⟩ rfl
  rw [bsSyndrome, cumErr_T1] at h0
  funext c
  have hc : (bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩)
      + ancErr f ⟨0, by omega⟩) c = 0 := congrFun h0 c
  have hsplit : (bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩
      + measErr f ⟨0, by omega⟩) + ancErr f ⟨0, by omega⟩) c
      = (bsStabChecks *ᵥ (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩)) c
        + ancErr f ⟨0, by omega⟩ c := rfl
  rw [hsplit] at hc
  exact ((add_eq_zero_iff_eq _ _).mp hc).symm

/-! ### Weight decomposition: the images of the three supports fall disjointly into the fault support -/

/-- The embedding of the data slots. -/
private def slotD (i : Fin 9) : Fin (1 * 20) := ⟨0 * 20 + i.val, by have := i.isLt; omega⟩

/-- The embedding of the measurement slots. -/
private def slotM (i : Fin 9) : Fin (1 * 20) := ⟨0 * 20 + 9 + i.val, by have := i.isLt; omega⟩

/-- The embedding of the ancilla slots. -/
private def slotA (c : Fin 2) : Fin (1 * 20) := ⟨0 * 20 + 18 + c.val, by have := c.isLt; omega⟩

/-- The three support images are pairwise disjoint: every disjointness obligation is discharged by `omega` on slot values. -/
private lemma images_disjoint (f : Vec (1 * 20)) :
    Disjoint ((support (dataErr f ⟨0, by omega⟩)).image slotD)
      ((support (measErr f ⟨0, by omega⟩)).image slotM
        ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA)
    ∧ Disjoint ((support (measErr f ⟨0, by omega⟩)).image slotM)
      ((support (ancErr f ⟨0, by omega⟩)).image slotA) := by
  constructor
  · refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
    · refine Finset.disjoint_right.mpr fun a ha hmem => ?_
      obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hmem
      have hval : (0 : ℕ) * 20 + i.val = 0 * 20 + 9 + j.val :=
        congrArg Fin.val (hia.trans hja.symm)
      omega
    · refine Finset.disjoint_right.mpr fun a ha hmem => ?_
      obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
      obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hmem
      have hval : (0 : ℕ) * 20 + i.val = 0 * 20 + 18 + c.val :=
        congrArg Fin.val (hia.trans hca.symm)
      have := i.isLt
      have := c.isLt
      omega
  · refine Finset.disjoint_right.mpr fun a ha hmem => ?_
    obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hmem
    have hval : (0 : ℕ) * 20 + 9 + i.val = 0 * 20 + 18 + c.val :=
      congrArg Fin.val (hia.trans hca.symm)
    have := i.isLt
    have := c.isLt
    omega

private lemma slotD_inj : Function.Injective slotD := fun a b h =>
  Fin.val_injective (by
    have hval : (0 : ℕ) * 20 + a.val = 0 * 20 + b.val := congrArg Fin.val h
    omega)

private lemma slotM_inj : Function.Injective slotM := fun a b h =>
  Fin.val_injective (by
    have hval : (0 : ℕ) * 20 + 9 + a.val = 0 * 20 + 9 + b.val := congrArg Fin.val h
    omega)

private lemma slotA_inj : Function.Injective slotA := fun a b h =>
  Fin.val_injective (by
    have hval : (0 : ℕ) * 20 + 18 + a.val = 0 * 20 + 18 + b.val := congrArg Fin.val h
    omega)

/-- **The weight decomposition at T=1 (the $\le$ direction)**: the supports of the three fault kinds fall disjointly into the fault support through the slot embeddings. -/
private lemma weight_one_round_le (f : Vec (1 * 20)) :
    hammingNorm (dataErr f ⟨0, by omega⟩) + hammingNorm (measErr f ⟨0, by omega⟩)
      + hammingNorm (ancErr f ⟨0, by omega⟩) ≤ hammingNorm f := by
  classical
  obtain ⟨hout, hin⟩ := images_disjoint f
  have hc1 := Finset.card_union_of_disjoint hout
  have hc2 := Finset.card_union_of_disjoint hin
  have cD : ((support (dataErr f ⟨0, by omega⟩)).image slotD).card
      = (support (dataErr f ⟨0, by omega⟩)).card :=
    Finset.card_image_of_injective _ slotD_inj
  have cM : ((support (measErr f ⟨0, by omega⟩)).image slotM).card
      = (support (measErr f ⟨0, by omega⟩)).card :=
    Finset.card_image_of_injective _ slotM_inj
  have cA : ((support (ancErr f ⟨0, by omega⟩)).image slotA).card
      = (support (ancErr f ⟨0, by omega⟩)).card :=
    Finset.card_image_of_injective _ slotA_inj
  have hkey : ((support (dataErr f ⟨0, by omega⟩)).image slotD
      ∪ ((support (measErr f ⟨0, by omega⟩)).image slotM
        ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA)).card
      = (support (dataErr f ⟨0, by omega⟩)).card
        + ((support (measErr f ⟨0, by omega⟩)).card
          + (support (ancErr f ⟨0, by omega⟩)).card) := by
    rw [hc1, hc2, cD, cM, cA]
  have hsub : ((support (dataErr f ⟨0, by omega⟩)).image slotD
      ∪ ((support (measErr f ⟨0, by omega⟩)).image slotM
        ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA)) ⊆ support f := by
    intro a ha
    have ha' : a ∈ (support (dataErr f ⟨0, by omega⟩)).image slotD
        ∨ a ∈ ((support (measErr f ⟨0, by omega⟩)).image slotM
          ∪ (support (ancErr f ⟨0, by omega⟩)).image slotA) := Finset.mem_union.mp ha
    rcases ha' with h | h
    · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp h
      rw [← hia]
      exact mem_support.mpr ((dataErr_apply f i) ▸ (mem_support.mp hi))
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp h
        rw [← hia]
        exact mem_support.mpr ((measErr_apply f i) ▸ (mem_support.mp hi))
      · obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp h
        rw [← hca]
        exact mem_support.mpr ((ancErr_apply f c) ▸ (mem_support.mp hc))
  rw [← weight_eq_hammingNorm (dataErr f ⟨0, by omega⟩),
    ← weight_eq_hammingNorm (measErr f ⟨0, by omega⟩),
    ← weight_eq_hammingNorm (ancErr f ⟨0, by omega⟩), ← weight_eq_hammingNorm f]
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [hkey]
  omega


/-! ### The closed form -/

/-- **Extracting the single-round readout flip**: at T=1 the majority vote has only one round to flip. -/
private lemma logical_T1 {f : Vec (1 * 20)} (h : bsLogicalFault f) :
    bsReadout f ⟨0, by omega⟩ = 1 := by
  rw [bsLogicalFault] at h
  have hle : (Finset.univ.filter (fun t : Fin 1 => bsReadout f t = 1)).card
      ≤ (Finset.univ : Finset (Fin 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  have h1 : (Finset.univ.filter (fun t : Fin 1 => bsReadout f t = 1)).card = 1 := by omega
  have hpos : 0 < (Finset.univ.filter (fun t : Fin 1 => bsReadout f t = 1)).card := by
    rw [h1]; exact zero_lt_one
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  have hte : t = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := t.isLt; omega)
  have := (Finset.mem_filter.mp ht).2
  rw [hte] at this
  exact this

/-- **The lower-bound direction**: any single-round escape yields a cheaper $y$. -/
private lemma formula_lower {f : Vec (1 * 20)} {s : ℕ} (hdet : bsDetectorsOK f)
    (_hlog : bsLogicalFault f) (hw : hammingNorm f ≤ s) (y : Vec 9)
    (hy : dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩ = y) :
    hammingNorm y + hammingNorm (bsStabChecks *ᵥ y) ≤ s := by
  have h1 : hammingNorm (dataErr f ⟨0, by omega⟩) + hammingNorm (measErr f ⟨0, by omega⟩)
      ≥ hammingNorm (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩) :=
    hammingNorm_add_le _ _
  have h2 := weight_one_round_le f
  have h3 : ancErr f ⟨0, by omega⟩ = bsStabChecks *ᵥ y := by
    rw [syndrome_of_T1 hdet, ← hy]
  rw [h3] at h2
  rw [hy] at h1
  omega

/-- **The single-round witness**: put $y$ into the data slots and the syndrome into the ancilla slots. -/
def t1Wit (y : Vec 9) : Vec (1 * 20) :=
  fun j => if h : j.val < 9 then y ⟨j.val, h⟩
    else if h2 : j.val < 18 then 0
    else (bsStabChecks *ᵥ y) ⟨j.val - 18, by omega⟩

private lemma t1Wit_lt9 (y : Vec 9) (j : Fin (1 * 20)) (h : j.val < 9) :
    t1Wit y j = y ⟨j.val, by omega⟩ := by
  show dite (j.val < 9) _ _ = _
  rw [dite_eq_left h]

private lemma t1Wit_mid (y : Vec 9) (j : Fin (1 * 20)) (h1 : ¬ j.val < 9) (h2 : j.val < 18) :
    t1Wit y j = 0 := by
  show dite (j.val < 9) _ _ = _
  rw [dite_eq_right h1, dite_eq_left h2]

private lemma t1Wit_ge18 (y : Vec 9) (j : Fin (1 * 20)) (h1 : ¬ j.val < 9) (h2 : ¬ j.val < 18) :
    t1Wit y j = (bsStabChecks *ᵥ y) ⟨j.val - 18, by omega⟩ := by
  show dite (j.val < 9) _ _ = _
  rw [dite_eq_right h1, dite_eq_right h2]

private lemma t1Wit_dataErr (y : Vec 9) : dataErr (t1Wit y) ⟨0, by omega⟩ = y := by
  funext i
  rw [dataErr_apply]
  show (t1Wit y) ⟨0 * 20 + i.val, by have := i.isLt; omega⟩ = y i
  simp only [t1Wit]
  have hi : 0 * 20 + i.val < 9 := by have := i.isLt; omega
  rw [dite_eq_left hi]
  have hidx : (⟨0 * 20 + i.val, hi⟩ : Fin 9) = i := Fin.ext (by
    have hv1 : (⟨0 * 20 + i.val, hi⟩ : Fin 9).val = 0 * 20 + i.val := rfl
    omega)
  rw [hidx]

private lemma t1Wit_measErr (y : Vec 9) : measErr (t1Wit y) ⟨0, by omega⟩ = 0 := by
  funext i
  rw [measErr_apply]
  show (t1Wit y) ⟨0 * 20 + 9 + i.val, by have := i.isLt; omega⟩ = 0
  simp only [t1Wit]
  have hi : ¬ (0 * 20 + 9 + i.val < 9) := by omega
  have hi2 : 0 * 20 + 9 + i.val < 18 := by have := i.isLt; omega
  rw [dite_eq_right hi, dite_eq_left hi2]

private lemma t1Wit_ancErr (y : Vec 9) :
    ancErr (t1Wit y) ⟨0, by omega⟩ = bsStabChecks *ᵥ y := by
  funext c
  rw [ancErr_apply]
  show (t1Wit y) ⟨0 * 20 + 18 + c.val, by have := c.isLt; omega⟩
    = (bsStabChecks *ᵥ y) c
  simp only [t1Wit]
  have hi : ¬ (0 * 20 + 18 + c.val < 9) := by omega
  have hi2 : ¬ (0 * 20 + 18 + c.val < 18) := by omega
  rw [dite_eq_right hi, dite_eq_right hi2]
  have hidx : (⟨0 * 20 + 18 + c.val - 18, by omega⟩ : Fin 2) = c :=
    Fin.ext (by
      have hv1 : (⟨0 * 20 + 18 + c.val - 18, by omega⟩ : Fin 2).val
          = 0 * 20 + 18 + c.val - 18 := rfl
      omega)
  rw [hidx]

/--
**The upper-bound direction**: the weight of the witness is at most $\mathrm{wt}(y)+\mathrm{wt}(Hy)$
(the images of the data slots and the ancilla slots cover the support).
-/
private lemma t1Wit_weight (y : Vec 9) :
    hammingNorm (t1Wit y)
      ≤ hammingNorm y + hammingNorm (bsStabChecks *ᵥ y) := by
  classical
  rw [← weight_eq_hammingNorm (t1Wit y)]
  have hsub : support (t1Wit y)
      ⊆ (support y).image slotD ∪ (support (bsStabChecks *ᵥ y)).image slotA := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_image]
    by_cases h9 : j.val < 9
    · left
      have hd : (⟨j.val, by have := j.isLt; omega⟩ : Fin (1 * 20)) = j :=
        Fin.ext (by
          have hv1 : (⟨j.val, by have := j.isLt; omega⟩ : Fin (1 * 20)).val = j.val := rfl
          omega)
      have hv : t1Wit y j = y ⟨j.val, by omega⟩ := t1Wit_lt9 y j h9
      refine ⟨⟨j.val, h9⟩, ?_, ?_⟩
      · rw [mem_support]
        have hv : t1Wit y j = y ⟨j.val, h9⟩ := t1Wit_lt9 y j h9
        have hval := mem_support.mp hj
        rw [hv] at hval
        exact hval
      · exact Fin.ext (by
          have hv1 : (slotD ⟨j.val, h9⟩).val = 0 * 20 + j.val := rfl
          omega)
    · right
      have h18 : ¬ (j.val < 18) := by
        intro hcon
        have hval := mem_support.mp hj
        rw [t1Wit_mid y j h9 hcon] at hval
        exact hval rfl
      obtain ⟨hc, hceq⟩ : ∃ hc : Fin 2,
          hc = ⟨j.val - 18, by have := j.isLt; omega⟩ := ⟨_, rfl⟩
      have hm : hc ∈ support (bsStabChecks *ᵥ y) := by
        rw [mem_support]
        have hv : t1Wit y j = (bsStabChecks *ᵥ y) hc := by
          rw [hceq]
          exact t1Wit_ge18 y j h9 h18
        have hval := mem_support.mp hj
        rw [hv] at hval
        exact hval
      have heq : slotA hc = j := by
        rw [hceq]
        exact Fin.ext (by
          have hv1 : (slotA ⟨j.val - 18, by have := j.isLt; omega⟩).val
              = 0 * 20 + 18 + (j.val - 18) := rfl
          omega)
      exact Finset.mem_image.mpr ⟨hc, hm, heq⟩
  rw [← weight_eq_hammingNorm y, ← weight_eq_hammingNorm (bsStabChecks *ᵥ y)]
  have hd : Disjoint ((support y).image slotD)
      ((support (bsStabChecks *ᵥ y)).image slotA) := by
    refine Finset.disjoint_right.mpr fun a ha hmem => ?_
    obtain ⟨c, _, hca⟩ := Finset.mem_image.mp ha
    obtain ⟨i, _, hia⟩ := Finset.mem_image.mp hmem
    have hval : (0 : ℕ) * 20 + i.val = 0 * 20 + 18 + c.val :=
      congrArg Fin.val (hia.trans hca.symm)
    have := i.isLt
    have := c.isLt
    omega
  have hcard : ((support y).image slotD
      ∪ (support (bsStabChecks *ᵥ y)).image slotA).card
      = (support y).card + (support (bsStabChecks *ᵥ y)).card := by
    rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ slotD_inj,
      Finset.card_image_of_injective _ slotA_inj]
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [hcard]

private lemma t1Wit_detectors (y : Vec 9) : bsDetectorsOK (t1Wit y) := by
  constructor
  · intro t _
    have ht : t = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := t.isLt; omega)
    rw [ht]
    rw [bsSyndrome]
    have hcum : cumErr (t1Wit y) ⟨0, by omega⟩ = y := by
      rw [cumErr_T1, t1Wit_dataErr]
    rw [hcum, t1Wit_measErr, add_zero, t1Wit_ancErr]
    exact add_self _
  · intro t u htu
    have := t.isLt
    have := u.isLt
    omega

private lemma t1Wit_logical {y : Vec 9} (hy : bstXW ⬝ᵥ y = 1) :
    bsLogicalFault (t1Wit y) := by
  have hread : bsReadout (t1Wit y) ⟨0, by omega⟩ = 1 := by
    rw [bsReadout, cumErr_T1, t1Wit_dataErr, t1Wit_measErr, add_zero]
    exact hy
  have hfil : (Finset.univ.filter (fun t : Fin 1 => bsReadout (t1Wit y) t = 1))
      = Finset.univ := by
    refine Finset.filter_eq_self.mpr fun t _ => ?_
    have hte : t = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := t.isLt; omega)
    rw [hte]
    exact hread
  rw [bsLogicalFault, hfil, Finset.card_univ, Fintype.card_fin]
  omega

/--
**The single-round closed form**: no escape of weight $\le s$ exists $\iff$ every $y$ with flipped
readout costs $\mathrm{wt}(y)+\mathrm{wt}(Hy) > s$.
-/
theorem bsHook_T1_formula (s : ℕ) :
    hookCand 1 s = [] ↔ ∀ y : Vec 9, bstXW ⬝ᵥ y = 1 →
      s < hammingNorm y + hammingNorm (bsStabChecks *ᵥ y) := by
  constructor
  · intro h y hy
    by_contra hcon
    push Not at hcon
    have hmem : t1Wit y ∈ hookCand 1 s := by
      refine (List.mem_filter).mpr ⟨mem_lightVecs _ s _ ?_, ?_⟩
      · rw [wtRec_eq_hammingNorm]
        exact le_trans (t1Wit_weight y) (by omega)
      · simp only [decide_eq_true_eq]
        exact ⟨t1Wit_detectors y, t1Wit_logical hy⟩
    rw [h] at hmem
    exact absurd hmem (by simp)
  · intro h
    refine (List.filter_eq_nil_iff).mpr fun f hf hp => ?_
    simp only [decide_eq_true_eq] at hp
    obtain ⟨hdet, hlog⟩ := hp
    have hwf : hammingNorm f ≤ s := by
      have hwt := wt_le_of_mem_lightVecs (1 * 20) s f hf
      rwa [wtRec_eq_hammingNorm] at hwt
    have hread := logical_T1 hlog
    -- 读出 = w·(cum+μ) = w·y
    have hy : bstXW ⬝ᵥ (dataErr f ⟨0, by omega⟩ + measErr f ⟨0, by omega⟩) = 1 := by
      rw [← cumErr_T1 f]
      rw [bsReadout] at hread
      exact hread
    have := formula_lower hdet hlog hwf _ rfl
    exact absurd (h _ hy) (not_lt.mpr this)

/-- **The single-round distance reading (both directions of the closed form)**: the lower bound and the value at $y=e_0$ coincide, so $\min=2$. -/
theorem bsHook_T1_min :
    (∀ y : Vec 9, bstXW ⬝ᵥ y = 1 →
      2 ≤ hammingNorm y + hammingNorm (bsStabChecks *ᵥ y))
    ∧ bstXW ⬝ᵥ ((e ⟨0, by norm_num⟩ : Vec 9)) = 1
    ∧ hammingNorm ((e ⟨0, by norm_num⟩ : Vec 9))
      + hammingNorm (bsStabChecks *ᵥ (e ⟨0, by norm_num⟩ : Vec 9)) = 2 := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- **The closed form reconciled with the item-by-item reading**: the single-round fault distance is exactly the $2$ given by the closed form. -/
theorem bsHook_T1_distance_eq_two_formula :
    hookCand 1 1 = [] ∧
      (∀ y : Vec 9, bstXW ⬝ᵥ y = 1 →
        2 ≤ hammingNorm y + hammingNorm (bsStabChecks *ᵥ y)) ∧
      ∃ f : Vec (1 * 20), bsDetectorsOK f ∧ bsLogicalFault f ∧ hammingNorm f = 2 := by
  refine ⟨bsHook_T1_formula 1 |>.mpr (fun y hy => by
      have h2 := bsHook_T1_min.1 y hy
      omega), bsHook_T1_min.1, ?_⟩
  refine ⟨t1Wit (e ⟨0, by norm_num⟩ : Vec 9), t1Wit_detectors _,
    t1Wit_logical bsHook_T1_min.2.1, ?_⟩
  have hle := t1Wit_weight (e ⟨0, by norm_num⟩ : Vec 9)
  have h2 := bsHook_T1_min.2.2
  have hge : 2 ≤ hammingNorm (t1Wit (e ⟨0, by norm_num⟩ : Vec 9)) := by
    have := formula_lower (t1Wit_detectors _) (t1Wit_logical bsHook_T1_min.2.1)
      (le_of_eq rfl) (e ⟨0, by norm_num⟩ : Vec 9)
      (by rw [t1Wit_dataErr, t1Wit_measErr, add_zero])
    omega
  omega
end QECCertificates
