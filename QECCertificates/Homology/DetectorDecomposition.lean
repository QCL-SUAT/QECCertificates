/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.Basic
import QECCertificates.Codes.FullProtocolFaults

set_option maxHeartbeats 1000000

/-!
# The decomposition step of the generating lemma (gauging draft SI Lemma 1): a
cross-round detector is the sum of adjacent-round comparisons

What the project has always called the "detector generating lemma" is **Lemma 1
(Spacetime code)** and **Lemma 2** of the gauging draft's Supplementary Information, both
of them "a **generating set** of local **detectors**". Lemma 1 lists the generators of a
detector split by time, and its **proof** contains one purely combinatorial sentence:

> Any detector formed by the measurement of the same check at times $(t, t+\kappa)$,
> can be decomposed into detectors at time steps $(t,t+1), (t+1,t+2), \dots,
> (t+\kappa-1, t+\kappa)$.

This module turns that sentence into a theorem. It **does not need** the operator
semantics of the spacetime code: a detector's site is "which round × which check", the
adjacent-round comparisons and the cross-round detectors are both GF(2) vectors on this
site set, and the sentence is exactly a **telescoping sum** -- the intermediate sites
cancel in pairs (over characteristic 2, $1+1=0$), leaving only the two ends.

**Rounds are numbered by the naturals**: the protocol uses the first $T$, but this
identity holds window by window and is independent of $T$ ($t$ through $t+\kappa$ lying
inside the protocol is enough), so $T$ is not pinned in the types here, to keep index
arithmetic out of the statements. **This is the only choice made**, and no content is
dropped.

## Deliverables

* `adjPairVec`: the **adjacent-round comparison** (the generator of Lemma 1) -- the two
  measurements of the same check in rounds $t$ and $t+1$;
* `windowVec`: the **cross-round detector** -- the two measurements of the same check in
  rounds $t$ and $t+\kappa$;
* the **main theorem** `sum_adjPairVec_eq_windowVec`: the cross-round one is exactly the
  sum of $\kappa$ adjacent-round comparisons (the two ends remain, and the "intermediate"
  $t+1,\dots,t+\kappa-1$ each appear twice and cancel);
* `windowVec_eq_zero_of_sum_eq_zero`: the meaning "generating" has here follows from it --
  **all adjacent-round comparisons vanishing implies every cross-round comparison
  vanishes**. This is two faces of the same mechanism as `bsDetectorsOK_syndrome_eq_zero`
  of `QECCertificates.Codes.FullProtocolFaults` (the boundary round plus the
  adjacent-round comparisons pin every syndrome at zero).

## Boundaries

* What is proved here is the **decomposition step inside the proof** of Lemma 1, not
  Lemma 1 itself: Lemma 1 also needs that "any local detector must contain two
  measurements of the **same check**", and that one uses **C4** (the original's verbatim
  *This step assumes there are no local relations in the original code*) and requires
  first building the **circuit-level check set of the spacetime code**. **Lemma 2** is the
  generating set of the **spacetime stabilizers** (Definition 2 of the original) and
  likewise lives at that layer. This module does not claim either of them.
* A site is a "round × check" pair, not the same thing as a qubit of the spacetime code;
  this module uses only this layer of indexing.
-/

namespace QECCertificates.Homology

open QECCertificates

/-- The **site** of a detector: which round × which check. -/
abbrev DetSite (m : ℕ) := ℕ × Fin m

/-- A GF(2) vector on the site set (which "same round, same check" measurements are
counted). -/
abbrev DetVec (m : ℕ) := DetSite m → ZMod 2

/-- The unit vector: only one site is counted. -/
def siteVec {m : ℕ} (x : DetSite m) : DetVec m := fun y => if y = x then 1 else 0

/-- Characteristic 2: a site vector added to itself is zero, an instance of the shared
`QECCertificates.add_self_fun`. -/
@[simp] theorem detVec_add_self {m : ℕ} (v : DetVec m) : v + v = 0 := add_self_fun v

@[simp] theorem siteVec_self {m : ℕ} (x : DetSite m) : siteVec x x = 1 := by
  simp [siteVec]

theorem siteVec_of_ne {m : ℕ} {x y : DetSite m} (h : y ≠ x) : siteVec x y = 0 := by
  simp [siteVec, h]

/-- **The adjacent-round comparison**: the two measurements of the same check $j$ in
rounds $t$ and $t+1$ (the generator of Lemma 1). -/
def adjPairVec {m : ℕ} (j : Fin m) (t : ℕ) : DetVec m :=
  siteVec (t, j) + siteVec (t + 1, j)

/-- **The cross-round detector**: the two measurements of the same check $j$ in rounds
$t$ and $t+\kappa$. -/
def windowVec {m : ℕ} (j : Fin m) (t κ : ℕ) : DetVec m :=
  siteVec (t, j) + siteVec (t + κ, j)

/-- **The decomposition step of Lemma 1**: a detector spanning $(t, t+\kappa)$ is the
sum of $\kappa$ adjacent-round comparisons.

In the sum on the right, the sites of rounds $t+1,\dots,t+\kappa-1$ each appear twice and
cancel over characteristic 2, leaving only the two ends. -/
theorem sum_adjPairVec_eq_windowVec {m : ℕ} (j : Fin m) (t : ℕ) :
    ∀ κ : ℕ, (∑ s ∈ Finset.range κ, adjPairVec j (t + s)) = windowVec j t κ := by
  intro κ
  induction κ with
  | zero => simp [windowVec]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hshift : siteVec ((t + n + 1 : ℕ), j) = siteVec ((t + (n + 1) : ℕ), j) := by
      have h : (t + n + 1 : ℕ) = t + (n + 1) := by omega
      rw [h]
    simp only [windowVec, adjPairVec]
    rw [hshift, add_assoc, ← add_assoc (siteVec ((t + n : ℕ), j)) (siteVec ((t + n : ℕ), j))
          (siteVec ((t + (n + 1) : ℕ), j)), detVec_add_self, zero_add]

/-- **The meaning of "generating" here**: every adjacent-round comparison **vanishing**
$\Rightarrow$ the cross-round detectors it covers vanish.

This is a direct corollary of the main line (`sum_adjPairVec_eq_windowVec`) and the
landing point of that sentence in the proof of Lemma 1: a cross-round detector expresses
nothing beyond what the adjacent-round comparisons can. -/
theorem windowVec_eq_zero_of_sum_eq_zero {m : ℕ} (j : Fin m) (κ t : ℕ)
    (h : (∑ s ∈ Finset.range κ, adjPairVec j (t + s)) = 0) : windowVec j t κ = 0 := by
  rw [← sum_adjPairVec_eq_windowVec j t κ]
  exact h

/-! ## Instantiating on the protocol model: comparing the syndromes of rounds $t$ and
$t+\kappa$ = $\kappa$ adjacent-round comparisons

The `bsDetectorsOK` of `QECCertificates.Codes.FullProtocolFaults` says exactly this: the
ones where adjacent-round syndromes are equal **are** the detectors of that model (along
with one boundary detector on the first round). Transporting the telescoping sum above to
the syndromes gives: **the "cross-round detector" that compares rounds $t$ and
$t+\kappa$ directly equals the sum of the $\kappa$ adjacent-round detectors it covers**
-- no new information, hence no new detectors. This is the form, in this library's model,
of the sentence *can be decomposed into detectors at time steps* in the proof of Lemma 1,
and the other face of the same mechanism as `bsDetectorsOK_syndrome_eq_zero` (boundary
plus adjacent-round comparisons pin the syndrome at zero). -/

/-- The syndrome with rounds numbered by the naturals: rounds outside the protocol are
$0$ (only to make the sum below a **total function**, introducing no physical content). -/
def bsSyndromeNat {T : ℕ} (f : Vec (T * 20)) (t : ℕ) : Vec 2 :=
  if h : t < T then bsSyndrome f ⟨t, h⟩ else 0

/-- On rounds inside the protocol, `bsSyndromeNat` is `bsSyndrome`. -/
theorem bsSyndromeNat_eq {T : ℕ} (f : Vec (T * 20)) {t : ℕ} (h : t < T) :
    bsSyndromeNat f t = bsSyndrome f ⟨t, h⟩ := by
  simp [bsSyndromeNat, h]

/-- **The telescoping sum** (rounds numbered by the naturals, no side condition): the
difference of the syndromes of rounds $t$ and $t+\kappa$ is the sum of $\kappa$
adjacent-round differences. -/
theorem bsSyndromeNat_window_eq_sum_adjacent {T : ℕ} (f : Vec (T * 20)) (t : ℕ) :
    ∀ κ : ℕ, bsSyndromeNat f t + bsSyndromeNat f (t + κ)
      = ∑ s ∈ Finset.range κ,
          (bsSyndromeNat f (t + s) + bsSyndromeNat f (t + s + 1)) := by
  intro κ
  induction κ with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    exact add_self _
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hshift : bsSyndromeNat f (t + n + 1) = bsSyndromeNat f (t + (n + 1)) := by
      have h : t + n + 1 = t + (n + 1) := by omega
      rw [h]
    rw [hshift, add_assoc, ← add_assoc (bsSyndromeNat f (t + n)) (bsSyndromeNat f (t + n))
          (bsSyndromeNat f (t + (n + 1))), add_self, zero_add]

/-- **The form on the protocol model**: the reading obtained by comparing rounds $t$ and
$t+\kappa$ **directly** equals the sum of the $\kappa$ **adjacent-round** readings it
covers -- a cross-round comparison carries no information beyond the adjacent-round
comparisons.

The `bsDetectorsOK` of `QECCertificates.Codes.FullProtocolFaults` is exactly "adjacent
syndromes are equal", so this is the shape, in this library's model, of the sentence *can
be decomposed into detectors at time steps* in the proof of Lemma 1, and the other face
of the same mechanism as `bsDetectorsOK_syndrome_eq_zero` (boundary plus adjacent-round
comparisons pin the syndrome at zero). -/
theorem bsSyndrome_window_eq_sum_adjacent {T : ℕ} (f : Vec (T * 20)) (κ t : ℕ)
    (ht : t + κ < T) :
    bsSyndrome f ⟨t, Nat.lt_of_le_of_lt (Nat.le_add_right t κ) ht⟩
        + bsSyndrome f ⟨t + κ, ht⟩
      = ∑ s ∈ Finset.range κ,
          (bsSyndromeNat f (t + s) + bsSyndromeNat f (t + s + 1)) := by
  have h := bsSyndromeNat_window_eq_sum_adjacent f t κ
  rw [bsSyndromeNat_eq f (Nat.lt_of_le_of_lt (Nat.le_add_right t κ) ht),
      bsSyndromeNat_eq f ht] at h
  exact h

/-! ## 3. Lemma 1 itself: pairs of the same operator generate every deterministic form

The two sections above turned the "decomposition step" into a theorem. The other half of
Lemma 1 -- the original's *in this setting any local detector must contain a pair of
measurements of the same check* -- also lands at the same layer, because its proof is two
sentences:

> the fault-tolerant gauging measurement procedure consists of **repeatedly measuring the
> same checks**. In this setting any local detector must contain a pair of measurements of
> the same check. **This step assumes there are no local relations in the original code.**

Read in the language of the results, this says: attach an **operator label** to each
measurement site, and in the absence of faults **sites with the same label give the same
result** (the measurement does not disturb and the operator is unchanged), so

* a linear form is **deterministic** (constant on every fault-free outcome pattern)
  $\iff$ **the total multiplicity on each label is zero**;
* and the forms whose total multiplicity is zero **are exactly** the sums of "pairs with
  the same label" -- this is the **generating set** Lemma 1 speaks of.

"No local detectors" (C4) in this model is "no linear dependence within a round": a linear
dependence among several checks within one round would give one extra deterministic form,
matching what Remark 2 says ("just add that kind of spacelike detector"). So the
generating set of this section agrees with the one listed in the original (the middle
segment; the two ends additionally involve the initialization / readout of edge qubits,
which this module does not cover). -/

/-- A form: a GF(2) coefficient at each measurement site. The site set may be
"round × check", or any finite set. -/
abbrev Form (S : Type*) := S → ZMod 2

/-- Characteristic 2: a form added to itself is zero, an instance of the shared
`QECCertificates.add_self_fun`. -/
@[simp] theorem form_add_self {S : Type*} (v : Form S) : v + v = 0 := add_self_fun v

/-- The unit form: $1$ at a single site. -/
def unitForm {S : Type*} [DecidableEq S] (a : S) : Form S := Pi.single a 1

/-- **The pair form**: $1$ at each of two sites with the **same operator**. Without
faults their outcomes agree, so it is necessarily deterministic. -/
def pairForm {S : Type*} [DecidableEq S] (a b : S) : Form S := unitForm a + unitForm b

/-- **A deterministic form**: constant on every outcome pattern in which the same
operator keeps giving the same result.

"The same operator repeatedly gives the same result" is a fault-free fact (the measurement
does not disturb and the operator is unchanged), and is the sentence *the procedure
consists of repeatedly measuring the same checks* in the proof of Lemma 1. -/
def IsDeterministic {S L : Type*} [Fintype S] [DecidableEq L] (lab : S → L) (D : Form S) : Prop :=
  ∀ o : Form S, (∀ a b, lab a = lab b → o a = o b) → ∑ s, D s * o s = 0

theorem isDeterministic_zero {S L : Type*} [Fintype S] [DecidableEq L] (lab : S → L) :
    IsDeterministic lab (0 : Form S) := by
  intro o _
  simp

theorem isDeterministic_add {S L : Type*} [Fintype S] [DecidableEq L] {lab : S → L}
    {D D' : Form S} (h : IsDeterministic lab D) (h' : IsDeterministic lab D') :
    IsDeterministic lab (D + D') := by
  intro o ho
  have : ∑ s, (D + D') s * o s = (∑ s, D s * o s) + (∑ s, D' s * o s) := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [this, h o ho, h' o ho, add_zero]

/-- **Determinism $\Rightarrow$ the total multiplicity on each label is zero**: for each
label, take the **indicator form** of that label's sites as the outcome pattern -- it is
constant on labels, so determinism requires its readout to be zero, and that readout is
exactly the total multiplicity on that label.

This half **needs** no choice axiom and does not need every label to occur. -/
theorem classSum_zero_of_isDeterministic {S L : Type*} [Fintype S] [DecidableEq L]
    {lab : S → L} {D : Form S} (h : IsDeterministic lab D) (c : L) :
    ∑ s ∈ Finset.univ.filter (fun s => lab s = c), D s = 0 := by
  classical
  have hconst : ∀ a b : S, lab a = lab b →
      (fun s => if lab s = c then (1 : ZMod 2) else 0) a
        = (fun s => if lab s = c then (1 : ZMod 2) else 0) b := by
    intro a b hab
    simp only
    rw [hab]
  have hz := h (fun s => if lab s = c then (1 : ZMod 2) else 0) hconst
  simp only [mul_ite, mul_one, mul_zero] at hz
  rw [← Finset.sum_filter] at hz
  exact hz

/-- **Determinism $\iff$ the total multiplicity on each label is zero** (when every label
occurs).

$\Leftarrow$: a fault-free outcome pattern is constant on labels, that is some
$x\circ\mathrm{lab}$, and grouping by label gives it; $\Rightarrow$ is the previous item. -/
theorem isDeterministic_iff {S L : Type*} [Fintype S] [Fintype L] [DecidableEq L]
    {lab : S → L} (hlab : Function.Surjective lab) (D : Form S) :
    IsDeterministic lab D
      ↔ ∀ c : L, ∑ s ∈ Finset.univ.filter (fun s => lab s = c), D s = 0 := by
  classical
  constructor
  · intro h c
    exact classSum_zero_of_isDeterministic h c
  · intro h o ho
    -- pick one representative per label, writing `o` as `x ∘ lab`
    set x : L → ZMod 2 := fun c => o (Classical.choose (hlab c)) with hx
    have hxo : ∀ s : S, o s = x (lab s) := by
      intro s
      have hspec : lab (Classical.choose (hlab (lab s))) = lab s := Classical.choose_spec (hlab (lab s))
      exact ho s (Classical.choose (hlab (lab s))) hspec.symm
    calc ∑ s, D s * o s
        = ∑ s, D s * x (lab s) := Finset.sum_congr rfl fun s _ => by rw [hxo s]
      _ = ∑ s, ∑ c : L, (if lab s = c then D s * x c else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_eq_single (lab s)
            (fun c _ hc => by rw [ite_eq_right (fun hh : lab s = c => hc hh.symm)])
            (fun h => absurd (Finset.mem_univ (lab s)) h)]
          exact (ite_eq_left rfl).symm
      _ = ∑ c : L, ∑ s, (if lab s = c then D s * x c else 0) := Finset.sum_comm
      _ = 0 := by
          refine Finset.sum_eq_zero fun c _ => ?_
          rw [← Finset.sum_filter]
          rw [← Finset.sum_mul, h c, zero_mul]

/-- **The pair form is deterministic**: two sites with the same label give the same
result, so their sum reads out zero on any outcome pattern. -/
theorem isDeterministic_pairForm {S L : Type*} [Fintype S] [DecidableEq S] [DecidableEq L]
    {lab : S → L} {a b : S} (h : lab a = lab b) : IsDeterministic lab (pairForm a b) := by
  classical
  intro o ho
  have hsingle_a : (∑ s, ((Pi.single a (1 : ZMod 2) : Form S)) s * o s) = o a := by
    rw [Finset.sum_eq_single a
      (fun s _ hs => by rw [Pi.single_apply, ite_eq_right hs, zero_mul])
      (fun hh => absurd (Finset.mem_univ a) hh)]
    rw [Pi.single_eq_same, one_mul]
  have hsingle_b : (∑ s, ((Pi.single b (1 : ZMod 2) : Form S)) s * o s) = o b := by
    rw [Finset.sum_eq_single b
      (fun s _ hs => by rw [Pi.single_apply, ite_eq_right hs, zero_mul])
      (fun hh => absurd (Finset.mem_univ b) hh)]
    rw [Pi.single_eq_same, one_mul]
  calc ∑ s, pairForm a b s * o s
      = (∑ s, ((Pi.single a (1 : ZMod 2) : Form S)) s * o s)
          + (∑ s, ((Pi.single b (1 : ZMod 2) : Form S)) s * o s) := by
        rw [pairForm, unitForm, unitForm]
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    _ = o a + o b := by rw [hsingle_a, hsingle_b]
    _ = 0 := by rw [ho a b h]; exact CharTwo.add_self_eq_zero (o b)

/-- A form whose support lies in `κ` and whose total multiplicity on `κ` is zero is a sum
of pair forms inside `κ`.

Strong induction on the support size: take a nonzero site $a$; total multiplicity zero
says there is a nonzero $b$ among the remaining sites (otherwise the remaining sum is zero
while $f\,a\ne0$); subtract this pair and the support loses two sites. -/
theorem mem_span_pairForm_of_sum_eq_zero {S : Type*} [DecidableEq S] (κ : Finset S)
    (f : Form S) (hsup : ∀ s, f s ≠ 0 → s ∈ κ) (hsum : ∑ s ∈ κ, f s = 0) :
    f ∈ Submodule.span (ZMod 2)
      {v : Form S | ∃ a ∈ κ, ∃ b ∈ κ, v = pairForm a b} := by
  classical
  have key : ∀ n : ℕ, ∀ f : Form S, (κ.filter (fun s => f s ≠ 0)).card = n →
      (∀ s, f s ≠ 0 → s ∈ κ) → (∑ s ∈ κ, f s = 0) →
      f ∈ Submodule.span (ZMod 2) {v : Form S | ∃ a ∈ κ, ∃ b ∈ κ, v = pairForm a b} := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hcard hsup hsum
      by_cases hempty : κ.filter (fun s => f s ≠ 0) = ∅
      · have hzero : f = 0 := by
          funext s
          by_contra hs
          have : s ∈ κ.filter (fun s => f s ≠ 0) := Finset.mem_filter.mpr ⟨hsup s hs, hs⟩
          rw [hempty] at this
          exact absurd this (Finset.notMem_empty s)
        rw [hzero]
        exact Submodule.zero_mem _
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨haκ, haf⟩ := Finset.mem_filter.mp ha
        have hne : (κ.erase a).filter (fun s => f s ≠ 0) ≠ ∅ := by
          intro hcon
          have hzero : (∑ s ∈ κ.erase a, f s) = 0 := by
            refine Finset.sum_eq_zero fun s hs => ?_
            by_contra hs0
            have : s ∈ (κ.erase a).filter (fun s => f s ≠ 0) := Finset.mem_filter.mpr ⟨hs, hs0⟩
            rw [hcon] at this
            exact absurd this (Finset.notMem_empty s)
          have h1 : f a + (∑ s ∈ κ.erase a, f s) = 0 := by
            rw [Finset.add_sum_erase κ f haκ, hsum]
          rw [hzero, add_zero] at h1
          exact haf h1
        obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hbkerase, hbf⟩ := Finset.mem_filter.mp hb
        obtain ⟨hba, hbκ⟩ := Finset.mem_erase.mp hbkerase
        have hnewsup : ∀ s, (f + pairForm a b) s ≠ 0 → s ∈ κ := by
          intro s hs
          by_contra hsc
          have hs1 : f s = 0 := by
            by_contra h
            exact hsc (hsup s h)
          have hs2 : pairForm a b s = 0 := by
            rw [pairForm, Pi.add_apply, unitForm, unitForm, Pi.single_apply, Pi.single_apply,
              ite_eq_right (fun h : s = a => hsc (h ▸ haκ)),
              ite_eq_right (fun h : s = b => hsc (h ▸ hbκ)), add_zero]
          rw [Pi.add_apply, hs1, hs2, add_zero] at hs
          exact hs rfl
        have hnewsum : (∑ s ∈ κ, (f + pairForm a b) s) = 0 := by
          have ha' : (∑ s ∈ κ, unitForm a s) = 1 := by
            rw [Finset.sum_eq_single a
              (fun x _ hx => by rw [unitForm, Pi.single_apply, ite_eq_right hx])
              (fun h => absurd haκ h)]
            rw [unitForm, Pi.single_eq_same]
          have hb' : (∑ s ∈ κ, unitForm b s) = 1 := by
            rw [Finset.sum_eq_single b
              (fun x _ hx => by rw [unitForm, Pi.single_apply, ite_eq_right hx])
              (fun h => absurd hbκ h)]
            rw [unitForm, Pi.single_eq_same]
          simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib, hsum, zero_add]
          simp only [pairForm, Pi.add_apply]
          rw [Finset.sum_add_distrib, ha', hb', CharTwo.add_self_eq_zero]

        have hcardlt : (κ.filter (fun s => (f + pairForm a b) s ≠ 0)).card < n := by
          rw [← hcard]
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
          · intro s hs
            rw [Finset.mem_filter] at hs ⊢
            refine ⟨hs.1, ?_⟩
            by_contra hfs
            have h1 : f s = 0 := by simpa using hfs
            have h2 : pairForm a b s ≠ 0 := by
              rw [Pi.add_apply, h1, zero_add] at hs
              exact hs.2
            have h3 : s = a ∨ s = b := by
              by_contra hcon
              rw [not_or] at hcon
              exact h2 (by
                rw [pairForm, Pi.add_apply, unitForm, unitForm, Pi.single_apply, Pi.single_apply,
                  ite_eq_right (fun h : s = a => hcon.1 h),
                  ite_eq_right (fun h : s = b => hcon.2 h), add_zero])
            rcases h3 with rfl | rfl
            · exact haf h1
            · exact hbf h1
          · intro heq
            have hold : a ∈ κ.filter (fun s => f s ≠ 0) := Finset.mem_filter.mpr ⟨haκ, haf⟩
            have hnotnew : a ∉ κ.filter (fun s => (f + pairForm a b) s ≠ 0) := by
              rw [Finset.mem_filter]
              rintro ⟨_, hne'⟩
              refine hne' ?_
              rw [Pi.add_apply, pairForm, Pi.add_apply, unitForm, unitForm,
                Pi.single_eq_same, Pi.single_apply, ite_eq_right (fun h : a = b => hba h.symm),
                add_zero, eq_one_of_ne_zero haf, CharTwo.add_self_eq_zero]
            rw [← heq] at hold
            exact hnotnew hold
        have hspan := ih _ hcardlt (f + pairForm a b) rfl hnewsup hnewsum
        have hpair : pairForm a b ∈ Submodule.span (ZMod 2)
            {v : Form S | ∃ a ∈ κ, ∃ b ∈ κ, v = pairForm a b} :=
          Submodule.subset_span ⟨a, haκ, b, hbκ, rfl⟩
        have hrecon : f = (f + pairForm a b) + pairForm a b := by
          rw [eq_comm, add_assoc, form_add_self, add_zero]
        rw [hrecon]
        exact Submodule.add_mem _ hspan hpair
  exact key (κ.filter (fun s => f s ≠ 0)).card f rfl hsup hsum

/-- The **submodule** of deterministic forms (closed under addition and scalar
multiplication). -/
def detSubmodule {S L : Type*} [Fintype S] [DecidableEq L] (lab : S → L) :
    Submodule (ZMod 2) (Form S) where
  carrier := {D | IsDeterministic lab D}
  zero_mem' := isDeterministic_zero lab
  add_mem' := fun h h' => isDeterministic_add h h'
  smul_mem' := by
    intro a D hD o ho
    have hpt : ∀ s, (a • D) s * o s = a * (D s * o s) := by
      intro s
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun s _ => hpt s, ← Finset.mul_sum, hD o ho, mul_zero]

/-- A form is the sum of its class slices, $\sum_c \mathbf 1_{\{\mathrm{lab} = c\}} D$.
Both directions of the two generating-set theorems below start from this decomposition, so
it is one lemma rather than a block copied into each. -/
private lemma eq_sum_classSlices {S L : Type*} [Fintype L] [DecidableEq L]
    (lab : S → L) (D : Form S) :
    D = ∑ c : L, fun s => if lab s = c then D s else 0 := by
  funext s
  rw [Finset.sum_apply, Finset.sum_eq_single (lab s)]
  · exact (ite_eq_left rfl).symm
  · intro c _ hc
    rw [ite_eq_right (fun hh : lab s = c => hc hh.symm)]
  · intro h
    exact absurd (Finset.mem_univ (lab s)) h

/-- **Lemma 1 (middle segment)**: every deterministic form is exactly a linear
combination of **pairs with the same operator**.

A pair of the same operator in two adjacent rounds is an adjacent-round comparison, and
the telescoping sum of the previous section reduces the cross-round ones to adjacent ones;
"no local detectors" (C4) here is no linear dependence within a round, so the generating
set agrees with the one listed in the original. -/
theorem isDeterministic_iff_mem_span_pairForm {S L : Type*} [Fintype S] [Fintype L]
    [DecidableEq S] [DecidableEq L] (lab : S → L) (D : Form S) :
    IsDeterministic lab D ↔
      D ∈ Submodule.span (ZMod 2)
        {v : Form S | ∃ a b, lab a = lab b ∧ v = pairForm a b} := by
  classical
  constructor
  · intro hD
    have hcls : ∀ c : L, (∑ s ∈ Finset.univ.filter fun s => lab s = c, D s) = 0 :=
      fun c => classSum_zero_of_isDeterministic hD c
    have hdecomp : D = ∑ c : L, fun s => if lab s = c then D s else 0 :=
      eq_sum_classSlices lab D
    rw [hdecomp]
    refine Submodule.sum_mem _ fun c _ => ?_
    refine Submodule.span_mono ?_ (mem_span_pairForm_of_sum_eq_zero
      (Finset.univ.filter fun s => lab s = c) (fun s => if lab s = c then D s else 0) ?_ ?_)
    · rintro v ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, b, by rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2], rfl⟩
    · intro s hs
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ s, ?_⟩
      by_contra hsc
      rw [ite_eq_right hsc] at hs
      exact hs rfl
    · refine Eq.trans ?_ (hcls c)
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [ite_eq_left (Finset.mem_filter.mp hs).2]
  · intro hD
    have hsub : {v : Form S | ∃ a b, lab a = lab b ∧ v = pairForm a b} ⊆ (detSubmodule lab : Set _) := by
      rintro v ⟨a, b, hab, rfl⟩
      exact isDeterministic_pairForm hab
    exact Submodule.span_le.mpr hsub hD

/-! ## 4. Lemma 2: the spacetime stabilizers in the same model

Lemma 2 lists a generating set of the **spacetime stabilizers** (Definition 2 of the
original: the fault sets that violate no detector and change no readout). In the result
model it is shorter than Lemma 1, because **faults and detectors live in the same space**:
a form can be read either as "which sites are counted into a detector" or as "which sites
are flipped by a fault", and pairing the two is $\sum_s D_sF_s$. Lemma 1 has already
pinned the **detectors** down to the forms "total multiplicity zero on each operator
label", so taking the orthogonal complement gives

* **the dual** (`stabilizer_iff_const_on_labels`): a fault is seen by no detector $\iff$
  it is **constant on each operator label** -- "the same fault repeating in every round"
  is exactly the family the original lists;
* **the generating set** (`const_on_labels_iff_mem_span_classInd`): these faults are
  exactly the linear combinations of the **indicator forms of the individual label
  classes**.

Here C4 plays the same role as in Lemma 1 (two faces of the same theorem). The "changes no
readout" half in Definition 2 of the original adds one more orthogonality condition, on
the readout form, which this module does not touch; the initialization / readout of the
two ends is the same. -/

/-- **Pairing a detector with a fault**: whether the form $D$ is seen by the fault $F$
($=1$ means seen). This is mathlib's `Matrix.dotProduct` on `Form S`, which is the GF(2)
pairing the package uses throughout, so the dot-product lemmas of
`QECCertificates.GF2.Basis` apply to it directly. -/
def sees {S : Type*} [Fintype S] (D F : Form S) : ZMod 2 := D ⬝ᵥ F

/-- **The indicator form of a label class**: all the sites of one operator. -/
def classInd {S L : Type*} [DecidableEq L] (lab : S → L) (c : L) : Form S :=
  fun s => if lab s = c then 1 else 0

/-- A class indicator form is constant on labels -- so it is a stabilizer (see the next
item). -/
theorem classInd_const {S L : Type*} [DecidableEq L] {lab : S → L} (c : L) :
    ∀ a b : S, lab a = lab b → classInd lab c a = classInd lab c b := by
  intro a b hab
  simp only [classInd]
  rw [hab]

/-- **The readout of a pair form**: $\langle e_a+e_b, F\rangle = F_a+F_b$. -/
theorem sees_pairForm {S : Type*} [Fintype S] [DecidableEq S] (a b : S) (F : Form S) :
    sees (pairForm a b) F = F a + F b := by
  rw [sees, pairForm, unitForm, unitForm, add_dotProduct, single_dotProduct,
    single_dotProduct, one_mul, one_mul]

/-- The submodule of forms not seen by `F`. -/
def zeroSeen {S : Type*} [Fintype S] (F : Form S) : Submodule (ZMod 2) (Form S) where
  carrier := {D | sees D F = 0}
  zero_mem' := by simp [sees]
  add_mem' := by
    intro x y hx hy
    have hx' : sees x F = 0 := hx
    have hy' : sees y F = 0 := hy
    show sees (x + y) F = 0
    rw [sees] at hx' hy' ⊢
    rw [add_dotProduct, hx', hy', add_zero]
  smul_mem' := by
    intro a x hx
    have hx' : sees x F = 0 := hx
    show sees (a • x) F = 0
    rw [sees] at hx' ⊢
    rw [smul_dotProduct, hx', smul_zero]

/-- The submodule of forms constant on each label. -/
def constSubmodule {S L : Type*} [DecidableEq L] (lab : S → L) :
    Submodule (ZMod 2) (Form S) where
  carrier := {F | ∀ a b, lab a = lab b → F a = F b}
  zero_mem' := by intro a b _; simp
  add_mem' := by
    intro x y hx hy a b hab
    simp only [Pi.add_apply, hx a b hab, hy a b hab]
  smul_mem' := by
    intro c x hx a b hab
    simp only [Pi.smul_apply, hx a b hab]

/-- **Lemma 2 (result model)**: under C4, a fault is seen by no detector $\iff$ it is
constant on each label. -/
theorem stabilizer_iff_const_on_labels {S L : Type*} [Fintype S] [Fintype L]
    [DecidableEq S] [DecidableEq L] (lab : S → L) (F : Form S) :
    (∀ D, IsDeterministic lab D → sees D F = 0) ↔ ∀ a b, lab a = lab b → F a = F b := by
  constructor
  · intro h a b hab
    have hz := h _ (isDeterministic_pairForm hab)
    rw [sees_pairForm] at hz
    exact (add_eq_zero_iff_eq (F a) (F b)).mp hz
  · intro hF D hD
    have hmem := (isDeterministic_iff_mem_span_pairForm lab D).mp hD
    have hsub : {v : Form S | ∃ a b, lab a = lab b ∧ v = pairForm a b}
        ⊆ (zeroSeen F : Set (Form S)) := by
      rintro v ⟨a, b, hab, rfl⟩
      show sees (pairForm a b) F = 0
      rw [sees_pairForm, hF a b hab]
      exact CharTwo.add_self_eq_zero _
    exact Submodule.span_le.mpr hsub hmem

/-- **The generating set of Lemma 2**: the faults constant on labels are exactly the
linear combinations of the label-class indicator forms. -/
theorem const_on_labels_iff_mem_span_classInd {S L : Type*} [Fintype S] [Fintype L]
    [DecidableEq L] (lab : S → L) (hlab : Function.Surjective lab) (F : Form S) :
    (∀ a b, lab a = lab b → F a = F b) ↔
      F ∈ Submodule.span (ZMod 2) {v : Form S | ∃ c : L, v = classInd lab c} := by
  classical
  constructor
  · intro hF
    have hdecomp : F = ∑ c : L, F (Classical.choose (hlab c)) • classInd lab c := by
      funext s
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single (lab s)]
      · rw [Pi.smul_apply, smul_eq_mul]
        have hspec : lab (Classical.choose (hlab (lab s))) = lab s :=
          Classical.choose_spec (hlab (lab s))
        rw [classInd, ite_eq_left rfl, mul_one]
        exact hF s (Classical.choose (hlab (lab s))) hspec.symm
      · intro c _ hc
        have hne : ¬ (lab s = c) := fun hh => hc hh.symm
        rw [Pi.smul_apply, classInd, ite_eq_right hne, smul_zero]
      · intro hh
        exact absurd (Finset.mem_univ (lab s)) hh
    rw [hdecomp]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · intro hF a b hab
    have hsub : {v : Form S | ∃ c : L, v = classInd lab c}
        ⊆ (constSubmodule lab : Set (Form S)) := by
      rintro v ⟨c, rfl⟩
      exact classInd_const c
    exact Submodule.span_le.mpr hsub hF a b hab

/-! ## 5. The two ends: the state is "reset" by the deformation, so the result need not
repeat

The key fact of the middle segment is "the same operator keeps giving the same result".
**It fails at the two ends**: the deformation changes the state, and the result of the
same operator before and after the deformation can differ. In the result model this is
written out as

* labels are taken **per segment** -- the same operator repeats within a segment, not
  across segments (the pre-deformation $s_j$ and the post-deformation $\tilde s_j$ are
  then two labels, which the `lab` of this module already allows);
* the **initialization and readout** sites are recorded separately as the site set `Z` on
  which "the result is pinned at zero" -- initialization to $|0\rangle$, readout to a
  known eigenvalue, both ends have this shape.

The criterion then becomes: **the label classes not touching `Z` must still have total
multiplicity zero**; **the classes touching `Z` are no longer restricted**, because in
such a class "the result of the whole class" is not free -- that one site in `Z` pins it
down -- and a single site becomes a deterministic form by itself. This is exactly why the
original lists **extra generators** for the two ends:

$$\text{detector} \;=\; \langle\text{pairs of the same operator}\rangle
  \;+\; \langle\text{singletons on the pinned sites}\rangle .$$

Taking `Z` empty, this section falls back to the theorem of section 4, so this section is
its strict generalization. -/

/-- A deterministic form under the **pinned site set** `Z`: one condition fewer than
`IsDeterministic` (the outcome pattern must also vanish on `Z`). -/
def IsDetZ {S L : Type*} [Fintype S] [DecidableEq L] (lab : S → L) (Z : Finset S)
    (D : Form S) : Prop :=
  ∀ o : Form S, (∀ a b, lab a = lab b → o a = o b) → (∀ s ∈ Z, o s = 0) →
    ∑ s, D s * o s = 0

/-- The forms satisfying `IsDetZ` form a submodule (the criterion is linear in `D`). -/
def detZSubmodule {S L : Type*} [Fintype S] [DecidableEq L] (lab : S → L) (Z : Finset S) :
    Submodule (ZMod 2) (Form S) where
  carrier := {D | IsDetZ lab Z D}
  zero_mem' := by intro o _ _; simp
  add_mem' := by
    intro x y hx hy o ho hz
    have hx' : IsDetZ lab Z x := hx
    have hy' : IsDetZ lab Z y := hy
    have hxy : ∑ s, (x + y) s * o s = (∑ s, x s * o s) + (∑ s, y s * o s) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply, add_mul]
    rw [hxy, hx' o ho hz, hy' o ho hz, add_zero]
  smul_mem' := by
    intro a x hx o ho hz
    have hx' : IsDetZ lab Z x := hx
    have hfac : ∑ s, (a • x) s * o s = a * ∑ s, x s * o s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfac, hx' o ho hz, mul_zero]

/-- **The criterion**: on the label classes not touching `Z`, the total multiplicity must
still be zero -- while the **classes touching `Z` are unrestricted**.

Take the indicator form of the class as the outcome pattern: the class has no site in
`Z`, so it satisfies the pinned condition, and the criterion reads off the total
multiplicity of the class. -/
theorem classSum_zero_of_isDetZ {S L : Type*} [Fintype S] [DecidableEq L]
    {lab : S → L} {Z : Finset S} {D : Form S} (h : IsDetZ lab Z D) {c : L}
    (hc : ∀ s, lab s = c → s ∉ Z) :
    ∑ s ∈ Finset.univ.filter (fun s => lab s = c), D s = 0 := by
  classical
  have hconst : ∀ a b : S, lab a = lab b →
      (fun s => if lab s = c then (1 : ZMod 2) else 0) a
        = (fun s => if lab s = c then (1 : ZMod 2) else 0) b := by
    intro a b hab
    simp only
    rw [hab]
  have hzero : ∀ s ∈ Z, (fun s => if lab s = c then (1 : ZMod 2) else 0) s = 0 := by
    intro s hs
    simp only
    rw [ite_eq_right (fun hh : lab s = c => hc s hh hs)]
  have hz := h _ hconst hzero
  simp only [mul_ite, mul_one, mul_zero] at hz
  rw [← Finset.sum_filter] at hz
  exact hz

/-- **The generating set (two ends)**: pairs of the same operator, **plus** singletons on
the pinned sites.

$\Rightarrow$: split by label class. A class not touching `Z` has total multiplicity zero
by the criterion, hence is a sum of pairs inside the class; a class touching `Z` (taking
$a\in Z$ in the class) has its total multiplicity pulled out as $\sigma\cdot e_a$, and the
remainder lies inside the class with total multiplicity zero, still a sum of pairs.
$\Leftarrow$: both families of generators are deterministic -- the pairs because the same
operator gives the same result, the singletons because the result is pinned at zero on
`Z`. -/
theorem isDetZ_iff_mem_span {S L : Type*} [Fintype S] [Fintype L]
    [DecidableEq S] [DecidableEq L] (lab : S → L) (Z : Finset S) (D : Form S) :
    IsDetZ lab Z D ↔
      D ∈ Submodule.span (ZMod 2) {v : Form S |
        (∃ a b, lab a = lab b ∧ v = pairForm a b) ∨ (∃ a ∈ Z, v = unitForm a)} := by
  classical
  constructor
  · intro hD
    have hdecomp : D = ∑ c : L, fun s => if lab s = c then D s else 0 :=
      eq_sum_classSlices lab D
    rw [hdecomp]
    refine Submodule.sum_mem _ fun c _ => ?_
    set Dc : Form S := (fun s => if lab s = c then D s else 0) with hDc
    have hmono : ∀ f : Form S,
        f ∈ Submodule.span (ZMod 2) {v : Form S |
          ∃ a ∈ Finset.univ.filter (fun s => lab s = c),
            ∃ b ∈ Finset.univ.filter (fun s => lab s = c), v = pairForm a b} →
        f ∈ Submodule.span (ZMod 2) {v : Form S |
          (∃ a b, lab a = lab b ∧ v = pairForm a b) ∨ (∃ a ∈ Z, v = unitForm a)} := by
      intro f hf
      refine Submodule.span_mono ?_ hf
      rintro v ⟨a', ha', b', hb', rfl⟩
      exact Or.inl ⟨a', b',
        by rw [(Finset.mem_filter.mp ha').2, (Finset.mem_filter.mp hb').2], rfl⟩
    by_cases hZc : ∃ a ∈ Z, lab a = c
    · obtain ⟨a, haZ, hac⟩ := hZc
      set σ : ZMod 2 := ∑ s ∈ Finset.univ.filter (fun s => lab s = c), D s with hσ
      set R : Form S := Dc - σ • unitForm a with hR
      have hsum : Dc = σ • unitForm a + R := by
        rw [hR]
        exact (add_sub_cancel _ _).symm
      rw [hsum]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨a, haZ, rfl⟩))
      · refine hmono R (mem_span_pairForm_of_sum_eq_zero
          (Finset.univ.filter fun s => lab s = c) R ?_ ?_)
        · intro s hs
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ s, ?_⟩
          by_contra hsc
          exact hs (by
            have hsa : s ≠ a := fun h => hsc (h ▸ hac)
            rw [hR, hDc]
            simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitForm, hsc, hsa])
        · have e1 : ∀ s, R s = (if lab s = c then D s else 0) - σ * unitForm a s := by
            intro s
            rw [hR, hDc]
            simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have hunit : ∑ s ∈ Finset.univ.filter (fun s => lab s = c), unitForm a s = 1 := by
            rw [Finset.sum_eq_single a
              (fun t _ hta => by rw [unitForm, Pi.single_apply, ite_eq_right hta])
              (fun h => (h (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hac⟩)).elim)]
            rw [unitForm, Pi.single_eq_same]
          rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_sub_distrib]
          have h1 : ∑ s ∈ Finset.univ.filter (fun s => lab s = c),
              (if lab s = c then D s else 0) = σ := by
            rw [hσ]
            exact Finset.sum_congr rfl fun s hs => ite_eq_left (Finset.mem_filter.mp hs).2
          have h2 : ∑ s ∈ Finset.univ.filter (fun s => lab s = c), σ * unitForm a s = σ * 1 := by
            rw [← Finset.mul_sum, hunit]
          rw [h1, h2, mul_one, sub_self]
    · have hsumD : (∑ s ∈ Finset.univ.filter (fun s => lab s = c), D s) = 0 :=
        classSum_zero_of_isDetZ hD (fun s hs => fun hsz => hZc ⟨s, hsz, hs⟩)
      refine hmono Dc (mem_span_pairForm_of_sum_eq_zero
        (Finset.univ.filter fun s => lab s = c) Dc ?_ ?_)
      · intro s hs
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ s, ?_⟩
        by_contra hsc
        exact hs (by rw [hDc]; simp [hsc])
      · refine Eq.trans ?_ hsumD
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [hDc]
        exact ite_eq_left (Finset.mem_filter.mp hs).2
  · intro hD
    have hsub : {v : Form S |
        (∃ a b, lab a = lab b ∧ v = pairForm a b) ∨ (∃ a ∈ Z, v = unitForm a)}
        ⊆ (detZSubmodule lab Z : Set (Form S)) := by
      rintro v (⟨a, b, hab, rfl⟩ | ⟨a, haZ, rfl⟩)
      · show IsDetZ lab Z (pairForm a b)
        intro o ho _
        show sees (pairForm a b) o = 0
        rw [sees_pairForm, ho a b hab]
        exact CharTwo.add_self_eq_zero (o b)
      · show IsDetZ lab Z (unitForm a)
        intro o _ hz
        show sees (unitForm a) o = 0
        rw [sees, unitForm, single_dotProduct, one_mul]
        exact hz a haZ
    exact Submodule.span_le.mpr hsub hD

end QECCertificates.Homology
