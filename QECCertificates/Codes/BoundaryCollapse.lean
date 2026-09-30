/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.Basic

/-!
# Removing the boundary detectors collapses the distance to $1$ for **any** code (family-level form)

The C3 case in Section V of the companion paper is an **instance** (Bacon–Shor, $20$ slots). This
module lifts it to the **family level**: **the mechanism never looks at the code**. A single data
fault placed in round $0$ **persists** through every later round, so the syndrome is the same in
every round and every comparison of adjacent rounds is silent; once the boundary detectors are
removed nothing can see the fault any more, and the readout is $1$ in **every** round.

The model is the **comparison-layer abstraction** of the full protocol model: $T+1$ rounds, one
data-fault vector per round, an arbitrary parity-check matrix, an arbitrary readout functional, and
detectors that only compare **adjacent rounds** (the boundary detectors are exactly the ones
removed).

**Main theorem**: `boundaryRemoved_distance_eq_one`. For **any** `n`, any parity-check matrix `H`,
any readout `w` and any number of rounds `T`, a fault that both keeps every comparison silent and
reads out as $1$ in every round has minimum spacetime weight **exactly $1$**.

The matrix `H` is never actually used in the proof, and that is what makes the conclusion strong:
**the collapse is independent of the code**, since it follows from the modelling fact that a fault
may persist. C1 and C2 are therefore properties of the code; C3 is not.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {n m : ℕ}

/-- Round-by-round fault: `T + 1` rounds, one data-fault vector per round. -/
abbrev RoundFault (T n : ℕ) := Fin (T + 1) → Vec n

/-- **Cumulative fault**: the error still attached to the data at the end of round `t`, namely the
faults of every round `s ≤ t`. -/
def cum {T n : ℕ} (f : RoundFault T n) (t : Fin (T + 1)) : Vec n :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin (T + 1) => s ≤ t), f s

/-- Spacetime weight: the sum of the per-round weights, counting each fault location once. -/
def faultWeight {T n : ℕ} (f : RoundFault T n) : ℕ := ∑ t, hammingNorm (f t)

/-- **Comparison-silent**: every pair of adjacent rounds has the same syndrome. -/
def ComparisonsSilent {T n m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (f : RoundFault T n) : Prop :=
  ∀ t : Fin T, H *ᵥ cum f t.castSucc = H *ᵥ cum f t.succ

/-- Readout in round `t`: the readout functional applied to the **cumulative** fault. -/
def readout {T n : ℕ} (w : Vec n) (f : RoundFault T n) (t : Fin (T + 1)) : ZMod 2 :=
  w ⬝ᵥ cum f t

/-- Witness: a single `e j` in round $0$ and zero in every other round. -/
def witFault {T n : ℕ} (j : Fin n) : RoundFault T n :=
  fun t => if t = 0 then e j else 0

/-! ## 1. Two basis-vector lemmas -/

/-- The support of `e j` is exactly the singleton. -/
lemma support_e {n : ℕ} (j : Fin n) : support (e j) = {j} := by
  ext i
  simp [support, e]

/-- The weight of `e j` is $1$. -/
lemma hammingNorm_e {n : ℕ} (j : Fin n) : hammingNorm (e j) = 1 := by
  rw [← weight_eq_hammingNorm, support_e]
  simp

/-! ## 2. Three readouts of the witness -/

/-- The cumulative fault of the witness is always `e j`: the fault is placed in round $0$ and
**stays there** afterwards. -/
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

/-- `w ⬝ᵥ e j = w j`. -/
lemma dot_e {n : ℕ} (w : Vec n) (j : Fin n) : w ⬝ᵥ e j = w j := by
  classical
  rw [dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [e]
  · intro b _ hb
    simp [e, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The witness keeps the comparison of adjacent rounds silent for **any** parity-check matrix: the
syndrome is the same in every round. -/
theorem comparisonsSilent_witFault {T : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (j : Fin n) : ComparisonsSilent H (witFault (T := T) j) := by
  intro t
  rw [cum_witFault, cum_witFault]

/-- The witness reads out as `w j` in **every** round. -/
lemma readout_witFault {T : ℕ} (w : Vec n) (j : Fin n) (t : Fin (T + 1)) :
    readout w (witFault (T := T) j) t = w j := by
  unfold readout
  rw [cum_witFault, dot_e]

/-- The spacetime weight of the witness is exactly $1$: a single nonzero entry, in round $0$. -/
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

/-! ## 3. Upper bound: the witness

**Whenever the readout functional reads $1$ somewhere, the witness sits there.** It need not be a
logical operator, and no assumption about the code distance is required (`H` does not appear at
all). -/

/-- **Upper bound (family level)**: for any nonzero readout, any parity-check matrix and any number
of rounds, there is a comparison-silent fault of weight exactly $1$ whose readout is $1$ in every
round. -/
theorem boundaryRemoved_witness {T : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) (j : Fin n) (hj : w j = 1) :
    ∃ f : RoundFault T n, ComparisonsSilent H f ∧ (∀ t, readout w f t = 1) ∧
      faultWeight f = 1 :=
  ⟨witFault j, comparisonsSilent_witFault H j,
   fun _ => by rw [readout_witFault, hj], faultWeight_witFault j⟩

/-! ## 4. Lower bound: the weight cannot be $0$ -/

/-- **Lower bound (family level)**: a fault that reads out as $1$ in every round has weight at least
$1$, since the zero fault reads out as $0$ in every round. -/
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

/-! ## 5. Main theorem -/

/-- **After the boundary detectors are removed, the fault distance is exactly $1$, for any code and
any number of rounds.**

Both directions are given: a witness of weight $1$, and the statement that no fault of weight $0$
qualifies. The minimum is therefore **exactly** $1$, and it is independent of `H`. This is the
difference between C3 and C1, C2: the latter two are properties of the code, whereas C3 follows
from the modelling fact that a fault is read as a cumulative one. -/
theorem boundaryRemoved_distance_eq_one {T : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) (j : Fin n) (hj : w j = 1) :
    (∃ f : RoundFault T n, ComparisonsSilent H f ∧ (∀ t, readout w f t = 1) ∧
        faultWeight f = 1) ∧
      (∀ f : RoundFault T n, ComparisonsSilent H f → (∀ t, readout w f t = 1) →
        1 ≤ faultWeight f) :=
  ⟨boundaryRemoved_witness H w j hj,
   fun _ _ hf => one_le_faultWeight_of_readout hf⟩

end QECCertificates
