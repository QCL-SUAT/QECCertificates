/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.MeasurementProtocol
import QECCertificates.Codes.BaconShor

/-!
# The two components of transversal measurement for Bacon–Shor $[[9,1,3]]$ (kernel-checked instances)

`Codes/BaconShor.lean` gives the **static** structure of this code ($k=1$, $d_X=d_Z=3$),
and `Codes/MeasurementProtocol.lean` gives the representation layer of the **measurement
protocol** (single-round fault patterns, concatenation across rounds, the timelike law
$T\cdot s$). This module joins the two, giving one kernel-checked instance in each of two
coordinate systems.

## The protocol

The bare X-type logical operator is $\bar X = $ all $X$ on a single column (weight $3$,
`bstXW`). It is a **product of single-bit operators**, so it can be **measured
transversally**: measure $X$ once on each bit of the support, and the logical readout is
the product of the three outcomes. The two questions correspond to the two components:

* **Spacelike component.** Within one round the logical readout is only **one classical
  bit**. If only those three bits are measured, no check can detect that one of the
  outcomes is wrong (`bare_noLightFault`: single-round fault distance $=1$). If instead
  the **whole $3\times3$ array** is measured in $X$, the two X-type stabilizers of the
  code (products of adjacent columns, weight $6$) become within-round checks, and the
  single-round fault distance jumps to $3=d$ (Section 1).
* **Timelike component.** When only the support is measured, the sole protection is to
  **repeat and compare the round readouts**. Section 2 evaluates this exactly: the
  spacetime fault distance over $T$ rounds is exactly $T$ (Section 3). Taking $T=d=3$
  gives $\ge d$ for both components.

## Two coordinate systems, one protocol

Section 2 uses **flat coordinates**: the $9$ bits are numbered $3t+i$ (round $t$, support
bit $i$), and the cross-round checks are written as an explicit $2\times9$ parity-check
matrix `bsCrossChecks`, of the same shape as the code instances of
`Codes/CaseMatrix.lean` and directly amenable to `by decide`. Section 4 uses **layered
coordinates** `Fin 3 → Vec 3` and instantiates the timelike law of
`MeasurementProtocol`. The two give the same number $3$, each a check on the other.

## The geometry of the escape patterns

The kernel characterization of Section 1 deserves a word of its own: the fault patterns
that evade both X-type stabilizers are exactly those whose three columns have equal
parity (the spacelike version of `bsCrossChecks_ker_iff`), and the half in which all three
columns are odd is exactly $\text{Z-type bare logical} + \text{Z-type gauge group}$ (an
independent implementation of the same route checks this entry by entry). The minimum
representative is **one full row of $X$** ($=$ the code's Z-type bare logical `bstZW`): on
the spacelike component, the logical-flip fault of a transversal measurement is one of the
code's own logical operators.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. Spacelike component: one round, the whole array measured in X (within-round checks = the X-type stabilizers of the code) -/

/-- **The single-round readout functional of a transversal measurement** (the parity of the
three bits of the logical support).

Three bits, $X$ measured once on each, and the logical readout $=$ the product of the
three outcomes: that is the whole content of a transversal measurement. -/
def bsColumnReadout : Vec 3 := fun _ => 1

/-- The second X-type stabilizer: all $X$ on the adjacent columns $\{1,2\}$ (weight $6$).
The first one is `bstSX` in `Codes/BaconShor.lean` (columns $\{0,1\}$). -/
def bsCol12 : Vec 9 := e 1 + e 2 + e 4 + e 5 + e 7 + e 8

/-- **The within-round checks of a single round**: the two X-type stabilizers that can be
extracted only when the whole array is measured in $X$. -/
def bsStabChecks : Matrix (Fin 2) (Fin 9) (ZMod 2) := Matrix.of ![bstSX, bsCol12]

/-- **Single-round fault distance $=3=d$**: a fault pattern that evades both X-type
stabilizers and flips the logical readout has weight at least $3$.

The certificate is that a weight-bounded enumeration (`faultCand`, $46$ candidates) is
empty, so a single wrong outcome among the three is detected, and flipping the logic
requires an odd number of faults **in every column**. -/
theorem bsSingleRound_noLightFault : NoLightFault bsStabChecks bstXW 3 :=
  noLightFault_of_faultCand_nil bsStabChecks bstXW (by decide)

/-- **Witness**: all $X$ on a single row ($=$ the code's Z-type bare logical `bstZW`)
evades both X-type stabilizers and yet flips the logical readout, with weight exactly $3$.

So the escape pattern is not abstract: it is one of the code's own logical operators,
carried across to the measurement outcomes. -/
theorem bsSingleRound_witness :
    inKerB bsStabChecks bstZW = true ∧ bstXW ⬝ᵥ bstZW = 1 ∧ hammingNorm bstZW = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- **The two-sided bracket for the spacelike component**: the single-round fault distance
is exactly $3$, the lower bound being the statement above and the upper bound the witness
`bstZW`. -/
theorem bsSingleRound_eq_d :
    (NoLightFault bsStabChecks bstXW 3) ∧
      (∃ f : Vec 9, inKerB bsStabChecks f = true ∧ bstXW ⬝ᵥ f = 1 ∧ hammingNorm f = 3) :=
  ⟨bsSingleRound_noLightFault, bstZW, bsSingleRound_witness.1, bsSingleRound_witness.2.1,
    bsSingleRound_witness.2.2⟩

/-! ## 2. Timelike component: only the support measured, repeated over $T$ rounds (flat coordinates, explicit parity-check matrix)

Bits are numbered $3t+i$ (round $t$, support bit $i$, with $t<3$ and $i<3$). A cross-round
check covers all bits of rounds $t$ and $t+1$: the check vanishes exactly when the readouts
of two adjacent rounds agree, so these $2$ checks **say precisely that all round readouts
are equal**. -/

/-- The readout of round $0$ (the indicator vector of that round's three bits). -/
def bsRound0 : Vec 9 := e 0 + e 1 + e 2

/-- The readout of round $1$. -/
def bsRound1 : Vec 9 := e 3 + e 4 + e 5

/-- The readout of round $2$. -/
def bsRound2 : Vec 9 := e 6 + e 7 + e 8

/-- **The cross-round parity-check matrix** ($T=3$): row $0$ covers all bits of rounds
$0,1$ and row $1$ those of rounds $1,2$. -/
def bsCrossChecks : Matrix (Fin 2) (Fin 9) (ZMod 2) :=
  Matrix.of ![
    e 0 + e 1 + e 2 + e 3 + e 4 + e 5,
    e 3 + e 4 + e 5 + e 6 + e 7 + e 8
  ]

/-- **Kernel characterization of the cross-round checks**: all checks vanish $\iff$ the
three round readouts agree, which is the entire content of the cross-round comparison. -/
theorem bsCrossChecks_ker_iff :
    ∀ f : Vec 9, inKerB bsCrossChecks f = true ↔
      (bsRound0 ⬝ᵥ f = bsRound1 ⬝ᵥ f ∧ bsRound1 ⬝ᵥ f = bsRound2 ⬝ᵥ f) := by
  decide

/-- **Witness**: the outcome of the **same** bit is reported wrongly in every round (weight
$3=T$). The three round readouts flip consistently, so the cross-round comparison sees
nothing wrong. -/
def bsMeasureW : Vec 9 := e 0 + e 3 + e 6

/-- The three witness facts: in the kernel of the checks (all three round readouts agree
and all are $1$), the logical readout is flipped, and the weight is $=3=T$. -/
theorem bsMeasureW_witness :
    inKerB bsCrossChecks bsMeasureW = true ∧ bsRound0 ⬝ᵥ bsMeasureW = 1 ∧
      hammingNorm bsMeasureW = 3 :=
  ⟨by decide, by decide, by decide⟩

/-- **Timelike component $=3=T=d$ (lower bound)**: a fault pattern that evades the
cross-round checks and flips the logical readout has weight at least $3$.

That is, each of the three rounds must carry its own undetectable flip: one round
differing from the others is exposed. -/
theorem bsMeasure_noLightFault : NoLightFault bsCrossChecks bsRound0 3 :=
  noLightFault_of_faultCand_nil bsCrossChecks bsRound0 (by decide)

/-- **The two-sided bracket for the timelike component**: for a transversal measurement
over $T=3$ rounds the spacetime fault distance is exactly $3$, the lower bound being
`bsMeasure_noLightFault` and the upper bound the witness `bsMeasureW`. With $T=d=3$ both
components are $\ge d$. -/
theorem bsMeasure_eq_T :
    (NoLightFault bsCrossChecks bsRound0 3) ∧
      (∃ f : Vec 9, inKerB bsCrossChecks f = true ∧ bsRound0 ⬝ᵥ f = 1 ∧ hammingNorm f = 3) :=
  ⟨bsMeasure_noLightFault, bsMeasureW, bsMeasureW_witness.1, bsMeasureW_witness.2.1,
    bsMeasureW_witness.2.2⟩

/-! ## 3. Sharpness of C2: at $T=2$ the distance is only $2<d$

A round count $\ge d$ is not a loose sufficient condition but **exactly** the threshold:
at $T=2$ the same protocol, by the same construction, gives the distance $2<3=d$, so the
converse direction holds as well. -/

/-- The cross-round parity-check matrix for $T=2$: one row, covering the bits of the two
rounds. -/
def bsCrossChecks2 : Matrix (Fin 1) (Fin 6) (ZMod 2) :=
  Matrix.of (fun _ => (e 0 + e 1 + e 2 + e 3 + e 4 + e 5 : Vec 6))

/-- The readout of round $0$ when $T=2$. -/
def bsRound0of2 : Vec 6 := e 0 + e 1 + e 2

/-- **Fault distance $=2$ when $T=2$** (lower bound). -/
theorem bsMeasure2_noLightFault : NoLightFault bsCrossChecks2 bsRound0of2 2 :=
  noLightFault_of_faultCand_nil bsCrossChecks2 bsRound0of2 (by decide)

/-- **Sharpness of C2**: the same protocol at $T=2$ admits an undetectable logical fault of
weight exactly $2$, and $2<3=d$. So the implication from a round count $<d$ to a timelike
component $<d$ has an **explicit witness** here, not merely a lower bound. -/
theorem bsMeasure2_lt_d :
    ∃ f : Vec 6, inKerB bsCrossChecks2 f = true ∧ bsRound0of2 ⬝ᵥ f = 1 ∧
      hammingNorm f = 2 ∧ 2 < 3 :=
  ⟨e 0 + e 3, by decide, by decide, by decide, by norm_num⟩

/-! ### 3.2. Readings for two further round counts ($T=1$ and $T=4$)

The measurement curve of the companion paper (Figure 2) takes four round counts; the two
statements below make $T=1$ and $T=4$ kernel readings as well, so that **every plotted
point** of that curve has a kernel assertion (one per round count). -/

/-- **$T=1$: a single round has no cross-round check at all**, so a readout error of weight
$1$ is both undetectable and logically flipping, and the distance is exactly $1$. This is
the extreme reading of the requirement that a transversal measurement be protected along
the timelike direction. -/
theorem bsMeasure1_eq_one :
    (NoLightFault (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) (e 0 + e 1 + e 2 : Vec 3) 1) ∧
      (∃ f : Vec 3,
        inKerB (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) f = true ∧
          (e 0 + e 1 + e 2 : Vec 3) ⬝ᵥ f = 1 ∧ hammingNorm f = 1) :=
  ⟨noLightFault_of_faultCand_nil _ _ (by decide),
    ⟨e 0, by decide, by decide, by decide⟩⟩

/-- The cross-round parity-check matrix for $T=4$: three rows, row $i$ covering all bits of
rounds $i$ and $i+1$. -/
def bsCrossChecks4 : Matrix (Fin 3) (Fin 12) (ZMod 2) :=
  Matrix.of ![(e 0 + e 1 + e 2 + e 3 + e 4 + e 5 : Vec 12),
               (e 3 + e 4 + e 5 + e 6 + e 7 + e 8 : Vec 12),
               (e 6 + e 7 + e 8 + e 9 + e 10 + e 11 : Vec 12)]

/-- The readout of round $0$ when $T=4$. -/
def bsRound0of4 : Vec 12 := e 0 + e 1 + e 2

/-- **The timelike component is $=4=T$ for $T=4$** (lower bound). -/
theorem bsMeasure4_noLightFault : NoLightFault bsCrossChecks4 bsRound0of4 4 :=
  noLightFault_of_faultCand_nil bsCrossChecks4 bsRound0of4 (by decide)

/-- **The witness for $T=4$**: the same bit is flipped in every round, weight $=4=T$. -/
def bsMeasure4W : Vec 12 := e 0 + e 3 + e 6 + e 9

/-- The three witness facts: in the kernel of the checks, the logical readout is flipped,
and the weight is $=4=T$. -/
theorem bsMeasure4W_witness :
    inKerB bsCrossChecks4 bsMeasure4W = true ∧ bsRound0of4 ⬝ᵥ bsMeasure4W = 1 ∧
      hammingNorm bsMeasure4W = 4 :=
  ⟨by decide, by decide, by decide⟩

/-- **Two-sided bracket for the timelike component at $T=4$: the distance is exactly
$4=T$**, the fourth point of the measurement curve. -/
theorem bsMeasure4_eq_T :
    (NoLightFault bsCrossChecks4 bsRound0of4 4) ∧
      (∃ f : Vec 12, inKerB bsCrossChecks4 f = true ∧ bsRound0of4 ⬝ᵥ f = 1 ∧
        hammingNorm f = 4) :=
  ⟨bsMeasure4_noLightFault, bsMeasure4W, bsMeasure4W_witness.1, bsMeasure4W_witness.2.1,
    bsMeasure4W_witness.2.2⟩

/-! ## 4. Layered coordinates: instantiating the timelike law of `MeasurementProtocol`

The flat coordinates of Section 2 are convenient for `by decide`, while the layered
coordinates `Fin T → Vec 3` of Section 4 are the general shape of `MeasurementProtocol`.
The two are two spellings of one protocol and give the same number. -/

/-- **The timelike law instantiated on this protocol**: the single-round distance is $s=1$
(`bare_noLightFault`: with only the support measured there is no check within a round), so
the spacetime fault weight over $T$ rounds is $\ge T\cdot 1=T$. -/
theorem bsTransversal_time_lower {T : ℕ} (f : SpacetimeFault T 3)
    (hker : ∀ t, inKerB (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) (f t) = true)
    (hlog : ∀ t, bsColumnReadout ⬝ᵥ f t = 1) : T ≤ spacetimeWeight f := by
  simpa using le_spacetimeWeight (bare_noLightFault bsColumnReadout (n := 3)) hker hlog

/-- **The witness for $T=3$**: the same bit is flipped in every round, weight $=3=T$, the
same pattern as `bsMeasureW` in Section 2 (flattened by $3t+i$ it is $e_0+e_3+e_6$). -/
theorem bsTransversal_T3_witness :
    ∃ f : SpacetimeFault 3 3,
      IsUndetectedSpacetimeFault (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)) bsColumnReadout f ∧
      spacetimeWeight f = 3 := by
  have h := spacetimeWeight_witness (T := 3) (s := 1) (H := (0 : Matrix (Fin 0) (Fin 3) (ZMod 2)))
    (w := bsColumnReadout) (e (0 : Fin 3)) (by decide) (by decide) (by decide)
  simpa using h

/-- **The general lower bound for a measurement-type timelike axis (for every round
count)**: when all round readouts agree and more than half the rounds flip, the spacetime
weight is $\ge T$.

The proof is one step: agreement (`AgreeOn`) gives a common value $b$. If $b=1$ then every
round satisfies $w\cdot f_t=1$ on its own, so each round has weight $\ge1$ and the sum is
$T$; if $b=0$ then no round flips, which contradicts the hypothesis that more than half
do. **Note that the cross-round constraint has no other way out here**: it only ties the
rounds to a single value, and flipping requires that value to be $1$, so every round has
to pay its own share of the weight. -/
theorem le_spacetimeWeight_of_agree {T : ℕ} {f : SpacetimeFault T 3}
    (hagree : AgreeOn bsColumnReadout f)
    (hlog : T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card) :
    T ≤ spacetimeWeight f := by
  obtain ⟨b, hb⟩ := hagree
  have hcases : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
  by_cases hb1 : b = 1
  · have hone : ∀ t : Fin T, bsColumnReadout ⬝ᵥ f t = 1 := by
      intro t; rw [hb t, hb1]
    have hpos : ∀ t : Fin T, 1 ≤ hammingNorm (f t) := by
      intro t
      have hne : f t ≠ 0 := by
        intro h0
        have hd : bsColumnReadout ⬝ᵥ (0 : Vec 3) = 0 := by simp [dotProduct]
        have hd1 : bsColumnReadout ⬝ᵥ (0 : Vec 3) = 1 := by rw [← h0]; exact hone t
        rw [hd] at hd1
        exact one_ne_zero hd1.symm
      exact Nat.pos_of_ne_zero fun hz => hne (hammingNorm_eq_zero.mp hz)
    calc T = ∑ _t : Fin T, 1 := by simp
      _ ≤ ∑ t : Fin T, hammingNorm (f t) := Finset.sum_le_sum fun t _ => hpos t
      _ = spacetimeWeight f := rfl
  · have hb0 : b = 0 := hcases b hb1
    have hne : ∀ t : Fin T, bsColumnReadout ⬝ᵥ f t ≠ 1 := by
      intro t h1
      have hz : bsColumnReadout ⬝ᵥ f t = (0 : ZMod 2) := by rw [hb t, hb0]
      rw [hz] at h1
      exact one_ne_zero h1.symm
    have hemp : (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun t _ => hne t
    rw [hemp] at hlog
    simp at hlog

/-- **The general attainable bound for a measurement-type timelike axis (for every round
count)**: copying the single-round witness into every round gives weight exactly $T$,
which together with the lower bound yields a distance of $T$. -/
theorem spacetimeWeight_witness_of_agree {T : ℕ} (hT : 0 < T) :
    ∃ f : SpacetimeFault T 3, AgreeOn bsColumnReadout f ∧
      T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card ∧
      spacetimeWeight f = T := by
  have hdot : bsColumnReadout ⬝ᵥ (e 0 : Vec 3) = 1 := by decide
  have hwt : hammingNorm (e 0 : Vec 3) = 1 := by decide
  refine ⟨fun _ => (e 0 : Vec 3), ⟨1, fun _ => hdot⟩, ?_, ?_⟩
  · have hfil : (Finset.univ.filter
        (fun t : Fin T => bsColumnReadout ⬝ᵥ (fun _ => (e 0 : Vec 3)) t = 1)) = Finset.univ :=
      Finset.filter_eq_self.mpr fun _ _ => hdot
    rw [hfil, Finset.card_univ, Fintype.card_fin]
    omega
  · simp only [spacetimeWeight]
    rw [Finset.sum_congr rfl fun t _ => hwt, Finset.sum_const, Finset.card_univ]
    simp

/-- **For a measurement model that relies only on cross-round comparison, the fault
distance is exactly the number of rounds $T$** (any $T\ge1$): the lower bound is
`le_spacetimeWeight_of_agree` and attainability is `spacetimeWeight_witness_of_agree`.
The four per-$T$ readings of Section 3 ($T=1,2,3,4$) are the two sides of this statement
evaluated at concrete round counts. -/
theorem measureTime_distance_eq_rounds {T : ℕ} (hT : 0 < T) :
    (∀ f : SpacetimeFault T 3, AgreeOn bsColumnReadout f →
      T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card →
      T ≤ spacetimeWeight f) ∧
    (∃ f : SpacetimeFault T 3, AgreeOn bsColumnReadout f ∧
      T < 2 * (Finset.univ.filter (fun t : Fin T => bsColumnReadout ⬝ᵥ f t = 1)).card ∧
      spacetimeWeight f = T) :=
  ⟨fun _ h1 h2 => le_spacetimeWeight_of_agree h1 h2, spacetimeWeight_witness_of_agree hT⟩

/-- **Each component has a kernel-checked instance**: the spacelike component gives $3=d$
(Section 1) and the timelike component $T=d=3$ (Sections 2 and 3), and $3$ is exactly the
code distance `bst_dX` determined in `Codes/BaconShor.lean`. -/
theorem bsMeasure_T_eq_codeDistance :
    (3 : ℕ) = min_weight_ker_not_mem_rowspace bstHz bstHx := by
  rw [bst_dX]

end QECCertificates
