/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.LRATDataCircuit
import QECCertificates.Codes.TimeLikeInstance
import QECCertificates.Codes.GaugeMeasurementInstance

/-!
# Encoding faithfulness on the circuit side: the CNF replayed by the kernel is the output of the encoder

This module is the **circuit-side sibling** of `Reflect/Faithful.lean`. The chain on the
code side (soundness from `Reflect/Encode.lean`, the identity of `Reflect/Faithful.lean` and
the replay of `Reflect/LRATData.lean`) proves that

    the evidence returned by the solver is genuine: the assignment it returns corresponds
    to a light logical operator carrying a dual witness.

This module connects the same machinery to **spacetime faults**. The distance decision for
a quantum code **and a quantum circuit** is to be reduced to SAT; that is already done on
the code side, and the circuit side lands here. The objects encoded are the timelike
detector codes of **two** measurement circuits, which share a single detector shape: $m$
checks are measured repeatedly for $T$ rounds, one bit is one **reported outcome** of check
$a$ in round $t$ (numbered `T*a + t`), and a detector compares two adjacent rounds of the
same check ($H_{(a,t)} = e_{T a + t} + e_{T a + t + 1}$); "all detectors silent" means
$Hf = 0$. A nonzero vector in the kernel is constant along the time axis of each check, so
the minimal undetectable weight is exactly $T$.

| instance | the $m$ checks measured repeatedly | $T$ |
|---|---|---|
| `timelike34` | the three repeated checks of `timeLike34H` in `Codes/TimeLikeInstance.lean` | 4 |
| `bbgauge44` | the $\lvert V \rvert = 4$ Gauss laws of the BB gauging measurement circuit (`Codes/GaugeMeasurementInstance.lean`) | $4 = d$ |

**Relation to the two `Codes` modules**: the CNF replayed here asserts that there is no
$0 \ne f$ with $\mathrm{wt}(f) \le 3$ and $Hf = 0$, which is **the same proposition** as
`<instance>_d` there (`min_weight_ker_not_mem_rowspace <instance>H (zeroRows N) = 4`);
`timelike34Ker_rows` / `bbgauge44Ker_rows` pin the row lists word for word to the two
matrices of those instances, and both ask for a fault that is nonzero with all detectors
silent (the minimal weight inside the kernel), and **not** for the `IsUndetectedFault`
branch of `Codes/MeasurementProtocol.lean`, which carries the logical functional
$w\cdot f=1$; neither of the two has such a $w$, so the two are different statements.

**Direction**: as in `Reflect/Faithful.lean`, this module provides the **soundness
direction** (the evidence returned by the solver is genuine); the converse (no light fault
implies that the CNF is unsatisfiable) likewise requires constructing values for the
auxiliary variables and is not formalized. The lower bound itself has an independent route
(the weight-bounded enumeration of `Codes/TimeLikeInstance.lean` and
`Codes/GaugeMeasurementInstance.lean`, and the further family-level theorem
`bbGauge44_le_weight_of_ker` of the latter) that does not depend on this one.
-/

namespace QECCertificates.LRAT

set_option maxRecDepth 1000000

set_option maxHeartbeats 8000000

/-! ## 1. The row list of the Bacon–Shor detector code

The rows agree word for word with an external generator that solves the same instance: nine
detector rows, each row a **list of column indices** (a column being the bit numbered
$4a+t$). The pairing side is the empty list, since this instance asks only for a nonzero
fault with all detectors silent, which is the role played by `zeroRows 12` in
`Codes/TimeLikeInstance.lean`. -/

/-- The nine detector rows of the timelike detector code ($m=3$, $T=4$). -/
def timelike34Ker : List (List Nat) :=
  [[0, 1], [1, 2], [2, 3], [4, 5], [5, 6], [6, 7], [8, 9], [9, 10], [10, 11]]

/-- The pairing side is empty (there is no logical functional $w$; see the module header). -/
def timelike34Pair : List (List Nat) := []

/-- The `timelike34CNF` used for the replay is exactly the output of the encoder applied to
this list of rows. -/
theorem timelike34_eq : buildPair timelike34Ker timelike34Pair 12 3 = timelike34CNF := by decide

/-- **The row list is pinned to the protocol matrix**: this instance has nine detector
rows, and they agree word for word with `timeLike34H` of `Codes/TimeLikeInstance.lean`.
With this, the CNF that is replayed and the machine-checked timelike instance are really
the same object. -/
theorem timelike34Ker_rows :
    (timelike34Ker.map (fun r => fun j : Fin 12 => if j.val ∈ r then (1 : ZMod 2) else 0))
      = List.ofFn (fun i : Fin 9 => timeLike34H i) := by decide

/-- The timelike instance: an assignment satisfying `timelike34CNF` yields a fault of weight
at most 3 with every detector silent. -/
theorem timelike34_certified {σ : Assign} (h : SatFormula σ timelike34CNF) :
    cntS σ (List.range 12) ≤ 3 ∧
    (∀ r ∈ timelike34Ker, dotS σ r = false) ∧
    (∀ r ∈ timelike34Pair, dotS (fun t => σ (12 + t)) r = false) ∧
    dotS (fun t => σ t && σ (12 + t)) (List.range 12) = true := by
  rw [← timelike34_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-! ## 2. The row list of the BB gauging measurement circuit

These rows again agree word for word with the external generator: $|V| = 4$ Gauss laws,
$T = 4$ rounds, $12$ detector rows, each row a **list of column indices** (a column being
the bit numbered $4v+t$). **Scope**, as in the header of
`Codes/GaugeMeasurementInstance.lean`: this instance covers only the $|V|$ Gauss laws of the
gauging measurement step, and **not** the full syndrome-extraction cycle of the whole gauged
code $[[24,3,4]]$. -/

/-- The twelve detector rows of the BB gauging measurement circuit ($|V|=4$ Gauss laws,
$T=4$ rounds). -/
def bbgauge44Ker : List (List Nat) :=
  [[0, 1], [1, 2], [2, 3], [4, 5], [5, 6], [6, 7],
   [8, 9], [9, 10], [10, 11], [12, 13], [13, 14], [14, 15]]

/-- The pairing side is empty (as in `timelike34Pair`: there is no logical functional $w$). -/
def bbgauge44Pair : List (List Nat) := []

/-- The `bbgauge44CNF` used for the replay is exactly the output of the encoder applied to
this list of rows. -/
theorem bbgauge44_eq : buildPair bbgauge44Ker bbgauge44Pair 16 3 = bbgauge44CNF := by decide

/-- **The row list is pinned to the protocol matrix**: this instance has twelve detector
rows, and they agree word for word with `bbGauge44H` of
`Codes/GaugeMeasurementInstance.lean` (the adjacent-round comparisons of the $|V| = 4$
Gauss laws). With this, the CNF that is replayed and the machine-checked gauging
measurement circuit instance are really the same object. -/
theorem bbgauge44Ker_rows :
    (bbgauge44Ker.map (fun r => fun j : Fin 16 => if j.val ∈ r then (1 : ZMod 2) else 0))
      = List.ofFn (fun i : Fin 12 => bbGauge44H i) := by decide

/-- The BB gauging measurement circuit instance: an assignment satisfying `bbgauge44CNF`
yields a spacetime fault of weight at most 3 with every detector of every Gauss law silent. -/
theorem bbgauge44_certified {σ : Assign} (h : SatFormula σ bbgauge44CNF) :
    cntS σ (List.range 16) ≤ 3 ∧
    (∀ r ∈ bbgauge44Ker, dotS σ r = false) ∧
    (∀ r ∈ bbgauge44Pair, dotS (fun t => σ (16 + t)) r = false) ∧
    dotS (fun t => σ t && σ (16 + t)) (List.range 16) = true := by
  rw [← bbgauge44_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

end QECCertificates.LRAT
