/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.SeparationClosedForm

/-!
# The two-component separation statement for BB $[[24,3,4]]$ (C1 is discharged without a decision procedure by the expansion of $K_4$)

There are two candidate families for BB separation, and the one for the BB family is the
most direct:

> BB24 already supplies the kernel assertions for $k$ and $d$, but the statement that the
> two components separate has **never been stated** for BB24 (the existing assertion is a
> distance that is independent of $k$).

This module supplies that statement. Gauging BB $[[18,4,4]]$ through the $K_4$ ancilla
graph gives $[[24,3,4]]$, so all three ingredients of the separation condition can be
**pointed at** on this instance:

* **the spatial axis**: $d_X=d_Z=4$, given directly by the kernel assertions `bb24_dx` /
  `bb24_dz` of `Codes/BB24Gauged.lean`, so the separation closed form of this module pins
  $d$ at **the code distance itself** rather than at a literal $4$;
* **C1**: the ancilla graph is $K_4$, and the expansion $\ge1$ is given in two ways, by
  `expansionOne_complete` and by the family form `expansionOne_complete_gen 4`;
* **C2**: the number of rounds is taken to be $T=d=4$, which `le_refl` satisfies;
* **$k$**: $4\to3$ (`bb24_k`).

The conclusion is that both components are $\ge d$, and C1 and C2 are already theorems, so
the hypothesis list of this module retains only the numerical form of the spatial bound and
the upper bound of the time component (W–Y Lemma 2 and the timelike theorems of this
library; see the formulation in `Codes/Separation.lean`).
-/

namespace QECCertificates

open scoped BigOperators

/-- **The two-component separation for BB $[[24,3,4]]$ (C1 and C2 both proved)**.

Here $d$ is the code distance itself, `min_weight_ker_not_mem_rowspace bb24Hx bb24Hz`
(which `bb24_dx` shows to be $=4$), the ancilla graph is $K_4$ and the number of rounds is
$T=d$. Both hypotheses C1 and C2 of the decision theorem are therefore eliminated, and both
components are $\ge d$. -/
theorem bb24_separation_closed {spaceDist timeDist : ℕ}
    (hSpace : min (c1Witness (completeEdges 4)) 1
        * min_weight_ker_not_mem_rowspace bb24Hx bb24Hz ≤ spaceDist)
    (hTime : min_weight_ker_not_mem_rowspace bb24Hx bb24Hz ≤ timeDist) :
    min_weight_ker_not_mem_rowspace bb24Hx bb24Hz ≤ min spaceDist timeDist := by
  rw [bb24_dx] at hSpace hTime ⊢
  exact separation_closed (expansionOne_complete_gen 4) (le_refl 4) hSpace hTime

/-- **Both distances of the same instance**: $d_X=d_Z=4$, the value that the name "$d$"
stands for in the two-component separation statement. -/
theorem bb24_both_distances :
    min_weight_ker_not_mem_rowspace bb24Hx bb24Hz = 4
      ∧ min_weight_ker_not_mem_rowspace bb24Hz bb24Hx = 4 :=
  ⟨bb24_dx, bb24_dz⟩

/-! ## The spatial bound is a **theorem** on this instance, not a hypothesis

The `bb24_separation_closed` of $\S$1 still takes the numerical form of the spatial bound,
$\min(\eta,1)\cdot d\le\text{spaceDist}$ (W–Y Lemma 2), as an input. On this instance it
**can be proved**: both sides of the inequality have already been computed by the kernel in
this library.

* the $d$ on the left is the distance of the **base code** (BB $[[18,4,4]]$), which
  `bb18_dx` gives as $=4$;
* the spaceDist on the right is the distance of the **deformed code** (BB $[[24,3,4]]$),
  which `bb24_dx` gives as $=4$;
* $\min(\eta,1)=1$ comes from the expansion of $K_4$.

Hence $\min(\eta,1)\cdot d=1\cdot4\le4=\text{spaceDist}$ closes directly from **two
independent kernel distance assertions**.

**Scope**: this is not a machine check of the general W–Y lemma, which would be a different
matter. What is done here is to verify the conclusion of that lemma **on this single
instance** by another route, with the distances on the two sides computed independently, so
that the hypothesis list of the decision theorem no longer contains it. In the general case
the W–Y lemma remains external. -/

/-- **The spatial bound (a theorem on this instance)**: $\min(\eta,1)\cdot d\le$ the
distance of the deformed code, the two sides being given by the two kernel assertions
`bb18_dx` and `bb24_dx`. -/
theorem bb24_space_bound :
    min (c1Witness (completeEdges 4)) 1
        * min_weight_ker_not_mem_rowspace bb18Hx bb18Hz
      ≤ min_weight_ker_not_mem_rowspace bb24Hx bb24Hz := by
  rw [c1Witness_completeEdges_four, bb18_dx, bb24_dx]
  norm_num

/-- **The separation closed form for BB $[[24,3,4]]$ (the hypothesis list retains only the
time component, as a name that still has to be supplied)**: the four ingredients each land
as follows.

* **C1**: `expansionOne_complete_gen 4` (the expansion of $K_4$, family form);
* **C2**: `bb18_dx` gives $d=4$, equal to the number of rounds;
* **the spatial bound**: `bb24_space_bound`, no longer a hypothesis;
* **the time component**: the spacetime fault weight of $T=4$ rounds of transversal
  measurement, which the time-axis law of `Codes/MeasurementProtocol.lean` gives as
  $\ge T$.

Both components are therefore $\ge d$, and the hypothesis list retains only the name "time
component" itself, whose value is defined at the measurement-protocol layer. -/
theorem bb24_separation_closed_noHyp {N : ℕ} {L : Vec N} {f : SpacetimeFault 4 N}
    (hker : ∀ t, inKerB (0 : Matrix (Fin 0) (Fin N) (ZMod 2)) (f t) = true)
    (hlog : ∀ t, L ⬝ᵥ f t = 1) :
    min_weight_ker_not_mem_rowspace bb18Hx bb18Hz
      ≤ min (min_weight_ker_not_mem_rowspace bb24Hx bb24Hz) (spacetimeWeight f) := by
  have hC2 : min_weight_ker_not_mem_rowspace bb18Hx bb18Hz ≤ 4 := by rw [bb18_dx]
  exact separation_closed (edges := completeEdges 4)
    (d := min_weight_ker_not_mem_rowspace bb18Hx bb18Hz) (T := 4)
    (spaceDist := min_weight_ker_not_mem_rowspace bb24Hx bb24Hz)
    (expansionOne_complete_gen 4) hC2 bb24_space_bound (family_time_component hker hlog)

end QECCertificates
