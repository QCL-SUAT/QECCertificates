/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.Separation
import QECCertificates.Codes.CaseMatrix

/-!
# The representation layer of a measurement protocol (spacetime fault model and the time axis of the two components)

`Codes/Separation.lean` writes the two components as **abstract parameters** (`rounds`,
`d`, `η`), and `Codes/Gauging.lean` proves the time axis as a theorem **on a chain**
(adjacent-round checks imply that all values are equal, which implies weight = number of
rounds). One layer is missing between the two: **writing "a measurement protocol" itself
as an object**, so that the number of rounds is no longer an external parameter but a
field of the protocol, and the time-axis component becomes a number computed from the
protocol.

This module supplies that layer. It uses only three notions:

## 1. A single round: fault patterns and "undetectable logical faults"

After one round of measurements, the set of qubits whose **reported outcomes** are wrong
is a fault pattern $f \in \mathbb F_2^n$. Its two consequences are each a linear
functional:

* **checks**: the parity-check matrix $H$ available within the round (each row a
  stabilizer) gives the syndrome $Hf$, which is all zero exactly when the fault is not
  detected (`inKerB H f = true`);
* **logic**: the logical readout is $w \cdot f$ (where $w$ is the support indicator vector
  of the logical operator), which equals $1$ exactly when the readout is flipped.

Together these are `IsUndetectedFault H w f`. **Note that this must be "the logical
functional is $1$", not "$f$ lies outside the row space of $H$"**: the two are not
equivalent on other codes (this library's own `min_weight_ker_not_mem_rowspace` uses the
latter), and on the Bacon–Shor instance below they differ by $2$ versus $3$. The decision
uses a weight-limited enumeration (`faultCand`, shaped like `lightCand`), and its
soundness again rests only on the covering theorem `mem_lightVecs`.

## 2. Across rounds: spacetime fault patterns and "identical readouts"

Repeat the measurement $T$ times, with one fault pattern per round
(`SpacetimeFault T n = Fin T → Vec n`). **The cross-round check is precisely "the logical
readouts of all rounds agree"**: a readout differing from the others is itself a visible
anomaly, and that is what repeating the measurement is for. A spacetime undetectable
logical fault is therefore one that evades the intra-round checks in every round, with all
readouts identical and all equal to $1$.

## 3. The time-axis law: the two components **multiply** rather than taking a minimum

Let $s$ be the minimum weight of a single-round undetectable logical fault. Then the
spacetime fault distance of the $T$-round protocol is **exactly** $T \cdot s$:

* **lower bound** (`le_spacetimeWeight`): every round reads $1$, so each round is itself
  an undetectable logical flip, so every round has weight $\ge s$, and the total weight is
  $\ge T\cdot s$;
* **attained** (`spacetimeWeight_witness`): copying the single-round witness into every
  round gives a spacetime fault of weight $T\cdot s$.

**Why it multiplies**: the cross-round constraint "all identical" **ties the rounds
together**, since a single round differing from the others is exposed, so either every
round is flipped (a cost of $T$ copies) or none is (harmless). With no intra-round check
one has $s=1$ (`bare_noLightFault`: the logical operator is a product of outcomes, any one
of them being wrong flips it, and a single round offers nothing that could notice), so the
protocol distance is $T$, which is **exactly the `d ≤ rounds` of C2**:
`exists_undetectable_of_rounds_lt` in `Codes/Separation.lean` states that with fewer than
$d$ rounds a lighter undetectable operator exists, and this module computes it as an
**exact value** (`separation_C2`, together with the two-sided squeeze of the instance
modules).
-/

namespace QECCertificates

open scoped BigOperators

variable {n m : ℕ}

/-! ## 1. The fault pattern of a single round -/

/-- **An undetectable logical fault** (single round): the fault pattern `f` (which reported
outcomes are flipped) evades every intra-round check (its syndrome is zero) and yet flips the
logical readout.

The two conjuncts are the computable decision `inKerB` and the computable functional `⬝ᵥ`, so the
whole predicate can be reduced by the kernel. -/
abbrev IsUndetectedFault {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (w : Vec n)
    (f : Vec n) : Prop :=
  inKerB H f = true ∧ w ⬝ᵥ f = 1

/-- **The fault candidate set** (a weight-limited enumeration, shaped like `lightCand`): the fault
patterns of weight $\le d-1$ that go undetected and flip the logical readout. -/
def faultCand {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (w : Vec n) (d : ℕ) :
    List (Vec n) :=
  (lightVecs n (d - 1)).filter (fun f => decide (IsUndetectedFault H w f))

/-- The membership characterisation (`faultCand` unfolded into the candidate set and the predicate). -/
theorem mem_faultCand {m : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    {d : ℕ} {f : Vec n} :
    f ∈ faultCand H w d ↔ f ∈ lightVecs n (d - 1) ∧ IsUndetectedFault H w f := by
  rw [faultCand, List.mem_filter, decide_eq_true_eq]

/-- **The single-round lower-bound hypothesis**: every undetectable logical fault has weight at least `s`.

This is the computable form of "the single-round fault distance is $\ge s$": it is the
**hypothesis** that the decision layer has to establish, and `faultCand` being empty is its
**certificate** (`noLightFault_of_faultCand_nil`). -/
abbrev NoLightFault {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (w : Vec n) (s : ℕ) :
    Prop :=
  ∀ f : Vec n, IsUndetectedFault H w f → s ≤ hammingNorm f

/-- **Certificate implies hypothesis**: if the weight-limited enumeration holds no undetectable
logical fault, the lower bound `d` follows.

The proof is isomorphic to `lowerHyp_of_lightCand_nil`: contradiction, then covering
(`mem_lightVecs`), then putting the vector back into the set. -/
theorem noLightFault_of_faultCand_nil {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) {d : ℕ} (h : faultCand H w d = []) : NoLightFault H w d := by
  intro f hf
  by_contra hlt
  have hlt' : hammingNorm f < d := not_le.mp hlt
  have hcov : f ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) f ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : f ∈ faultCand H w d := mem_faultCand.mpr ⟨hcov, hf⟩
  rw [h] at hmem
  simp at hmem

/-- **Transversal measurement with no intra-round check: the single-round fault distance is 1**.

When the logical readout is a product of outcomes, any one of the three being wrong flips it, and
within a single round **no check at all** can detect this, so a fault pattern of weight $1$ already
suffices. This is the representation-layer content of "transversal measurement has to be protected
by the time axis", and it is why C2 turns from "sufficient" into "exactly" in the instances. -/
theorem bare_noLightFault (w : Vec n) :
    NoLightFault (0 : Matrix (Fin 0) (Fin n) (ZMod 2)) w 1 := by
  intro f hf
  have hne : f ≠ 0 := by
    intro h0
    have hd : w ⬝ᵥ (0 : Vec n) = 0 := by simp [dotProduct]
    rw [h0] at hf
    exact one_ne_zero (hf.2.symm.trans hd)
  have hpos : 0 < hammingNorm f :=
    Nat.pos_of_ne_zero fun hz => hne (hammingNorm_eq_zero.mp hz)
  omega

/-! ## 2. Spacetime fault patterns across rounds -/

/-- **A spacetime fault pattern**: one fault vector per round (the fault pattern of round `t` is `f t`). -/
abbrev SpacetimeFault (T n : ℕ) := Fin T → Vec n

/-- **The weight of a spacetime fault** is the sum of the weights of the rounds (every wrong reported
outcome counts once). -/
def spacetimeWeight {T n : ℕ} (f : SpacetimeFault T n) : ℕ := ∑ t, hammingNorm (f t)

/-- **Identical readouts**: the logical readouts of all rounds take the same value, so comparing
rounds reveals nothing. -/
abbrev AgreeOn {T n : ℕ} (w : Vec n) (f : SpacetimeFault T n) : Prop :=
  ∃ b : ZMod 2, ∀ t, w ⬝ᵥ f t = b

/-- **A spacetime undetectable logical fault**: every round evades the intra-round checks, the readouts
of all rounds agree, and all of them are `1` (the logical readout is flipped). -/
abbrev IsUndetectedSpacetimeFault {T n m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Vec n) (f : SpacetimeFault T n) : Prop :=
  (∀ t, inKerB H (f t) = true) ∧ (∀ t, w ⬝ᵥ f t = 1)

/-! ## 3. The time-axis law: distance = rounds × single-round distance -/

/-- **The time-axis law (lower bound)**: a single-round distance $\ge s$ implies that the spacetime
fault weight of a $T$-round protocol is $\ge T\cdot s$.

Only one thing is used: every round reads $1$, so **each round by itself** is a single-round
undetectable logical fault, hence every round has weight $\ge s$, and summing gives $T\cdot s$. The
cross-round constraint "all identical" leaves no other way out. -/
theorem le_spacetimeWeight {T : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    {s : ℕ} (h : NoLightFault H w s) {f : SpacetimeFault T n}
    (hker : ∀ t, inKerB H (f t) = true) (hlog : ∀ t, w ⬝ᵥ f t = 1) :
    T * s ≤ spacetimeWeight f := by
  have hstep : ∀ t : Fin T, s ≤ hammingNorm (f t) := fun t => h (f t) ⟨hker t, hlog t⟩
  have hsum : (∑ _t : Fin T, s) = T * s := by
    simp [Finset.sum_const, Finset.card_univ]
  calc T * s = ∑ _t : Fin T, s := hsum.symm
    _ ≤ ∑ t : Fin T, hammingNorm (f t) := Finset.sum_le_sum fun t _ => hstep t
    _ = spacetimeWeight f := rfl

/-- **The time-axis law (attained)**: copying the single-round witness into every round gives a
spacetime fault of weight exactly $T\cdot s$.

The two-sided squeeze for "spacetime fault distance $=T\cdot s$" is now complete; the lower bound is
`le_spacetimeWeight`. -/
theorem spacetimeWeight_witness {T : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    {s : ℕ} (f₀ : Vec n) (hker : inKerB H f₀ = true) (hlog : w ⬝ᵥ f₀ = 1)
    (hw : hammingNorm f₀ = s) :
    ∃ f : SpacetimeFault T n, IsUndetectedSpacetimeFault H w f ∧
      spacetimeWeight f = T * s := by
  have hfault : IsUndetectedSpacetimeFault H w (fun _ : Fin T => f₀) :=
    ⟨fun _ => hker, fun _ => hlog⟩
  have hwt : spacetimeWeight (fun _ : Fin T => f₀) = T * s := by
    have hterm : ∀ t : Fin T, hammingNorm ((fun _ : Fin T => f₀) t) = s := fun _ => hw
    simp only [spacetimeWeight]
    rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const, Finset.card_univ]
    simp
  exact ⟨fun _ => f₀, hfault, hwt⟩

/-- **Where C2 lands**: a sufficient condition for "the spacetime fault distance is $\ge d$" is
$d\le T\cdot s$.

For a transversal measurement with no intra-round check (`s = 1`) this is the $d\le T$ of the
companion paper, that is, at least as many rounds as the code distance; the instance modules compute
it as an **exact value** on Bacon–Shor and establish its sharpness. -/
theorem separation_C2 {T s d : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {w : Vec n}
    (hds : d ≤ T * s) (h : NoLightFault H w s) {f : SpacetimeFault T n}
    (hker : ∀ t, inKerB H (f t) = true) (hlog : ∀ t, w ⬝ᵥ f t = 1) :
    d ≤ spacetimeWeight f :=
  le_trans hds (le_spacetimeWeight h hker hlog)

end QECCertificates
