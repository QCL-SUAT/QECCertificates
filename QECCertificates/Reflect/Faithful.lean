/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.LRATData

/-!
# Encoding faithfulness: the CNF that the kernel replays is the encoder's output

`Reflect/Encode.lean` proves **soundness** of that encoding (the `build_pair` routine of an
external encoder) inside the kernel: every satisfying assignment yields

* the weight of `x` is at most `k` (`cntS` counts the true bits);
* `x` lies in the kernel of the kernel-side row table and `w` in the kernel of the
  pairing-side row table;
* `x.w = 1`, which by itself rules out `x` lying in the pairing-side row space (the row space
  is contained in the orthogonal complement of the kernel).

This module **joins the two ends**: the four CNFs carried into the kernel are equal, word for
word, to the output of `buildPair` applied to the same row tables (`by decide`, four
identities). Hence

    ¬ Satisfiable <instance>CNF   (LRAT replay, see LRATData)
  + <instance>CNF = buildPair <row table>   (this module)
  ⟹ ¬ Satisfiable (buildPair <row table>)

**A note on direction (this has to be stated precisely)**: what `buildPair_sat` in
`Reflect/Encode.lean` proves is

    Satisfiable (buildPair <row table>)  ⟹  a light logical operator with a dual witness exists

that is, "a satisfying assignment implies a light logical operator exists" (equivalently,
"no light logical operator implies unsatisfiable"). To get from the `¬ Satisfiable` above to
"no light logical operator exists", one needs the **converse**:

    a light logical operator exists  ⟹  Satisfiable (buildPair <row table>)

that is, the encoding does not overconstrain. That statement **is given by
`Reflect/Complete.lean`**: it constructs the values of the auxiliary variables of the Tseitin
chains, the product blocks and the sequential counter, and the four pieces concatenate into
`buildPair_complete`. Together with `Reflect.Complete`, this module therefore gives
"**satisfiable if and only if a light logical operator exists**", and combined with the LRAT
replay that lets a single unsatisfiability verdict **yield a distance lower bound directly**.
The lower bound for $[[144,12,12]]$ has a separate, independent route (in
`Codes/BB144Distance.lean`, through the Gross formalization of QECLean) and does not depend
on this.
-/

namespace QECCertificates.LRAT

set_option maxRecDepth 1000000

set_option maxHeartbeats 8000000

/-!
## The row tables of the four replayed instances

The sources match, word for word, the instance table of the external encoder: the repetition,
Steane and toric (`cycle`) instances of its test engine, and the BB18 rows of its encoding
test. A row is a **list of column indices**.
-/

/-- The kernel-side row table of the repetition code $[7,1,7]$ (6 parity checks). -/
def rep7Ker : List (List Nat) := [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6]]

/-- The pairing side of the repetition code is empty (this instance only asks for "a nonzero vector in the kernel"). -/
def rep7Pair : List (List Nat) := []

/-- The kernel side of Steane $[[7,1,3]]$ (the Z-type checks). -/
def steaneKer : List (List Nat) :=
  [[0, 2, 4, 6], [1, 2, 5, 6], [3, 4, 5, 6]]

/-- The pairing side of Steane (the X-type checks). -/
def steanePair : List (List Nat) :=
  [[0, 2, 4, 6], [1, 2, 5, 6], [3, 4, 5, 6]]

/-- The kernel side of the toric $[[18,2,3]]$ (the HGP of the 3-cycle matrix). -/
def hgp_toric3Ker : List (List Nat) :=
  [[0, 1, 9, 15], [1, 2, 10, 16], [0, 2, 11, 17],
   [3, 4, 9, 12], [4, 5, 10, 13], [3, 5, 11, 14],
   [6, 7, 12, 15], [7, 8, 13, 16], [6, 8, 14, 17]]

/-- The pairing side of the toric $[[18,2,3]]$. -/
def hgp_toric3Pair : List (List Nat) :=
  [[0, 3, 9, 11], [1, 4, 9, 10], [2, 5, 10, 11],
   [3, 6, 12, 14], [4, 7, 12, 13], [5, 8, 13, 14],
   [0, 6, 15, 17], [1, 7, 15, 16], [2, 8, 16, 17]]

/-- The kernel side of the bivariate bicycle $[[18,4,4]]$. -/
def bb18_lb3Ker : List (List Nat) :=
  [[0, 1, 3, 9, 11, 15], [1, 2, 4, 9, 10, 16], [0, 2, 5, 10, 11, 17],
   [3, 4, 6, 9, 12, 14], [4, 5, 7, 10, 12, 13], [3, 5, 8, 11, 13, 14],
   [0, 6, 7, 12, 15, 17], [1, 7, 8, 13, 15, 16], [2, 6, 8, 14, 16, 17]]

/-- The pairing side of the bivariate bicycle $[[18,4,4]]$. -/
def bb18_lb3Pair : List (List Nat) :=
  [[0, 1, 3, 9, 11, 15], [1, 2, 4, 9, 10, 16], [0, 2, 5, 10, 11, 17],
   [3, 4, 6, 9, 12, 14], [4, 5, 7, 10, 12, 13], [3, 5, 8, 11, 13, 14],
   [0, 6, 7, 12, 15, 17], [1, 7, 8, 13, 15, 16], [2, 6, 8, 14, 16, 17]]

/-! ## The four identities (checked by the kernel with `decide`) -/

/-- The repetition-code CNF used in the replay is exactly the encoder's output. -/
theorem rep7_eq : buildPair rep7Ker rep7Pair 7 6 = rep7CNF := by decide

/-- The same for the Steane instance. -/
theorem steane_eq : buildPair steaneKer steanePair 7 2 = steaneCNF := by decide

/-- The same for the toric $[[18,2,3]]$ instance. -/
theorem hgp_toric3_eq : buildPair hgp_toric3Ker hgp_toric3Pair 18 2 = hgp_toric3CNF := by decide

/-- The same for the bivariate bicycle $[[18,4,4]]$ instance. -/
theorem bb18_lb3_eq : buildPair bb18_lb3Ker bb18_lb3Pair 18 3 = bb18_lb3CNF := by decide

/-! ## Composing the two ends: every satisfying assignment yields a light logical operator together with a dual witness -/

/-- The repetition-code instance: an assignment satisfying `rep7CNF` yields a kernel vector of weight at most 6 together with a pairing witness. -/
theorem rep7_certified {σ : Assign} (h : SatFormula σ rep7CNF) :
    cntS σ (List.range 7) ≤ 6 ∧
    (∀ r ∈ rep7Ker, dotS σ r = false) ∧
    (∀ r ∈ rep7Pair, dotS (fun t => σ (7 + t)) r = false) ∧
    dotS (fun t => σ t && σ (7 + t)) (List.range 7) = true := by
  rw [← rep7_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-- The Steane instance. -/
theorem steane_certified {σ : Assign} (h : SatFormula σ steaneCNF) :
    cntS σ (List.range 7) ≤ 2 ∧
    (∀ r ∈ steaneKer, dotS σ r = false) ∧
    (∀ r ∈ steanePair, dotS (fun t => σ (7 + t)) r = false) ∧
    dotS (fun t => σ t && σ (7 + t)) (List.range 7) = true := by
  rw [← steane_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-- The toric $[[18,2,3]]$ instance. -/
theorem hgp_toric3_certified {σ : Assign} (h : SatFormula σ hgp_toric3CNF) :
    cntS σ (List.range 18) ≤ 2 ∧
    (∀ r ∈ hgp_toric3Ker, dotS σ r = false) ∧
    (∀ r ∈ hgp_toric3Pair, dotS (fun t => σ (18 + t)) r = false) ∧
    dotS (fun t => σ t && σ (18 + t)) (List.range 18) = true := by
  rw [← hgp_toric3_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

/-- The bivariate bicycle $[[18,4,4]]$ instance. -/
theorem bb18_lb3_certified {σ : Assign} (h : SatFormula σ bb18_lb3CNF) :
    cntS σ (List.range 18) ≤ 3 ∧
    (∀ r ∈ bb18_lb3Ker, dotS σ r = false) ∧
    (∀ r ∈ bb18_lb3Pair, dotS (fun t => σ (18 + t)) r = false) ∧
    dotS (fun t => σ t && σ (18 + t)) (List.range 18) = true := by
  rw [← bb18_lb3_eq] at h
  exact buildPair_sat (by decide) (by decide) (by decide) h

end QECCertificates.LRAT
