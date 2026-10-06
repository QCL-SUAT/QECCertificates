/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.CosystolicLowerBound

open QECCertificates

/-!
# The **low-weight criterion** for the $1$-cosystolic distance: $d_1^\bullet\ge3$ is decidable

Sections 3–6 of `Homology/CosystolicLowerBound.lean` give **two families** of instances with
unbounded $d_1^\bullet$, but its honest boundary records one item: **on a general hypergraph
the lower bound $d_1^\bullet\ge3$ (indeed any $d$) is not formalized** — the reason being
that $d_1^\bullet$ is the minimum weight of the quotient space
$\ker\delta_2/\mathrm{im}\,\delta_1$, and a general lower bound is of the same difficulty as
the code-distance lower bound of a classical code. This module **sharpens that sentence into
a decidable criterion**, so that "$d_1^\bullet\ge3$" is no longer an open problem but a
**finite condition**:

$$\texttt{cosystolicDistance}\ge3
\iff \text{no }1\text{-cosystolic cochain of weight }1\ \wedge\
\text{no }1\text{-cosystolic cochain of weight }2,$$

and both ranges already have a **necessary-and-sufficient classification** in the library
(weight $1$ in `isCosystolic_indVec_singleton_iff`, weight $2$ in
`isCosystolic_indVec_pair_iff_component`); substituting gives a fully explicit criterion
(`three_le_cosystolicDistance_of_pairExclusion`: $W$ covers every vertex, plus no pair of
points that is "$\sim_W$-equivalent and separated by some component").

## Contents

* §1, general tools: **the parity of the weight equals the coordinate sum** (over
  $\mathbb F_2$ the coordinate sum of an indicator vector is its weight mod 2), and the
  **pointwise characterization** of $d_1^\bullet$ (`le_cosystolicDistance_iff`: the lower
  bound is equivalent to "every cosystolic cochain has weight at least that") — this is the
  bridge between "a lower bound" and "a statement about each vector".
* §2, the vectors of weight $\le2$ are only three: zero, a single point, two distinct points
  (`eq_zero_or_indVec_singleton_or_pair`).
* §3, the **main criterion** (`three_le_cosystolicDistance_iff`) and its classification form
  (`three_le_cosystolicDistance_of_pairExclusion`).
* §4, one **structural** constraint: if the family of components contains the whole vertex set
  $V$ as a component, then every cosystolic cochain has **even** weight
  (`even_hammingNorm_of_isCosystolic_univ`) — so the range $3$ never occurs and
  $d_1^\bullet$ is even.

## Division of labour with `Homology/CosystolicCharacterization.lean`

This module writes the criterion on the **weight** side: the vectors of weight $\le2$ have
only the three shapes zero, a single point, two distinct points (§2), and classifying them
shape by shape gives the criterion. `Homology/CosystolicCharacterization.lean` rewrites it on
the **set** side — over $\mathbb F_2$ a vector is the indicator vector of its support, both
membership decisions become one parity condition each, and so the same criterion is **no
longer limited by weight**:

$$\mathbf 1_S\in\ker\delta_2\setminus\mathrm{im}\,\delta_1
\iff \bigl(\forall w,\ |S\cap W_w|\ \text{is even}\bigr)\ \wedge\
\bigl(\exists\ \text{a component}\ C,\ |S\cap C|\ \text{is odd}\bigr),$$

The `three_le_cosystolicDistance_iff` of §3 of this module is its specialization to
$|S|\le2$ (the `three_le_cosystolicDistance_iff_no_small` there is the set-side writing of
the same criterion).

## Honest boundary

* **No closed form** (the **decision** at arbitrary weight is already given by
  `Homology/CosystolicCharacterization.lean`): $d_1^\bullet$ is the minimum weight of the
  quotient code $\ker\delta_2/\mathrm{im}\,\delta_1$, and minimizing the cardinality over the
  coset structure of the admissible set is of the same difficulty as the code-distance lower
  bound of a classical code. Both this module and that one deliver **criteria**, not closed
  forms.
* The "no cosystolic cochain of weight $2$" in the criterion uses the classification of §5;
  this module does not write the criterion for $d_1^\bullet\ge4$ (it would need the
  classification at weight $3$), but the criterion at **arbitrary weight** is in
  `Homology/CosystolicCharacterization.lean`.
-/

namespace QECCertificates.Homology

open _root_.Matrix

open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. General tools: weight parity and the pointwise lower bound -/

/-- **The parity of the weight equals the coordinate sum**: over $\mathbb F_2$ every nonzero
entry is $1$, so the coordinate sum of a vector is the parity of its weight (this translates a
**coordinate-sum** constraint such as "$\delta_2u=0$" into a constraint on the weight). -/
theorem natCast_hammingNorm_eq_sum {n : ℕ} (u : Vec n) :
    ((hammingNorm u : ℕ) : ZMod 2) = ∑ v : Fin n, u v := by
  have hterm : ∀ v : Fin n, u v = if u v ≠ 0 then (1 : ZMod 2) else 0 := by
    intro v
    by_cases hv : u v = 0
    · rw [ite_eq_right (by simp [hv]), hv]
    · rw [ite_eq_left (by simp [hv]), eq_one_of_ne_zero hv]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_boole]
  exact congrArg (fun t : ℕ => (t : ZMod 2)) (weight_eq_hammingNorm u).symm

/-- **The pointwise characterization of $d_1^\bullet$**: the lower bound $w\le d_1^\bullet$ is
equivalent to "every cosystolic cochain has weight $\ge w$". This is the bridge between "a
lower bound" and a statement about each vector (when the set is nonempty, $d_1^\bullet$ is
that minimum). -/
theorem le_cosystolicDistance_iff {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (hne : ∃ u : Vec k, IsCosystolic H W u) (w : ℕ) :
    w ≤ cosystolicDistance H W ↔ ∀ u : Vec k, IsCosystolic H W u → w ≤ hammingNorm u := by
  constructor
  · intro h u hu
    exact le_trans h (csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ ⟨u, hu, rfl⟩)
  · intro h
    obtain ⟨u₀, hu₀⟩ := hne
    exact le_csInf ⟨hammingNorm u₀, ⟨u₀, hu₀, rfl⟩⟩
      (fun n ⟨v, hv, hw⟩ => hw ▸ h v hv)

/-! ## 2. A low-weight vector has only three shapes -/

/-- **A vector of weight $\le2$ has only three shapes**: the zero vector, a single-point
indicator vector, and a two-distinct-point indicator vector. (Over GF(2) every nonzero entry
is $1$, so a vector is the indicator vector of its support, see `eq_indVec_support`.) -/
theorem eq_zero_or_indVec_singleton_or_pair {n : ℕ} {u : Vec n} (h : hammingNorm u ≤ 2) :
    u = 0 ∨ (∃ a : Fin n, u = indVec ({a} : Finset (Fin n)))
      ∨ (∃ a b : Fin n, a ≠ b ∧ u = indVec ({a, b} : Finset (Fin n))) := by
  have hle2 : (support u).card ≤ 2 := by rw [weight_eq_hammingNorm]; exact h
  have hu : u = indVec (support u) := eq_indVec_support u
  rcases Nat.lt_or_ge (support u).card 2 with hlt | hge
  · have hcases : (support u).card = 0 ∨ (support u).card = 1 := by omega
    rcases hcases with h0 | h1
    · left
      rw [hu, Finset.card_eq_zero.mp h0]
      rfl
    · right; left
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      exact ⟨a, by rw [hu, ha]⟩
  · have h2 : (support u).card = 2 := by omega
    right; right
    obtain ⟨a, b, hab, hsp⟩ := Finset.card_eq_two.mp h2
    exact ⟨a, b, hab, by rw [hu, hsp]⟩

/-- **The zero vector is not a cosystolic cochain**: $\delta_1 0=0$, so $0$ lies in
$\mathrm{im}\,\delta_1$. -/
theorem not_isCosystolic_zero {ι : Type*} (H : AuxHypergraph k m) (W : ι → Finset (Fin k)) :
    ¬ IsCosystolic H W (0 : Vec k) :=
  fun h => h.2 ⟨0, by simp⟩

/-! ## 3. The main criterion: $d_1^\bullet\ge3$ is decidable -/

/-- **The main criterion**: $d_1^\bullet\ge3$ if and only if there is **no** cosystolic cochain
of weight $1$ and **no** cosystolic cochain of weight $2$. (A vector of weight $\le2$ has only
three shapes, and the zero vector is not a cosystolic cochain, so only these two ranges
remain.) -/
theorem three_le_cosystolicDistance_iff {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (hne : ∃ u : Vec k, IsCosystolic H W u) :
    3 ≤ cosystolicDistance H W
      ↔ (∀ a : Fin k, ¬ IsCosystolic H W (indVec ({a} : Finset (Fin k))))
        ∧ (∀ a b : Fin k, a ≠ b →
            ¬ IsCosystolic H W (indVec ({a, b} : Finset (Fin k)))) := by
  rw [le_cosystolicDistance_iff H W hne]
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun a b hab hb => ?_⟩
    · have := h _ ha
      rw [hammingNorm_indVec, Finset.card_singleton] at this
      omega
    · have := h _ hb
      rw [hammingNorm_indVec, Finset.card_pair hab] at this
      omega
  · rintro ⟨h1, h2⟩ u hu
    by_contra hlt
    have hle : hammingNorm u ≤ 2 := by omega
    rcases eq_zero_or_indVec_singleton_or_pair hle with h0 | ⟨a, ha⟩ | ⟨a, b, hab, hab'⟩
    · exact not_isCosystolic_zero H W (h0 ▸ hu)
    · exact h1 a (ha ▸ hu)
    · exact h2 a b hab (hab' ▸ hu)

/-- **The classification form of the criterion (fully explicit)**: if `W` covers every vertex
(so the weight-$1$ range is excluded directly by `two_le_hammingNorm_of_isCosystolic`), and
there is **no** pair of points that is "$\sim_W$-equivalent and separated by some component",
then $d_1^\bullet\ge3$.

Both conditions are decidable: the former by checking vertex by vertex, the latter by checking
pair by pair (`WSame` and component separation are both finite decisions). -/
theorem three_le_cosystolicDistance_of_pairExclusion {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (heven : IsEvenHyper H)
    (hne : ∃ u : Vec k, IsCosystolic H W u)
    (hcover : ∀ v : Fin k, ∃ w : ι, v ∈ W w)
    (hpair : ∀ a b : Fin k, a ≠ b → WSame W a b →
      ¬ ∃ S : Finset (Fin k), IsComponent H S ∧ (a ∈ S ↔ b ∉ S)) :
    3 ≤ cosystolicDistance H W := by
  rw [three_le_cosystolicDistance_iff H W hne]
  refine ⟨fun a ha => ?_, fun a b hab hb => ?_⟩
  · have h2 := two_le_hammingNorm_of_isCosystolic H W heven hcover ha
    rw [hammingNorm_indVec, Finset.card_singleton] at h2
    omega
  · exact hpair a b hab ((isCosystolic_indVec_pair_iff_component H W hab).mp hb).1
      ((isCosystolic_indVec_pair_iff_component H W hab).mp hb).2

/-! ## 4. A structural constraint: a component equal to the whole vertex set ⟹ an even weight -/

/-- **The weight must be even**: if the family of components contains a component equal to the
whole vertex set $V$, then every cosystolic cochain has even weight ($\delta_2u=0$ on that
component says "the coordinate sum is $0$", and the coordinate sum equals the parity of the
weight).

So in this case $d_1^\bullet$ can only be $0$ or $\ge4$, and **the range $3$ never occurs**. -/
theorem even_hammingNorm_of_isCosystolic_univ {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (w₀ : ι) (hW : W w₀ = Finset.univ) {u : Vec k}
    (hu : IsCosystolic H W u) : Even (hammingNorm u) := by
  have hz := congrFun hu.1 w₀
  rw [surgeryD2_mulVec_sum, hW] at hz
  simp only [Pi.zero_apply] at hz
  have hcast : ((hammingNorm u : ℕ) : ZMod 2) = 0 := by
    rw [natCast_hammingNorm_eq_sum]
    exact hz
  obtain ⟨t, ht⟩ := (CharP.cast_eq_zero_iff (ZMod 2) 2 (hammingNorm u)).mp hcast
  exact ⟨t, by omega⟩

end QECCertificates.Homology
