/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

import QECCertificates.Codes.ClosureTheorem

/-!
# The latitude a decoder keeps at a Hamming check matrix

Where a decoder keeps latitude, in the same abstraction as the closure theorem: a check
matrix whose columns are all the nonzero width-`r` vectors, with no code-specific input.

The closure theorem fixes the same-type class. Under exhaustion the XOR of two distinct
columns is a column, so a weight-1 decoder reads a same-type pair as one single fault,
corrects a third location, and leaves a zero-syndrome triple. What a decoder still owns is
the cross-type class, and this module records the two facts that settle it.

* **(L1) three readings.** A syndrome no single fault reaches has two sector syndromes that
  are nonzero and unequal; writing them $s_1$ and $s_2$, three weight-2 operators carry it,
  namely the $Z$-at-$s_1$ with $X$-at-$s_2$ pair, the $Y$-at-$s_1$ with
  $X$-at-$\mathrm{Xor}(s_1,s_2)$ pair, and the $Y$-at-$s_2$ with
  $Z$-at-$\mathrm{Xor}(s_1,s_2)$ pair.
* **(L2) the separators.** Any two of the three differ by one of the three operators
  supported on the zero-sum triple $\{s_1, s_2, s_1 \oplus s_2\}$, each of weight three
  with trivial syndrome, which is a logical operator whenever every nontrivial stabilizer
  has weight at least four. The three readings therefore sit one to a logical class: a
  decoder correcting one of them leaves the other two as logical failures, whichever of
  the three it picks.

The two facts together are why the family coefficient is decoder-independent: the same-type
pairs have no latitude at all, and the cross-type pairs have a three-way choice that trades
one reading for another rather than removing a failure.

**Boundary.** This module does not show that the three are the minimum-weight readings,
which is what makes the cost two of three rather than fewer, and it does not compute the
family's $7/9$ fraction. Those are the enumeration in the development this module comes
from, together with its deposit; the structural facts above are the spine that enumeration
is checked against.

Ported from the measurement-free QEC development, where this module is
`QECFormal.HammingLatitude`; the proofs are unchanged and only the namespace differs.
-/

namespace QECCertificates.HammingLatitude

open QECCertificates.ClosureTheorem

/-- The syndrome a support list presents: the XOR of its members, on a register
    of width `r` (the empty support presents the zero syndrome). -/
def suppXor (r : Nat) : List (List Bool) → List Bool
  | [] => Zeros r
  | v :: vs => Xor v (suppXor r vs)

/-- A reading is a pair of supports, the Z-support and the X-support of a
    Pauli; its syndrome is the pair of their XORs. -/
def synd (r : Nat) (p : List (List Bool) × List (List Bool)) :
    List Bool × List Bool :=
  (suppXor r p.1, suppXor r p.2)

theorem suppXor_singleton {r : Nat} {v : List Bool} (h : v.length = r) :
    suppXor r [v] = v := by
  show Xor v (Zeros r) = v
  rw [← h]
  exact xor_zeros_right v

theorem suppXor_pair {r : Nat} {v w : List Bool} (_hv : v.length = r)
    (hw : w.length = r) : suppXor r [v, w] = Xor v w := by
  show Xor v (Xor w (Zeros r)) = Xor v w
  rw [← hw]
  exact congrArg (Xor v) (xor_zeros_right w)

/-- The third column of the triple, the one exhaustion guarantees. -/
theorem third_width {r : Nat} {s₁ s₂ : List Bool} (h₁ : s₁.length = r)
    (h₂ : s₂.length = r) : (Xor s₁ s₂).length = r := by
  rw [xor_length (by omega : s₁.length = s₂.length)]
  exact h₁

theorem third_nonzero {s₁ s₂ : List Bool} (h : s₁.length = s₂.length)
    (hne : s₁ ≠ s₂) : NonzeroVec (Xor s₁ s₂) := by
  intro h0
  have h0' : Xor s₁ s₂ = Zeros s₁.length := by rw [h0, xor_length h]
  exact hne ((xor_eq_zeros h).mp h0')

theorem third_ne_left {s₁ s₂ : List Bool} (h : s₁.length = s₂.length)
    (h₂ : NonzeroVec s₂) : Xor s₁ s₂ ≠ s₁ := by
  intro heq
  exact h₂ (xor_eq_left_imp_zeros h heq)

theorem third_ne_right {s₁ s₂ : List Bool} (h : s₁.length = s₂.length)
    (h₁ : NonzeroVec s₁) : Xor s₁ s₂ ≠ s₂ := by
  intro heq
  exact h₁ (xor_eq_right_imp_zeros h heq)

/-! ## (L1) Three readings share the syndrome. -/

/-- **(L1) Three readings.** Write `t` for `Xor s₁ s₂`. The three weight-2
    operators of the latitude, `Z@s₁` with `X@s₂`, `Y@s₁` with `X@t`, and
    `Y@s₂` with `Z@t`, all present the syndrome `(s₁, s₂)`: a decoder reading
    that syndrome sees three candidates and no way, from the syndrome, to
    prefer one. -/
theorem readings_share_syndrome (r : Nat) (s₁ s₂ : List Bool)
    (h₁ : s₁.length = r) (h₂ : s₂.length = r) :
    synd r ([s₁], [s₂]) = (s₁, s₂) ∧
    synd r ([s₁], [s₁, Xor s₁ s₂]) = (s₁, s₂) ∧
    synd r ([s₂, Xor s₁ s₂], [s₂]) = (s₁, s₂) := by
  have hlen : s₁.length = s₂.length := by omega
  have hA : (Xor s₁ s₂).length = r := third_width h₁ h₂
  have hX : Xor s₁ (Xor s₁ s₂) = s₂ := xor_cancel hlen
  have hZ : Xor s₂ (Xor s₁ s₂) = s₁ := by
    rw [xor_comm s₁ s₂]
    exact xor_cancel hlen.symm
  refine ⟨?_, ?_, ?_⟩
  · show (suppXor r [s₁], suppXor r [s₂]) = (s₁, s₂)
    rw [suppXor_singleton h₁, suppXor_singleton h₂]
  · show (suppXor r [s₁], suppXor r [s₁, Xor s₁ s₂]) = (s₁, s₂)
    rw [suppXor_singleton h₁, suppXor_pair h₁ hA, hX]
  · show (suppXor r [s₂, Xor s₁ s₂], suppXor r [s₂]) = (s₁, s₂)
    rw [suppXor_pair h₂ hA, suppXor_singleton h₂, hZ]

/-! ## (L2) The separators lie on the zero-sum triple. -/

/-- **(L2) The separators.** The three operators supported on the triple
    `{s₁, s₂, s₁⊕s₂}` are the pairwise separators of the three readings, and
    each carries the trivial syndrome: the X-type one, the Z-type one, and the
    Y-type one. Under exhaustion the triple is a zero-sum set of three distinct
    locations, the weight-3 dependency of the Steiner structure, so each
    separator is a logical operator whenever every nontrivial stabilizer has
    weight at least four. -/
theorem separators_trivial (r : Nat) (s₁ s₂ : List Bool)
    (h₁ : s₁.length = r) (h₂ : s₂.length = r) :
    suppXor r [s₁, s₂, Xor s₁ s₂] = Zeros r ∧
    Xor s₁ (Xor s₂ (Xor s₁ s₂)) = Zeros r := by
  have hlen : s₁.length = s₂.length := by omega
  have hA : (Xor s₁ s₂).length = r := third_width h₁ h₂
  have htriple : Xor s₁ (Xor s₂ (Xor s₁ s₂)) = Zeros r :=
    Eq.trans (triple_xor_zero hlen) (by rw [h₁])
  refine ⟨?_, htriple⟩
  show Xor s₁ (Xor s₂ (Xor (Xor s₁ s₂) (Zeros r))) = Zeros r
  rw [xor_zeros_width_right hA]
  exact htriple

/-- The three locations of the triple are distinct, so the separators have
    weight three and not less. -/
theorem triple_nodup {r : Nat} {s₁ s₂ : List Bool}
    (h₁ : s₁.length = r) (h₂ : s₂.length = r)
    (hn₁ : NonzeroVec s₁) (hn₂ : NonzeroVec s₂) (hne : s₁ ≠ s₂) :
    [s₁, s₂, Xor s₁ s₂].Nodup := by
  have hlen : s₁.length = s₂.length := by omega
  have h1t : s₁ ≠ Xor s₁ s₂ := fun h => third_ne_left hlen hn₂ h.symm
  have h2t : s₂ ≠ Xor s₁ s₂ := fun h => third_ne_right hlen hn₁ h.symm
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr
    ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩⟩⟩
  · intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact hne h
    · exact h1t (List.mem_singleton.mp h)
  · intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact h2t h
    · exact List.not_mem_nil h
  · intro hm
    exact List.not_mem_nil hm

/-- **(Capstone)** A syndrome no single fault reaches, its two sector syndromes
    nonzero and unequal, is carried by the three weight-2 readings of (L1), and
    any two of them differ by one of the three weight-3 separators of (L2): the
    decoder's whole latitude is which of the three it names, and no choice
    removes the other two as logical failures. -/
theorem latitude (r : Nat) (s₁ s₂ : List Bool)
    (h₁ : s₁.length = r) (h₂ : s₂.length = r)
    (hn₁ : NonzeroVec s₁) (hn₂ : NonzeroVec s₂) (hne : s₁ ≠ s₂) :
    synd r ([s₁], [s₂]) = (s₁, s₂) ∧
    synd r ([s₁], [s₁, Xor s₁ s₂]) = (s₁, s₂) ∧
    synd r ([s₂, Xor s₁ s₂], [s₂]) = (s₁, s₂) ∧
    suppXor r [s₁, s₂, Xor s₁ s₂] = Zeros r ∧
    [s₁, s₂, Xor s₁ s₂].Nodup := by
  have hrs := readings_share_syndrome r s₁ s₂ h₁ h₂
  have hsep := separators_trivial r s₁ s₂ h₁ h₂
  exact ⟨hrs.1, hrs.2.1, hrs.2.2, hsep.1,
         triple_nodup h₁ h₂ hn₁ hn₂ hne⟩

end QECCertificates.HammingLatitude
