/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

import QECCertificates.GF2.Basis
import QECCertificates.GF2.RankEchelon

/-!
# A rank bound for arrays of permutation blocks

If every block row of a `J x L` array of `P x P` permutation blocks has the same total as
every other block row, then deleting one row from each of the last `J - 1` block rows leaves
a spanning set, so the rank is at most `J * P - (J - 1)`.

The two `by decide` facts of the original fixed-size instance -- which indices are kept, and
how many -- enter here as the hypotheses `hkeep_mem` and `hlen`, so that the combinatorial
spine is generic and an instance supplies only its own finite count.

## Main result

* `finrank_blockRow_le`

Ported from the certificate-code-parameters development, where this module is
`QuantumCodeCertificates.Codes.APMRankGeneric`; the proofs are unchanged and only the
namespace differs.
-/


open QECCertificates
open scoped BigOperators

/-! ## The parametric structural rank bound

The block-row-sum hypothesis `hsum` is what a permutation block array supplies. The proof
never opens a coordinate of a row: it recovers each deleted row from the kept ones through
the block-row identity, so the combinatorial spine stays generic and an instance supplies
only its own finite count. -/

namespace QECCertificates

/-- Row `i` of a `J * P` block-row array sits in block row `i / P`, at position `i % P`;
the positivity `hP` is all it needs. -/
def blockRowIdx {J P : ℕ} (hP : 0 < P) (i : Fin (J * P)) : Fin J × Fin P :=
  (⟨i.val / P, (Nat.div_lt_iff_lt_mul hP).mpr i.isLt⟩,
   ⟨i.val % P, Nat.mod_lt _ hP⟩)

/-- **Parametric structural rank bound for a permutation block array.**

`row : Fin J × Fin P → Vec N` is the row family of a `J`-block-row array of block width `P`.
If every block row `j` has the same total `Σ p, row (j, p)` as the distinguished block row
`hfirst` (`hsum`), and `keep` is a sublist of the block-row indices that consists exactly of
block row `hfirst` together with every index whose position differs from `hlast`
(`hkeep_mem`), of length `J * P - (J - 1)` (`hlen`), then the whole `J * P`-row family spans a
space of dimension at most `J * P - (J - 1)`: the deleted rows are recovered from the kept ones
by the block-row identity.

The proof does not open a single coordinate of a row: it is the fixed-size argument with the
two `decide` facts abstracted out. -/
theorem finrank_blockRow_le {J P N : ℕ}
    (fidx : Fin (J * P) → Fin J × Fin P)
    (row : Fin J × Fin P → Vec N)
    (keep : List (Fin J × Fin P))
    (hfirst : Fin J) (hlast : Fin P)
    (hkeep_mem : ∀ k : Fin J × Fin P, k ∈ keep ↔ k.1 = hfirst ∨ k.2 ≠ hlast)
    (hlen : keep.length = J * P - (J - 1))
    (hsum : ∀ j : Fin J,
      (∑ p : Fin P, row (j, p)) = ∑ p : Fin P, row (hfirst, p)) :
    Module.finrank (ZMod 2)
      (spanL (List.ofFn (fun i : Fin (J * P) => row (fidx i)))) ≤ J * P - (J - 1) := by
  let A := keep.map row
  have hkeep (k : Fin J × Fin P) (hk : k.1 = hfirst ∨ k.2 ≠ hlast) :
      row k ∈ spanL A := by
    exact subset_spanL (List.mem_map.mpr ⟨k, (hkeep_mem k).mpr hk, rfl⟩)
  have hbase : (∑ p : Fin P, row (hfirst, p)) ∈ spanL A := by
    exact Submodule.sum_mem _ (fun p _ => hkeep (hfirst, p) (Or.inl rfl))
  have hrow (k : Fin J × Fin P) : row k ∈ spanL A := by
    by_cases hk : k.1 = hfirst ∨ k.2 ≠ hlast
    · exact hkeep k hk
    · have hp : k.2 = hlast := by tauto
      have hrest :
          (∑ p ∈ (Finset.univ : Finset (Fin P)).erase hlast, row (k.1, p)) ∈ spanL A := by
        apply Submodule.sum_mem
        intro p hp'
        exact hkeep (k.1, p) (Or.inr (Finset.mem_erase.mp hp').1)
      have hsplit :
          row (k.1, hlast) +
            (∑ p ∈ (Finset.univ : Finset (Fin P)).erase hlast, row (k.1, p)) =
              ∑ p : Fin P, row (hfirst, p) := by
        rw [Finset.add_sum_erase Finset.univ (fun p : Fin P => row (k.1, p))
          (Finset.mem_univ hlast)]
        exact hsum k.1
      have hsolve : row (k.1, hlast) =
          (∑ p : Fin P, row (hfirst, p)) +
            (∑ p ∈ (Finset.univ : Finset (Fin P)).erase hlast, row (k.1, p)) := by
        have h := congrArg
          (fun z : Vec N => z +
            (∑ p ∈ (Finset.univ : Finset (Fin P)).erase hlast, row (k.1, p))) hsplit
        simpa only [add_assoc, QECCertificates.add_self, add_zero] using h
      have heq : k = (k.1, hlast) := Prod.ext rfl hp
      rw [heq, hsolve]
      exact Submodule.add_mem _ hbase hrest
  have hmem : ∀ v ∈ List.ofFn (fun i : Fin (J * P) => row (fidx i)),
      v ∈ spanL A := by
    intro v hv
    rcases List.mem_ofFn.mp hv with ⟨i, rfl⟩
    exact hrow (fidx i)
  have h := finrank_spanL_le_of_mem_of_subset (A := A) hmem
  simpa only [A, List.length_map, hlen] using h

end QECCertificates
