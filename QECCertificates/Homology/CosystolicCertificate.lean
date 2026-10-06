/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.CosystolicCharacterization
import QECCertificates.GF2.LowerBound

/-!
# Exact 1-cosystolic distance from the existing certificate engine

This is an interface, not a polynomial-time algorithm and not a closed form.
The upper witness makes the admissible set nonempty, so the `sInf ∅ = 0`
convention can never be confused with the matrix-distance sentinel `k + 1`.
No enumeration or external solver is run by this module.
-/

namespace QECCertificates.Homology

open QECCertificates _root_.Matrix

/-- The columns of δ₁ are the rows of δ₁ᵀ. -/
theorem surgeryD1_transpose_rowSpace {k m : ℕ} (H : AuxHypergraph k m) :
    (surgeryD1 H).transpose.rowSpace = LinearMap.range (surgeryD1 H).toLin' := by
  rw [Matrix.range_toLin']
  rfl

theorem isCosystolic_iff_matrix_logical {k m r : ℕ} (H : AuxHypergraph k m)
    (W : Fin r → Finset (Fin k)) (u : Vec k) :
    IsCosystolic H W u ↔
      u ∈ LinearMap.ker (surgeryD2 W).toLin' ∧
        u ∉ (surgeryD1 H).transpose.rowSpace := by
  rw [surgeryD1_transpose_rowSpace]
  simp only [IsCosystolic, LinearMap.mem_ker, Matrix.toLin'_apply,
    LinearMap.mem_range]

/-- **The two declarations bound the same set**: the set of $1$-cosystolic cochains is
exactly the set of vectors that lie in the kernel of `surgeryD2 W` and outside the row
space of `(surgeryD1 H)ᵀ` — that is, the `undetectableSet` of the shared package
`GF2/Witness`.

So the two quantities are not two problems: **both are the minimum weight over "the
kernel of one explicit matrix minus the row space of another explicit matrix"**. They
differ only in the convention for the empty set (see
`sInf_image_undetectableSet_eq_minWeight`). -/
theorem isCosystolic_iff_undetectable {k m r : ℕ} (H : AuxHypergraph k m)
    (W : Fin r → Finset (Fin k)) (u : Vec k) :
    IsCosystolic H W u ↔ u ∈ undetectableSet (surgeryD2 W) (surgeryD1 H).transpose := by
  rw [isCosystolic_iff_matrix_logical]
  simp only [undetectableSet, Set.mem_sdiff, SetLike.mem_coe]

/-- A checked empty lower-candidate list plus one upper witness fixes the distance. -/
theorem cosystolicDistance_eq_of_lightCand {k m r d : ℕ}
    (H : AuxHypergraph k m) (W : Fin r → Finset (Fin k))
    (u : Vec k) (hu : IsCosystolic H W u) (hw : hammingNorm u = d)
    (hlow : lightCand (surgeryD2 W) (surgeryD1 H).transpose d = []) :
    cosystolicDistance H W = d := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun t _ => Nat.zero_le t⟩ ⟨u, hu, hw⟩
  · apply (le_cosystolicDistance_iff H W ⟨u, hu⟩ d).mpr
    intro v hv
    obtain ⟨hker, hnot⟩ := (isCosystolic_iff_matrix_logical H W v).mp hv
    exact lowerHyp_of_lightCand_nil (surgeryD2 W) (surgeryD1 H).transpose hlow
      v hker hnot

end QECCertificates.Homology
