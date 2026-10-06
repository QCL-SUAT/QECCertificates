/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.Basic

/-!
# Dot-product duality over GF(2): the orthogonal complement of the left kernel

This module is the single home of the orthogonal-complement characterisation of the column
space of a GF(2) matrix. Over `ZMod 2` the standard dot product is non-degenerate, so the
column space of `M` is exactly the set of vectors orthogonal to the left kernel of `M`:

$$v \in \operatorname{range}(M.\mathrm{mulVecLin})
  \quad\Longleftrightarrow\quad
  \mu\cdot v = 0 \ \text{for every } \mu \text{ with } M^{\mathsf T}\mu = 0.$$

The statement is not proved anywhere else in the library: the call sites elsewhere state
their specializations by referring here, so a correction is made in one place.

## Main results

* `dot_mulVec_transpose`: the transpose law of the dot product and matrix-vector
  multiplication, $\mu\cdot(My)=(M^{\mathsf T}\mu)\cdot y$.
* `eq_zero_of_forall_dot_eq_zero`: non-degeneracy of the dot product on GF(2) vectors.
* `mem_range_mulVecLin_iff_forall_dot_eq_zero`: the orthogonal-complement characterisation
  of `LinearMap.range M.mulVecLin`.
-/

namespace QECCertificates

open scoped BigOperators

open _root_.Matrix

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- The transpose law of the dot product and `mulVec`:
$\mu\cdot(My)=(M^{\mathsf T}\mu)\cdot y$. -/
theorem dot_mulVec_transpose {M : Matrix α β (ZMod 2)} (μ : α → ZMod 2) (y : β → ZMod 2) :
    μ ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ μ) ⬝ᵥ y := by
  rw [dotProduct_mulVec]
  simpa using congrArg (· ⬝ᵥ y) (Matrix.vecMul_transpose Mᵀ μ)

/-- Non-degeneracy: a vector whose dot product with every vector is zero is zero. -/
theorem eq_zero_of_forall_dot_eq_zero {z : α → ZMod 2}
    (h : ∀ y : α → ZMod 2, z ⬝ᵥ y = 0) : z = 0 := by
  funext c
  have h1 := h (Pi.single c 1)
  simpa [dotProduct_single_one] using h1

/-- **The orthogonal-complement characterisation of `range`**: the column space $=$ the
"orthogonal complement" of the left kernel. -/
theorem mem_range_mulVecLin_iff_forall_dot_eq_zero {M : Matrix α β (ZMod 2)}
    (v : α → ZMod 2) :
    v ∈ LinearMap.range M.mulVecLin
      ↔ ∀ μ : α → ZMod 2, Mᵀ *ᵥ μ = 0 → μ ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ μ hμ
    rw [Matrix.mulVecLin_apply, dot_mulVec_transpose, hμ, zero_dotProduct]
  · intro h
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := LinearMap.range M.mulVecLin),
      Submodule.mem_dualCoannihilator]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    set μ : α → ZMod 2 := (dotProductEquiv (ZMod 2) α).symm φ with hμdef
    have hφeq : ∀ x : α → ZMod 2, φ x = μ ⬝ᵥ x := by
      intro x
      have h1 : (dotProductEquiv (ZMod 2) α) μ = φ := by
        rw [hμdef, LinearEquiv.apply_symm_apply]
      rw [← h1]
      rfl
    have hμ : Mᵀ *ᵥ μ = 0 := by
      apply eq_zero_of_forall_dot_eq_zero
      intro y
      have hmem : M *ᵥ y ∈ LinearMap.range M.mulVecLin :=
        ⟨y, by rw [Matrix.mulVecLin_apply]⟩
      have hz := hφ (M *ᵥ y) hmem
      rwa [hφeq (M *ᵥ y), dot_mulVec_transpose] at hz
    rw [hφeq v]
    exact h μ hμ

end QECCertificates
