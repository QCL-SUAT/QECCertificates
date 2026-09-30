/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB144Literal
import QECCertificates.Codes.BB144Rank
import QECCertificates.Codes.FoldTransversal

/-!
# The **translation symmetry** of BB $[[144,12,12]]$ (first step of the symmetry-breaking route)

## What this branch needs

The symmetry-breaking encoder adds lexicographic orbit-representative constraints to the
SAT encoding of BB144, which in measurements cuts the number of addition steps in its own
certificates by a factor of four to seven. The **soundness** of that route (UNSAT after
breaking implies UNSAT of the original) rests on one thing: every element of the
translation group $G=Z_{12}\times Z_6$ induces a permutation of the physical bits that
**simultaneously** preserves

* weight (the support of $x$ is transported, so the weight is unchanged);
* $\mathrm{rowsp}(H_X)$ and $\mathrm{rowsp}(H_Z)$, hence $\ker H_X$ and $\ker H_Z$;
* the pairing $x\cdot w$, hence also the condition of being nontrivial.

Once all three are preserved, $(x,w)\mapsto(g\cdot x,\,g\cdot w)$ is a **symmetry action**
of the code, and taking the lexicographic minimum of each orbit is meaningful. This
module proves the three in the kernel.

## Division of labour with the existing modules: almost nothing is re-proved here

`Codes/FoldTransversal.lean` has already proved the **general form** of these three facts,
and states them for an **arbitrary** bit permutation: `hammingNorm_permVec` (weight),
`dotProduct_permVec` (pairing), `permVec_mem_spanL_iff` (row space, which needs the row
lists to map into themselves in both directions) and `inKerB_permVec` (kernel
membership). So the **only** new content in this module is one thing: **a translation
permutation maps every check row to a check row** (the `permVec_bb144Trans_hxRow`
family). Everything else instantiates those general lemmas.

## Why the symbolic route

A kernel reduction of the dot product on a 144-wide literal matrix takes about 5 minutes
and peaks at several gigabytes, and the `olean` of `Codes/BB144Literal` is 90 MB. So
$72\times144$ matrices are **not** handled by `by decide`; instead this module uses the
**entrywise** lemmas already prepared in `Codes/BB144Distance.lean`,
`LE_X_entry_zero/one` and `LE_Z_entry_zero/one` (they write an entry as the group-ring
monomial `grossA (h - e₇₂ g)`), and relabels at the level of **group elements**. A
translation sends the column $(h,b)$ to $(h-t,b)$, so

$$\big(\text{row }k\big)(h-t,\,b)\;=\;\mathrm{gross}\big(h-t-e_g k\big)
\;=\;\mathrm{gross}\big(h-(e_g k+t)\big)\;=\;\big(\text{row }e_g^{-1}(e_g k+t)\big)(h,\,b),$$

that is, **row $k$ moves to row $e_g^{-1}(e_g k+t)$**, a purely algebraic identity with no
enumeration.

**The index is the same on both sides** (`e₇₂⁻¹(e₇₂ k + t)`), even though the entries are
`h - e₇₂ k` on the X side and `e₇₂ k - h` on the Z side: in both places `t` lands on the
side that is being subtracted from. This step was written the wrong way once (the Z side
was misrecorded as `-t`), so both places end with `abel` rather than relying on the eye.

## Trusted base

Throughout, the only use of `by decide` is on **small group-level equations** (the
two-valued split of `Fin 2`); zero `sorry`, zero custom axioms, zero `native_decide`.
-/

namespace QECCertificates

open QECCertificates.BB144Distance

open _root_.Matrix

-- `GrossGroup`（`= ZMod 12 × ZMod 6`）、`grossA`/`grossB` 都在上游 QEC 的命名空间里
open Quantum.Stabilizer.Homological.BB

/-- `Fin 2` has exactly two elements. This is a named lemma so that the branches below
receive the **literals** `0`/`1`: `fin_cases` produces the un-beta-reduced shape
`(fun i => i) ⟨0, ⋯⟩`, whereas the left-hand side of `LE_X_entry_zero` is the literal
`0`, which `rw` would fail to match syntactically. -/
theorem fin2_eq_zero_or_one (b : Fin 2) : b = 0 ∨ b = 1 := by
  revert b; decide

/-- **Translation permutation**: shifts the group element of a physical bit `c` (read
through `e144` as a `(group element, block)` pair) by `t`, leaving the block fixed.

These are the 72 permutations that the external symmetry-breaking encoder generates: its
listing writes them by decimal index into `Fin 144` and this definition writes them by the
group structure of the code, but the two are the same permutation. -/
noncomputable def bb144Trans (t : GrossGroup) : Equiv.Perm (Fin 144) where
  toFun c := e144.symm ((e144 c).1 + t, (e144 c).2)
  invFun c := e144.symm ((e144 c).1 - t, (e144 c).2)
  left_inv c := by
    dsimp only
    simp only [Equiv.apply_symm_apply]
    have h : ((e144 c).1 + t - t, (e144 c).2) = e144 c := by simp
    rw [h, Equiv.symm_apply_apply]
  right_inv c := by
    dsimp only
    simp only [Equiv.apply_symm_apply]
    have h : ((e144 c).1 - t + t, (e144 c).2) = e144 c := by simp
    rw [h, Equiv.symm_apply_apply]

/-- The inverse of a translation permutation is the reverse translation. This is what
lets the obligation that the row lists map into themselves in both directions be
discharged once. -/
theorem bb144Trans_symm_eq (t : GrossGroup) : (bb144Trans t).symm = bb144Trans (-t) := by
  apply Equiv.ext
  intro c
  simp only [bb144Trans, Equiv.coe_fn_mk, Equiv.symm_mk, sub_eq_add_neg]

/-- An explicit form for a translation permutation acting on a **column**: `(h,b) ↦ (h+t,b)`. -/
theorem bb144Trans_apply (t g : GrossGroup) (b : Fin 2) :
    bb144Trans t (e144.symm (g, b)) = e144.symm (g + t, b) := by
  simp only [bb144Trans, Equiv.coe_fn_mk, Equiv.apply_symm_apply]

/-- An explicit form for the inverse permutation acting on a **column**: `(h,b) ↦ (h-t,b)`.
Kernel membership and the row space use this branch (`permVec π v i = v (π.symm i)`). -/
theorem bb144Trans_symm_apply (t g : GrossGroup) (b : Fin 2) :
    (bb144Trans t).symm (e144.symm (g, b)) = e144.symm (g - t, b) := by
  simp only [bb144Trans, Equiv.coe_fn_mk, Equiv.symm_mk, Equiv.apply_symm_apply]

/-! ## 1. The core: a translation moves row `k` to row `e₇₂⁻¹(e₇₂ k + t)`

Split by block (`b = 0` / `b = 1`) and combine afterwards: once split, the second
component of a column is a **literal**, which is what lets
`LE_X_entry_zero`/`LE_X_entry_one` match syntactically. -/

theorem permVec_bb144Trans_hxRow_apply_zero (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HxRow k) (e144.symm (g, 0))
      = bb144HxRow (e72.symm (e72 k + t)) (e144.symm (g, 0)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HxRow, bb144HxRow, bb144Hx_eq_LE_X,
      LE_X_entry_zero, LE_X_entry_zero, Equiv.apply_symm_apply]
  congr 1
  abel

theorem permVec_bb144Trans_hxRow_apply_one (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HxRow k) (e144.symm (g, 1))
      = bb144HxRow (e72.symm (e72 k + t)) (e144.symm (g, 1)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HxRow, bb144HxRow, bb144Hx_eq_LE_X,
      LE_X_entry_one, LE_X_entry_one, Equiv.apply_symm_apply]
  congr 1
  abel

/-- **The core entrywise identity** (X side). -/
theorem permVec_bb144Trans_hxRow_apply (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) (b : Fin 2) :
    permVec (bb144Trans t) (bb144HxRow k) (e144.symm (g, b))
      = bb144HxRow (e72.symm (e72 k + t)) (e144.symm (g, b)) := by
  rcases fin2_eq_zero_or_one b with rfl | rfl
  · exact permVec_bb144Trans_hxRow_apply_zero t k g
  · exact permVec_bb144Trans_hxRow_apply_one t k g

/-- **The core identity in function form**: row `k` moves to row `e₇₂⁻¹(e₇₂ k + t)`
(X side). -/
theorem permVec_bb144Trans_hxRow (t : GrossGroup) (k : Fin (12 * 6)) :
    permVec (bb144Trans t) (bb144HxRow k)
      = bb144HxRow (e72.symm (e72 k + t)) := by
  funext c
  conv_lhs => rw [← Equiv.symm_apply_apply e144 c]
  conv_rhs => rw [← Equiv.symm_apply_apply e144 c]
  exact permVec_bb144Trans_hxRow_apply t k (e144 c).1 (e144 c).2

theorem permVec_bb144Trans_hzRow_apply_zero (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HzRow k) (e144.symm (g, 0))
      = bb144HzRow (e72.symm (e72 k + t)) (e144.symm (g, 0)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HzRow, bb144HzRow, bb144Hz_eq_LE_Z,
      LE_Z_entry_zero, LE_Z_entry_zero, Equiv.apply_symm_apply]
  congr 1
  abel

theorem permVec_bb144Trans_hzRow_apply_one (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) :
    permVec (bb144Trans t) (bb144HzRow k) (e144.symm (g, 1))
      = bb144HzRow (e72.symm (e72 k + t)) (e144.symm (g, 1)) := by
  rw [permVec_apply, bb144Trans_symm_apply, bb144HzRow, bb144HzRow, bb144Hz_eq_LE_Z,
      LE_Z_entry_one, LE_Z_entry_one, Equiv.apply_symm_apply]
  congr 1
  abel

/-- **The core entrywise identity** (Z side). Note that the entries of `LE_Z` are
`e₇₂ g - h`, differing from the X side by a sign, so the rearrangement takes a different
route: the same statement, a different algebraic form, and no shared proof text. -/
theorem permVec_bb144Trans_hzRow_apply (t : GrossGroup) (k : Fin (12 * 6))
    (g : GrossGroup) (b : Fin 2) :
    permVec (bb144Trans t) (bb144HzRow k) (e144.symm (g, b))
      = bb144HzRow (e72.symm (e72 k + t)) (e144.symm (g, b)) := by
  rcases fin2_eq_zero_or_one b with rfl | rfl
  · exact permVec_bb144Trans_hzRow_apply_zero t k g
  · exact permVec_bb144Trans_hzRow_apply_one t k g

/-- **The core identity in function form** (Z side). -/
theorem permVec_bb144Trans_hzRow (t : GrossGroup) (k : Fin (12 * 6)) :
    permVec (bb144Trans t) (bb144HzRow k)
      = bb144HzRow (e72.symm (e72 k + t)) := by
  funext c
  conv_lhs => rw [← Equiv.symm_apply_apply e144 c]
  conv_rhs => rw [← Equiv.symm_apply_apply e144 c]
  exact permVec_bb144Trans_hzRow_apply t k (e144 c).1 (e144 c).2

/-! ## 2. The row lists map into themselves (both directions)

`permVec_mem_spanL_iff` asks for `∀ r ∈ L, permVec π r ∈ L` **and**
`∀ r ∈ L, permVec π.symm r ∈ L`. Both directions are needed: the reverse one shows that
an image in the row space implies a preimage in the row space, which is half of the
statement that the image is still a **nontrivial** operator. -/

theorem bb144_permVec_hxRow_mem (t : GrossGroup) {r : Vec 144} (hr : r ∈ bb144Rx) :
    permVec (bb144Trans t) r ∈ bb144Rx := by
  rw [bb144Rx, List.mem_ofFn] at hr ⊢
  obtain ⟨k, rfl⟩ := hr
  exact ⟨e72.symm (e72 k + t), (permVec_bb144Trans_hxRow t k).symm⟩

theorem bb144_permVec_hzRow_mem (t : GrossGroup) {r : Vec 144} (hr : r ∈ bb144Rz) :
    permVec (bb144Trans t) r ∈ bb144Rz := by
  rw [bb144Rz, List.mem_ofFn] at hr ⊢
  obtain ⟨k, rfl⟩ := hr
  exact ⟨e72.symm (e72 k + t), (permVec_bb144Trans_hzRow t k).symm⟩

/-! ## 3. The three assertions

The translation permutation of a group element `t` preserves weight, both row spaces and
the pairing. All three instantiate general lemmas of `Codes/FoldTransversal.lean`; there
is **no new mathematics**. -/

/-- **Preserves weight**: a translation leaves the Hamming weight of `v` unchanged. -/
theorem bb144Trans_hammingNorm (t : GrossGroup) (v : Vec 144) :
    hammingNorm (permVec (bb144Trans t) v) = hammingNorm v :=
  hammingNorm_permVec _ _

/-- **Preserves the pairing**: a translation leaves $x\cdot w$ unchanged. -/
theorem bb144Trans_dotProduct (t : GrossGroup) (v w : Vec 144) :
    (permVec (bb144Trans t) v) ⬝ᵥ (permVec (bb144Trans t) w) = v ⬝ᵥ w :=
  dotProduct_permVec _ _ _

/-- **Preserves the X-side row space**: a translation is an automorphism of the code
(X side). -/
theorem bb144Trans_preserves_spanL_x (t : GrossGroup) {v : Vec 144}
    (hv : v ∈ spanL bb144Rx) : permVec (bb144Trans t) v ∈ spanL bb144Rx :=
  permVec_mem_spanL _ (fun _ hr => subset_spanL (bb144_permVec_hxRow_mem t hr)) hv

/-- **Preserves the Z-side row space**: a translation is an automorphism of the code
(Z side). -/
theorem bb144Trans_preserves_spanL_z (t : GrossGroup) {v : Vec 144}
    (hv : v ∈ spanL bb144Rz) : permVec (bb144Trans t) v ∈ spanL bb144Rz :=
  permVec_mem_spanL _ (fun _ hr => subset_spanL (bb144_permVec_hzRow_mem t hr)) hv

/-- **Row-space membership is invariant in both directions** (X side): the image lies in
the row space if and only if the preimage does. The reverse direction comes from
`t ↦ -t` (`bb144Trans_symm_eq`). -/
theorem bb144Trans_mem_spanL_iff_x (t : GrossGroup) {v : Vec 144} :
    permVec (bb144Trans t) v ∈ spanL bb144Rx ↔ v ∈ spanL bb144Rx :=
  permVec_mem_spanL_iff _ (fun _ hr => bb144_permVec_hxRow_mem t hr)
    (fun r hr => by
      rw [bb144Trans_symm_eq]
      exact bb144_permVec_hxRow_mem (-t) hr)

/-- **Row-space membership is invariant in both directions** (Z side). -/
theorem bb144Trans_mem_spanL_iff_z (t : GrossGroup) {v : Vec 144} :
    permVec (bb144Trans t) v ∈ spanL bb144Rz ↔ v ∈ spanL bb144Rz :=
  permVec_mem_spanL_iff _ (fun _ hr => bb144_permVec_hzRow_mem t hr)
    (fun r hr => by
      rw [bb144Trans_symm_eq]
      exact bb144_permVec_hzRow_mem (-t) hr)

/-! ## 4. Group structure: 72 elements

The symmetry-breaking encoder takes either all 72 translations of $Z_{12}\times Z_6$ or
just two generators of it. Both are instances of the same `bb144Trans t` here: that step
of the tooling only **picks a few `t`**, and involves no new mathematics. -/

/-- A composite of translation permutations is again a translation permutation
(`bb144Trans s ≫ bb144Trans t = bb144Trans (s+t)`). This is the algebraic content of the
statement that the group consists of exactly 72 translations. -/
theorem bb144Trans_trans (s t : GrossGroup) :
    (bb144Trans s).trans (bb144Trans t) = bb144Trans (s + t) := by
  apply Equiv.ext
  intro c
  simp only [Equiv.trans_apply, bb144Trans, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
             add_assoc]

end QECCertificates
