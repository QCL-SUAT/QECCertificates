/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.HGPToricFamily
import QECCertificates.Codes.SeparationClosedForm
import QECCertificates.GF2.Witness

/-!
# The **spacelike side** of the toric family (both distances of the deformed code $=m$, with a surviving witness of weight $m$)

The remaining spacelike gap was this statement:

> the spacelike side of the toric family: the deformed code of that family needs a
> surviving witness of weight $m$, which has not been computed inside the kernel
> (BB24 closes because it is a single instance whose two distances were both computed).

This module closes that statement and makes the counting core of W–Y Lemma 2 a separate
theorem. **First, the model.**

The gauging **representation layer** used here, and in the exploration scripts that
accompanied the companion paper, attaches the measured logical operator $\ell$ as a new
row to the X checks (`deformXRows` in `Codes/Gauging.lean`:
$H_X' = H_X + [\ell]$, $H_Z' = H_Z$). The **circuit-level** construction of the
companion paper additionally carries ancillas (the Gauss law $A_v$, the flux checks
$B_p$, the checks $\tilde s_i$ deformed along a perfect matching), and this library
realizes it instance by instance in `Codes/BB24Gauged.lean` and
`Codes/SeparationInstances.lean`. Every conclusion of this module lies inside the
**representation-layer model**, the model shared by this library and those exploration
scripts, and not inside the circuit-level model.

## 1. A general fact: appending one check row only shrinks the set of logical operators

`le_minWeight_of_lower_appendRow` (appending a row on the X side: the kernel shrinks) and
`le_minWeight_of_lower_rowSpace_appendRow` (appending a row on the Z side: the row space
grows) show that $\ker M_1 \setminus \mathrm{row}\,M_2$ can only shrink in either
direction, so **any** per-operator lower bound that holds for the code is inherited by
the deformed code. This is the general argument that gauging does not conjure a lighter
logical operator out of nothing, and in the representation-layer model it holds for
**every** code. Lemma 2 of the companion paper is not covered by it: in the
circuit-level model an ancilla can let an operator of weight 1 survive, and the
failing-side `sepFail_lightLogical` in `Codes/SeparationInstances.lean` is the
kernel-level evidence for that phenomenon.

## 2. The surviving witness of the toric family and the two distances $=m$

The measured logical operator is `hgpToricZW m`, an X-type logical operator of weight $m$:
a kernel vector of `H_Z` that does not lie in the row space of `H_X`. The pre-existing
X-side witness `hgpToricXW m` pairs with it to $1$ and is **killed**, since it no longer
commutes with $\ell$; `toricXWFin_not_mem_ker` is the machine-checked form of that.
What **survives** is the row witness of the right block, `toricRW m s₀`: it has weight
$m$, it commutes with $\ell$ because its support is disjoint from that of $\ell$
(`dot_toricRW_toricZW`), and it still does not lie in the row space of `H_Z`. On the Z
side the column witness `toricRWZ m t₀` of the right block survives for the same reason.
All three facts about the right block, two kernel memberships and one non-membership in
the row space, use the fact that the **column** sums of `cycMat` are even
(`cycMat_col_sum`; the pre-existing witness of the left block uses the row sums, and
`cycMat` is not symmetric, so neither statement implies the other):

* `toric_family_deformed_dx`: $\mathrm{dx}(H_X', H_Z) = m$;
* `toric_family_deformed_dz`: $\mathrm{dz}(H_Z, H_X') = m$.

The two bounds come from **different** arguments: the lower bound is the cleaning theorem
for the base code (`hgp_toric_family`) together with a general containment, and the upper
bound is the explicit surviving witness of weight $m$ together with a dual witness.

## 3. The spacelike side of the closed separation form

`toric_family_space_bound` connects Section 2 back to the spacelike bound hypothesis of
`separation_closed`, the bound $\min(\eta,1)\cdot d \le \text{spaceDist}$ of
Lemma 2 of the companion paper, which on this family is no longer a hypothesis.
`toric_family_separation_closed_spatial` is the final form.

## 4. The counting core of W–Y Lemma 2 (one half of the lemma; an honest list follows)

`space_fault_weight_ge_of_expansion` machine-checks the **counting step** of Methods
Lemma 2 of the companion paper in isolation. Cleaning, that is multiplying by
$\prod_{v\in T}A_v$, turns the vertex support $S$ into $S\triangle T$ and the added
edge support is the cut $\partial T$; after passing to a representative with
$|T|\le |V|/2$, Cheeger constant $\ge1$, which is C1 of this library, gives
$|T|\le|\partial T|$; and then "after cleaning, the operator restricted to the
base-code bits is a logical operator of the base code, of weight $\ge d$" yields
$|S|+|\partial T|+w \ge d$.

**What is not done.** The full Lemma 2 of the companion paper also needs two things that
this module does not formalize: (i) the **circuit-level** definition of the deformed code,
with ancillas, $A_v$, $B_p$ and the perfect matching $\tilde s_i$; and (ii) the
derivation from it that an X-type support on the edges is a **cut** of some vertex set
(graph-theoretic duality: the cut space is the orthogonal complement of the cycle space),
and that after cleaning the restriction to the base-code bits is a logical operator of
the base code. These two pieces enter the statement of the counting core as
**hypotheses**, and this module turns only the counting piece into a theorem. It makes no
claim to have machine-checked the general case of Lemma 2.

## 5. Boundaries

* The generic branch $h(G)<1$, where $\min(h,1)=\eta$, requires a rational-valued
  Cheeger constant; C1 of this library is the 0/1 form with $\eta\ge1$
  (`HasExpansionOne`/`c1Witness`), so this module covers only the branch $h\ge1$.
* This module carries **no** readout of $k$. The lemma `deformX_k` in `Codes/Gauging.lean`
  already shows for an arbitrary code that $k$ decreases by exactly one, and here only
  the statement "$\ell$ is a nontrivial logical operator" is needed, supplied by
  `toricZW_not_mem`.
* The row and column indices of the HGP parity-check matrix are product and direct-sum
  types, whereas `min_weight_ker_not_mem_rowspace` requires `Fin` indices. Section 2
  bridges the two with a **column permutation transport** (`flatVec`); the transport
  itself is a relabelling at the level of `Fintype.sum_equiv` and carries no mathematical
  content.
* The two facts about the "$m$-cycle matrix" used here are `cycMat_one_ker` (even row
  sums, already in `Codes/HGPToricFamily.lean`) and `cycMat_col_sum` (**even column**
  sums, new in this module; `cycMat` is not symmetric, so neither implies the other).
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {n : ℕ}

/-! ## 1. Appending one check row (the algebraic form of representation-layer gauging) -/

/-- **Appending one row**: attach `v` below `M` as the new last row, the matrix form of
representation-layer gauging in this library, $H_X \mapsto H_X + [\ell]$. The row index
is `Fin m`, so a row can indeed be appended at the end. -/
def appendRow {m : ℕ} {κ : Type*} (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) :
    Matrix (Fin (m + 1)) κ (ZMod 2) :=
  fun i => Fin.lastCases v (fun j => M j) i

/-- The appended row agrees with the original matrix at the old indices. -/
theorem appendRow_castSucc {m : ℕ} {κ : Type*} (M : Matrix (Fin m) κ (ZMod 2))
    (v : κ → ZMod 2) (j : Fin m) : appendRow M v (Fin.castSucc j) = M j := by
  simp only [appendRow, Fin.lastCases_castSucc]

/-- The appended row lands at the last position. -/
theorem appendRow_last {m : ℕ} {κ : Type*} (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) :
    appendRow M v (Fin.last m) = v := by
  simp only [appendRow, Fin.lastCases_last]

/-- Kernel membership: the `toLin'` form and the matrix-vector form are equivalent. -/
theorem mem_ker_toLin'_iff {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ (ZMod 2)) (x : κ → ZMod 2) : x ∈ LinearMap.ker M.toLin' ↔ M *ᵥ x = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]

/-- The matrix-vector action is zero if and only if every row is orthogonal to the vector. -/
theorem mulVec_eq_zero_iff {ι κ : Type*} [Fintype κ] (M : Matrix ι κ (ZMod 2))
    (x : κ → ZMod 2) : M *ᵥ x = 0 ↔ ∀ i, M i ⬝ᵥ x = 0 := by
  constructor
  · intro h i
    have hi := congrFun h i
    change M i ⬝ᵥ x = 0 at hi
    exact hi
  · intro h
    funext i
    change M i ⬝ᵥ x = 0
    exact h i

/-- **Kernel characterization of the appended row**: the new kernel is the old kernel
intersected with the orthogonal complement of the new row. This is the whole content of
"the kernel shrinks", and the source of "gauging can only kill logical operators". -/
theorem mem_ker_appendRow {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) (E : κ → ZMod 2) :
    E ∈ LinearMap.ker (appendRow M v).toLin' ↔ E ∈ LinearMap.ker M.toLin' ∧ v ⬝ᵥ E = 0 := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have hj := h (Fin.castSucc j)
      rwa [appendRow_castSucc] at hj
    · have hl := h (Fin.last m)
      rwa [appendRow_last] at hl
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases (motive := fun i => (appendRow M v i) ⬝ᵥ E = 0) ?_ ?_ i
    · rw [appendRow_last]; exact h2
    · intro j; rw [appendRow_castSucc]; exact h1 j

/-- The matrix-vector action of the appended matrix: the old part and the new row are
each zero. -/
theorem mulVec_appendRow_eq_zero_iff {m : ℕ} {κ : Type*} [Fintype κ]
    (M : Matrix (Fin m) κ (ZMod 2)) (v E : κ → ZMod 2) :
    (appendRow M v) *ᵥ E = 0 ↔ M *ᵥ E = 0 ∧ v ⬝ᵥ E = 0 := by
  rw [mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have hj := h (Fin.castSucc j)
      rwa [appendRow_castSucc] at hj
    · have hl := h (Fin.last m)
      rwa [appendRow_last] at hl
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases (motive := fun i => (appendRow M v i) ⬝ᵥ E = 0) ?_ ?_ i
    · rw [appendRow_last]; exact h2
    · intro j; rw [appendRow_castSucc]; exact h1 j

/-- **The row space of the appended matrix contains the original row space** (the step
"the row space grows"). -/
theorem rowSpace_appendRow_le {m : ℕ} {κ : Type*} [Fintype κ]
    (M : Matrix (Fin m) κ (ZMod 2)) (v : κ → ZMod 2) :
    M.rowSpace ≤ (appendRow M v).rowSpace := by
  refine Submodule.span_mono ?_
  rintro x ⟨j, rfl⟩
  exact ⟨Fin.castSucc j, appendRow_castSucc M v j⟩

/-- **The general argument, X side**: on appending a row to the X checks, a per-operator
lower bound transfers verbatim, so gauging does not create a lighter X-side logical
operator. -/
theorem le_minWeight_of_lower_appendRow {m₁ m₂ n : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) {d₀ : ℕ} (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ min_weight_ker_not_mem_rowspace (appendRow M₁ v) M₂ :=
  le_minWeight_of_lower _ _ hd fun E hker hnot =>
    h E ((mem_ker_appendRow M₁ v E).mp hker).1 hnot

/-- **The general argument, Z side**: on appending a row to the Z checks, a per-operator
lower bound transfers verbatim, so gauging does not create a lighter Z-side logical
operator. -/
theorem le_minWeight_of_lower_rowSpace_appendRow {m₁ m₂ n : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) {d₀ : ℕ} (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ min_weight_ker_not_mem_rowspace M₁ (appendRow M₂ v) :=
  le_minWeight_of_lower _ _ hd fun E hker hnot =>
    h E hker fun hmem => hnot (rowSpace_appendRow_le M₂ v hmem)

/-! ## 2. Column permutation transport (HGP column indices are a direct-sum type, `min_weight` wants `Fin`)

`flatVec e v := v ∘ e.symm` moves a vector on a direct-sum or product index to `Fin`;
the four results below show that it preserves weight, dot product, kernel membership, and
in one direction row space membership.
-/

/-- **Column permutation**: move a vector on `α` to `β` along `e : α ≃ β`. -/
def flatVec {α β : Type*} (e : α ≃ β) (v : α → ZMod 2) : β → ZMod 2 := v ∘ ⇑e.symm

theorem flatVec_apply {α β : Type*} (e : α ≃ β) (v : α → ZMod 2) (j : β) :
    flatVec e v j = v (e.symm j) := rfl

theorem flatVec_comp {α β : Type*} (e : α ≃ β) (v : α → ZMod 2) :
    flatVec e v ∘ ⇑e = v := by
  funext a
  simp [flatVec_apply]

/-- After a column permutation the matrix-vector action is the original one, with the
vector transported by `flatVec`. -/
theorem mulVec_submatrix {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) (w : β → ZMod 2) :
    (M.submatrix id ⇑e.symm) *ᵥ w = M *ᵥ (w ∘ ⇑e) := by
  funext i
  simp only [Matrix.mulVec_apply, Matrix.submatrix_apply, Matrix.row_apply, dotProduct,
    Function.comp_apply]
  exact Fintype.sum_equiv e.symm (fun j : β => M i (e.symm j) * w j)
    (fun a : α => M i a * w (e a)) (fun j => by rw [Equiv.apply_symm_apply])

/-- A column permutation does not change the kernel. -/
theorem mem_ker_submatrix {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) (w : β → ZMod 2) :
    w ∈ LinearMap.ker (M.submatrix id ⇑e.symm).toLin' ↔ (w ∘ ⇑e) ∈ LinearMap.ker M.toLin' := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, ← mulVec_submatrix M e w]

/-- A column permutation does not change the weight. -/
theorem hammingNorm_flatVec {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (v : α → ZMod 2) : hammingNorm (flatVec e v) = hammingNorm v := by
  have hset : (Finset.univ.filter (fun j : β => flatVec e v j ≠ 0))
      = (Finset.univ.filter (fun a : α => v a ≠ 0)).image ⇑e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨e.symm j, by simpa [flatVec_apply] using h, e.apply_symm_apply j⟩
    · rintro ⟨a, ha, rfl⟩
      simpa [flatVec_apply] using ha
  show (Finset.univ.filter (fun j : β => flatVec e v j ≠ 0)).card
      = (Finset.univ.filter (fun a : α => v a ≠ 0)).card
  rw [hset, Finset.card_image_of_injective _ e.injective]

/-- A column permutation does not change the (bilinear) dot product. -/
theorem dotProduct_flatVec {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (u w : α → ZMod 2) : flatVec e u ⬝ᵥ flatVec e w = u ⬝ᵥ w := by
  rw [dotProduct, dotProduct, flatVec, flatVec, Function.comp_def, Function.comp_def]
  exact Fintype.sum_equiv e.symm
    (fun j : β => u (e.symm j) * w (e.symm j)) (fun a : α => u a * w a) (fun _ => rfl)

/-- Row space membership transports along a column permutation; this is used to bring a
logical operator of the deformed code back down to the base code. -/
theorem comp_symm_mem_rowSpace {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) {x : α → ZMod 2} (hx : x ∈ M.rowSpace) :
    flatVec e x ∈ (M.submatrix id ⇑e.symm).rowSpace := by
  refine Submodule.span_induction
    (p := fun y _ => flatVec e y ∈ (M.submatrix id ⇑e.symm).rowSpace) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    have hrow : (M.submatrix id ⇑e.symm) i = flatVec e (M i) := by
      funext j
      simp [flatVec_apply, Matrix.submatrix_apply]
    exact Submodule.subset_span ⟨i, hrow⟩
  · simp [flatVec]
  · intro a b _ _ ha hb
    have hgoal : flatVec e (a + b) = flatVec e a + flatVec e b := by
      funext j
      simp [flatVec_apply, Pi.add_apply]
    rw [hgoal]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have hgoal : flatVec e (c • a) = c • flatVec e a := by
      funext j
      simp [flatVec_apply, Pi.smul_apply]
    rw [hgoal]
    exact Submodule.smul_mem _ c ha

/-- The reverse direction of the transport: `E ∘ e` in the original row space implies `E`
in the permuted row space. -/
theorem unflatVec_mem_rowSpace {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (M : Matrix ι α (ZMod 2)) (e : α ≃ β) {E : β → ZMod 2}
    (h : E ∘ ⇑e ∈ M.rowSpace) : E ∈ (M.submatrix id ⇑e.symm).rowSpace := by
  have hx := comp_symm_mem_rowSpace M e h
  rwa [show flatVec e (E ∘ ⇑e) = E from by
    funext j; simp [flatVec_apply]] at hx

/-! ## 3. Column sums of the $m$-cycle matrix (needed for the kernel membership of the right-block witnesses)

The pre-existing witness of the left block (`hgpToricZW`) lies in `ker H_Z` thanks to the
**row** sums of `cycMat` being even. The three right-block witnesses (`toricRW` in
`ker H_X`, `toricRWZ` in `ker H_Z`) rely instead on the **column** sums being even. The
latter needs a statement of its own, since `cycMat` is not a symmetric matrix and neither
statement implies the other.
-/

/-- The **predecessor column** of column `j` of the $m$-cycle matrix: the column support
of `j` is exactly `{j, predIdx hm j}`. -/
def predIdx {m : ℕ} (hm : 2 ≤ m) (j : Fin m) : Fin m :=
  ⟨if (j : ℕ) = 0 then m - 1 else (j : ℕ) - 1, by split <;> omega⟩

theorem predIdx_val {m : ℕ} (hm : 2 ≤ m) (j : Fin m) :
    (predIdx hm j : ℕ) = if (j : ℕ) = 0 then m - 1 else (j : ℕ) - 1 := rfl

/-- **Backward**: if `(i+1) mod m = j`, then `i` is the predecessor column of `j`. -/
theorem predIdx_of_succ {m : ℕ} (hm : 2 ≤ m) {i j : Fin m}
    (h : ((i : ℕ) + 1) % m = (j : ℕ)) : (i : ℕ) = (predIdx hm j : ℕ) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [predIdx_val]
  by_cases hj0 : (j : ℕ) = 0
  · rw [ite_eq_left hj0]
    by_cases hlt : (i : ℕ) + 1 < m
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · omega
  · rw [ite_eq_right hj0]
    by_cases hlt : (i : ℕ) + 1 < m
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have hm1 : (i : ℕ) + 1 = m := by omega
      rw [hm1, Nat.mod_self] at h
      exact absurd h.symm hj0

/-- **Forward**: the successor of the predecessor column is `j` itself. -/
theorem succ_of_predIdx {m : ℕ} (hm : 2 ≤ m) {i j : Fin m}
    (h : (i : ℕ) = (predIdx hm j : ℕ)) : ((i : ℕ) + 1) % m = (j : ℕ) := by
  have hj := j.isLt
  rw [predIdx_val] at h
  by_cases hj0 : (j : ℕ) = 0
  · rw [ite_eq_left hj0] at h
    rw [h, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self, hj0]
  · rw [ite_eq_right hj0] at h
    rw [h, Nat.sub_add_cancel (by omega : 1 ≤ (j : ℕ)), Nat.mod_eq_of_lt hj]

/-- **Characterization of the column support**: `i` lies in the support of column `j` if
and only if `i = j` or `i = predIdx hm j`. -/
theorem cycMat_col_supp {m : ℕ} (hm : 2 ≤ m) (i j : Fin m) :
    ((j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m)
      ↔ ((i : ℕ) = (j : ℕ) ∨ (i : ℕ) = (predIdx hm j : ℕ)) :=
  ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (predIdx_of_succ hm h.symm)),
   fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (succ_of_predIdx hm h).symm)⟩

/-- **Even column sums, structural form**: every column of the $m$-cycle matrix has
exactly two 1s, at `j` and at its predecessor. -/
theorem cycMat_col_sum {m : ℕ} (hm : 2 ≤ m) (j : Fin m) :
    (∑ i : Fin m, cycMat m i j) = 0 := by
  have hne : j ≠ predIdx hm j := by
    intro h
    have hv : (j : ℕ) = (predIdx hm j : ℕ) := congrArg Fin.val h
    rw [predIdx_val] at hv
    by_cases hj0 : (j : ℕ) = 0
    · rw [ite_eq_left hj0] at hv; omega
    · rw [ite_eq_right hj0] at hv; omega
  have hhot : ∀ i : Fin m, cycMat m i j
      = (if (i : ℕ) = (j : ℕ) ∨ (i : ℕ) = (predIdx hm j : ℕ) then (1 : ZMod 2) else 0) := by
    intro i
    rw [cycMat]
    by_cases h : (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
    · rw [ite_eq_left h, ite_eq_left ((cycMat_col_supp hm i j).mp h)]
    · rw [ite_eq_right h, ite_eq_right fun hc => h ((cycMat_col_supp hm i j).mpr hc)]
  rw [Finset.sum_congr rfl fun i _ => hhot i]
  rw [sum_two_hot j (predIdx hm j) hne fun _ => (1 : ZMod 2)]
  exact CharTwo.add_self_eq_zero 1

/-- **Even row sums of the transpose**: component `a` of `cycMatᵀ *ᵥ 1`, that is the sum
of column `a` of `cycMat`, is zero. -/
theorem cycMatT_one_ker_row {m : ℕ} (hm : 2 ≤ m) (a : Fin m) :
    (∑ i : Fin m, cycMat m i a * 1) = 0 := by
  simpa only [mul_one] using cycMat_col_sum hm a

/-! ## 4. The two weight-$m$ witnesses of the right block -/

/-- **Row witness of the right block**: on the right block, row `s₀` is all 1 and
everything else is 0, so the weight is $m$.

It is the **surviving witness**: its support is disjoint from that of the measured
logical operator `hgpToricZW m` on the left block, hence the two commute and it is still
in the kernel after gauging. The left-block witness `hgpToricXW m` pairs with
`hgpToricZW m` to 1 and is killed. This is the surviving witness of weight $m$ that the
module is after. -/
def toricRW {m : ℕ} (s₀ : Fin m) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun st => if st.1 = s₀ then 1 else 0)

/-- **Column witness of the right block**: on the right block, column `t₀` is all 1 and
everything else is 0, so the weight is $m$.

It is the **dual witness** for `toricRW`: it lies in the kernel of `H_Z`, thanks to the
column sums of `cycMat` being even, and it meets `toricRW s₀` in exactly one lattice
point, so the two pair to 1. -/
def toricRWZ {m : ℕ} (t₀ : Fin m) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun st => if st.2 = t₀ then 1 else 0)

theorem toricRW_inl {m : ℕ} (s₀ : Fin m) (ab : Fin m × Fin m) :
    toricRW s₀ (Sum.inl ab) = 0 := rfl

theorem toricRW_inr {m : ℕ} (s₀ : Fin m) (st : Fin m × Fin m) :
    toricRW s₀ (Sum.inr st) = (if st.1 = s₀ then 1 else 0) := rfl

theorem toricRWZ_inl {m : ℕ} (t₀ : Fin m) (ab : Fin m × Fin m) :
    toricRWZ t₀ (Sum.inl ab) = 0 := rfl

theorem toricRWZ_inr {m : ℕ} (t₀ : Fin m) (st : Fin m × Fin m) :
    toricRWZ t₀ (Sum.inr st) = (if st.2 = t₀ then 1 else 0) := rfl

/-- **`toricRW` lies in the kernel of the X checks**: after the right-block row pattern
passes through `blockR`, each row is a sum of the entries of one column of `cycMat`, and
the column sums are even. -/
theorem toricRW_ker {m : ℕ} (hm : 2 ≤ m) (s₀ : Fin m) :
    hgpHX (cycMat m) (cycMat m) *ᵥ toricRW s₀ = 0 := by
  rw [hgpHX_mulVec_eq_zero_iff]
  have hL : blockL (toricRW s₀) = 0 := by ext a b; rfl
  rw [hL, Matrix.mul_zero]
  symm
  ext s d
  rw [Matrix.mul_apply]
  change (∑ t : Fin m, blockR (toricRW s₀) s t * cycMat m t d) = 0
  by_cases hs : s = s₀
  · have he : ∀ t : Fin m, blockR (toricRW s₀) s t * cycMat m t d = cycMat m t d * 1 := by
      intro t
      rw [blockR_apply, toricRW_inr, ite_eq_left hs, one_mul, mul_one]
    rw [Finset.sum_congr rfl fun t _ => he t]
    exact cycMatT_one_ker_row hm d
  · have he : ∀ t : Fin m, blockR (toricRW s₀) s t * cycMat m t d = 0 := by
      intro t
      rw [blockR_apply, toricRW_inr, ite_eq_right hs, zero_mul]
    rw [Finset.sum_congr rfl fun t _ => he t, Finset.sum_const_zero]

/-- **`toricRWZ` lies in the kernel of the Z checks**: after the right-block column
pattern passes through `cycMatᵀ`, each column is a sum of the entries of one column of
`cycMat`, and the column sums are even. -/
theorem toricRWZ_ker {m : ℕ} (hm : 2 ≤ m) (t₀ : Fin m) :
    hgpHZ (cycMat m) (cycMat m) *ᵥ toricRWZ t₀ = 0 := by
  rw [hgpHZ_mulVec_eq_zero_iff]
  have hL : blockL (toricRWZ t₀) = 0 := by ext a b; rfl
  rw [hL, Matrix.zero_mul]
  symm
  ext a d
  rw [Matrix.mul_apply]
  change (∑ s : Fin m, (cycMat m).transpose a s * blockR (toricRWZ t₀) s d) = 0
  have he : ∀ s : Fin m, (cycMat m).transpose a s * blockR (toricRWZ t₀) s d
      = cycMat m s a * (if d = t₀ then 1 else 0) := by
    intro s
    rw [Matrix.transpose_apply, blockR_apply, toricRWZ_inr]
  rw [Finset.sum_congr rfl fun s _ => he s]
  by_cases hd : d = t₀
  · rw [ite_eq_left hd]
    exact cycMatT_one_ker_row hm a
  · rw [ite_eq_right hd, Finset.sum_congr rfl fun s _ => mul_zero (cycMat m s a),
      Finset.sum_const_zero]

/-- **Weight $m$**: the support of `toricRW` is one whole row of the right block. -/
theorem hammingNorm_toricRW {m : ℕ} (s₀ : Fin m) : hammingNorm (toricRW s₀) = m := by
  have hinj : Function.Injective fun t : Fin m =>
      (Sum.inr (s₀, t) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := by
    intro a b h
    exact congrArg Prod.snd ((Sum.inr.injEq (s₀, a) (s₀, b)).mp h)
  have hset : (Finset.univ.filter (fun i => toricRW s₀ i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun t => Sum.inr (s₀, t)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · exact absurd (toricRW_inl s₀ ab) hi
      · refine ⟨st.2, Finset.mem_univ _, ?_⟩
        by_cases h : st.1 = s₀
        · exact congrArg Sum.inr (Prod.ext h.symm rfl)
        · rw [toricRW_inr, ite_eq_right h] at hi
          exact absurd rfl hi
    · rintro ⟨t, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [toricRW_inr, ite_eq_left rfl]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => toricRW s₀ i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **Weight $m$**: the support of `toricRWZ` is one whole column of the right block. -/
theorem hammingNorm_toricRWZ {m : ℕ} (t₀ : Fin m) : hammingNorm (toricRWZ t₀) = m := by
  have hinj : Function.Injective fun s : Fin m =>
      (Sum.inr (s, t₀) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := by
    intro a b h
    exact congrArg Prod.fst ((Sum.inr.injEq (a, t₀) (b, t₀)).mp h)
  have hset : (Finset.univ.filter (fun i => toricRWZ t₀ i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun s => Sum.inr (s, t₀)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · exact absurd (toricRWZ_inl t₀ ab) hi
      · refine ⟨st.1, Finset.mem_univ _, ?_⟩
        by_cases h : st.2 = t₀
        · exact congrArg Sum.inr (Prod.ext rfl h.symm)
        · rw [toricRWZ_inr, ite_eq_right h] at hi
          exact absurd rfl hi
    · rintro ⟨s, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [toricRWZ_inr, ite_eq_left rfl]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => toricRWZ t₀ i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **Pairing zero**: the supports of `toricRW` (right block) and `hgpToricZW` (left
block) are disjoint. This is exactly the mechanism behind survival, that is, commutation. -/
theorem dot_toricRW_toricZW {m : ℕ} (s₀ : Fin m) :
    toricRW s₀ ⬝ᵥ hgpToricZW m = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases i with ab | st <;> simp [toricRW_inl, toricRW_inr, hgpToricZW]

/-- **Pairing one**: `toricRW s₀` and `toricRWZ t₀` meet in exactly the lattice point
`(s₀, t₀)`, so `toricRWZ` is the dual witness for `toricRW \notin row H_Z`. -/
theorem dot_toricRW_toricRWZ {m : ℕ} (s₀ t₀ : Fin m) :
    toricRW s₀ ⬝ᵥ toricRWZ t₀ = 1 := by
  rw [dotProduct, Fintype.sum_sum_type]
  have hL : (∑ ab : Fin m × Fin m, toricRW s₀ (Sum.inl ab) * toricRWZ t₀ (Sum.inl ab)) = 0 :=
    Finset.sum_eq_zero fun ab _ => by rw [toricRW_inl, zero_mul]
  have hR : (∑ st : Fin m × Fin m, toricRW s₀ (Sum.inr st) * toricRWZ t₀ (Sum.inr st)) = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single s₀]
    · rw [Finset.sum_eq_single t₀]
      · rw [toricRW_inr, toricRWZ_inr, ite_eq_left rfl, ite_eq_left rfl, mul_one]
      · intro t _ ht
        rw [toricRWZ_inr, ite_eq_right ht, mul_zero]
      · intro h; exact absurd (Finset.mem_univ t₀) h
    · intro s _ hs
      exact Finset.sum_eq_zero fun t _ => by rw [toricRW_inr, ite_eq_right hs, zero_mul]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  rw [hL, hR, zero_add]

/-- The two blocks of the pre-existing X-type witness, column 0 of the left block, under
the direct-sum index; both are at the `rfl` level. -/
theorem hgpToricXW_inl {m : ℕ} (ab : Fin m × Fin m) :
    hgpToricXW m (Sum.inl ab) = (if (ab.2 : ℕ) = 0 then 1 else 0) := rfl

theorem hgpToricXW_inr {m : ℕ} (st : Fin m × Fin m) : hgpToricXW m (Sum.inr st) = 0 := rfl

theorem hgpToricZW_inl {m : ℕ} (ab : Fin m × Fin m) :
    hgpToricZW m (Sum.inl ab) = (if (ab.1 : ℕ) = 0 then 1 else 0) := rfl

theorem hgpToricZW_inr {m : ℕ} (st : Fin m × Fin m) : hgpToricZW m (Sum.inr st) = 0 := rfl

/-- **The measured logical operator pairs with the old witness to 1**, for every
$m\ge2$: the two meet in exactly the lattice point `(0,0)`.

The library has `decide` instances for $m=9,12,16$ (`toric9_dot` and the like); a
**structural** proof is given here, valid for every $m$, because the statement that the
old witness is killed uses it below. -/
theorem dot_toricXW_toricZW {m : ℕ} (hm : 2 ≤ m) : hgpToricXW m ⬝ᵥ hgpToricZW m = 1 := by
  obtain ⟨z, hz⟩ : ∃ z : Fin m, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  rw [dotProduct, Fintype.sum_sum_type]
  have hL : (∑ ab : Fin m × Fin m, hgpToricXW m (Sum.inl ab) * hgpToricZW m (Sum.inl ab)) = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single z]
    · rw [Finset.sum_eq_single z]
      · simp [hgpToricXW_inl, hgpToricZW_inl, hz]
      · intro t _ ht
        have ht' : ¬((t : ℕ) = 0) := fun h0 => ht (Fin.ext (h0.trans hz.symm))
        simp [hgpToricXW_inl, hgpToricZW_inl, hz, ht']
      · intro h; exact absurd (Finset.mem_univ z) h
    · intro a _ ha
      have ha' : ¬((a : ℕ) = 0) := fun h0 => ha (Fin.ext (h0.trans hz.symm))
      exact Finset.sum_eq_zero fun t _ => by simp [hgpToricXW_inl, hgpToricZW_inl, ha']
    · intro h; exact absurd (Finset.mem_univ z) h
  have hR : (∑ st : Fin m × Fin m, hgpToricXW m (Sum.inr st) * hgpToricZW m (Sum.inr st)) = 0 :=
    Finset.sum_eq_zero fun st _ => by simp [hgpToricXW_inr, hgpToricZW_inr]
  rw [hL, hR, add_zero]

/-- **Weight of the left-block row witness** (`hgpToricZW`, the measured logical
operator): the support is one whole row of the left block. -/
theorem hammingNorm_hgpToricZW {m : ℕ} (hm : 2 ≤ m) : hammingNorm (hgpToricZW m) = m := by
  obtain ⟨z, hz⟩ : ∃ z : Fin m, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hinj : Function.Injective fun b : Fin m =>
      (Sum.inl (z, b) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := fun a b h =>
    congrArg Prod.snd ((Sum.inl.injEq (z, a) (z, b)).mp h)
  have hset : (Finset.univ.filter (fun i => hgpToricZW m i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun b => Sum.inl (z, b)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · refine ⟨ab.2, Finset.mem_univ _, ?_⟩
        by_cases h : (ab.1 : ℕ) = 0
        · exact congrArg Sum.inl (Prod.ext (Fin.ext (h.trans hz.symm).symm) rfl)
        · rw [hgpToricZW_inl, ite_eq_right h] at hi
          exact absurd rfl hi
      · exact absurd (hgpToricZW_inr st) hi
    · rintro ⟨b, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [hgpToricZW_inl, ite_eq_left hz]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => hgpToricZW m i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **Weight of the left-block column witness** (`hgpToricXW`): the support is one whole
column of the left block. -/
theorem hammingNorm_hgpToricXW {m : ℕ} (hm : 2 ≤ m) : hammingNorm (hgpToricXW m) = m := by
  obtain ⟨z, hz⟩ : ∃ z : Fin m, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hinj : Function.Injective fun a : Fin m =>
      (Sum.inl (a, z) : (Fin m × Fin m) ⊕ (Fin m × Fin m)) := fun a b h =>
    congrArg Prod.fst ((Sum.inl.injEq (a, z) (b, z)).mp h)
  have hset : (Finset.univ.filter (fun i => hgpToricXW m i ≠ 0))
      = (Finset.univ : Finset (Fin m)).image (fun a => Sum.inl (a, z)) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      rcases i with ab | st
      · refine ⟨ab.1, Finset.mem_univ _, ?_⟩
        by_cases h : (ab.2 : ℕ) = 0
        · exact congrArg Sum.inl (Prod.ext rfl (Fin.ext (h.trans hz.symm).symm))
        · rw [hgpToricXW_inl, ite_eq_right h] at hi
          exact absurd rfl hi
      · exact absurd (hgpToricXW_inr st) hi
    · rintro ⟨a, -, rfl⟩
      exact ⟨Finset.mem_univ _, by rw [hgpToricXW_inl, ite_eq_left hz]; exact one_ne_zero⟩
  show (Finset.univ.filter (fun i => hgpToricXW m i ≠ 0)).card = m
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## 5. The deformed code of the toric family (representation-layer gauging) and column flattening -/

/-- Row permutation `Fin (m*m) ≃ Fin m × Fin m`. The HGP row index is a product type
while `min_weight_ker_not_mem_rowspace` requires `Fin` indices, so the rows are flattened
first. -/
def pairIdx (m : ℕ) : Fin (m * m) ≃ Fin m × Fin m :=
  (finProdFinEquiv (m := m) (n := m)).symm

/-- Column permutation `(Fin m × Fin m) ⊕ (Fin m × Fin m) ≃ Fin (m*m + m*m)`. -/
def colIdx (m : ℕ) :
    ((Fin m × Fin m) ⊕ (Fin m × Fin m)) ≃ Fin (m * m + m * m) :=
  (Equiv.sumCongr (pairIdx m).symm (pairIdx m).symm).trans finSumFinEquiv

/-- The row-list form of the toric-family X checks, permuted to `Fin (m*m)` by
`pairIdx`; the row space and the kernel are unchanged. -/
def toricHxRows (m : ℕ) : Matrix (Fin (m * m)) ((Fin m × Fin m) ⊕ (Fin m × Fin m)) (ZMod 2) :=
  fun i => hgpHX (cycMat m) (cycMat m) (pairIdx m i)

/-- The row-list form of the toric-family Z checks, as above, purely to obtain `Fin`
indices. -/
def toricHzRows (m : ℕ) : Matrix (Fin (m * m)) ((Fin m × Fin m) ⊕ (Fin m × Fin m)) (ZMod 2) :=
  fun i => hgpHZ (cycMat m) (cycMat m) (pairIdx m i)

/-- **The X checks of the deformed toric-family code**: $H_X' = H_X + [\ell]$, where
$\ell$ is the measured X-type logical operator `hgpToricZW m`, that is,
representation-layer gauging as in `deformXRows` of `Codes/Gauging.lean`. The column
index is in `Fin` form, flattened by `colIdx`. -/
def toricGaugedHx (m : ℕ) : Matrix (Fin (m * m + 1)) (Fin (m * m + m * m)) (ZMod 2) :=
  (appendRow (toricHxRows m) (hgpToricZW m)).submatrix id ⇑(colIdx m).symm

/-- The `Fin` column form of the toric-family Z checks. -/
def toricHzFin (m : ℕ) : Matrix (Fin (m * m)) (Fin (m * m + m * m)) (ZMod 2) :=
  (toricHzRows m).submatrix id ⇑(colIdx m).symm

/-- The `Fin` column form of the toric-family X checks, used in the lower-bound
argument. -/
def toricHxFin (m : ℕ) : Matrix (Fin (m * m)) (Fin (m * m + m * m)) (ZMod 2) :=
  (toricHxRows m).submatrix id ⇑(colIdx m).symm

/-- The surviving witness, in `Fin` column form. -/
def toricRWFin (m : ℕ) (s₀ : Fin m) : Vec (m * m + m * m) :=
  flatVec (colIdx m) (toricRW s₀)

/-- The dual witness, in `Fin` column form. -/
def toricRWZFin (m : ℕ) (t₀ : Fin m) : Vec (m * m + m * m) :=
  flatVec (colIdx m) (toricRWZ t₀)

/-- The row permutation does not change the kernel, X side. -/
theorem mem_ker_toricHxRows {m : ℕ} {E : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2} :
    E ∈ LinearMap.ker (toricHxRows m).toLin'
      ↔ E ∈ LinearMap.ker (hgpHX (cycMat m) (cycMat m)).toLin' := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  exact ⟨fun h i => by
      have := h ((pairIdx m).symm i)
      simpa [toricHxRows, Equiv.apply_symm_apply] using this,
    fun h j => by
      have := h (pairIdx m j)
      simpa [toricHxRows] using this⟩

/-- The row permutation does not change the kernel, Z side. -/
theorem mem_ker_toricHzRows {m : ℕ} {E : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2} :
    E ∈ LinearMap.ker (toricHzRows m).toLin'
      ↔ E ∈ LinearMap.ker (hgpHZ (cycMat m) (cycMat m)).toLin' := by
  rw [mem_ker_toLin'_iff, mem_ker_toLin'_iff, mulVec_eq_zero_iff, mulVec_eq_zero_iff]
  exact ⟨fun h i => by
      have := h ((pairIdx m).symm i)
      simpa [toricHzRows, Equiv.apply_symm_apply] using this,
    fun h j => by
      have := h (pairIdx m j)
      simpa [toricHzRows] using this⟩

/-- The row permutation does not change the row space, X side. -/
theorem rowSpace_toricHxRows {m : ℕ} :
    (hgpHX (cycMat m) (cycMat m)).rowSpace = (toricHxRows m).rowSpace := by
  unfold Matrix.rowSpace
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pairIdx m).symm i, by simp only [toricHxRows, Equiv.apply_symm_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨pairIdx m j, by simp only [toricHxRows]⟩

/-- The row permutation does not change the row space, Z side. -/
theorem rowSpace_toricHzRows {m : ℕ} :
    (hgpHZ (cycMat m) (cycMat m)).rowSpace = (toricHzRows m).rowSpace := by
  unfold Matrix.rowSpace
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pairIdx m).symm i, by simp only [toricHzRows, Equiv.apply_symm_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨pairIdx m j, by simp only [toricHzRows]⟩

/-- The row space of the deformed code contains the original row space: the row space
grows. -/
theorem rowSpace_toricHx_le_gaugedRows {m : ℕ} :
    (toricHxRows m).rowSpace ≤ (appendRow (toricHxRows m) (hgpToricZW m)).rowSpace :=
  rowSpace_appendRow_le _ _

/-- **`toricRW` lies in the kernel of the deformed code**, so it survives: it commutes
with $\ell$, the pairing being 0, and it lies in the original kernel. -/
theorem toricRWFin_mem_ker {m : ℕ} (hm : 2 ≤ m) (s₀ : Fin m) :
    toricRWFin m s₀ ∈ LinearMap.ker (toricGaugedHx m).toLin' := by
  rw [mem_ker_toLin'_iff]
  show (appendRow (toricHxRows m) (hgpToricZW m)).submatrix id ⇑(colIdx m).symm
    *ᵥ flatVec (colIdx m) (toricRW s₀) = 0
  rw [mulVec_submatrix (appendRow (toricHxRows m) (hgpToricZW m)) (colIdx m), flatVec_comp]
  rw [mulVec_appendRow_eq_zero_iff, mulVec_eq_zero_iff]
  refine ⟨fun i => ?_, ?_⟩
  · exact congrFun (toricRW_ker hm s₀) (pairIdx m i)
  · rw [dotProduct_comm]; exact dot_toricRW_toricZW s₀

/-- **The old witness is killed**: `hgpToricXW m`, column 0 of the left block, pairs with
the measured logical operator `hgpToricZW m` to $1$, so after gauging it **no longer**
lies in the kernel.

Together with `toricRWFin_mem_ker` this shows why the surviving witness of weight $m$ has
to be a **new** one: `toricRW` has support disjoint from that of $\ell$ and therefore
survives, whereas `hgpToricXW` pairs with $\ell$ to $1$ and is killed. -/
theorem toricXWFin_not_mem_ker {m : ℕ} (hm : 2 ≤ m) :
    flatVec (colIdx m) (hgpToricXW m) ∉ LinearMap.ker (toricGaugedHx m).toLin' := by
  intro hmem
  have hker := (mem_ker_submatrix (appendRow (toricHxRows m) (hgpToricZW m)) (colIdx m)
    (flatVec (colIdx m) (hgpToricXW m))).mp hmem
  rw [flatVec_comp] at hker
  rw [mem_ker_appendRow] at hker
  have hpair := hker.2
  rw [dotProduct_comm] at hpair
  exact absurd (hpair.symm.trans (dot_toricXW_toricZW hm)) zero_ne_one

/-- **`toricRWFin` is not an element of the Z-check row space**: its dual witness is
`toricRWZFin`. -/
theorem toricRWFin_not_mem {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    toricRWFin m s₀ ∉ (toricHzFin m).rowSpace := by
  refine not_mem_rowSpace_of_ker_dot (toricHzFin m)
    (E := toricRWFin m s₀) (w := toricRWZFin m t₀) ?_ ?_
  · show (toricHzRows m).submatrix id ⇑(colIdx m).symm
      *ᵥ flatVec (colIdx m) (toricRWZ t₀) = 0
    rw [mulVec_submatrix (toricHzRows m) (colIdx m), flatVec_comp, mulVec_eq_zero_iff]
    intro i
    exact congrFun (toricRWZ_ker hm t₀) (pairIdx m i)
  · show flatVec (colIdx m) (toricRWZ t₀) ⬝ᵥ flatVec (colIdx m) (toricRW s₀) = 1
    rw [dotProduct_flatVec, dotProduct_comm]
    exact dot_toricRW_toricRWZ s₀ t₀

/-- **`toricRWZFin` does not lie in the row space of the deformed code**: its dual
witness is `toricRWFin`, which lies in the kernel of the deformed code. This statement
needs survival, that is `toricRWFin_mem_ker`, and it is the key to the Z-side upper
bound. -/
theorem toricRWZFin_not_mem {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    toricRWZFin m t₀ ∉ (toricGaugedHx m).rowSpace :=
  not_mem_rowSpace_of_ker_dot _ (E := toricRWZFin m t₀) (w := toricRWFin m s₀)
    (by
      rw [← mem_ker_toLin'_iff]
      exact toricRWFin_mem_ker hm s₀)
    (by
      show flatVec (colIdx m) (toricRW s₀) ⬝ᵥ flatVec (colIdx m) (toricRWZ t₀) = 1
      rw [dotProduct_flatVec]
      exact dot_toricRW_toricRWZ s₀ t₀)

/-! ## 6. Both distances $=m$ -/

/-- The row space of the deformed code contains the original X row space in
flattened-column form, which the Z-side lower bound needs. -/
theorem rowSpace_toricHxFin_le_gauged {m : ℕ} :
    (toricHxFin m).rowSpace ≤ (toricGaugedHx m).rowSpace := by
  refine Submodule.span_mono ?_
  rintro x ⟨i, rfl⟩
  exact ⟨Fin.castSucc i, by
    funext j
    simp only [toricGaugedHx, toricHxFin, Matrix.submatrix_apply, id_eq, appendRow_castSucc]⟩

/-- The X-side lower bound: the cleaning theorem for the base code together with the
general containment, since the kernel only shrinks. -/
theorem toricGauged_dx_lower {m : ℕ} (hm : 2 ≤ m) {E : Vec (m * m + m * m)}
    (hker : E ∈ LinearMap.ker (toricGaugedHx m).toLin')
    (hnot : E ∉ (toricHzFin m).rowSpace) : m ≤ hammingNorm E := by
  have hker' : (E ∘ ⇑(colIdx m)) ∈
      LinearMap.ker (appendRow (toricHxRows m) (hgpToricZW m)).toLin' :=
    (mem_ker_submatrix (appendRow (toricHxRows m) (hgpToricZW m)) (colIdx m) E).mp hker
  have hnot' : (E ∘ ⇑(colIdx m)) ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace := by
    intro hmem
    rw [rowSpace_toricHzRows] at hmem
    exact hnot (unflatVec_mem_rowSpace (toricHzRows m) (colIdx m) hmem)
  have hbase := (hgp_toric_family hm).2.1 (E ∘ ⇑(colIdx m))
    ((mem_ker_toLin'_iff _ _).mp ((mem_ker_toricHxRows).mp
      ((mem_ker_appendRow (toricHxRows m) (hgpToricZW m) _).mp hker').1)) hnot'
  calc m ≤ hammingNorm (E ∘ ⇑(colIdx m)) := hbase
    _ = hammingNorm E := by
        rw [← hammingNorm_flatVec (colIdx m) (E ∘ ⇑(colIdx m))]
        congr 1
        funext j
        simp [flatVec_apply]

/-- The Z-side lower bound: the cleaning theorem for the base code together with the
general containment, since the row space only grows. -/
theorem toricGauged_dz_lower {m : ℕ} (hm : 2 ≤ m) {E : Vec (m * m + m * m)}
    (hker : E ∈ LinearMap.ker (toricHzFin m).toLin')
    (hnot : E ∉ (toricGaugedHx m).rowSpace) : m ≤ hammingNorm E := by
  have hker' : (E ∘ ⇑(colIdx m)) ∈ LinearMap.ker (hgpHZ (cycMat m) (cycMat m)).toLin' :=
    (mem_ker_toricHzRows).mp ((mem_ker_submatrix (toricHzRows m) (colIdx m) E).mp hker)
  have hnot' : (E ∘ ⇑(colIdx m)) ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace := by
    intro hmem
    refine hnot (rowSpace_toricHxFin_le_gauged ?_)
    exact unflatVec_mem_rowSpace (toricHxRows m) (colIdx m) (by rwa [rowSpace_toricHxRows] at hmem)
  have hbase := (hgp_toric_family hm).2.2 (E ∘ ⇑(colIdx m))
    ((mem_ker_toLin'_iff _ _).mp hker') hnot'
  calc m ≤ hammingNorm (E ∘ ⇑(colIdx m)) := hbase
    _ = hammingNorm E := by
        rw [← hammingNorm_flatVec (colIdx m) (E ∘ ⇑(colIdx m))]
        congr 1
        funext j
        simp [flatVec_apply]

/-- Kernel membership of the dual witness `toricRWZFin`, transported from
`toricRWZ_ker` on the direct-sum index. -/
theorem toricRWZFin_mem_ker {m : ℕ} (hm : 2 ≤ m) (t₀ : Fin m) :
    toricRWZFin m t₀ ∈ LinearMap.ker (toricHzFin m).toLin' := by
  rw [mem_ker_toLin'_iff]
  show (toricHzRows m).submatrix id ⇑(colIdx m).symm
    *ᵥ flatVec (colIdx m) (toricRWZ t₀) = 0
  rw [mulVec_submatrix (toricHzRows m) (colIdx m), flatVec_comp, mulVec_eq_zero_iff]
  intro i
  exact congrFun (toricRWZ_ker hm t₀) (pairIdx m i)

/-- Weight $m$, in `Fin` column form. -/
theorem hammingNorm_toricRWFin {m : ℕ} (s₀ : Fin m) : hammingNorm (toricRWFin m s₀) = m := by
  rw [toricRWFin, hammingNorm_flatVec]
  exact hammingNorm_toricRW s₀

/-- Weight $m$, in `Fin` column form. -/
theorem hammingNorm_toricRWZFin {m : ℕ} (t₀ : Fin m) : hammingNorm (toricRWZFin m t₀) = m := by
  rw [toricRWZFin, hammingNorm_flatVec]
  exact hammingNorm_toricRWZ t₀

/-- **The X-side deformed distance is $m$**: the upper bound is the surviving witness
`toricRW`, of weight $m$, in the kernel and not in the row space of `H_Z`, while the
lower bound is the cleaning theorem for the base code (`hgp_toric_family`) together with
the fact that the kernel only shrinks.

Contrast with the BB24 instance in `Codes/BB24Separation.lean`: there both distances are
per-instance kernel computations, whereas here the value is **family-level**, with the
witness and the lower-bound argument valid for every $m\ge2$. -/
theorem toric_family_deformed_dx {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    min_weight_ker_not_mem_rowspace (toricGaugedHx m) (toricHzFin m) = m := by
  refine le_antisymm ?_ ?_
  · refine minWeight_le_of_witness _ _ (toricRWFin_mem_ker hm s₀)
      (toricRWFin_not_mem hm s₀ t₀) (hammingNorm_toricRWFin s₀)
  · exact le_minWeight_of_lower _ _ (by nlinarith [hm]) fun E hker hnot =>
      toricGauged_dx_lower hm hker hnot

/-- **The Z-side deformed distance is $m$**: the upper bound is the surviving witness
`toricRWZ`, and the lower bound is the cleaning theorem for the base code together with
the fact that the row space only grows. -/
theorem toric_family_deformed_dz {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    min_weight_ker_not_mem_rowspace (toricHzFin m) (toricGaugedHx m) = m := by
  refine le_antisymm ?_ ?_
  · refine minWeight_le_of_witness _ _ (toricRWZFin_mem_ker hm t₀)
      (toricRWZFin_not_mem hm s₀ t₀) (hammingNorm_toricRWZFin t₀)
  · exact le_minWeight_of_lower _ _ (by nlinarith [hm]) fun E hker hnot =>
      toricGauged_dz_lower hm hker hnot

/-! ## 7. Landing the spacelike side of the closed separation form -/

/-- **The spacelike bound for the toric family, a theorem in this model**:
$\min(\eta,1)\cdot m \le$ the deformed code distance.

This is the W–Y Lemma 2 spacelike bound that appears as a named hypothesis in
`separation_judgment`, with $d$ the base-code distance $m$ and `spaceDist` the deformed
code distance. On this family it closes via `toric_family_deformed_dx`, which gives the
deformed distance $=m$, and the expansion of $K_m$, which gives $\min(\eta,1)=1$. -/
theorem toric_family_space_bound {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m) :
    min (c1Witness (completeEdges m)) 1 * m
      ≤ min_weight_ker_not_mem_rowspace (toricGaugedHx m) (toricHzFin m) := by
  rw [toric_family_deformed_dx hm s₀ t₀,
    min_eq_right (one_le_c1Witness (expansionOne_complete_gen m)), one_mul]

/-- **The closed separation form for the toric family, with the spacelike side no longer
a hypothesis**: the deformed code distance is $m$, the ancilla graph $K_m$ expands (C1),
and the number of rounds is $T=m$ (C2). Of the whole hypothesis list of
`separation_closed`, only the timelike component `timeDist` is left undetermined.

Contrast `toric_family_separation_closed` in `Codes/SeparationClosedForm.lean`: that
statement still takes the spacelike bound as input, whereas this one eliminates it on
this family. -/
theorem toric_family_separation_closed_spatial {m : ℕ} (hm : 2 ≤ m) (s₀ t₀ : Fin m)
    {timeDist : ℕ} (hTime : m ≤ timeDist) :
    m ≤ min (min_weight_ker_not_mem_rowspace (toricGaugedHx m) (toricHzFin m)) timeDist :=
  separation_closed (edges := completeEdges m) (d := m) (T := m)
    (expansionOne_complete_gen m) (le_refl m) (toric_family_space_bound hm s₀ t₀) hTime

/-! ## 8. The counting core of W–Y Lemma 2 (one half of the lemma)

The proof of Methods Lemma 2 of the companion paper splits into three pieces:

1. **Graph-theoretic duality**: the X-type support $M$ of a deformed-code logical
   operator on the edges commutes with every flux check $B_p$, a cycle, if and only if
   $M$ is a 1-cocycle, if and only if $M$ is a **cut** $\partial T$ of some vertex set
   $T$; that is, the cut space is the orthogonal complement of the cycle space;
2. **Cleaning**: multiplying by $\prod_{v\in T}A_v$ removes the edge support and
   replaces the vertex support $S$ by $S\triangle T$; the remaining operator, restricted
   to the base-code bits, has to be a **logical operator of the base code**, of weight
   $\ge d$; and since $\prod_{v\in V}A_v$ is the measured logical operator itself,
   a stabilizer of the deformed code, one may take $|T|\le|V|/2$;
3. **Counting**: Cheeger constant $\ge1$, which is C1, gives
   $|T|\le|\partial T|$, so the weight satisfies
   $|S|+|\partial T|+w \ge |S\triangle T| + w \ge d$.

The theorem below turns **piece 3** into a theorem, while pieces 1 and 2 enter the
statement as explicit hypotheses: `hT` says that a representative with at most half the
vertices can be taken, and `hlog` that after cleaning the restriction to the base code is
a logical operator. No claim is made that the general case of Lemma 2 has been
machine-checked; see the honest list in Section 4 of the module header.
-/

/-- **The counting core of W–Y Lemma 2**: under ancilla graph expansion $\ge1$, which
is C1, the sum of the vertex X-support $S$ of a deformed-code logical operator and of its
edge X-support, the cut $\partial T$ that cleaning needs, is at least the base-code
distance $d$.

The hypotheses correspond one to one with the companion paper: `hG` is C1
($h(G)\ge1$), `hT` says that a representative has support $\le|V|/2$, and `hlog` says
that after cleaning the restriction to the base-code bits is a logical operator of the
base code, of weight $\ge d$. In the conclusion, `w` is the weight contribution of the
operator on the remaining bits: the non-vertex bits of the base code and the rest of the
ancillas. -/
theorem space_fault_weight_ge_of_expansion {k : ℕ} (edges : List (Fin k × Fin k))
    (hG : HasExpansionOne edges) {S T : Finset (Fin k)} {d w : ℕ}
    (hT : T.card ≤ k - T.card)
    (hlog : d ≤ (S \ T ∪ T \ S).card + w) :
    d ≤ S.card + cutSize edges T + w := by
  have hcut : T.card ≤ cutSize edges T := by
    have := hG T
    rwa [min_eq_left hT] at this
  have htri : (S \ T ∪ T \ S).card ≤ S.card + T.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    exact hx.elim (fun h => Or.inl (Finset.mem_sdiff.mp h).1)
      (fun h => Or.inr (Finset.mem_sdiff.mp h).1)
  omega

end QECCertificates
