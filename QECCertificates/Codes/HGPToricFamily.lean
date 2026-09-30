/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.HGPKunneth
import QECCertificates.GF2.HGPCleaning
import QECCertificates.GF2.HGPCleaningDual

/-!
# HGP family instances for $n\ge144$, and the all-$m$ toric family theorem

The structural theorems of `GF2/HGPKunneth` (the dimension tensor formula) and of
`GF2/HGPCleaning(±Dual)` (the two distance lower bounds) are **family-level**. This
module instantiates them on the hypergraph product of the $m$-cycle seed
$\mathrm{cyc}_m$: $m=9$ gives $[[162,2,9]]$, $m=12$ gives $[[288,2,12]]$ and $m=16$
gives $[[512,2,16]]$. It then goes further and gives an **all-$m$ theorem**,
`hgp_toric_family`: for every $m\ge2$, HGP($\mathrm{cyc}_m$,$\mathrm{cyc}_m$) is
$[[\,2m^2,\,2,\,m\,]]$. The three seed facts (even row sums, rank $m-1$, kernel minimum
weight $m$ in both directions) come structurally from **constancy of the kernel**
(`cycMat_ker_const`: the row equation $w_i+w_{i+1}=0$ propagates along the cycle in
characteristic 2, so a kernel vector must be constant): **no enumeration, and it holds
for every $m$**. Nothing here ranks or enumerates anything of width $\ge100$, and the
certificate stays $O(m^2)$:

* **the dimension $k=2$** (`hgp_toric9_k` / `hgp_toric12_k`): the Künneth formula needs
  only the rank of the $m\times m$ seed matrix, and the rank of the $162$-wide (or
  $288$-wide) matrix is never computed;
* **the two distance lower bounds $d\ge m$** (`hgp_toric9_dx_lb` and the like): the
  cleaning theorem needs only the kernel minimum weight of the seed (a `by decide` over a
  space of size $2^m$);
* **the witness upper bounds $d\le m$** (`hgp_toric9_X_logical` and the like): explicit
  logical operators of weight $m$. Kernel membership reduces, through the compression
  identity, to two $m\times m$ block equations, and non-membership is given by a single
  dot-product certificate through the **dual witness for general indices**
  (`not_mem_rowSpace_of_ker_dot`, added in this module: the `Fin` version of that name in
  `GF2/LowerBound.lean` does not cover product or sum indices).

This is also the shape contrast with the enumerative evidence that QECLean uses on
$[[144,12,12]]$: for $n\ge144$ a per-operator enumeration ($\sum_{k<d}\binom nk$) is
infeasible in the kernel, whereas the certificate of a structural assertion is still
$O(m^2)$.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. The dual-witness lemma for general indices -/

/-- **Dual witness (arbitrary index version)**: if `w` is orthogonal to every row of `M`
(`M *ᵥ w = 0`) and `w ⬝ᵥ E = 1`, then `E` is not in the row space of `M`.

`not_mem_rowSpace_of_dualCheck` in `GF2/LowerBound.lean` restricts the row and column
indices to `Fin`; the HGP parity-check matrices are indexed by product and sum types, so a
directly usable general version is given here. The proof is the statement that a vector in
the row space is orthogonal to the kernel: expanding `E` along the rows of `M` and pairing
term by term collapses the sum to `∑ cᵢ·(M *ᵥ w)ᵢ = 0`, contradicting that the dot
product is 1. -/
theorem not_mem_rowSpace_of_ker_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod 2)) {E w : κ → ZMod 2}
    (hker : M *ᵥ w = 0) (hdot : w ⬝ᵥ E = 1) : E ∉ M.rowSpace := by
  intro hmem
  have hspan : E ∈ Submodule.span (ZMod 2) (Set.range M) := hmem
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := M) (x := E)).mp hspan
  -- E 的逐坐标展开
  have hc' : ∑ i, c i • (fun j => M i j) = E := hc
  have hcoord : ∀ j, E j = ∑ i, c i * M i j := by
    intro j
    have hj : (∑ i, c i • (fun j' => M i j')) j = E j := congrFun hc' j
    rw [← hj, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  -- 点积交换求和序后逐项为零
  have hexpand : ∀ j, w j * E j = ∑ i, w j * (c i * M i j) := by
    intro j; rw [hcoord j, Finset.mul_sum]
  have h1 : w ⬝ᵥ E = ∑ j, ∑ i, w j * (c i * M i j) := by
    rw [dotProduct, Finset.sum_congr rfl (fun j _ => hexpand j)]
  have h2 : ∑ j, ∑ i, w j * (c i * M i j) = ∑ i, ∑ j, c i * (M i j * w j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∀ i, ∑ j, c i * (M i j * w j) = c i * ((M *ᵥ w) i) := by
    intro i
    have hv : ((M *ᵥ w) i) = ∑ j, M i j * w j := rfl
    rw [hv, ← Finset.mul_sum]
  have hzero : ∀ i, c i * ((M *ᵥ w) i) = 0 := by
    intro i; rw [congrFun hker i]; simp
  rw [h1, h2, Finset.sum_congr rfl (fun i _ => h3 i)] at hdot
  rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const_zero] at hdot
  exact absurd hdot (by simp)

/-! ## 2. The $m$-cycle seed and the toric-family witnesses (general definitions) -/

/-- **The $m$-cycle incidence matrix** $\mathrm{cyc}_m$: row $i$ has a 1 in columns $i$ and
$i{+}1$ (modulo $m$). Every row has exactly two 1s (so the row sums are even), the rank is
$m-1$, and the kernel is spanned by the all-ones vector.
$\mathrm{HGP}(\mathrm{cyc}_m,\mathrm{cyc}_m)$ is the $m\times m$ toric code
$[[2m^2, 2, m]]$ (for $m=3$ this is the `toric3` case matrix of
`Codes/CaseMatrix.lean`). -/
def cycMat (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j => if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m then 1 else 0

/-- **X-type witness**: all 1s in column $0$ of the left block (the $n_1\times n_2$
lattice) and all 0s in the right block: a closed loop on the torus in one direction, of
weight $m$. -/
def hgpToricXW (m : ℕ) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun ab => if (ab.2 : ℕ) = 0 then 1 else 0) (fun _ => 0)

/-- **Z-type witness**: all 1s in row $0$ of the left block and all 0s in the right block:
the closed loop in the other direction, meeting `hgpToricXW` in exactly one lattice point
(dot product 1). -/
def hgpToricZW (m : ℕ) : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2 :=
  Sum.elim (fun ab => if (ab.1 : ℕ) = 0 then 1 else 0) (fun _ => 0)

/-! ## 3. Structured kernel membership of the witnesses (any $m$, using only that the row sums are even) -/

/-- The right block of the X-type witness is empty (a definitional fact). -/
theorem blockR_toricXW_zero (m : ℕ) : blockR (hgpToricXW m) = 0 := by
  ext s t; rfl

/-- The right block of the Z-type witness is empty (a definitional fact). -/
theorem blockR_toricZW_zero (m : ℕ) : blockR (hgpToricZW m) = 0 := by
  ext s t; rfl

/-- The left block of the X-type witness is annihilated by $\mathrm{cyc}_m$: each column is
either all 1s (killed by the even row sums) or zero. -/
theorem cycMat_mul_blockL_XW {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    cycMat m * blockL (hgpToricXW m) = 0 := by
  ext i j
  change ∑ a : Fin m, cycMat m i a * hgpToricXW m (Sum.inl (a, j)) = 0
  by_cases hj : (j : ℕ) = 0
  · have he : ∀ a : Fin m, cycMat m i a * hgpToricXW m (Sum.inl (a, j)) = cycMat m i a * 1 := by
      intro a; congr 1; simp [hgpToricXW, hj]
    rw [Finset.sum_congr rfl (fun a _ => he a)]
    exact congrFun hone i
  · have he : ∀ a : Fin m, cycMat m i a * hgpToricXW m (Sum.inl (a, j)) = 0 := by
      intro a; simp [hgpToricXW, hj]
    rw [Finset.sum_congr rfl (fun a _ => he a), Finset.sum_const_zero]

/-- The left block of the Z-type witness becomes zero when multiplied on the right by
$\mathrm{cyc}_m^\top$: each row is either all 1s (transposition does not change row sums)
or zero. -/
theorem blockL_ZW_mul_transpose {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    blockL (hgpToricZW m) * (cycMat m).transpose = 0 := by
  ext a d
  change ∑ b : Fin m, hgpToricZW m (Sum.inl (a, b)) * cycMat m d b = 0
  by_cases ha : (a : ℕ) = 0
  · have he : ∀ b : Fin m, hgpToricZW m (Sum.inl (a, b)) * cycMat m d b
        = cycMat m d b * 1 := by
      intro b
      rw [mul_comm (hgpToricZW m (Sum.inl (a, b)))]
      congr 1; simp [hgpToricZW, ha]
    rw [Finset.sum_congr rfl (fun b _ => he b)]
    exact congrFun hone d
  · have he : ∀ b : Fin m, hgpToricZW m (Sum.inl (a, b)) * cycMat m d b = 0 := by
      intro b; simp [hgpToricZW, ha]
    rw [Finset.sum_congr rfl (fun b _ => he b), Finset.sum_const_zero]

/-- **The X-type witness is a kernel vector of the X checks** (the compression identity
plus two block facts). -/
theorem toricXW_ker {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    hgpHX (cycMat m) (cycMat m) *ᵥ hgpToricXW m = 0 := by
  rw [hgpHX_mulVec_eq_zero_iff, cycMat_mul_blockL_XW hone, blockR_toricXW_zero, zero_mul]

/-- **The Z-type witness is a kernel vector of the Z checks**. -/
theorem toricZW_ker {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0) :
    hgpHZ (cycMat m) (cycMat m) *ᵥ hgpToricZW m = 0 := by
  rw [hgpHZ_mulVec_eq_zero_iff, blockL_ZW_mul_transpose hone, blockR_toricZW_zero,
    Matrix.mul_zero]

/-! ## 4. The family-level assembler: the three seed facts give the HGP toric parameters -/

/-- **Family-level dimension**: seed rank $m-1$ gives
$k = (m-(m-1))^2 + (m-(m-1))^2 = 2$ logical qubits for
$\mathrm{HGP}(\mathrm{cyc}_m,\mathrm{cyc}_m)$ (the Künneth formula; the rank of the large
matrix is never computed). -/
theorem hgp_toric_k {m : ℕ} (hm : 1 ≤ m) (hrank : (cycMat m).rank = m - 1) :
    (m * m + m * m) - (hgpHX (cycMat m) (cycMat m)).rank
      - (hgpHZ (cycMat m) (cycMat m)).rank = 2 := by
  rw [hgp_kunneth, hrank]
  have h1 : m - (m - 1) = 1 := by omega
  rw [h1]

/-- **Family-level X-distance lower bound**: kernel minimum weight $m$ for the seed (in
both directions) gives weight $\ge m$ for every nontrivial X-type logical operator (the
cleaning theorem). -/
theorem hgp_toric_dx_lb {m : ℕ}
    (hmin : ∀ w : Vec m, w ≠ 0 → cycMat m *ᵥ w = 0 → m ≤ hammingNorm w)
    (hminT : ∀ w : Vec m, w ≠ 0 → (cycMat m).transpose *ᵥ w = 0 → m ≤ hammingNorm w)
    {v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2}
    (hv : hgpHX (cycMat m) (cycMat m) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace) :
    m ≤ hammingNorm v := by
  have h := hgp_X_distance_ge (cycMat m) (cycMat m) hv hlog hmin hminT
  rwa [min_self] at h

/-- **Family-level Z-distance lower bound**. -/
theorem hgp_toric_dz_lb {m : ℕ}
    (hmin : ∀ w : Vec m, w ≠ 0 → cycMat m *ᵥ w = 0 → m ≤ hammingNorm w)
    (hminT : ∀ w : Vec m, w ≠ 0 → (cycMat m).transpose *ᵥ w = 0 → m ≤ hammingNorm w)
    {v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2}
    (hv : hgpHZ (cycMat m) (cycMat m) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace) :
    m ≤ hammingNorm v := by
  have h := hgp_Z_distance_ge (cycMat m) (cycMat m) hv hlog hminT hmin
  rwa [min_self] at h

/-- **Family-level witness non-membership**: the X-type witness is not in the row space of
the Z checks; the certificate is the kernel membership of the Z witness plus one dot
product. -/
theorem toricXW_not_mem {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0)
    (hdot : hgpToricXW m ⬝ᵥ hgpToricZW m = 1) :
    hgpToricXW m ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace := by
  refine not_mem_rowSpace_of_ker_dot _ (toricZW_ker hone) ?_
  rw [dotProduct_comm]; exact hdot

/-- **Family-level witness non-membership (Z side)**. -/
theorem toricZW_not_mem {m : ℕ} (hone : cycMat m *ᵥ (fun _ => 1) = 0)
    (hdot : hgpToricXW m ⬝ᵥ hgpToricZW m = 1) :
    hgpToricZW m ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace :=
  not_mem_rowSpace_of_ker_dot _ (toricXW_ker hone) hdot

/-! ## 5. Instance one: $m=9$, $[[162,2,9]]$ -/

/-- The seed row sums are even (the all-ones vector is in the kernel). -/
theorem cyc9_one_ker : cycMat 9 *ᵥ (fun _ : Fin 9 => 1) = 0 := by decide

/-- The seed has rank $8$. -/
theorem rank_cyc9 : (cycMat 9).rank = 8 := by
  rw [Matrix.rank_eq_length_rowReduce]; decide

/-- The kernel minimum weight of the seed is $9$ (checked vector by vector over a space of
size $2^9$). -/
theorem cyc9_ker_min : ∀ w : Vec 9, w ≠ 0 → cycMat 9 *ᵥ w = 0 →
    9 ≤ hammingNorm w := by decide

/-- The kernel minimum weight of the transposed seed is $9$. -/
theorem cyc9T_ker_min : ∀ w : Vec 9, w ≠ 0 → (cycMat 9).transpose *ᵥ w = 0 →
    9 ≤ hammingNorm w := by decide

/-- The dot product of the two witnesses is exactly 1 (a sum of 162 terms each, checked
term by term). -/
theorem toric9_dot : hgpToricXW 9 ⬝ᵥ hgpToricZW 9 = 1 := by decide

/-- The X-type witness has weight 9. -/
theorem toric9_XW_weight : hammingNorm (hgpToricXW 9) = 9 := by decide

/-- The Z-type witness has weight 9. -/
theorem toric9_ZW_weight : hammingNorm (hgpToricZW 9) = 9 := by decide

/-- The code length is $n = 81 + 81 = 162$. -/
theorem toric9_n : Fintype.card ((Fin 9 × Fin 9) ⊕ (Fin 9 × Fin 9)) = 162 := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **$k$ for $[[162,2,9]]$**: $\mathrm{HGP}(\mathrm{cyc}_9,\mathrm{cyc}_9)$ has 2
logical qubits (Künneth plus seed rank 8; the rank of the 162-wide matrix is never
computed). -/
theorem hgp_toric9_k :
    (9 * 9 + 9 * 9) - (hgpHX (cycMat 9) (cycMat 9)).rank
      - (hgpHZ (cycMat 9) (cycMat 9)).rank = 2 :=
  hgp_toric_k (by decide) rank_cyc9

/-- **$d_X \ge 9$ for $[[162,2,9]]$**: every nontrivial X-type logical operator has weight
at least 9. -/
theorem hgp_toric9_dx_lb {v : (Fin 9 × Fin 9) ⊕ (Fin 9 × Fin 9) → ZMod 2}
    (hv : hgpHX (cycMat 9) (cycMat 9) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat 9) (cycMat 9)).rowSpace) :
    9 ≤ hammingNorm v :=
  hgp_toric_dx_lb cyc9_ker_min cyc9T_ker_min hv hlog

/-- **$d_Z \ge 9$ for $[[162,2,9]]$**. -/
theorem hgp_toric9_dz_lb {v : (Fin 9 × Fin 9) ⊕ (Fin 9 × Fin 9) → ZMod 2}
    (hv : hgpHZ (cycMat 9) (cycMat 9) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat 9) (cycMat 9)).rowSpace) :
    9 ≤ hammingNorm v :=
  hgp_toric_dz_lb cyc9_ker_min cyc9T_ker_min hv hlog

/-- **$d_X \le 9$ for $[[162,2,9]]$**: an explicit X-type logical operator of weight 9
(kernel membership is structural, and non-membership comes from a dual-witness
certificate). -/
theorem hgp_toric9_X_logical :
    hgpHX (cycMat 9) (cycMat 9) *ᵥ hgpToricXW 9 = 0
      ∧ hgpToricXW 9 ∉ (hgpHZ (cycMat 9) (cycMat 9)).rowSpace
      ∧ hammingNorm (hgpToricXW 9) = 9 :=
  ⟨toricXW_ker cyc9_one_ker, toricXW_not_mem cyc9_one_ker toric9_dot,
    toric9_XW_weight⟩

/-- **$d_Z \le 9$ for $[[162,2,9]]$**. -/
theorem hgp_toric9_Z_logical :
    hgpHZ (cycMat 9) (cycMat 9) *ᵥ hgpToricZW 9 = 0
      ∧ hgpToricZW 9 ∉ (hgpHX (cycMat 9) (cycMat 9)).rowSpace
      ∧ hammingNorm (hgpToricZW 9) = 9 :=
  ⟨toricZW_ker cyc9_one_ker, toricZW_not_mem cyc9_one_ker toric9_dot,
    toric9_ZW_weight⟩

/-! ## 6. Instance two: $m=12$, $[[288,2,12]]$ -/

/-- The seed row sums are even. -/
theorem cyc12_one_ker : cycMat 12 *ᵥ (fun _ : Fin 12 => 1) = 0 := by decide

/-- The seed has rank $11$. -/
theorem rank_cyc12 : (cycMat 12).rank = 11 := by
  rw [Matrix.rank_eq_length_rowReduce]; decide

/-- The kernel minimum weight of the seed is $12$ (checked vector by vector over a space of
size $2^{12}$). -/
theorem cyc12_ker_min : ∀ w : Vec 12, w ≠ 0 → cycMat 12 *ᵥ w = 0 →
    12 ≤ hammingNorm w := by decide

/-- The kernel minimum weight of the transposed seed is $12$. -/
theorem cyc12T_ker_min : ∀ w : Vec 12, w ≠ 0 → (cycMat 12).transpose *ᵥ w = 0 →
    12 ≤ hammingNorm w := by decide

/-- The dot product of the two witnesses is exactly 1 (a sum of 288 terms each, checked
term by term). -/
theorem toric12_dot : hgpToricXW 12 ⬝ᵥ hgpToricZW 12 = 1 := by decide

/-- The X-type witness has weight 12. -/
theorem toric12_XW_weight : hammingNorm (hgpToricXW 12) = 12 := by decide

/-- The Z-type witness has weight 12. -/
theorem toric12_ZW_weight : hammingNorm (hgpToricZW 12) = 12 := by decide

/-- The code length is $n = 144 + 144 = 288$. -/
theorem toric12_n : Fintype.card ((Fin 12 × Fin 12) ⊕ (Fin 12 × Fin 12)) = 288 := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- **$k$ for $[[288,2,12]]$**. -/
theorem hgp_toric12_k :
    (12 * 12 + 12 * 12) - (hgpHX (cycMat 12) (cycMat 12)).rank
      - (hgpHZ (cycMat 12) (cycMat 12)).rank = 2 :=
  hgp_toric_k (by decide) rank_cyc12

/-- **$d_X \ge 12$ for $[[288,2,12]]$**. -/
theorem hgp_toric12_dx_lb {v : (Fin 12 × Fin 12) ⊕ (Fin 12 × Fin 12) → ZMod 2}
    (hv : hgpHX (cycMat 12) (cycMat 12) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat 12) (cycMat 12)).rowSpace) :
    12 ≤ hammingNorm v :=
  hgp_toric_dx_lb cyc12_ker_min cyc12T_ker_min hv hlog

/-- **$d_Z \ge 12$ for $[[288,2,12]]$**. -/
theorem hgp_toric12_dz_lb {v : (Fin 12 × Fin 12) ⊕ (Fin 12 × Fin 12) → ZMod 2}
    (hv : hgpHZ (cycMat 12) (cycMat 12) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat 12) (cycMat 12)).rowSpace) :
    12 ≤ hammingNorm v :=
  hgp_toric_dz_lb cyc12_ker_min cyc12T_ker_min hv hlog

/-- **$d_X \le 12$ for $[[288,2,12]]$**. -/
theorem hgp_toric12_X_logical :
    hgpHX (cycMat 12) (cycMat 12) *ᵥ hgpToricXW 12 = 0
      ∧ hgpToricXW 12 ∉ (hgpHZ (cycMat 12) (cycMat 12)).rowSpace
      ∧ hammingNorm (hgpToricXW 12) = 12 :=
  ⟨toricXW_ker cyc12_one_ker, toricXW_not_mem cyc12_one_ker toric12_dot,
    toric12_XW_weight⟩

/-- **$d_Z \le 12$ for $[[288,2,12]]$**. -/
theorem hgp_toric12_Z_logical :
    hgpHZ (cycMat 12) (cycMat 12) *ᵥ hgpToricZW 12 = 0
      ∧ hgpToricZW 12 ∉ (hgpHX (cycMat 12) (cycMat 12)).rowSpace
      ∧ hammingNorm (hgpToricZW 12) = 12 :=
  ⟨toricZW_ker cyc12_one_ker, toricZW_not_mem cyc12_one_ker toric12_dot,
    toric12_ZW_weight⟩

/-! ## 7. The structural route for the whole family: kernel constancy gives the seed facts with no enumeration (any $m$) -/

/-- **Two-hot sum**: a sum whose indicator is nonzero at exactly two distinct positions
equals the sum of the two values there. -/
theorem sum_two_hot {m : ℕ} (a b : Fin m) (hab : a ≠ b) (f : Fin m → ZMod 2) :
    (∑ j : Fin m, if (j : ℕ) = (a : ℕ) ∨ (j : ℕ) = (b : ℕ) then f j else 0) = f a + f b := by
  rw [← Finset.sum_filter
      (p := fun j : Fin m => (j : ℕ) = (a : ℕ) ∨ (j : ℕ) = (b : ℕ))]
  have hset : (Finset.univ.filter (fun j : Fin m => (j : ℕ) = (a : ℕ) ∨ (j : ℕ) = (b : ℕ)))
      = ({a, b} : Finset (Fin m)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    simp [Fin.val_inj]
  rw [hset]
  exact Finset.sum_pair hab

/-- The two hot columns of row $i$ are distinct ($m\ge2$). -/
theorem cycMat_ne_next {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    (i : ℕ) ≠ ((i : ℕ) + 1) % m := by
  intro heq
  rcases Nat.lt_or_ge ((i : ℕ) + 1) m with h | h
  · rw [Nat.mod_eq_of_lt h] at heq; omega
  · have him : (i : ℕ) + 1 = m := by omega
    rw [him, Nat.mod_self] at heq; omega

/-- **The row equation**: the $i$-th component of the $m$-cycle matrix acting on a vector
is exactly $w_i + w_{(i+1)\bmod m}$. -/
theorem cycMat_mulVec_apply {m : ℕ} (hm : 2 ≤ m) (w : Vec m) (i : Fin m) :
    (cycMat m *ᵥ w) i = w i + w ⟨((i : ℕ) + 1) % m, Nat.mod_lt ((i : ℕ) + 1) (by omega)⟩ := by
  have hot : ∀ j : Fin m, cycMat m i j * w j
      = (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m then w j else 0) := by
    intro j
    by_cases h : (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
    · simp [cycMat, h]
    · simp [cycMat, h]
  change (∑ j : Fin m, cycMat m i j * w j)
    = w i + w ⟨((i : ℕ) + 1) % m, Nat.mod_lt ((i : ℕ) + 1) (by omega)⟩
  rw [Finset.sum_congr rfl (fun j _ => hot j),
    sum_two_hot i ⟨((i : ℕ) + 1) % m, Nat.mod_lt ((i : ℕ) + 1) (by omega)⟩
      (by intro heq; exact cycMat_ne_next hm i (congrArg Fin.val heq)) w]

/-- **Even row sums (structural)**: the all-ones vector is in the kernel, since every row
equation reads $1+1=0$. -/
theorem cycMat_one_ker {m : ℕ} (hm : 2 ≤ m) : cycMat m *ᵥ (fun _ => 1) = 0 := by
  funext i
  rw [cycMat_mulVec_apply hm _ i]
  exact CharTwo.add_self_eq_zero _

/-- **Kernel constancy**: a kernel vector of the $m$-cycle matrix must be constant, since
the row equation $w_i + w_{i+1} = 0$ reads $w_{i+1} = w_i$ in characteristic 2 and
propagates along the cycle. -/
theorem cycMat_ker_const {m : ℕ} (hm : 2 ≤ m) {w : Vec m} (h : cycMat m *ᵥ w = 0) :
    ∃ c : ZMod 2, w = fun _ => c := by
  have hstep : ∀ k : ℕ, (hk : k + 1 < m) → w ⟨k + 1, by omega⟩ = w ⟨k, by omega⟩ := by
    intro k hk
    have hrow := congrFun h ⟨k, by omega⟩
    rw [cycMat_mulVec_apply hm w ⟨k, by omega⟩] at hrow
    simp only [Pi.zero_apply, Nat.mod_eq_of_lt hk] at hrow
    exact ((add_eq_zero_iff_eq _ _).mp hrow).symm
  have key : ∀ k : ℕ, (hk : k < m) → w ⟨k, by omega⟩ = w ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        exact (hstep n (by omega)).trans (ih (by omega))
  refine ⟨w ⟨0, by omega⟩, funext fun i => key (i : ℕ) i.isLt⟩

/-- **The row equation for the transpose** (rows with $j\ge1$): the two hot positions are
$j-1$ and $j$. -/
theorem cycMatT_mulVec_pred {m : ℕ} (_hm : 2 ≤ m) (w : Vec m) {j : Fin m} (hj : 1 ≤ (j : ℕ)) :
    ((cycMat m).transpose *ᵥ w) j
      = w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ + w j := by
  have hot : ∀ i : Fin m, (cycMat m).transpose j i * w i
      = (if (i : ℕ) = (j : ℕ) - 1 ∨ (i : ℕ) = (j : ℕ) then w i else 0) := by
    intro i
    by_cases h1 : (i : ℕ) = (j : ℕ) - 1 ∨ (i : ℕ) = (j : ℕ)
    · have hval : cycMat m i j = 1 := by
        change (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
            then (1 : ZMod 2) else 0) = 1
        rcases h1 with h | h
        · have hmod : (j : ℕ) = ((i : ℕ) + 1) % m := by
            rw [h, Nat.sub_add_cancel hj, Nat.mod_eq_of_lt j.isLt]
          rw [ite_eq_left (Or.inr hmod)]
        · rw [ite_eq_left (Or.inl h.symm)]
      rw [Matrix.transpose_apply, ite_eq_left h1, hval, one_mul]
    · have hval : cycMat m i j = 0 := by
        change (if (j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m
            then (1 : ZMod 2) else 0) = 0
        have hnot : ¬((j : ℕ) = (i : ℕ) ∨ (j : ℕ) = ((i : ℕ) + 1) % m) := by
          rcases Nat.lt_or_ge ((i : ℕ) + 1) m with h2 | h2
          · rw [Nat.mod_eq_of_lt h2]
            omega
          · have him : (i : ℕ) + 1 = m := by omega
            rw [show ((i : ℕ) + 1) % m = 0 from by rw [him, Nat.mod_self]]
            omega
        rw [ite_eq_right hnot]
      rw [Matrix.transpose_apply, ite_eq_right h1, hval, zero_mul]
  change (∑ i : Fin m, (cycMat m).transpose j i * w i)
    = w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ + w j
  rw [Finset.sum_congr rfl (fun i _ => hot i),
    sum_two_hot ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ j
      (by intro heq
          have h0 : ((⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin m) : ℕ)
              = (j : ℕ) - 1 := rfl
          have hv := congrArg (fun x : Fin m => (x : ℕ)) heq
          rw [h0] at hv
          have := j.isLt
          omega) w]

/-- **Kernel constancy for the transpose**: a kernel vector of the transpose is constant
as well (the same argument along the $j-1$ direction). -/
theorem cycMatT_ker_const {m : ℕ} (hm : 2 ≤ m) {w : Vec m}
    (h : (cycMat m).transpose *ᵥ w = 0) : ∃ c : ZMod 2, w = fun _ => c := by
  have hstep : ∀ k : ℕ, (hk : k + 1 < m) → w ⟨k + 1, by omega⟩ = w ⟨k, by omega⟩ := by
    intro k hk
    have hrow := congrFun h ⟨k + 1, by omega⟩
    rw [cycMatT_mulVec_pred hm w (by simp)] at hrow
    simp only [Pi.zero_apply] at hrow
    exact ((add_eq_zero_iff_eq _ _).mp hrow).symm
  have key : ∀ k : ℕ, (hk : k < m) → w ⟨k, by omega⟩ = w ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        exact (hstep n (by omega)).trans (ih (by omega))
  refine ⟨w ⟨0, by omega⟩, funext fun i => key (i : ℕ) i.isLt⟩

/-- The weight of a constant vector: $m$ for a nonzero constant and $0$ for the zero
constant. -/
theorem hammingNorm_const {m : ℕ} {c : ZMod 2} (hc : c ≠ 0) :
    hammingNorm (fun _ : Fin m => c) = m := by
  change (Finset.univ.filter (fun i : Fin m => (fun _ : Fin m => c) i ≠ 0)).card = m
  have hfil : (Finset.univ.filter (fun _ : Fin m => c ≠ 0)) = Finset.univ :=
    Finset.ext fun x => by simp [hc]
  rw [hfil, Finset.card_univ, Fintype.card_fin]

/-- **Seed kernel minimum weight (structural, no enumeration)**: a nonzero kernel vector is
constant, so its weight is $m$. -/
theorem cycMat_ker_min {m : ℕ} (hm : 2 ≤ m) {w : Vec m} (hne : w ≠ 0)
    (h : cycMat m *ᵥ w = 0) : m ≤ hammingNorm w := by
  obtain ⟨c, rfl⟩ := cycMat_ker_const hm h
  have hc : c ≠ 0 := by
    intro hc0
    exact hne (by rw [hc0]; rfl)
  rw [hammingNorm_const hc]

/-- **Kernel minimum weight for the transpose (structural)**. -/
theorem cycMatT_ker_min {m : ℕ} (hm : 2 ≤ m) {w : Vec m} (hne : w ≠ 0)
    (h : (cycMat m).transpose *ᵥ w = 0) : m ≤ hammingNorm w := by
  obtain ⟨c, rfl⟩ := cycMatT_ker_const hm h
  have hc : c ≠ 0 := by
    intro hc0
    exact hne (by rw [hc0]; rfl)
  rw [hammingNorm_const hc]

/-- **Seed rank (structural)**: the kernel is the span of the constant vectors
(one-dimensional), and rank plus nullity gives $m-1$. -/
theorem rank_cycMat {m : ℕ} (hm : 2 ≤ m) : (cycMat m).rank = m - 1 := by
  have hspan : LinearMap.ker (cycMat m).mulVecLin
      = Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
    apply le_antisymm
    · intro w hw
      have h0 : cycMat m *ᵥ w = 0 := LinearMap.mem_ker.mp hw
      obtain ⟨c, rfl⟩ := cycMat_ker_const hm h0
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      funext i
      simp
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      refine LinearMap.mem_ker.mpr ?_
      rw [(cycMat m).mulVecLin.map_smul]
      change c • (cycMat m *ᵥ (fun _ => (1 : ZMod 2))) = 0
      rw [cycMat_one_ker hm, smul_zero]
  have hfr : Module.finrank (ZMod 2) ↥(LinearMap.ker (cycMat m).mulVecLin) = 1 := by
    rw [hspan, finrank_span_singleton]
    intro h
    exact one_ne_zero (congrFun h ⟨0, by omega⟩)
  have hrn := LinearMap.finrank_range_add_finrank_ker (cycMat m).mulVecLin
  have hdim : Module.finrank (ZMod 2) (Fin m → ZMod 2) = m := by
    simp
  change Module.finrank (ZMod 2) ↥(LinearMap.range (cycMat m).mulVecLin) = m - 1
  omega

/-- **The all-$m$ toric family theorem**: for every $m \ge 2$,
$\mathrm{HGP}(\mathrm{cyc}_m,\mathrm{cyc}_m)$ is $[[\,2m^2,\,2,\,m\,]]$. The dimension
comes from the Künneth formula and the two distance lower bounds from the cleaning
theorem, while all the seed facts (even row sums, rank $=m-1$, kernel minimum weight $=m$
in both directions) are given structurally by **kernel constancy**: **no enumeration, and
it holds for every $m$**.

This is the extreme form of the contrast between structural evidence and per-instance
enumeration: for arbitrarily large $m$ the seed side needs no computation over $2^m$ at
all, and the certificate is only the $O(m^2)$ term-by-term check of the witnesses. -/
theorem hgp_toric_family {m : ℕ} (hm : 2 ≤ m) :
    (m * m + m * m) - (hgpHX (cycMat m) (cycMat m)).rank
        - (hgpHZ (cycMat m) (cycMat m)).rank = 2
      ∧ (∀ v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2,
          hgpHX (cycMat m) (cycMat m) *ᵥ v = 0 →
            v ∉ (hgpHZ (cycMat m) (cycMat m)).rowSpace → m ≤ hammingNorm v)
      ∧ (∀ v : (Fin m × Fin m) ⊕ (Fin m × Fin m) → ZMod 2,
          hgpHZ (cycMat m) (cycMat m) *ᵥ v = 0 →
            v ∉ (hgpHX (cycMat m) (cycMat m)).rowSpace → m ≤ hammingNorm v) :=
  ⟨hgp_toric_k (by omega) (rank_cycMat hm),
   fun v hv hlog => hgp_toric_dx_lb (fun w hne h => cycMat_ker_min hm hne h)
     (fun w hne h => cycMatT_ker_min hm hne h) hv hlog,
   fun v hv hlog => hgp_toric_dz_lb (fun w hne h => cycMat_ker_min hm hne h)
     (fun w hne h => cycMatT_ker_min hm hne h) hv hlog⟩

/-! ## 8. Instance three: $m=16$, $[[512,2,16]]$ (the seed facts of the all-$m$ theorem plus a term-by-term check of the witnesses) -/

/-- The dot product of the two witnesses is exactly 1 (a sum of 512 terms, checked term by
term). -/
theorem toric16_dot : hgpToricXW 16 ⬝ᵥ hgpToricZW 16 = 1 := by decide

/-- The X-type witness has weight 16. -/
theorem toric16_XW_weight : hammingNorm (hgpToricXW 16) = 16 := by decide

/-- The Z-type witness has weight 16. -/
theorem toric16_ZW_weight : hammingNorm (hgpToricZW 16) = 16 := by decide

/-- **$k$ for $[[512,2,16]]$** (Künneth plus the structural seed rank). -/
theorem hgp_toric16_k :
    (16 * 16 + 16 * 16) - (hgpHX (cycMat 16) (cycMat 16)).rank
      - (hgpHZ (cycMat 16) (cycMat 16)).rank = 2 :=
  hgp_toric_k (by decide) (rank_cycMat (by decide))

/-- **$d_X \ge 16$ for $[[512,2,16]]$** (the cleaning theorem plus the structural seed
facts). -/
theorem hgp_toric16_dx_lb {v : (Fin 16 × Fin 16) ⊕ (Fin 16 × Fin 16) → ZMod 2}
    (hv : hgpHX (cycMat 16) (cycMat 16) *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ (cycMat 16) (cycMat 16)).rowSpace) :
    16 ≤ hammingNorm v :=
  hgp_toric_dx_lb (fun w hne h => cycMat_ker_min (by decide) hne h) (fun w hne h => cycMatT_ker_min (by decide) hne h) hv hlog

/-- **$d_Z \ge 16$ for $[[512,2,16]]$**. -/
theorem hgp_toric16_dz_lb {v : (Fin 16 × Fin 16) ⊕ (Fin 16 × Fin 16) → ZMod 2}
    (hv : hgpHZ (cycMat 16) (cycMat 16) *ᵥ v = 0)
    (hlog : v ∉ (hgpHX (cycMat 16) (cycMat 16)).rowSpace) :
    16 ≤ hammingNorm v :=
  hgp_toric_dz_lb (fun w hne h => cycMat_ker_min (by decide) hne h) (fun w hne h => cycMatT_ker_min (by decide) hne h) hv hlog

/-- **$d_X \le 16$ for $[[512,2,16]]$**. -/
theorem hgp_toric16_X_logical :
    hgpHX (cycMat 16) (cycMat 16) *ᵥ hgpToricXW 16 = 0
      ∧ hgpToricXW 16 ∉ (hgpHZ (cycMat 16) (cycMat 16)).rowSpace
      ∧ hammingNorm (hgpToricXW 16) = 16 :=
  ⟨toricXW_ker (cycMat_one_ker (by decide)),
    toricXW_not_mem (cycMat_one_ker (by decide)) toric16_dot, toric16_XW_weight⟩

/-- **$d_Z \le 16$ for $[[512,2,16]]$**. -/
theorem hgp_toric16_Z_logical :
    hgpHZ (cycMat 16) (cycMat 16) *ᵥ hgpToricZW 16 = 0
      ∧ hgpToricZW 16 ∉ (hgpHX (cycMat 16) (cycMat 16)).rowSpace
      ∧ hammingNorm (hgpToricZW 16) = 16 :=
  ⟨toricZW_ker (cycMat_one_ker (by decide)),
    toricZW_not_mem (cycMat_one_ker (by decide)) toric16_dot, toric16_ZW_weight⟩

end QECCertificates
