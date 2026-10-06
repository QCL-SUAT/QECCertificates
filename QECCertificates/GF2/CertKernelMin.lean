/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

import QECCertificates.GF2.WeightEnum

open QECCertificates

/-!
# A spanning certificate gives the kernel's minimum weight and the rank

Given three matrices $T$ ($n \times k$), $S$ ($k \times n$) and $X$ ($n \times r$) with

$$T\,S + X\,M = 1,$$

every vector in $\ker M$ is a combination of the columns of $T$: for $v \in \ker M$ one has
$v = T\,(S\,v)$.  So "no nonzero vector of weight $< d$ lies in the kernel" can be checked
over the $2^k$ **coefficient vectors** ($k = \dim \ker M$) rather than over the
$\sum_{j<d} \binom{n}{j}$ vectors of the kernel itself, which decouples the seed width $n$
from the enumeration.

The same certificate carries two further **kernel-side readings** ($M\,T = 0$ and
$S\,T = 1$, both small matrix products) which turn $\dim \ker M \le k$ into an equality, so
the dimension of the kernel and the rank of the matrix are read off the same certificate --
the cost of counting pivots on a wide matrix need not be paid.

This module holds those four pieces of machinery and nothing else; the certificates $T, S,
X$ themselves are supplied by the developments that use it.

Ported from the certificate-code-parameters development, where this module is
`QuantumCodeCertificates.Codes.CertKernelMin`; the proofs are unchanged and only the
namespace differs.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000

/-- **Spanning certificate.** If $T S + X M = 1$ then every vector in $\ker M$ is a
combination of the columns of $T$, so "no nonzero vector of weight $< d$ lies in the
kernel" can be checked over the $2^k$ coefficient vectors ($k = \dim\ker M$) rather than
over the $\sum_{j<d}\binom nj$ vectors. -/
theorem eq_smul_of_cert {r n k : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2))
    (T : Matrix (Fin n) (Fin k) (ZMod 2)) (S : Matrix (Fin k) (Fin n) (ZMod 2))
    (X : Matrix (Fin n) (Fin r) (ZMod 2)) (hcert : T * S + X * M = 1)
    {v : Vec n} (hv : M *ᵥ v = 0) : v = T *ᵥ (S *ᵥ v) := by
  have h : (T * S + X * M) *ᵥ v = v := by rw [hcert, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, add_zero] at h
  exact h.symm

/-- **Certificate gives the kernel's minimum-weight lower bound**: a kernel test over
`(lightVecs k k)` covers all of $\mathbb F_2^k$. -/
theorem ker_min_of_cert {r n k d : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2))
    (T : Matrix (Fin n) (Fin k) (ZMod 2)) (S : Matrix (Fin k) (Fin n) (ZMod 2))
    (X : Matrix (Fin n) (Fin r) (ZMod 2)) (hcert : T * S + X * M = 1)
    (hsp : (lightVecs k k).all (fun c => decide (c = 0 ∨ d ≤ hammingNorm (T *ᵥ c)))
      = true) :
    ∀ w : Vec n, w ≠ 0 → M *ᵥ w = 0 → d ≤ hammingNorm w := by
  intro w hne hw
  have hcoe : w = T *ᵥ (S *ᵥ w) := eq_smul_of_cert M T S X hcert hw
  have hc : S *ᵥ w ≠ 0 := by
    intro h0
    exact hne (by rw [hcoe, h0, Matrix.mulVec_zero])
  have hmem : S *ᵥ w ∈ lightVecs k k := by
    refine mem_lightVecs k k _ ?_
    rw [wtRec_eq_hammingNorm]
    change (Finset.univ.filter (fun i => (S *ᵥ w) i ≠ 0)).card ≤ k
    calc (Finset.univ.filter (fun i => (S *ᵥ w) i ≠ 0)).card
        ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = k := by simp
  rcases of_decide_eq_true (List.all_eq_true.mp hsp (S *ᵥ w) hmem) with h0 | hd
  · exact absurd h0 hc
  · rw [hcoe]
    exact hd

/-! ## The dimension side of the certificate: the kernel's dimension and the rank

`eq_smul_of_cert` uses only half of the certificate's information -- $TS + XM = 1$ gives
$\ker M \subseteq \mathrm{range}(T)$, that is $\dim\ker M \le k$.  The same certificate
carries two further **kernel-side readings**, both small matrix products:

* $M\,T = 0$: every column of $T$ lies in the kernel;
* $S\,T = 1$: $S$ is a left inverse for those column coordinates.

The two together turn $\le$ into $=$, so "the kernel's dimension is exactly $k$ and the
rank exactly $n - k$" is a theorem too.  For a seed matrix this route is cheaper than
counting the pivots of a row reduction by several orders of magnitude: a reduction of width
36 was measured running through the eight-million-heartbeat budget, while the two `decide`s
here are small matrix products. -/

/-- **Certificate gives the dimension of the kernel as the certificate's column count**:
$S$ gives a linear isomorphism from $\ker M$ to $\mathbb F_2^k$.

The two supplements are not extra hypotheses but readings of the same certificate: without
$M T = 0$ the range of $T$ could genuinely be smaller than the kernel, and without
$S T = 1$ the independence of those columns is undetermined. -/
theorem finrank_ker_eq_of_cert {r n k : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2))
    (T : Matrix (Fin n) (Fin k) (ZMod 2)) (S : Matrix (Fin k) (Fin n) (ZMod 2))
    (X : Matrix (Fin n) (Fin r) (ZMod 2)) (hcert : T * S + X * M = 1)
    (hMT : M * T = 0) (hST : S * T = 1) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker M.mulVecLin) = k := by
  let φ : ↥(LinearMap.ker M.mulVecLin) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun v => S *ᵥ (v : Vec n)
      map_add' := by
        intro v w
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c v
        change S *ᵥ (c • (v : Vec n)) = c • (S *ᵥ (v : Vec n))
        rw [Matrix.mulVec_smul] }
  have hker_of : ∀ v : ↥(LinearMap.ker M.mulVecLin), M *ᵥ (v : Vec n) = 0 := fun v => v.2
  have hbij : Function.Bijective φ := by
    constructor
    · intro v w hvw
      have hv : (v : Vec n) = T *ᵥ (S *ᵥ (v : Vec n)) :=
        eq_smul_of_cert M T S X hcert (hker_of v)
      have hw : (w : Vec n) = T *ᵥ (S *ᵥ (w : Vec n)) :=
        eq_smul_of_cert M T S X hcert (hker_of w)
      have hvw' : S *ᵥ (v : Vec n) = S *ᵥ (w : Vec n) := hvw
      exact Subtype.ext (by rw [hv, hw, hvw'])
    · intro u
      refine ⟨⟨T *ᵥ u, ?_⟩, ?_⟩
      · refine LinearMap.mem_ker.mpr ?_
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hMT]
        simp
      · show S *ᵥ (T *ᵥ u) = u
        rw [Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]
  have h := (LinearEquiv.ofBijective φ hbij).finrank_eq
  simpa [Module.finrank_fin_fun] using h

/-- **Certificate gives the rank**: `rank M = n - k` (`n` the number of columns of `M`,
`k` the number of columns of the certificate's `T`).

Same source as `ker_min_of_cert`: the kernel's dimension is $k$, so the rank is $n - k$. -/
theorem rank_eq_sub_of_cert {r n k : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2))
    (T : Matrix (Fin n) (Fin k) (ZMod 2)) (S : Matrix (Fin k) (Fin n) (ZMod 2))
    (X : Matrix (Fin n) (Fin r) (ZMod 2)) (hcert : T * S + X * M = 1)
    (hMT : M * T = 0) (hST : S * T = 1) : M.rank = n - k := by
  have hker := finrank_ker_eq_of_cert M T S X hcert hMT hST
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [hker, Module.finrank_fin_fun] at hsum
  change Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = n - k
  omega

end QECCertificates
