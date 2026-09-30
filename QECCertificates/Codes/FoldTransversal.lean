/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.BB18Anchor
import QECCertificates.GF2.RankEchelon

/-!
# Fold-transversal gates: a kernel-checked instance for the BB $[[18,4,4]]$ code

The gap being filled here is on the gate side. The rest of the package covers the **code
side** (dimension, distance, separation conditions); this module adds the **gate side**, by
turning "fault-tolerant logical gate" into an instance checked by the kernel.

The source is J. N. Eberhardt and V. Steffan,
*Logical Operators and Fold-Transversal Gates of Bivariate Bicycle Codes*,
IEEE Trans. Inf. Theory **71**, 1140–1152 (2025) (arXiv:2407.03973). The facts used below,
with their places in that paper (page and item numbers follow the arXiv v1 layout):

* **A BB code is a group-algebra code**: the bits of `C(c,d)` are two copies, one
  horizontal and one vertical, of $\mathbb Z_\ell\times\mathbb Z_m$, with
  $X_h=\prod_{g\in\operatorname{supp}c}X_{(hg^{-1})_h}
  \prod_{g\in\operatorname{supp}d}X_{(hg^{-1})_v}$ and $Z_h$ dual to it (§3.1 Eq. (5),
  p. 7; §4.1, p. 10).
* **An automorphism gives a swap-type gate**: multiplication by an element $t$ of $G$ is a
  code automorphism, giving the gate
  $\mathrm{SWAP}_\phi=\prod_g(\mathrm{SWAP}_{g_h,\phi(g_h)}\mathrm{SWAP}_{g_v,\phi(g_v)})$,
  which is always a logical gate (§3.3 Theorem 3.2, p. 9; §4.3, "we always obtain the
  swap-gates $\mathrm{SWAP}_x,\mathrm{SWAP}_y$", p. 13).
* **The standard ZX-duality gives a Hadamard-type gate**: $\tau_0$ exchanges the X-type and
  Z-type checks and, on bits, sends $g_h$ to $(g^{-1})_v$ and $g_v$ to $(g^{-1})_h$
  (§3.2, `σ` and `τ_0 t`, p. 8; §3.4 Theorem 3.3, p. 9; §4.3, "another fold-transversal
  gate arises from the ZX-duality $\tau_0$", p. 13).
* **A phase-type (CZ) gate**: this needs a group automorphism $\omega$ with
  $\omega^2=\mathrm{id}$ and **$\omega(c)=d$**, in $R=\mathbb F_2[G]$. Then
  $\tau_0\omega(g_h)=(\omega(g)^{-1})_h$ and $\tau_0\omega(g_v)=(\omega(g)^{-1})_v$, and
  the corresponding CZ gate is a logical gate (§3.5 Theorem 3.4, pp. 9–10). The
  **sufficient condition** the paper gives for BB codes is `symmetric` from Definition 4.9
  ($\ell=m$ and $c(x,y)=d(y,x)$, p. 13), for which taking $\omega$ to be the axis swap
  $x\leftrightarrow y$ works.

  **That BB18 satisfies this needs a word of its own, and it is not the paper's own
  statement**: BB18 does **not** satisfy Definition 4.9, since
  $d(y,x)=1+y^2+x^2=d\neq c$, but it does satisfy the **general hypothesis** of §3.5.
  Taking $\omega=(\text{axis swap})\circ\iota$, with $\iota:g\mapsto g^{-1}$ as in §3.2,
  gives $\omega^2=\mathrm{id}$, $\omega(x)=y^{-1}$, $\omega(y)=x^{-1}$ and
  $\omega(c)=1+y^{-1}+x^{-1}=1+y^2+x^2=d$. So **§3.5 Theorem 3.4 covers BB18, whereas the
  sentence in §4.3, which is about symmetric codes, does not cover it directly**. The
  `bb18FoldCz` below is the permutation induced by $\tau_0\omega$ on the physical bits; that
  it is a **code automorphism** is checked by the kernel in
  `bb18_foldCz_rows_x`/`bb18_foldCz_rows_z`, and that conclusion is independent of whether
  the algebraic details above are right.

## The BB18 parameters used here (recomputed entry by entry from `Codes/BB18Anchor.lean`)

$\ell=m=3$, $c=1+x+y$, $d=1+x^2+y^2$, $H_X=[A\mid B]$ and $H_Z=[B^{tr}\mid A^{tr}]$ with
$A=\rho(c)$ and $B=\rho(d)$ (§4.1 Remark 4.2, p. 11). This code has $H_X=H_Z$, since
$d=\iota(c)$ for the antipode $\iota:g\mapsto g^{-1}$ of §3.2, so it is also a
self-dual CSS code; every statement below is written against the check lists of **both
sides** and does not rely on that coincidence.

## Three machine-checked families of assertions

1. The `bb18_foldCz_rows` family: **every check row is again mapped to a check row** by the
   fold permutation (an automorphism, or ZX-duality); the corollaries `…_preserves_spanL`
   lift this to the level of row spaces.
2. The `bb18_foldCz_log0` family: **the induced logical action**, namely the images of the
   four explicit logical basis operators under the fold, together with the **explicit
   stabilizer correction** that pulls each image back to the logical basis (each by
   `by decide`).
3. The `bb18_foldCz_logical` family: **the fold maps a logical operator to a logical operator
   of the same weight**, the structural content of "the distance does not drop".

Assertion 3 also has a **general form** (`permVec_preserves_undetectable`, for an arbitrary
code and an arbitrary bit permutation; the BB18-specific version is
`bb18Log_permVec_undetectable`). Invariance of kernel membership and of row-space membership
under a permutation (`inKerB_permVec` and `permVec_mem_spanL_iff`, resting on the
relabelling lemma for the dot product `dotProduct_permVec`) makes "the image is still an
undetectable **nontrivial** operator" a structural theorem, of which the four
`bb18_*_undetectable` are instances. With that structural theorem in hand, "the image is
still an undetectable nontrivial operator" is no longer an open item, so the gaps listed
below do not include it.

**Trusted base**: nothing but `by decide`, that is, kernel reduction. Zero `sorry`, zero
custom axiom, zero `native_decide`.

## An independent second route

An independent Python implementation of the same route, using pure Python bit operations,
performing no row reduction and sharing no code with this module, recomputed every assertion
above: the images of the four permutations, kernel membership, absence from the row space and
weight for the four basis operators, the pairing matrix, independence modulo the row space,
the 16 fold actions, and the undetectability and weight of the fold images, 90 assertions in
all, every one of them in agreement. That implementation reads the two parity-check matrices
straight from `Codes/BB18Anchor.lean`, so the data has a single source and cannot drift
between two copies.

## What is not done here (stated plainly)

* **The `#print axioms` output**: the 56 gate-side assertions are part of the audit region of
  the root module, including the general structural lemma and the general form of assertion
  3, and a full build puts all of them at exactly `[propext, Classical.choice, Quot.sound]`.
* **The group generated by `SWAP_x` and `SWAP_y`**: for [[98,8,12]] the paper gives
  $C_2\times\mathrm{Sp}_2(\mathbb F_{2^3})$; this module establishes only that these gates
  are logical gates and which logical permutation each of them realizes, and does not compute
  the order of the generated group.
-/

namespace QECCertificates

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. Carrying vectors along a permutation of the physical bits -/

/-- The **pushforward** of a GF(2) vector along a permutation `π`:
`(permVec π v) i = v (π⁻¹ i)`.

The support as a whole is carried to its image under `π`. This carry is exactly what a
fold-transversal gate does at the operator level: the single-qubit gates H and S only
multiply by a phase, while `SWAP` and `CZ` move the support along the orbits of the
permutation (§3.3–§3.5). -/
def permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) : Vec n := fun i => v (π.symm i)

@[simp] lemma permVec_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) (i : Fin n) :
    permVec π v i = v (π.symm i) := rfl

/-- The support is carried to its image under `π`. -/
theorem support_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    support (permVec π v) = (support v).image π := by
  ext i
  simp only [mem_support, Finset.mem_image]
  constructor
  · intro h
    exact ⟨π.symm i, h, π.apply_symm_apply i⟩
  · rintro ⟨j, hj, rfl⟩
    simpa [permVec] using hj

/-- **Weight is preserved**: a permutation does not change the Hamming weight.

This is the first half of "a fold does not lower the effective distance": the weight of any
operator is **exactly the same** before and after the fold, so a fold cannot make a heavy
codeword light. -/
theorem hammingNorm_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    hammingNorm (permVec π v) = hammingNorm v := by
  rw [← weight_eq_hammingNorm, ← weight_eq_hammingNorm, support_permVec]
  exact Finset.card_image_of_injective _ π.injective

/-- **Row spaces are preserved**: if `π` keeps every row of the row list `L` inside the
row space of `L`, then it preserves the whole row space.

This is the **row-space form of "the permutation is a code automorphism"**: the stabilizer
generators map to combinations of generators, hence the whole stabilizer group maps to
itself. The proof follows `Submodule.span_induction`; `permVec` is linear coordinate by
coordinate, and the three linearity steps are each a pointwise `rfl`. -/
theorem permVec_mem_spanL {n : ℕ} (π : Equiv.Perm (Fin n)) {L : List (Vec n)}
    (h : ∀ r ∈ L, permVec π r ∈ spanL L) {v : Vec n} (hv : v ∈ spanL L) :
    permVec π v ∈ spanL L := by
  refine Submodule.span_induction (p := fun x _ => permVec π x ∈ spanL L) ?_ ?_ ?_ ?_ hv
  · intro r hr
    exact h r hr
  · have h0 : permVec π (0 : Vec n) = 0 := by funext i; simp [permVec]
    rw [h0]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    have hadd : permVec π (x + y) = permVec π x + permVec π y := by
      funext i; simp [permVec, Pi.add_apply]
    rw [hadd]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    have hsmul : permVec π (c • x) = c • permVec π x := by
      funext i; simp [permVec, Pi.smul_apply]
    rw [hsmul]
    exact Submodule.smul_mem _ _ hx

/-! ### Invariance of the dot product, the kernel and the row space under a permutation

What a fold-transversal gate does at the operator level is the **carry of the support**
`permVec π`. Showing that it takes undetectable operators to undetectable operators requires
two things to be invariant under the permutation: **kernel membership**, that is, the pairing
with every check row being zero, and **row-space membership**, that is, not lying in the
stabilizer group. The first comes from invariance of the dot product under a permutation, the
second from completing `permVec_mem_spanL` in the other direction. Both are structural
theorems stated for an **arbitrary** permutation, depending on no particular code and on no
`decide`. -/

/-- `permVec` is a group action on `Vec n`: carrying with `π` and then back with `π⁻¹`
leaves the vector unchanged. -/
@[simp] lemma permVec_symm_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    permVec π.symm (permVec π v) = v := by
  funext i; simp [permVec]

/-- The previous statement in the other direction. -/
@[simp] lemma permVec_permVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Vec n) :
    permVec π (permVec π.symm v) = v := by
  funext i; simp [permVec]

/-- **Invariance of the dot product under a permutation**: carrying both factors does not
change the GF(2) dot product.

The notation `⬝ᵥ` is a sum of coordinatewise products, and a permutation merely relabels the
summation index (`Equiv.sum_comp`), so this is a direct consequence of a sum not depending on
how its index is named. It is also the **entire algebraic content** of the invariance of
kernel membership: the pairing of `x` with a check row `r` equals the pairing of the carried
`x` with the carried `r`. -/
theorem dotProduct_permVec {n : ℕ} (π : Equiv.Perm (Fin n)) (v w : Vec n) :
    (permVec π v) ⬝ᵥ (permVec π w) = v ⬝ᵥ w := by
  rw [dotProduct, dotProduct]
  simp only [permVec_apply]
  exact Equiv.sum_comp π.symm (fun j => v j * w j)

/-- **The relabelling form of the dot product, on one side**: carrying only the right
factor is the same as carrying the left factor with `π⁻¹`.

The kernel membership test `inKerB M x` says that every row of `M` pairs to zero with `x`.
Replacing `x` by the `permVec π x` of interest here turns the pairing into
`M i ⬝ᵥ permVec π x = (permVec π⁻¹ (M i)) ⬝ᵥ x`, so "the image is still in the kernel"
reduces to "`π⁻¹` still maps check rows to check rows". -/
theorem dotProduct_permVec_left {n : ℕ} (π : Equiv.Perm (Fin n)) (a b : Vec n) :
    a ⬝ᵥ (permVec π b) = (permVec π.symm a) ⬝ᵥ b := by
  rw [dotProduct, dotProduct]
  simp only [permVec_apply, Equiv.symm_symm]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp π (fun i => a i * b (π.symm i))).symm

/-- **Invariance of the row space under a permutation, in both directions**: if the row
list `L` is invariant under `π` and under its inverse, then `π` preserves the row space
of `L`.

One direction, `v ∈ spanL L → permVec π v ∈ spanL L`, is `permVec_mem_spanL`; the other
applies the same statement to `π⁻¹` and recovers the result with
`permVec π.symm (permVec π v) = v`. Both directions are needed: it is the other direction
that gives "the image is still a **nontrivial** operator" in assertion 3, since if the image
lay in the row space then so would the preimage, contradicting the preimage being
nontrivial. -/
theorem permVec_mem_spanL_iff {n : ℕ} (π : Equiv.Perm (Fin n)) {L : List (Vec n)}
    (h : ∀ r ∈ L, permVec π r ∈ L) (h' : ∀ r ∈ L, permVec π.symm r ∈ L) {v : Vec n} :
    permVec π v ∈ spanL L ↔ v ∈ spanL L := by
  constructor
  · intro hv
    have hmem : permVec π.symm (permVec π v) ∈ spanL L :=
      permVec_mem_spanL π.symm (fun r hr => subset_spanL (h' r hr)) hv
    rwa [permVec_symm_permVec] at hmem
  · intro hv
    exact permVec_mem_spanL π (fun r hr => subset_spanL (h r hr)) hv

/-- **Invariance of kernel membership under a permutation**: if `π⁻¹` still maps every
row of `M` to some row of `M`, then `π` maps the kernel of `M` to itself.

The proof is `dotProduct_permVec_left` plus one relabelling: `M i ⬝ᵥ permVec π x` equals
`permVec π⁻¹ (M i) ⬝ᵥ x`, and by hypothesis the latter is the pairing of some row `M j`
with `x`, which is known to be zero. -/
theorem inKerB_permVec {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (π : Equiv.Perm (Fin n)) (h : ∀ i, permVec π.symm (M i) ∈ List.ofFn M)
    {x : Vec n} (hx : inKerB M x = true) : inKerB M (permVec π x) = true := by
  unfold inKerB at hx ⊢
  rw [List.all_eq_true] at hx ⊢
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (h i)
  have hleft : (M i) ⬝ᵥ (permVec π x) = (M j) ⬝ᵥ x := by
    rw [dotProduct_permVec_left, ← hj]
  rw [hleft]
  exact hx _ (by rw [List.mem_ofFn]; exact ⟨j, rfl⟩)

/-- **The general form of assertion 3, for an arbitrary code and an arbitrary
permutation**: if a bit permutation `π` maps the rows of the parity-check matrix `M`, through
`π⁻¹`, and the row list `L`, through `π` and its inverse, to themselves, then it maps an
operator that is undetectable with respect to `M` and outside the row space of `L` to an
operator of **the same weight and the same property**.

This is the general content of "a transversal gate does not lower the effective distance":
undetectability comes from `inKerB_permVec`, nontriviality, that is, not lying in the
stabilizer group, from the other direction of `permVec_mem_spanL_iff`, and the weight from
`hammingNorm_permVec`. None of the three is a computation over individual operators. -/
theorem permVec_preserves_undetectable {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (L : List (Vec n)) (π : Equiv.Perm (Fin n))
    (hM : ∀ i, permVec π.symm (M i) ∈ List.ofFn M)
    (hL : ∀ r ∈ L, permVec π r ∈ L) (hL' : ∀ r ∈ L, permVec π.symm r ∈ L)
    {x : Vec n} (hk : inKerB M x = true) (hs : inSpanEch L x = false) :
    inKerB M (permVec π x) = true ∧ inSpanEch L (permVec π x) = false ∧
      hammingNorm (permVec π x) = hammingNorm x :=
  ⟨inKerB_permVec M π hM hk,
   by
     rw [inSpanEch_eq_false_iff] at hs ⊢
     exact fun hcon => hs ((permVec_mem_spanL_iff π hL hL').mp hcon),
   hammingNorm_permVec π x⟩

/-! ## 2. The four fold permutations of BB18

Bit numbering convention: `q < 9` is the $h$ block, where the group-element index `3i+j`
stands for $x^iy^j$, and `q ≥ 9` is the $v$ block with the same index. All four permutations
are concrete permutations of `Fin 18` with both directions given explicitly, so `decide` can
reduce them directly; `Function.invFun` would block the reduction. -/

/-- **The phase-type (CZ) fold $\tau_0\omega$**: $\omega(x)=y^{-1}$ and $\omega(y)=x^{-1}$,
which inside each block sends $x^iy^j$ to $x^jy^i$, the mirror image of the lattice along the
diagonal (§3.5 p. 9, §4.3 p. 13). It is an involution whose fixed points are those with
$i=j$, the $G_0$ of §3.5; the remaining bits fall into pairs, each carrying one CZ.

For BB18, $c=1+x+y$ and $d=1+x^2+y^2$, and
$\omega(c)=1+y^{-1}+x^{-1}=1+y^2+x^2=d$ meets the hypothesis of §3.5, while
$\omega^2=\mathrm{id}$ is verified directly. -/
def bb18FoldCz : Equiv.Perm (Fin 18) where
  toFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 12, 15, 10, 13, 16, 11, 14, 17]
  invFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 12, 15, 10, 13, 16, 11, 14, 17]
  left_inv := by decide
  right_inv := by decide

/-- **The Hadamard-type fold $\tau_0$**: $g_h\mapsto(g^{-1})_v$ and
$g_v\mapsto(g^{-1})_h$ (§3.2 p. 8, §3.4 Theorem 3.3 p. 9). It has no fixed bit, only the 9
pairs $(g_h,(g^{-1})_v)$. -/
def bb18FoldH : Equiv.Perm (Fin 18) where
  toFun := ![9, 11, 10, 15, 17, 16, 12, 14, 13, 0, 2, 1, 6, 8, 7, 3, 5, 4]
  invFun := ![9, 11, 10, 15, 17, 16, 12, 14, 13, 0, 2, 1, 6, 8, 7, 3, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- **The swap-type gate $\mathrm{SWAP}_x$**: multiplication by $x$ on $G$ (§3.3
Theorem 3.2 p. 9, §4.3 p. 13). It has order three, with 6 three-cycles. -/
def bb18ShiftX : Equiv.Perm (Fin 18) where
  toFun := ![3, 4, 5, 6, 7, 8, 0, 1, 2, 12, 13, 14, 15, 16, 17, 9, 10, 11]
  invFun := ![6, 7, 8, 0, 1, 2, 3, 4, 5, 15, 16, 17, 9, 10, 11, 12, 13, 14]
  left_inv := by decide
  right_inv := by decide

/-- **The swap-type gate $\mathrm{SWAP}_y$**: multiplication by $y$ on $G$. -/
def bb18ShiftY : Equiv.Perm (Fin 18) where
  toFun := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 16, 17, 15]
  invFun := ![2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13, 17, 15, 16]
  left_inv := by decide
  right_inv := by decide

/-! ## 3. Assertion 1: the fold permutations are code automorphisms (checks map to checks)

This uses self-maps of row lists rather than `inSpanB`: for a wide row list with $n=18$ the
former is an element-by-element comparison while the latter runs row reduction internally,
which measurably differs by an order of magnitude. A self-map of the row list is **stronger**
than preservation of the row space, and it is exactly what is wanted here, namely that each
stabilizer generator maps to a generator of the same stabilizer group. -/

/-- Membership extraction on a list of vectors for "every row maps into the target list",
in the `List.all` form, which `by decide` can reduce. -/
theorem mem_of_list_all {α : Type*} [DecidableEq α] {f : α → α} {L M : List α} {r : α}
    (h : L.all (fun u => decide (f u ∈ M)) = true) (hr : r ∈ L) : f r ∈ M := by
  rw [List.all_eq_true] at h
  simpa using h r hr

/-- A self-map lifted to the level of row spaces. -/
theorem mem_spanL_of_list_all {n : ℕ} {f : Vec n → Vec n} {L M : List (Vec n)} {r : Vec n}
    (h : L.all (fun u => decide (f u ∈ M)) = true) (hr : r ∈ L) : f r ∈ spanL M :=
  subset_spanL (mem_of_list_all h hr)

/-- The hypothesis that `inKerB_permVec` needs, obtained from invariance of the row list
under `π⁻¹`: from the `List.all` form to the `∀ i` form.

This bridges the `List.all` statement of invariance of the row set, which `by decide` can
reduce, and the `∀ i` statement the general lemma requires. -/
lemma kerRows_of_list_all {n k : ℕ} {M : Matrix (Fin k) (Fin n) (ZMod 2)}
    {L : List (Vec n)} {π : Equiv.Perm (Fin n)} (hM : List.ofFn M = L)
    (h : L.all (fun r => decide (permVec π.symm r ∈ L)) = true) :
    ∀ i, permVec π.symm (M i) ∈ List.ofFn M := by
  intro i
  rw [hM]
  exact mem_of_list_all h (by rw [← hM]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)

-- CZ 折叠：X 校验行 ↦ X 校验行
theorem bb18_foldCz_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18FoldCz r ∈ bb18Rx)) = true := by decide

-- CZ 折叠：Z 校验行 ↦ Z 校验行
theorem bb18_foldCz_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18FoldCz r ∈ bb18Rz)) = true := by decide

-- Hadamard 折叠：X 校验行 ↦ Z 校验行（ZX-对偶，交换两侧）
theorem bb18_foldH_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18FoldH r ∈ bb18Rz)) = true := by decide

-- Hadamard 折叠：Z 校验行 ↦ X 校验行
theorem bb18_foldH_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18FoldH r ∈ bb18Rx)) = true := by decide

-- swap 型（x 方向平移）
theorem bb18_shiftX_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18ShiftX r ∈ bb18Rx)) = true := by decide

theorem bb18_shiftX_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18ShiftX r ∈ bb18Rz)) = true := by decide

-- swap 型（y 方向平移）
theorem bb18_shiftY_rows_x :
    bb18Rx.all (fun r => decide (permVec bb18ShiftY r ∈ bb18Rx)) = true := by decide

theorem bb18_shiftY_rows_z :
    bb18Rz.all (fun r => decide (permVec bb18ShiftY r ∈ bb18Rz)) = true := by decide

/-- **The same facts in the direction of the inverse permutation**: the eight statements
above use only the forward direction, whereas invariance of the kernel and of the row space
(`inKerB_permVec`, `permVec_mem_spanL_iff`) requires the **inverse** permutation to preserve
the row set as well. The four statements below supply that half. For the involutions
(`bb18FoldCz`, `bb18FoldH`) the inverse is the forward permutation itself, and for the
order-three elements (`bb18ShiftX`, `bb18ShiftY`) it is `π² = π⁻¹`.

The statements are written against `bb18Rz`: this code has $H_X = H_Z$, with `bb18Rx` and
`bb18Rz` the same literal list, so one fact holds of the row lists of both sides. -/

theorem bb18_foldCz_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18FoldCz.symm r ∈ bb18Rz)) = true := by decide

theorem bb18_foldH_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18FoldH.symm r ∈ bb18Rz)) = true := by decide

theorem bb18_shiftX_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18ShiftX.symm r ∈ bb18Rz)) = true := by decide

theorem bb18_shiftY_rows_symm :
    bb18Rz.all (fun r => decide (permVec bb18ShiftY.symm r ∈ bb18Rz)) = true := by decide

/-- **The CZ fold preserves the X row space** (an automorphism, X side). -/
theorem bb18_foldCz_preserves_spanL_x {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18FoldCz v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldCz_rows_x hr) hv

/-- **The CZ fold preserves the Z row space** (an automorphism, Z side). -/
theorem bb18_foldCz_preserves_spanL_z {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18FoldCz v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldCz_rows_z hr) hv

/-- **The Hadamard fold sends the X row space to the Z row space** (ZX-duality; by §3.2,
$\tau_0$ exchanges the two sides). -/
theorem bb18_foldH_maps_spanL_xz {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18FoldH v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldH_rows_x hr) hv

/-- **The Hadamard fold sends the Z row space to the X row space**. -/
theorem bb18_foldH_maps_spanL_zx {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18FoldH v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_foldH_rows_z hr) hv

/-- **The swap-type gate preserves the X row space** (§3.3 Theorem 3.2). -/
theorem bb18_shiftX_preserves_spanL_x {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18ShiftX v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftX_rows_x hr) hv

theorem bb18_shiftX_preserves_spanL_z {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18ShiftX v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftX_rows_z hr) hv

theorem bb18_shiftY_preserves_spanL_x {v : Vec 18} (hv : v ∈ spanL bb18Rx) :
    permVec bb18ShiftY v ∈ spanL bb18Rx :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftY_rows_x hr) hv

theorem bb18_shiftY_preserves_spanL_z {v : Vec 18} (hv : v ∈ spanL bb18Rz) :
    permVec bb18ShiftY v ∈ spanL bb18Rz :=
  permVec_mem_spanL _ (fun _ hr => mem_spanL_of_list_all bb18_shiftY_rows_z hr) hv

/-! ## 4. Assertion 2: the induced logical action

The logical space is the quotient $\ker H_Z/\operatorname{rowspace}H_X$, of dimension $k=4$
(`bb18_k`: $18-7-7=4$). Below, **four explicit logical operators** are given as a basis of
it, each with a **dual witness** that lies in $\ker H_X$ and pairs to 1 with it:

| basis operator | support | dual witness | support |
|---|---|---|---|
| $L_0$ | `{4,13,14,16}` | $D_0$ | `{2,12,13,14,16,17}` |
| $L_1$ | `{3,12,13,15}` | $D_1$ | `{0,12,13,14,15,17}` |
| $L_2$ | `{0,2,15,16}` | $D_2$ | `{9,11,12,13,16,17}` |
| $L_3$ | `{0,1,16,17}` | $D_3$ | `{10,11,12,14,15,16}` |

All four have weight 4, which is the code distance. That they are logical operators is given
by two **row-by-row pairing** assertions only (`mem_ker_of_inKerB` together with
`not_mem_rowSpace_of_dualCheck`), with **no row reduction**; independence modulo the row
space is given by the rank assertion of `rankEchelon`, the rank rising from 7 to 11.

**An honest remark**: this basis is the product of a **finite search**, taking the
minimum-weight representative of each of the 128 cosets of the row space inside $\ker H_X$
and then a quadruple whose pairing matrix is the identity. The search was used only to
**find** the numbers, not to **prove** anything: every property in the table above is
recomputed inside the kernel by the `by decide` proofs below. -/

/-- The logical basis operator $L_0$. -/
def bb18Log0 : Vec 18 := e 4 + e 13 + e 14 + e 16

/-- The logical basis operator $L_1$. -/
def bb18Log1 : Vec 18 := e 3 + e 12 + e 13 + e 15

/-- The logical basis operator $L_2$. -/
def bb18Log2 : Vec 18 := e 0 + e 2 + e 15 + e 16

/-- The logical basis operator $L_3$. -/
def bb18Log3 : Vec 18 := e 0 + e 1 + e 16 + e 17

/-- The four logical basis operators as a function, for compact statements. -/
def bb18Log : Fin 4 → Vec 18 := ![bb18Log0, bb18Log1, bb18Log2, bb18Log3]

/-- The dual witness of $L_0$. -/
def bb18Dual0 : Vec 18 := e 2 + e 12 + e 13 + e 14 + e 16 + e 17

/-- The dual witness of $L_1$. -/
def bb18Dual1 : Vec 18 := e 0 + e 12 + e 13 + e 14 + e 15 + e 17

/-- The dual witness of $L_2$. -/
def bb18Dual2 : Vec 18 := e 9 + e 11 + e 12 + e 13 + e 16 + e 17

/-- The dual witness of $L_3$. -/
def bb18Dual3 : Vec 18 := e 10 + e 11 + e 12 + e 14 + e 15 + e 16

/-- A partial sum of check rows, which over GF(2) is an XOR. The image of a logical
operator under a fold equals a logical combination plus a sum of stabilizers, and this is how
that sum of stabilizers is written; the row numbers come from the `bb18Hx` row table of
`Codes/BB18Anchor.lean`. -/
def rowSum (s : List (Fin 9)) : Vec 18 := (s.map (fun j => bb18Hx j)).sum

/-- $L_0$ is a logical operator: it lies in $\ker H_Z$ and not in the row space of
$H_X$. -/
theorem bb18Log0_logical :
    bb18Log0 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log0 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual0) (by decide) (by decide)⟩

/-- $L_1$ is a logical operator. -/
theorem bb18Log1_logical :
    bb18Log1 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log1 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual1) (by decide) (by decide)⟩

/-- $L_2$ is a logical operator. -/
theorem bb18Log2_logical :
    bb18Log2 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log2 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual2) (by decide) (by decide)⟩

/-- $L_3$ is a logical operator. -/
theorem bb18Log3_logical :
    bb18Log3 ∈ LinearMap.ker bb18Hz.toLin' ∧ bb18Log3 ∉ bb18Hx.rowSpace :=
  ⟨mem_ker_of_inKerB bb18Hz (by decide),
   not_mem_rowSpace_of_dualCheck bb18Hx (w := bb18Dual3) (by decide) (by decide)⟩

/-- **The four classes are linearly independent modulo the row space**: together with the
check rows the rank is $7+4=11=\dim\ker H_Z$, so they are exactly a basis of the logical
space, and the $k=4$ given by `bb18_k` is realized explicitly here. -/
theorem bb18_logical_independent :
    rankEchelon (bb18Rx ++ [bb18Log0, bb18Log1, bb18Log2, bb18Log3]) = 11 := by decide

/-! ### The action induced on the logical basis

Each assertion pulls the **image** back to the logical basis:
`θ(L_i) + (stabilizer correction) = row sum`. The row sum on the right lies in
$\operatorname{rowspace}H_X$, so the assertion says verbatim that $\theta$ sends the logical
class $[L_i]$ to $[\,\sum_j c_j L_j\,]$. That is the logical gate this gate implements. -/

/-- **The CZ fold is the identity on $L_0$**, which is a fixed point of the fold: its
support `{4,13,14,16}` lies entirely on the fixed orbit $i=j$. -/
theorem bb18_foldCz_log0 : permVec bb18FoldCz bb18Log0 = bb18Log0 := by decide

/-- **CZ fold: $[L_1]\mapsto[L_0+L_1]$**. -/
theorem bb18_foldCz_log1 :
    permVec bb18FoldCz bb18Log1 + bb18Log0 + bb18Log1 = rowSum [4, 5, 7] := by decide

/-- **CZ fold: $[L_2]\mapsto[L_0+L_2]$**. -/
theorem bb18_foldCz_log2 :
    permVec bb18FoldCz bb18Log2 + bb18Log0 + bb18Log2 = rowSum [2, 4, 6] := by decide

/-- **CZ fold: $[L_3]\mapsto[L_1+L_2+L_3]$**. -/
theorem bb18_foldCz_log3 :
    permVec bb18FoldCz bb18Log3 + bb18Log1 + bb18Log2 + bb18Log3 = rowSum [6, 7, 8] :=
  by decide

/-- **Hadamard fold: $[L_0]\mapsto[L_0+L_1+L_2]$**, this gate exchanging the X and Z
sides (§3.4). -/
theorem bb18_foldH_log0 :
    permVec bb18FoldH bb18Log0 + bb18Log0 + bb18Log1 + bb18Log2 = rowSum [2, 4, 5] :=
  by decide

/-- **Hadamard fold: $[L_1]\mapsto[L_1+L_3]$**. -/
theorem bb18_foldH_log1 :
    permVec bb18FoldH bb18Log1 + bb18Log1 + bb18Log3 = rowSum [6, 7] := by decide

/-- **Hadamard fold: $[L_2]\mapsto[L_2+L_3]$**. -/
theorem bb18_foldH_log2 :
    permVec bb18FoldH bb18Log2 + bb18Log2 + bb18Log3 = rowSum [0, 2] := by decide

/-- **Hadamard fold: $[L_3]\mapsto[L_3]$**, up to a stabilizer. -/
theorem bb18_foldH_log3 :
    permVec bb18FoldH bb18Log3 + bb18Log3 = rowSum [1, 2] := by decide

/-- **The swap-type gate $\mathrm{SWAP}_x$: $[L_0]\mapsto[L_1]$**. -/
theorem bb18_shiftX_log0 :
    permVec bb18ShiftX bb18Log0 + bb18Log1 = rowSum [0, 1, 2, 4] := by decide

/-- **$\mathrm{SWAP}_x$: $[L_1]\mapsto[L_0+L_1]$**. -/
theorem bb18_shiftX_log1 :
    permVec bb18ShiftX bb18Log1 + bb18Log0 + bb18Log1 = rowSum [3] := by decide

/-- **$\mathrm{SWAP}_x$: $[L_2]\mapsto[L_2+L_3]$**. -/
theorem bb18_shiftX_log2 :
    permVec bb18ShiftX bb18Log2 + bb18Log2 + bb18Log3 = rowSum [0, 2] := by decide

/-- **$\mathrm{SWAP}_x$: $[L_3]\mapsto[L_2]$**. -/
theorem bb18_shiftX_log3 :
    permVec bb18ShiftX bb18Log3 + bb18Log2 = rowSum [0, 1] := by decide

/-- **The swap-type gate $\mathrm{SWAP}_y$: $[L_0]\mapsto[L_0+L_1]$**. -/
theorem bb18_shiftY_log0 :
    permVec bb18ShiftY bb18Log0 + bb18Log0 + bb18Log1 = rowSum [0, 1, 2] := by decide

/-- **$\mathrm{SWAP}_y$: $[L_1]\mapsto[L_0]$**, with no stabilizer correction. -/
theorem bb18_shiftY_log1 : permVec bb18ShiftY bb18Log1 = bb18Log0 := by decide

/-- **$\mathrm{SWAP}_y$: $[L_2]\mapsto[L_3]$**, with no stabilizer correction. -/
theorem bb18_shiftY_log2 : permVec bb18ShiftY bb18Log2 = bb18Log3 := by decide

/-- **$\mathrm{SWAP}_y$: $[L_3]\mapsto[L_2+L_3]$**, with no stabilizer correction. -/
theorem bb18_shiftY_log3 :
    permVec bb18ShiftY bb18Log3 + bb18Log2 + bb18Log3 = 0 := by decide

/-! ## 5. Assertion 3: the distance does not drop

There are two concrete grounds for "a fold does not lower the effective distance".

1. **The weight is preserved exactly** (`hammingNorm_permVec`): a permutation does not
   change the Hamming weight of any operator, so it can neither make a heavy logical
   operator light nor a light one heavy.
2. **A check generator remains a check generator under the fold** (§3), so both the kernel
   and the row space are preserved, and the fold maps the set of undetectable nontrivial
   operators to itself.

Together: the least weight of a logical operator is the same number before and after the
fold. Below, item 1 is carried out for each of the four folds, and it is machine-checked that
under all four folds the four basis operators remain undetectable of weight 4.

**Item 2 is a general theorem.** The **general** invariance of `inKerB` and of `spanL` under
a permutation (`inKerB_permVec` and `permVec_mem_spanL_iff`, which is derived from the
relabelling lemma for the dot product `dotProduct_permVec`) raises "the image is still an
undetectable operator" from an operator-by-operator instance to the structural theorem
`permVec_preserves_undetectable`, stated for an arbitrary code and an arbitrary permutation,
and its BB18 instance `bb18Log_permVec_undetectable`. The four `_undetectable` theorems below
are applications of that theorem: all that `decide` still has to do is the already computed
fact that `bb18Log i` is itself a logical operator of weight 4, and preservation of the
kernel, of the row space and of the weight is no longer recomputed operator by operator.

**A note on what is claimed, stated plainly**: for a code automorphism, "the code distance is
4 before and after the fold" is a tautology. This module does not restate it. What it
provides is the first two items above, which are the substance of "a transversal gate leaves
the effective distance alone", together with the general theorem and its four instances. -/

/-- The CZ fold preserves the weight of every operator. -/
theorem bb18_foldCz_weight (v : Vec 18) :
    hammingNorm (permVec bb18FoldCz v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- The Hadamard fold preserves the weight of every operator. -/
theorem bb18_foldH_weight (v : Vec 18) :
    hammingNorm (permVec bb18FoldH v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- $\mathrm{SWAP}_x$ preserves the weight of every operator. -/
theorem bb18_shiftX_weight (v : Vec 18) :
    hammingNorm (permVec bb18ShiftX v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- $\mathrm{SWAP}_y$ preserves the weight of every operator. -/
theorem bb18_shiftY_weight (v : Vec 18) :
    hammingNorm (permVec bb18ShiftY v) = hammingNorm v :=
  hammingNorm_permVec _ v

/-- **Assertion 3 for BB18, holding for an arbitrary automorphism permutation**: if a bit
permutation `π` preserves the row sets of both parity checks, in that `π⁻¹` still maps every
row of `bb18Hz` to one of its rows, and preserves the X row list `bb18Rx` under `π` and under
`π⁻¹`, then the images of the four logical basis operators under `π` are again
**undetectable nontrivial operators of weight 4**.

The structural part is supplied in one step by `permVec_preserves_undetectable`, leaving
`decide` only the already computed fact that `bb18Log i` is itself a logical operator of
weight 4. -/
theorem bb18Log_permVec_undetectable (π : Equiv.Perm (Fin 18))
    (hM : ∀ i : Fin 9, permVec π.symm (bb18Hz i) ∈ List.ofFn (bb18Hz))
    (hL : ∀ r ∈ bb18Rx, permVec π r ∈ bb18Rx)
    (hL' : ∀ r ∈ bb18Rx, permVec π.symm r ∈ bb18Rx)
    (i : Fin 4) :
    inKerB bb18Hz (permVec π (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec π (bb18Log i)) = false ∧
    hammingNorm (permVec π (bb18Log i)) = 4 := by
  obtain ⟨h1, h2, h3⟩ := permVec_preserves_undetectable bb18Hz bb18Rx π hM hL hL'
    (x := bb18Log i) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  exact ⟨h1, h2, by rw [h3]; fin_cases i <;> decide⟩

/-- **The CZ fold maps a logical basis operator to an undetectable nontrivial operator of
weight 4**, an instance of the general theorem.

The `inKerB` side is the vanishing of the pairing with every Z-type check, the
`inSpanEch … = false` side is absence from the row space of $H_X$, and the last conjunct is
the weight. All three, being the structural part, come from
`bb18Log_permVec_undetectable` and agree with the code distance 4. -/
theorem bb18_foldCz_undetectable (i : Fin 4) :
    inKerB bb18Hz (permVec bb18FoldCz (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec bb18FoldCz (bb18Log i)) = false ∧
    hammingNorm (permVec bb18FoldCz (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18FoldCz
    (kerRows_of_list_all bb18_ofFn_z bb18_foldCz_rows_symm)
    (fun _ hr => mem_of_list_all bb18_foldCz_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_foldCz_rows_symm hr) i

/-- **The Hadamard fold, the ZX-duality, maps a logical basis operator to an undetectable
nontrivial operator of weight 4**.

Note the **exchange** of the two sides: $\tau_0$ sends X-type checks to Z-type checks
(§3.2), so the image lies in $\ker H_X$ and outside the row space of $H_Z$. This is the
machine-checked form of §3.2 Remark 3.1, "$\tau_0$ exchanges logical $Z$-operators and
$X$-operators". Since this code has $H_X = H_Z$, with `bb18Rx` and `bb18Rz` the same literal
list, the `bb18Hz`/`bb18Rx` version of the general theorem can be reused here by definitional
equality. -/
theorem bb18_foldH_undetectable (i : Fin 4) :
    inKerB bb18Hx (permVec bb18FoldH (bb18Log i)) = true ∧
    inSpanEch bb18Rz (permVec bb18FoldH (bb18Log i)) = false ∧
    hammingNorm (permVec bb18FoldH (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18FoldH
    (kerRows_of_list_all bb18_ofFn_x bb18_foldH_rows_symm)
    (fun _ hr => mem_of_list_all bb18_foldH_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_foldH_rows_symm hr) i

/-- **$\mathrm{SWAP}_x$ maps a logical basis operator to an undetectable nontrivial
operator of weight 4**, an instance of the general theorem. -/
theorem bb18_shiftX_undetectable (i : Fin 4) :
    inKerB bb18Hz (permVec bb18ShiftX (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec bb18ShiftX (bb18Log i)) = false ∧
    hammingNorm (permVec bb18ShiftX (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18ShiftX
    (kerRows_of_list_all bb18_ofFn_z bb18_shiftX_rows_symm)
    (fun _ hr => mem_of_list_all bb18_shiftX_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_shiftX_rows_symm hr) i

/-- **$\mathrm{SWAP}_y$ maps a logical basis operator to an undetectable nontrivial
operator of weight 4**, an instance of the general theorem. -/
theorem bb18_shiftY_undetectable (i : Fin 4) :
    inKerB bb18Hz (permVec bb18ShiftY (bb18Log i)) = true ∧
    inSpanEch bb18Rx (permVec bb18ShiftY (bb18Log i)) = false ∧
    hammingNorm (permVec bb18ShiftY (bb18Log i)) = 4 :=
  bb18Log_permVec_undetectable bb18ShiftY
    (kerRows_of_list_all bb18_ofFn_z bb18_shiftY_rows_symm)
    (fun _ hr => mem_of_list_all bb18_shiftY_rows_x hr)
    (fun _ hr => mem_of_list_all bb18_shiftY_rows_symm hr) i

end QECCertificates
