/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
import QECCertificates.Homology.ModuleExpansion

/-!
# Linear-algebra core for the three declared scope boundaries

This module is independent of numerical searches and external solvers. It proves
the zero-homology criterion, and a cleaning/triangle-inequality distance theorem
for a legal CSS coupling. The Künneth identity is supplied by the existing library
in `Codes/FaultComplexKunneth`; it is not asserted as an axiom here. The
`#print axioms` of the load-bearing declarations are printed in the audit region at
the end of the root module `QECCertificates.lean`.
-/

namespace QECCertificates.Homology

section Exactness

variable {K A B C : Type*} [Field K]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module K A] [Module K B] [Module K C] [FiniteDimensional K B]

/-- Zero middle Betti number is equivalent to exactness, provided this is a complex. -/
theorem betti_zero_iff_exact (a : A →ₗ[K] B) (b : B →ₗ[K] C)
    (h : LinearMap.range a ≤ LinearMap.ker b) :
    Module.finrank K (LinearMap.ker b) - Module.finrank K (LinearMap.range a) = 0 ↔
      LinearMap.ker b = LinearMap.range a := by
  constructor
  · intro hz
    have heq : Module.finrank K (LinearMap.range a) =
        Module.finrank K (LinearMap.ker b) := by
      have hle := Submodule.finrank_mono h
      omega
    exact (Submodule.eq_of_le_of_finrank_eq h heq).symm
  · intro heq
    rw [heq, Nat.sub_self]

theorem kernel_dim_zero_iff (b : B →ₗ[K] C) :
    Module.finrank K (LinearMap.ker b) = 0 ↔ Function.Injective b := by
  rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]

/-- Universal rank criterion for any finite-dimensional middle, not just Koszul. -/
theorem exact_iff_rank_sum (a : A →ₗ[K] B) (b : B →ₗ[K] C)
    (h : LinearMap.range a ≤ LinearMap.ker b) :
    LinearMap.ker b = LinearMap.range a ↔
      Module.finrank K (LinearMap.range a) + Module.finrank K (LinearMap.range b) =
        Module.finrank K B := by
  rw [← betti_zero_iff_exact a b h]
  have hrn := LinearMap.finrank_range_add_finrank_ker b
  have hle := Submodule.finrank_mono h
  omega

theorem cokernel_dim_zero_iff (a : A →ₗ[K] B) :
    Module.finrank K (B ⧸ LinearMap.range a) = 0 ↔ Function.Surjective a := by
  constructor
  · intro hz
    have hd := Submodule.finrank_quotient_add_finrank (LinearMap.range a)
    rw [hz, zero_add] at hd
    have heq : LinearMap.range a = ⊤ :=
      Submodule.eq_of_le_of_finrank_eq le_top (by simpa using hd)
    exact LinearMap.range_eq_top.mp heq
  · intro hs
    rw [LinearMap.range_eq_top.mpr hs]
    have hd := Submodule.finrank_quotient_add_finrank (⊤ : Submodule K B)
    simpa using hd

end Exactness

/-- Both nonnegative Künneth summands must vanish; neither one can cancel the other. -/
theorem kunneth_zero_iff (r₁ c₀ r₀ c₁ : ℕ) :
    r₁ * c₀ + r₀ * c₁ = 0 ↔ (r₁ = 0 ∨ c₀ = 0) ∧ (r₀ = 0 ∨ c₁ = 0) := by
  simp only [Nat.add_eq_zero_iff, Nat.mul_eq_zero]

section Cleaning

variable {Q V E S : Type*} [Fintype Q] [Fintype V] [Fintype E] [Fintype S]

/-- Hamming weight; definitionally the same weight used by the GF(2) library. -/
def weight {ι : Type*} [Fintype ι] (x : ι → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- Restricted weight on port vertices. -/
def portWeight [DecidableEq V] (U : Finset V) (v : V → ZMod 2) : ℕ :=
  (U.filter (fun i => v i ≠ 0)).card

theorem weight_add_le (x y : Q → ZMod 2) : weight (x + y) ≤ weight x + weight y := by
  classical
  have hsub : Finset.univ.filter (fun i => (x + y) i ≠ 0) ⊆
      (Finset.univ.filter (fun i => x i ≠ 0)) ∪
        (Finset.univ.filter (fun i => y i ≠ 0)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    push Not at h
    exact hi (by simp [h.1, h.2])
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Over $\mathbb F_2$ the sum of two elements is zero iff they are **both zero or both
nonzero** -- elementwise, "one is zero and the other is not" and "the sum is not zero" say
the same thing. -/
private theorem zmod2_add_ne_zero_iff (a b : ZMod 2) :
    a + b ≠ 0 ↔ (b ≠ 0 ∧ a = 0) ∨ (b = 0 ∧ a ≠ 0) := by
  revert a b
  decide

omit [Fintype V] in
/-- **The bridge between the two encodings**: one and the same count, on a vector and on
a set.

The support of $v+w$ on $U$ splits, by the previous item, into the two blocks "$w$ nonzero
and $v$ zero" and "$w$ zero and $v$ nonzero"; the blocks are disjoint and their cardinals
add -- this is exactly the count that the branch writes as $|(v+w)\cap U|$ on vertex
vectors and that the source paper prints on sets as the modular-expansion summand. -/
theorem filter_add_ne_zero_card [DecidableEq V] (U : Finset V) (v w : V → ZMod 2) :
    (U.filter fun x => (v + w) x ≠ 0).card
      = (U.filter fun x => w x ≠ 0 ∧ v x = 0).card
        + (U.filter fun x => w x = 0 ∧ v x ≠ 0).card := by
  classical
  have hdisj : Disjoint (U.filter fun x => w x ≠ 0 ∧ v x = 0)
      (U.filter fun x => w x = 0 ∧ v x ≠ 0) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hy).2.1
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Pi.add_apply]
  constructor
  · rintro ⟨hxU, hx⟩
    rcases (zmod2_add_ne_zero_iff (v x) (w x)).mp hx with ⟨hw, hv⟩ | ⟨hw, hv⟩
    · exact Or.inl ⟨hxU, hw, hv⟩
    · exact Or.inr ⟨hxU, hw, hv⟩
  · rintro (⟨hxU, hw, hv⟩ | ⟨hxU, hw, hv⟩)
    · exact ⟨hxU, (zmod2_add_ne_zero_iff (v x) (w x)).mpr (Or.inl ⟨hw, hv⟩)⟩
    · exact ⟨hxU, (zmod2_add_ne_zero_iff (v x) (w x)).mpr (Or.inr ⟨hw, hv⟩)⟩

/-! ## The bridge between the two encodings: vertex vectors and sets

The branch writes the expansion hypothesis on **vertex vectors** (the `portWeight U (v +
w)` in `hM` of `expansion_cases`), while the original prints it on **sets** (the
`modExpArgOf κ U S = |κ \\ S| + |(S ∩ U) \\ κ|` of `ModuleExpansion`). The two translate
into each other by indicator vectors: taking $S = \operatorname{supp} v$ and
$w = \mathrm{ind}\\,\kappa$, the counts on the two sides agree term by term.

**This step needs one hypothesis**: $\kappa \subseteq U$. It is exactly the `hκU` of
`ModuleExpansion.modularExpansion_thicken`, and exactly the extra thing the branch form
asks for relative to the printed form -- and it is not hard to see why: the first term
$|\kappa \\ S|$ of `modExpArgOf` is not restricted to $U$, whereas `portWeight` is
entirely restricted to $U$, so the two agree only under this inclusion. -/

/-- The indicator vector: encoding a vertex set as a vertex vector over $\mathbb F_2$. -/
def indOf {V : Type*} [DecidableEq V] (κ : Finset V) : V → ZMod 2 :=
  fun x => if x ∈ κ then 1 else 0

/-- The support: the nonzero positions of a vertex vector. -/
def suppOf {V : Type*} [Fintype V] (v : V → ZMod 2) : Finset V :=
  Finset.univ.filter (fun x => v x ≠ 0)

theorem mem_suppOf {V : Type*} [Fintype V] (v : V → ZMod 2) (x : V) :
    x ∈ suppOf v ↔ v x ≠ 0 := by
  simp [suppOf]

theorem indOf_ne_zero_iff {V : Type*} [DecidableEq V] (κ : Finset V) (x : V) :
    indOf κ x ≠ 0 ↔ x ∈ κ := by
  by_cases h : x ∈ κ <;> simp [indOf, h]

/-- **The bridge between the two encodings**: $|\kappa \\ S| + |(S \cap U) \\ \kappa|$
and $|(v + \mathrm{ind}\,\kappa) \cap U|$ are the same number
($S = \operatorname{supp} v$, $\kappa \subseteq U$). -/
theorem modExpArgOf_eq_portWeight [DecidableEq V] (κ U : Finset V)
    (v : V → ZMod 2) (hκU : κ ⊆ U) :
    modExpArgOf κ U (suppOf v) = portWeight U (v + indOf κ) := by
  classical
  have hdiff : κ \ suppOf v = U.filter (fun x => indOf κ x ≠ 0 ∧ v x = 0) := by
    ext x
    by_cases hxκ : x ∈ κ
    · have hxU : x ∈ U := hκU hxκ
      simp [suppOf, indOf, hxκ, hxU]
    · simp [suppOf, indOf, hxκ]
  have hinter : (suppOf v ∩ U) \ κ = U.filter (fun x => indOf κ x = 0 ∧ v x ≠ 0) := by
    ext x
    by_cases hxκ : x ∈ κ
    · simp [suppOf, indOf, hxκ]
    · simp [suppOf, indOf, hxκ, and_comm]
  rw [modExpArgOf, portWeight, filter_add_ne_zero_card U v (indOf κ), hdiff, hinter]

private theorem add_self_zero {ι : Type*} (v : ι → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

omit [Fintype Q] [Fintype V] [Fintype E] [Fintype S] in
/-- Full cycle checks restrict the auxiliary part to `range B`. On this range
every legal coupling agrees. Thus changing a legal coupling changes neither
the logical set nor its distance, when the Z stabilizers are held fixed. -/
theorem legal_couplings_agree_on_cycles
    (L : (Q → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2))
    (B : (V → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2))
    (P : (V → ZMod 2) →ₗ[ZMod 2] (Q → ZMod 2))
    (J J' : (E → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2))
    (hJ : J.comp B = L.comp P) (hJ' : J'.comp B = L.comp P)
    (a : E → ZMod 2) (ha : a ∈ LinearMap.range B) : J a = J' a := by
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp ha
  exact congrArg (fun f => f v) (hJ.trans hJ'.symm)

omit [Fintype V] [Fintype S] in
/--
General legal-coupling distance theorem. `L` is the original X check map, `B`
the auxiliary boundary map, `P` the port map, and `J` the otherwise free coupling.
`hlegal` is precisely the commutativity of the extended original X rows with
the vertex Z rows. `T` contains the original and vertex Z stabilizers.

The expansion condition is the two cases of modular expansion: either the
boundary already has weight at least `d`, or a zero-boundary representative
makes the port correction no heavier than that boundary. No hypothesis says
that the coupling contribution vanishes.
-/
theorem distance_of_legal_coupling
    (L : (Q → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2))
    (B : (V → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2))
    (P : (V → ZMod 2) →ₗ[ZMod 2] (Q → ZMod 2))
    (J : (E → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2))
    (Z : Submodule (ZMod 2) (Q → ZMod 2))
    (T : Submodule (ZMod 2) ((Q → ZMod 2) × (E → ZMod 2)))
    (d : ℕ)
    (hlegal : J.comp B = L.comp P)
    (hlift : ∀ z ∈ Z, (z, 0) ∈ T)
    (hvertex : ∀ v, (P v, B v) ∈ T)
    (hQ : ∀ q, L q = 0 → q ∉ Z → d ≤ weight q)
    (hexpand : ∀ v, d ≤ weight (B v) ∨
      ∃ w, B w = 0 ∧ weight (P (v + w)) ≤ weight (B v))
    (q : Q → ZMod 2) (a : E → ZMod 2)
    (hcheck : L q + J a = 0) (hcycle : a ∈ LinearMap.range B)
    (hlogical : (q, a) ∉ T) : d ≤ weight q + weight a := by
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hcycle
  subst a
  rcases hexpand v with hbig | ⟨w, hw, hsmall⟩
  · omega
  · have hcomm : J (B v) = L (P v) := congrArg (fun f => f v) hlegal
    have hcommw : L (P w) = 0 := by
      have h := congrArg (fun f => f w) hlegal
      simpa [hw] using h.symm
    have hclosed : L (q + P (v + w)) = 0 := by
      simpa [map_add, hcommw, ← hcomm] using hcheck
    have hnot : q + P (v + w) ∉ Z := by
      intro hz
      have hclean := hlift _ hz
      have hprod := hvertex (v + w)
      have hmem := T.add_mem hclean hprod
      have heq : (q + P (v + w), (0 : E → ZMod 2)) + (P (v + w), B (v + w)) =
          (q, B v) := by
        apply Prod.ext
        · change (q + P (v + w)) + P (v + w) = q
          rw [add_assoc, add_self_zero, add_zero]
        · change 0 + B (v + w) = B v
          simp [map_add, hw]
      exact hlogical (heq ▸ hmem)
    have hlow := hQ _ hclosed hnot
    have htri := weight_add_le q (P (v + w))
    omega

omit [Fintype V] in
/-- A finite-family min bound (the printed modular-expansion shape) implies the
two-case condition consumed by `distance_of_legal_coupling`. -/
theorem expansion_cases [DecidableEq V]
    (B : (V → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2))
    (P : (V → ZMod 2) →ₗ[ZMod 2] (Q → ZMod 2))
    (U : Finset V) (W : Finset (V → ZMod 2)) (hne : W.Nonempty) (d : ℕ)
    (hW : ∀ w ∈ W, B w = 0)
    (hport : ∀ v, weight (P v) ≤ portWeight U v)
    (hM : ∀ v, min d (W.inf' hne (fun w => portWeight U (v + w))) ≤ weight (B v)) :
    ∀ v, d ≤ weight (B v) ∨
      ∃ w, B w = 0 ∧ weight (P (v + w)) ≤ weight (B v) := by
  intro v
  by_cases hbig : d ≤ weight (B v)
  · exact Or.inl hbig
  · right
    obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_inf' hne (fun w => portWeight U (v + w))
    refine ⟨w, hW w hw, (hport (v + w)).trans ?_⟩
    have h := hM v
    rw [heq] at h
    omega

end Cleaning

/-! ## Translating modular expansion: the `hM` of the branch is the condition of the
original

The `expansion_cases` of the branch writes the expansion hypothesis on **vertex
vectors**, while the original prints it on **sets**
(`ModuleExpansion.HasModularExpansion`). The previous section showed that the counts on
the two sides agree term by term; this section connects the **whole inequality** as well
-- so `hM` is not something the branch asks for additionally, but the same reading of the
original's condition under the other encoding.

Two pieces of machinery: (i) the transpose of the incidence matrix, `incTranspose`
(vertex vectors ↦ edge vectors), with `weight_incTranspose_eq_edgeDegOf` saying its weight
is exactly `edgeDegOf`; (ii) `expansionCriterion_of_modularExpansion`, which moves the
original's inequality onto the shape of `hM`, and `inf'_image_indOf_eq_modExpMin`, which
connects the branch's `W.inf'` back to `modExpMin`. -/

/-- An element of $\mathbb F_2$ is **either zero or one** -- the fact used when counting
"nonzero terms" as a number of terms. -/
private theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- A natural number is nonzero in $\mathbb F_2$ iff it is **odd**. -/
private theorem zmod2_natCast_ne_zero_iff_odd (n : ℕ) : ((n : ZMod 2) ≠ 0) ↔ Odd n := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod 2) 2 n]
  simpa [Nat.even_iff, Nat.dvd_iff_mod_eq_zero] using Nat.not_even_iff_odd (n := n)

/-- Over $\mathbb F_2$ a sum equals the **number of nonzero terms** (modulo 2). -/
private theorem sum_eq_card_filter {V : Type*} [DecidableEq V] (s : Finset V) (v : V → ZMod 2) :
    (∑ x ∈ s, v x) = ((s.filter fun x => v x ≠ 0).card : ZMod 2) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, ih, Finset.filter_insert]
    by_cases hv : v a ≠ 0
    · rw [ite_eq_left hv]
      have h1 : v a = 1 := by
        rcases zmod2_eq_zero_or_one (v a) with h | h
        · exact absurd h hv
        · exact h
      have hin : a ∉ s.filter (fun x => v x ≠ 0) := by simp [ha]
      rw [h1, Finset.card_insert_of_notMem hin, Nat.cast_add, Nat.cast_one, add_comm]
    · rw [ite_eq_right hv]
      have h0 : v a = 0 := by simpa using hv
      rw [h0, zero_add]

/-- Filtering a set by "nonzero" is intersecting it with the support. -/
private theorem filter_eq_inter_suppOf {V : Type*} [Fintype V] [DecidableEq V]
    (v : V → ZMod 2) (s : Finset V) :
    (s.filter fun x => v x ≠ 0) = s ∩ suppOf v := by
  ext x
  simp [suppOf]

/-- **The transpose of the incidence matrix**: vertex vectors ↦ edge vectors,
$(G^{\mathsf T}v)_e=\sum_{x\in\mathrm{inc}(e)}v_x$. -/
def incTranspose {V E : Type*} [Fintype V] (inc : E → Finset V) :
    (V → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun v := fun e => ∑ x ∈ inc e, v x
  map_add' v w := by
    funext e
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (Finset.mul_sum (inc e) v c).symm

/-- **The same quantity on both sides**: the weight of $G^{\mathsf T}v$ is the number of
edges meeting $\operatorname{supp}v$ in an odd number of vertices, that is `edgeDegOf`. -/
theorem weight_incTranspose_eq_edgeDegOf {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (inc : E → Finset V) (v : V → ZMod 2) :
    weight (incTranspose inc v) = edgeDegOf inc (suppOf v) := by
  classical
  rw [weight, edgeDegOf]
  congr 1
  refine Finset.filter_congr ?_
  intro e _
  show (∑ x ∈ inc e, v x) ≠ 0 ↔ Odd ((suppOf v ∩ inc e).card)
  rw [sum_eq_card_filter, Finset.inter_comm, ← filter_eq_inter_suppOf v (inc e),
    zmod2_natCast_ne_zero_iff_odd]

/-- **Modular expansion ⇒ the branch's inequality**: the one the original prints on sets,
taken at $S=\operatorname{supp}v$, reads as a shape on vertex vectors through the bridge
between the two encodings.

So the `hM` of `expansion_cases` **is not an assumption** -- it is a reading of the
original's condition; the two encodings differ only by $\kappa\subseteq U$, which is
supplied by the cardinality condition of the port fibres. -/
theorem expansionCriterion_of_modularExpansion {V E ι : Type*} [Fintype V] [Fintype E]
    [Fintype ι] [Nonempty ι] [DecidableEq V] (inc : E → Finset V) (κ : ι → Finset V)
    (U : Finset V) {d : ℕ}
    (h : HasModularExpansion inc κ U (d : ℝ) 1) (v : V → ZMod 2) :
    min d (modExpMin κ U (suppOf v)) ≤ weight (incTranspose inc v) := by
  have hv := h (suppOf v)
  rw [one_mul] at hv
  have hcast : ((min d (modExpMin κ U (suppOf v)) : ℕ) : ℝ)
      ≤ (edgeDegOf inc (suppOf v) : ℝ) := by
    rw [Nat.cast_min]
    exact hv
  rw [weight_incTranspose_eq_edgeDegOf]
  exact_mod_cast hcast

/-- **The branch's `W.inf'` is `modExpMin`**: when the image of the family $\kappa$ under
the indicator map is taken as $W$, the infima on the two sides are the same number --
each term agrees term by term by the bridge of the previous section. -/
theorem inf'_image_indOf_eq_modExpMin {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq V] (κ : ι → Finset V) (U : Finset V) (hκU : ∀ a, κ a ⊆ U) (v : V → ZMod 2) :
    (Finset.univ.image (fun a => indOf (κ a))).inf'
        ⟨indOf (κ (Classical.arbitrary ι)),
          Finset.mem_image.mpr ⟨Classical.arbitrary ι, Finset.mem_univ _, rfl⟩⟩
        (fun w => portWeight U (v + w))
      = modExpMin κ U (suppOf v) := by
  classical
  rw [modExpMin]
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' _ _ ?_
    intro a _
    rw [modExpArgOf_eq_portWeight (κ a) U v (hκU a)]
    exact Finset.inf'_le _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  · refine Finset.le_inf' _ _ ?_
    intro w hw
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hw
    rw [← modExpArgOf_eq_portWeight (κ a) U v (hκU a)]
    exact Finset.inf'_le _ (Finset.mem_univ a)


end QECCertificates.Homology
