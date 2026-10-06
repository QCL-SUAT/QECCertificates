/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.C1Census

/-!
# A kernel proof of C1 optimality: $m-1$ edges is the lower bound

`Codes/C1Census.lean` gives the witness that $m-1$ edges (the star graph) on $m$ vertices
satisfy C1, and left **optimality** (fewer edges cannot work) as an honest boundary, on the
grounds that the notion of "connected" had to be set up in the library first. This module
closes that gap, and **without graph theory**: by linear algebra.

## The route

Write "the two endpoints of every edge carry the same value" as a linear map

$$\delta_L : (\mathrm{Fin}\,k \to \mathbb{Z}_2) \;\longrightarrow\;
  (\mathrm{Fin}\,L.\mathrm{length} \to \mathbb{Z}_2),\qquad
  (\delta_L x)_i = x\,(L_i).1 + x\,(L_i).2 .$$

* `mem_ker_edgeDiff_iff`: $x \in \ker \delta_L$ holds if and only if **the two endpoints of
  every edge carry the same value** (in characteristic $2$, $a+b=0$ means $a=b$).
* `ker_edgeDiff_le_span_one`: every function in $\ker \delta_L$ is **constant**. Otherwise
  take $S = \{v : x_v = 0\}$; equal endpoint values make every edge of $S$ **not cross**
  it, so $\mathrm{cut}(S)=0$; and C1 demands $\min(|S|, k-|S|) \le 0$, leaving $S$ either
  $\varnothing$ or everything. But when $S$ is nonempty its complement $\{v : x_v = 1\}$ is
  nonempty too -- both ends empty only if $x$ is identically $0$ or identically $1$.
* Hence $\mathrm{finrank}\,\ker\delta_L \le 1$, while
  $\mathrm{finrank}\,\mathrm{range}\,\delta_L \le L.\mathrm{length}$; rank-nullity gives
  $k \le L.\mathrm{length} + 1$, that is **$k-1 \le L.\mathrm{length}$**.

## What this closes

The census of `Codes/C1Census.lean` lowers the cost of C1 from the $m(m-1)/2$ of $K_m$ to
$m-1+r$; this module puts the optimality side's lower bound into the kernel, so that
**"the least number of edges for C1 on $m$ vertices is exactly $m-1$" is a theorem as a
whole** (the census's exhaustive computation is its cross-check).
-/

namespace QECCertificates

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {k : ℕ}

/-! ## 1. Two small facts about $\mathbb{Z}_2$ -/

/-- In characteristic $2$, `a + b = 0` if and only if `a = b`. -/
theorem zmod2_add_eq_zero_iff {a b : ZMod 2} : a + b = 0 ↔ a = b :=
  add_eq_zero_iff_eq a b

/-- The elements of $\mathbb{Z}_2$ are only $0$ and $1$. -/
theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
  intro x
  by_cases h : x = 0
  · exact Or.inl h
  · exact Or.inr (eq_one_of_ne_zero h)

/-! ## 2. The endpoint-difference linear map -/

/-- **Endpoint difference**: $\delta_L x$ gives, on the $i$-th edge, the sum of the values
at its two endpoints. -/
def edgeDiff (L : List (Fin k × Fin k)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin L.length → ZMod 2) where
  toFun x := fun i => x (L.get i).1 + x (L.get i).2
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add]

/-- $\delta_L x = 0$ if and only if **the two endpoints of every edge carry the same
value**. -/
theorem mem_ker_edgeDiff_iff {L : List (Fin k × Fin k)} {x : Fin k → ZMod 2} :
    x ∈ LinearMap.ker (edgeDiff L) ↔ ∀ i : Fin L.length, x (L.get i).1 = x (L.get i).2 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i
    have hi : x (L.get i).1 + x (L.get i).2 = 0 := by
      have := congrFun h i
      simpa only [edgeDiff, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] using this
    exact zmod2_add_eq_zero_iff.mp hi
  · intro h
    funext i
    simp only [edgeDiff, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    exact zmod2_add_eq_zero_iff.mpr (h i)

/-! ## 3. An edge whose endpoints agree does not cross the cut -/

/-- If the two endpoints of every edge in a list **agree** on membership in `S`, then the
cut size of that list at `S` is $0$. -/
theorem cutSize_eq_zero_of_agree {L : List (Fin k × Fin k)} {S : Finset (Fin k)}
    (h : ∀ e ∈ L, (e.1 ∈ S ↔ e.2 ∈ S)) : cutSize L S = 0 := by
  rw [cutSize, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  rcases h e he with ⟨h12, h21⟩
  by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;> simp_all

/-! ## 4. The core: everything in $\ker \delta_L$ is constant -/

/-- **Every function in $\ker\delta_L$ is constant**. The proof uses C1 only on the set
$\{v : x_v = 0\}$: that set has both endpoints of every edge on the same side, so its cut
is $0$, and C1 forces it to be empty or all of `Fin k`. -/
theorem ker_edgeDiff_le_span_one {L : List (Fin k × Fin k)} (hC1 : HasExpansionOne L) :
    LinearMap.ker (edgeDiff L) ≤ ZMod 2 ∙ (fun _ : Fin k => (1 : ZMod 2)) := by
  intro x hx
  rw [Submodule.mem_span_singleton]
  by_cases hk : k = 0
  · subst hk
    exact ⟨0, by funext i; exact i.elim0⟩
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk
    obtain ⟨a₀⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hpos
    refine ⟨x a₀, ?_⟩
    have hconst : ∀ a b : Fin k, x a = x b := by
      intro a b
      -- `S` is the half on which $x$ vanishes
      set S : Finset (Fin k) := Finset.univ.filter (fun v => x v = 0) with hS
      have hagree : ∀ e ∈ L, (e.1 ∈ S ↔ e.2 ∈ S) := by
        intro e he
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
        have hval : x (L.get i).1 = x (L.get i).2 := (mem_ker_edgeDiff_iff.mp hx) i
        rw [hi] at hval
        have hmem : ∀ v : Fin k, v ∈ S ↔ x v = 0 := by
          intro v
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hmem e.1, hmem e.2]
        exact ⟨fun h => hval ▸ h, fun h => hval.symm ▸ h⟩
      have hcut : cutSize L S = 0 := cutSize_eq_zero_of_agree hagree
      have hmin : min S.card (k - S.card) ≤ 0 := by
        have := hC1 S
        rw [hcut] at this
        exact this
      have hcases : S.card = 0 ∨ k - S.card = 0 := by omega
      rcases hcases with hzero | hfull
      · -- no vertex takes the value $0$, so $x$ is $1$ everywhere
        have hSempty : S = ∅ := Finset.card_eq_zero.mp hzero
        have hone : ∀ v : Fin k, x v = 1 := by
          intro v
          rcases zmod2_eq_zero_or_one (x v) with h0 | h1
          · exfalso
            have : v ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ v, h0⟩
            rw [hSempty] at this
            simp at this
          · exact h1
        rw [hone a, hone b]
      · -- every vertex takes the value $0$, so $x$ is $0$ everywhere
        have hcard : S.card = k := by
          have hle : S.card ≤ k := by
            have := Finset.card_le_card (Finset.subset_univ S)
            rwa [Finset.card_univ, Fintype.card_fin] at this
          omega
        have hSuniv : S = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [hcard, Fintype.card_fin]
        have key : ∀ v : Fin k, x v = 0 := by
          intro v
          have hv : v ∈ S := by rw [hSuniv]; exact Finset.mem_univ v
          rw [hS, Finset.mem_filter] at hv
          exact hv.2
        rw [key a, key b]
    funext v
    show x a₀ • (1 : ZMod 2) = x v
    rw [smul_eq_mul, mul_one]
    exact (hconst v a₀).symm

/-! ## 5. The main theorem -/

/-- **The edge-count lower bound for C1**: an edge list on $k$ vertices satisfying C1 has
at least $k-1$ edges.

Together with the star witness of `Codes/C1Census.lean` ($k-1$ edges satisfy C1), this
gives **"the least number of edges for C1 on $k$ vertices is exactly $k-1$"** -- the
optimality claim of the census is no longer only an exhaustive computation. -/
theorem card_sub_one_le_length_of_hasExpansionOne {L : List (Fin k × Fin k)}
    (hC1 : HasExpansionOne L) : k - 1 ≤ L.length := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk
    obtain ⟨a₀⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hpos
    have hker := ker_edgeDiff_le_span_one hC1
    -- the dimension of the kernel is ≤ 1: it is a subspace of the constant functions, and
    -- `1 ≠ 0` makes that space exactly one-dimensional
    have hone : (fun _ : Fin k => (1 : ZMod 2)) ≠ 0 := by
      intro h
      have := congrFun h a₀
      simp at this
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.ker (edgeDiff L)) ≤ 1 := by
      calc Module.finrank (ZMod 2) ↥(LinearMap.ker (edgeDiff L))
          ≤ Module.finrank (ZMod 2) ↥(ZMod 2 ∙ (fun _ : Fin k => (1 : ZMod 2))) :=
            Submodule.finrank_mono hker
        _ = 1 := finrank_span_singleton hone
    -- the dimension of the range is at most the edge count
    have h2 : Module.finrank (ZMod 2) ↥(LinearMap.range (edgeDiff L)) ≤ L.length := by
      calc Module.finrank (ZMod 2) ↥(LinearMap.range (edgeDiff L))
          ≤ Module.finrank (ZMod 2) (Fin L.length → ZMod 2) := Submodule.finrank_le _
        _ = L.length := Module.finrank_fin_fun (ZMod 2)
    -- rank-nullity
    have hrn := LinearMap.finrank_range_add_finrank_ker (edgeDiff L)
    rw [Module.finrank_fin_fun (ZMod 2)] at hrn
    omega

end QECCertificates
