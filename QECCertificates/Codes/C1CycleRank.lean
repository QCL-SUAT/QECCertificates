/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.C1Optimal
import QECCertificates.GF2.Duality

/-!
# The C1 edge lower bound at cycle rank: the **lower-bound side** of $m-1+r$

`Codes/C1Census.lean` and `Codes/C1Optimal.lean` pin down $r=0$: an edge list on $k$
vertices satisfying C1 needs **exactly** $k-1$ edges. This module supplies the **lower
bound** of the $r\ge1$ side, so that

$$k \text{ vertices, cycle rank} \ge r \ \Longrightarrow\ \text{edge count} \ge k-1+r$$

gains a counterpart to its upper-bound side (the star plus $r$ chords, see
`expansionOne_append_list`).

## The route: the cycle space is not defined through a boundary map but through its dual description

The standard description of the cycle space is "the edge vectors orthogonal to every cut"
(a cycle has zero algebraic sum over every cut), and "orthogonal to every cut" means lying
in the orthogonal complement of `range δ_L`, where $δ_L$ is the endpoint-difference map of
`Codes/C1Optimal.lean`. Hence **there is no need to define an edge-to-vertex boundary map,
or to prove equal rank of transposes**: `LinearMap.BilinForm.finrank_orthogonal` gives
directly

$$\mathrm{finrank}\,(\mathrm{range}\,δ_L)^{\perp} = E - \mathrm{finrank}\,\mathrm{range}\,δ_L ,$$

while rank-nullity gives
$\mathrm{finrank}\,\mathrm{range}\,δ_L = k - \mathrm{finrank}\,\ker δ_L$, and together with
the $\mathrm{finrank}\,\ker δ_L = 1$ forced by C1 this yields

$$\dim(\text{cycle space}) = E - (k-1).$$

Requiring it to be $\ge r$ is exactly $E \ge k-1+r$.

## Convention

"Cycle space" in this module is a **definition** (the dual description), not a dimension
computed from a boundary map. The two dimensions agree on a finite graph, but that is not
proved here -- all this module needs is "carrying $r$ independent cycles $\Rightarrow$ edge
count lower bound".
-/

namespace QECCertificates

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {k : ℕ}

/-! ## 1. The standard dot product on `Fin n → ZMod 2` -/

/-- The standard dot product on `Fin n → ZMod 2`, as a bilinear form. -/
def stdDot (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i, x i * y i)
    (fun x₁ x₂ y => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun x y₁ y₂ => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

/-- The standard dot product is symmetric. -/
theorem stdDot_comm (n : ℕ) (x y : Fin n → ZMod 2) : (stdDot n) x y = (stdDot n) y x := by
  simp only [stdDot, LinearMap.mk₂_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The standard dot product is **non-degenerate**: the only vector orthogonal to every
vector in both directions is zero.

`Nondegenerate` is the conjunction `SeparatingLeft ∧ SeparatingRight`, so both directions
are given; this is `GF2/Duality.lean`'s `eq_zero_of_forall_dot_eq_zero`, the non-degeneracy
of the GF(2) dot product, read through `LinearMap.mk₂`. -/
theorem stdDot_nondegenerate (n : ℕ) : (stdDot n).Nondegenerate := by
  have hdot : ∀ x y : Fin n → ZMod 2, (stdDot n) x y = x ⬝ᵥ y := by
    intro x y
    simp only [stdDot, LinearMap.mk₂_apply, dotProduct]
  exact ⟨fun x hx => eq_zero_of_forall_dot_eq_zero (fun y => by
      rw [← hdot x y]; exact hx y),
    fun y hy => eq_zero_of_forall_dot_eq_zero (fun x => by
      rw [← hdot y x, stdDot_comm n y x]; exact hy x)⟩

/-! ## 2. The cycle space: the edge vectors orthogonal to every cut -/

/-- **The cycle space**: the edge vectors orthogonal to `range δ_L` (every cut). -/
def cycleSpace (L : List (Fin k × Fin k)) : Submodule (ZMod 2) (Fin L.length → ZMod 2) :=
  (stdDot L.length).orthogonal (LinearMap.range (edgeDiff L))

/-! ## 3. The dimension of $\ker δ_L$ is exactly $1$ -/

/-- The constant function lies in $\ker δ_L$. -/
theorem const_mem_ker_edgeDiff (L : List (Fin k × Fin k)) :
    (fun _ : Fin k => (1 : ZMod 2)) ∈ LinearMap.ker (edgeDiff L) := by
  rw [mem_ker_edgeDiff_iff]
  intro i
  rfl

/-- Under C1, $\ker δ_L$ is exactly the space of constant functions, of dimension $1$. -/
theorem finrank_ker_edgeDiff_eq_one {L : List (Fin k × Fin k)} (hC1 : HasExpansionOne L)
    (hk : 0 < k) : Module.finrank (ZMod 2) ↥(LinearMap.ker (edgeDiff L)) = 1 := by
  obtain ⟨a₀⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hone : (fun _ : Fin k => (1 : ZMod 2)) ≠ 0 := by
    intro h
    have := congrFun h a₀
    simp at this
  have hspan : ZMod 2 ∙ (fun _ : Fin k => (1 : ZMod 2)) ≤ LinearMap.ker (edgeDiff L) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (const_mem_ker_edgeDiff L))
  have heq : LinearMap.ker (edgeDiff L) = ZMod 2 ∙ (fun _ : Fin k => (1 : ZMod 2)) :=
    le_antisymm (ker_edgeDiff_le_span_one hC1) hspan
  rw [heq, finrank_span_singleton hone]

/-! ## 4. The main theorem -/

/-- **The C1 edge lower bound at cycle rank**: an edge list on $k$ vertices satisfying C1
whose cycle-space dimension is $\ge r$ has at least $k-1+r$ edges.

The upper side is given by the star plus $r$ chords (`expansionOne_append_list`), and the
two sides together say that **on $m$ vertices with cycle rank $\ge r$ the least number of
edges for C1 is exactly $m-1+r$**. -/
theorem card_ge_of_finrank_cycleSpace {L : List (Fin k × Fin k)} (hC1 : HasExpansionOne L)
    (hk : 0 < k) {r : ℕ} (hr : r ≤ Module.finrank (ZMod 2) ↥(cycleSpace L)) :
    k - 1 + r ≤ L.length := by
  -- rank-nullity gives the dimension of `range δ_L`
  have hrn := LinearMap.finrank_range_add_finrank_ker (edgeDiff L)
  rw [Module.finrank_fin_fun (ZMod 2), finrank_ker_edgeDiff_eq_one hC1 hk] at hrn
  have hrange : Module.finrank (ZMod 2) ↥(LinearMap.range (edgeDiff L)) = k - 1 := by omega
  -- the dimension of the orthogonal complement is pinned by `finrank_orthogonal`
  have horth := LinearMap.BilinForm.finrank_orthogonal (stdDot_nondegenerate L.length)
    (LinearMap.range (edgeDiff L))
  have hcs : Module.finrank (ZMod 2) ↥(cycleSpace L)
      = Module.finrank (ZMod 2) ↥((stdDot L.length).orthogonal
          (LinearMap.range (edgeDiff L))) := rfl
  rw [hcs, horth, Module.finrank_fin_fun (ZMod 2), hrange] at hr
  -- truncated subtraction: `r ≤ L.length - (k-1)` needs `k-1 ≤ L.length` to give the goal
  have hbase : k - 1 ≤ L.length := card_sub_one_le_length_of_hasExpansionOne hC1
  omega

end QECCertificates
