/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.GF2.RankCertificate
import QECCertificates.GF2.Canonical
import QECCertificates.GF2.HGPCompression

/-!
# The two components of gauging, as a formal statement (representation layer)

This module provides the **formal statement of the two components of gauging
(spacelike and timelike)**. It turns the **representation-layer content** of both
components into theorems, matched one by one against an independent Python probe
of the same route:

## 1. Spacelike component: measuring a logical operator deforms the code

Lifting an X-type logical operator $\ell$ to a stabilizer ("measuring $\ell$")
deforms the code so that its checks become

$$H_X' = \begin{pmatrix}H_X\\ \hline \ell\end{pmatrix},\qquad H_Z' = H_Z .$$

* `deformX_css`: **CSS compatibility is preserved**: $\ell \perp H_Z$ row by row implies
  $H_X'H_Z'^\top = 0$.
* `finrank_deformX` / `deformX_k`: **dimension law**; when
  $\ell \notin \mathrm{row}\,H_X$, $k$ drops by exactly one (matching
  $k:8\to7$ in the $[[90,8,10]] \to [[90,7,10]]$ example of the independent probe).

## 2. W–Y lifting: the product of the Gauss laws equals the product of the vertex operators

The curve-gauging identity $L = \prod_v A_v$ is a **purely combinatorial fact** at
the representation layer: on an auxiliary graph without self-loops every edge qubit
has exactly two endpoints, so in the product of the Gauss operators
$A_v = X_v\prod_{e\ni v}X_e$ all edge operators cancel in pairs:

`gauss_prod_eq_vertex_prod`: $\sum_v A_v = \sum_v X_v$ (an equality of GF(2) vectors).

This is the representation-layer content of `L = Π_v A_v` and of the dimension drop
$4\to3$ along the end-to-end route.

## 3. Timelike component: the minimal undetectable weight equals the number of rounds

The timelike gauging chain consists of the adjacent-round checks $e_i + e_{i+1}$
($i=0..T-2$):

* `timeLike_eq_of_repCheck`: orthogonality to every timelike check implies that the
  values agree round by round;
* `timeLike_weight_eq`: nonzero implies that every value is one, hence the weight is
  exactly the number of rounds $T = S+1$.

Thus "the minimal undetectable weight equals the number of rounds" becomes a theorem
at the representation layer, with the lower and the upper bound given by the same line.
-/

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {n : ℕ}

/-! ## 1. Spacelike component: the deformed code -/

/-- **Spacelike gauging**: lift the X-type operator `ell` to a stabilizer by appending
the single row `ell` to the X checks, leaving the Z checks unchanged (representation
layer). -/
def deformXRows (L : List (Vec n)) (ell : Vec n) : List (Vec n) := L ++ [ell]

/-- **CSS compatibility is preserved by the deformation**: orthogonality of `ell` with
every Z check row is the essential hypothesis (this is exactly the criterion for `ell`
being an X-type logical operator). -/
theorem deformX_css {Hx Hz : List (Vec n)} {ell : Vec n}
    (hell : ∀ r ∈ Hz, ell ⬝ᵥ r = 0) (hcss : ∀ a ∈ Hx, ∀ b ∈ Hz, a ⬝ᵥ b = 0) :
    ∀ a ∈ deformXRows Hx ell, ∀ b ∈ Hz, a ⬝ᵥ b = 0 := by
  intro a ha b hb
  rcases List.mem_append.mp ha with ha' | ha'
  · exact hcss a ha' b hb
  · have heq : a = ell := by simpa using ha'
    rw [heq]
    exact hell b hb

/-- Appending one vector outside the row space increases the dimension by exactly one. -/
theorem finrank_spanL_append_singleton_of_not_mem {L : List (Vec n)} {ell : Vec n}
    (h : ell ∉ spanL L) :
    Module.finrank (ZMod 2) (spanL (L ++ [ell])) = Module.finrank (ZMod 2) (spanL L) + 1 := by
  rw [spanL_append_singleton L ell]
  have hbot : spanL L ⊓ Submodule.span (ZMod 2) ({ell} : Set (Vec n)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx2' : x = 0 ∨ x = ell := by
      have hmem : x ∈ Submodule.span (ZMod 2) ({ell} : Set (Vec n)) := hx2
      refine Submodule.span_induction (p := fun y _ => y = 0 ∨ y = ell) ?_ ?_ ?_ ?_ hmem
      · intro y hy
        exact Or.inr (by simpa using hy)
      · exact Or.inl rfl
      · intro a b _ _ ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by rw [zero_add])
        · exact Or.inr (by rw [add_zero])
        · exact Or.inl (by rw [add_self])
      · intro c a _ ha
        rcases ha with rfl | rfl
        · exact Or.inl (by rw [smul_zero])
        · by_cases hc : c = 0
          · exact Or.inl (by rw [hc, zero_smul])
          · exact Or.inr (by rw [eq_one_of_ne_zero hc, one_smul])
    rcases hx2' with rfl | rfl
    · rfl
    · exact absurd hx1 h
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (V := Vec n)
    (s := spanL L) (t := Submodule.span (ZMod 2) ({ell} : Set (Vec n)))
  rw [hbot, finrank_bot, add_zero] at hdim
  rw [hdim]
  congr 1
  exact finrank_span_singleton (K := ZMod 2) (by rintro rfl; exact h (Submodule.zero_mem _))

/-- **Rank theorem for the deformed code**: when `ell ∉ row H_X` the X rank increases
by exactly one (as read off by `rowReduce`). -/
theorem deformX_rowReduce_length {L : List (Vec n)} {ell : Vec n} (h : ell ∉ spanL L) :
    (rowReduce (L ++ [ell])).length = (rowReduce L).length + 1 := by
  have h1 := finrank_spanL_eq_length_rowReduce (L ++ [ell])
  have h2 := finrank_spanL_eq_length_rowReduce L
  have h3 := finrank_spanL_append_singleton_of_not_mem (n := n) h
  omega

/-- **Dimension law for spacelike gauging**: lifting a nontrivial X-type logical
operator to a stabilizer decreases the number of logical qubits by exactly one
($k = n - \mathrm{rank}\,H_X - \mathrm{rank}\,H_Z$, matching $k:8\to7$ in the
independent probe). -/
theorem deformX_k {Lx Lz : List (Vec n)} {ell : Vec n} (h : ell ∉ spanL Lx) :
    n - (rowReduce (Lx ++ [ell])).length - (rowReduce Lz).length
      = (n - (rowReduce Lx).length - (rowReduce Lz).length) - 1 := by
  have hlen := deformX_rowReduce_length (n := n) h
  have hle := length_rowReduce_le Lx
  rw [hlen]
  omega

/-! ## 2. W–Y lifting: the product of the Gauss laws equals the product of the vertex operators -/

/-- **Gauss operator**: the star of the vertex `v`, namely $X_v\prod_{e\ni v}X_e$ (a
representation-layer vector on the auxiliary graph).

Qubit numbering: `Sum.inl v` is a vertex qubit and `Sum.inr e` is an edge qubit. -/
def gaussOp {k m : ℕ} (ends : Fin m → Fin k × Fin k) (v : Fin k) : (Fin k ⊕ Fin m) → ZMod 2 :=
  Sum.elim (fun w => if w = v then 1 else 0)
    (fun e => if (ends e).1 = v ∨ (ends e).2 = v then 1 else 0)

/-- **Vertex operator**: $X_v$, acting on the vertex qubits only. -/
def vertexOp {k m : ℕ} (v : Fin k) : (Fin k ⊕ Fin m) → ZMod 2 :=
  Sum.elim (fun w => if w = v then 1 else 0) (fun _ => 0)

/-- **W–Y lifting identity**: on an auxiliary graph without self-loops, the product of
all the Gauss operators equals the product of all the vertex operators (the edge
operators cancel in pairs, since every edge has exactly two endpoints). This corresponds
to $L = \prod_v A_v$ in the independent probe. -/
theorem gauss_prod_eq_vertex_prod {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) :
    (∑ v : Fin k, gaussOp ends v) = ∑ v : Fin k, vertexOp v := by
  funext i
  have hsingle : ∀ a : Fin k, (∑ v : Fin k, (if a = v then (1 : ZMod 2) else 0)) = 1 := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [ite_eq_left rfl]
    · intro b _ hb
      rw [ite_eq_right (fun h : a = b => hb h.symm)]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rcases i with w | e
  · simp only [Finset.sum_apply, gaussOp, vertexOp, Sum.elim_inl]
  · simp only [Finset.sum_apply, gaussOp, vertexOp, Sum.elim_inr]
    have hor : ∀ v : Fin k,
        (if (ends e).1 = v ∨ (ends e).2 = v then (1 : ZMod 2) else 0)
          = (if (ends e).1 = v then 1 else 0) + (if (ends e).2 = v then 1 else 0) := by
      intro v
      by_cases h1 : (ends e).1 = v
      · have h2 : ¬((ends e).2 = v) := fun h2 => hloop e (h1.trans h2.symm)
        rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right h2, add_zero]
      · by_cases h2 : (ends e).2 = v
        · rw [ite_eq_right h1, ite_eq_left (Or.inr h2), ite_eq_left h2, zero_add]
        · rw [ite_eq_right (fun h => h.elim h1 h2), ite_eq_right h1, ite_eq_right h2,
            add_zero]
    rw [Finset.sum_congr rfl fun v _ => hor v, Finset.sum_add_distrib,
      hsingle (ends e).1, hsingle (ends e).2, Finset.sum_const_zero]
    exact CharTwo.add_self_eq_zero 1

/-! ## 3. Timelike component: the minimal undetectable weight equals the number of rounds -/

/-- **Adjacent-pair checks of the timelike chain**: the `i`-th check is
`e_i + e_{i+1}` (the data qubits being `Fin (S+1)`). -/
def repCheck (S : ℕ) (i : Fin S) : Vec (S + 1) :=
  unitVec (Fin.castSucc i) + unitVec i.succ

/-- The dot product of `unitVec i` with `x` is `x i`. -/
lemma unitVec_dot {n : ℕ} (i : Fin n) (x : Vec n) : unitVec i ⬝ᵥ x = x i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · rw [unitVec, ite_eq_left rfl, one_mul]
  · intro b _ hb
    rw [unitVec, ite_eq_right (fun h : b = i => hb h), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Timelike component (lower-bound direction)**: a vector orthogonal to every
timelike check takes the same value in every round, so on the timelike chain an
operator spanning all rounds is the only undetectable direction. -/
theorem timeLike_eq_of_repCheck {S : ℕ} {x : Vec (S + 1)}
    (h : ∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) : ∀ i j : Fin (S + 1), x i = x j := by
  have hstep : ∀ i : Fin S, x (Fin.castSucc i) = x i.succ := by
    intro i
    have hi := h i
    rw [repCheck, add_dotProduct, unitVec_dot, unitVec_dot] at hi
    exact (add_eq_zero_iff_eq _ _).mp hi
  have key : ∀ i : Fin (S + 1), x i = x 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih => rw [← hstep j]; exact ih
  intro i j
  rw [key i, key j]

/-- **Timelike component (exact value)**: a **nonzero** vector orthogonal to every
timelike check takes the value one everywhere, so its weight is exactly the number of
rounds `T = S+1`. Thus "the minimal undetectable weight equals the number of rounds"
holds at the representation layer. -/
theorem timeLike_weight_eq {S : ℕ} {x : Vec (S + 1)}
    (h : ∀ i : Fin S, repCheck S i ⬝ᵥ x = 0) (hx : x ≠ 0) :
    hammingNorm x = S + 1 := by
  have hzeroOfNeOne : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  have hall : ∀ i : Fin (S + 1), x i = 1 := by
    intro i
    by_contra hne
    refine hx (funext fun j => ?_)
    rw [← timeLike_eq_of_repCheck h i j]
    exact hzeroOfNeOne (x i) hne
  have hfilter : (Finset.univ.filter (fun i : Fin (S + 1) => x i ≠ 0)) = Finset.univ := by
    refine Finset.filter_true_of_mem fun i _ => ?_
    rw [hall i]
    exact one_ne_zero
  show (Finset.univ.filter (fun i : Fin (S + 1) => x i ≠ 0)).card = S + 1
  rw [hfilter, Finset.card_univ, Fintype.card_fin]

end QECCertificates
