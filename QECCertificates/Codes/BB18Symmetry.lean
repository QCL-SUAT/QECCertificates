/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.FoldTransversal

/-!
# BB $[[18,4,4]]$: the translation group, lifted to the space the predicate lives on

## What was missing

`Codes/FoldTransversal.lean` already supplies the two generators at the level of the **physical
qubits**: `bb18ShiftX` and `bb18ShiftY` are permutations of `Fin 18`, and the lemmas there prove
that each maps every check row into the check row list, in both directions, so that
`bb18_shiftX_preserves_spanL_x` and its three companions hold. What it does **not** supply is what
the symmetry-breaking argument consumes: a group of permutations of the space the **predicate** is
defined on, together with the group's own closure properties.

This module adds that, and it is a lift rather than a re-proof:

* `permVec_permVec` records how `permVec` composes, which is what makes the lift below a group
  homomorphism rather than a set of unrelated permutations;
* `pairPerm` lifts a qubit permutation to the pair space `Vec n × Vec n`, acting on both halves;
* `bb18Trans` is the translation by a pair of exponents $(a,b) \in \mathbb{Z}_3 \times
  \mathbb{Z}_3$, and `bb18Trans_mul` shows that the product of two translations is the translation
  by the sum of the exponents — which needs only that the two generators commute (`bb18ShiftX_comm`);
* `bb18Group` is the nine-element group, with `bb18Group_one_mem` and `bb18Group_mul_mem` for the
  two closure properties `Reflect/SymmetryBreak.lean` asks of it.

## Why the pair space and not the qubits

The orbit lemma there is stated for `G : Finset (Equiv.Perm α)` and `P : α → Prop`. For this
development's lower bound the predicate `P` is "light logical operator", a property of a **pair**
`(x, w)` — one vector in the first check matrix's kernel, one in the second's, pairing to one — so
`α` is `Vec n × Vec n` and the group has to act there. Acting on both halves at once is what keeps
the pairing and both kernel memberships intact, which is exactly what the three facts proved at the
qubit level in `Codes/FoldTransversal.lean` are for.

## Trusted base

Zero `sorry`, zero custom axioms, zero `native_decide`; the only computation is `decide` on
explicit permutations of `Fin 18`, an eighteen-element type.
-/

namespace QECCertificates

variable {n : ℕ}

/-! ## 1. How `permVec` composes -/

/-- **Composition**: carrying with `σ` and then with `π` is carrying with `π * σ`.

`Codes/FoldTransversal.lean` records the action's two cancellation laws — `permVec_symm_permVec`
and `permVec_permVec_symm` — but not this one, which is what makes the lift below multiplicative. -/
theorem perm_mul_symm_apply (π σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (π * σ).symm i = σ.symm (π.symm i) := by
  apply (π * σ).injective
  rw [Equiv.apply_symm_apply]
  simp [Equiv.Perm.mul_apply]

/-- **Composition**: carrying with `σ` and then with `π` is carrying with `π * σ`.

`Codes/FoldTransversal.lean` records the action's two cancellation laws — `permVec_symm_permVec`
and `permVec_permVec_symm` — but not this one, which is what makes the lift below multiplicative. -/
theorem permVec_permVec (π σ : Equiv.Perm (Fin n)) (v : Vec n) :
    permVec π (permVec σ v) = permVec (π * σ) v := by
  funext i
  simp only [permVec_apply, perm_mul_symm_apply]

/-! ## 2. The lift to the pair space -/

/-- **The lift**: a permutation of the qubits acts on a pair of vectors by acting on each half.

The predicate this development certifies is a property of a pair, so this — and not the qubit
permutation itself — is the shape the symmetry-breaking argument needs. -/
noncomputable def pairPerm (π : Equiv.Perm (Fin n)) : Equiv.Perm (Vec n × Vec n) where
  toFun p := (permVec π p.1, permVec π p.2)
  invFun p := (permVec π.symm p.1, permVec π.symm p.2)
  left_inv p := by obtain ⟨v, w⟩ := p; simp
  right_inv p := by obtain ⟨v, w⟩ := p; simp

/-- **The lift is a group homomorphism**: `pairPerm` carries a product of qubit permutations to the
product of the lifted ones. Closure of the lifted group then follows from closure at the qubit
level, and no separate argument is needed. -/
theorem pairPerm_mul (π σ : Equiv.Perm (Fin n)) :
    pairPerm (π * σ) = pairPerm π * pairPerm σ := by
  refine Equiv.ext fun p => ?_
  obtain ⟨v, w⟩ := p
  show (permVec (π * σ) v, permVec (π * σ) w)
      = (permVec π (permVec σ v), permVec π (permVec σ w))
  exact Prod.ext (permVec_permVec π σ v).symm (permVec_permVec π σ w).symm

/-- The lift carries the identity to the identity, so a group containing the identity at the qubit
level contains it after the lift. -/
theorem pairPerm_one : pairPerm (1 : Equiv.Perm (Fin n)) = 1 := by
  refine Equiv.ext fun p => ?_
  obtain ⟨v, w⟩ := p
  show (permVec (1 : Equiv.Perm (Fin n)) v, permVec 1 w) = (v, w)
  exact Prod.ext (funext fun i => rfl) (funext fun i => rfl)

/-! ## 3. The translation group on the qubits -/

/-- **The translation by the exponent pair `(a, b)`**: apply the first generator `a` times and the
second `b` times. Since both have order three these are the nine elements of
$\mathbb{Z}_3 \times \mathbb{Z}_3$. -/
noncomputable def bb18Trans (a b : Fin 3) : Equiv.Perm (Fin 18) :=
  bb18ShiftX ^ a.val * bb18ShiftY ^ b.val

/-- **The two generators commute.** With this, a product of translations is again a translation,
which is what makes the set below a group rather than nine unrelated permutations. -/
theorem bb18ShiftX_comm : Commute bb18ShiftX bb18ShiftY := by
  rw [Commute]
  refine Equiv.ext fun q => ?_
  fin_cases q <;> decide

/-- **Products of translations are translations**, with the exponents added. The proof is a finite
check: four elements of `Fin 3` and eighteen qubits, each closed by `decide`. -/
theorem bb18Trans_mul (a b c d : Fin 3) :
    bb18Trans a b * bb18Trans c d = bb18Trans (a + c) (b + d) := by
  refine Equiv.ext fun q => ?_
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases q <;> decide

/-! ## 4. The lifted group, and its two closure properties -/

/-- **The translation group, lifted to the pair space**: the nine images of the translations under
`pairPerm`. This is the `G` of `Reflect/SymmetryBreak.lean`'s orbit lemma for the BB18 instance. -/
noncomputable def bb18Group : Finset (Equiv.Perm (Vec 18 × Vec 18)) :=
  Finset.univ.image fun p : Fin 3 × Fin 3 => pairPerm (bb18Trans p.1 p.2)

/-- The identity lies in the lifted group — the `⟸` half of the orbit lemma needs it. -/
theorem bb18Group_one_mem : (1 : Equiv.Perm (Vec 18 × Vec 18)) ∈ bb18Group := by
  refine Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, ?_⟩
  have h : bb18Trans 0 0 = 1 := by
    refine Equiv.ext fun q => ?_
    fin_cases q <;> decide
  rw [h, pairPerm_one]

/-- **The lifted group is closed under multiplication** (in the order the orbit lemma asks for:
`h * g`). Closure is inherited from the qubit level through `pairPerm_mul`, and needs nothing
about the code — only `bb18Trans_mul`. -/
theorem bb18Group_mul_mem {g h : Equiv.Perm (Vec 18 × Vec 18)}
    (hg : g ∈ bb18Group) (hh : h ∈ bb18Group) : h * g ∈ bb18Group := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  refine Finset.mem_image.mpr ⟨(c + a, d + b), Finset.mem_univ _, ?_⟩
  rw [← pairPerm_mul, bb18Trans_mul]

end QECCertificates
