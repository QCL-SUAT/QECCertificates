/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Reflect.LRAT
import QECCertificates.Reflect.SymmetryBreak

/-!
# Soundness of the lexicographic-comparator clauses (the CNF layer of A3)

`Reflect/SymmetryBreak.lean` proves the **semantics**: if the symmetry-broken predicate is
satisfiable then so is the original predicate. To connect the **CNF** produced by the tool, one
more step is needed:

    `SatFormula σ (lexClauses key img c)  ⟹  key ≤_lex img`

This module supplies it: the `lex_leader` of the external encoder is ported word for word into the
Lean clause generator `lexClauses`, and it is proved that **satisfying every clause implies the
lexicographic order asserted by the comparator**.

## Recap of the encoding (one-to-one with `lex_leader`)

Let the comparison vector have `n` bits, let `key i` be the variable number of bit `i` and `img i`
the source of its value under `g·v` (the tool passes the **inverse** of the permutation, so `img i`
is exactly `(g·v)_i`). The auxiliary variable `e i` (`1 ≤ i`) asserts that the first `i` bits are
equal, and `e 0` is the constant true, to which no variable is assigned. The clauses fall into four
families:

| Family | Count | Clause |
|---|---|---|
| `lexHead` | 4 | defines `e 1 ↔ (key 0 ↔ img 0)` |
| `lexStep i` (`2 ≤ i < n`) | 5 | defines `e i ↔ (e (i-1) ∧ (key (i-1) ↔ img (i-1)))` |
| `lexOrder` | 1 | `¬key 0 ∨ img 0` (there is no `e` at `i = 0`) |
| `lexConstraint i` (`1 ≤ i < n`) | 1 | `¬e i ∨ ¬key i ∨ img i` |

The families with four and five clauses together define `e` **exactly**, no more and no less, which
is where the encoding avoids being too tight; the `⟸` half of `Reflect/SymmetryBreak.lean` is what
needs this. The last family forbids "prefix equal with `key i = 1, img i = 0`", the only shape that
has `key >_lex img`.

## Shape of the conclusion

`LexLe v w` is written as "there is no position at which `v >_lex w`":

    ∀ i, (prefix equal) → v i = true → w i = true

It corresponds word for word to the clauses of families 3 and 4, so the proof **follows the
clauses** rather than the order relation.
-/

namespace QECCertificates.LRAT

/-! ## Literals and the lexicographic order -/

/-- A positive literal (the variable is true). -/
def pos (v : Nat) : Lit := (v, true)

/-- A negative literal (the variable is false). -/
def neg (v : Nat) : Lit := (v, false)

/-- The variable number of the comparator auxiliary variable `e i` (`i ≥ 1`); `e 0` is the constant
true and is not assigned one. -/
def eVar (c i : Nat) : Nat := c + (i - 1)

/-- Bit `i` of the vector `v`; out of range it is `0` (callers supply the bound, so this never
happens). -/
def idx (v : List Nat) (i : Nat) : Nat := v.getD i 0

/-- **Lexicographic order `≤`**: there is no position at which the prefixes are equal, `v` is true
and `w` is false.

This shape is used rather than a recursive definition because it corresponds word for word to the
clauses of `lexConstraint`: the proof follows the clauses. -/
def LexLe (v w : List Bool) : Prop :=
  ∀ i, (∀ j, j < i → v.getD j false = w.getD j false) →
    v.getD i false = true → w.getD i false = true

/-! ## The clauses of each family (word for word with `lex_leader`) -/

/-- Family 1: defines `e 1 ↔ (key 0 ↔ img 0)` (4 clauses). -/
def lexHead (key img : List Nat) (c : Nat) : CNF :=
  [[neg (eVar c 1), neg (idx key 0), pos (idx img 0)],
   [neg (eVar c 1), pos (idx key 0), neg (idx img 0)],
   [neg (idx key 0), neg (idx img 0), pos (eVar c 1)],
   [pos (idx key 0), pos (idx img 0), pos (eVar c 1)]]

/-- Family 2: defines `e i ↔ (e (i-1) ∧ (key (i-1) ↔ img (i-1)))` (5 clauses). -/
def lexStep (key img : List Nat) (c i : Nat) : CNF :=
  [[neg (eVar c i), pos (eVar c (i - 1))],
   [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))],
   [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))],
   [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)), pos (eVar c i)],
   [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)), pos (eVar c i)]]

/-- Family 3: `¬key 0 ∨ img 0`. -/
def lexOrder (key img : List Nat) : CNF :=
  [[neg (idx key 0), pos (idx img 0)]]

/-- Family 4: `¬e i ∨ ¬key i ∨ img i`. -/
def lexConstraint (key img : List Nat) (c i : Nat) : CNF :=
  [[neg (eVar c i), neg (idx key i), pos (idx img i)]]

/-- **All clauses of the comparator** (a word-for-word port of `lex_leader`). -/
def lexClauses (key img : List Nat) (c : Nat) : CNF :=
  lexHead key img c
  ++ (List.range' 2 (key.length - 2)).flatMap (lexStep key img c)
  ++ lexOrder key img
  ++ (List.range' 1 (key.length - 1)).flatMap (lexConstraint key img c)

/-! ## Small lemmas for the two combining clauses

The clauses of families 1 and 2 each define some `e` to be equal to a Boolean combination. Those
two combinations are extracted as lemmas first, so that the induction below does not have to unfold
the clauses again and again. -/

/-- Write the expansion of `SatClause` over three literals as a Boolean disjunction; the lemmas below
all start from here. -/
theorem satClause_three {σ : Assign} {x y z : Nat} {sx sy sz : Bool}
    (h : SatClause σ [(x, sx), (y, sy), (z, sz)]) :
    σ x = sx ∨ σ y = sy ∨ σ z = sz := by
  simpa [SatClause] using h

/-- The same for four literals. -/
theorem satClause_four {σ : Assign} {w x y z : Nat} {sw sx sy sz : Bool}
    (h : SatClause σ [(w, sw), (x, sx), (y, sy), (z, sz)]) :
    σ w = sw ∨ σ x = sx ∨ σ y = sy ∨ σ z = sz := by
  simpa [SatClause] using h

/-- The same for one literal. -/
theorem satClause_one {σ : Assign} {x : Nat} {sx : Bool}
    (h : SatClause σ [(x, sx)]) : σ x = sx := by
  simpa [SatClause] using h

/-- The same for two literals. -/
theorem satClause_two {σ : Assign} {x y : Nat} {sx sy : Bool}
    (h : SatClause σ [(x, sx), (y, sy)]) : σ x = sx ∨ σ y = sy := by
  simpa [SatClause] using h

/-- **Soundness of family 1**: the four clauses together define `e ↔ (a ↔ b)` exactly. -/
theorem head_iff {σ : Assign} {a b e : Nat}
    (h1 : SatClause σ [neg e, neg a, pos b])
    (h2 : SatClause σ [neg e, pos a, neg b])
    (h3 : SatClause σ [neg a, neg b, pos e])
    (h4 : SatClause σ [pos a, pos b, pos e]) :
    σ e = true ↔ σ a = σ b := by
  rcases satClause_three (σ := σ) h1 with h | h | h <;>
  rcases satClause_three (σ := σ) h2 with h' | h' | h' <;>
  rcases satClause_three (σ := σ) h3 with h'' | h'' | h'' <;>
  rcases satClause_three (σ := σ) h4 with h''' | h''' | h''' <;>
  simp_all [neg, pos]

/-- **Soundness of family 2**: the five clauses together define `e ↔ (e' ∧ (a ↔ b))` exactly. -/
theorem step_iff {σ : Assign} {a b e e' : Nat}
    (h1 : SatClause σ [neg e, pos e'])
    (h2 : SatClause σ [neg e, neg a, pos b])
    (h3 : SatClause σ [neg e, pos a, neg b])
    (h4 : SatClause σ [neg e', neg a, neg b, pos e])
    (h5 : SatClause σ [neg e', pos a, pos b, pos e]) :
    σ e = true ↔ (σ e' = true ∧ σ a = σ b) := by
  rcases satClause_two (σ := σ) h1 with h | h <;>
  rcases satClause_three (σ := σ) h2 with h' | h' | h' <;>
  rcases satClause_three (σ := σ) h3 with h'' | h'' | h'' <;>
  rcases satClause_four (σ := σ) h4 with h₄ | h₄ | h₄ | h₄ <;>
  rcases satClause_four (σ := σ) h5 with h₅ | h₅ | h₅ | h₅ <;>
  simp_all [neg, pos]


/-! ## Family membership: the concrete clauses really are in `lexClauses`

`lexClauses` is the concatenation of the four families, so "a given clause is in it" is pure list
arithmetic, which `simp` decides. -/

variable {σ : Assign} {key img : List Nat} {c : Nat}

theorem mem_head {C : Clause} (h : C ∈ lexHead key img c) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

theorem mem_step {C : Clause} {i : Nat} (hi : i ∈ List.range' 2 (key.length - 2))
    (h : C ∈ lexStep key img c i) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨i, hi, h⟩))

theorem mem_order {C : Clause} (h : C ∈ lexOrder key img) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append]
  exact Or.inl (Or.inr h)

theorem mem_constraint {C : Clause} {i : Nat} (hi : i ∈ List.range' 1 (key.length - 1))
    (h : C ∈ lexConstraint key img c i) : C ∈ lexClauses key img c := by
  simp only [lexClauses, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨i, hi, h⟩

/-! ## Core: `e i` is exactly the indicator that the first `i` bits are equal -/

/-- Families 1 and 2 are a **definition** of `e` (both directions are present), so the value of `e` is
uniquely determined. This lemma states it in one line: **if the first `i` bits are equal then
`e i` is true, and if `e i` is true then the first `i` bits are equal**. -/
theorem eVar_spec (h : SatFormula σ (lexClauses key img c)) :
    ∀ i, 1 ≤ i → i < key.length →
      (σ (eVar c i) = true ↔ ∀ j, j < i → σ (idx key j) = σ (idx img j)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h1 hlt
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · -- i = 1：族 1 的四条
      have hi1 : i = 1 := by omega
      subst hi1
      have c₁ : SatClause σ [neg (eVar c 1), neg (idx key 0), pos (idx img 0)] :=
        h [neg (eVar c 1), neg (idx key 0), pos (idx img 0)] (mem_head (by simp [lexHead]) : [neg (eVar c 1), neg (idx key 0), pos (idx img 0)] ∈ lexClauses key img c)
      have c₂ : SatClause σ [neg (eVar c 1), pos (idx key 0), neg (idx img 0)] :=
        h [neg (eVar c 1), pos (idx key 0), neg (idx img 0)] (mem_head (by simp [lexHead]) : [neg (eVar c 1), pos (idx key 0), neg (idx img 0)] ∈ lexClauses key img c)
      have c₃ : SatClause σ [neg (idx key 0), neg (idx img 0), pos (eVar c 1)] :=
        h [neg (idx key 0), neg (idx img 0), pos (eVar c 1)] (mem_head (by simp [lexHead]) : [neg (idx key 0), neg (idx img 0), pos (eVar c 1)] ∈ lexClauses key img c)
      have c₄ : SatClause σ [pos (idx key 0), pos (idx img 0), pos (eVar c 1)] :=
        h [pos (idx key 0), pos (idx img 0), pos (eVar c 1)] (mem_head (by simp [lexHead]) : [pos (idx key 0), pos (idx img 0), pos (eVar c 1)] ∈ lexClauses key img c)
      refine (head_iff c₁ c₂ c₃ c₄).trans ?_
      constructor
      · intro heq j hj
        have : j = 0 := by omega
        subst this
        exact heq
      · intro hall
        exact hall 0 (by omega)
    · -- i ≥ 2：族 2 的五条 + 归纳假设
      have hi1 : 1 ≤ i - 1 := by omega
      have hlt' : i - 1 < key.length := by omega
      have hprev := ih (i - 1) (by omega) hi1 hlt'
      have s₁ : SatClause σ [neg (eVar c i), pos (eVar c (i - 1))] :=
        h [neg (eVar c i), pos (eVar c (i - 1))] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c i), pos (eVar c (i - 1))] ∈ lexClauses key img c)
      have s₂ : SatClause σ [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))] :=
        h [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c i), neg (idx key (i - 1)), pos (idx img (i - 1))] ∈ lexClauses key img c)
      have s₃ : SatClause σ [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))] :=
        h [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c i), pos (idx key (i - 1)), neg (idx img (i - 1))] ∈ lexClauses key img c)
      have s₄ : SatClause σ [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)),
                             pos (eVar c i)] :=
        h [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)),
                             pos (eVar c i)] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c (i - 1)), neg (idx key (i - 1)), neg (idx img (i - 1)),
                             pos (eVar c i)] ∈ lexClauses key img c)
      have s₅ : SatClause σ [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)),
                             pos (eVar c i)] :=
        h [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)),
                             pos (eVar c i)] (mem_step (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 2, by omega, by omega⟩)
              (by simp [lexStep]) : [neg (eVar c (i - 1)), pos (idx key (i - 1)), pos (idx img (i - 1)),
                             pos (eVar c i)] ∈ lexClauses key img c)
      rw [step_iff s₁ s₂ s₃ s₄ s₅, hprev]
      constructor
      · rintro ⟨hpre, hlast⟩ j hj
        rcases Nat.lt_or_ge j (i - 1) with hltj | hgej
        · exact hpre j hltj
        · have : j = i - 1 := by omega
          subst this
          exact hlast
      · intro hall
        refine ⟨fun j hj => hall j (by omega), hall (i - 1) (by omega)⟩

/-! ## Main theorem: satisfying every comparator clause implies the lexicographic order -/

/-- **The lexicographic shape asserted by the comparator**, written in the form that corresponds word
for word to the clauses of `lexConstraint`: there is no position at which the prefixes are equal,
`key i` is true and `img i` is false.

`idx` is used rather than `List.map` because the clauses contain `idx key i`, so both sides use the
same notation, and the cell `i = 0` (where no `e` is available) does not have to go through the
conversion between `List.getD` and `List.map`. -/
def LexLeOver (key img : List Nat) (σ : Assign) : Prop :=
  ∀ i, i < key.length → (∀ j, j < i → σ (idx key j) = σ (idx img j)) →
    σ (idx key i) = true → σ (idx img i) = true

/-- **Soundness of `lexClauses`** (the CNF layer of A3): if every clause is satisfied, the comparison
vector is **lexicographically non-increasing** under its own image.

The proof does two things: family 4 gives "prefix equal and `key i` true implies `img i` true" for
`i ≥ 1`, and family 3 covers the cell `i = 0`; the prefix-equality hypothesis is translated from
the value of `e` by `eVar_spec`. -/
theorem lexClauses_sat (himg : img.length = key.length)
    (h : SatFormula σ (lexClauses key img c)) : LexLeOver key img σ := by
  intro i hlt hpre hkey
  by_cases hi0 : i = 0
  · subst hi0
    have c₀ : SatClause σ [neg (idx key 0), pos (idx img 0)] :=
      h _ (mem_order (key := key) (img := img) (by simp [lexOrder]))
    rcases satClause_two (σ := σ) c₀ with h' | h'
    · exact absurd (h' ▸ hkey) (by simp)
    · exact h'
  · have hi1 : 1 ≤ i := by omega
    have hev := (eVar_spec (σ := σ) (key := key) (img := img) (c := c) h i hi1 hlt).mpr hpre
    have c₂ : SatClause σ [neg (eVar c i), neg (idx key i), pos (idx img i)] :=
      h _ (mem_constraint (key := key) (img := img) (c := c) (i := i) (by rw [List.mem_range']; exact ⟨i - 1, by omega, by omega⟩)
            (by simp [lexConstraint]))
    rcases satClause_three (σ := σ) c₂ with h' | h' | h'
    · exact absurd (h' ▸ hev) (by simp)
    · exact absurd (h' ▸ hkey) (by simp)
    · exact h'

end QECCertificates.LRAT
