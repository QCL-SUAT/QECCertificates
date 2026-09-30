/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.LexLeader

/-!
# Assembling a symmetry-broken CNF: `buildPair` plus `lexClauses`

The symmetry-broken CNF produced by an external Python tool is a **concatenation of two
parts**: the base pair encoding (`buildPair` in `Reflect/Encode.lean`) and one lexicographic
comparator block per group element (`lexClauses` in `Reflect/LexLeader.lean`), the auxiliary
variables of the comparators being allocated immediately after the variable numbers of the base
part. This module writes that assembly as the Lean definition `sbCNF` and proves its
**soundness**:

    `SatFormula σ (sbCNF base key imgs c)`
      implies  `SatFormula σ base`  and  `LexLeOver key img σ` for every group element
      `img ∈ imgs`

## Two correspondences with the tool

* **Auxiliary variable numbering.** The `lex_leader` of the external tool allocates `n - 1`
  fresh variables per group element (`n = len(key)`; `e 0` is the constant true and occupies no
  variable), and the next group element continues from the end of the previous block. The
  accumulating parameter `c + (key.length - 1)` of `sbBlocks` is exactly this.
* **Clause counts.** Measured on the tool side at **`6n - 6` per group element** (the
  `sb_clauses_per_elem` of the external deposit: $n = 144$ gives $858$ and $n = 288$ gives
  $1722$). The lemmas `lexClauses_length` / `sbBlocks_length` below turn that arithmetic into
  theorems, so the reading of the tool and the Lean port land on **the same formula**. This is
  no coincidence, since `lexClauses` is a verbatim port of `lex_leader` and adding up the four
  families gives exactly $4 + 5(n-2) + 1 + (n-1)$.

## The step this module does **not** take (stated plainly)

The CNF of the tool is a **byte string assembled in Python**; what this module provides is the
**mathematics of the assembly**, not the statement that "that byte string equals this
definition". The latter would require transcribing the instance CNF into literals and running
`by decide`, as `Reflect/Faithful.lean` does (that module does exactly this for four small
entries), and it is a separate matter. **Both links have to be in place before the replay is
closed**; this module is the earlier of the two, and it is the one that is **independent of any
instance**.
-/

namespace QECCertificates.LRAT

/-! ## The sizes of the four families (one at a time, used by the arithmetic above) -/

theorem lexHead_length (key img : List Nat) (c : Nat) : (lexHead key img c).length = 4 := by
  simp [lexHead]

theorem lexStep_length (key img : List Nat) (c i : Nat) : (lexStep key img c i).length = 5 := by
  simp [lexStep]

theorem lexOrder_length (key img : List Nat) : (lexOrder key img).length = 1 := by
  simp [lexOrder]

theorem lexConstraint_length (key img : List Nat) (c i : Nat) :
    (lexConstraint key img c i).length = 1 := by
  simp [lexConstraint]

/-- `flatMap` over a family of **constant size**: the length is the number of elements times that constant. -/
theorem length_flatMap_const {α β : Type*} (f : α → List β) (l : List α) (m : Nat)
    (h : ∀ a, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, h a, ih]
      ring

/-- **The clause count of the comparator**: one family of 4 clauses, one of $5(n-2)$, one of 1 and one
of $n-1$, for a total of $6n - 6$, which is exactly the `sb_clauses_per_elem` of the external deposit. -/
theorem lexClauses_length {key : List Nat} (h2 : 2 ≤ key.length) (img : List Nat) (c : Nat) :
    (lexClauses key img c).length = 6 * key.length - 6 := by
  have hs : ((List.range' 2 (key.length - 2)).flatMap (lexStep key img c)).length
      = (key.length - 2) * 5 := by
    rw [length_flatMap_const (lexStep key img c) _ 5 (fun i => lexStep_length key img c i),
      List.length_range']
  have hc : ((List.range' 1 (key.length - 1)).flatMap (lexConstraint key img c)).length
      = (key.length - 1) * 1 := by
    rw [length_flatMap_const (lexConstraint key img c) _ 1
        (fun i => lexConstraint_length key img c i),
      List.length_range']
  simp only [lexClauses, List.length_append, lexHead_length, lexOrder_length, hs, hc]
  omega

/-! ## Assembly -/

/-- **The comparator block of one group element**: the auxiliary variable numbers start at `c`, each
block takes `key.length - 1` of them, and the next block continues from there.

The correspondence with the external tool is in the module header. The empty list gives the empty
CNF (only non-identity elements are selected, so the identity is not in `imgs`). -/
def sbBlocks (key : List Nat) : List (List Nat) → Nat → CNF
  | [], _ => []
  | img :: rest, c => lexClauses key img c ++ sbBlocks key rest (c + (key.length - 1))

/-- **The symmetry-broken CNF**: the base part `base` followed by one comparator block per group element.

On the tool side the call is: `build_from(...)` produces `base` and its variable count `c`, and then
one block is appended per group element; this definition makes both "the block" and "the
accumulating variable number" explicit. -/
def sbCNF (base : CNF) (key : List Nat) (imgs : List (List Nat)) (c : Nat) : CNF :=
  base ++ sbBlocks key imgs c

theorem sbBlocks_length {key : List Nat} (h2 : 2 ≤ key.length)
    (imgs : List (List Nat)) (c : Nat) :
    (sbBlocks key imgs c).length = imgs.length * (6 * key.length - 6) := by
  induction imgs generalizing c with
  | nil => simp [sbBlocks]
  | cons img rest ih =>
      have hA : 6 * key.length - 6 = 6 * (key.length - 1) := by omega
      simp only [sbBlocks, List.length_append, lexClauses_length h2, List.length_cons]
      rw [ih, hA]
      ring

/-- **The clause count of the assembly**: the base part plus $6n - 6$ per group element.

The readings of the two entries of the external tool can be checked against this: `gens` (2
generators, $n = 144$) adds $1716$ to the base part, matching $12238 - 10522 = 1716$ in the
external deposit exactly. -/
theorem sbCNF_length (base : CNF) {key : List Nat} (h2 : 2 ≤ key.length)
    (imgs : List (List Nat)) (c : Nat) :
    (sbCNF base key imgs c).length = base.length + imgs.length * (6 * key.length - 6) := by
  simp [sbCNF, List.length_append, sbBlocks_length h2]

/-! ## Soundness -/

/-- Single step: **the head and the tail are genuine theorem variables**, not induction case bindings.

This is deliberate: in `induction … with | cons …`, if an assumption of the statement also uses
`img` as its binding name (as `hlen` here does), Lean degrades the head and the tail of the case to
**inaccessible names** (`head✝`/`tail✝`) that can no longer be referred to after `intro`. Pulling the
head and the tail out into theorem variables makes the whole passage independent of what the case
bindings happen to be called. -/
theorem sbBlocks_sat_cons {σ : Assign} {key : List Nat} (hd : List Nat) (tl : List (List Nat))
    {c : Nat}
    (hlen : ∀ img ∈ hd :: tl, img.length = key.length)
    (ihh : (∀ img ∈ tl, img.length = key.length) →
        ∀ c, SatFormula σ (sbBlocks key tl c) → ∀ img ∈ tl, LexLeOver key img σ)
    (h : SatFormula σ (sbBlocks key (hd :: tl) c)) :
    ∀ img ∈ hd :: tl, LexLeOver key img σ := by
  intro w hw
  have h' : SatFormula σ (lexClauses key hd c)
      ∧ SatFormula σ (sbBlocks key tl (c + (key.length - 1))) := by
    rw [sbBlocks] at h
    exact satFormula_append.mp h
  rcases List.mem_cons.mp hw with hEq | hmem
  · -- 头那一支：`hEq : w = hd`。**不能用 `subst`**——它会把 `hd` 从上下文里消掉，
    -- 后面再引用就报 "unknown identifier"；`rw` 只改目标、留着 `hd`。
    rw [hEq]
    exact lexClauses_sat (hlen hd (by simp)) h'.1
  · exact ihh (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
      (c + (key.length - 1)) h'.2 w hmem

/-- **Every comparator block contributes its lexicographic assertion.** An induction suffices: blocks
differ only in the accumulated variable number, and `lexClauses_sat` holds for **any** starting point
`c`, so the accumulation does not affect the conclusion. -/
theorem sbBlocks_sat {σ : Assign} {key : List Nat} {imgs : List (List Nat)}
    (hlen : ∀ img ∈ imgs, img.length = key.length) :
    ∀ c, SatFormula σ (sbBlocks key imgs c) → ∀ img ∈ imgs, LexLeOver key img σ := by
  induction imgs with
  | nil => intro c h img himg; simp at himg
  | cons =>
      -- `| cons =>` 的头/尾/归纳假设是不可及名，`rename_i` 按位置取出即可；
      -- 头在**任何 `intro` 之前**交给 `sbBlocks_sat_cons`，故不受其影响。
      rename_i hd tl ihh
      intro c
      exact sbBlocks_sat_cons hd tl hlen ihh

/-- **Soundness of the symmetry-broken CNF** (the main theorem of this module): an assignment that
satisfies the symmetry-broken encoding satisfies the base part and every symmetry-breaking
constraint.

This is the **semantic** counterpart of the assembly "symmetry-broken CNF = `buildPair` plus
`lexClauses`": it joins the soundness of the two halves (`Encode.lean` and `LexLeader.lean`) into
one. -/
theorem sbCNF_sat {σ : Assign} {base : CNF} {key : List Nat} {imgs : List (List Nat)} {c : Nat}
    (hlen : ∀ img ∈ imgs, img.length = key.length)
    (h : SatFormula σ (sbCNF base key imgs c)) :
    SatFormula σ base ∧ ∀ img ∈ imgs, LexLeOver key img σ := by
  have h' : SatFormula σ base ∧ SatFormula σ (sbBlocks key imgs c) := by
    rw [sbCNF] at h
    exact satFormula_append.mp h
  exact ⟨h'.1, sbBlocks_sat hlen c h'.2⟩

/-- **Faithfulness of the symmetry-broken encoding (the whole chain)**: an assignment that satisfies
the symmetry-broken CNF yields

* a model of the original encoding, that is, a light logical operator read off through
  `buildPair_sat` (weight $\le k$, in the kernel on both sides, and pairing equal to 1, the last two
  conditions together ruling out that it lies in the row space);
* the lexicographic assertion of every symmetry-breaking constraint (read off through
  `LexLeader.lexClauses_sat`).

Feeding `LexLeOver` to the orbit lemma of `Reflect/SymmetryBreak.lean` then gives "there exists a
light logical operator that is **minimal in its orbit**", that is, the symmetry breaking **does not
cut away all the solutions**. -/
theorem sbCNF_buildPair_sat {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    {key : List Nat} {imgs : List (List Nat)} {c : Nat}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hlen : ∀ img ∈ imgs, img.length = key.length)
    (h : SatFormula σ (sbCNF (buildPair Rker Rpair n k) key imgs c)) :
    (cntS σ (List.range n) ≤ k ∧
      (∀ r ∈ Rker, dotS σ r = false) ∧
      (∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false) ∧
      dotS (fun t => σ t && σ (n + t)) (List.range n) = true) ∧
    (∀ img ∈ imgs, LexLeOver key img σ) := by
  obtain ⟨hbase, hcmp⟩ := sbCNF_sat hlen h
  exact ⟨buildPair_sat hn hne₁ hne₂ hbase, hcmp⟩

end QECCertificates.LRAT
