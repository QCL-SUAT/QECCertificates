/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Reflect.LexLeader

/-!
# Completeness of the lexicographic-comparator clauses (the other half of `LexLeader`)

`Reflect/LexLeader.lean` supplies **soundness**: satisfying every clause of the comparator
implies `key ≤_lex img`. The symmetry-breaking route needs **both directions**, and the other
one has been the gap:

    `key ≤_lex img`  ⟹  some assignment satisfies `lexClauses` and agrees with the given one
                         on every original variable.

**Both directions are needed, and not out of a taste for symmetry.** With soundness alone, a
clause set that is *too tight* is indistinguishable inside the kernel from a genuine UNSAT:
a tight encoding drives the solver to report UNSAT, and that UNSAT does not entail the UNSAT
of the original problem. Completeness is exactly the half that rules out being too tight —
the same axis as the `⟸` direction of `Reflect/SymmetryBreak.lean`.

## The construction

The comparator variables `e i` are **not free**: families 1 and 2 pin their values, and the
value pinned is precisely "the first `i` bits agree":

    `eVal key img σ i := (List.range i).all (fun j => σ (idx key j) == σ (idx img j))`

So the extension does one thing — it writes the `e` block from those values and leaves every
other variable alone:

    `lexExtend key img σ c v := if c ≤ v ∧ v < c + (key.length - 1) then eVal … (v - c + 1) else σ v`

Each of the four clause families is then checked family by family, and **every family's proof
is nothing but a `by_cases` on the two bits being compared**.

## Two hypotheses, neither of them removable

* `2 ≤ key.length`: the variable `e 1` must really fall inside the allocated block
  `[c, c + key.length - 2]`;
* `∀ v ∈ key, v < c` (and the same for `img`): the comparator **must not take a variable number
  that belongs to the formula it compares**. On the tool side this follows from writing the base
  encoding first and appending the comparator blocks afterwards; in Lean it is these two.

## Trusted base

Zero `sorry`, zero custom axioms, zero `native_decide`.
-/

namespace QECCertificates.LRAT

/-! ## Prefix equality: its computable form and its two laws -/

/-- **Prefix equality** in computable form: the first `i` bits of `key` and of `img` carry
pointwise equal values.

`List.all` rather than a `∀` proposition, because the extension `lexExtend` has to *compute*
this value — it is written into an assignment, not merely asserted of one. -/
def eVal (key img : List Nat) (σ : Assign) (i : Nat) : Bool :=
  (List.range i).all (fun j => σ (idx key j) == σ (idx img j))

/-- `eVal` corresponds word for word to its propositional form, which is the "prefix equal"
hypothesis of `LexLeader`. -/
theorem eVal_spec (key img : List Nat) (σ : Assign) (i : Nat) :
    eVal key img σ i = true ↔ ∀ j, j < i → σ (idx key j) = σ (idx img j) := by
  simp only [eVal, List.all_eq_true, List.mem_range]
  constructor
  · intro h j hj
    have := h j hj
    simpa using this
  · intro h j hj
    have := h j hj
    simpa using this

/-- **One-step recursion**: the conjunction over `i` bits splits into the conjunction over
`i-1` bits and the `(i-1)`-th comparison.

The five clauses of family 2 are the clause-level shadow of this law, so the five branches
below only ever call it. -/
theorem eVal_succ (key img : List Nat) (σ : Assign) (i : Nat) :
    eVal key img σ (i + 1) =
      (eVal key img σ i && (σ (idx key i) == σ (idx img i))) := by
  simp only [eVal, List.range_succ, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]

/-- `eVal` at position 1, explicitly; the four clauses of family 1 use only this cell. -/
theorem eVal_one (key img : List Nat) (σ : Assign) :
    eVal key img σ 1 = (σ (idx key 0) == σ (idx img 0)) := by
  simp only [eVal, List.range_one, List.all_cons, List.all_nil, Bool.and_true]

/-! ## The extension: only the `e` block moves -/

/-- **The extension**: the `e i` block takes the values `eVal … i`; every other variable is
left untouched.

"Every other variable" means those numbered below `c`, together with those outside the `e`
block `[c, c + key.length - 2]` — the latter do not occur on the tool side, since the
comparator blocks are appended last. -/
def lexExtend (key img : List Nat) (σ : Assign) (c : Nat) : Assign :=
  fun v => if c ≤ v ∧ v < c + (key.length - 1) then eVal key img σ (v - c + 1) else σ v

/-- The extension is the **identity** outside the `e` block. -/
theorem lexExtend_of_lt {key img : List Nat} {σ : Assign} {c v : Nat} (hv : v < c) :
    lexExtend key img σ c v = σ v := by
  simp only [lexExtend]
  split_ifs with h
  · omega
  · rfl

/-- The same fact in the form the proof uses: the **compared variables** of the comparator all
lie below `c`. -/
theorem lexExtend_of_mem {key img : List Nat} {σ : Assign} {c v : Nat}
    (hk : ∀ u ∈ key, u < c) (hv : v ∈ key) :
    lexExtend key img σ c v = σ v :=
  lexExtend_of_lt (hk v hv)

/-- **The extension on the `e` variables**: exactly `eVal`. -/
theorem lexExtend_eVar {key img : List Nat} {σ : Assign} {c i : Nat}
    (h1 : 1 ≤ i) (h2 : i ≤ key.length - 1) :
    lexExtend key img σ c (eVar c i) = eVal key img σ i := by
  simp only [lexExtend]
  split_ifs with h
  · congr 1
    simp only [eVar] at h ⊢
    omega
  · exfalso
    simp only [eVar] at h
    omega

/-- `idx v i` is an element of `v` whenever it is in range. Families 3 and 4 use it to connect
`lexExtend_of_mem` to the variable numbers the clauses actually carry. -/
theorem idx_mem {v : List Nat} {i : Nat} (hi : i < v.length) : idx v i ∈ v := by
  have h : idx v i = v[i] := by
    simp only [idx, List.getD_eq_getElem _ _ hi]
  rw [h]
  exact List.getElem_mem _

/-! ## Building clauses: the `satClause_*` lemmas read backwards

The `satClause_*` group in `LexLeader` decomposes a `SatClause` into a disjunction, which is
what the soundness direction needs. Completeness needs the opposite: **assembling** a
`SatClause` out of a disjunction. `SatClause` says "some literal takes its value", so `simpa`
is all it takes. -/

theorem satClause_two_of {σ : Assign} {x y : Nat} {sx sy : Bool}
    (h : σ x = sx ∨ σ y = sy) : SatClause σ [(x, sx), (y, sy)] := by
  simpa [SatClause] using h

theorem satClause_three_of {σ : Assign} {x y z : Nat} {sx sy sz : Bool}
    (h : σ x = sx ∨ σ y = sy ∨ σ z = sz) : SatClause σ [(x, sx), (y, sy), (z, sz)] := by
  simpa [SatClause] using h

theorem satClause_four_of {σ : Assign} {w x y z : Nat} {sw sx sy sz : Bool}
    (h : σ w = sw ∨ σ x = sx ∨ σ y = sy ∨ σ z = sz) :
    SatClause σ [(w, sw), (x, sx), (y, sy), (z, sz)] := by
  simpa [SatClause] using h

/-! ## The main theorem: the lexicographic assertion implies `lexClauses` is satisfiable -/

/-- **Completeness**, the main theorem of this module and the other half of `lexClauses_sat`:

if the comparison vector does not increase lexicographically under its own image (`LexLeOver`),
then writing the `e` block from `eVal` satisfies every family of `lexClauses`; and the resulting
assignment is **pointwise identical** to the given one below `c`.

Neither hypothesis can be dropped: `2 ≤ key.length` is what puts `e 1` inside the allocated
block, and `∀ v ∈ key, v < c` (likewise for `img`) is what keeps the comparator from taking a
variable number belonging to the formula it compares — on the tool side, "base encoding first,
comparator blocks appended afterwards". -/
theorem lexClauses_complete {key img : List Nat} {σ : Assign} {c : Nat}
    (h2 : 2 ≤ key.length) (himg : img.length = key.length)
    (hk : ∀ v ∈ key, v < c) (hi : ∀ v ∈ img, v < c)
    (h : LexLeOver key img σ) :
    ∃ τ : Assign, (∀ v, v < c → τ v = σ v) ∧ SatFormula τ (lexClauses key img c) := by
  have hkey_len : 0 < key.length := by omega
  refine ⟨lexExtend key img σ c, fun v hv => lexExtend_of_lt hv, ?_⟩
  -- The compared variables do not move under the extension (`idx` is a list element when in
  -- range, so `hk` applies).
  have hfixK : ∀ {i : Nat}, i < key.length → lexExtend key img σ c (idx key i) = σ (idx key i) :=
    fun hlt => lexExtend_of_lt (hk _ (idx_mem hlt))
  have hfixI : ∀ {i : Nat}, i < img.length → lexExtend key img σ c (idx img i) = σ (idx img i) :=
    fun hlt => lexExtend_of_lt (hi _ (idx_mem hlt))
  have hfixI' : ∀ {i : Nat}, i < key.length → lexExtend key img σ c (idx img i) = σ (idx img i) :=
    fun hlt => hfixI (by omega)
  -- Family 1: four clauses, involving only `e 1`, `key 0` and `img 0`.
  have head_sat : ∀ C ∈ lexHead key img c, SatClause (lexExtend key img σ c) C := by
    intro C hC
    simp only [lexHead, List.mem_cons, List.mem_nil_iff, or_false] at hC
    have hK0 := hfixK (i := 0) hkey_len
    have hI0 := hfixI' (i := 0) hkey_len
    have he1 : lexExtend key img σ c (eVar c 1) = (σ (idx key 0) == σ (idx img 0)) := by
      rw [lexExtend_eVar (le_refl 1) (by omega), eVal_one]
    rcases hC with rfl | rfl | rfl | rfl
    · refine satClause_three_of ?_
      simp only [he1, hK0, hI0]
      cases σ (idx key 0) <;> cases σ (idx img 0) <;> simp_all
    · refine satClause_three_of ?_
      simp only [he1, hK0, hI0]
      cases σ (idx key 0) <;> cases σ (idx img 0) <;> simp_all
    · refine satClause_three_of ?_
      simp only [he1, hK0, hI0]
      cases σ (idx key 0) <;> cases σ (idx img 0) <;> simp_all
    · refine satClause_three_of ?_
      simp only [he1, hK0, hI0]
      cases σ (idx key 0) <;> cases σ (idx img 0) <;> simp_all
  -- Family 3: `¬key 0 ∨ img 0`.
  have order_sat : ∀ C ∈ lexOrder key img, SatClause (lexExtend key img σ c) C := by
    intro C hC
    simp only [lexOrder, List.mem_cons, List.mem_nil_iff, or_false] at hC
    subst hC
    refine satClause_two_of ?_
    simp only [hfixK (i := 0) hkey_len, hfixI' (i := 0) hkey_len]
    by_cases hk0 : σ (idx key 0) = true
    · exact Or.inr (h 0 hkey_len (fun j hj => by omega) hk0)
    · exact Or.inl (by simpa using hk0)
  -- Family 2: five clauses; step by step `e i` unfolds into `e (i-1)` conjoined with the
  -- `(i-1)`-th comparison.
  have step_sat : ∀ i ∈ List.range' 2 (key.length - 2),
      ∀ C ∈ lexStep key img c i, SatClause (lexExtend key img σ c) C := by
    intro i hi C hC
    obtain ⟨m, hm, heq⟩ := List.mem_range'.mp hi
    have hi2 : 2 ≤ i := by omega
    have hilt : i < key.length := by omega
    simp only [lexStep, List.mem_cons, List.mem_nil_iff, or_false] at hC
    have hE_i := lexExtend_eVar (key := key) (img := img) (σ := σ) (c := c)
      (i := i) (by omega) (by omega)
    have hE_p := lexExtend_eVar (key := key) (img := img) (σ := σ) (c := c)
      (i := i - 1) (by omega) (by omega)
    have hKp := hfixK (i := i - 1) (by omega)
    have hIp := hfixI' (i := i - 1) (by omega)
    have hstep : eVal key img σ i =
        (eVal key img σ (i - 1) && (σ (idx key (i - 1)) == σ (idx img (i - 1)))) := by
      have hs := eVal_succ key img σ (i - 1)
      rwa [Nat.sub_add_cancel (by omega)] at hs
    rcases hC with rfl | rfl | rfl | rfl | rfl
    · refine satClause_two_of ?_
      simp only [hE_i, hE_p, hstep]
      cases eVal key img σ (i - 1) <;> cases σ (idx key (i - 1)) <;>
        cases σ (idx img (i - 1)) <;> simp_all
    · refine satClause_three_of ?_
      simp only [hE_i, hKp, hIp, hstep]
      cases eVal key img σ (i - 1) <;> cases σ (idx key (i - 1)) <;>
        cases σ (idx img (i - 1)) <;> simp_all
    · refine satClause_three_of ?_
      simp only [hE_i, hKp, hIp, hstep]
      cases eVal key img σ (i - 1) <;> cases σ (idx key (i - 1)) <;>
        cases σ (idx img (i - 1)) <;> simp_all
    · refine satClause_four_of ?_
      simp only [hE_p, hKp, hIp, hE_i, hstep]
      cases eVal key img σ (i - 1) <;> cases σ (idx key (i - 1)) <;>
        cases σ (idx img (i - 1)) <;> simp_all
    · refine satClause_four_of ?_
      simp only [hE_p, hKp, hIp, hE_i, hstep]
      cases eVal key img σ (i - 1) <;> cases σ (idx key (i - 1)) <;>
        cases σ (idx img (i - 1)) <;> simp_all
  -- Family 4: `¬e i ∨ ¬key i ∨ img i` — the first place `h` is really used.
  have constr_sat : ∀ i ∈ List.range' 1 (key.length - 1),
      ∀ C ∈ lexConstraint key img c i, SatClause (lexExtend key img σ c) C := by
    intro i hi C hC
    obtain ⟨m, hm, heq⟩ := List.mem_range'.mp hi
    have hi1 : 1 ≤ i := by omega
    have hilt : i < key.length := by omega
    simp only [lexConstraint, List.mem_cons, List.mem_nil_iff, or_false] at hC
    subst hC
    refine satClause_three_of ?_
    simp only [lexExtend_eVar (key := key) (img := img) (σ := σ) (c := c)
      (i := i) hi1 (by omega), hfixK (i := i) hilt, hfixI' (i := i) hilt]
    by_cases hk1 : σ (idx key i) = true
    · by_cases he : eVal key img σ i = true
      · exact Or.inr (Or.inr (h i hilt ((eVal_spec key img σ i).mp he) hk1))
      · exact Or.inl (by simpa using he)
    · exact Or.inr (Or.inl (by simpa using hk1))
  -- Putting it together: `lexClauses` is the concatenation of the four families.
  intro C hC
  simp only [lexClauses] at hC
  -- `++` is **left**-associative in Lean 4: `((head ++ steps) ++ order) ++ constraints`.
  rcases List.mem_append.mp hC with hC | hC
  · rcases List.mem_append.mp hC with hC | hC
    · rcases List.mem_append.mp hC with hC | hC
      · exact head_sat C hC
      · rcases List.mem_flatMap.mp hC with ⟨i, hi, hCi⟩
        exact step_sat i hi C hCi
    · exact order_sat C hC
  · rcases List.mem_flatMap.mp hC with ⟨i, hi, hCi⟩
    exact constr_sat i hi C hCi

end QECCertificates.LRAT
