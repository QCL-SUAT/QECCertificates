/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

/-!
# The closure theorem for syndrome-exhaustive check matrices

An abstract theory of the columns of a GF(2) parity-check matrix, with no
code-specific input. Its subject is the *syndrome map* of a check matrix and
the dichotomy between the two regimes every weight-1 decoder lives in.

* **(T1) closure.** Under exhaustion — every nonzero width-`r` vector is a
  column — the XOR of two distinct columns is again a column, at a third
  location different from both. Two same-sector faults present a weight-1
  decoder with the syndrome of a single fault, and the correction it applies
  leaves a zero-syndrome weight-three triple.
* **(T5) the decoder information limit.** The closure bounds the syndrome,
  not the decoder: no decoder correct on every single fault avoids that
  triple, because the information separating the pair from the single fault
  is not in the syndrome.
* **(T3) Steiner.** Under exhaustion the weight-three dependencies form a
  Steiner triple system on the columns — the Fano plane at $r = 3$.
* **(T2) sharp converse.** Pair closure together with a spanning column set
  *is* exhaustion, so closure cannot be bought partially: the codes in which
  every pair miscorrects are exactly the Hamming parity checks.
* **(T4) detection.** If no three distinct columns XOR to zero then no pair
  miscorrects — the far side of the dichotomy.

The worked instance `hammingCols` runs **T1** and **T3** through the abstract
interface at the seven columns of the $[[7,1,3]]$ check matrix, its exhaustiveness
discharged by an eight-way case split.

**Boundary.** This module formalizes the combinatorics of a column set over
`Bool` lists. It does not formalize a quantum code, a stabilizer group or a
decoding algorithm: `dec` in T5 is any function satisfying one hypothesis, and
the connection to a physical decoder is a dictionary this module does not
state. The quantum-code instances that use it live in the developments that
import this library.

Ported from the measurement-free QEC development, where this module is
`QECFormal.ClosureTheorem`; the proof bodies are unchanged and only the
namespace differs.

**No imports.** This module elaborates against the core library alone, which
is how the development it comes from keeps its artifact rebuildable offline;
the port added an `import Mathlib` and the module does not need it, so it is
gone.
-/

namespace QECCertificates.ClosureTheorem

/-! ## GF(2) vectors as Bool lists. -/

/-- Pointwise XOR of two equal-width GF(2) vectors. -/
def Xor (a b : List Bool) : List Bool := List.zipWith (fun x y => x ^^ y) a b

/-- The zero vector of width `n`. -/
def Zeros (n : Nat) : List Bool := List.replicate n false

/-- `v` is not the zero vector. -/
def NonzeroVec (v : List Bool) : Prop := v ≠ Zeros v.length

/-- Every column has width `r`. -/
def AllWidth (r : Nat) (cols : List (List Bool)) : Prop :=
  ∀ c ∈ cols, c.length = r

/-- EXHAUSTION: every nonzero vector of width `r` is a column, i.e. the
    single-fault syndrome map is bijective onto the nonzero syndromes. -/
def Exhaustive (r : Nat) (cols : List (List Bool)) : Prop :=
  ∀ v : List Bool, v.length = r → NonzeroVec v → v ∈ cols

/-- PAIR CLOSURE: the XOR of any two distinct columns is again a column. -/
def PairClosed (cols : List (List Bool)) : Prop :=
  ∀ a ∈ cols, ∀ b ∈ cols, a ≠ b → Xor a b ∈ cols

/-- NO TRIPLE: no three distinct columns XOR to zero. -/
def NoTriple (r : Nat) (cols : List (List Bool)) : Prop :=
  ∀ a ∈ cols, ∀ b ∈ cols, ∀ c ∈ cols,
    a ≠ b → b ≠ c → a ≠ c → Xor a (Xor b c) ≠ Zeros r

/-- The span of the columns: the least class containing the zero vector and
    the columns and closed under XOR - the XORs of sublists, "the columns
    span the full space" for the full version. -/
inductive Span (r : Nat) (cols : List (List Bool)) : List Bool → Prop
  | zeros : Span r cols (Zeros r)
  | col {c : List Bool} (h : c ∈ cols) (hc : c.length = r) : Span r cols c
  | xor {u w : List Bool} (hu : Span r cols u) (hw : Span r cols w)
      (hl : u.length = r) (hl' : w.length = r) : Span r cols (Xor u w)

/-! ## XOR algebra. -/

theorem zeros_length (n : Nat) : (Zeros n).length = n := by simp [Zeros]

/-- Congruence lemmas: each is `rfl`, so induction proofs rewrite one layer
    at a time without unfolding the definition. -/
theorem xor_nil_left (b : List Bool) : Xor [] b = [] := rfl

theorem xor_nil_right (a : List Bool) : Xor a [] = [] := by
  cases a with
  | nil => rfl
  | cons _ _ => rfl

theorem xor_cons (x y : Bool) (xs ys : List Bool) :
    Xor (x :: xs) (y :: ys) = (x ^^ y) :: Xor xs ys := rfl

theorem zeros_zero : Zeros 0 = [] := rfl

theorem zeros_succ (n : Nat) : Zeros (n + 1) = false :: Zeros n := rfl

theorem xor_comm : ∀ (a b : List Bool), Xor a b = Xor b a := by
  intro a
  induction a with
  | nil => intro b; cases b <;> rfl
  | cons x xs ih =>
    intro b
    cases b with
    | nil => rfl
    | cons y ys => simp [xor_cons, ih ys, Bool.xor_comm]

theorem xor_length {a b : List Bool} (h : a.length = b.length) :
    (Xor a b).length = a.length := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have h' : xs.length = ys.length := by simp at h; omega
      simp [xor_cons, List.length_cons, ih h']

theorem xor_zeros_left (a : List Bool) : Xor (Zeros a.length) a = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp [xor_cons, zeros_succ, List.length_cons, ih]

theorem xor_zeros_right (a : List Bool) : Xor a (Zeros a.length) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp [xor_cons, zeros_succ, List.length_cons, ih]

theorem xor_zeros_width_left {a : List Bool} {n : Nat} (h : a.length = n) :
    Xor (Zeros n) a = a := by
  have hz : Zeros n = Zeros a.length := by rw [← h]
  rw [hz]
  exact xor_zeros_left a

theorem xor_zeros_width_right {a : List Bool} {n : Nat} (h : a.length = n) :
    Xor a (Zeros n) = a := by
  have hz : Zeros n = Zeros a.length := by rw [← h]
  rw [hz]
  exact xor_zeros_right a

theorem xor_self (a : List Bool) : Xor a a = Zeros a.length := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp [xor_cons, zeros_succ, List.length_cons, ih]

theorem xor_assoc {a b c : List Bool} (hab : a.length = b.length)
    (hbc : b.length = c.length) :
    Xor a (Xor b c) = Xor (Xor a b) c := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil => cases c <;> rfl
    | cons _ _ => simp at hab
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases c with
      | nil => simp at hbc
      | cons z zs =>
        have e1 : xs.length = ys.length := by simp at hab; omega
        have e2 : ys.length = zs.length := by simp at hbc; omega
        simp [xor_cons, ih e1 e2]

theorem xor_cancel {a b : List Bool} (h : a.length = b.length) :
    Xor a (Xor a b) = b := by
  rw [xor_assoc (rfl : a.length = a.length) h, xor_self]
  have hz : Zeros a.length = Zeros b.length := by rw [h]
  rw [hz]
  exact xor_zeros_left b

theorem xor_eq_zeros {a b : List Bool} (h : a.length = b.length) :
    Xor a b = Zeros a.length ↔ a = b := by
  constructor
  · intro heq
    have h1 : Xor a (Xor a b) = b := xor_cancel h
    rw [heq] at h1
    rw [xor_zeros_right] at h1
    exact h1
  · intro heq
    rw [heq, xor_self]

/-- If the XOR of two equal-width vectors equals the first, the second is
    the zero vector. -/
theorem xor_eq_left_imp_zeros {a b : List Bool} (h : a.length = b.length)
    (heq : Xor a b = a) : b = Zeros b.length := by
  have h1 : Xor a (Xor a b) = b := xor_cancel h
  rw [heq, xor_self] at h1
  exact Eq.trans h1.symm (by rw [h])

/-- If the XOR of two equal-width vectors equals the second, the first is
    the zero vector. -/
theorem xor_eq_right_imp_zeros {a b : List Bool} (h : a.length = b.length)
    (heq : Xor a b = b) : a = Zeros a.length :=
  xor_eq_left_imp_zeros h.symm (by rw [xor_comm]; exact heq)

/-- The corrected triple has zero syndrome: pure algebra, no hypotheses
    beyond equal widths. -/
theorem triple_xor_zero {a b : List Bool} (h : a.length = b.length) :
    Xor a (Xor b (Xor a b)) = Zeros a.length := by
  have hx : (Xor a b).length = a.length := xor_length h
  rw [xor_assoc h (by omega), xor_self, xor_length h]

/-! ## (T1) Closure: exhaustion gives the third location. -/

/-- **(T1) Closure.** Under exhaustion, the XOR of any two distinct columns
    is again a column, at a third location different from both: two
    same-sector faults present the weight-1 decoder with the syndrome of
    one single fault, and the correction it applies leaves a triple with
    zero syndrome - a logical operator whenever every nontrivial stabilizer
    has weight at least four. -/
theorem closure_third_mem (r : Nat) (cols : List (List Bool))
    (hw : AllWidth r cols) (hnz : ∀ c ∈ cols, NonzeroVec c)
    (hex : Exhaustive r cols) :
    ∀ a ∈ cols, ∀ b ∈ cols, a ≠ b →
      ∃ c, c ∈ cols ∧ c ≠ a ∧ c ≠ b ∧ Xor a b = c := by
  intro a ha b hb hab
  have hla : a.length = r := hw a ha
  have hlb : b.length = r := hw b hb
  have hlab : b.length = a.length := by omega
  have hxl : (Xor a b).length = r := by
    rw [xor_length hlab.symm]; exact hla
  have hvz : NonzeroVec (Xor a b) := by
    intro h0
    have h0' : Xor a b = Zeros a.length := by
      rw [h0, xor_length hlab.symm]
    exact hab ((xor_eq_zeros hlab.symm).mp h0')
  have hmem : Xor a b ∈ cols := hex (Xor a b) hxl hvz
  refine ⟨Xor a b, hmem, ?_, ?_, rfl⟩
  · exact fun heq => hnz b hb (xor_eq_left_imp_zeros hlab.symm heq)
  · exact fun heq => hnz a ha (xor_eq_right_imp_zeros hlab.symm heq)

/-- **(T5) Decoder information limit.** The closure is a limit on the
    syndrome, not on the decoder.  Let `dec` be *any* decoder: it is handed a
    syndrome and returns a correction, and it is assumed correct on every
    single fault, in the sense that feeding it a column returns that column.
    Under exhaustion, on the syndrome of any pair of distinct faults it must
    return a third column, different from both, because that syndrome is the
    third column's own.  The residual is then the zero-syndrome weight-three
    triple, and no choice of decoder avoids it: the information separating the
    pair from the single fault is not in the syndrome. -/
theorem decoder_information_limit (r : Nat) (cols : List (List Bool))
    (hw : AllWidth r cols) (hnz : ∀ c ∈ cols, NonzeroVec c)
    (hex : Exhaustive r cols) (dec : List Bool → List Bool)
    (hdec : ∀ c ∈ cols, dec c = c) :
    ∀ a ∈ cols, ∀ b ∈ cols, a ≠ b →
      ∃ c, c ∈ cols ∧ c ≠ a ∧ c ≠ b ∧ dec (Xor a b) = c ∧
        Xor (Xor a b) c = Zeros r := by
  intro a ha b hb hab
  obtain ⟨c, hc, hca, hcb, hx⟩ :=
    closure_third_mem r cols hw hnz hex a ha b hb hab
  refine ⟨c, hc, hca, hcb, ?_, ?_⟩
  · rw [hx]; exact hdec c hc
  · rw [hx, xor_self]; exact congrArg Zeros (hw c hc)

/-! ## (T3) Steiner: the unique third completing a zero-sum triple. -/

/-- **(T3) Steiner.** Under exhaustion, for every pair of distinct columns
    there is exactly one column completing the pair to a zero-sum triple:
    the weight-3 dependencies form a Steiner triple system on the columns. -/
theorem steiner_unique_third (r : Nat) (cols : List (List Bool))
    (hw : AllWidth r cols) (hnz : ∀ c ∈ cols, NonzeroVec c)
    (hex : Exhaustive r cols) :
    ∀ a ∈ cols, ∀ b ∈ cols, a ≠ b →
      ∃ c, c ∈ cols ∧ c ≠ a ∧ c ≠ b ∧ Xor a (Xor b c) = Zeros r ∧
        ∀ c' ∈ cols, Xor a (Xor b c') = Zeros r → c' = c := by
  intro a ha b hb hab
  obtain ⟨c, hc, hca, hcb, hxab⟩ :=
    closure_third_mem r cols hw hnz hex a ha b hb hab
  have hla : a.length = r := hw a ha
  have hlb : b.length = r := hw b hb
  refine ⟨c, hc, hca, hcb, ?_, ?_⟩
  · have hz : Xor a (Xor b (Xor a b)) = Zeros a.length :=
      triple_xor_zero (by omega)
    rw [← hxab, hz, hla]
  · intro c' hc' hzero
    have hlb' : b.length = c'.length := by
      have := hw c' hc'; omega
    -- Xor a (Xor b c') = Zeros r  =>  Xor b c' = a
    have key : Xor b c' = a := by
      have h1 : a.length = (Xor b c').length := by
        rw [xor_length hlb']; omega
      have h2 : Xor a (Xor a (Xor b c')) = Xor b c' := xor_cancel h1
      rw [hzero, ← hla] at h2
      rw [xor_zeros_right] at h2
      exact h2.symm
    -- c' = Xor b (Xor b c') = Xor b a = Xor a b = c
    have h3 : Xor b (Xor b c') = c' := xor_cancel hlb'
    rw [key, xor_comm] at h3
    exact (hxab.symm.trans h3).symm

/-! ## (T2) Sharp converse: pair closure + full span forces exhaustion. -/

/-- Pair closure confines the span: everything reachable from the columns
    under XOR is either the zero vector or a column itself. -/
theorem span_pair_closed_mem (r : Nat) (cols : List (List Bool))
    (hw : AllWidth r cols) (hpc : PairClosed cols) :
    ∀ v, Span r cols v → v = Zeros r ∨ v ∈ cols := by
  intro v hv
  induction hv with
  | zeros => exact Or.inl rfl
  | col h _ => exact Or.inr h
  | @xor u w _ _ _ _ ih_u ih_w =>
    cases ih_u with
    | inl hu0 =>
      cases ih_w with
      | inl hw0 =>
        left
        rw [hu0, hw0, xor_self, zeros_length]
      | inr hwc =>
        right
        rw [hu0, xor_zeros_width_left (hw w hwc)]
        exact hwc
    | inr huc =>
      cases ih_w with
      | inl hw0 =>
        right
        rw [hw0, xor_zeros_width_right (hw u huc)]
        exact huc
      | inr hwc =>
        by_cases hEq : u = w
        · left
          rw [hEq, xor_self, hw w hwc]
        · exact Or.inr (hpc u huc w hwc hEq)

/-- **(T2) Sharp converse.** If every pair of distinct columns XORs to a
    column and the columns span the full space, then every nonzero vector
    is a column: pair closure plus full rank IS exhaustion. The codes in
    which every pair miscorrects are exactly the Hamming parity checks. -/
theorem sharp_converse (r : Nat) (cols : List (List Bool))
    (hw : AllWidth r cols) (hpc : PairClosed cols)
    (hspan : ∀ v, v.length = r → Span r cols v) :
    Exhaustive r cols := by
  intro v hlen hvz
  cases span_pair_closed_mem r cols hw hpc v (hspan v hlen) with
  | inl h0 => exact absurd (by rw [hlen]; exact h0) hvz
  | inr hmem => exact hmem

/-! ## (T4) Detection: no zero-sum triple means no pair miscorrects. -/

/-- **(T4) Detection.** If no three distinct columns XOR to zero, then the
    XOR of any two distinct columns is not a column: no two-fault syndrome
    is a single-fault syndrome, so every pair is detected rather than
    miscorrected. -/
theorem detection (r : Nat) (cols : List (List Bool))
    (hw : AllWidth r cols) (hnz : ∀ c ∈ cols, NonzeroVec c)
    (hnt : NoTriple r cols) :
    ∀ a ∈ cols, ∀ b ∈ cols, a ≠ b → ∀ c ∈ cols, c ≠ Xor a b := by
  intro a ha b hb hab c hc heq
  have hla : a.length = r := hw a ha
  have hlb : b.length = r := hw b hb
  have hlab : b.length = a.length := by omega
  have hca : c ≠ a := by
    intro hca'
    have hXa : Xor a b = a := heq.symm.trans hca'
    exact hnz b hb (xor_eq_left_imp_zeros hlab.symm hXa)
  have hcb : c ≠ b := by
    intro hcb'
    have hXb : Xor a b = b := heq.symm.trans hcb'
    exact hnz a ha (xor_eq_right_imp_zeros hlab.symm hXb)
  apply hnt a ha b hb c hc hab (Ne.symm hcb) (Ne.symm hca)
  have hz : Xor a (Xor b (Xor a b)) = Zeros a.length :=
    triple_xor_zero (by omega)
  rw [heq, hz, hla]

/-! ## The worked instance: the [[7,1,3]] check matrix through the
    abstract interface. -/

/-- The seven columns of the Steane check matrix Eq.~(2): all seven nonzero
    3-bit vectors, in the column order of SteaneCode. -/
def hammingCols : List (List Bool) :=
  [[true, true, true], [true, true, false], [true, false, true],
   [true, false, false], [false, true, true], [false, true, false],
   [false, false, true]]

theorem hamming_width : AllWidth 3 hammingCols := by
  intro c hc
  have h : hammingCols.all (fun c => c.length == 3) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem hamming_nonzero : ∀ c ∈ hammingCols, NonzeroVec c := by
  intro c hc h0
  have h3 : c.length = 3 := hamming_width c hc
  have hz3 : c = Zeros 3 := by rw [h0, h3]
  have hnm : Zeros 3 ∉ hammingCols := by decide
  exact hnm (by rw [← hz3]; exact hc)

/-- EXHAUSTION for the Steane check matrix, discharged by the eight-way
    case split over 3-bit vectors: the single-fault syndrome map of the
    [[7,1,3]] is bijective onto the nonzero syndromes. -/
theorem hamming_exhaustive : Exhaustive 3 hammingCols := by
  intro v hv hvz
  cases v with
  | nil => simp at hv
  | cons x1 v1 =>
    cases v1 with
    | nil => simp at hv
    | cons x2 v2 =>
      cases v2 with
      | nil => simp at hv
      | cons x3 v3 =>
        cases v3 with
        | nil =>
          cases x1 <;> cases x2 <;> cases x3 <;>
            first
            | exact absurd rfl hvz
            | decide
        | cons _ _ => simp at hv

/-- The [[7,1,3]] closure through the abstract interface (T1): the
    instance certificate of SyndromeClosure is this theorem at the
    literals. -/
theorem hamming_closure_instance :
    ∀ a ∈ hammingCols, ∀ b ∈ hammingCols, a ≠ b →
      ∃ c, c ∈ hammingCols ∧ c ≠ a ∧ c ≠ b ∧ Xor a b = c :=
  closure_third_mem 3 hammingCols hamming_width hamming_nonzero
    hamming_exhaustive

/-- The [[7,1,3]] Steiner structure through the abstract interface (T3):
    every pair of locations has a unique third completing a zero-sum
    triple, the Fano-plane incidence of SteaneGeometry. -/
theorem hamming_steiner_instance :
    ∀ a ∈ hammingCols, ∀ b ∈ hammingCols, a ≠ b →
      ∃ c, c ∈ hammingCols ∧ c ≠ a ∧ c ≠ b ∧ Xor a (Xor b c) = Zeros 3 ∧
        ∀ c' ∈ hammingCols, Xor a (Xor b c') = Zeros 3 → c' = c :=
  steiner_unique_third 3 hammingCols hamming_width hamming_nonzero
    hamming_exhaustive

end QECCertificates.ClosureTheorem
