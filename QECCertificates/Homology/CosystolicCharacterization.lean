/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.CosystolicLowWeight

open QECCertificates

/-!
# A complete characterization of the $1$-cosystolic distance, reducing the minimal weight
to a pair of parity conditions

`Homology/CosystolicLowWeight.lean` reduces $d_1^\bullet\ge3$ to a finite criterion, and its
honest boundary left one item open: **the classification at weight $\ge3$ and the general
lower bound were not done**, the reason being that $d_1^\bullet$ is the minimum weight of the
quotient code $\ker\delta_2/\mathrm{im}\,\delta_1$, of the same difficulty as the classical
code-distance lower bound. This module pushes that boundary to **arbitrary weight**:
$d_1^\bullet$ has a fully explicit **combinatorial characterization**, so that the
classification by weight becomes a finite parity decision at **every** weight $w$, no longer
"only up to 2".

$u$ is a vector over $\mathbb F_2$, so $u=\mathbf 1_S$ (with $S$ taken as its support, see
`eq_indVec_support`), and both membership decisions therefore become **"the cardinality of
the intersection of two sets"**:

* the coordinatewise form of $\delta_2\mathbf 1_S=0$ is that $|S\cap W_w|$ is **even** (for
  every $w$) — the $w$-th row of $\delta_2$ is the indicator vector of $W_w$
  (`surgeryD2_mulVec_indVec_apply`);
* the criterion for $\mathbf 1_S\in\mathrm{im}\,\delta_1$
  (`exists_surgeryD1_eq_iff_forall_component`, i.e.
  $\mathrm{im}\,\delta_1=(\ker\delta_1^{\mathsf T})^\perp$) is that $|S\cap C|$ is **even**
  (for every component $C$).

The two are **of the same form**: both ask for "an even value on some family of sets", the
only difference being the object that must be even — the kernel asks "even on every $W_w$",
the image asks "even on every component". Hence

$$\mathbf 1_S\in\ker\delta_2\setminus\mathrm{im}\,\delta_1
\iff \Bigl(\forall w,\ |S\cap W_w|\ \text{is even}\Bigr)\ \wedge\
\Bigl(\exists\ \text{component}\ C,\ |S\cap C|\ \text{is odd}\Bigr),$$

that is, `isCosystolic_indVec_iff`. **Both factors are decidable**: the former checks the
members of $W$ one by one, the latter checks the parity of $|S\cap C|$ one by one ($C$ is
limited to components, so it suffices to look for $C$ in $\ker\delta_1^{\mathsf T}$ (a kernel
over GF(2)), without enumerating $\binom{k}{|S|}$ subspace membership decisions).

## Contents

* §1, two tools: the **coordinatewise formula** for $\delta_2$ on an indicator vector
  (`surgeryD2_mulVec_indVec_apply`), and the **coordinate-sum formula** for an indicator
  vector over an arbitrary set (`sum_indVec_mem`).
* §2, the **main characterization** (`isCosystolic_indVec_iff`).
* §3, three corollaries: the **lower-bound criterion at arbitrary weight**
  (`le_cosystolicDistance_iff_finset` — every lower bound is a statement about sets), the
  **upper witness** (`cosystolicDistance_le_card_of_indVec`), and its **low-weight form**
  (`three_le_cosystolicDistance_iff_no_small`, the same criterion as in `CosystolicLowWeight`).

## Honest boundary

* This module reduces $d_1^\bullet$ to a **finite parity problem**, so the classification at
  every fixed weight $w$ is decidable; it **gives no closed form**, and a closed form (or even
  a "general lower bound") remains of the same difficulty as the code-distance lower bound of
  a classical code. The difficulty is not circumvented, only **named**: the solution set of the
  parity conditions is exactly a coset of a linear code, and the minimal-weight problem sits
  there.
* The first criterion must be checked for **every** $w$; when the index set of $W$ is infinite
  it is not a finite condition (the uses in this library are all finite).
* Throughout, the convention is the $Z$ side ($1$-cosystolic distance); no claim is made about
  the two components.
-/

namespace QECCertificates.Homology

open _root_.Matrix

open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. Two tools: the cardinality of an intersection, as a coordinate and a coordinate sum -/

/-- **The coordinatewise formula for $\delta_2$ on an indicator vector**: the value
$(\delta_2\mathbf 1_S)_w$ is the cardinality of $S\cap W_w$ (in $\mathbb F_2$). The $w$-th
row of $\delta_2$ is the indicator vector of $W_w$, so this coordinate is the coordinate sum
of $S\cap W_w$, and the coordinate sum of an indicator vector is its cardinality. -/
theorem surgeryD2_mulVec_indVec_apply {ι : Type*} (W : ι → Finset (Fin k))
    (S : Finset (Fin k)) (w : ι) :
    (surgeryD2 W *ᵥ indVec S) w = ((S ∩ W w).card : ZMod 2) := by
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row_apply]
  have hterm : ∀ v : Fin k, surgeryD2 W w v * indVec S v
      = (if v ∈ S ∩ W w then (1 : ZMod 2) else 0) := by
    intro v
    have h1 : surgeryD2 W w v = (if v ∈ W w then (1 : ZMod 2) else 0) := rfl
    by_cases hv : v ∈ S <;> by_cases hw : v ∈ W w <;>
      simp [h1, indVec, hv, hw, Finset.mem_inter]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The coordinate sum of an indicator vector over an arbitrary set equals the
cardinality of the intersection**: $\sum_{v\in C}\mathbf 1_S(v)=|C\cap S|$. -/
theorem sum_indVec_mem {n : ℕ} (C S : Finset (Fin n)) :
    ∑ v ∈ C, indVec S v = ((C ∩ S).card : ZMod 2) := by
  have hterm : ∀ v : Fin n, indVec S v = (if v ∈ S then (1 : ZMod 2) else 0) := by
    intro v
    by_cases hv : v ∈ S <;> simp [indVec, hv]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_boole,
    Finset.filter_mem_eq_inter]

/-! ## 2. The main characterization -/

/-- **A complete characterization of the $1$-cosystolic cochains** (the main theorem): the
indicator vector $\mathbf 1_S$ is a $1$-cosystolic cochain if and only if

* **kernel condition**: $S$ meets **every** $W_w$ in an even number of vertices;
* **non-image condition**: there is a component $C$ whose intersection with $S$ has an
  **odd** number of vertices.

Both are finite parity decisions, and **neither is specific to a weight** — this is the source
of the classification of $d_1^\bullet$ by weight at an arbitrary $w$. -/
theorem isCosystolic_indVec_iff {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (S : Finset (Fin k)) :
    IsCosystolic H W (indVec S)
      ↔ (∀ w : ι, Even ((S ∩ W w).card))
        ∧ (∃ C : Finset (Fin k), IsComponent H C ∧ Odd ((S ∩ C).card)) := by
  classical
  have hker : surgeryD2 W *ᵥ indVec S = 0 ↔ ∀ w : ι, Even ((S ∩ W w).card) := by
    constructor
    · intro h w
      have hw := congrFun h w
      rw [Pi.zero_apply, surgeryD2_mulVec_indVec_apply] at hw
      exact (even_iff_natCast_zmod_two_eq_zero _).mpr hw
    · intro h
      funext w
      rw [Pi.zero_apply, surgeryD2_mulVec_indVec_apply]
      exact (even_iff_natCast_zmod_two_eq_zero _).mp (h w)
  have him : (∃ f : Vec m, surgeryD1 H *ᵥ f = indVec S)
      ↔ ∀ C : Finset (Fin k), IsComponent H C → Even ((S ∩ C).card) := by
    rw [exists_surgeryD1_eq_iff_forall_component]
    constructor
    · intro h C hC
      have hz := h C hC
      rw [sum_indVec_mem, Finset.inter_comm] at hz
      exact (even_iff_natCast_zmod_two_eq_zero _).mpr hz
    · intro h C hC
      rw [sum_indVec_mem, Finset.inter_comm]
      exact (even_iff_natCast_zmod_two_eq_zero _).mp (h C hC)
  have hnot : (¬ ∃ f : Vec m, surgeryD1 H *ᵥ f = indVec S)
      ↔ ∃ C : Finset (Fin k), IsComponent H C ∧ Odd ((S ∩ C).card) := by
    rw [him]
    constructor
    · intro h
      by_contra hno
      exact h fun C hC => by
        by_contra hodd
        exact hno ⟨C, hC, Nat.not_even_iff_odd.mp hodd⟩
    · rintro ⟨C, hC, hodd⟩ hcon
      exact Nat.not_even_iff_odd.mpr hodd (hcon C hC)
  exact and_congr hker hnot

/-- **The vector form of the main characterization**: every vector is the indicator vector of
its support, so the criterion carries over to vectors verbatim. -/
theorem isCosystolic_iff_support {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (u : Vec k) :
    IsCosystolic H W u
      ↔ (∀ w : ι, Even ((support u ∩ W w).card))
        ∧ (∃ C : Finset (Fin k), IsComponent H C ∧ Odd ((support u ∩ C).card)) := by
  conv_lhs => rw [eq_indVec_support u]
  exact isCosystolic_indVec_iff H W (support u)

/-! ## 3. Three corollaries -/

/-- **The lower-bound criterion at arbitrary weight**: $t\le d_1^\bullet$ is equivalent to
"there is **no** set of cardinality $<t$ that is even on every $W_w$ and odd on some
component". This **reduces every lower-bound proof to a statement about a set**, with no
restriction on the weight — weights $1$, $2$, $3$, $\dots$ all use the same criterion. -/
theorem le_cosystolicDistance_iff_finset {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (hne : ∃ u : Vec k, IsCosystolic H W u) (t : ℕ) :
    t ≤ cosystolicDistance H W
      ↔ ∀ S : Finset (Fin k), (∀ w : ι, Even ((S ∩ W w).card)) →
          (∃ C : Finset (Fin k), IsComponent H C ∧ Odd ((S ∩ C).card)) →
          t ≤ S.card := by
  rw [le_cosystolicDistance_iff H W hne]
  constructor
  · intro h S h1 h2
    have := h (indVec S) ((isCosystolic_indVec_iff H W S).mpr ⟨h1, h2⟩)
    rwa [hammingNorm_indVec] at this
  · intro h u hu
    have hu' : IsCosystolic H W (indVec (support u)) := by
      rw [← eq_indVec_support u]; exact hu
    obtain ⟨h1, h2⟩ := (isCosystolic_indVec_iff H W (support u)).mp hu'
    exact h (support u) h1 h2

/-- **The upper witness**: a set satisfying the two parity conditions gives an upper bound on
$d_1^\bullet$, and the witness is its indicator vector. Together with the previous item,
$d_1^\bullet$ is squeezed on **both sides**: the lower bound is "no small set", the upper bound
is "there is such a set". -/
theorem cosystolicDistance_le_card_of_indVec {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) {S : Finset (Fin k)}
    (h1 : ∀ w : ι, Even ((S ∩ W w).card))
    (h2 : ∃ C : Finset (Fin k), IsComponent H C ∧ Odd ((S ∩ C).card)) :
    cosystolicDistance H W ≤ S.card := by
  have hmem : S.card ∈ {t : ℕ | ∃ u : Vec k, IsCosystolic H W u ∧ hammingNorm u = t} :=
    ⟨indVec S, (isCosystolic_indVec_iff H W S).mpr ⟨h1, h2⟩, hammingNorm_indVec S⟩
  exact csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hmem

/-- **The low-weight form**: the specialization of the main characterization to $t=3$, the
same criterion as in `CosystolicLowWeight` — "no solution set of cardinality $\le2$" is
$d_1^\bullet\ge3$. This one **does not need** a weight classification: the enumeration of the
shapes at weight $\le2$ (zero, a single point, two points) is replaced by the single phrase
"the cardinality of the set". -/
theorem three_le_cosystolicDistance_iff_no_small {ι : Type*} (H : AuxHypergraph k m)
    (W : ι → Finset (Fin k)) (hne : ∃ u : Vec k, IsCosystolic H W u) :
    3 ≤ cosystolicDistance H W
      ↔ ∀ S : Finset (Fin k), S.card ≤ 2 → (∀ w : ι, Even ((S ∩ W w).card)) →
          ¬ ∃ C : Finset (Fin k), IsComponent H C ∧ Odd ((S ∩ C).card) := by
  rw [le_cosystolicDistance_iff_finset H W hne 3]
  constructor
  · intro h S hcard h1 h2
    exact absurd (h S h1 h2) (by omega)
  · intro h S h1 h2
    by_contra hlt
    exact h S (by omega) h1 h2

/-! ## 4. The machine form of the hardness reduction: each (parity-check, generator) pair is
realized as an auxiliary hypergraph

The sentence "no closed form is available" in `SM` rests on a construction: take any linear
code $C=\ker M$ and its subcode $D=\operatorname{rowsp}G$, take the **row supports** of $M$ as
the family of components and the **row supports** of $G$ as the hyperedges; then the
admissible vectors on the resulting auxiliary hypergraph are exactly the elements of
$C\setminus D$ — so a general algorithm for $d_1^\bullet$ incidentally computes the minimum
weight of a linear code (after removing a subcode). This section turns that construction into
theorems: the two bridges are each a single `ext` (a GF(2) matrix entry is only $0$ or $1$,
so "the indicator of a row support" is the row itself), and the main characterization is read
off directly from the definitions of §2. -/

/-- A GF(2) matrix entry is only $0$ or $1$. -/
theorem zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl (ZMod.val_injective 2 (by rw [h, ZMod.val_zero]))
  · exact Or.inr (ZMod.val_injective 2 (by rw [h, ZMod.val_one]))

/-- The support of the `w`-th row of a matrix (as a `Finset`). -/
def matRowSupport {k : ℕ} {ι : Type*} (M : Matrix ι (Fin k) (ZMod 2)) (w : ι) :
    Finset (Fin k) :=
  Finset.univ.filter (fun v => M w v = 1)

/-- Build an auxiliary hypergraph from the row supports of a generator matrix: the `e`-th
hyperedge is exactly the support of the `e`-th row of `G`. -/
def hypergraphOfRows {k m : ℕ} (G : Matrix (Fin m) (Fin k) (ZMod 2)) : AuxHypergraph k m where
  edge e := matRowSupport G e

/-- **Bridge one**: $\delta_2$ of the family of row supports is the original matrix —
$\ker\delta_2$ is exactly the kernel $\ker M$ of the parity-check matrix. -/
theorem surgeryD2_matRowSupport {k : ℕ} {ι : Type*} (M : Matrix ι (Fin k) (ZMod 2)) :
    surgeryD2 (matRowSupport M) = M := by
  ext w v
  show (if v ∈ Finset.univ.filter (fun v => M w v = 1) then (1 : ZMod 2) else 0) = M w v
  rcases zmod2_eq_zero_or_eq_one (M w v) with h | h
  · rw [ite_eq_right (by simp [h]), h]
  · rw [ite_eq_left (by simp [h]), h]

/-- **Bridge two**: $\delta_1$ of the row-support hypergraph is the transpose of the generator
matrix — $\operatorname{im}\delta_1$ is exactly spanned by the rows of $G$ (as vectors). -/
theorem surgeryD1_hypergraphOfRows {k m : ℕ} (G : Matrix (Fin m) (Fin k) (ZMod 2)) :
    surgeryD1 (hypergraphOfRows G) = Gᵀ := by
  ext v e
  show (if v ∈ Finset.univ.filter (fun v => G e v = 1) then (1 : ZMod 2) else 0) = G e v
  rcases zmod2_eq_zero_or_eq_one (G e v) with h | h
  · rw [ite_eq_right (by simp [h]), h]
  · rw [ite_eq_left (by simp [h]), h]

/-- On this realization the composite $\delta_2\circ\delta_1=0$ is exactly
$M * G^{\mathsf T}=0$ — the subcode is contained in the code. -/
theorem surgeryD2_mul_surgeryD1_hypergraphOfRows {k m : ℕ} {ι : Type*}
    (M : Matrix ι (Fin k) (ZMod 2)) (G : Matrix (Fin m) (Fin k) (ZMod 2)) :
    surgeryD2 (matRowSupport M) * surgeryD1 (hypergraphOfRows G) = M * Gᵀ := by
  rw [surgeryD2_matRowSupport, surgeryD1_hypergraphOfRows]

/-- **The main reduction theorem**: on the row-support realization, the admissible vectors are
exactly the vectors that lie in $\ker M$ but not in the span of the rows of $G$ (as vectors)
— that is, membership in $\ker M \setminus \operatorname{rowsp}G$. -/
theorem isCosystolic_hypergraphOfRows {k m : ℕ} {ι : Type*}
    (M : Matrix ι (Fin k) (ZMod 2)) (G : Matrix (Fin m) (Fin k) (ZMod 2)) (u : Vec k) :
    IsCosystolic (hypergraphOfRows G) (matRowSupport M) u
      ↔ M *ᵥ u = 0 ∧ ¬ ∃ c : Vec m, Gᵀ *ᵥ c = u := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [surgeryD1_hypergraphOfRows] at h2
    refine ⟨?_, h2⟩
    have h3 : surgeryD2 (matRowSupport M) *ᵥ u = 0 := h1
    rwa [surgeryD2_matRowSupport] at h3
  · rintro ⟨h1, h2⟩
    rw [← surgeryD1_hypergraphOfRows] at h2
    exact ⟨by rwa [surgeryD2_matRowSupport], h2⟩

/-- **The distance-level reading**: on this realization $d_1^\bullet$ is the minimum weight of
"the code after the subcode is removed". -/
theorem cosystolicDistance_hypergraphOfRows {k m : ℕ} {ι : Type*}
    (M : Matrix ι (Fin k) (ZMod 2)) (G : Matrix (Fin m) (Fin k) (ZMod 2)) :
    cosystolicDistance (hypergraphOfRows G) (matRowSupport M)
      = sInf {w : ℕ | ∃ u : Vec k, M *ᵥ u = 0 ∧ (¬ ∃ c : Vec m, Gᵀ *ᵥ c = u)
        ∧ hammingNorm u = w} := by
  have hset : {w : ℕ | ∃ u : Vec k,
        IsCosystolic (hypergraphOfRows G) (matRowSupport M) u ∧ hammingNorm u = w}
      = {w : ℕ | ∃ u : Vec k, M *ᵥ u = 0 ∧ (¬ ∃ c : Vec m, Gᵀ *ᵥ c = u)
        ∧ hammingNorm u = w} := by
    ext w
    constructor
    · rintro ⟨u, hu, hw⟩
      obtain ⟨h1, h2⟩ := (isCosystolic_hypergraphOfRows M G u).mp hu
      exact ⟨u, h1, h2, hw⟩
    · rintro ⟨u, h1, h2, hw⟩
      exact ⟨u, (isCosystolic_hypergraphOfRows M G u).mpr ⟨h1, h2⟩, hw⟩
  unfold cosystolicDistance
  rw [hset]

/-- **The empty-hyperedge special case**: when $G$ has zero rows (no hyperedges), $d_1^\bullet$
is exactly the minimum nonzero weight of the linear code $\ker M$ — the machine form of "a
general method for $d_1^\bullet$ incidentally computes the minimum distance of a linear code";
by Vardy's 1997 NP-hardness theorem, a general closed form for $d_1^\bullet$ cannot be expected
to be easier than the code distance. -/
theorem cosystolicDistance_eq_sInf_ker_ne_zero {k : ℕ} {ι : Type*}
    (M : Matrix ι (Fin k) (ZMod 2)) :
    cosystolicDistance (hypergraphOfRows (0 : Matrix (Fin 0) (Fin k) (ZMod 2)))
        (matRowSupport M)
      = sInf {w : ℕ | ∃ u : Vec k, M *ᵥ u = 0 ∧ u ≠ 0 ∧ hammingNorm u = w} := by
  rw [cosystolicDistance_hypergraphOfRows]
  have hzero : ∀ c : Vec 0,
      (0 : Matrix (Fin 0) (Fin k) (ZMod 2))ᵀ *ᵥ c = (0 : Vec k) := by
    intro c
    funext v
    simp [Matrix.mulVec, dotProduct]
  congr 1
  ext w
  constructor
  · rintro ⟨u, h1, h2, hw⟩
    refine ⟨u, h1, ?_, hw⟩
    intro hu
    exact h2 ⟨0, by rw [hzero 0, hu]⟩
  · rintro ⟨u, h1, h2, hw⟩
    refine ⟨u, h1, ?_, hw⟩
    rintro ⟨c, hc⟩
    rw [hzero c] at hc
    exact h2 hc.symm

end QECCertificates.Homology
