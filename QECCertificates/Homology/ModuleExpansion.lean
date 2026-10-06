/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.HypergraphSurgery

open QECCertificates

/-!
# The modular expansion and thickening of [14] §7

This module continues item 8 of §2 of the proposal (bringing homomorphic measurement into
the same reduce/solve/verify chain) on **[14] §7**: `Homology/HypergraphSurgery.lean`
generalises the auxiliary structure from a graph to a hypergraph and proves the Gauss-law
side, and this module supplies the part of §7 that **can be honestly machine-checked** —
among the inference chain "expansion condition on the auxiliary structure → distance
condition on the deformed code / compacted code", the **expansion side**: its definition,
its transfers and its construction.

[14] = Cowtan–He–Williamson–Yoder, *Fast and fault-tolerant logical measurements:
auxiliary hypergraphs and transversal surgery*, arXiv:2510.14895.

## 1. The formulation of [14] §7 (the source of this module's definitions)

The opening of [14] §7 (p. 35):

> In previous sections, we studied hypergraph surgery operations where the compacted code
> or the deformed codes has distance $d$. This is critical for fault-tolerance. In this
> section, we discuss sufficient expansion properties on the hypergraph for these
> conditions to hold.

**Definition 7.2 (Modular expansion)** (p. 35):

> Let $\mathcal{H}(\mathcal{V},\mathcal{E})$ be a hypergraph with incidence matrix
> $G : \mathbb{F}_2^{\mathcal{E}} \to \mathbb{F}_2^{\mathcal{V}}$ and specified subspace
> $W \subset \mathbb{F}_2^{\mathcal{V}}$ containing elements $\kappa_\lambda$. Let
> $t \in \mathbb{R}_+$ be a positive real number. The modular expansion
> $\mathcal{M}_t$ of $\mathcal{H}$ is the largest real number such that, for all
> $v \subseteq \mathcal{V}$,
> $$|G^{\intercal}v| \geq \mathcal{M}_t\min\bigl(t,\ |\kappa_\lambda| - |v \cap \kappa_\lambda|
> + |v \cap \mathcal{U}\backslash\kappa_\lambda| : \lambda \in 2^{I}\bigr)$$

where $\mathcal{U} = \bigcup_i V_i$, $V_i = \operatorname{supp}(v_i)$, and the $v_i$ form a
basis of $W$ (Def 7.1, p. 35).

**Definition 7.3 (Global expansion)** (p. 35): $\beta$ is the largest real number such that
$|G^{\intercal}v| \geq \beta\min(|v|,|\mathcal{V}\backslash v|)$ holds for every $v$.

**Definition 7.4 (Relative expansion)** (p. 36): $\beta_t$ is the largest real number such
that $|G^{\intercal}v| \geq \beta_t\min(t, |v \cap \mathcal{U}|, |\mathcal{U}| - |v \cap
\mathcal{U}|)$ holds for every $v$.

[14] §7 then gives this **commuting diagram** (the "informal commuting diagram" of p. 36):

> Modular expansion --($k=1$)--> Relative expansion --($\mathcal{U}=\mathcal{V}$, $t \geq n$)-->
> Global expansion
> (there is also a Soundness-of-an-LTC route: $t \geq n$, $\mathcal{U}=\mathcal{V}$)

**Lemma 7.9** (p. 37):

> Let $\mathcal{H}(\mathcal{V},\mathcal{E})$ be a hypergraph such that each element in
> $\ker(G^{\intercal})$ has the supporting set $\kappa_\lambda$ for some
> $\lambda \in 2^{I}$. Then $\mathcal{M}_t(\mathcal{H}) \geq \frac{1}{t}$.

**Theorem 7.8 (Thickening)** (p. 37):

> Let $\mathcal{H}(\mathcal{V},\mathcal{E})$ be a hypergraph with modular expansion
> $\mathcal{M}_t(\mathcal{H})$. Let $\mathcal{J}_L$ be the path graph with length
> $L \geq \frac{1}{\mathcal{M}_t(\mathcal{H})}$, i.e. $L$ vertices and $L-1$ edges. Let
> $\mathcal{H}_L := \mathcal{H}\,\square\,\mathcal{J}_L$ be the hypergraph of $\mathcal{H}$
> thickened $L$ times. Then $\mathcal{H}_L$ has modular expansion
> $\mathcal{M}_t(\mathcal{H}_L) \geq 1$ for $\mathcal{U}^{\ell} = \bigcup_i V^{\ell}_i$
> at any level $\ell \in \{1,2,\cdots,L\}$, where $V^{\ell}_i$ is the copy of $V_i$ in the
> $\ell$th level of the thickened hypergraph.

The first line of its proof (Appendix C, p. 86) is

$$G_L = \begin{pmatrix}G \otimes I_L & I_n \otimes R_L\end{pmatrix}$$

whence $|G_L^{\intercal}v| = \sum_{j=2}^{L}|v^{j-1} + v^{j}| +
\sum_{j=1}^{L}|G^{\intercal}v^{j}|$ — the `edgeDeg_thicken` of this module is that
**degree decomposition**.

**Corollary 7.10** (p. 37): if every element of $\ker(G^{\intercal})$ is some
$\kappa_\lambda$, then $\mathcal{H}_t$, thickened $t$ times, has
$\mathcal{M}_t(\mathcal{H}_t) \geq 1$ at every level.

## 2. This module's choice: why a constant-form predicate rather than a $\sup$

[14] defines $\mathcal{M}_t$ as the **largest** real number satisfying the inequality. This
module does not take a $\sup$; it writes "$\mathcal{M}_t(\mathcal{H}) \geq M$" directly as a
**predicate**

`HasModularExpansion inc κ U t M` := `∀ S, M * min t (modExpMin κ U S) ≤ |GᵀS|`.

This is mathematically equivalent: the set of real numbers satisfying the inequality is
closed under taking the smaller one (for $M' \le M$, $M'\min(\cdot) \le M\min(\cdot)$, and
$\min(\cdot) \ge 0$), so "$\mathcal{M}_t \geq M$" $\iff$ "$M$ satisfies the inequality"
$\iff$ this predicate. Writing a predicate has two advantages: (i) there is no need to form
a `csSup` over the reals (`Real` has no `OrderBot`, and `sSup` needs infrastructure such as
`BddAbove`); (ii) the downstream consumers (Thm 7.7 / 7.12 / 7.15) use **precisely** the
form "$\mathcal{M}_d \geq 1$", so the predicate lines up with the consumption interface
word for word (see `PreservesDistance` in §5).

## 3. The list of main theorems

* `edgeDeg_eq_zero_iff_isComponent`: **the bridge to the existing layer** — $|G^{\intercal}S|
  = 0$ $\iff$ `IsComponent H S` (a component) of `Homology/HypergraphSurgery.lean`. Thus the
  $\ker(G^{\intercal})$ of [14] and the component predicate already in this library are the
  same thing.
* `modExpMin_two`: for $|I| = 1$, `modExpMin` degenerates to $\min(|S \cap \mathcal{U}|,
  |\mathcal{U}| - |S \cap \mathcal{U}|)$ — the machine check of [14] §7 p. 36, "when
  $|I| = 1$ modular expansion reduces to relative expansion".
* `globalExpansion_of_modular_two`: for $\mathcal{U} = \mathcal{V}$, $t \geq
  |\mathcal{V}|$ and $|I| = 1$, modular expansion gives **the global expansion of Def 7.3**
  — the machine check of the arrow at the lower right of the commuting diagram.
* `modularExpansion_inv_of_component_mem`: **Lemma 7.9, word for word**.
* `edgeDeg_thicken`: **the degree decomposition in the proof of Theorem 7.8**.
* `symmDiffCard_level_le_sum_levelCut`: **the path triangle inequality** (the step in
  Appendix C that "uses the triangle inequality" to bound $|v^r + v^{\ell}|$ by the sum of
  all cuts).
* `modExpArgOf_le_add_symmDiffCard`: **the set-theoretic core of the Venn count** (the step
  in the proof of Thm 7.7 where the $\kappa$ expression is bounded by a symmetric
  difference).
* `modularExpansion_thicken`: **the conclusion of Theorem 7.8** ($\mathcal{M}_t \geq 1$
  after thickening, at any level).
* `PreservesDistance` / `preservesDistance_of_thicken`: **the constructive version of
  Corollary 7.10** — it gives a name to the hypothesis $\mathcal{M}_d \geq 1$ consumed by
  Theorem 7.7 / 7.12 / 7.15, and proves that "$\ker \subseteq W$ + thickening `d` times"
  suffices for it.
* `edgeDeg_univ_eq_zero_iff_starOp_sum_eq` / `edgeDeg_graphOf`: the two interfaces with the
  existing `starOp` layer and the 2-regular `graphOf` layer.

## 4. Honest boundaries

**Done**: the machine-checked form of the definitions of §7 (Def 7.2/7.3/7.4) on the
auxiliary hypergraph layer, the three degeneration relations, Lemma 7.9, the degree
decomposition and the conclusion of Theorem 7.8, Corollary 7.10, and the two interfaces
with the existing `IsComponent`/`starOp`.

**Not done** (the scope of this module; **no claim** is made):

1. **The distance transfer of Theorem 7.7**. The "distance of the deformed code
   $Q \leftrightarrow \mathcal{H}$ is $\geq d$" in the statement of the theorem needs the
   gluing of $Q$ and $\mathcal{H}$ — **this module** does not formalize the deformed code,
   so it is not stated here. (`the gauged-measurement companion development's `DeformedCode` module` gives the **original form** of
   Thm 7.7, and what is proved there is Case 1; Case 2 is still not claimed — it is stuck
   on the support reading of Figure 9, and that connectivity is not missing from the
   source, [57]'s equation (9) supplies it.)
   The core of its proof (Appendix C, p. 86) is a **seven-region Venn count**
   ($\tau_\lambda,\sigma_\lambda,B_\lambda,B'_\lambda,R_\lambda,\gamma_\lambda,
   \varphi_\lambda$ given by the figure of Figure 9; the text does not write the region
   definitions down verbatim). **That count is machine-checked**, in
   `the gauged-measurement companion development's `VennPartition` module`: the partition is recovered from the Boolean combinations
   of $\bar\Lambda_Z,\mathcal U,\kappa_\lambda,v$, equation (2) is proved as an
   **identity** (`venn_card_identity`, with no hypotheses), and the merged arithmetic is in
   `modularExpansion_merge_bound`. **The determinacy of the partition** comes from
   exhausting the structure "the lattice of set memberships" and then solving back for the
   region membership from equation (2); equations (1) and (3) are still **not done** (they
   are operator-level products and supports, and need the semantics of the deformed code).
2. **The "cycles are gauge-fixed" layer** (Remark 7.11): it needs gauge logical operators
   and the distance definition of a subsystem code, which this library does not formalize.
3. **The cross-block versions of Theorem 7.12 / Corollary 7.13 / Lemma 7.15**: all of them
   rest on Thm 7.7.
4. **The layer "$W$ is generated by $f_p(\xi_i)$"**: this module takes the $\kappa$ family
   as a **parameter** (`κ : ι → Finset V`, where $\iota$ is $2^I$), and does not construct
   its relation to the port function.

**Trust base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axioms; the `#print axioms` of the load-bearing theorems is in the root module
`QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open scoped BigOperators

/-! ## 1. $|G^{\intercal}S|$: the weight of the image of the transposed incidence matrix

The $G : \mathbb{F}_2^{\mathcal{E}} \to \mathbb{F}_2^{\mathcal{V}}$ of [14] is the
edge-vertex incidence matrix, $(G^{\intercal}v)_e = \sum_{x \in e} v_x \bmod 2$, so
$|G^{\intercal}v|$ is "the number of edges meeting $v$ in an **odd** number of vertices".
This module writes the incidence as a function `inc : E → Finset V` (`inc e` = the vertex
set of the `e`th edge), covering both `AuxHypergraph.edge` and the thickened hypergraph of
§3 (whose vertex and edge index types are no longer `Fin k` / `Fin m`). -/

/-- **$|G^{\intercal}S|$**: the number of edges meeting `S` in an odd number of vertices. -/
def edgeDegOf {V E : Type*} [Fintype E] [DecidableEq V] (inc : E → Finset V)
    (S : Finset V) : ℕ :=
  (Finset.univ.filter fun e => Odd ((S ∩ inc e).card)).card

/-- The $|G^{\intercal}S|$ of an auxiliary hypergraph. -/
def edgeDeg {k m : ℕ} (H : AuxHypergraph k m) (S : Finset (Fin k)) : ℕ :=
  edgeDegOf H.edge S

/-- **The bridge to the existing layer**: $|G^{\intercal}S| = 0$ $\iff$ `S` is a component
(`IsComponent` of `Homology/HypergraphSurgery.lean`, that is, the "meets every hyperedge in
an even number of vertices" of [14] §1.2). Thus the $\ker(G^{\intercal})$ of [14] §7 and the
component predicate already in this library are the same thing. -/
theorem edgeDeg_eq_zero_iff_isComponent {k m : ℕ} (H : AuxHypergraph k m)
    (S : Finset (Fin k)) : edgeDeg H S = 0 ↔ IsComponent H S := by
  rw [edgeDeg, edgeDegOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h e
    exact Nat.not_odd_iff_even.mp (h (Finset.mem_univ e))
  · intro h e _
    exact Nat.not_odd_iff_even.mpr (h e)

/-- A component is another spelling of $|G^{\intercal}S| = 0$ (in the `IsComponent`
direction). -/
theorem isComponent_iff_edgeDeg_eq_zero {k m : ℕ} (H : AuxHypergraph k m)
    (S : Finset (Fin k)) : IsComponent H S ↔ edgeDeg H S = 0 :=
  (edgeDeg_eq_zero_iff_isComponent H S).symm

/-! ## 2. The argument of Def 7.2, and modular expansion (the constant-form predicate) -/

/-- **The argument of the $\min$ in [14] Def 7.2**:
$|\kappa| - |v \cap \kappa| + |v \cap \mathcal{U}\backslash\kappa|$.

Written set-theoretically as $|\kappa \backslash v| + |(v \cap \mathcal{U}) \backslash
\kappa|$ — equivalent to the subtraction form word for word ($v \cap \kappa \subseteq
\kappa$), and without introducing truncated subtraction. -/
def modExpArgOf {V : Type*} [DecidableEq V] (κ U S : Finset V) : ℕ :=
  (κ \ S).card + ((S ∩ U) \ κ).card

/-- The $\min$ of Def 7.2 is taken over $\lambda \in 2^{I}$ — `ι` is $2^I$ (a finite index
set, hence nonempty) and `κ a` is $\kappa_a$. (`Finset.inf'` is used rather than
`Finset.inf`: $\mathbb{N}$ has `OrderBot` but no `OrderTop`.) -/
def modExpMin {V ι : Type*} [DecidableEq V] [Fintype ι] [Nonempty ι] (κ : ι → Finset V)
    (U S : Finset V) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a => modExpArgOf (κ a) U S)

/-- **The constant-form predicate for modular expansion**: $M$ satisfies the inequality of
Def 7.2, i.e. $\mathcal{M}_t(\mathcal{H}) \geq M$ (see §2 of the module docstring for why a
predicate rather than `sSup`). -/
def HasModularExpansion {V E ι : Type*} [Fintype E] [DecidableEq V] [Fintype ι] [Nonempty ι]
    (inc : E → Finset V) (κ : ι → Finset V) (U : Finset V) (t M : ℝ) : Prop :=
  ∀ S : Finset V, M * min t ((modExpMin κ U S : ℕ) : ℝ) ≤ (edgeDegOf inc S : ℝ)

/-- The relative expansion of [14] Def 7.4 (constant form). -/
def HasRelativeExpansion {V E : Type*} [Fintype E] [DecidableEq V]
    (inc : E → Finset V) (U : Finset V) (t M : ℝ) : Prop :=
  ∀ S : Finset V,
    M * min t (min (((S ∩ U).card : ℕ) : ℝ) (((U \ S).card : ℕ) : ℝ)) ≤ (edgeDegOf inc S : ℝ)

/-- The global expansion of [14] Def 7.3 (constant form). -/
def HasGlobalExpansion {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (inc : E → Finset V) (M : ℝ) : Prop :=
  ∀ S : Finset V,
    M * min (((S.card : ℕ) : ℝ)) (((Finset.univ \ S).card : ℕ) : ℝ) ≤ (edgeDegOf inc S : ℝ)

/-! ### The two degenerations of Def 7.2 (the commuting diagram of [14] §7 p. 36) -/

/-- For $|I| = 1$ (that is, $W = \{0, \mathcal{U}\}$) the $\min$ ranges over only two
elements — **this is the $\min$ of Def 7.4**. First a general form is proved: "the `inf'`
of two elements is their `min`". -/
theorem modExpMin_eq_min {V : Type*} [DecidableEq V] (κ : Fin 2 → Finset V) (U S : Finset V) :
    modExpMin κ U S = min (modExpArgOf (κ 0) U S) (modExpArgOf (κ 1) U S) := by
  rw [modExpMin]
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · exact Finset.inf'_le _ (Finset.mem_univ (0 : Fin 2))
    · exact Finset.inf'_le _ (Finset.mem_univ (1 : Fin 2))
  · refine Finset.le_inf' _ _ ?_
    intro b _
    fin_cases b
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- For $|I| = 1$ and $W = \{0,\mathcal{U}\}$, $\kappa_0 = \emptyset$ (the one with
$\lambda = \varnothing$ in Def 7.1). -/
theorem modExpArgOf_two_zero {V : Type*} [DecidableEq V] (U S : Finset V) :
    modExpArgOf ((fun i : Fin 2 => if i = 0 then (∅ : Finset V) else U) 0) U S
      = (S ∩ U).card := by
  change modExpArgOf (if (0 : Fin 2) = 0 then (∅ : Finset V) else U) U S = (S ∩ U).card
  rw [ite_eq_left rfl]
  simp [modExpArgOf]

/-- For $|I| = 1$ and $W = \{0,\mathcal{U}\}$, $\kappa_1 = \mathcal{U}$. -/
theorem modExpArgOf_two_one {V : Type*} [DecidableEq V] (U S : Finset V) :
    modExpArgOf ((fun i : Fin 2 => if i = 0 then (∅ : Finset V) else U) 1) U S
      = (U \ S).card := by
  change modExpArgOf (if (1 : Fin 2) = 0 then (∅ : Finset V) else U) U S = (U \ S).card
  rw [ite_eq_right (by decide : ¬((1 : Fin 2) = 0))]
  simp [modExpArgOf]

/-- For $|I| = 1$ we have $W = \{0, \mathcal{U}\}$, so the $\min$ ranges over only two
elements — **this is the $\min$ of Def 7.4** (the left half of the commuting diagram of
[14] §7 p. 36). -/
theorem modExpMin_two {V : Type*} [DecidableEq V] (U S : Finset V) :
    modExpMin (fun i : Fin 2 => if i = 0 then (∅ : Finset V) else U) U S
      = min ((S ∩ U).card) ((U \ S).card) := by
  rw [modExpMin_eq_min, modExpArgOf_two_zero, modExpArgOf_two_one]

/-- **[14] §7 p. 36: "when $|I| = 1$ modular expansion reduces to relative expansion"**. -/
theorem relativeExpansion_of_modular_two {V E : Type*} [Fintype E] [DecidableEq V]
    (inc : E → Finset V) (U : Finset V) (t M : ℝ)
    (h : HasModularExpansion inc (fun i : Fin 2 => if i = 0 then (∅ : Finset V) else U)
      U t M) :
    HasRelativeExpansion inc U t M := by
  intro S
  have hS := h S
  rw [modExpMin_two, Nat.cast_min] at hS
  exact hS

/-- **The arrow at the lower right of the commuting diagram of [14] §7 p. 36**: for
$\mathcal{U} = \mathcal{V}$ and $t \geq n$, the modular expansion with $|I| = 1$ gives
**the global expansion of Def 7.3**.

($t \geq n$ makes $\min(t, \cdot) = \cdot$: both arguments of the inner $\min$ are
$\leq n$.) -/
theorem globalExpansion_of_modular_two {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (inc : E → Finset V) {U : Finset V} (hU : U = Finset.univ) {t M : ℝ}
    (ht : (Fintype.card V : ℝ) ≤ t)
    (h : HasModularExpansion inc (fun i : Fin 2 => if i = 0 then (∅ : Finset V) else U)
      U t M) :
    HasGlobalExpansion inc M := by
  subst hU
  intro S
  have hrel := relativeExpansion_of_modular_two inc Finset.univ t M h S
  simp only [Finset.inter_univ] at hrel
  have h1 : ((S.card : ℕ) : ℝ) ≤ t :=
    le_trans (by exact_mod_cast Finset.card_le_univ S) ht
  have hle : min ((S.card : ℕ) : ℝ) (((Finset.univ \ S).card : ℕ) : ℝ) ≤ t :=
    le_trans (min_le_left _ _) h1
  rw [min_eq_right hle] at hrel
  exact hrel

/-! ## 3. Lemma 7.9: the kernel is covered by the specified family ⟹ $\mathcal{M}_t \geq 1/t$ -/

/-- **[14] §7 Lemma 7.9, word for word**: if every element of $\ker(G^{\intercal})$ is some
specified set $\kappa_\lambda$ (that is, $\ker \subseteq W$), then
$\mathcal{M}_t(\mathcal{H}) \geq \frac{1}{t}$.

The proof is the two-case argument of [14]:
* $|G^{\intercal}v| = 0$: $v$ lies in the kernel, so $v = \kappa_\lambda$, and then
  $|\kappa_\lambda| - |v \cap \kappa_\lambda| + |v \cap
  \mathcal{U}\backslash\kappa_\lambda| = 0$
  ($|\kappa_\lambda \backslash v| = 0$, $(v \cap \mathcal{U}) \backslash \kappa_\lambda =
  \emptyset$), so the right-hand side of the inequality is $0$;
* $|G^{\intercal}v| \geq 1$: look at which term the $\min$ takes — if it takes $t$, then
  $\frac{1}{t} \cdot t = 1 \leq |G^{\intercal}v|$; if it takes the expression $g$ in
  $\kappa$, then $g \leq t$, hence $\frac{1}{t} \cdot g \leq 1 \leq |G^{\intercal}v|$. -/
theorem modularExpansion_inv_of_component_mem {V E ι : Type*} [Fintype E] [DecidableEq V]
    [Fintype ι] [Nonempty ι] (inc : E → Finset V) (κ : ι → Finset V) (U : Finset V)
    {t : ℝ} (ht : 0 < t)
    (hker : ∀ S : Finset V, edgeDegOf inc S = 0 → ∃ a : ι, κ a = S) :
    HasModularExpansion inc κ U t (1 / t) := by
  intro S
  by_cases h0 : edgeDegOf inc S = 0
  · -- case 1: `S` lies in the kernel, so it is one of the specified `κ_λ`
    obtain ⟨lam₀, hlam₀⟩ := hker S h0
    have harg : modExpArgOf (κ lam₀) U S = 0 := by
      rw [← hlam₀]
      simp [modExpArgOf]
    have hle0 : modExpMin κ U S ≤ modExpArgOf (κ lam₀) U S := by
      rw [modExpMin]
      exact Finset.inf'_le _ (Finset.mem_univ lam₀)
    have hmin : modExpMin κ U S = 0 :=
      le_antisymm (by rw [harg] at hle0; exact hle0) (Nat.zero_le _)
    rw [hmin, h0, Nat.cast_zero, min_eq_right ht.le, mul_zero]
  · -- case 2: `|GᵀS| ≥ 1`
    have hpos : (1 : ℝ) ≤ (edgeDegOf inc S : ℝ) := by
      have : 1 ≤ edgeDegOf inc S := Nat.one_le_iff_ne_zero.mpr h0
      exact_mod_cast this
    by_cases htle : t ≤ ((modExpMin κ U S : ℕ) : ℝ)
    · rw [min_eq_left htle]
      have hone : (1 / t) * t = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt ht)]
      rw [hone]
      exact hpos
    · rw [min_eq_right (le_of_lt (lt_of_not_ge htle))]
      have hmle : ((modExpMin κ U S : ℕ) : ℝ) ≤ t := le_of_lt (lt_of_not_ge htle)
      calc (1 / t) * ((modExpMin κ U S : ℕ) : ℝ) ≤ (1 / t) * t :=
            mul_le_mul_of_nonneg_left hmle (by positivity)
        _ = 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt ht)]
        _ ≤ (edgeDegOf inc S : ℝ) := hpos

/-! ## 4. [14] Theorem 7.8: thickening

The first line of the proof in [14] Appendix C (p. 86) is `G_L = (G ⊗ I_L  I_n ⊗ R_L)`,
whence the **degree decomposition**
$$|G_L^{\intercal}v| = \sum_{j=2}^{L}|v^{j-1} + v^{j}| + \sum_{j=1}^{L}|G^{\intercal}v^{j}|$$
(`edgeDeg_thicken`) and $\mathcal{M}_t(\mathcal{H}_L) \geq 1$ (`modularExpansion_thicken`).
The $+$ of "$v^{j-1} + v^{j}$" is F₂ addition, that is, the **symmetric difference** of the
vertex sets. -/

/-- The vertex set on level `l`: the original-vertex part of `S` on the `l`th level — the
`v^{\ell}` of [14] Appendix C. -/
def level {k L : ℕ} (S : Finset (Fin k × Fin L)) (l : Fin L) : Finset (Fin k) :=
  Finset.univ.filter (fun x => (x, l) ∈ S)

@[simp] theorem mem_level {k L : ℕ} (S : Finset (Fin k × Fin L)) (l : Fin L) (x : Fin k) :
    x ∈ level S l ↔ (x, l) ∈ S := by
  simp [level]

/-- **The incidence map of the thickened `H □ J_L`** ([14] Appendix C's
`G_L = (G ⊗ I_L  I_n ⊗ R_L)`). The edges fall into two classes:

* the within-level copies `(e, l)`: the `e`th hyperedge of the `l`th level (`G ⊗ I_L`);
* the column path edges `(x, i)`: joining `(x, i)` to `(x, i+1)` (`I_n ⊗ R_L`).

When `i` is the last level the edge is empty, so there are exactly `L − 1` nonempty path
edges, matching the `L − 1` edges of the path graph `J_L` (for `L = 0` both classes are
empty). -/
def thickenInc {k m : ℕ} (H : AuxHypergraph k m) (L : ℕ) :
    ((Fin m × Fin L) ⊕ (Fin k × Fin L)) → Finset (Fin k × Fin L)
  | Sum.inl q => (H.edge q.1).image (fun x => (x, q.2))
  | Sum.inr q => if h : q.2.val + 1 < L then {(q.1, q.2), (q.1, ⟨q.2.val + 1, h⟩)} else ∅

@[simp] theorem thickenInc_inl {k m L : ℕ} (H : AuxHypergraph k m) (e : Fin m) (l : Fin L) :
    thickenInc H L (Sum.inl (e, l)) = (H.edge e).image (fun x => (x, l)) := rfl

@[simp] theorem thickenInc_inr {k m L : ℕ} (H : AuxHypergraph k m) (x : Fin k) (i : Fin L) :
    thickenInc H L (Sum.inr (x, i))
      = if h : i.val + 1 < L then {(x, i), (x, ⟨i.val + 1, h⟩)} else ∅ := rfl

theorem thickenInc_inr_of_lt {k m L : ℕ} (H : AuxHypergraph k m) (x : Fin k) (i : Fin L)
    (hi : i.val + 1 < L) :
    thickenInc H L (Sum.inr (x, i)) = {(x, i), (x, ⟨i.val + 1, hi⟩)} := by
  rw [thickenInc_inr, dite_eq_left hi]

theorem thickenInc_inr_of_not_lt {k m L : ℕ} (H : AuxHypergraph k m) (x : Fin k) (i : Fin L)
    (hi : ¬ i.val + 1 < L) : thickenInc H L (Sum.inr (x, i)) = ∅ := by
  rw [thickenInc_inr, dite_eq_right hi]

/-- The "next level" of level `i` (the last level is taken to be itself, so the cut there
is 0). -/
def levelNext {k L : ℕ} (S : Finset (Fin k × Fin L)) (i : Fin L) : Finset (Fin k) :=
  if h : i.val + 1 < L then level S ⟨i.val + 1, h⟩ else level S i

theorem levelNext_of_lt {k L : ℕ} (S : Finset (Fin k × Fin L)) (i : Fin L)
    (hi : i.val + 1 < L) : levelNext S i = level S ⟨i.val + 1, hi⟩ := by
  rw [levelNext, dite_eq_left hi]

theorem levelNext_of_not_lt {k L : ℕ} (S : Finset (Fin k × Fin L)) (i : Fin L)
    (hi : ¬ i.val + 1 < L) : levelNext S i = level S i := by
  rw [levelNext, dite_eq_right hi]

/-- The symmetric difference `A + B` of two vertex sets (F₂ addition). -/
def symmDiffSet {V : Type*} [DecidableEq V] (A B : Finset V) : Finset V :=
  (A \ B) ∪ (B \ A)

/-- The size `|A + B|` of the symmetric difference. -/
def symmDiffCard {V : Type*} [DecidableEq V] (A B : Finset V) : ℕ :=
  (A \ B).card + (B \ A).card

theorem symmDiffCard_eq_card_symmDiffSet {V : Type*} [DecidableEq V] (A B : Finset V) :
    symmDiffCard A B = (symmDiffSet A B).card := by
  rw [symmDiffCard, symmDiffSet, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun x hx hy => by
    rw [Finset.mem_sdiff] at hx hy
    exact hx.2 hy.1)

/-- **The interlevel cut** `|v^i + v^{i+1}|` (the last level is taken to be 0). -/
def levelCut {k L : ℕ} (S : Finset (Fin k × Fin L)) (i : Fin L) : ℕ :=
  (symmDiffSet (level S i) (levelNext S i)).card

/-- The intersection of a 2-element set with `S` has exactly one element ⟺ exactly one
element lies in `S`. -/
theorem odd_card_inter_pair {α : Type*} [DecidableEq α] (S : Finset α) {a b : α} (hab : a ≠ b) :
    Odd ((S ∩ ({a, b} : Finset α)).card) ↔ (a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S) := by
  have hcard : (S ∩ ({a, b} : Finset α)).card
      = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
    have h : S ∩ ({a, b} : Finset α) = ({a, b} : Finset α).filter (fun y => y ∈ S) := by
      ext y
      rw [Finset.mem_inter, Finset.mem_filter]
      exact and_comm
    rw [h, Finset.card_filter, Finset.sum_pair hab]
  rw [hcard]
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · refine iff_of_false ?_ (by simp [ha, hb])
      rw [ite_eq_left ha, ite_eq_left hb]
      decide
    · refine iff_of_true ?_ (by simp [ha, hb])
      rw [ite_eq_left ha, ite_eq_right hb]
      decide
  · by_cases hb : b ∈ S
    · refine iff_of_true ?_ (by simp [ha, hb])
      rw [ite_eq_right ha, ite_eq_left hb]
      decide
    · refine iff_of_false ?_ (by simp [ha, hb])
      rw [ite_eq_right ha, ite_eq_right hb]
      decide

/-- The intersection of a within-level copy with `S`: after projecting back to the `l`th
level it is `level S l ∩ E`. -/
theorem card_inter_levelImage {k L : ℕ} (S : Finset (Fin k × Fin L)) (E : Finset (Fin k))
    (l : Fin L) : (S ∩ E.image (fun x => (x, l))).card = (level S l ∩ E).card := by
  have h1 : S ∩ E.image (fun x => (x, l))
      = (E.filter (fun x => (x, l) ∈ S)).image (fun x => (x, l)) := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_inter, Finset.mem_image] at hp
      obtain ⟨hS, ⟨x, hx, hf⟩⟩ := hp
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hf.symm ▸ hS⟩, hf⟩
    · intro hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hx, hf⟩ := hp
      rw [Finset.mem_filter] at hx
      exact Finset.mem_inter.mpr
        ⟨hf ▸ hx.2, Finset.mem_image.mpr ⟨x, hx.1, hf⟩⟩
  have h2 : (level S l ∩ E) = E.filter (fun x => (x, l) ∈ S) := by
    ext x
    rw [Finset.mem_inter, Finset.mem_filter, mem_level]
    exact and_comm
  rw [h1, h2, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]

/-- **The degree decomposition in the proof of Theorem 7.8** ([14] Appendix C, p. 86):

$$|G_L^{\intercal}v| = \sum_{j=2}^{L}|v^{j-1} + v^{j}| + \sum_{j=1}^{L}|G^{\intercal}v^{j}|.$$ -/
theorem edgeDeg_thicken {k m L : ℕ} (H : AuxHypergraph k m) (S : Finset (Fin k × Fin L)) :
    edgeDegOf (thickenInc H L) S
      = (∑ l : Fin L, edgeDeg H (level S l)) + (∑ i : Fin L, levelCut S i) := by
  rw [edgeDegOf, Finset.card_filter, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [edgeDeg, edgeDegOf, Finset.card_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [thickenInc_inl, card_inter_levelImage]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.val + 1 < L
    · rw [levelCut, levelNext_of_lt S i hi, ← Finset.card_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        thickenInc_inr_of_lt H x i hi]
      have hne : (x, i) ≠ (x, ⟨i.val + 1, hi⟩) := by
        intro hh
        have h2 : i = ⟨i.val + 1, hi⟩ := ((Prod.mk.injEq x i x ⟨i.val + 1, hi⟩).mp hh).2
        have h3 : i.val = i.val + 1 := congrArg Fin.val h2
        omega
      simp only [symmDiffSet, Finset.mem_union, Finset.mem_sdiff, mem_level]
      rw [odd_card_inter_pair S hne]
      tauto
    · rw [levelCut, levelNext_of_not_lt S i hi, ← Finset.card_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        thickenInc_inr_of_not_lt H x i hi, symmDiffSet, Finset.sdiff_self, Finset.union_empty,
        Finset.inter_empty, Finset.card_empty]
      simp

/-! ### The specified family and $\mathcal{U}$ after thickening -/

/-- The specified family on the `l`th level after thickening: move `κ a` to the `l`th level
(the `V^{\ell}_i` of [14] Thm 7.8). -/
def levelFam {k L : ℕ} {ι : Type*} (κ : ι → Finset (Fin k)) (l : Fin L) :
    ι → Finset (Fin k × Fin L) :=
  fun a => (κ a).image (fun x => (x, l))

/-- The `U` on the `l`th level after thickening (the `\mathcal{U}^{\ell}` of [14] Thm 7.8). -/
def levelSet {k L : ℕ} (U : Finset (Fin k)) (l : Fin L) : Finset (Fin k × Fin L) :=
  U.image (fun x => (x, l))

theorem image_sdiff {k L : ℕ} (S : Finset (Fin k × Fin L)) (E : Finset (Fin k))
    (l : Fin L) :
    E.image (fun x => (x, l)) \ S = (E \ level S l).image (fun x => (x, l)) := by
  ext p
  constructor
  · intro hp
    simp only [Finset.mem_sdiff, Finset.mem_image, mem_level] at hp ⊢
    obtain ⟨⟨x, hx, hf⟩, hS⟩ := hp
    exact ⟨x, ⟨hx, fun hxl => hS (hf ▸ hxl)⟩, hf⟩
  · intro hp
    simp only [Finset.mem_sdiff, Finset.mem_image, mem_level] at hp ⊢
    obtain ⟨x, hx, hf⟩ := hp
    exact ⟨⟨x, hx.1, hf⟩, fun hS => hx.2 (hf.symm ▸ hS)⟩

theorem image_inter_sdiff {k L : ℕ} (S : Finset (Fin k × Fin L)) (A B : Finset (Fin k))
    (l : Fin L) :
    (S ∩ A.image (fun x => (x, l))) \ B.image (fun x => (x, l))
      = ((level S l ∩ A) \ B).image (fun x => (x, l)) := by
  ext p
  constructor
  · intro hp
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_image, mem_level] at hp ⊢
    obtain ⟨⟨hSp, ⟨x, hx, hf⟩⟩, hB⟩ := hp
    exact ⟨x, ⟨⟨hf ▸ hSp, hx⟩, fun hxb => hB ⟨x, hxb, hf⟩⟩, hf⟩
  · intro hp
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_image, mem_level] at hp ⊢
    obtain ⟨x, ⟨⟨hxl, hx⟩, hxB⟩, hf⟩ := hp
    refine ⟨⟨hf.symm ▸ hxl, ⟨x, hx, hf⟩⟩, fun h => ?_⟩
    obtain ⟨y, hy, hyx⟩ := h
    exact hxB (((Prod.mk.injEq y l x l).mp (hyx.trans hf.symm)).1 ▸ hy)

/-- **After thickening lifts the `κ` family to the `l`th level, the argument of Def 7.2
is unchanged word for word**. -/
theorem modExpArg_level {k L : ℕ} {ι : Type*} (κ : ι → Finset (Fin k)) (U : Finset (Fin k))
    (l : Fin L) (S : Finset (Fin k × Fin L)) (a : ι) :
    modExpArgOf (levelFam κ l a) (levelSet U l) S = modExpArgOf (κ a) U (level S l) := by
  rw [modExpArgOf, modExpArgOf, levelFam, levelSet, image_sdiff, image_inter_sdiff,
    Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_image_of_injective _ (fun x y h => by simpa using h)]

theorem modExpMin_eq_of_forall_eq {V₁ V₂ ι : Type*} [DecidableEq V₁] [DecidableEq V₂]
    [Fintype ι] [Nonempty ι] (f : ι → Finset V₁) (g : ι → Finset V₂)
    (U₁ : Finset V₁) (U₂ : Finset V₂) (S₁ : Finset V₁) (S₂ : Finset V₂)
    (h : ∀ a, modExpArgOf (f a) U₁ S₁ = modExpArgOf (g a) U₂ S₂) :
    modExpMin f U₁ S₁ = modExpMin g U₂ S₂ := by
  unfold modExpMin
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' Finset.univ_nonempty (fun a => modExpArgOf (g a) U₂ S₂)
      (fun b _ => ?_)
    exact (Finset.inf'_le (fun a => modExpArgOf (f a) U₁ S₁)
      (Finset.mem_univ b)).trans_eq (h b)
  · refine Finset.le_inf' Finset.univ_nonempty (fun a => modExpArgOf (f a) U₁ S₁)
      (fun b _ => ?_)
    exact (Finset.inf'_le (fun a => modExpArgOf (g a) U₂ S₂)
      (Finset.mem_univ b)).trans_eq (h b).symm

/-- **The modular-expansion quantity on the `l`th level after thickening is that level's
`modExpMin`**. -/
theorem modExpMin_level {k L : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (κ : ι → Finset (Fin k)) (U : Finset (Fin k)) (l : Fin L) (S : Finset (Fin k × Fin L)) :
    modExpMin (levelFam κ l) (levelSet U l) S = modExpMin κ U (level S l) :=
  modExpMin_eq_of_forall_eq (levelFam κ l) κ (levelSet U l) U S (level S l)
    (fun a => modExpArg_level κ U l S a)

/-! ### The path triangle inequality (the "use the triangle inequality" step in the proof
of [14] Thm 7.8) -/

/-- Monotonicity along the level chain: if `x` has the same membership on every pair of
adjacent levels, it has the same membership on the whole chain (by `Nat` induction on the
level index). -/
theorem level_mono_of_iff {k L : ℕ} {S : Finset (Fin k × Fin L)} {x : Fin k}
    (hstep : ∀ (i : Fin L) (hi : i.val + 1 < L),
      (x ∈ level S i ↔ x ∈ level S ⟨i.val + 1, hi⟩)) :
    ∀ a b : Fin L, a ≤ b → (x ∈ level S a ↔ x ∈ level S b) := by
  intro a b hab
  have key : ∀ t : ℕ, ∀ (ht : t < L), a.val ≤ t →
      (x ∈ level S a ↔ x ∈ level S ⟨t, ht⟩) := by
    intro t
    induction t with
    | zero =>
        intro ht hle
        rw [show a = (⟨0, ht⟩ : Fin L) from Fin.ext (Nat.eq_zero_of_le_zero hle)]
    | succ k ih =>
        intro ht hle
        by_cases hk : a.val ≤ k
        · exact (ih (by omega) hk).trans (hstep ⟨k, by omega⟩ (by omega))
        · have hlast : a.val = k + 1 := by omega
          rw [show a = (⟨k + 1, ht⟩ : Fin L) from Fin.ext hlast]
  exact key b.val b.isLt hab

/-- **The path triangle inequality**: the sum of all interlevel cuts ≥ the symmetric
difference between any two levels (the step in the proof of [14] Thm 7.8 that bounds
`|v^r + v^{\ell}|` by the sum of all cuts). -/
theorem symmDiffCard_level_le_sum_levelCut {k L : ℕ} (S : Finset (Fin k × Fin L))
    (a b : Fin L) :
    symmDiffCard (level S a) (level S b) ≤ ∑ i : Fin L, levelCut S i := by
  -- if `x` is in the symmetric difference, some adjacent pair of levels separates it
  have hkey : ∀ x : Fin k, x ∈ symmDiffSet (level S a) (level S b) →
      ∃ i : Fin L, x ∈ symmDiffSet (level S i) (levelNext S i) := by
    intro x hx
    by_contra hcon
    simp only [symmDiffSet, Finset.mem_union, Finset.mem_sdiff] at hx
    push Not at hcon
    have hstep : ∀ (i : Fin L) (hi : i.val + 1 < L),
        (x ∈ level S i ↔ x ∈ level S ⟨i.val + 1, hi⟩) := by
      intro i hi
      have hnc := hcon i
      rw [levelNext_of_lt S i hi] at hnc
      simp only [symmDiffSet, Finset.mem_union, Finset.mem_sdiff] at hnc
      constructor
      · intro hxi
        by_contra hxj
        exact hnc (Or.inl ⟨hxi, hxj⟩)
      · intro hxj
        by_contra hxi
        exact hnc (Or.inr ⟨hxj, hxi⟩)
    have hiff : x ∈ level S a ↔ x ∈ level S b := by
      rcases le_total a b with hab | hba
      · exact level_mono_of_iff hstep a b hab
      · exact (level_mono_of_iff hstep b a hba).symm
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.mp h1)
    · exact h2 (hiff.mpr h1)
  have hsub : symmDiffSet (level S a) (level S b)
      ⊆ Finset.univ.biUnion (fun i : Fin L => symmDiffSet (level S i) (levelNext S i)) := by
    intro x hx
    obtain ⟨i, hi⟩ := hkey x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
  calc symmDiffCard (level S a) (level S b)
      = (symmDiffSet (level S a) (level S b)).card := symmDiffCard_eq_card_symmDiffSet _ _
    _ ≤ (Finset.univ.biUnion (fun i : Fin L => symmDiffSet (level S i) (levelNext S i))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin L, (symmDiffSet (level S i) (levelNext S i)).card := Finset.card_biUnion_le
    _ = ∑ i : Fin L, levelCut S i := rfl

/-! ### The counting lemma (the Venn-count step in the proof of [14] Thm 7.7, set side) -/

theorem min_le_min_left' {α : Type*} [LinearOrder α] {a b c : α} (h : b ≤ c) :
    min a b ≤ min a c :=
  le_min (min_le_left a b) (le_trans (min_le_right a b) h)

/-- Taking subsets never increases the symmetric difference: `|(A∩U) + (B∩U)| ≤ |A + B|`. -/
theorem symmDiffCard_inter_le {V : Type*} [DecidableEq V] (A B U : Finset V) :
    symmDiffCard (A ∩ U) (B ∩ U) ≤ symmDiffCard A B := by
  rw [symmDiffCard, symmDiffCard]
  refine Nat.add_le_add ?_ ?_ <;> refine Finset.card_le_card ?_ <;> intro x hx <;>
    rw [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_inter] at hx
  · exact Finset.mem_sdiff.mpr ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩
  · exact Finset.mem_sdiff.mpr ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩

/-- **The set-theoretic inequality of the Venn-count step in the proof of [14] Thm 7.7**
(for `κ ⊆ U`):
$$\mathrm{arg}(\kappa,B) \leq \mathrm{arg}(\kappa,A) + |(A\cap U) + (B\cap U)|.$$

This corresponds to the source's line
"`|\kappa_\lambda| - |v\cap\kappa_\lambda| + |v\cap\mathcal{U}\backslash
\kappa_\lambda| = |\varphi_\lambda| + |\sigma_\lambda| + |B'_\lambda| + |\gamma_\lambda|`"
(this module keeps only its set-theoretic core: the difference of the two sides is bounded
by the symmetric difference). -/
theorem modExpArgOf_le_add_symmDiffCard {V : Type*} [DecidableEq V] (κ U A B : Finset V)
    (hκU : κ ⊆ U) :
    modExpArgOf κ U B ≤ modExpArgOf κ U A + symmDiffCard (A ∩ U) (B ∩ U) := by
  have h1 : (κ \ B).card ≤ (κ \ A).card + ((A ∩ U) \ (B ∩ U)).card := by
    have hsub : κ \ B ⊆ (κ \ A) ∪ ((A ∩ U) \ (B ∩ U)) := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at hx ⊢
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨⟨hxA, hκU hx.1⟩, fun h => hx.2 h.1⟩
      · exact Or.inl ⟨hx.1, hxA⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h2 : ((B ∩ U) \ κ).card ≤ ((A ∩ U) \ κ).card + ((B ∩ U) \ (A ∩ U)).card := by
    have hsub : (B ∩ U) \ κ ⊆ ((A ∩ U) \ κ) ∪ ((B ∩ U) \ (A ∩ U)) := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at hx ⊢
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨⟨hxA, hx.1.2⟩, hx.2⟩
      · exact Or.inr ⟨hx.1, fun h => hxA h.1⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [modExpArgOf, modExpArgOf, symmDiffCard]
  omega

/-! ### The conclusion of Theorem 7.8: thickening raises the modular expansion to 1 -/

/-- **[14] Theorem 7.8 (thickening)**: if `H` has modular expansion constant `M` (with
parameter `t`) and `M · L ≥ 1`, then the hypergraph thickened `L` times has modular
expansion `≥ 1` at **every** level `l` (the specified family = the copy of `κ` on the `l`th
level, `U` = the copy of `U` on the `l`th level).

The proof is the three steps of Appendix C: the degree decomposition (`edgeDeg_thicken`) →
bound `|v^r + v^{\ell}|` using `M·L ≥ 1` and the path triangle inequality
(`symmDiffCard_level_le_sum_levelCut`) → complete the Venn count with
`modExpArgOf_le_add_symmDiffCard`. -/
theorem modularExpansion_thicken {k m L : ℕ} (H : AuxHypergraph k m) {ι : Type*}
    [Fintype ι] [Nonempty ι] (κ : ι → Finset (Fin k)) (U : Finset (Fin k)) {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hML : 1 ≤ M * (L : ℝ)) (hL : 1 ≤ L) (l : Fin L)
    (hκU : ∀ a, κ a ⊆ U) (h : HasModularExpansion H.edge κ U t M) :
    HasModularExpansion (thickenInc H L) (levelFam κ l) (levelSet U l) t 1 := by
  intro S
  rw [modExpMin_level]
  obtain ⟨r, -, hr⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin L))
    (fun j => modExpMin κ U (level S j)) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image (Finset.univ : Finset ι)
    (fun a => modExpArgOf (κ a) U (level S r)) Finset.univ_nonempty
  -- notation: `mr` = the minimal expansion quantity of level `r`, `cr` = its real value
  -- after truncating by the parameter `t`
  have hmr_eq : modExpMin κ U (level S r) = modExpArgOf (κ a₀) U (level S r) := by
    refine le_antisymm ?_ ?_
    · rw [modExpMin]; exact Finset.inf'_le _ (Finset.mem_univ a₀)
    · rw [modExpMin]; exact Finset.le_inf' _ _ (fun b _ => ha₀ b (Finset.mem_univ b))
  have hcr_nonneg : (0 : ℝ) ≤ min t ((modExpMin κ U (level S r) : ℕ) : ℝ) := by
    exact le_min ht.le (by positivity)
  -- lower bound for the first term (the within-level copies)
  have hA : (L : ℝ) * (M * min t ((modExpMin κ U (level S r) : ℕ) : ℝ))
      ≤ ((∑ j : Fin L, edgeDeg H (level S j) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine le_trans ?_ (Finset.sum_le_sum (fun j _ => h (level S j)))
    rw [show (L : ℝ) * (M * min t ((modExpMin κ U (level S r) : ℕ) : ℝ))
        = ∑ _j : Fin L, M * min t ((modExpMin κ U (level S r) : ℕ) : ℝ) from by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
      (min_le_min_left' (by exact_mod_cast hr j (Finset.mem_univ j))) hM)
  -- lower bound for the second term (the interlevel cuts)
  have hC : ((symmDiffCard (level S r) (level S l) : ℕ) : ℝ)
      ≤ ((∑ i : Fin L, levelCut S i : ℕ) : ℝ) := by
    exact_mod_cast symmDiffCard_level_le_sum_levelCut S r l
  have hD : (edgeDegOf (thickenInc H L) S : ℝ)
      = ((∑ j : Fin L, edgeDeg H (level S j) : ℕ) : ℝ)
        + ((∑ i : Fin L, levelCut S i : ℕ) : ℝ) := by
    rw [edgeDeg_thicken, Nat.cast_add]
  -- `min t mr` itself is bounded by the first term (using `M·L ≥ 1`)
  have hcr_le_A : min t ((modExpMin κ U (level S r) : ℕ) : ℝ)
      ≤ ((∑ j : Fin L, edgeDeg H (level S j) : ℕ) : ℝ) := by
    refine le_trans ?_ hA
    have h1 := mul_le_mul_of_nonneg_right hML hcr_nonneg
    rw [one_mul] at h1
    have h2 : (M * (L : ℝ)) * min t ((modExpMin κ U (level S r) : ℕ) : ℝ)
        = (L : ℝ) * (M * min t ((modExpMin κ U (level S r) : ℕ) : ℝ)) := by ring
    rw [h2] at h1
    exact h1
  by_cases hcase : t ≤ min t ((modExpMin κ U (level S r) : ℕ) : ℝ)
  · -- case 1: the `min` of level `r` takes the parameter `t`
    have hcr : min t ((modExpMin κ U (level S r) : ℕ) : ℝ) = t :=
      le_antisymm (min_le_left _ _) hcase
    have hgoal : min t ((modExpMin κ U (level S l) : ℕ) : ℝ)
        ≤ (edgeDegOf (thickenInc H L) S : ℝ) := by
      calc min t ((modExpMin κ U (level S l) : ℕ) : ℝ)
          ≤ t := min_le_left _ _
        _ = min t ((modExpMin κ U (level S r) : ℕ) : ℝ) := hcr.symm
        _ ≤ (edgeDegOf (thickenInc H L) S : ℝ) := by
              rw [hD]
              exact le_trans hcr_le_A (le_add_of_nonneg_right (by positivity))
    calc 1 * min t ((modExpMin κ U (level S l) : ℕ) : ℝ)
        = min t ((modExpMin κ U (level S l) : ℕ) : ℝ) := one_mul _
      _ ≤ (edgeDegOf (thickenInc H L) S : ℝ) := hgoal
  · -- case 2: the `min` of level `r` takes the expression in `κ`
    have hcr : min t ((modExpMin κ U (level S r) : ℕ) : ℝ)
        = ((modExpMin κ U (level S r) : ℕ) : ℝ) := by
      have hXt : ¬ (t ≤ ((modExpMin κ U (level S r) : ℕ) : ℝ)) :=
        fun hle => hcase (by rw [min_eq_left hle])
      rw [min_def, ite_eq_right hXt]
    -- `m_l ≤ m_r + |Δ|`
    have hml : modExpMin κ U (level S l)
        ≤ modExpMin κ U (level S r) + symmDiffCard (level S r) (level S l) := by
      have h1 : modExpMin κ U (level S l) ≤ modExpArgOf (κ a₀) U (level S l) := by
        rw [modExpMin]; exact Finset.inf'_le _ (Finset.mem_univ a₀)
      have h2 : modExpArgOf (κ a₀) U (level S l)
          ≤ modExpArgOf (κ a₀) U (level S r)
            + symmDiffCard (level S r ∩ U) (level S l ∩ U) :=
        modExpArgOf_le_add_symmDiffCard (κ a₀) U (level S r) (level S l) (hκU a₀)
      refine le_trans h1 ?_
      rw [hmr_eq]
      exact le_trans h2 (Nat.add_le_add_left (symmDiffCard_inter_le _ _ U) _)
    have hgoal : min t ((modExpMin κ U (level S l) : ℕ) : ℝ)
        ≤ (edgeDegOf (thickenInc H L) S : ℝ) := by
      have hcast : min t ((modExpMin κ U (level S l) : ℕ) : ℝ)
          ≤ ((modExpMin κ U (level S r) : ℕ) : ℝ)
            + ((symmDiffCard (level S r) (level S l) : ℕ) : ℝ) := by
        refine le_trans (min_le_right _ _) ?_
        rw [← Nat.cast_add]
        exact_mod_cast hml
      rw [hD]
      refine le_trans hcast (add_le_add ?_ hC)
      rw [← hcr]
      exact hcr_le_A
    calc 1 * min t ((modExpMin κ U (level S l) : ℕ) : ℝ)
        = min t ((modExpMin κ U (level S l) : ℕ) : ℝ) := one_mul _
      _ ≤ (edgeDegOf (thickenInc H L) S : ℝ) := hgoal

/-! ### Corollary 7.10: when `ker ⊆ W`, thickening `d` times suffices -/

/-- **The hypothesis consumed by [14] Thm 7.7 / 7.12 / 7.15**:
$\mathcal{M}_d(\mathcal{H}) \geq 1$. -/
def PreservesDistance {V E ι : Type*} [Fintype E] [DecidableEq V] [Fintype ι] [Nonempty ι]
    (inc : E → Finset V) (κ : ι → Finset V) (U : Finset V) (d : ℕ) : Prop :=
  HasModularExpansion inc κ U (d : ℝ) 1

/-- **[14] Corollary 7.10 (constructive version)**: if every element of
$\ker(G^{\intercal})$ is some $\kappa_\lambda$ (the hypothesis of Lemma 7.9), then after
**thickening `d` times** one gets $\mathcal{M}_d \geq 1$ at every level — that is, the
hypothesis required by `Thm 7.7` is **constructively satisfiable**
([14] p. 39: "the conditions of Theorem 4.5 can be satisfied constructively,
by choosing subcodes of distance `d` and then thickening"). -/
theorem preservesDistance_of_thicken {k m : ℕ} (H : AuxHypergraph k m) {ι : Type*}
    [Fintype ι] [Nonempty ι] (κ : ι → Finset (Fin k)) (U : Finset (Fin k))
    (hκU : ∀ a, κ a ⊆ U) {d : ℕ} (hd : 1 ≤ d)
    (hker : ∀ S : Finset (Fin k), edgeDeg H S = 0 → ∃ a : ι, κ a = S)
    (L : ℕ) (hL : d ≤ L) (l : Fin L) :
    PreservesDistance (thickenInc H L) (levelFam κ l) (levelSet U l) d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hL1 : 1 ≤ L := le_trans hd hL
  have hML : 1 ≤ (1 / (d : ℝ)) * (L : ℝ) := by
    have h2 : (1 / (d : ℝ)) * (L : ℝ) = (L : ℝ) / (d : ℝ) := by ring
    rw [h2, le_div_iff₀ hdpos]
    simpa using (by exact_mod_cast hL : (d : ℝ) ≤ (L : ℝ))
  exact modularExpansion_thicken H κ U hdpos (by positivity) hML hL1 l hκU
    (modularExpansion_inv_of_component_mem H.edge κ U hdpos (fun S hS => hker S hS))

/-! ## 5. The interface with the existing layer

Connect the new quantity of §1 to the existing `IsComponent` / `starOp` / `graphOf` layer of
`Homology/HypergraphSurgery.lean`, so that the expansion conditions of [14] §7 and the
existing Gauss laws, components and 2-regular reduction say the same thing. -/

/-- **$|G^{\intercal}\mathcal{V}| = 0$ ⟺ the Gauss-law product = the vertex-operator
product**: for $S = \mathcal{V}$, the $|G^{\intercal}S| = 0$ of §1 is exactly `IsEvenHyper`,
and the latter is precisely the **necessary and sufficient** condition for the existing
lifting identity `starOp_sum_eq_vertexOp_sum` (`starOp_sum_eq_vertexOp_sum_iff`). -/
theorem edgeDeg_univ_eq_zero_iff_starOp_sum_eq {k m : ℕ} (H : AuxHypergraph k m) :
    edgeDeg H Finset.univ = 0 ↔
      (∑ v : Fin k, starOp H v) = ∑ v : Fin k, vertexOp (k := k) (m := m) v := by
  rw [edgeDeg_eq_zero_iff_isComponent, component_univ_iff_even, starOp_sum_eq_vertexOp_sum_iff]

/-- On an even hypergraph $|G^{\intercal}\mathcal{V}| = 0$ (that is, it holds automatically
in the 2-regular case). -/
theorem edgeDeg_univ_eq_zero_of_isEvenHyper {k m : ℕ} {H : AuxHypergraph k m}
    (h : IsEvenHyper H) : edgeDeg H Finset.univ = 0 :=
  (edgeDeg_eq_zero_iff_isComponent H _).mpr ((component_univ_iff_even H).mpr h)

/-- **The 2-regular (graph) case: $|G^{\intercal}S|$ is the edge boundary of the graph** —
the number of edges with exactly one endpoint in `S`. This is both the graph-theoretic form
of the quantity in Def 7.3 (global expansion) and connects the new quantity of §1 to the
existing `Gauging.graphOf` convention. -/
theorem edgeDeg_graphOf {k m : ℕ} (ends : Fin m → Fin k × Fin k)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (S : Finset (Fin k)) :
    edgeDeg (graphOf ends) S
      = (Finset.univ.filter (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S)
          ∨ ((ends e).1 ∉ S ∧ (ends e).2 ∈ S))).card := by
  rw [edgeDeg, edgeDegOf, Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [graphOf_edge]
  by_cases h : Odd ((S ∩ ({(ends e).1, (ends e).2} : Finset (Fin k))).card)
  · rw [ite_eq_left h, ite_eq_left ((odd_card_inter_pair S (hloop e)).mp h)]
  · rw [ite_eq_right h,
      ite_eq_right (fun hc => h ((odd_card_inter_pair S (hloop e)).mpr hc))]

end QECCertificates.Homology
