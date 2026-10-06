/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.MappingCone

open QECCertificates

/-!
# The Snake dimension formula: the deferred item of `Homology/MappingCone.lean`

`Homology/MappingCone.lean` delivers the mapping cone (the cone is a complex, the short exact
sequence is exact, the connecting homomorphism is `F`), but the **dimension formula** of the
Snake long exact sequence of [14] Appendix A.1 (p. 60) is not there — item 6 of that module
header's honest boundaries and the division of labour at the end of §5 state that the missing
step is **the induced map on the quotient space**. This module supplies it.

## 1. The text of [14] p. 60 and the index convention (align first, then prove)

The source (`refs/Fast and fault-tolerant logical measurements - Auxiliary hypergraphs and
transversal surgery.pdf`, p. 60):

> The Snake Lemma [90, Lem. 1.3.2] and rank-nullity together imply that for a mapping cone
> $\mathrm{cone}(f^\bullet)$ defined by a chain map $f^\bullet : A^\bullet \to C^\bullet$, we have
> $|H_i(\mathrm{cone}(f^\bullet))| = |H_i(C^\bullet)| + |H_{i-1}(A^\bullet)|
> - |\mathrm{im}\,H_i(f^\bullet)| - |\mathrm{im}\,H_{i-1}(f^\bullet)|$,
> where $|V|$ is shorthand for $\dim V$ when $V$ is a vector space.

**The index conventions must be aligned, or copying it down yields a false proposition.** The
source uses **homological** indices (the smaller $i$, the earlier), assembling the cone as
$\mathrm{cone}(f)_i = C_i \oplus A_{i-1}$; this library (`Cochain4` / `coneD*`) uses
**cochain** indices, assembling the cone as $\mathrm{cone}(F)^n = D^n \oplus C^{n+1}$, with
$F : C \to D$ playing the role of the source's $f : A \to C$ (that is, the $D$ of this library
is the $C$ of the source). Putting $i = -n$ turns the source's $H_{i-1}(A)$ into $H^{n+1}(C)$,
so the form in this library is

$$\dim H^n(\mathrm{cone}(F)) = \dim H^n(D) + \dim H^{n+1}(C)
  - \dim \mathrm{im}\,H^n(F) - \dim \mathrm{im}\,H^{n+1}(F).$$

**This is what this module proves** (§4's `finrank_coh0_mappingCone` …
`finrank_coh3_mappingCone`).

## 2. The derivation (written out first, then proved)

### 2.1 The long exact sequence route (the textbook writing, as a cross-check)

The short exact sequence
$0 \to D^n \xrightarrow{\iota} \mathrm{cone}^n \xrightarrow{\pi} C^{n+1} \to 0$ gives the
long exact sequence

$$\cdots \to H^n(D) \xrightarrow{\alpha_n} H^n(\mathrm{cone})
  \xrightarrow{\beta_n} H^{n+1}(C) \xrightarrow{\delta_n} H^{n+1}(D) \to \cdots$$

in which $\delta_n$ is exactly $H^{n+1}(F)$ — precisely what the previous module's
`connectingMap_coneD0` / `connectingMap_coneD1` state as "the connecting homomorphism is
induced by $F$". Taking dimensions at $H^n(\mathrm{cone})$ by exactness:

$$\dim H^n(\mathrm{cone}) = \dim \ker\beta_n + \dim \mathrm{im}\,\beta_n
  = \dim \mathrm{im}\,\alpha_n + \dim \ker\delta_n,$$

then using $\dim \mathrm{im}\,\alpha_n = \dim H^n(D) - \dim \mathrm{im}\,\delta_{n-1}$
(exactness at $H^n(D)$) and $\dim \ker\delta_n = \dim H^{n+1}(C) - \dim \mathrm{im}\,\delta_n$
(rank-nullity) gives it.

**This route requires formalizing three exactness statements one by one (diagram chasing)**;
this module does not take it.

### 2.2 The route this module actually takes: a fibre computation + rank-nullity (no exactness)

Write $Z^n = \ker d_n$, $B^n = \mathrm{im}\,d_{n-1}$ (endpoints by the truncation convention
$B^0 = 0$, $Z^3 = \top$) and $H^n = Z^n/B^n$. The differential of the cone is
block-triangular

$$d^n_{\mathrm{cone}} = \begin{pmatrix} d^n_D & F_{n+1} \\ 0 & -d^{n+1}_C\end{pmatrix}
: D^n \oplus C^{n+1} \longrightarrow D^{n+1} \oplus C^{n+2}.$$

**Step one (the fibre computation of the kernel, `finrank_ker_blockTri`)**: the equations
$d^n_D x + F_{n+1} y = 0$ and $d^{n+1}_C y = 0$ show that the set of values of the second
component is

$$S_n := Z^{n+1}(C) \cap F_{n+1}^{-1}\bigl(B^{n+1}(D)\bigr)
  \qquad(\text{$y$ is a cycle, and $F_{n+1} y$ is a boundary}),$$

and for each $y \in S_n$ the fibre of $x$ is a nonempty coset of $\ker d^n_D$, so

$$\dim Z^n(\mathrm{cone}) = \dim Z^n(D) + \dim S_n. \tag{F}$$

**Step two (rewriting $S_n$ through the induced map on the quotient,
`finrank_inf_comap_add_finrank_range_cohMap`)**: the kernel of
$\varphi_{n+1} : Z^{n+1}(C) \to H^{n+1}(D)$, $y \mapsto [F_{n+1} y]$, is exactly $S_n$ and
its image is exactly $\mathrm{im}\,H^{n+1}(F)$; rank-nullity for $\varphi_{n+1}$ gives

$$\dim S_n + \dim \mathrm{im}\,H^{n+1}(F) = \dim Z^{n+1}(C). \tag{S}$$

**Step three (the boundary)**: $B^n(\mathrm{cone}) = \mathrm{im}\,d^{n-1}_{\mathrm{cone}}$,
and rank-nullity gives

$$\dim B^n(\mathrm{cone}) = \dim \mathrm{cone}^{n-1} - \dim Z^{n-1}(\mathrm{cone})
  = \bigl(\dim D^{n-1} + \dim C^n\bigr) - \dim Z^{n-1}(D) - \dim S_{n-1}, \tag{B}$$

the last step using (F) at $n-1$, while $\dim \mathrm{cone}^{n-1} = \dim D^{n-1} + \dim C^n$
is the previous module's `finrank_cone0..3` (for $n = 0$, $\mathrm{cone}^{-1} = C_0$, the
same set of formulas).

**Step four (algebra)**: with
$\dim H^n(\mathrm{cone}) = \dim Z^n(\mathrm{cone}) - \dim B^n(\mathrm{cone})$, substituting
(F)(B)(S) and the three rank-nullity identities
($\dim B^n(D) = \dim D^{n-1} - \dim Z^{n-1}(D)$,
$\dim H^n(D) = \dim Z^n(D) - \dim B^n(D)$,
$\dim B^{n+1}(C) = \dim C^n - \dim Z^n(C)$) gives it. The four main theorems of §4 write the
divisibility identities above one by one as a **subtraction-free form** that `omega` can
read, then close.

## 3. What this module does

* **§1, general helpers**: negation does not change the kernel, `comap` to a subtype has the
  same dimension, plus the **fibre computation** `finrank_ker_blockTri`, plus the **induced
  map on the quotient** `cyclesMap` / `cohMap` (via `Submodule.mapQ`) / `cohLift`, with its
  **well-definedness** ($F$ sends cycles to cycles and boundaries to boundaries, given by the
  commuting squares of $F_{m+1}$ and $F_{m-1}$ respectively), the equality of images
  `range_cohLift_eq_range_cohMap`, and the **dimension bridge**
  `finrank_inf_comap_add_finrank_range_cohMap` (that is, (S)).
* **§2, cohomology (degrees $0$–$3$)**: the two truncations at the endpoints `bounds0`
  ($B^0 = 0$), `cycles3` ($Z^3 = \top$), the four cohomologies `coh0..coh3`, and the four
  components of $F$, `cohMap0..cohMap3` ($H^m(C) \to H^m(D)$).
* **§3, the terms of the cone**: $S_{-1}, S_0, S_1, S_2$ and the four instances of (F) and
  the four instances of (S), together with the dimensions of the boundaries/cohomology of the
  cone at the endpoints, and the three rank-nullity identities.
* **§4, the main theorems**: the four formulas for $n = 0,1,2,3$ (each with a
  subtraction-free form).

## 4. Honest boundaries (the paper cites this section)

1. **Covers the four degrees $n = 0,1,2,3$**, that is, all degrees of the four-term complex
   ($\mathrm{cone}^{-1} = C_0$ and $\mathrm{cone}^3 = D_3$). The degrees $n = -1, 4$ are not
   among them: under truncation the term $H^{-1}(D)$ and the term $H^4(C)$ are zero, so in
   the $n = 3$ case the two terms $H^4(C)$ and $\mathrm{im}\,H^4(F)$ vanish directly, and
   this module writes $n = 3$ as $\dim H^3(D) - \dim \mathrm{im}\,H^3(F)$ and points out the
   two vanishing terms in its docstring. If the complex is lengthened to five terms, what is
   needed is still the same machinery (fibre computation + induced map + dimension bridge),
   with no new obstacle of principle.
2. **Still not done**: the instantiation of the fault complex on a concrete hypergraph, a
   conclusion about the phenomenological fault distance $d$, the modular expansion /
   thickening of §7 / [14] Thm 7.7 / 7.8 — these are the boundaries of items 1, 2, 5 of §4 of
   `Homology/MappingCone.lean`, and this module **does not** touch them (it closes only the
   one deferred item, item 6 of that module's §4). This module also gives no distance
   reading: item 2 of Section 5 of `the gauged-measurement companion development's `SurgerySchedule` module`, "the static distance of this
   library and the $1$-cosystolic distance of [14] are two different quantities", holds here
   as well.
3. **The derivation takes "the fibre computation + rank-nullity", not the diagram chase of
   the long exact sequence** (§2.2). Hence this module does **not** formalize "the long exact
   sequence is exact"; it formalizes only its **dimension corollary** — which is exactly the
   one used in [14] p. 60; the route of §2.1 is written in the docstring as a cross-check.

**Trusted base**: this module uses no `sorry` / `admit` / `native_decide` and introduces no
custom axiom; the `#print axioms` output for the load-bearing theorems is in the audit region
at the end of the root module `QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open scoped BigOperators

open _root_.Matrix

variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
variable [Fintype C₀] [Fintype C₁] [Fintype C₂] [Fintype C₃]
variable [Fintype D₀] [Fintype D₁] [Fintype D₂] [Fintype D₃]

/-! ## 1. General helpers -/

/-! ### 1.1 Three small blocks -/

/-- Over characteristic $2$, negation does not change a function. -/
theorem neg_eq_self_fun {ι : Type*} (v : ι → ZMod 2) : -v = v := by
  funext i
  exact ZMod.neg_eq_self_mod_two (v i)

/-- Over characteristic $2$, a function added to itself is zero (pointwise via
`CharTwo.add_self_eq_zero`; the function space itself yields no `CharP` instance, hence the
pointwise proof). -/
theorem add_self_eq_zero_fun {ι : Type*} (v : ι → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

/-- Negation does not change the kernel (used on the $-d^C$ in the cone's differentials). -/
theorem ker_mulVecLin_neg {m n : Type*} [Fintype n] (M : Matrix m n (ZMod 2)) :
    LinearMap.ker (-M).mulVecLin = LinearMap.ker M.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.neg_mulVec, neg_eq_zero]

/-- A submodule `comap`-ed to a subtype has the same dimension as the intersection. -/
theorem finrank_comap_subtype {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p q : Submodule R M) :
    Module.finrank R ↥(Submodule.comap q.subtype p) = Module.finrank R ↥(p ⊓ q) := by
  have h : Submodule.comap q.subtype p = Submodule.comap q.subtype (p ⊓ q) := by
    ext x
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  rw [h]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq

/-- Equal submodules have the same dimension (this avoids instance-transport problems from
`rw` inside `↥(·)`). -/
theorem finrank_submodule_congr {K M : Type*} [Ring K] [AddCommGroup M] [Module K M]
    {p q : Submodule K M} (h : p = q) : Module.finrank K ↥p = Module.finrank K ↥q :=
  (LinearEquiv.ofEq p q h).finrank_eq

/-! ### 1.2 The fibre computation: the kernel dimension of a block-triangular matrix -/

/-- The block-triangular matrix $\begin{pmatrix} A & B \\ 0 & D\end{pmatrix}$ (rows
$Q \oplus S$, columns $P \oplus R$). -/
def blockTri {P R Q S : Type*} [Fintype P] [Fintype R] [Fintype Q] [Fintype S]
    (A : Matrix Q P (ZMod 2)) (B : Matrix Q R (ZMod 2))
    (Dd : Matrix S R (ZMod 2)) : Matrix (Q ⊕ S) (P ⊕ R) (ZMod 2) :=
  Matrix.fromBlocks A B 0 Dd

/-- The second summand of the fibre computation, $W = \ker D \sqcap B^{-1}(\mathrm{im}\,A)$. -/
def blockW {P R Q S : Type*} [Fintype P] [Fintype R] [Fintype Q] [Fintype S]
    (A : Matrix Q P (ZMod 2)) (B : Matrix Q R (ZMod 2))
    (Dd : Matrix S R (ZMod 2)) : Submodule (ZMod 2) (R → ZMod 2) :=
  (LinearMap.ker Dd.mulVecLin) ⊓ (LinearMap.range A.mulVecLin).comap B.mulVecLin

/-- The composite of `Sum.elim` on the left component. -/
theorem sumElim_comp_inl {P R : Type*} (x : P → ZMod 2) (y : R → ZMod 2) :
    (Sum.elim x y) ∘ Sum.inl = x := rfl

/-- The composite of `Sum.elim` on the right component. -/
theorem sumElim_comp_inr {P R : Type*} (x : P → ZMod 2) (y : R → ZMod 2) :
    (Sum.elim x y) ∘ Sum.inr = y := rfl

/-- The first component of `inclLin d`. -/
theorem inclLin_comp_inl {A B : Type*} [Fintype A] [Fintype B] (d : A → ZMod 2) :
    (inclLin A B d) ∘ Sum.inl = d := rfl

/-- The second component of `inclLin d` is identically zero. -/
theorem inclLin_comp_inr {A B : Type*} [Fintype A] [Fintype B] (d : A → ZMod 2) :
    (inclLin A B d) ∘ Sum.inr = (0 : B → ZMod 2) := rfl

/-- `projLin` is just taking the second component. -/
theorem projLin_eq_comp_inr {A B : Type*} [Fintype A] [Fintype B] (x : A ⊕ B → ZMod 2) :
    projLin A B x = x ∘ Sum.inr := rfl

/-- **The fibre computation (the kernel dimension of a block-triangular matrix)**:
$A : \mathbb F_2^P \to \mathbb F_2^Q$, $B : \mathbb F_2^R \to \mathbb F_2^Q$,
$D : \mathbb F_2^R \to \mathbb F_2^S$; then

$$\dim \ker \begin{pmatrix} A & B \\ 0 & D\end{pmatrix}
  = \dim \ker A + \dim \bigl(\ker D \cap \{\,y : B y \in \mathrm{im}\,A\,\}\bigr).$$

Proof: projecting $z \in \ker$ to its second component gives a linear map $\pi$ whose image
is exactly the second term on the right and whose kernel is isomorphic to $\ker A$ (via the
first component of $z$); rank-nullity for $\pi$ then gives it. -/
theorem finrank_ker_blockTri {P R Q S : Type*}
    [Fintype P] [Fintype R] [Fintype Q] [Fintype S]
    (A : Matrix Q P (ZMod 2)) (B : Matrix Q R (ZMod 2)) (Dd : Matrix S R (ZMod 2)) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (blockTri A B Dd).mulVecLin)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin)
        + Module.finrank (ZMod 2) ↥(blockW A B Dd) := by
  have hmem : ∀ z : P ⊕ R → ZMod 2, z ∈ LinearMap.ker (blockTri A B Dd).mulVecLin ↔
      (A *ᵥ (z ∘ Sum.inl) + B *ᵥ (z ∘ Sum.inr) = 0 ∧ Dd *ᵥ (z ∘ Sum.inr) = 0) := by
    intro z
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, blockTri, Matrix.fromBlocks_mulVec]
    constructor
    · intro h
      refine ⟨funext fun q => ?_, funext fun s => ?_⟩
      · simpa using congrFun h (Sum.inl q)
      · simpa using congrFun h (Sum.inr s)
    · rintro ⟨h1, h2⟩
      funext q
      rcases q with q | s
      · simpa using congrFun h1 q
      · simpa using congrFun h2 s
  have hWmem : ∀ y : R → ZMod 2, y ∈ blockW A B Dd ↔
      (Dd *ᵥ y = 0 ∧ B *ᵥ y ∈ LinearMap.range A.mulVecLin) := by
    intro y
    simp only [blockW, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_comap,
      Matrix.mulVecLin_apply]
  set π : ↥(LinearMap.ker (blockTri A B Dd).mulVecLin) →ₗ[ZMod 2] (R → ZMod 2) :=
    (projLin P R).comp (LinearMap.ker (blockTri A B Dd).mulVecLin).subtype with hπ
  have hrange : LinearMap.range π = blockW A B Dd := by
    rw [hπ]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change projLin P R (z : P ⊕ R → ZMod 2) ∈ blockW A B Dd
      rw [projLin_eq_comp_inr, hWmem (z.1 ∘ Sum.inr)]
      have hz := (hmem z.1).mp z.2
      refine ⟨hz.2, ?_⟩
      refine ⟨z.1 ∘ Sum.inl, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      have hBA : B *ᵥ (z.1 ∘ Sum.inr) = A *ᵥ (z.1 ∘ Sum.inl) := by
        calc B *ᵥ (z.1 ∘ Sum.inr)
            = B *ᵥ (z.1 ∘ Sum.inr)
              + (A *ᵥ (z.1 ∘ Sum.inl) + B *ᵥ (z.1 ∘ Sum.inr)) := by rw [hz.1, add_zero]
          _ = B *ᵥ (z.1 ∘ Sum.inr)
              + (B *ᵥ (z.1 ∘ Sum.inr) + A *ᵥ (z.1 ∘ Sum.inl)) := by
                rw [add_comm (A *ᵥ (z.1 ∘ Sum.inl)) (B *ᵥ (z.1 ∘ Sum.inr))]
          _ = (B *ᵥ (z.1 ∘ Sum.inr) + B *ᵥ (z.1 ∘ Sum.inr))
              + A *ᵥ (z.1 ∘ Sum.inl) := by rw [← add_assoc]
          _ = A *ᵥ (z.1 ∘ Sum.inl) := by rw [add_self_eq_zero_fun, zero_add]
      exact hBA.symm
    · intro hy
      rw [hWmem y] at hy
      obtain ⟨hD, hB⟩ := hy
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hB
      have hx' : A *ᵥ x = B *ᵥ y := by simpa only [Matrix.mulVecLin_apply] using hx
      refine ⟨⟨Sum.elim x y, (hmem _).mpr ⟨?_, ?_⟩⟩, ?_⟩
      · rw [sumElim_comp_inl, sumElim_comp_inr, ← hx']
        exact add_self_eq_zero_fun _
      · rw [sumElim_comp_inr]
        exact hD
      · change projLin P R (Sum.elim x y) = y
        rw [projLin_eq_comp_inr, sumElim_comp_inr]
  have hker_eq : (LinearMap.range (inclLin P R)) ⊓ (LinearMap.ker (blockTri A B Dd).mulVecLin)
      = (LinearMap.ker A.mulVecLin).map (inclLin P R) := by
    ext z
    constructor
    · rintro ⟨hzr, hzK⟩
      obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp hzr
      refine Submodule.mem_map.mpr ⟨d, ?_, rfl⟩
      have hz := (hmem (inclLin P R d)).mp hzK
      have h1 := hz.1
      rw [inclLin_comp_inl, inclLin_comp_inr] at h1
      simpa using h1
    · rintro hz
      obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.mp hz
      have hd' : A *ᵥ d = 0 := by simpa using hd
      refine ⟨LinearMap.mem_range.mpr ⟨d, rfl⟩, ?_⟩
      refine (hmem (inclLin P R d)).mpr ⟨?_, ?_⟩
      · rw [inclLin_comp_inl, inclLin_comp_inr, hd', Matrix.mulVec_zero, add_zero]
      · rw [inclLin_comp_inr, Matrix.mulVec_zero]
  have hkerdim : Module.finrank (ZMod 2) ↥(LinearMap.ker π)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker A.mulVecLin) := by
    rw [hπ, LinearMap.ker_comp, ker_projLin_eq_range_inclLin]
    rw [finrank_comap_subtype, hker_eq]
    exact (Submodule.equivMapOfInjective (inclLin P R) (inclLin_injective P R)
      (LinearMap.ker A.mulVecLin)).finrank_eq.symm
  have hrank := LinearMap.finrank_range_add_finrank_ker π
  rw [hrange, hkerdim] at hrank
  exact hrank.symm.trans (Nat.add_comm _ _)

/-! ### 1.3 The induced map on the quotient space and the dimension bridge -/

section Bridge

variable {X X' Y Y' P Q : Type*}
variable [Fintype X] [Fintype X'] [Fintype Y] [Fintype P] [Fintype Q]

/-- The restriction of a cochain map to the cycles,
$F_m|_{\ker d^m_C} : Z^m(C) \to Z^m(D)$.

Well-definedness ($F_m$ sends cycles to cycles) is given by the commuting square
$F_{m+1} d^m_C = d^m_D F_m$. -/
def cyclesMap (dC : Matrix X' X (ZMod 2)) (dD : Matrix Y' Y (ZMod 2))
    (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2)) (hcomm : Fmp * dC = dD * Fm) :
    ↥(LinearMap.ker dC.mulVecLin) →ₗ[ZMod 2] ↥(LinearMap.ker dD.mulVecLin) :=
  (Fm.mulVecLin.domRestrict (LinearMap.ker dC.mulVecLin)).codRestrict
    (LinearMap.ker dD.mulVecLin) fun x => by
      have hx : dC *ᵥ (x : X → ZMod 2) = 0 := by
        simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using x.2
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearMap.domRestrict_apply,
        Matrix.mulVecLin_apply]
      calc dD *ᵥ (Fm *ᵥ (x : X → ZMod 2))
          = (dD * Fm) *ᵥ (x : X → ZMod 2) := Matrix.mulVec_mulVec _ dD Fm
        _ = (Fmp * dC) *ᵥ (x : X → ZMod 2) := by rw [hcomm]
        _ = Fmp *ᵥ (dC *ᵥ (x : X → ZMod 2)) := (Matrix.mulVec_mulVec _ Fmp dC).symm
        _ = 0 := by rw [hx, Matrix.mulVec_zero]

/-- The value of `cyclesMap`: $F_m$ acting on cycles. -/
theorem cyclesMap_apply (dC : Matrix X' X (ZMod 2)) (dD : Matrix Y' Y (ZMod 2))
    (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2)) (hcomm : Fmp * dC = dD * Fm)
    (x : ↥(LinearMap.ker dC.mulVecLin)) :
    (LinearMap.ker dD.mulVecLin).subtype (cyclesMap dC dD Fm Fmp hcomm x)
      = Fm *ᵥ (LinearMap.ker dC.mulVecLin).subtype x :=
  rfl

/-- **The induced map on the quotient space** $H^m(F) : H^m(C) \to H^m(D)$,
$[y] \mapsto [F_m y]$.

Well-definedness needs two things: $F_m$ sends cycles to cycles (using the commuting square
`hcomm` of $F_{m+1}$), and $F_m$ sends boundaries to boundaries (using the commuting square
`hcommPrev` of $F_{m-1}$). This is exactly the "missing step" named in the division of labour
at the end of §5 of `Homology/MappingCone.lean`. -/
def cohMap (dC : Matrix X' X (ZMod 2)) (dCp : Matrix X P (ZMod 2))
    (dD : Matrix Y' Y (ZMod 2)) (dDp : Matrix Y Q (ZMod 2))
    (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2)) (Fprev : Matrix Q P (ZMod 2))
    (hcomm : Fmp * dC = dD * Fm) (hcommPrev : Fm * dCp = dDp * Fprev) :
    (↥(LinearMap.ker dC.mulVecLin) ⧸
        (LinearMap.range dCp.mulVecLin).comap (LinearMap.ker dC.mulVecLin).subtype) →ₗ[ZMod 2]
      (↥(LinearMap.ker dD.mulVecLin) ⧸
        (LinearMap.range dDp.mulVecLin).comap (LinearMap.ker dD.mulVecLin).subtype) :=
  Submodule.mapQ _ _ (cyclesMap dC dD Fm Fmp hcomm) fun x hx => by
    rw [Submodule.mem_comap] at hx ⊢
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    have hy' : dCp *ᵥ y = (LinearMap.ker dC.mulVecLin).subtype x := by
      rw [← Matrix.mulVecLin_apply]
      exact hy
    refine LinearMap.mem_range.mpr ⟨Fprev *ᵥ y, ?_⟩
    rw [Matrix.mulVecLin_apply, cyclesMap_apply, Matrix.mulVec_mulVec, ← hcommPrev,
      ← Matrix.mulVec_mulVec, hy']

/-- $\varphi_m : Z^m(C) \to H^m(D)$, $y \mapsto [F_m y]$ (the lift of the induced map to the
cycles). -/
def cohLift (dC : Matrix X' X (ZMod 2)) (dD : Matrix Y' Y (ZMod 2))
    (dDp : Matrix Y Q (ZMod 2)) (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2))
    (hcomm : Fmp * dC = dD * Fm) :
    ↥(LinearMap.ker dC.mulVecLin) →ₗ[ZMod 2]
      (↥(LinearMap.ker dD.mulVecLin) ⧸
        (LinearMap.range dDp.mulVecLin).comap (LinearMap.ker dD.mulVecLin).subtype) :=
  ((LinearMap.range dDp.mulVecLin).comap (LinearMap.ker dD.mulVecLin).subtype).mkQ.comp
    (cyclesMap dC dD Fm Fmp hcomm)

/-- `cohLift` is the composite of `cohMap` with the quotient projection
(`Submodule.mapQ_mkQ`). -/
theorem cohMap_comp_mkQ (dC : Matrix X' X (ZMod 2)) (dCp : Matrix X P (ZMod 2))
    (dD : Matrix Y' Y (ZMod 2)) (dDp : Matrix Y Q (ZMod 2))
    (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2)) (Fprev : Matrix Q P (ZMod 2))
    (hcomm : Fmp * dC = dD * Fm) (hcommPrev : Fm * dCp = dDp * Fprev) :
    (cohMap dC dCp dD dDp Fm Fmp Fprev hcomm hcommPrev).comp
        ((LinearMap.range dCp.mulVecLin).comap (LinearMap.ker dC.mulVecLin).subtype).mkQ
      = cohLift dC dD dDp Fm Fmp hcomm := by
  ext x
  rfl

/-- The image of $\varphi_m$ is the image of the induced map $H^m(F)$. -/
theorem range_cohLift_eq_range_cohMap (dC : Matrix X' X (ZMod 2)) (dCp : Matrix X P (ZMod 2))
    (dD : Matrix Y' Y (ZMod 2)) (dDp : Matrix Y Q (ZMod 2))
    (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2)) (Fprev : Matrix Q P (ZMod 2))
    (hcomm : Fmp * dC = dD * Fm) (hcommPrev : Fm * dCp = dDp * Fprev) :
    LinearMap.range (cohLift dC dD dDp Fm Fmp hcomm)
      = LinearMap.range (cohMap dC dCp dD dDp Fm Fmp Fprev hcomm hcommPrev) := by
  rw [← cohMap_comp_mkQ dC dCp dD dDp Fm Fmp Fprev hcomm hcommPrev]
  rw [LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top]

/-- The kernel of $\varphi_m$: the cycles $y$ with $F_m y \in B^m(D)$ (that is, $S_{m-1}$ in
identity (S) of §2). -/
theorem ker_cohLift (dC : Matrix X' X (ZMod 2)) (dD : Matrix Y' Y (ZMod 2))
    (dDp : Matrix Y Q (ZMod 2)) (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2))
    (hcomm : Fmp * dC = dD * Fm) :
    LinearMap.ker (cohLift dC dD dDp Fm Fmp hcomm)
      = Submodule.comap (LinearMap.ker dC.mulVecLin).subtype
          ((LinearMap.ker dC.mulVecLin) ⊓ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin) := by
  rw [cohLift, LinearMap.ker_comp, Submodule.ker_mkQ]
  ext x
  constructor
  · intro hx
    have hx1 : (LinearMap.ker dD.mulVecLin).subtype (cyclesMap dC dD Fm Fmp hcomm x)
        ∈ LinearMap.range dDp.mulVecLin := hx
    rw [cyclesMap_apply dC dD Fm Fmp hcomm x] at hx1
    rw [Submodule.mem_comap]
    refine ⟨x.2, ?_⟩
    change (LinearMap.ker dC.mulVecLin).subtype x
      ∈ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin
    rw [Submodule.mem_comap]
    exact hx1
  · intro hx
    rw [Submodule.mem_comap] at hx
    have hx1 : Fm *ᵥ (LinearMap.ker dC.mulVecLin).subtype x
        ∈ LinearMap.range dDp.mulVecLin := hx.2
    change (LinearMap.ker dD.mulVecLin).subtype (cyclesMap dC dD Fm Fmp hcomm x)
      ∈ LinearMap.range dDp.mulVecLin
    rw [cyclesMap_apply dC dD Fm Fmp hcomm x]
    exact hx1

/-- **The dimension bridge (identity (S))**:
$\dim S + \dim \mathrm{im}\,H^m(F) = \dim Z^m(C)$, where
$S = Z^m(C) \cap F_m^{-1}(B^m(D))$ is the kernel of $\varphi_m$. -/
theorem finrank_inf_comap_add_finrank_range_cohMap (dC : Matrix X' X (ZMod 2))
    (dCp : Matrix X P (ZMod 2)) (dD : Matrix Y' Y (ZMod 2)) (dDp : Matrix Y Q (ZMod 2))
    (Fm : Matrix Y X (ZMod 2)) (Fmp : Matrix Y' X' (ZMod 2)) (Fprev : Matrix Q P (ZMod 2))
    (hcomm : Fmp * dC = dD * Fm) (hcommPrev : Fm * dCp = dDp * Fprev) :
    Module.finrank (ZMod 2)
        ↥((LinearMap.ker dC.mulVecLin) ⊓ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin)
      + Module.finrank (ZMod 2)
          ↥(LinearMap.range (cohMap dC dCp dD dDp Fm Fmp Fprev hcomm hcommPrev))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker dC.mulVecLin) := by
  have hSe : Module.finrank (ZMod 2)
        ↥(((LinearMap.ker dC.mulVecLin) ⊓ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin)
          ⊓ (LinearMap.ker dC.mulVecLin))
      = Module.finrank (ZMod 2)
        ↥((LinearMap.ker dC.mulVecLin) ⊓ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin) :=
    finrank_submodule_congr (inf_eq_left.mpr
      (inf_le_left : (LinearMap.ker dC.mulVecLin) ⊓ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin
        ≤ LinearMap.ker dC.mulVecLin))
  have hbridge := LinearMap.finrank_range_add_finrank_ker (cohLift dC dD dDp Fm Fmp hcomm)
  rw [ker_cohLift dC dD dDp Fm Fmp hcomm] at hbridge
  rw [finrank_comap_subtype
    ((LinearMap.ker dC.mulVecLin) ⊓ (LinearMap.range dDp.mulVecLin).comap Fm.mulVecLin)
    (LinearMap.ker dC.mulVecLin)] at hbridge
  rw [hSe] at hbridge
  rw [← range_cohLift_eq_range_cohMap dC dCp dD dDp Fm Fmp Fprev hcomm hcommPrev]
  omega

end Bridge

/-! ## 2. The cohomology of the four-term complex and the four components of $F$

The two ends of the four-term complex $C_0 \to C_1 \to C_2 \to C_3$ are zero: $C_{-1} = 0$
and $C_4 = 0$, so $B^0 = \mathrm{im}\,d_{-1} = 0$ and $Z^3 = \ker d_3 = \top$. The `bounds0`
and `cycles3` below write these two endpoints in a form **letter-for-letter the same shape as
the generic formulas of §1** ($B^0$ as the image of the zero matrix, $Z^3$ as the kernel of
the zero matrix), so that the instantiation in §3 is `rfl`-level. -/

/-- $B^0 = \mathrm{im}\,d_{-1} = 0$ (written as the image of the zero matrix, see this
section's note). -/
def bounds0 (_K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₀ → ZMod 2) :=
  LinearMap.range (0 : Matrix C₀ (Fin 0) (ZMod 2)).mulVecLin

/-- $Z^3 = \ker d_3 = \top$ (written as the kernel of the zero matrix, see this section's
note). -/
def cycles3 (_K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₃ → ZMod 2) :=
  LinearMap.ker (0 : Matrix (Fin 0) C₃ (ZMod 2)).mulVecLin

/-- $Z^3$ is the whole space. -/
theorem cycles3_eq_top (K : Cochain4 C₀ C₁ C₂ C₃) : cycles3 K = ⊤ := by
  rw [cycles3, Submodule.eq_top_iff']
  intro v
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact Matrix.zero_mulVec v

/-- $B^0$ is the zero submodule. -/
theorem bounds0_eq_bot (K : Cochain4 C₀ C₁ C₂ C₃) : bounds0 K = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  rw [Submodule.mem_bot]
  rw [bounds0] at hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv
  rw [← hw, Matrix.mulVecLin_apply]
  exact Matrix.zero_mulVec w

/-- The $H^0 = Z^0/B^0$ of the four-term complex ($B^0 = 0$, so it is isomorphic to $Z^0$). -/
abbrev coh0 (K : Cochain4 C₀ C₁ C₂ C₃) : Type _ :=
  ↥(cycles0 K) ⧸ (bounds0 K).comap (cycles0 K).subtype

/-- The $H^1 = Z^1/B^1$ of the four-term complex. -/
abbrev coh1 (K : Cochain4 C₀ C₁ C₂ C₃) : Type _ :=
  ↥(cycles1 K) ⧸ (bounds1 K).comap (cycles1 K).subtype

/-- The $H^2 = Z^2/B^2$ of the four-term complex. -/
abbrev coh2 (K : Cochain4 C₀ C₁ C₂ C₃) : Type _ :=
  ↥(cycles2 K) ⧸ (bounds2 K).comap (cycles2 K).subtype

/-- The $H^3 = Z^3/B^3$ of the four-term complex ($Z^3 = \top$). -/
abbrev coh3 (K : Cochain4 C₀ C₁ C₂ C₃) : Type _ :=
  ↥(cycles3 K) ⧸ (bounds3 K).comap (cycles3 K).subtype

variable {C : Cochain4 C₀ C₁ C₂ C₃} {D : Cochain4 D₀ D₁ D₂ D₃}

/-- $H^0(C) \to H^0(D)$: induced by $F_0$ (degree $m = 0$). -/
def cohMap0 (F : CochainMap C D) : coh0 C →ₗ[ZMod 2] coh0 D :=
  cohMap C.d0 (0 : Matrix C₀ (Fin 0) (ZMod 2)) D.d0 (0 : Matrix D₀ (Fin 0) (ZMod 2))
    F.F0 F.F1 (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) F.comm_d0
    (by rw [Matrix.mul_zero, Matrix.zero_mul])

/-- $H^1(C) \to H^1(D)$: induced by $F_1$ (degree $m = 1$). -/
def cohMap1 (F : CochainMap C D) : coh1 C →ₗ[ZMod 2] coh1 D :=
  cohMap C.d1 C.d0 D.d1 D.d0 F.F1 F.F2 F.F0 F.comm_d1 F.comm_d0

/-- $H^2(C) \to H^2(D)$: induced by $F_2$ (degree $m = 2$). -/
def cohMap2 (F : CochainMap C D) : coh2 C →ₗ[ZMod 2] coh2 D :=
  cohMap C.d2 C.d1 D.d2 D.d1 F.F2 F.F3 F.F1 F.comm_d2 F.comm_d1

/-- $H^3(C) \to H^3(D)$: induced by $F_3$ (degree $m = 3$, the top; the cycle condition is
empty). -/
def cohMap3 (F : CochainMap C D) : coh3 C →ₗ[ZMod 2] coh3 D :=
  cohMap (0 : Matrix (Fin 0) C₃ (ZMod 2)) C.d2 (0 : Matrix (Fin 0) D₃ (ZMod 2)) D.d2
    F.F3 (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) F.F2 (by rw [Matrix.mul_zero, Matrix.zero_mul])
    F.comm_d2

/-! ## 3. The dimensions of the terms of the mapping cone

$S_n := Z^{n+1}(C) \cap F_{n+1}^{-1}(B^{n+1}(D))$ (the second term of identity (F) of §2).
The four $S$ are written in a form **letter-for-letter the same shape as the generic
formula** ($S_{-1}$ and $S_2$ involve endpoints and use the zero matrix as a placeholder), so
that the instantiation of the fibre computation and the dimension bridge of §1 is `rfl`-level.
-/

/-- $S_{-1} \subseteq C_0$: the elements of $Z^0(C)$ whose $F_0$-image lies in
$B^0(D) = 0$. -/
def coneSm1 (F : CochainMap C D) : Submodule (ZMod 2) (C₀ → ZMod 2) :=
  (LinearMap.ker C.d0.mulVecLin) ⊓
    (LinearMap.range (0 : Matrix D₀ (Fin 0) (ZMod 2)).mulVecLin).comap F.F0.mulVecLin

/-- $S_0 \subseteq C_1$: the elements of $Z^1(C)$ whose $F_1$-image lies in $B^1(D)$. -/
def coneS0 (F : CochainMap C D) : Submodule (ZMod 2) (C₁ → ZMod 2) :=
  (LinearMap.ker C.d1.mulVecLin) ⊓ (LinearMap.range D.d0.mulVecLin).comap F.F1.mulVecLin

/-- $S_1 \subseteq C_2$. -/
def coneS1 (F : CochainMap C D) : Submodule (ZMod 2) (C₂ → ZMod 2) :=
  (LinearMap.ker C.d2.mulVecLin) ⊓ (LinearMap.range D.d1.mulVecLin).comap F.F2.mulVecLin

/-- $S_2 \subseteq C_3$ ($Z^3(C) = \top$, so only the condition "$F_3$-image is a boundary"
remains). -/
def coneS2 (F : CochainMap C D) : Submodule (ZMod 2) (C₃ → ZMod 2) :=
  (LinearMap.ker (0 : Matrix (Fin 0) C₃ (ZMod 2)).mulVecLin) ⊓
    (LinearMap.range D.d2.mulVecLin).comap F.F3.mulVecLin

/-- $Z^{-1}(\mathrm{cone}) = \ker d^{-1}_{\mathrm{cone}}$ (the term on $C_0$). -/
def coneZm1 (F : CochainMap C D) : Submodule (ZMod 2) (Fin 0 ⊕ C₀ → ZMod 2) :=
  LinearMap.ker (coneDm1 F).mulVecLin

/-- The $H^0$ of the cone: $Z^0(\mathrm{cone})/B^0(\mathrm{cone})$, where
$B^0(\mathrm{cone}) = \mathrm{im}\,d^{-1}_{\mathrm{cone}}$ (this term does not fit in
`mappingCone`; see `Homology/MappingCone.lean` and `coneDm1`). -/
abbrev coneCoh0 (F : CochainMap C D) : Type _ :=
  ↥(cycles0 (mappingCone F)) ⧸
    (LinearMap.range (coneDm1 F).mulVecLin).comap (cycles0 (mappingCone F)).subtype

/-! ### 3.1 The four instances of the fibre computation (identity (F)) -/

/-- **(F), $n = 0$**: $\dim Z^0(\mathrm{cone}) = \dim Z^0(D) + \dim S_0$. -/
theorem finrank_cycles0_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(cycles0 (mappingCone F))
      = Module.finrank (ZMod 2) ↥(cycles0 D) + Module.finrank (ZMod 2) ↥(coneS0 F) := by
  have h := finrank_ker_blockTri D.d0 F.F1 (-C.d1)
  have e1 : Module.finrank (ZMod 2)
        ↥(LinearMap.ker (blockTri D.d0 F.F1 (-C.d1)).mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles0 (mappingCone F)) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2) ↥(blockW D.d0 F.F1 (-C.d1))
      = Module.finrank (ZMod 2) ↥(coneS0 F) :=
    finrank_submodule_congr (by rw [blockW, coneS0, ker_mulVecLin_neg])
  have e3 : Module.finrank (ZMod 2) ↥(LinearMap.ker D.d0.mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles0 D) :=
    finrank_submodule_congr rfl
  rw [e1, e2, e3] at h
  exact h

/-- **(F), $n = 1$**: $\dim Z^1(\mathrm{cone}) = \dim Z^1(D) + \dim S_1$. -/
theorem finrank_cycles1_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(cycles1 (mappingCone F))
      = Module.finrank (ZMod 2) ↥(cycles1 D) + Module.finrank (ZMod 2) ↥(coneS1 F) := by
  have h := finrank_ker_blockTri D.d1 F.F2 (-C.d2)
  have e1 : Module.finrank (ZMod 2)
        ↥(LinearMap.ker (blockTri D.d1 F.F2 (-C.d2)).mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles1 (mappingCone F)) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2) ↥(blockW D.d1 F.F2 (-C.d2))
      = Module.finrank (ZMod 2) ↥(coneS1 F) :=
    finrank_submodule_congr (by rw [blockW, coneS1, ker_mulVecLin_neg])
  have e3 : Module.finrank (ZMod 2) ↥(LinearMap.ker D.d1.mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles1 D) :=
    finrank_submodule_congr rfl
  rw [e1, e2, e3] at h
  exact h

/-- **(F), $n = 2$**: $\dim Z^2(\mathrm{cone}) = \dim Z^2(D) + \dim S_2$. -/
theorem finrank_cycles2_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(cycles2 (mappingCone F))
      = Module.finrank (ZMod 2) ↥(cycles2 D) + Module.finrank (ZMod 2) ↥(coneS2 F) := by
  have h := finrank_ker_blockTri D.d2 F.F3 (0 : Matrix (Fin 0) C₃ (ZMod 2))
  have e1 : Module.finrank (ZMod 2)
        ↥(LinearMap.ker (blockTri D.d2 F.F3 (0 : Matrix (Fin 0) C₃ (ZMod 2))).mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles2 (mappingCone F)) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2)
        ↥(blockW D.d2 F.F3 (0 : Matrix (Fin 0) C₃ (ZMod 2)))
      = Module.finrank (ZMod 2) ↥(coneS2 F) :=
    finrank_submodule_congr (by rw [blockW, coneS2])
  have e3 : Module.finrank (ZMod 2) ↥(LinearMap.ker D.d2.mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles2 D) :=
    finrank_submodule_congr rfl
  rw [e1, e2, e3] at h
  exact h

/-- **(F), $n = -1$**: $\dim Z^{-1}(\mathrm{cone}) = \dim Z^{-1}(D) + \dim S_{-1}$, and
$Z^{-1}(D)$ lives on $D_{-1} = 0$ and has dimension $0$. -/
theorem finrank_coneZm1 (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(coneZm1 F) = Module.finrank (ZMod 2) ↥(coneSm1 F) := by
  have h := finrank_ker_blockTri (0 : Matrix D₀ (Fin 0) (ZMod 2)) F.F0 (-C.d0)
  have hzero : Module.finrank (ZMod 2)
      ↥(LinearMap.ker (0 : Matrix D₀ (Fin 0) (ZMod 2)).mulVecLin) = 0 := by
    have htop : LinearMap.ker (0 : Matrix D₀ (Fin 0) (ZMod 2)).mulVecLin = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro v
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact Matrix.zero_mulVec v
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have e1 : Module.finrank (ZMod 2)
        ↥(LinearMap.ker
          (blockTri (0 : Matrix D₀ (Fin 0) (ZMod 2)) F.F0 (-C.d0)).mulVecLin)
      = Module.finrank (ZMod 2) ↥(coneZm1 F) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2)
        ↥(blockW (0 : Matrix D₀ (Fin 0) (ZMod 2)) F.F0 (-C.d0))
      = Module.finrank (ZMod 2) ↥(coneSm1 F) :=
    finrank_submodule_congr (by rw [blockW, coneSm1, ker_mulVecLin_neg])
  rw [e1, e2, hzero] at h
  omega

/-! ### 3.2 The four instances of the dimension bridge (identity (S)) -/

/-- **(S), $n = -1$**: $\dim S_{-1} + \dim \mathrm{im}\,H^0(F) = \dim Z^0(C)$. -/
theorem finrank_coneSm1_add_range_cohMap0 (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(coneSm1 F)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap0 F))
      = Module.finrank (ZMod 2) ↥(cycles0 C) := by
  exact finrank_inf_comap_add_finrank_range_cohMap C.d0
    (0 : Matrix C₀ (Fin 0) (ZMod 2)) D.d0 (0 : Matrix D₀ (Fin 0) (ZMod 2))
    F.F0 F.F1 (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) F.comm_d0
    (by rw [Matrix.mul_zero, Matrix.zero_mul])

/-- **(S), $n = 0$**: $\dim S_0 + \dim \mathrm{im}\,H^1(F) = \dim Z^1(C)$. -/
theorem finrank_coneS0_add_range_cohMap1 (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(coneS0 F)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap1 F))
      = Module.finrank (ZMod 2) ↥(cycles1 C) := by
  exact finrank_inf_comap_add_finrank_range_cohMap C.d1 C.d0 D.d1 D.d0
    F.F1 F.F2 F.F0 F.comm_d1 F.comm_d0

/-- **(S), $n = 1$**: $\dim S_1 + \dim \mathrm{im}\,H^2(F) = \dim Z^2(C)$. -/
theorem finrank_coneS1_add_range_cohMap2 (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(coneS1 F)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap2 F))
      = Module.finrank (ZMod 2) ↥(cycles2 C) := by
  exact finrank_inf_comap_add_finrank_range_cohMap C.d2 C.d1 D.d2 D.d1
    F.F2 F.F3 F.F1 F.comm_d2 F.comm_d1

/-- **(S), $n = 2$ (the top)**: $\dim S_2 + \dim \mathrm{im}\,H^3(F) = \dim Z^3(C)$. -/
theorem finrank_coneS2_add_range_cohMap3 (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(coneS2 F)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap3 F))
      = Module.finrank (ZMod 2) ↥(cycles3 C) := by
  exact finrank_inf_comap_add_finrank_range_cohMap
    (0 : Matrix (Fin 0) C₃ (ZMod 2)) C.d2 (0 : Matrix (Fin 0) D₃ (ZMod 2)) D.d2
    F.F3 (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) F.F2
    (by rw [Matrix.mul_zero, Matrix.zero_mul]) F.comm_d2

/-! ### 3.3 The boundaries and cycles of the cone, and cohomology at the endpoints -/

/-- $\mathrm{im}\,d^{-1}_{\mathrm{cone}} \subseteq Z^0(\mathrm{cone})$
(that is, `cone_d0_comp_dm1`: the cone is a complex in degrees $-1 \to 0$ as well). -/
theorem range_coneDm1_le_cycles0 (F : CochainMap C D) :
    LinearMap.range (coneDm1 F).mulVecLin ≤ cycles0 (mappingCone F) := by
  rintro z ⟨w, rfl⟩
  rw [cycles0, mappingCone, LinearMap.mem_ker]
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, cone_d0_comp_dm1 F, Matrix.zero_mulVec]

/-- $\dim H^0(\mathrm{cone}) + \dim B^0(\mathrm{cone}) = \dim Z^0(\mathrm{cone})$. -/
theorem finrank_coneCoh0_add (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coneCoh0 F)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (coneDm1 F).mulVecLin)
      = Module.finrank (ZMod 2) ↥(cycles0 (mappingCone F)) := by
  have h := Submodule.finrank_quotient_add_finrank
    ((LinearMap.range (coneDm1 F).mulVecLin).comap (cycles0 (mappingCone F)).subtype)
  rw [finrank_comap_subtype, inf_eq_left.mpr (range_coneDm1_le_cycles0 F)] at h
  exact h

/-- $\dim B^0(\mathrm{cone}) + \dim Z^{-1}(\mathrm{cone}) = |C_0|$
(rank-nullity for $d^{-1}_{\mathrm{cone}} : \mathrm{cone}^{-1} = C_0 \to \mathrm{cone}^0$). -/
theorem finrank_coneB0_add (F : CochainMap C D) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (coneDm1 F).mulVecLin)
      + Module.finrank (ZMod 2) ↥(coneZm1 F)
      = Fintype.card C₀ := by
  have h := LinearMap.finrank_range_add_finrank_ker (coneDm1 F).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, zero_add] at h
  have e : Module.finrank (ZMod 2) ↥(coneZm1 F)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (coneDm1 F).mulVecLin) :=
    finrank_submodule_congr rfl
  rw [← e] at h
  exact h

/-- $\dim Z^3(K) = |C_3|$ ($Z^3 = \top$). -/
theorem finrank_cycles3 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) ↥(cycles3 K) = Fintype.card C₃ := by
  rw [cycles3_eq_top K, finrank_top, Module.finrank_fintype_fun_eq_card]

/-- $\dim H^0(K) = \dim Z^0(K)$ ($B^0 = 0$). -/
theorem finrank_coh0_eq (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2)
        (↥(cycles0 K) ⧸ (bounds0 K).comap (cycles0 K).subtype)
      = Module.finrank (ZMod 2) ↥(cycles0 K) := by
  have hle : bounds0 K ≤ cycles0 K := (le_of_eq (bounds0_eq_bot K)).trans bot_le
  have h := Submodule.finrank_quotient_add_finrank ((bounds0 K).comap (cycles0 K).subtype)
  rw [finrank_comap_subtype, inf_eq_left.mpr hle] at h
  have e : Module.finrank (ZMod 2) ↥(bounds0 K) = 0 := by
    rw [bounds0_eq_bot K, finrank_bot]
  rw [e, add_zero] at h
  exact h

/-- $\dim H^1(K) + \dim B^1(K) = \dim Z^1(K)$. -/
theorem finrank_coh1_add (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (coh1 K) + Module.finrank (ZMod 2) ↥(bounds1 K)
      = Module.finrank (ZMod 2) ↥(cycles1 K) := by
  have h := finrank_H1 K
  rw [finrank_comap_bounds1 K] at h
  exact h

/-- $\dim H^2(K) + \dim B^2(K) = \dim Z^2(K)$. -/
theorem finrank_coh2_add (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (coh2 K) + Module.finrank (ZMod 2) ↥(bounds2 K)
      = Module.finrank (ZMod 2) ↥(cycles2 K) := by
  have h := finrank_H2 K
  rw [finrank_comap_bounds2 K] at h
  exact h

/-- $\dim H^3(K) + \dim B^3(K) = |C_3|$ ($Z^3 = \top$). -/
theorem finrank_coh3_add (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (coh3 K) + Module.finrank (ZMod 2) ↥(bounds3 K)
      = Fintype.card C₃ := by
  have hle : bounds3 K ≤ cycles3 K := by rw [cycles3_eq_top K]; exact le_top
  have h := Submodule.finrank_quotient_add_finrank ((bounds3 K).comap (cycles3 K).subtype)
  rw [finrank_comap_subtype, inf_eq_left.mpr hle, finrank_cycles3 K] at h
  exact h

/-! ### 3.4 The three instances of rank-nullity (function-space dimensions as cardinalities) -/

/-- $\dim B^1(K) + \dim Z^0(K) = |C_0|$. -/
theorem finrank_bounds1_add_cycles0 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) ↥(bounds1 K) + Module.finrank (ZMod 2) ↥(cycles0 K)
      = Fintype.card C₀ := by
  have h := LinearMap.finrank_range_add_finrank_ker K.d0.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  have e1 : Module.finrank (ZMod 2) ↥(bounds1 K)
      = Module.finrank (ZMod 2) ↥(LinearMap.range K.d0.mulVecLin) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2) ↥(cycles0 K)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker K.d0.mulVecLin) :=
    finrank_submodule_congr rfl
  rw [← e1, ← e2] at h
  exact h

/-- $\dim B^2(K) + \dim Z^1(K) = |C_1|$. -/
theorem finrank_bounds2_add_cycles1 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) ↥(bounds2 K) + Module.finrank (ZMod 2) ↥(cycles1 K)
      = Fintype.card C₁ := by
  have h := LinearMap.finrank_range_add_finrank_ker K.d1.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  have e1 : Module.finrank (ZMod 2) ↥(bounds2 K)
      = Module.finrank (ZMod 2) ↥(LinearMap.range K.d1.mulVecLin) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2) ↥(cycles1 K)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker K.d1.mulVecLin) :=
    finrank_submodule_congr rfl
  rw [← e1, ← e2] at h
  exact h

/-- $\dim B^3(K) + \dim Z^2(K) = |C_2|$. -/
theorem finrank_bounds3_add_cycles2 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) ↥(bounds3 K) + Module.finrank (ZMod 2) ↥(cycles2 K)
      = Fintype.card C₂ := by
  have h := LinearMap.finrank_range_add_finrank_ker K.d2.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  have e1 : Module.finrank (ZMod 2) ↥(bounds3 K)
      = Module.finrank (ZMod 2) ↥(LinearMap.range K.d2.mulVecLin) :=
    finrank_submodule_congr rfl
  have e2 : Module.finrank (ZMod 2) ↥(cycles2 K)
      = Module.finrank (ZMod 2) ↥(LinearMap.ker K.d2.mulVecLin) :=
    finrank_submodule_congr rfl
  rw [← e1, ← e2] at h
  exact h

/-! ## 4. The main theorems: the Snake dimension formula ($n = 0,1,2,3$)

Each one proves the **subtraction-free form** first, then converts it to the form of [14].
The subtraction-free form is itself an equivalent statement and does not depend on the
truncation:

$$\dim H^n(\mathrm{cone}) + \dim \mathrm{im}\,H^n(F) + \dim \mathrm{im}\,H^{n+1}(F)
  = \dim H^n(D) + \dim H^{n+1}(C).$$ -/

/-- **The Snake dimension formula ($n = 0$, subtraction-free form)**. -/
theorem finrank_coneCoh0_add_range (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coneCoh0 F)
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap0 F))
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap1 F))
      = Module.finrank (ZMod 2) (coh0 D) + Module.finrank (ZMod 2) (coh1 C) := by
  have h1 := finrank_coneCoh0_add F
  have h2 := finrank_coneB0_add F
  have h3 := finrank_coneZm1 F
  have h4 := finrank_cycles0_mappingCone F
  have h5 := finrank_coh0_eq D
  have h6 := finrank_coneSm1_add_range_cohMap0 F
  have h7 := finrank_coneS0_add_range_cohMap1 F
  have h8 := finrank_coh1_add C
  have h9 := finrank_bounds1_add_cycles0 C
  simp only [coneCoh0, coh0, coh1] at *
  omega

/-- **The Snake dimension formula ($n = 1$, subtraction-free form)**. -/
theorem finrank_coh1_mappingCone_add_range (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coh1 (mappingCone F))
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap1 F))
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap2 F))
      = Module.finrank (ZMod 2) (coh1 D) + Module.finrank (ZMod 2) (coh2 C) := by
  have h1 := finrank_coh1_add (mappingCone F)
  have h2 := finrank_bounds1_add_cycles0 (mappingCone F)
  have h3 : Fintype.card (D₀ ⊕ C₁) = Fintype.card D₀ + Fintype.card C₁ := Fintype.card_sum
  have h4 := finrank_cycles1_mappingCone F
  have h5 := finrank_cycles0_mappingCone F
  have h6 := finrank_coh1_add D
  have h7 := finrank_bounds1_add_cycles0 D
  have h8 := finrank_coneS0_add_range_cohMap1 F
  have h9 := finrank_coneS1_add_range_cohMap2 F
  have h10 := finrank_coh2_add C
  have h11 := finrank_bounds2_add_cycles1 C
  simp only [coh1, coh2] at *
  omega

/-- **The Snake dimension formula ($n = 2$, subtraction-free form)**. -/
theorem finrank_coh2_mappingCone_add_range (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coh2 (mappingCone F))
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap2 F))
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap3 F))
      = Module.finrank (ZMod 2) (coh2 D) + Module.finrank (ZMod 2) (coh3 C) := by
  have h1 := finrank_coh2_add (mappingCone F)
  have h2 := finrank_bounds2_add_cycles1 (mappingCone F)
  have h3 : Fintype.card (D₁ ⊕ C₂) = Fintype.card D₁ + Fintype.card C₂ := Fintype.card_sum
  have h4 := finrank_cycles2_mappingCone F
  have h5 := finrank_cycles1_mappingCone F
  have h6 := finrank_coh2_add D
  have h7 := finrank_bounds2_add_cycles1 D
  have h8 := finrank_coneS1_add_range_cohMap2 F
  have h9 := finrank_coneS2_add_range_cohMap3 F
  have h9b := finrank_cycles3 C
  have h10 := finrank_coh3_add C
  have h11 := finrank_bounds3_add_cycles2 C
  simp only [coh2, coh3] at *
  omega

/-- **The Snake dimension formula ($n = 3$, subtraction-free form)**: the top has only one
term ($\mathrm{cone}^4 = 0$, so the two terms $\mathrm{im}\,H^4(F) = 0$ and $H^4(C) = 0$
vanish). -/
theorem finrank_coh3_mappingCone_add_range (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coh3 (mappingCone F))
      + Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap3 F))
      = Module.finrank (ZMod 2) (coh3 D) := by
  have h1 := finrank_coh3_add (mappingCone F)
  have h2 : Fintype.card (D₃ ⊕ Fin 0) = Fintype.card D₃ := by
    rw [Fintype.card_sum, Fintype.card_fin, add_zero]
  have h3 := finrank_bounds3_add_cycles2 (mappingCone F)
  have h4 : Fintype.card (D₂ ⊕ C₃) = Fintype.card D₂ + Fintype.card C₃ := Fintype.card_sum
  have h5 := finrank_cycles2_mappingCone F
  have h6 := finrank_coh3_add D
  have h7 := finrank_bounds3_add_cycles2 D
  have h8 := finrank_coneS2_add_range_cohMap3 F
  have h9 := finrank_cycles3 C
  simp only [coh3] at *
  omega

/-- **The Snake dimension formula, $n = 0$** (the form of [14] p. 60):
$$\dim H^0(\mathrm{cone}) = \dim H^0(D) + \dim H^1(C)
  - \dim\mathrm{im}\,H^0(F) - \dim\mathrm{im}\,H^1(F).$$ -/
theorem finrank_coh0_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coneCoh0 F)
      = Module.finrank (ZMod 2) (coh0 D) + Module.finrank (ZMod 2) (coh1 C)
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap0 F))
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap1 F)) := by
  have h := finrank_coneCoh0_add_range F
  simp only [coneCoh0, coh0, coh1] at *
  omega

/-- **The Snake dimension formula, $n = 1$** (the form of [14] p. 60):
$$\dim H^1(\mathrm{cone}) = \dim H^1(D) + \dim H^2(C)
  - \dim\mathrm{im}\,H^1(F) - \dim\mathrm{im}\,H^2(F).$$ -/
theorem finrank_coh1_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coh1 (mappingCone F))
      = Module.finrank (ZMod 2) (coh1 D) + Module.finrank (ZMod 2) (coh2 C)
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap1 F))
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap2 F)) := by
  have h := finrank_coh1_mappingCone_add_range F
  simp only [coh1, coh2] at *
  omega

/-- **The Snake dimension formula, $n = 2$** (the form of [14] p. 60):
$$\dim H^2(\mathrm{cone}) = \dim H^2(D) + \dim H^3(C)
  - \dim\mathrm{im}\,H^2(F) - \dim\mathrm{im}\,H^3(F).$$ -/
theorem finrank_coh2_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coh2 (mappingCone F))
      = Module.finrank (ZMod 2) (coh2 D) + Module.finrank (ZMod 2) (coh3 C)
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap2 F))
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap3 F)) := by
  have h := finrank_coh2_mappingCone_add_range F
  simp only [coh2, coh3] at *
  omega

/-- **The Snake dimension formula, $n = 3$** (the top; in the form of [14] p. 60 two terms
vanish here, because $\mathrm{cone}^4 = 0$):
$$\dim H^3(\mathrm{cone}) = \dim H^3(D) - \dim\mathrm{im}\,H^3(F).$$ -/
theorem finrank_coh3_mappingCone (F : CochainMap C D) :
    Module.finrank (ZMod 2) (coh3 (mappingCone F))
      = Module.finrank (ZMod 2) (coh3 D)
        - Module.finrank (ZMod 2) ↥(LinearMap.range (cohMap3 F)) := by
  have h := finrank_coh3_mappingCone_add_range F
  simp only [coh3] at *
  omega

end QECCertificates.Homology
