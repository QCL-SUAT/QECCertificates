/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.AuxComplex

/-!
# The mapping cone: the construction the fault complex of [14] Appendix A.1 rests on

`Homology/AuxComplex.lean` renders the four-term cochain complex of [14] §1.2
$\mathbb F_2^W \xleftarrow{\delta_2} \mathbb F_2^V \xleftarrow{\delta_1} \mathbb F_2^E
\xleftarrow{\delta_0} \mathbb F_2^C$ as GF(2) matrices and machine-checks its complex
conditions; item 1 of Section 5 ("Honest boundaries") of `the gauged-measurement companion development's `SurgerySchedule` module`
records: **the fault complex of [14] Appendix A.1 (the four-term complex + mapping cone +
the Snake long exact sequence) is not formalized in this library**. This module supplies the
**mapping cone** among these — the prerequisite **shared** by two gaps in the ledger (the
fault-complex side of [14] Thm 6.5, and the prerequisite of Thm 7.7).

## 1. The direction convention (aligned word for word with `Homology/AuxComplex.lean`)

The module header of `Homology/AuxComplex.lean` checked the direction of the arrows of
[14] §1.2 once, with the conclusion: all three arrows of the source point **left**
($\delta_2 : \mathbb F_2^V \to \mathbb F_2^W$, $\delta_1 : \mathbb F_2^E \to \mathbb F_2^V$,
$\delta_0 : \mathbb F_2^C \to \mathbb F_2^E$), so it is a **cochain** complex and
$\ker\delta_2$ and $\mathrm{im}\,\delta_1$ live in $\mathbb F_2^V$. This module follows the
same convention: differentials are represented by **matrices** (rather than `LinearMap`),
`A : Matrix m n (ZMod 2)` acting on **column vectors** denotes the linear map
$\mathbb F_2^n \to \mathbb F_2^m$; the index type is a general `Type*` (needing only
`Fintype`), of which `Fin n` and the `κ, ι` of `AuxComplex.lean` are special cases.

Thus the `Cochain4 C₀ C₁ C₂ C₃` of this module is
$$C_0 \xrightarrow{\ d_0\ } C_1 \xrightarrow{\ d_1\ } C_2 \xrightarrow{\ d_2\ } C_3,
\qquad d_1 d_0 = 0,\quad d_2 d_1 = 0,$$
where `d0 : Matrix C₁ C₀ (ZMod 2)`. The $\delta_0/\delta_1/\delta_2$ of `AuxComplex.lean`
are one instance of this structure (`surgeryCochain4`, §1).

## 2. The formula for the mapping cone (derived here, not left as "by the standard formula")

Let $F : C^\bullet \to D^\bullet$ be a cochain map (four components $F_0,\dots,F_3$ and
three commuting squares $F_1 d^C_0 = d^D_0 F_0$, and so on). In the **cochain** case the
mapping cone is by definition

$$\mathrm{cone}(F)^n := D^n \oplus C^{n+1},
\qquad d^n_{\mathrm{cone}} :=
\begin{pmatrix} d^n_D & F_{n+1} \\ 0 & -d^{n+1}_C \end{pmatrix}.$$

**Why this matrix**: the two rows of $d_{\mathrm{cone}}$ read the $D$-component and the
$C$-component. The $C$-component row cannot return to $D$ (the cone packs $D$ into a large
complex, making it a subcomplex, and $C$ is only the part filled in), so the lower-left block
is $0$; the $D$-component row must send $C^{n+1}$ back to $D^{n+1}$, which is exactly
$F_{n+1}$; the two diagonal blocks are the differentials of $D$ and $C$ themselves (the one of
$C$ carries a sign, so that the $F$ terms cancel in the composite below). The composite

$$d^{n+1}_{\mathrm{cone}} d^n_{\mathrm{cone}} =
\begin{pmatrix} d^{n+1}_D d^n_D & d^{n+1}_D F_{n+1} - F_{n+2} d^{n+1}_C \\
0 & d^{n+2}_C d^{n+1}_C\end{pmatrix}$$

has its three blocks given by zero respectively from "$D$ is a complex", "$C$ is a complex"
and "$F$ is a cochain map" — **this is the whole content of the complex condition $d^2 = 0$
on the cone**. The four-term complex of this library is in degrees $0..3$, so the nonzero
terms of the cone fall in degrees $-1,0,1,2,3$:

| degree of the cone | $-1$ | $0$ | $1$ | $2$ | $3$ |
|---|---|---|---|---|---|
| term | $C_0$ | $D_0 \oplus C_1$ | $D_1 \oplus C_2$ | $D_2 \oplus C_3$ | $D_3 \oplus 0$ |
| differential | `coneDm1` | `coneD0` | `coneD1` | `coneD2` | — |

Over $\mathbb F_2$, $-$ is $+$, but this module still **writes the general form** (`-C.d1`,
`-C.d2`, `-C.d0`), simplifying with `ZMod.neg_eq_self_mod_two` only where terms must be
merged — this way the formulas agree with the textbook, and the reader need not first believe
"characteristic 2, so signs do not matter".

`Cochain4` has only four terms and cannot hold the degree of $C_0$. So this module provides
two packagings: `coneDm1/coneD0/coneD1/coneD2` are the four differentials of the **whole
cone** (including the degree of $C_0$, with `cone_d0_comp_dm1`), while `mappingCone F` is its
**nonnegative part** (a `Cochain4`, with `cone_d1_comp_d0` and `cone_d2_comp_d1`). Why the
degree $-1$ must be kept: the cone has
$H^0 = \ker d^0_{\mathrm{cone}}/\mathrm{im}\,d^{-1}_{\mathrm{cone}}$, and dropping that term
makes $H^0$ larger (item 4 of §4 explains this point by point).

## 3. What this module does

(The §1…§5 referenced below are the **section markers inside the code**, unrelated to the
numbering of this section.)

* **§1, the four-term complex**: `Cochain4`; `surgeryCochain4` packages the
  `surgeryD0/surgeryD1/surgeryD2` of `AuxComplex.lean` and its two proved theorems into an
  instance — that is, [14] §1.2's "is a 4-term cochain complex" is one value of this
  structure.
* **§2, the cochain map**: `CochainMap` (four components + three commuting squares).
* **§3, the mapping cone**: `coneDm1/coneD0/coneD1/coneD2` (block matrices) and the **main
  theorems** `cone_d0_comp_dm1` / `cone_d1_comp_d0` / `cone_d2_comp_d1` (the cone is a
  complex), together with the four-term packaging `mappingCone`.
* **§4, the short exact sequence and the connecting homomorphism**: `inclLin`/`projLin`
  (the inclusion and projection of $0 \to D^n \to \mathrm{cone}^n \to C^{n+1} \to 0$),
  `proj_comp_incl` ($\mathrm{im} \subseteq \ker$), `ker_projLin_eq_range_inclLin`
  (**exactness in the middle**, $\ker\pi = \mathrm{im}\,\iota$), `inclLin_injective` /
  `projLin_surjective` (the two ends), that the inclusion and the projection are cochain maps
  (`coneD*_incl` / `coneD*_proj`), and that **the connecting homomorphism is $F$**
  (`connectingMap_coneD0` / `connectingMap_coneD1`): for $x \in \ker d^C_n$, the
  differential of $(0,x)$ on the cone is $(F_n x, 0)$ — that is, the map
  $H^{n}(C) \to H^{n}(D)$ induced by $F$ on cohomology.
* **§5, the dimension on the homology side**: `cycles*` / `bounds*` / `bounds*_le_cycles*`
  ($B \subseteq Z$), `finrank_H1` / `finrank_H2` (the rank-nullity of cohomology
  $\dim H^n + \dim B^n = \dim Z^n$, with the dimension change of `finrank_comap_bounds*`),
  `finrank_H1_eq` / `finrank_H2_eq` (the explicit form of
  $\dim H^n = \dim Z^n - \dim B^n$), and `finrank_cone*` (the dimension identity of the
  short exact sequence $\dim\mathrm{cone}^n = \dim D^n + \dim C^{n+1}$, including the last
  term `D₃ ⊕ Fin 0`).
* **After §5**: the complete dimension formula of the Snake long exact sequence is in
  **`Homology/MappingConeSnake.lean`, in the same directory** — this module gives "cone +
  short exact sequence + connecting homomorphism is $F$", and that one gives "the induced map
  on the quotient + the dimension reading".

## 4. Honest boundaries (the paper cites this section)

**Not done, and not claimed**:

1. **The instantiation of the fault complex on a concrete hypergraph.** [14] Appendix A.1
   connects $C_{-1},\dots,C_3$ concretely to the hypergraph $H$ and the geometry of the
   detectors (which term is a check, which is a data bit, which surgery map $F$ takes). This
   module gives **abstract** four-term complexes, cochain maps and their mapping cones: any
   concrete $F: C^\bullet \to D^\bullet$ has to be filled in by the user. This module only
   packages the $C^\bullet$ side of `AuxComplex.lean` into an instance (`surgeryCochain4`);
   neither $D^\bullet$ nor $F$ is instantiated.
2. **A conclusion about the phenomenological fault distance $d$** ([14] Thm 6.5 / 6.3
   itself). What this module proves is "the cone **is** a complex, the short exact sequence
   **is** exact, the connecting homomorphism **is** $F$" — it contains no weight lower bound,
   distance reading or fault-tolerance argument.
3. **The code distance of this library is the static distance of the
   `min_weight_ker_not_mem_rowspace` family, a different quantity from the $1$-cosystolic
   distance of [14]; mixing them is an error.** (The original warning of item 2 of Section 5
   of `the gauged-measurement companion development's `SurgerySchedule` module`, transcribed here.) The four-term complex and mapping cone
   of this module give **no** distance reading: `cosystolicDistance` is in `AuxComplex.lean`,
   and it is not the same thing as the cohomological dimension of §5.
4. **The degree of $C_0$ (the $-1$ degree of the cone) is dropped by `mappingCone`.** Among
   the five degrees $-1,0,1,2,3$ of the whole cone, `mappingCone` holds only the four $0..3$
   (`Cochain4` is a four-term structure). Hence the $H^0$ of `mappingCone` is **not** the
   $H^0$ of the cone (the latter is further divided by
   $\mathrm{im}\,d^{-1}_{\mathrm{cone}}$). This module gives $d^{-1}_{\mathrm{cone}}$ as the
   separate `coneDm1` together with its complex condition `cone_d0_comp_dm1`; a user who wants
   the true $H^0$ takes it. The dimension conclusions of §5 are all **independent** of this
   step of $H^0$.
5. **The modular expansion / thickening of §7 / [14] Thm 7.7 / 7.8**: not formalized, and
   neither is $\mathcal M_t$ over $\mathbb R$, the port function, or relative expansion
   (consistent with the boundary of `AuxComplex.lean`).
6. **The complete dimension formula of the Snake long exact sequence: it is in
   `Homology/MappingConeSnake.lean`** (this module gives the dimension identities of the short
   exact sequence, the rank-nullity of cohomology, and that the connecting homomorphism **is
   $F$**; the missing step is **the induced map on the quotient space**).
   `Homology/MappingConeSnake.lean` defines $H^m(F)$ via `Submodule.mapQ`, proves its
   well-definedness point by point (cycles to cycles, boundaries to boundaries, given by the
   commuting squares of $F_{m+1}$ and $F_{m-1}$ respectively), and gives the dimension
   formulas for the four degrees $n = 0,1,2,3$ (see §4 of that module); the endpoint
   convention of item 4 of §4 here, "$C_0$ is dropped by `mappingCone`", is also carried out
   point by point there (that module's §2 uses `bounds0` / `cycles3` to reduce the two ends
   to the generic shape).

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

/-! ## 1. The four-term cochain complex -/

/-- **A four-term cochain complex** (the abstract shape of the $4$-term cochain complex of
[14] §1.2).

The differentials are written as matrices: `d0 : Matrix C₁ C₀ (ZMod 2)` acting on column
vectors denotes $d_0 : C_0 \to C_1$, and similarly for the rest. The two fields are the
complex conditions $d_1 d_0 = 0$ and $d_2 d_1 = 0$.

The $\delta_0/\delta_1/\delta_2$ of `Homology/AuxComplex.lean` are its instance
(`surgeryCochain4`). -/
structure Cochain4 (C₀ C₁ C₂ C₃ : Type*) [Fintype C₀] [Fintype C₁] [Fintype C₂] [Fintype C₃] where
  /-- The differential $d_0 : C_0 \to C_1$. -/
  d0 : Matrix C₁ C₀ (ZMod 2)
  /-- The differential $d_1 : C_1 \to C_2$. -/
  d1 : Matrix C₂ C₁ (ZMod 2)
  /-- The differential $d_2 : C_2 \to C_3$. -/
  d2 : Matrix C₃ C₂ (ZMod 2)
  /-- The complex condition $d_1 d_0 = 0$. -/
  comp_d1_d0 : d1 * d0 = 0
  /-- The complex condition $d_2 d_1 = 0$. -/
  comp_d2_d1 : d2 * d1 = 0

/-- **The four-term complex of `AuxComplex.lean` is an instance of this structure**: the
$\delta_0 : \mathbb F_2^C \to \mathbb F_2^E$, $\delta_1 : \mathbb F_2^E \to \mathbb F_2^V$,
$\delta_2 : \mathbb F_2^V \to \mathbb F_2^W$ of [14] §1.2, together with its two complex
conditions (the members of $C$ are cycles, those of $W$ are components), are exactly
`Cochain4 κ (Fin m) (Fin k) ι` — that is, the machine form of [14]'s "is a 4-term cochain
complex", packaged into one `Cochain4` value. -/
def surgeryCochain4 {k m : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] (H : AuxHypergraph k m)
    (C : κ → Finset (Fin m)) (W : ι → Finset (Fin k)) (hC : ∀ c, IsCycleSet H (C c))
    (hW : ∀ w, IsComponent H (W w)) : Cochain4 κ (Fin m) (Fin k) ι where
  d0 := surgeryD0 H C
  d1 := surgeryD1 H
  d2 := surgeryD2 W
  comp_d1_d0 := surgeryD1_mul_surgeryD0_eq_zero H C hC
  comp_d2_d1 := surgeryD2_mul_surgeryD1_eq_zero H W hW

/-! ## 2. Cochain maps -/

/-- **A cochain map** $F : C^\bullet \to D^\bullet$: four components $F_0,\dots,F_3$ and
three commuting squares $F_1 d^C_0 = d^D_0 F_0$, $F_2 d^C_1 = d^D_1 F_1$,
$F_3 d^C_2 = d^D_2 F_2$.

(The squares are arranged as in the matrix notation: both sides run from $C_n$ to
$D_{n+1}$.) -/
structure CochainMap {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Fintype C₀] [Fintype C₁] [Fintype C₂] [Fintype C₃]
    [Fintype D₀] [Fintype D₁] [Fintype D₂] [Fintype D₃]
    (C : Cochain4 C₀ C₁ C₂ C₃) (D : Cochain4 D₀ D₁ D₂ D₃) where
  /-- The component $F_0 : C_0 \to D_0$. -/
  F0 : Matrix D₀ C₀ (ZMod 2)
  /-- The component $F_1 : C_1 \to D_1$. -/
  F1 : Matrix D₁ C₁ (ZMod 2)
  /-- The component $F_2 : C_2 \to D_2$. -/
  F2 : Matrix D₂ C₂ (ZMod 2)
  /-- The component $F_3 : C_3 \to D_3$. -/
  F3 : Matrix D₃ C₃ (ZMod 2)
  /-- The commuting square $F_1 d^C_0 = d^D_0 F_0$. -/
  comm_d0 : F1 * C.d0 = D.d0 * F0
  /-- The commuting square $F_2 d^C_1 = d^D_1 F_1$. -/
  comm_d1 : F2 * C.d1 = D.d1 * F1
  /-- The commuting square $F_3 d^C_2 = d^D_2 F_2$. -/
  comm_d2 : F3 * C.d2 = D.d2 * F2

/-! ## 3. The mapping cone -/

variable {C : Cochain4 C₀ C₁ C₂ C₃} {D : Cochain4 D₀ D₁ D₂ D₃}

/-- **The $-1$ differential of the cone** $d^{-1}_{\mathrm{cone}} : C_0 \to D_0 \oplus C_1$:
$\begin{pmatrix} 0 & F_0 \\ 0 & -d^C_0\end{pmatrix}$ (rows split as $D_0 \oplus C_1$,
columns as $\varnothing \oplus C_0$; the first column block uses `Fin 0` as a placeholder, so
that the block calculus matches the other three differentials).

This term does not fit in `mappingCone` (a four-term structure), yet it **must** exist: the
$H^0$ of the cone is $\ker d^0_{\mathrm{cone}} / \mathrm{im}\,d^{-1}_{\mathrm{cone}}$, and
dropping it makes $H^0$ larger. -/
def coneDm1 (F : CochainMap C D) : Matrix (D₀ ⊕ C₁) (Fin 0 ⊕ C₀) (ZMod 2) :=
  Matrix.fromBlocks 0 F.F0 0 (-C.d0)

/-- **The $0$ differential of the cone**
$d^0_{\mathrm{cone}} : D_0 \oplus C_1 \to D_1 \oplus C_2$:
$\begin{pmatrix} d^D_0 & F_1 \\ 0 & -d^C_1\end{pmatrix}$. -/
def coneD0 (F : CochainMap C D) : Matrix (D₁ ⊕ C₂) (D₀ ⊕ C₁) (ZMod 2) :=
  Matrix.fromBlocks D.d0 F.F1 0 (-C.d1)

/-- **The $1$ differential of the cone**
$d^1_{\mathrm{cone}} : D_1 \oplus C_2 \to D_2 \oplus C_3$:
$\begin{pmatrix} d^D_1 & F_2 \\ 0 & -d^C_2\end{pmatrix}$. -/
def coneD1 (F : CochainMap C D) : Matrix (D₂ ⊕ C₃) (D₁ ⊕ C₂) (ZMod 2) :=
  Matrix.fromBlocks D.d1 F.F2 0 (-C.d2)

/-- **The $2$ differential of the cone**
$d^2_{\mathrm{cone}} : D_2 \oplus C_3 \to D_3 \oplus \varnothing$:
$\begin{pmatrix} d^D_2 & F_3 \\ 0 & 0\end{pmatrix}$. The lower-right block is $0$ ($C_4 = 0$).

The last term is written `D₃ ⊕ Fin 0` (rather than `D₃`) so that the three differentials have
**one and the same block shape**, and the complex conditions can all be expanded mechanically
with `Matrix.fromBlocks_multiply`; `Fin 0` is an empty index and changes no dimension
(`finrank_cone3`). -/
def coneD2 (F : CochainMap C D) : Matrix (D₃ ⊕ Fin 0) (D₂ ⊕ C₃) (ZMod 2) :=
  Matrix.fromBlocks D.d2 F.F3 0 0

/-- **The cone is a complex (the first composite)**:
$d^0_{\mathrm{cone}} d^{-1}_{\mathrm{cone}} = 0$.

This is the statement that $d^{-1}_{\mathrm{cone}}$ is compatible with the other
differentials, and it must be given separately from `mappingCone` (which has only four
terms): the commuting square it uses is `comm_d0`, and the complex condition it uses is
`C.comp_d1_d0`. -/
theorem cone_d0_comp_dm1 (F : CochainMap C D) : coneD0 F * coneDm1 F = 0 := by
  have hc0 : coneD0 F
      = Matrix.fromBlocks D.d0 F.F1 (0 : Matrix C₂ D₀ (ZMod 2)) (-C.d1) := rfl
  have hcm : coneDm1 F
      = Matrix.fromBlocks (0 : Matrix D₀ (Fin 0) (ZMod 2)) F.F0
          (0 : Matrix C₁ (Fin 0) (ZMod 2)) (-C.d0) := rfl
  have h00 : D.d0 * (0 : Matrix D₀ (Fin 0) (ZMod 2))
      + F.F1 * (0 : Matrix C₁ (Fin 0) (ZMod 2)) = 0 := by
    rw [Matrix.mul_zero, Matrix.mul_zero, add_zero]
  have h01 : D.d0 * F.F0 + F.F1 * (-C.d0) = 0 := by
    rw [Matrix.mul_neg, F.comm_d0, add_neg_cancel]
  have h10 : (0 : Matrix C₂ D₀ (ZMod 2)) * (0 : Matrix D₀ (Fin 0) (ZMod 2))
      + (-C.d1) * (0 : Matrix C₁ (Fin 0) (ZMod 2)) = 0 := by
    rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  have h11 : (0 : Matrix C₂ D₀ (ZMod 2)) * F.F0 + (-C.d1) * (-C.d0) = 0 := by
    rw [Matrix.zero_mul, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg, C.comp_d1_d0]
  rw [hc0, hcm, Matrix.fromBlocks_multiply, h00, h01, h10, h11]
  exact Matrix.fromBlocks_zero

/-- **The cone is a complex (the second composite)**:
$d^1_{\mathrm{cone}} d^0_{\mathrm{cone}} = 0$.

The three blocks vanish respectively: upper-left from $d^D_1 d^D_0 = 0$, upper-right from
the commuting square `comm_d1` ($d^D_1 F_1 = F_2 d^C_1$), lower-right from
$d^C_2 d^C_1 = 0$. -/
theorem cone_d1_comp_d0 (F : CochainMap C D) : coneD1 F * coneD0 F = 0 := by
  have hc1 : coneD1 F
      = Matrix.fromBlocks D.d1 F.F2 (0 : Matrix C₃ D₁ (ZMod 2)) (-C.d2) := rfl
  have hc0 : coneD0 F
      = Matrix.fromBlocks D.d0 F.F1 (0 : Matrix C₂ D₀ (ZMod 2)) (-C.d1) := rfl
  have h00 : D.d1 * D.d0 + F.F2 * (0 : Matrix C₂ D₀ (ZMod 2)) = 0 := by
    rw [Matrix.mul_zero, add_zero, D.comp_d1_d0]
  have h01 : D.d1 * F.F1 + F.F2 * (-C.d1) = 0 := by
    rw [Matrix.mul_neg, F.comm_d1, add_neg_cancel]
  have h10 : (0 : Matrix C₃ D₁ (ZMod 2)) * D.d0
      + (-C.d2) * (0 : Matrix C₂ D₀ (ZMod 2)) = 0 := by
    rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  have h11 : (0 : Matrix C₃ D₁ (ZMod 2)) * F.F1 + (-C.d2) * (-C.d1) = 0 := by
    rw [Matrix.zero_mul, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg, C.comp_d2_d1]
  rw [hc1, hc0, Matrix.fromBlocks_multiply, h00, h01, h10, h11]
  exact Matrix.fromBlocks_zero

/-- **The cone is a complex (the third composite)**:
$d^2_{\mathrm{cone}} d^1_{\mathrm{cone}} = 0$.

Upper-left from $d^D_2 d^D_1 = 0$, upper-right from the commuting square `comm_d2`
($d^D_2 F_2 = F_3 d^C_2$), the bottom row from the $0$ of the lower-left block and the
lower-right zero block of $d^2_{\mathrm{cone}}$. -/
theorem cone_d2_comp_d1 (F : CochainMap C D) : coneD2 F * coneD1 F = 0 := by
  have hc2 : coneD2 F
      = Matrix.fromBlocks D.d2 F.F3 (0 : Matrix (Fin 0) D₂ (ZMod 2)) (0 : Matrix (Fin 0) C₃ (ZMod 2))
      := rfl
  have hc1 : coneD1 F
      = Matrix.fromBlocks D.d1 F.F2 (0 : Matrix C₃ D₁ (ZMod 2)) (-C.d2) := rfl
  have h00 : D.d2 * D.d1 + F.F3 * (0 : Matrix C₃ D₁ (ZMod 2)) = 0 := by
    rw [Matrix.mul_zero, add_zero, D.comp_d2_d1]
  have h01 : D.d2 * F.F2 + F.F3 * (-C.d2) = 0 := by
    rw [Matrix.mul_neg, F.comm_d2, add_neg_cancel]
  have h10 : (0 : Matrix (Fin 0) D₂ (ZMod 2)) * D.d1
      + (0 : Matrix (Fin 0) C₃ (ZMod 2)) * (0 : Matrix C₃ D₁ (ZMod 2)) = 0 := by
    rw [Matrix.zero_mul, Matrix.zero_mul, add_zero]
  have h11 : (0 : Matrix (Fin 0) D₂ (ZMod 2)) * F.F2
      + (0 : Matrix (Fin 0) C₃ (ZMod 2)) * (-C.d2) = 0 := by
    rw [Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [hc2, hc1, Matrix.fromBlocks_multiply, h00, h01, h10, h11]
  exact Matrix.fromBlocks_zero

/-- **The mapping cone (nonnegative part)**: the degrees $0..3$ of $\mathrm{cone}(F)$ packed
into one `Cochain4`.

Its three terms are `coneD0/coneD1/coneD2`, and its two complex conditions are
`cone_d1_comp_d0` and `cone_d2_comp_d1`. The degree of $C_0$ (the $-1$ degree) is not among
them — see item 4 of §4 of the module header and `coneDm1`. -/
def mappingCone (F : CochainMap C D) :
    Cochain4 (D₀ ⊕ C₁) (D₁ ⊕ C₂) (D₂ ⊕ C₃) (D₃ ⊕ Fin 0) where
  d0 := coneD0 F
  d1 := coneD1 F
  d2 := coneD2 F
  comp_d1_d0 := cone_d1_comp_d0 F
  comp_d2_d1 := cone_d2_comp_d1 F

/-! ## 4. The short exact sequence and the connecting homomorphism -/

/-- **The inclusion of the short exact sequence**
$\iota : D^n \to \mathrm{cone}^n = D^n \oplus C^{n+1}$, $d \mapsto (d, 0)$ (that is,
`Sum.elim d 0`). -/
def inclLin (A B : Type*) [Fintype A] [Fintype B] :
    (A → ZMod 2) →ₗ[ZMod 2] (A ⊕ B → ZMod 2) where
  toFun d := Sum.elim d 0
  map_add' d d' := by funext i; rcases i with a | b <;> rfl
  map_smul' c d := by funext i; rcases i with a | b <;> rfl

/-- **The projection of the short exact sequence**
$\pi : \mathrm{cone}^n = D^n \oplus C^{n+1} \to C^{n+1}$, $(d, c) \mapsto c$ (that is,
taking the `Sum.inr` component). -/
def projLin (A B : Type*) [Fintype A] [Fintype B] :
    (A ⊕ B → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2) where
  toFun x := fun b => x (Sum.inr b)
  map_add' x y := by funext b; rfl
  map_smul' c x := by funext b; rfl

/-- **$\mathrm{im} \subseteq \ker$**: $\pi \circ \iota = 0$ (that one step of the short exact
sequence). -/
theorem proj_comp_incl (A B : Type*) [Fintype A] [Fintype B] :
    (projLin A B).comp (inclLin A B) = 0 := by
  ext d b
  rfl

/-- **Exactness in the middle**: $\ker \pi = \mathrm{im}\,\iota$ — the image of the inclusion
is exactly the kernel of the projection.

This machine-checks the **exactness in the middle** of
$0 \to D^n \xrightarrow{\iota} \mathrm{cone}^n \xrightarrow{\pi} C^{n+1} \to 0$:
$\mathrm{im}\,\iota \subseteq \ker\pi$ is given by `proj_comp_incl`, and the reverse
inclusion comes from "$\pi x = 0 \Rightarrow x$ lives only on the $D^n$ side". -/
theorem ker_projLin_eq_range_inclLin (A B : Type*) [Fintype A] [Fintype B] :
    LinearMap.ker (projLin A B) = LinearMap.range (inclLin A B) := by
  ext x
  constructor
  · intro hx
    refine ⟨fun a => x (Sum.inl a), ?_⟩
    funext i
    rcases i with a | b
    · rfl
    · have hb : x (Sum.inr b) = 0 := congrFun hx b
      rw [hb]
      rfl
  · rintro ⟨d, rfl⟩
    funext b
    rfl

/-- **The inclusion is injective** (exactness at the left end of the short exact sequence). -/
theorem inclLin_injective (A B : Type*) [Fintype A] [Fintype B] :
    Function.Injective (inclLin A B) := by
  intro d d' h
  funext a
  exact congrFun h (Sum.inl a)

/-- **The projection is surjective** (exactness at the right end of the short exact
sequence). -/
theorem projLin_surjective (A B : Type*) [Fintype A] [Fintype B] :
    Function.Surjective (projLin A B) := by
  intro c
  refine ⟨Sum.elim 0 c, ?_⟩
  funext b
  rfl

/-- **The inclusion commutes with the differentials of the cone (degree $-1 \to 0$)** — the
degree of $C_0$ also matches (the inclusion is the identity in degree $-1$ and $\iota$ in
degree $0$). -/
theorem coneD0_incl (F : CochainMap C D) (d : D₀ → ZMod 2) :
    coneD0 F *ᵥ (Sum.elim d (0 : C₁ → ZMod 2)) = Sum.elim (D.d0 *ᵥ d) 0 := by
  have hc0 : coneD0 F
      = Matrix.fromBlocks D.d0 F.F1 (0 : Matrix C₂ D₀ (ZMod 2)) (-C.d1) := rfl
  have hi : (Sum.elim d (0 : C₁ → ZMod 2)) ∘ Sum.inl = d := by funext a; rfl
  have hj : (Sum.elim d (0 : C₁ → ZMod 2)) ∘ Sum.inr = (0 : C₁ → ZMod 2) := by
    funext c; rfl
  rw [hc0, Matrix.fromBlocks_mulVec, hi, hj]
  simp

/-- **The inclusion commutes with the differentials of the cone (degree $0 \to 1$)**:
$\iota \circ d^D_0 = d^{\mathrm{cone}}_0 \circ \iota$ — that is, the inclusion is a cochain
map, and it is the source of $H^n(D) \to H^n(\mathrm{cone})$. -/
theorem coneD1_incl (F : CochainMap C D) (d : D₁ → ZMod 2) :
    coneD1 F *ᵥ (Sum.elim d (0 : C₂ → ZMod 2)) = Sum.elim (D.d1 *ᵥ d) 0 := by
  have hc1 : coneD1 F
      = Matrix.fromBlocks D.d1 F.F2 (0 : Matrix C₃ D₁ (ZMod 2)) (-C.d2) := rfl
  have hi : (Sum.elim d (0 : C₂ → ZMod 2)) ∘ Sum.inl = d := by funext a; rfl
  have hj : (Sum.elim d (0 : C₂ → ZMod 2)) ∘ Sum.inr = (0 : C₂ → ZMod 2) := by
    funext c; rfl
  rw [hc1, Matrix.fromBlocks_mulVec, hi, hj]
  simp

/-- **The inclusion commutes with the differentials of the cone (degree $1 \to 2$)**. -/
theorem coneD2_incl (F : CochainMap C D) (d : D₂ → ZMod 2) :
    coneD2 F *ᵥ (Sum.elim d (0 : C₃ → ZMod 2))
      = Sum.elim (D.d2 *ᵥ d) (0 : Fin 0 → ZMod 2) := by
  have hc2 : coneD2 F
      = Matrix.fromBlocks D.d2 F.F3 (0 : Matrix (Fin 0) D₂ (ZMod 2)) (0 : Matrix (Fin 0) C₃ (ZMod 2))
      := rfl
  have hi : (Sum.elim d (0 : C₃ → ZMod 2)) ∘ Sum.inl = d := by funext a; rfl
  have hj : (Sum.elim d (0 : C₃ → ZMod 2)) ∘ Sum.inr = (0 : C₃ → ZMod 2) := by
    funext c; rfl
  rw [hc2, Matrix.fromBlocks_mulVec, hi, hj]
  simp

/-- **The projection commutes with the differentials of the cone (degree $0 \to 1$)**:
$\pi \circ d^{\mathrm{cone}}_0 = d^C_1 \circ \pi$ — the projection is a cochain map onto
$C[1]$. (The step $-d^C_1 = d^C_1$ over $\mathbb F_2$ is written out explicitly.) -/
theorem coneD0_proj (F : CochainMap C D) (x : D₀ ⊕ C₁ → ZMod 2) :
    projLin D₁ C₂ (coneD0 F *ᵥ x) = C.d1 *ᵥ projLin D₀ C₁ x := by
  have hc0 : coneD0 F
      = Matrix.fromBlocks D.d0 F.F1 (0 : Matrix C₂ D₀ (ZMod 2)) (-C.d1) := rfl
  have hproj : ∀ (u : D₁ → ZMod 2) (v : C₂ → ZMod 2), projLin D₁ C₂ (Sum.elim u v) = v :=
    fun u v => rfl
  have hv : x ∘ Sum.inr = projLin D₀ C₁ x := by funext c; rfl
  rw [hc0, Matrix.fromBlocks_mulVec, hproj, hv, Matrix.neg_mulVec]
  rw [Matrix.zero_mulVec, zero_add]
  funext c
  exact ZMod.neg_eq_self_mod_two _

/-- **The projection commutes with the differentials of the cone (degree $1 \to 2$)**. -/
theorem coneD1_proj (F : CochainMap C D) (x : D₁ ⊕ C₂ → ZMod 2) :
    projLin D₂ C₃ (coneD1 F *ᵥ x) = C.d2 *ᵥ projLin D₁ C₂ x := by
  have hc1 : coneD1 F
      = Matrix.fromBlocks D.d1 F.F2 (0 : Matrix C₃ D₁ (ZMod 2)) (-C.d2) := rfl
  have hproj : ∀ (u : D₂ → ZMod 2) (v : C₃ → ZMod 2), projLin D₂ C₃ (Sum.elim u v) = v :=
    fun u v => rfl
  have hv : x ∘ Sum.inr = projLin D₁ C₂ x := by funext c; rfl
  rw [hc1, Matrix.fromBlocks_mulVec, hproj, hv, Matrix.neg_mulVec]
  rw [Matrix.zero_mulVec, zero_add]
  funext c
  exact ZMod.neg_eq_self_mod_two _

/-- **The connecting homomorphism is $F$ (degree $0 \to 1$)**: for $x \in \ker d^C_1$, one
lift of it in degree $0$ of the cone is $(0, x)$ (written here as `Sum.elim 0 x`); then

$$d^0_{\mathrm{cone}}\,(0,x) = (F_1 x,\; 0) = \iota(F_1 x).$$

This is the **defining fact** of the Snake connecting homomorphism $H^1(C) \to H^1(D)$: it
is induced by $F_1$. The $C$ half on the left is $-d^C_1 x = 0$ (the hypothesis
$x \in \ker d^C_1$), and this is the whole content of "the connecting homomorphism is
well-defined". -/
theorem connectingMap_coneD0 (F : CochainMap C D) (x : C₁ → ZMod 2)
    (hx : C.d1 *ᵥ x = 0) :
    coneD0 F *ᵥ (Sum.elim (0 : D₀ → ZMod 2) x) = Sum.elim (F.F1 *ᵥ x) (0 : C₂ → ZMod 2) := by
  have hc0 : coneD0 F
      = Matrix.fromBlocks D.d0 F.F1 (0 : Matrix C₂ D₀ (ZMod 2)) (-C.d1) := rfl
  have hi : (Sum.elim (0 : D₀ → ZMod 2) x) ∘ Sum.inl = (0 : D₀ → ZMod 2) := by funext a; rfl
  have hj : (Sum.elim (0 : D₀ → ZMod 2) x) ∘ Sum.inr = x := by funext c; rfl
  rw [hc0, Matrix.fromBlocks_mulVec, hi, hj]
  simp [Matrix.neg_mulVec, hx]

/-- **The connecting homomorphism is $F$ (degree $1 \to 2$)**: for $x \in \ker d^C_2$,
$d^1_{\mathrm{cone}}(0,x) = (F_2 x, 0)$. -/
theorem connectingMap_coneD1 (F : CochainMap C D) (x : C₂ → ZMod 2)
    (hx : C.d2 *ᵥ x = 0) :
    coneD1 F *ᵥ (Sum.elim (0 : D₁ → ZMod 2) x) = Sum.elim (F.F2 *ᵥ x) (0 : C₃ → ZMod 2) := by
  have hc1 : coneD1 F
      = Matrix.fromBlocks D.d1 F.F2 (0 : Matrix C₃ D₁ (ZMod 2)) (-C.d2) := rfl
  have hi : (Sum.elim (0 : D₁ → ZMod 2) x) ∘ Sum.inl = (0 : D₁ → ZMod 2) := by funext a; rfl
  have hj : (Sum.elim (0 : D₁ → ZMod 2) x) ∘ Sum.inr = x := by funext c; rfl
  rw [hc1, Matrix.fromBlocks_mulVec, hi, hj]
  simp [Matrix.neg_mulVec, hx]

/-! ## 5. The dimension formulas on the homology side

On a finite-dimensional $\mathbb F_2$ vector space, $\dim H^n = \dim Z^n - \dim B^n$, where
$Z^n = \ker d_n$ and $B^n = \mathrm{im}\,d_{n-1}$. This section gives (i) the dimension
decomposition of each term (the dimension identities of the short exact sequence) and (ii)
the rank-nullity of cohomology.

Dimensions are throughout converted via `Module.finrank_fintype_fun_eq_card`
($\dim(\eta \to \mathbb F_2) = |\eta|$), so the dimension of a block term is given by
`Fintype.card_sum`. -/

/-- The **cycles** of a cochain complex `K` in degree $0$: $Z^0 = \ker d_0$. -/
def cycles0 (K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₀ → ZMod 2) :=
  LinearMap.ker K.d0.mulVecLin

/-- The **boundaries** of a cochain complex `K` in degree $1$: $B^1 = \mathrm{im}\,d_0$. -/
def bounds1 (K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₁ → ZMod 2) :=
  LinearMap.range K.d0.mulVecLin

/-- The **cycles** of a cochain complex `K` in degree $1$: $Z^1 = \ker d_1$. -/
def cycles1 (K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₁ → ZMod 2) :=
  LinearMap.ker K.d1.mulVecLin

/-- The **boundaries** of a cochain complex `K` in degree $2$: $B^2 = \mathrm{im}\,d_1$. -/
def bounds2 (K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₂ → ZMod 2) :=
  LinearMap.range K.d1.mulVecLin

/-- The **cycles** of a cochain complex `K` in degree $2$: $Z^2 = \ker d_2$. -/
def cycles2 (K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₂ → ZMod 2) :=
  LinearMap.ker K.d2.mulVecLin

/-- The **boundaries** of a cochain complex `K` in degree $3$: $B^3 = \mathrm{im}\,d_2$. -/
def bounds3 (K : Cochain4 C₀ C₁ C₂ C₃) : Submodule (ZMod 2) (C₃ → ZMod 2) :=
  LinearMap.range K.d2.mulVecLin

/-- **$B^1 \subseteq Z^1$**: an equivalent way of stating the complex condition
$d_1 d_0 = 0$ — a boundary is always a cycle. (This is exactly why the complex exists, and
the prerequisite for $H^1$ to be definable.) -/
theorem bounds1_le_cycles1 (K : Cochain4 C₀ C₁ C₂ C₃) : bounds1 K ≤ cycles1 K := by
  rintro x ⟨y, rfl⟩
  show K.d1.mulVecLin (K.d0.mulVecLin y) = 0
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, K.comp_d1_d0,
    Matrix.zero_mulVec]

/-- **$B^2 \subseteq Z^2$**. -/
theorem bounds2_le_cycles2 (K : Cochain4 C₀ C₁ C₂ C₃) : bounds2 K ≤ cycles2 K := by
  rintro x ⟨y, rfl⟩
  show K.d2.mulVecLin (K.d1.mulVecLin y) = 0
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, K.comp_d2_d1,
    Matrix.zero_mulVec]

/-- **The dimension identity of the short exact sequence (degree $0$ of the cone)**:
$\dim(D_0 \oplus C_1) = \dim D_0 + \dim C_1$. -/
theorem finrank_cone0 :
    Module.finrank (ZMod 2) (D₀ ⊕ C₁ → ZMod 2)
      = Module.finrank (ZMod 2) (D₀ → ZMod 2) + Module.finrank (ZMod 2) (C₁ → ZMod 2) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum]

/-- **The dimension identity of the short exact sequence (degree $1$ of the cone)**. -/
theorem finrank_cone1 :
    Module.finrank (ZMod 2) (D₁ ⊕ C₂ → ZMod 2)
      = Module.finrank (ZMod 2) (D₁ → ZMod 2) + Module.finrank (ZMod 2) (C₂ → ZMod 2) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum]

/-- **The dimension identity of the short exact sequence (degree $2$ of the cone)**. -/
theorem finrank_cone2 :
    Module.finrank (ZMod 2) (D₂ ⊕ C₃ → ZMod 2)
      = Module.finrank (ZMod 2) (D₂ → ZMod 2) + Module.finrank (ZMod 2) (C₃ → ZMod 2) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum]

/-- **The dimension identity of the short exact sequence (degree $3$ of the cone)**: the
last term is written `D₃ ⊕ Fin 0`, `Fin 0` contributes no dimension, so this statement is
just $\dim D_3$ itself. -/
theorem finrank_cone3 :
    Module.finrank (ZMod 2) (D₃ ⊕ Fin 0 → ZMod 2) = Module.finrank (ZMod 2) (D₃ → ZMod 2) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin, add_zero]

/-- **$B^1$ and its pullback in $Z^1$ have the same dimension**: the quotient in
`Submodule.finrank_quotient_add_finrank` is taken over "a submodule of $Z^1$", so
`finrank ↥B¹` has to be replaced by `finrank ↥(B¹.comap Z¹.subtype)`, the bridge being
`Submodule.comapSubtypeEquivOfLe`. -/
theorem finrank_comap_bounds1 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) ↥((bounds1 K).comap (cycles1 K).subtype)
      = Module.finrank (ZMod 2) ↥(bounds1 K) :=
  (Submodule.comapSubtypeEquivOfLe (bounds1_le_cycles1 K)).finrank_eq

/-- **$B^2$ and its pullback in $Z^2$ have the same dimension**. -/
theorem finrank_comap_bounds2 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) ↥((bounds2 K).comap (cycles2 K).subtype)
      = Module.finrank (ZMod 2) ↥(bounds2 K) :=
  (Submodule.comapSubtypeEquivOfLe (bounds2_le_cycles2 K)).finrank_eq

/-- **The rank-nullity of cohomology ($H^1$)**: $\dim H^1 + \dim B^1 = \dim Z^1$, where
$H^1 := Z^1/B^1$, $Z^1 = \ker d_1$ and $B^1 = \mathrm{im}\,d_0$.

This is the machine-checked form of $\dim H^1 = \dim Z^1 - \dim B^1$
(`Submodule.finrank_quotient_add_finrank`). -/
theorem finrank_H1 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (↥(cycles1 K) ⧸ (bounds1 K).comap (cycles1 K).subtype)
        + Module.finrank (ZMod 2) ↥((bounds1 K).comap (cycles1 K).subtype)
      = Module.finrank (ZMod 2) ↥(cycles1 K) :=
  Submodule.finrank_quotient_add_finrank _

/-- **The rank-nullity of cohomology ($H^2$)**. -/
theorem finrank_H2 (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (↥(cycles2 K) ⧸ (bounds2 K).comap (cycles2 K).subtype)
        + Module.finrank (ZMod 2) ↥((bounds2 K).comap (cycles2 K).subtype)
      = Module.finrank (ZMod 2) ↥(cycles2 K) :=
  Submodule.finrank_quotient_add_finrank _

/-- **The explicit form of the cohomology dimension ($H^1$)**: $\dim H^1 = \dim Z^1 - \dim B^1$. -/
theorem finrank_H1_eq (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (↥(cycles1 K) ⧸ (bounds1 K).comap (cycles1 K).subtype)
      = Module.finrank (ZMod 2) ↥(cycles1 K) - Module.finrank (ZMod 2) ↥(bounds1 K) := by
  have h := finrank_H1 K
  rw [finrank_comap_bounds1 K] at h
  omega

/-- **The explicit form of the cohomology dimension ($H^2$)**: $\dim H^2 = \dim Z^2 - \dim B^2$. -/
theorem finrank_H2_eq (K : Cochain4 C₀ C₁ C₂ C₃) :
    Module.finrank (ZMod 2) (↥(cycles2 K) ⧸ (bounds2 K).comap (cycles2 K).subtype)
      = Module.finrank (ZMod 2) ↥(cycles2 K) - Module.finrank (ZMod 2) ↥(bounds2 K) := by
  have h := finrank_H2 K
  rw [finrank_comap_bounds2 K] at h
  omega

/-! ### Division of labour (the content is in `Homology/MappingConeSnake.lean`)

The **complete** dimension formula of the Snake long exact sequence of [14] Appendix A.1

$$\dim H^n(\mathrm{cone}(F)) = \dim H^n(D) + \dim H^{n+1}(C)
  - \dim \mathrm{im}\,H^n(F) - \dim \mathrm{im}\,H^{n+1}(F)$$

is **not** formalized in this module; this section gives the three things that are done:
$\delta_n$ **is $F$** (`connectingMap_coneD0` / `connectingMap_coneD1`), the short exact
sequence **is exact** (`proj_comp_incl`, `ker_projLin_eq_range_inclLin`, `inclLin_injective`,
`projLin_surjective`), and the rank-nullity of cohomology (`finrank_H1_eq` / `finrank_H2_eq`);
it also names the missing step as **the induced map on the quotient space** (the lemma that
$F$ sends $B$ into $B$ + `Submodule.mapQ`).

**That gap is closed in `Homology/MappingConeSnake.lean`**: there $H^m(F) : H^m(C) \to
H^m(D)$ is defined (via `Submodule.mapQ`) and proved well-defined, the three identities
(F)(B)(S) and the dimension bridge are given, and finally the formulas for the four degrees
$n = 0,1,2,3$ are proved point by point. This module does **not** repeat that conclusion, nor
does it treat the theorems of `MappingConeSnake.lean` as this module's conclusions; the
division is "this module gives the cone and the short exact sequence, the Snake module gives
the dimension reading". -/

end QECCertificates.Homology
