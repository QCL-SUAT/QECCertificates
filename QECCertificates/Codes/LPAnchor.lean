/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.CaseMatrix
import QECCertificates.GF2.RankEchelon
import QECCertificates.GF2.LiftedProduct

/-!
# Lifted-product anchor: the 2BGA instances over $D_6$ (lifted-product family)

`GF2/LiftedProduct.lean` gives the general definition of the lifted product and its
structural theorems ($H_XH_Z^{\top} = 0$, and the degeneration to the HGP). This module
**instantiates** the construction on a table from the literature and records the
**parameters checked by the kernel**, following the three-step template of
`Codes/CaseMatrix.lean`.

## The literature row that is reproduced

Lin–Pryadko, *Quantum two-block group algebra codes*, PRA **109**, 022407 (2024),
DOI `10.1103/PhysRevA.109.022407`; **Table III of Appendix C of the published version** (the
two pages of seeds and $(k,d)$ were read against the published version word by word, and agree
with the same table of preprint v1), the $m = 6$ row:
the group $D_6 = \langle r,s \mid r^6 = s^2 = (rs)^2 = 1\rangle$ (12 elements), $n = 4m = 24$,
the two parameter pairs $(k, d) = (8, 3)$ and $(12, 2)$, with seeds

| instance | $k$ | $d$ | $a$ | $b$ |
|---|---|---|---|---|
| instance 1 | 8 | 3 | $1 + r^4$ | $1 + sr^4 + r^3 + r^4 + sr^2 + r$ |
| instance 2 | 12 | 2 | $1 + r^3$ | $1 + sr + r^3 + r^4 + sr^4 + r$ |

(The convention of that table: $W_a = 2$, $W_b = 6$, and every row satisfies $kd = n$.)

## The assertions established here (all by the kernel, through `by decide`)

* `lpAnchorHx` / `lpAnchorHz`: obtained from the **LP construction** (a 1 x 1 seed, that is, a
  2BGA) by relabelling the element numbering (`d6Equiv` numbers the 12 group elements `0..11`;
  columns are numbered "left block 0..11, right block 12..23");
* `lpAnchor_css`: $H_XH_Z^{\top} = 0$ (an instance of the general theorem `lp2_orthogonal`);
* `lpAnchor_k` / `lpAnchor2_k`: the dimension $k$ computed directly by row reduction (through
  the append-only echelon back end `rankEchelon`);
* `lpAnchor_dx` / `lpAnchor_dz` (and the two for instance 2): the distance is **exactly** $d$.
  The lower bound is given by an empty weight-limited candidate list (`lpAnchor_lowerHyp`,
  mirroring the arrangement of `lowerHyp_of_lightCand_nil` but running on the echelon back end
  `inSpanEch`), and the upper bound by an **explicit low-weight logical operator**.

## Relation to the numerical side (a second, independent route)

An independent Python implementation of the same route (the same group, the same seed, the same
element order and column order) recomputes the whole chain: $H_XH_Z^{\top}=0$,
`k = n - rank H_X - rank H_Z`, an empty weight-limited enumeration (lower bound), and an
explicit witness paired with a dual witness to give 1 (upper bound). It obtains the same
readings (instance 1: $n=24,k=8,d_X=d_Z=3$; instance 2: $n=24,k=12,d_X=d_Z=2$, with witness
column sets `{0,2,4}` and `{0,3}` respectively). The parts of this that the kernel can decide
are raised here to machine-checked assertions: the two routes corroborate each other, but only
the kernel side enters the trusted base.
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## 1. Numbering the elements of $D_6$ -/

/-- The elements of $D_6$ are numbered `0..11` as `r^0..r^5, sr^0..sr^5`. -/
def d6Code (x : DihedralGroup 6) : Fin 12 :=
  match x with
  | .r i => ⟨i.val, by have h := ZMod.val_lt i; omega⟩
  | .sr i => ⟨6 + i.val, by have h := ZMod.val_lt i; omega⟩

/-- The inverse of `d6Code` (it uses only the natural-number conversion of `ZMod` and does not construct a `Fin`). -/
def d6Index (k : Fin 12) : DihedralGroup 6 :=
  if (k : ℕ) < 6 then DihedralGroup.r (((k : ℕ) : ZMod 6))
  else DihedralGroup.sr ((((k : ℕ) - 6 : ℕ)) : ZMod 6)

theorem d6Index_code : Function.LeftInverse d6Index d6Code := by decide

theorem d6Code_index : Function.RightInverse d6Index d6Code := by decide

/-- Relabelling of the row indices: $D_6 \simeq \{0,\dots,11\}$. -/
def d6Equiv : DihedralGroup 6 ≃ Fin 12 where
  toFun := d6Code
  invFun := d6Index
  left_inv := d6Index_code
  right_inv := d6Code_index

/-- Relabelling of the column indices: the two $D_6$ blocks $\simeq \{0,\dots,23\}$ (**left block 0..11, right block 12..23**). -/
def d6ColEquiv : (DihedralGroup 6 ⊕ DihedralGroup 6) ≃ Fin 24 :=
  (Equiv.sumCongr d6Equiv d6Equiv).trans finSumFinEquiv

/-- The group-algebra element $\sum_{g \in s} g$ (coefficient 1 on $s$). -/
def gsum (s : Finset (DihedralGroup 6)) : DihedralGroup 6 → ZMod 2 :=
  fun g => if g ∈ s then 1 else 0

/-! ## 2. Instance 1: seeds $a = 1 + r^4$, $b = 1 + sr^4 + r^3 + r^4 + sr^2 + r$ -/

/-- The seed of instance 1: $a = 1 + r^4$. -/
def lpSeedA : DihedralGroup 6 → ZMod 2 := gsum {(1 : DihedralGroup 6), DihedralGroup.r 4}

/-- The seed of instance 1: $b = 1 + sr^4 + r^3 + r^4 + sr^2 + r$. -/
def lpSeedB : DihedralGroup 6 → ZMod 2 :=
  gsum {(1 : DihedralGroup 6), DihedralGroup.r 1, DihedralGroup.r 3, DihedralGroup.r 4,
    DihedralGroup.sr 2, DihedralGroup.sr 4}

/-- The X-type checks of instance 1: the LP construction (a 1 x 1 seed) relabelled by element numbering to `Fin 12 x Fin 24`. -/
def lpAnchorHx : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HX lpSeedA lpSeedB)

/-- The Z-type checks of instance 1. -/
def lpAnchorHz : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HZ lpSeedA lpSeedB)

/--
**The anchor identity (CSS compatibility)**: the identity $H_XH_Z^{\top} = 0$ of the LP construction holds on the instance (an instantiation of the general theorem `lp2_orthogonal`).
-/
theorem lpAnchor_css : lpAnchorHx * (lpAnchorHz).transpose = 0 := by decide

/-- The X-type witness of instance 1: a weight-3 logical operator (columns `0, 2, 4`, that is, $r^0, r^2, r^4$ of the left block). -/
def lpXW : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-- The X-type dual witness of instance 1 (it pairs with `lpXW` to give 1 and lies in the kernel of $H_Z$). -/
def lpXWdual : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-- The Z-type witness of instance 1. -/
def lpZW : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-- The Z-type dual witness of instance 1. -/
def lpZWdual : Vec 24 := (e 0 + e 2 + e 4 : Vec 24)

/-! ## 3. Instance 2: seeds $a = 1 + r^3$, $b = 1 + sr + r^3 + r^4 + sr^4 + r$ -/

/-- The seed of instance 2: $a = 1 + r^3$. -/
def lpSeed2A : DihedralGroup 6 → ZMod 2 := gsum {(1 : DihedralGroup 6), DihedralGroup.r 3}

/-- The seed of instance 2: $b = 1 + sr + r^3 + r^4 + sr^4 + r$. -/
def lpSeed2B : DihedralGroup 6 → ZMod 2 :=
  gsum {(1 : DihedralGroup 6), DihedralGroup.r 1, DihedralGroup.r 3, DihedralGroup.r 4,
    DihedralGroup.sr 1, DihedralGroup.sr 4}

/-- The X-type checks of instance 2. -/
def lpAnchor2Hx : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HX lpSeed2A lpSeed2B)

/-- The Z-type checks of instance 2. -/
def lpAnchor2Hz : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  (Matrix.reindex d6Equiv d6ColEquiv) (lp2HZ lpSeed2A lpSeed2B)

/-- **The anchor identity (CSS compatibility)**, instance 2. -/
theorem lpAnchor2_css : lpAnchor2Hx * (lpAnchor2Hz).transpose = 0 := by decide

/-- The X-type witness of instance 2: weight 2 (columns `0, 3`). -/
def lp2XW : Vec 24 := (e 0 + e 3 : Vec 24)

def lp2XWdual : Vec 24 := (e 0 + e 2 + e 6 + e 7 : Vec 24)

def lp2ZW : Vec 24 := (e 0 + e 3 : Vec 24)

def lp2ZWdual : Vec 24 := (e 0 + e 1 + e 7 + e 12 : Vec 24)

/-! ## 4. Dimension: direct row reduction (append-only echelon back end) -/

/--
**The dimension of instance 1**: $24 - 8 - 8 = 8$.

The reduction runs on the append-only echelon form of `GF2/RankEchelon.lean` (at width 24 the
back-substitution of `rowReduce` multiplies its own cost from round to round); the bridge
theorem `rankEchelon_eq_length_rowReduce` guarantees that both give the same rank, so the
statement is still written in the `rowReduce` form.
-/
theorem lpAnchor_k : 24 - (rowReduce (List.ofFn fun i => lpAnchorHx i)).length
    - (rowReduce (List.ofFn fun i => lpAnchorHz i)).length = 8 := by
  simp only [← rankEchelon_eq_length_rowReduce]
  decide

/-- **The dimension of instance 2**: $24 - 6 - 6 = 12$. -/
theorem lpAnchor2_k : 24 - (rowReduce (List.ofFn fun i => lpAnchor2Hx i)).length
    - (rowReduce (List.ofFn fun i => lpAnchor2Hz i)).length = 12 := by
  simp only [← rankEchelon_eq_length_rowReduce]
  decide

/-!
## 5. Distance: an empty weight-limited candidate list implies the lower bound (echelon back end)

The `lightCand` of `GF2/LowerBound.lean` uses `inSpanB` (which runs `rowReduce` internally) and
is too expensive at width 24. Here the **same candidate set** is moved onto `inSpanEch` (the
append-only echelon back end), and the implication "an empty candidate list implies the distance
lower bound" is proved inside this file (mirroring the arrangement of
`lowerHyp_of_lightCand_nil`).
-/

/-- The light-operator predicate (echelon back end): nonzero weight, commuting with `M₁`, and not in the row space of `M₂`. -/
abbrev lpLight {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (v : Vec 24) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧ inSpanEch (List.ofFn fun i => M₂ i) v = false

/-- The set of candidates of weight $\le w$. -/
def lpLightCand (w : ℕ) {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2)) :
    List (Vec 24) :=
  (lightVecs 24 w).filter (fun v => decide (lpLight M₁ M₂ v))

/-- **The lower-bound hypothesis** (mirroring `lowerHyp_of_lightCand_nil`): an empty candidate list at weight $\le d-1$ implies distance $\ge d$. -/
theorem lpAnchor_lowerHyp {m₁ m₂ d : ℕ} (hd : 1 ≤ d)
    (M₁ : Matrix (Fin m₁) (Fin 24) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin 24) (ZMod 2))
    (h : lpLightCand (d - 1) M₁ M₂ = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.rowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.rowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs 24 (d - 1) := by
    refine mem_lightVecs 24 (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lpLightCand (d - 1) M₁ M₂ := by
    unfold lpLightCand
    rw [List.mem_filter]
    refine ⟨hcov, ?_⟩
    rw [decide_eq_true_eq]
    exact ⟨hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanEch_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem

/-- **Lower-bound certificate (instance 1, X side)**: the candidate list at weight $\le 2$ is empty. -/
theorem lpAnchor_lightCand_x : lpLightCand 2 lpAnchorHx lpAnchorHz = [] := by decide

/-- **Lower-bound certificate (instance 1, Z side)**. -/
theorem lpAnchor_lightCand_z : lpLightCand 2 lpAnchorHz lpAnchorHx = [] := by decide

/-- **Lower-bound certificate (instance 2, X side)**: the candidate list at weight $\le 1$ is empty. -/
theorem lpAnchor2_lightCand_x : lpLightCand 1 lpAnchor2Hx lpAnchor2Hz = [] := by decide

/-- **Lower-bound certificate (instance 2, Z side)**. -/
theorem lpAnchor2_lightCand_z : lpLightCand 1 lpAnchor2Hz lpAnchor2Hx = [] := by decide

/-! ## 6. Exact distances -/

/-- **The X-side distance of instance 1 is 3**: the lower-bound candidate list is empty, and the upper bound is an explicit weight-3 logical operator paired with a dual witness. -/
theorem lpAnchor_dx : min_weight_ker_not_mem_rowspace lpAnchorHx lpAnchorHz = 3 :=
  eq_minWeight_of_bounds lpAnchorHx lpAnchorHz (by decide) (E := lpXW)
    (mem_ker_of_inKerB lpAnchorHx (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchorHz (w := lpXWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 3) (by decide) lpAnchorHx lpAnchorHz lpAnchor_lightCand_x)

/-- **The Z-side distance of instance 1 is 3**. -/
theorem lpAnchor_dz : min_weight_ker_not_mem_rowspace lpAnchorHz lpAnchorHx = 3 :=
  eq_minWeight_of_bounds lpAnchorHz lpAnchorHx (by decide) (E := lpZW)
    (mem_ker_of_inKerB lpAnchorHz (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchorHx (w := lpZWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 3) (by decide) lpAnchorHz lpAnchorHx lpAnchor_lightCand_z)

/-- **The X-side distance of instance 2 is 2**. -/
theorem lpAnchor2_dx : min_weight_ker_not_mem_rowspace lpAnchor2Hx lpAnchor2Hz = 2 :=
  eq_minWeight_of_bounds lpAnchor2Hx lpAnchor2Hz (by decide) (E := lp2XW)
    (mem_ker_of_inKerB lpAnchor2Hx (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchor2Hz (w := lp2XWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 2) (by decide) lpAnchor2Hx lpAnchor2Hz lpAnchor2_lightCand_x)

/-- **The Z-side distance of instance 2 is 2**. -/
theorem lpAnchor2_dz : min_weight_ker_not_mem_rowspace lpAnchor2Hz lpAnchor2Hx = 2 :=
  eq_minWeight_of_bounds lpAnchor2Hz lpAnchor2Hx (by decide) (E := lp2ZW)
    (mem_ker_of_inKerB lpAnchor2Hz (by decide))
    (not_mem_rowSpace_of_dualCheck lpAnchor2Hx (w := lp2ZWdual) (by decide) (by decide))
    (by decide)
    (lpAnchor_lowerHyp (d := 2) (by decide) lpAnchor2Hz lpAnchor2Hx lpAnchor2_lightCand_z)

end QECCertificates
