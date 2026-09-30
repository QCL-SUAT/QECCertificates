/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.CaseMatrix
import QECCertificates.Codes.BB18Anchor
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.CSSPair
import QECCertificates.Codes.LPAnchor

/-!
# X and Z distance labels: fixing the convention, and turning two-sided equality into a
machine-checked ledger

The first argument of `min_weight_ker_not_mem_rowspace M₁ M₂` supplies the **kernel** and
the second supplies the **row space**. The difficulty is that there are two readings of
which matrix supplies the kernel, and **the two readings give different numbers whenever the
two sides have unequal distances**:

* **The reading used by this library and by LeanQEC** (`libDX`): `dX` takes the **X-type
  parity-check matrix** as the kernel, that is
  $\min\{\mathrm{wt}(v) : v\in\ker H_X,\ v\notin\mathrm{row}\,H_Z\}$. LeanQEC has
  `CSS_pair.dX = min_weight_ker_not_mem_rowspace C.H₂ C.H₁`, and `CSS_BSM` puts $H_1$ into
  the Z slot and $H_2$ into the X slot (`Z2Z2_Pauli_equiv (1,0) = X`), so $H_1$ is the
  Z-type parity check and $H_2$ the X-type parity check, **the same order as here**.
* **The textbook reading** (`textbookDX`): an X-type logical operator has to commute with
  every Z-type stabilizer, so
  $d_X=\min\{\mathrm{wt}(v):v\in\ker H_Z,\ v\notin\mathrm{row}\,H_X\}$, which takes the
  **Z-type parity check as the kernel**, exactly the other order.

Two `rfl` bridges (`libDX_eq_textbookDZ`, `libDZ_eq_textbookDX`) record this as theorems
rather than as prose: **a `_dx` theorem of this library is numerically the textbook $d_Z$,
and conversely.**

## Why this is harmless, and when it is not

The 19 code instances present in this library have **equal distances on the two sides**
(each line below is machine-checked), so the two readings give the same number and no
published figure is affected. Trouble arises for instances whose **two sides differ**, and
gauging is exactly the kind of construction most likely to break the symmetry. This module
is therefore also a prerequisite for new instances: when writing a gauging instance, always
name `libDX` or `textbookDX` explicitly rather than relying on the name `_dx`.

## The ledger of two-sided equality

The `_dx_eq_dz` family combines the two existing theorems of each instance into a single
equality, with `libDX` on the left and `libDZ` on the right, both equal to the distance of
that instance. It is a **machine check** rather than a claim: for a new instance with
unequal sides this equation could not be proved.

* The three instances of the HGP family give **bounds** rather than a `min_weight`
  equation, the lower bound from the cleaning theorem and the upper bound from an explicit
  witness, so their two-sided equality is obtained by combining the bounds on $d_X$ and
  $d_Z$ separately; see `hgp_toric_family` in `Codes/HGPToricFamily.lean`, where the two
  components sit in one conjunction.
-/

namespace QECCertificates

open _root_.Matrix

/-! ## 1. The two named definitions -/

/-- **The X distance, in the reading used by this library and by LeanQEC**: the X-type
parity-check matrix `Hx` supplies the kernel.

That is, $\min\{\mathrm{wt}(v) : H_X v = 0,\ v\notin\mathrm{row}\,H_Z\}$. The order matches
LeanQEC's `CSS_pair.dX` (see `libDX_eq_CSSpair_dX`). -/
noncomputable def libDX {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hx Hz

/-- **The Z distance, in the reading used by this library and by LeanQEC**: the Z-type
parity-check matrix `Hz` supplies the kernel. -/
noncomputable def libDZ {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hz Hx

/-- **The X distance in the textbook reading**: the Z-type parity-check matrix supplies
the kernel, since an X-type operator commutes with every Z-type stabilizer. -/
noncomputable def textbookDX {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hz Hx

/-- **The Z distance in the textbook reading**: the X-type parity-check matrix supplies
the kernel. -/
noncomputable def textbookDZ {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) : ℕ :=
  min_weight_ker_not_mem_rowspace Hx Hz

/-- **The swap bridge (X side)**: the `dX` of this library's reading is the textbook
`dZ`. -/
theorem libDX_eq_textbookDZ {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) :
    libDX Hx Hz = textbookDZ Hx Hz := rfl

/-- **The swap bridge (Z side)**: the `dZ` of this library's reading is the textbook
`dX`. -/
theorem libDZ_eq_textbookDX {mx mz n : ℕ} (Hx : Matrix (Fin mx) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mz) (Fin n) (ZMod 2)) :
    libDZ Hx Hz = textbookDX Hx Hz := rfl

/-- **The exact correspondence with the LeanQEC field**: substituting the two matrices
of `CSS_pair` in their LeanQEC roles (`C.H₂` is the X-type parity check and `C.H₁` is the
Z-type parity check), the `libDX` of this library is `CSS_pair.dX`.

The equation holds by definition, so the distance fields of the two developments are
**interchangeable directly**, with no conversion factor, which is exactly what semantic
alignment requires. -/
theorem libDX_eq_CSSpair_dX {n k₁ k₂ : ℕ} (C : CSS_pair n k₁ k₂) :
    libDX C.H₂ C.H₁ = CSS_pair.dX C := rfl

/-- The correspondence between LeanQEC's `CSS_pair.dZ` and this library's `libDZ`. -/
theorem libDZ_eq_CSSpair_dZ {n k₁ k₂ : ℕ} (C : CSS_pair n k₁ k₂) :
    libDZ C.H₂ C.H₁ = CSS_pair.dZ C := rfl

/-! ## 2. The ledger of two-sided equality (every CSS code instantiated here) -/

/-- Steane code: both sides have the same distance. -/
theorem steane_dx_eq_dz : libDX steaneHx steaneHz = libDZ steaneHx steaneHz := by
  rw [libDX, libDZ, steane_dx, steane_dz]

/-- Shor code: both sides have the same distance. -/
theorem shor_dx_eq_dz : libDX shorHx shorHz = libDZ shorHx shorHz := by
  rw [libDX, libDZ, shor_dx, shor_dz]

/-- $[[4,2,2]]$: both sides have the same distance. -/
theorem four_dx_eq_dz : libDX fourHx fourHz = libDZ fourHx fourHz := by
  rw [libDX, libDZ, four_dx, four_dz]

/-- Toric code $[[8,2,2]]$: both sides have the same distance. -/
theorem toric_dx_eq_dz : libDX toricHx toricHz = libDZ toricHx toricHz := by
  rw [libDX, libDZ, toric_dx, toric_dz]

/-- Toric code $[[18,2,3]]$: both sides have the same distance. -/
theorem toric3_dx_eq_dz : libDX toric3Hx toric3Hz = libDZ toric3Hx toric3Hz := by
  rw [libDX, libDZ, toric3_dx, toric3_dz]

/-- BB $[[18,4,4]]$: both sides have the same distance. -/
theorem bb18_dx_eq_dz : libDX bb18Hx bb18Hz = libDZ bb18Hx bb18Hz := by
  rw [libDX, libDZ, bb18_dx, bb18_dz]

/-- The gauged BB $[[24,3,4]]$: both sides have the same distance.

This one deserves particular attention: gauging breaks the explicit symmetry between X and
Z, so the equality of the two sides is **not obvious** here; it is established by machine
check. -/
theorem bb24_dx_eq_dz : libDX bb24Hx bb24Hz = libDZ bb24Hx bb24Hz := by
  rw [libDX, libDZ, bb24_dx, bb24_dz]

/-- Lifted product $[[24,8,3]]$ (a 2BGA over $D_6$): both sides have the same
distance. -/
theorem lpAnchor_dx_eq_dz : libDX lpAnchorHx lpAnchorHz = libDZ lpAnchorHx lpAnchorHz := by
  rw [libDX, libDZ, lpAnchor_dx, lpAnchor_dz]

/-- Lifted product $[[24,12,2]]$ (a 2BGA over $D_6$): both sides have the same
distance. -/
theorem lpAnchor2_dx_eq_dz : libDX lpAnchor2Hx lpAnchor2Hz = libDZ lpAnchor2Hx lpAnchor2Hz := by
  rw [libDX, libDZ, lpAnchor2_dx, lpAnchor2_dz]

end QECCertificates
