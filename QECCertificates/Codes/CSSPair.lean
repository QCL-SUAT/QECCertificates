/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Codes.CaseMatrix
import LeanQEC.Stabilizer.CSS

/-!
# Feeding the distance results back into LeanQEC's `CSS_pair` (ecosystem alignment)

The distance results of this package have so far stayed in their **own** formula shape,
`min_weight_ker_not_mem_rowspace M₁ M₂`, the same definition word for word as LeanQEC's, but never
instantiated at the upstream `CSS_pair` structure. This module closes that last layer: the
upstream shorthand constructor `CSS_pair.of_matrices`, which only asks for a kernel-decidable "rows
pairwise orthogonal" condition, puts **all five CSS codes** of the case matrix (Steane, Shor,
$[[4,2,2]]$, and the toric codes at two sizes) into `CSS_pair`, so that the upstream
`CSS_pair.dX / dZ` agree word for word with the distance theorems of the case matrix: the proof
term of `steanePair.dX = 3` **is** `steane_dx`.

Three layers now close: (1) the decision layer (`inSpanB`/`inKerB`), (2) the distance layer (the
`by decide` assertions of the case matrix), and (3) the upstream structure layer (LeanQEC's
`CSS_pair`). **No extra mathematical assumption** is made: the orthogonality condition is checked
by `by decide`, and the distance conclusions are transferred from existing theorems.
-/

namespace QECCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The bare quantified form of "rows pairwise orthogonal". (`mutually_orth_rows` is a plain
`def : Prop`, so instance search does not unfold it and `by decide` cannot synthesize a decision
procedure for it; this `Iff.rfl` bridge comes first.) -/
theorem mutually_orth_rows_iff {k₁ k₂ n : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    M₁.mutually_orth_rows M₂ ↔ ∀ a b, M₁ a ⬝ᵥ M₂ b = 0 := Iff.rfl

/-! ## Steane $[[7,1,3]]$ -/

/-- The `CSS_pair` instance of the Steane code: `H₁` = Z checks and `H₂` = X checks (upstream
convention: `dZ = f(H₁, H₂)` and `dX = f(H₂, H₁)`, the same orientation as `steane_dz`/`steane_dx`
in this library). -/
def steanePair : CSS_pair 7 3 3 :=
  CSS_pair.of_matrices steaneHz steaneHx
    ((mutually_orth_rows_iff steaneHz steaneHx).mpr (by decide))

/-- **Upstream agreement (Steane)**: the upstream `CSS_pair.dX` is `steane_dx` of this library; the
proof term is word for word the same. -/
theorem steanePair_dX : CSS_pair.dX steanePair = 3 := steane_dx

/-- **Upstream agreement (Steane)**: the upstream `CSS_pair.dZ` is `steane_dz` of this library. -/
theorem steanePair_dZ : CSS_pair.dZ steanePair = 3 := steane_dz

/-! ## Shor $[[9,1,3]]$ -/

/-- The `CSS_pair` instance of the Shor code (6 rows on the Z side, 2 rows on the X side). -/
def shorPair : CSS_pair 9 6 2 :=
  CSS_pair.of_matrices shorHz shorHx
    ((mutually_orth_rows_iff shorHz shorHx).mpr (by decide))

/-- **Upstream agreement (Shor)**: the upstream `dX` is `shor_dx` of this library. -/
theorem shorPair_dX : CSS_pair.dX shorPair = 3 := shor_dx

/-- **Upstream agreement (Shor)**: the upstream `dZ` is `shor_dz` of this library. -/
theorem shorPair_dZ : CSS_pair.dZ shorPair = 3 := shor_dz

/-! ## $[[4,2,2]]$ -/

/-- The `CSS_pair` instance of the $[[4,2,2]]$ code (1 row on each side). -/
def fourPair : CSS_pair 4 1 1 :=
  CSS_pair.of_matrices fourHz fourHx
    ((mutually_orth_rows_iff fourHz fourHx).mpr (by decide))

/-- **Upstream agreement ($[[4,2,2]]$)**: the upstream `dX` is `four_dx` of this library. -/
theorem fourPair_dX : CSS_pair.dX fourPair = 2 := four_dx

/-- **Upstream agreement ($[[4,2,2]]$)**: the upstream `dZ` is `four_dz` of this library. -/
theorem fourPair_dZ : CSS_pair.dZ fourPair = 2 := four_dz

/-! ## Toric codes (two sizes) -/

/-- The `CSS_pair` instance of the $2\times2$ toric code $[[8,2,2]]$. -/
def toricPair : CSS_pair 8 4 4 :=
  CSS_pair.of_matrices toricHz toricHx
    ((mutually_orth_rows_iff toricHz toricHx).mpr (by decide))

/-- **Upstream agreement (toric $2\times2$)**: the upstream `dX` is `toric_dx` of this library. -/
theorem toricPair_dX : CSS_pair.dX toricPair = 2 := toric_dx

/-- **Upstream agreement (toric $2\times2$)**: the upstream `dZ` is `toric_dz` of this library. -/
theorem toricPair_dZ : CSS_pair.dZ toricPair = 2 := toric_dz

/-- The `CSS_pair` instance of the $3\times3$ toric code $[[18,2,3]]$ ($n = 18$; the orthogonality
condition is 9×9 dot products, decided by the kernel in seconds, the same shape as `toric3_css`). -/
def toric3Pair : CSS_pair 18 9 9 :=
  CSS_pair.of_matrices toric3Hz toric3Hx
    ((mutually_orth_rows_iff toric3Hz toric3Hx).mpr (by decide))

/-- **Upstream agreement (toric $3\times3$)**: the upstream `dX` is `toric3_dx` of this library. -/
theorem toric3Pair_dX : CSS_pair.dX toric3Pair = 3 := toric3_dx

/-- **Upstream agreement (toric $3\times3$)**: the upstream `dZ` is `toric3_dz` of this library. -/
theorem toric3Pair_dZ : CSS_pair.dZ toric3Pair = 3 := toric3_dz

end QECCertificates
