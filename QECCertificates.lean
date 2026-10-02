/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/

import QECCertificates.Codes.BB144Distance
import QECCertificates.Codes.BB144Literal
import QECCertificates.Codes.BB144Rank
import QECCertificates.Codes.BB144Symmetry
import QECCertificates.Codes.BB144Witness
import QECCertificates.Codes.BB18Anchor
import QECCertificates.Codes.BB18Symmetry
import QECCertificates.Codes.BB24Gauged
import QECCertificates.Codes.BB24Separation
import QECCertificates.Codes.BaconShor
import QECCertificates.Codes.BaconShorMeasurement
import QECCertificates.Codes.BoundaryCollapse
import QECCertificates.Codes.CSSPair
import QECCertificates.Codes.CaseMatrix
import QECCertificates.Codes.DistanceLabel
import QECCertificates.Codes.FoldTransversal
import QECCertificates.Codes.FullProtocolFaults
import QECCertificates.Codes.GaugeMeasurementInstance
import QECCertificates.Codes.Gauging
import QECCertificates.Codes.HGPToricFamily
import QECCertificates.Codes.LPAnchor
import QECCertificates.Codes.MeasurementProtocol
import QECCertificates.Codes.Separation
import QECCertificates.Codes.SeparationClosedForm
import QECCertificates.Codes.SeparationInstances
import QECCertificates.Codes.TimeLikeInstance
import QECCertificates.Codes.ToricFamilySpatial
import QECCertificates.GF2.Basic
import QECCertificates.GF2.Canonical
import QECCertificates.GF2.HGP
import QECCertificates.GF2.HGPCleaning
import QECCertificates.GF2.HGPCleaningDual
import QECCertificates.GF2.HGPCompression
import QECCertificates.GF2.HGPKunneth
import QECCertificates.GF2.KernelBasis
import QECCertificates.GF2.KunnethCore
import QECCertificates.GF2.LiftedProduct
import QECCertificates.GF2.LowerBound
import QECCertificates.GF2.Membership
import QECCertificates.GF2.RankCertificate
import QECCertificates.GF2.RankEchelon
import QECCertificates.GF2.RowReduce
import QECCertificates.GF2.WeightEnum
import QECCertificates.GF2.Witness
import QECCertificates.Pauli.Expr
import QECCertificates.Reflect.Certified
import QECCertificates.Reflect.Complete
import QECCertificates.Reflect.Encode
import QECCertificates.Reflect.Faithful
import QECCertificates.Reflect.FaithfulCircuit
import QECCertificates.Reflect.LRAT
import QECCertificates.Reflect.LRATData
import QECCertificates.Reflect.LRATDataCircuit
import QECCertificates.Reflect.LexComplete
import QECCertificates.Reflect.LexLeader
import QECCertificates.Reflect.SBAssembly
import QECCertificates.Reflect.SymmetryBreak

/-!
# QECCertificates

Certified code parameters and fault distances for quantum error correction

This module imports every module of the package, and maintains the audit region at the
end of the file: every non-private theorem and lemma of the package is printed there by
`#print axioms`, so that a reader can see, without trusting anyone, that each of them
rests on exactly the three standard axioms.

## Modules

| Module | Contents |
|---|---|
| `QECCertificates.Codes.BB144Distance` | BB $[[144,12,12]]$: an in-kernel proof of the lower bound $d\ge12$ (through QECLean's Gross formalization) |
| `QECCertificates.Codes.BB144Literal` | BB $[[144,12,12]]$: **identity** of the literal matrices with the QECLean spelling (the last step towards $d=12$) |
| `QECCertificates.Codes.BB144Rank` | the dimension of $[[144,12,12]]$ |
| `QECCertificates.Codes.BB144Symmetry` | **translation symmetry** of BB $[[144,12,12]]$ (the first step of the symmetry-breaking route) |
| `QECCertificates.Codes.BB144Witness` | BB $[[144,12,12]]$: in-kernel assertions for the witness upper bound |
| `QECCertificates.Codes.BB18Anchor` | the BB anchor $[[18,4,4]]$: all parameters (the smallest instance of the family, and the base code for gauging) |
| `QECCertificates.Codes.BB18Symmetry` | the BB18 translation group lifted to the pair space, with its closure properties and the key order on it |
| `QECCertificates.Codes.BB24Gauged` | a gauging instance of the BB family: $[[18,4,4]]$ through the $K_4$ auxiliary graph to $[[24,3,4]]$ |
| `QECCertificates.Codes.BB24Separation` | the two-component separation statement for BB $[[24,3,4]]$ (C1 discharged by the expansion of $K_4$) |
| `QECCertificates.Codes.BaconShor` | Bacon–Shor $[[9,1,3]]$: the structure and distance of a **subsystem code** (in-kernel) |
| `QECCertificates.Codes.BaconShorMeasurement` | the two components of transversal measurement for Bacon–Shor $[[9,1,3]]$ (in-kernel instance) |
| `QECCertificates.Codes.BoundaryCollapse` | removing the boundary detectors collapses the distance to $1$ for **every** code (family-level form) |
| `QECCertificates.Codes.CSSPair` | feeding into LeanQEC's `CSS_pair`: the distance conclusions of the case matrix meet the upstream interface |
| `QECCertificates.Codes.CaseMatrix` | the case matrix: machine-checked assertions of code parameters (end to end) |
| `QECCertificates.Codes.DistanceLabel` | the X/Z distance labels: fixing the convention, and machine-checking that the two sides agree |
| `QECCertificates.Codes.FoldTransversal` | fold-transversal gates: an in-kernel instance for BB $[[18,4,4]]$ |
| `QECCertificates.Codes.FullProtocolFaults` | the fault model of the full protocol: data, ancilla and measurement errors (a Bacon–Shor instance) |
| `QECCertificates.Codes.GaugeMeasurementInstance` | the timelike detector code of the BB gauging measurement circuit: $\lvert V\rvert = 4$ Gauss laws, $T = 4 = d$ rounds |
| `QECCertificates.Codes.Gauging` | the formal statement of the two gauging components (representation layer) |
| `QECCertificates.Codes.HGPToricFamily` | an HGP instance at $n\ge144$, and a whole-family theorem for the toric family |
| `QECCertificates.Codes.LPAnchor` | the lifted-product anchor: a 2BGA instance over $D_6$ |
| `QECCertificates.Codes.MeasurementProtocol` | the representation layer of the measurement protocol (spacetime fault model, and the time axis of the two components) |
| `QECCertificates.Codes.Separation` | the decision layer for the C1–C4 separation conditions (fault-tolerant distance under logical measurement) |
| `QECCertificates.Codes.SeparationClosedForm` | closed forms for the separation conditions (C1 discharged for complete-graph families by the expansion theorem) |
| `QECCertificates.Codes.SeparationInstances` | instances of C1: **two-sided counterexamples** (a failing side and a distance-preserving side) |
| `QECCertificates.Codes.TimeLikeInstance` | a named instance of the timelike component: a repetition-code detector with $m = 3$ checks and $T = 4$ rounds |
| `QECCertificates.Codes.ToricFamilySpatial` | the **spacelike side** of the toric family (both distances of the deformed code are $m$, with a surviving witness of weight $m$) |
| `QECCertificates.GF2.Basic` | GF(2) vector algebra primitives |
| `QECCertificates.GF2.Canonical` | uniqueness of the canonical form: the row-reduction output of a row space is a canonical invariant |
| `QECCertificates.GF2.HGP` | the tensor decomposition of the hypergraph-product parity-check matrix |
| `QECCertificates.GF2.HGPCleaning` | HGP, part three: the cleaning argument and the X-distance lower bound |
| `QECCertificates.GF2.HGPCleaningDual` | HGP, part three, dual side: the Z-distance lower bound (transport through the transpose code) |
| `QECCertificates.GF2.HGPCompression` | HGP, part two: compression identities, the transpose code, and single-block weight lower bounds |
| `QECCertificates.GF2.HGPKunneth` | the dimension formula `k = k₁k₂ + k₁ᵀk₂ᵀ` for HGP |
| `QECCertificates.GF2.KernelBasis` | kernel basis extraction and completeness |
| `QECCertificates.GF2.KunnethCore` | tensor intersections of subspaces: the dimension of `{X : columns ⊆ U ∧ rows ⊆ W}` |
| `QECCertificates.GF2.LiftedProduct` | the lifted product: HGP over a group algebra, and its degeneration to HGP |
| `QECCertificates.GF2.LowerBound` | a computable certificate for distance lower bounds: handing "no lighter logical operator" to the kernel |
| `QECCertificates.GF2.Membership` | computable membership: letting the kernel compute an exact distance |
| `QECCertificates.GF2.RankCertificate` | the rank certificate: `finrank (rowSpace H) = #(row-reduction output)` |
| `QECCertificates.GF2.RankEchelon` | an append-only echelon-form rank routine (a rank reading available on wide matrices) |
| `QECCertificates.GF2.RowReduce` | trusted GF(2) row reduction |
| `QECCertificates.GF2.WeightEnum` | weight-bounded vector enumeration: shrinking the search space from $2^n$ to $\sum_{k\le w}\binom nk$ |
| `QECCertificates.GF2.Witness` | dual-witness certificates, and the two exact-distance theorems |
| `QECCertificates.Pauli.Expr` | translation theorems between the operator algebra (operator trees) and the decision layer (GF(2) symplectic representation) |
| `QECCertificates.Reflect.Certified` | a certificate is a lower bound: connecting the in-kernel replay to a code-distance theorem |
| `QECCertificates.Reflect.Complete` | encoding faithfulness: the completeness direction |
| `QECCertificates.Reflect.Encode` | encoding faithfulness: a model of the CNF is a light logical operator |
| `QECCertificates.Reflect.Faithful` | encoding faithfulness: the CNF that was replayed is the encoder's output |
| `QECCertificates.Reflect.FaithfulCircuit` | circuit-side encoding faithfulness: the CNF that was replayed is the encoder's output |
| `QECCertificates.Reflect.LRAT` | the in-kernel LRAT checker and its soundness theorem |
| `QECCertificates.Reflect.LRATData` | **in-kernel replay** of the package's SAT certificates |
| `QECCertificates.Reflect.LRATDataCircuit` | in-kernel replay of the **circuit-side** (timelike) SAT certificates |
| `QECCertificates.Reflect.LexComplete` | completeness of the lexicographic-comparator clauses (soundness is not enough: too tight is not UNSAT) |
| `QECCertificates.Reflect.LexLeader` | soundness of the lexicographic-comparator clauses (the CNF layer of the symmetry break) |
| `QECCertificates.Reflect.SBAssembly` | assembly of the broken-symmetry CNF: `buildPair` and `lexClauses` |
| `QECCertificates.Reflect.SymmetryBreak` | faithfulness of symmetry breaking: unsatisfiability after breaking implies unsatisfiability of the original |
-/

-- 公理审计（包内全部非 private 定理/引理；期望三条标准公理）
-- QECCertificates.Codes.BB144Distance
#print axioms QECCertificates.BB144Distance.idxZ_fst_val
#print axioms QECCertificates.BB144Distance.idxZ_snd_val
#print axioms QECCertificates.BB144Distance.val_add_natCast
#print axioms QECCertificates.BB144Distance.idxZ_add_iff
#print axioms QECCertificates.BB144Distance.x_entry
#print axioms QECCertificates.BB144Distance.val_add_natCast6
#print axioms QECCertificates.BB144Distance.idxZ_add_iff_y
#print axioms QECCertificates.BB144Distance.y_entry
#print axioms QECCertificates.BB144Distance.grossA_support_eq
#print axioms QECCertificates.BB144Distance.grossB_support_eq
#print axioms QECCertificates.BB144Distance.grossA_mem_iff
#print axioms QECCertificates.BB144Distance.grossA_eq_indicator
#print axioms QECCertificates.BB144Distance.mem_support_iff
#print axioms QECCertificates.BB144Distance.BB144_A_entry
#print axioms QECCertificates.BB144Distance.grossB_mem_iff
#print axioms QECCertificates.BB144Distance.grossB_eq_indicator
#print axioms QECCertificates.BB144Distance.mem_support_iff_B
#print axioms QECCertificates.BB144Distance.BB144_B_entry
#print axioms QECCertificates.BB144Distance.LE_A_apply
#print axioms QECCertificates.BB144Distance.LE_B_apply
#print axioms QECCertificates.BB144Distance.finEquiv12_val
#print axioms QECCertificates.BB144Distance.finEquiv6_val
#print axioms QECCertificates.BB144Distance.e72_apply
#print axioms QECCertificates.BB144Distance.e144_symm_apply
#print axioms QECCertificates.BB144Distance.e144_symm_zero
#print axioms QECCertificates.BB144Distance.e144_symm_one
#print axioms QECCertificates.BB144Distance.b1_apply
#print axioms QECCertificates.BB144Distance.b2_apply
#print axioms QECCertificates.BB144Distance.psi_injective
#print axioms QECCertificates.BB144Distance.sum_smul_single
#print axioms QECCertificates.BB144Distance.boundary1_eq_sum
#print axioms QECCertificates.BB144Distance.boundary2_eq_sum
#print axioms QECCertificates.BB144Distance.boundary1_single_zero
#print axioms QECCertificates.BB144Distance.boundary1_single_one
#print axioms QECCertificates.BB144Distance.boundary2_single_zero
#print axioms QECCertificates.BB144Distance.boundary2_single_one
#print axioms QECCertificates.BB144Distance.LE_Z_entry_zero
#print axioms QECCertificates.BB144Distance.LE_Z_entry_one
#print axioms QECCertificates.BB144Distance.LE_X_entry_zero
#print axioms QECCertificates.BB144Distance.LE_X_entry_one
#print axioms QECCertificates.BB144Distance.b1_eq
#print axioms QECCertificates.BB144Distance.b2_eq
#print axioms QECCertificates.BB144Distance.psiLin_apply
#print axioms QECCertificates.BB144Distance.LE_Z_entry
#print axioms QECCertificates.BB144Distance.LE_X_entry
#print axioms QECCertificates.BB144Distance.LE_Z_mulVec
#print axioms QECCertificates.BB144Distance.LE_X_row
#print axioms QECCertificates.BB144Distance.LE_Z_ker_iff
#print axioms QECCertificates.BB144Distance.LE_Z_ker_cycles
#print axioms QECCertificates.BB144Distance.mem_rowSpace_of_mem_boundaries
#print axioms QECCertificates.BB144Distance.chainWeight_psi
#print axioms QECCertificates.BB144Distance.hammingNorm_eq_zero_iff
#print axioms QECCertificates.BB144Distance.gross_chain_distance_eq_12
#print axioms QECCertificates.BB144Distance.twelve_le_hammingNorm
#print axioms QECCertificates.BB144Distance.b0_apply
#print axioms QECCertificates.BB144Distance.b0d_apply
#print axioms QECCertificates.BB144Distance.LE_X_mulVec
#print axioms QECCertificates.BB144Distance.LE_X_ker_dualCycles
#print axioms QECCertificates.BB144Distance.LE_X_ker_dualCycles'
#print axioms QECCertificates.BB144Distance.LE_Z_row
#print axioms QECCertificates.BB144Distance.b0_eq_sum
#print axioms QECCertificates.BB144Distance.mem_rowSpace_of_mem_dualBoundaries
#print axioms QECCertificates.BB144Distance.dual_bound_of_primal
#print axioms QECCertificates.BB144Distance.twelve_le_hammingNorm_dual
#print axioms QECCertificates.BB144Distance.BB144_dX_ge_12
#print axioms QECCertificates.BB144Distance.BB144_dZ_ge_12
#print axioms QECCertificates.BB144Distance.BB144_toBSM_distance_ge_12
#print axioms QECCertificates.BB144Distance.bb144_libDX_le_12
#print axioms QECCertificates.BB144Distance.bb144_libDZ_le_12
-- QECCertificates.Codes.BB144Literal
#print axioms QECCertificates.bb144Hx_eq_LE_X
#print axioms QECCertificates.bb144Hz_eq_LE_Z
#print axioms QECCertificates.bb144_dX_eq_12
#print axioms QECCertificates.bb144_dZ_eq_12
#print axioms QECCertificates.bb144_dx_eq_dz
-- QECCertificates.Codes.BB144Rank
#print axioms QECCertificates.bb144RowSum_mem_spanL
#print axioms QECCertificates.bb144RowSumZ_mem_spanL
#print axioms QECCertificates.bb144CertX_mem
#print axioms QECCertificates.bb144CertX_get_mem
#print axioms QECCertificates.bb144CertX_ech
#print axioms QECCertificates.bb144RxHead_length
#print axioms QECCertificates.bb144HxRow_mem_head
#print axioms QECCertificates.bb144RowSum_mem_head
#print axioms QECCertificates.bb144RelX64
#print axioms QECCertificates.bb144RelX64_mem
#print axioms QECCertificates.bb144RelX65
#print axioms QECCertificates.bb144RelX65_mem
#print axioms QECCertificates.bb144RelX68
#print axioms QECCertificates.bb144RelX68_mem
#print axioms QECCertificates.bb144RelX69
#print axioms QECCertificates.bb144RelX69_mem
#print axioms QECCertificates.bb144RelX70
#print axioms QECCertificates.bb144RelX70_mem
#print axioms QECCertificates.bb144RelX71
#print axioms QECCertificates.bb144RelX71_mem
#print axioms QECCertificates.bb144Rx_mem_head
#print axioms QECCertificates.bb144_rankX_le
#print axioms QECCertificates.bb144_rankX_ge
#print axioms QECCertificates.bb144_rankX
#print axioms QECCertificates.bb144CertZ_mem
#print axioms QECCertificates.bb144CertZ_get_mem
#print axioms QECCertificates.bb144CertZ_ech
#print axioms QECCertificates.bb144RzHead_length
#print axioms QECCertificates.bb144HzRow_mem_head
#print axioms QECCertificates.bb144RowSumZ_mem_head
#print axioms QECCertificates.bb144RelZ64
#print axioms QECCertificates.bb144RelZ64_mem
#print axioms QECCertificates.bb144RelZ65
#print axioms QECCertificates.bb144RelZ65_mem
#print axioms QECCertificates.bb144RelZ68
#print axioms QECCertificates.bb144RelZ68_mem
#print axioms QECCertificates.bb144RelZ69
#print axioms QECCertificates.bb144RelZ69_mem
#print axioms QECCertificates.bb144RelZ70
#print axioms QECCertificates.bb144RelZ70_mem
#print axioms QECCertificates.bb144RelZ71
#print axioms QECCertificates.bb144RelZ71_mem
#print axioms QECCertificates.bb144Rz_mem_head
#print axioms QECCertificates.bb144_rankZ_le
#print axioms QECCertificates.bb144_rankZ_ge
#print axioms QECCertificates.bb144_rankZ
#print axioms QECCertificates.bb144_rowReduceX
#print axioms QECCertificates.bb144_rowReduceZ
#print axioms QECCertificates.bb144_k
-- QECCertificates.Codes.BB144Symmetry
#print axioms QECCertificates.fin2_eq_zero_or_one
#print axioms QECCertificates.bb144Trans_symm_eq
#print axioms QECCertificates.bb144Trans_apply
#print axioms QECCertificates.bb144Trans_symm_apply
#print axioms QECCertificates.permVec_bb144Trans_hxRow_apply_zero
#print axioms QECCertificates.permVec_bb144Trans_hxRow_apply_one
#print axioms QECCertificates.permVec_bb144Trans_hxRow_apply
#print axioms QECCertificates.permVec_bb144Trans_hxRow
#print axioms QECCertificates.permVec_bb144Trans_hzRow_apply_zero
#print axioms QECCertificates.permVec_bb144Trans_hzRow_apply_one
#print axioms QECCertificates.permVec_bb144Trans_hzRow_apply
#print axioms QECCertificates.permVec_bb144Trans_hzRow
#print axioms QECCertificates.bb144_permVec_hxRow_mem
#print axioms QECCertificates.bb144_permVec_hzRow_mem
#print axioms QECCertificates.bb144Trans_hammingNorm
#print axioms QECCertificates.bb144Trans_dotProduct
#print axioms QECCertificates.bb144Trans_preserves_spanL_x
#print axioms QECCertificates.bb144Trans_preserves_spanL_z
#print axioms QECCertificates.bb144Trans_mem_spanL_iff_x
#print axioms QECCertificates.bb144Trans_mem_spanL_iff_z
#print axioms QECCertificates.bb144Trans_trans
-- QECCertificates.Codes.BB144Witness
#print axioms QECCertificates.bb144_X_logical
#print axioms QECCertificates.bb144_Z_logical
-- QECCertificates.Codes.BB18Anchor
-- QECCertificates.Codes.BB18Symmetry
#print axioms QECCertificates.permVec_permVec
#print axioms QECCertificates.perm_mul_symm_apply
#print axioms QECCertificates.pairPerm_mul
#print axioms QECCertificates.pairPerm_one
#print axioms QECCertificates.bb18ShiftX_comm
#print axioms QECCertificates.bb18Trans_mul
#print axioms QECCertificates.bb18Group_one_mem
#print axioms QECCertificates.bb18Group_mul_mem
#print axioms QECCertificates.zmod2Fin2
#print axioms QECCertificates.keyWord_injective
#print axioms QECCertificates.keyOrder
#print axioms QECCertificates.bb18_ofFn_x
#print axioms QECCertificates.bb18_ofFn_z
#print axioms QECCertificates.bb18_k
#print axioms QECCertificates.bb18_dx
#print axioms QECCertificates.bb18_dz
-- QECCertificates.Codes.BB24Gauged
#print axioms QECCertificates.bb24_ofFn_x
#print axioms QECCertificates.bb24_ofFn_z
#print axioms QECCertificates.bb24_k
#print axioms QECCertificates.bb24_lightCand_x
#print axioms QECCertificates.bb24_lightCand_z
#print axioms QECCertificates.bb24_lowerHyp
#print axioms QECCertificates.bb24_dx
#print axioms QECCertificates.bb24_dz
#print axioms QECCertificates.bb18L_logical
#print axioms QECCertificates.bb24_gauss_sum
#print axioms QECCertificates.bb24HxC_eq
#print axioms QECCertificates.bb24HzC_eq
#print axioms QECCertificates.bb24L_mem_rowSpace
#print axioms QECCertificates.bb24_deformZ_matching
#print axioms QECCertificates.bb24_deformZ_none
#print axioms QECCertificates.bb24_flux_commute
#print axioms QECCertificates.bb24_orth
#print axioms QECCertificates.bb18_gauged_drop
#print axioms QECCertificates.bb18_gauged_k
-- QECCertificates.Codes.BB24Separation
#print axioms QECCertificates.bb24_separation_closed
#print axioms QECCertificates.bb24_both_distances
#print axioms QECCertificates.bb24_space_bound
#print axioms QECCertificates.bb24_separation_closed_noHyp
-- QECCertificates.Codes.BaconShor
#print axioms QECCertificates.bst_rX
#print axioms QECCertificates.bst_rZ
#print axioms QECCertificates.bst_centerX_rank
#print axioms QECCertificates.bst_centerZ_rank
#print axioms QECCertificates.bst_k
#print axioms QECCertificates.bstSX_mem_ker
#print axioms QECCertificates.bstSX_mem_gauge
#print axioms QECCertificates.bstXW_mem_ker
#print axioms QECCertificates.bstXW_not_mem_gauge
#print axioms QECCertificates.bst_dX
#print axioms QECCertificates.bst_dZ
-- QECCertificates.Codes.BaconShorMeasurement
#print axioms QECCertificates.bsSingleRound_noLightFault
#print axioms QECCertificates.bsSingleRound_witness
#print axioms QECCertificates.bsSingleRound_eq_d
#print axioms QECCertificates.bsCrossChecks_ker_iff
#print axioms QECCertificates.bsMeasureW_witness
#print axioms QECCertificates.bsMeasure_noLightFault
#print axioms QECCertificates.bsMeasure_eq_T
#print axioms QECCertificates.bsMeasure2_noLightFault
#print axioms QECCertificates.bsMeasure2_lt_d
#print axioms QECCertificates.bsMeasure1_eq_one
#print axioms QECCertificates.bsMeasure4_noLightFault
#print axioms QECCertificates.bsMeasure4W_witness
#print axioms QECCertificates.bsMeasure4_eq_T
#print axioms QECCertificates.bsTransversal_time_lower
#print axioms QECCertificates.bsTransversal_T3_witness
#print axioms QECCertificates.le_spacetimeWeight_of_agree
#print axioms QECCertificates.spacetimeWeight_witness_of_agree
#print axioms QECCertificates.measureTime_distance_eq_rounds
#print axioms QECCertificates.bsMeasure_T_eq_codeDistance
-- QECCertificates.Codes.BoundaryCollapse
#print axioms QECCertificates.support_e
#print axioms QECCertificates.hammingNorm_e
#print axioms QECCertificates.cum_witFault
#print axioms QECCertificates.dot_e
#print axioms QECCertificates.comparisonsSilent_witFault
#print axioms QECCertificates.readout_witFault
#print axioms QECCertificates.faultWeight_witFault
#print axioms QECCertificates.boundaryRemoved_witness
#print axioms QECCertificates.one_le_faultWeight_of_readout
#print axioms QECCertificates.boundaryRemoved_distance_eq_one
-- QECCertificates.Codes.CSSPair
#print axioms QECCertificates.mutually_orth_rows_iff
#print axioms QECCertificates.steanePair_dX
#print axioms QECCertificates.steanePair_dZ
#print axioms QECCertificates.shorPair_dX
#print axioms QECCertificates.shorPair_dZ
#print axioms QECCertificates.fourPair_dX
#print axioms QECCertificates.fourPair_dZ
#print axioms QECCertificates.toricPair_dX
#print axioms QECCertificates.toricPair_dZ
#print axioms QECCertificates.toric3Pair_dX
#print axioms QECCertificates.toric3Pair_dZ
-- QECCertificates.Codes.CaseMatrix
#print axioms QECCertificates.rep3_k
#print axioms QECCertificates.rep3_d
#print axioms QECCertificates.rep5_k
#print axioms QECCertificates.rep5_d
#print axioms QECCertificates.rep7_k
#print axioms QECCertificates.rep7_d
#print axioms QECCertificates.ham7_k
#print axioms QECCertificates.ham7_d
#print axioms QECCertificates.ham15_k
#print axioms QECCertificates.ham15_d
#print axioms QECCertificates.steane_k
#print axioms QECCertificates.steane_dx
#print axioms QECCertificates.steane_dz
#print axioms QECCertificates.shor_k
#print axioms QECCertificates.shor_dx
#print axioms QECCertificates.shor_dz
#print axioms QECCertificates.four_k
#print axioms QECCertificates.four_dx
#print axioms QECCertificates.four_dz
#print axioms QECCertificates.toric_k
#print axioms QECCertificates.toric_dx
#print axioms QECCertificates.toric_dz
#print axioms QECCertificates.toric3_ofFn_hz
#print axioms QECCertificates.toric3_ofFn_hx
#print axioms QECCertificates.toric3_k
#print axioms QECCertificates.toric3_dx
#print axioms QECCertificates.toric3_dz
#print axioms QECCertificates.p5_pairwise_commute
#print axioms QECCertificates.p5_k
#print axioms QECCertificates.p5_d
-- QECCertificates.Codes.DistanceLabel
#print axioms QECCertificates.libDX_eq_textbookDZ
#print axioms QECCertificates.libDZ_eq_textbookDX
#print axioms QECCertificates.libDX_eq_CSSpair_dX
#print axioms QECCertificates.libDZ_eq_CSSpair_dZ
#print axioms QECCertificates.steane_dx_eq_dz
#print axioms QECCertificates.shor_dx_eq_dz
#print axioms QECCertificates.four_dx_eq_dz
#print axioms QECCertificates.toric_dx_eq_dz
#print axioms QECCertificates.toric3_dx_eq_dz
#print axioms QECCertificates.bb18_dx_eq_dz
#print axioms QECCertificates.bb24_dx_eq_dz
#print axioms QECCertificates.lpAnchor_dx_eq_dz
#print axioms QECCertificates.lpAnchor2_dx_eq_dz
-- QECCertificates.Codes.FoldTransversal
#print axioms QECCertificates.permVec_apply
#print axioms QECCertificates.support_permVec
#print axioms QECCertificates.hammingNorm_permVec
#print axioms QECCertificates.permVec_mem_spanL
#print axioms QECCertificates.permVec_symm_permVec
#print axioms QECCertificates.permVec_permVec_symm
#print axioms QECCertificates.dotProduct_permVec
#print axioms QECCertificates.dotProduct_permVec_left
#print axioms QECCertificates.permVec_mem_spanL_iff
#print axioms QECCertificates.inKerB_permVec
#print axioms QECCertificates.permVec_preserves_undetectable
#print axioms QECCertificates.mem_of_list_all
#print axioms QECCertificates.mem_spanL_of_list_all
#print axioms QECCertificates.kerRows_of_list_all
#print axioms QECCertificates.bb18_foldCz_rows_x
#print axioms QECCertificates.bb18_foldCz_rows_z
#print axioms QECCertificates.bb18_foldH_rows_x
#print axioms QECCertificates.bb18_foldH_rows_z
#print axioms QECCertificates.bb18_shiftX_rows_x
#print axioms QECCertificates.bb18_shiftX_rows_z
#print axioms QECCertificates.bb18_shiftY_rows_x
#print axioms QECCertificates.bb18_shiftY_rows_z
#print axioms QECCertificates.bb18_foldCz_rows_symm
#print axioms QECCertificates.bb18_foldH_rows_symm
#print axioms QECCertificates.bb18_shiftX_rows_symm
#print axioms QECCertificates.bb18_shiftY_rows_symm
#print axioms QECCertificates.bb18_foldCz_preserves_spanL_x
#print axioms QECCertificates.bb18_foldCz_preserves_spanL_z
#print axioms QECCertificates.bb18_foldH_maps_spanL_xz
#print axioms QECCertificates.bb18_foldH_maps_spanL_zx
#print axioms QECCertificates.bb18_shiftX_preserves_spanL_x
#print axioms QECCertificates.bb18_shiftX_preserves_spanL_z
#print axioms QECCertificates.bb18_shiftY_preserves_spanL_x
#print axioms QECCertificates.bb18_shiftY_preserves_spanL_z
#print axioms QECCertificates.bb18Log0_logical
#print axioms QECCertificates.bb18Log1_logical
#print axioms QECCertificates.bb18Log2_logical
#print axioms QECCertificates.bb18Log3_logical
#print axioms QECCertificates.bb18_logical_independent
#print axioms QECCertificates.bb18_foldCz_log0
#print axioms QECCertificates.bb18_foldCz_log1
#print axioms QECCertificates.bb18_foldCz_log2
#print axioms QECCertificates.bb18_foldCz_log3
#print axioms QECCertificates.bb18_foldH_log0
#print axioms QECCertificates.bb18_foldH_log1
#print axioms QECCertificates.bb18_foldH_log2
#print axioms QECCertificates.bb18_foldH_log3
#print axioms QECCertificates.bb18_shiftX_log0
#print axioms QECCertificates.bb18_shiftX_log1
#print axioms QECCertificates.bb18_shiftX_log2
#print axioms QECCertificates.bb18_shiftX_log3
#print axioms QECCertificates.bb18_shiftY_log0
#print axioms QECCertificates.bb18_shiftY_log1
#print axioms QECCertificates.bb18_shiftY_log2
#print axioms QECCertificates.bb18_shiftY_log3
#print axioms QECCertificates.bb18_foldCz_weight
#print axioms QECCertificates.bb18_foldH_weight
#print axioms QECCertificates.bb18_shiftX_weight
#print axioms QECCertificates.bb18_shiftY_weight
#print axioms QECCertificates.bb18Log_permVec_undetectable
#print axioms QECCertificates.bb18_foldCz_undetectable
#print axioms QECCertificates.bb18_foldH_undetectable
#print axioms QECCertificates.bb18_shiftX_undetectable
#print axioms QECCertificates.bb18_shiftY_undetectable
-- QECCertificates.Codes.FullProtocolFaults
#print axioms QECCertificates.bsDetectorsOK_syndrome_eq_zero
#print axioms QECCertificates.bsHook_T1_witness
#print axioms QECCertificates.bsHook_T1_no_light_one
#print axioms QECCertificates.bsHook_T1_distance_eq_two
#print axioms QECCertificates.bsHook_T2_no_light
#print axioms QECCertificates.bsHook_T3_no_light
#print axioms QECCertificates.bsHook_T4_no_light
#print axioms QECCertificates.bsHook_twoRounds_witness
#print axioms QECCertificates.bsHook_threeRounds_witness
#print axioms QECCertificates.bsHook_fourRounds_witness
#print axioms QECCertificates.bsHook_T2_distance_eq_three
#print axioms QECCertificates.bsHook_T3_distance_eq_three
#print axioms QECCertificates.bsHook_T4_distance_eq_three
#print axioms QECCertificates.bsHook_noBoundary_weight_one
#print axioms QECCertificates.noBoundary_light_of_any_rounds
#print axioms QECCertificates.bsHook_summary
#print axioms QECCertificates.bsDetectorsOK_closed_of_firstEnd
#print axioms QECCertificates.bsDetectorsOK_firstEnd_syndrome_eq_zero
#print axioms QECCertificates.bsDetectorsOK_syndrome_eq_zero_of_terminal
#print axioms QECCertificates.hookCandClosed_eq
#print axioms QECCertificates.c3_both_ends_agree
#print axioms QECCertificates.card_touchedRounds_le
#print axioms QECCertificates.wt_cumErr_le
#print axioms QECCertificates.bsHook_no_light_of_four_le
#print axioms QECCertificates.bsHook_no_light_universal
#print axioms QECCertificates.hookW3gen_witness
#print axioms QECCertificates.bsHook_distance_eq_three_universal
#print axioms QECCertificates.hookCandDup_no_light_of
#print axioms QECCertificates.dupHook_T1_witness
#print axioms QECCertificates.hookCandDup_T1_no_light_two
#print axioms QECCertificates.hookCandDup_T1_distance_eq_three
#print axioms QECCertificates.hookW3Dup_witness
#print axioms QECCertificates.c4_dup_price_verdict
#print axioms QECCertificates.bsHook_T1_formula
#print axioms QECCertificates.bsHook_T1_min
#print axioms QECCertificates.bsHook_T1_distance_eq_two_formula
-- QECCertificates.Codes.GaugeMeasurementInstance
#print axioms QECCertificates.bbGauge44Checks_rows
#print axioms QECCertificates.bbGauge44Star_weight
#print axioms QECCertificates.bbGauge44Checks_prod
#print axioms QECCertificates.bbGauge44_witness_mem_ker
#print axioms QECCertificates.bbGauge44_witness_ne_zero
#print axioms QECCertificates.bbGauge44_witness_weight
#print axioms QECCertificates.bbGauge44_block_witnesses
#print axioms QECCertificates.bbGauge44Blk_injective
#print axioms QECCertificates.bbGauge44H_row
#print axioms QECCertificates.e_dot
#print axioms QECCertificates.inKerB_dot_row
#print axioms QECCertificates.bbGauge44_ker_row_eq
#print axioms QECCertificates.bbGauge44Blk_surjective
#print axioms QECCertificates.bbGauge44_ker_slice_const
#print axioms QECCertificates.bbGauge44_le_weight_of_ker
#print axioms QECCertificates.bbGauge44_d
#print axioms QECCertificates.bbGauge44_lightSet_zero
#print axioms QECCertificates.bbGauge44_d_eq_codeDistance
-- QECCertificates.Codes.Gauging
#print axioms QECCertificates.deformX_css
#print axioms QECCertificates.finrank_spanL_append_singleton_of_not_mem
#print axioms QECCertificates.deformX_rowReduce_length
#print axioms QECCertificates.deformX_k
#print axioms QECCertificates.gauss_prod_eq_vertex_prod
#print axioms QECCertificates.unitVec_dot
#print axioms QECCertificates.timeLike_eq_of_repCheck
#print axioms QECCertificates.timeLike_weight_eq
-- QECCertificates.Codes.HGPToricFamily
#print axioms QECCertificates.not_mem_rowSpace_of_ker_dot
#print axioms QECCertificates.blockR_toricXW_zero
#print axioms QECCertificates.blockR_toricZW_zero
#print axioms QECCertificates.cycMat_mul_blockL_XW
#print axioms QECCertificates.blockL_ZW_mul_transpose
#print axioms QECCertificates.toricXW_ker
#print axioms QECCertificates.toricZW_ker
#print axioms QECCertificates.hgp_toric_k
#print axioms QECCertificates.hgp_toric_dx_lb
#print axioms QECCertificates.hgp_toric_dz_lb
#print axioms QECCertificates.toricXW_not_mem
#print axioms QECCertificates.toricZW_not_mem
#print axioms QECCertificates.cyc9_one_ker
#print axioms QECCertificates.rank_cyc9
#print axioms QECCertificates.cyc9_ker_min
#print axioms QECCertificates.cyc9T_ker_min
#print axioms QECCertificates.toric9_dot
#print axioms QECCertificates.toric9_XW_weight
#print axioms QECCertificates.toric9_ZW_weight
#print axioms QECCertificates.toric9_n
#print axioms QECCertificates.hgp_toric9_k
#print axioms QECCertificates.hgp_toric9_dx_lb
#print axioms QECCertificates.hgp_toric9_dz_lb
#print axioms QECCertificates.hgp_toric9_X_logical
#print axioms QECCertificates.hgp_toric9_Z_logical
#print axioms QECCertificates.cyc12_one_ker
#print axioms QECCertificates.rank_cyc12
#print axioms QECCertificates.cyc12_ker_min
#print axioms QECCertificates.cyc12T_ker_min
#print axioms QECCertificates.toric12_dot
#print axioms QECCertificates.toric12_XW_weight
#print axioms QECCertificates.toric12_ZW_weight
#print axioms QECCertificates.toric12_n
#print axioms QECCertificates.hgp_toric12_k
#print axioms QECCertificates.hgp_toric12_dx_lb
#print axioms QECCertificates.hgp_toric12_dz_lb
#print axioms QECCertificates.hgp_toric12_X_logical
#print axioms QECCertificates.hgp_toric12_Z_logical
#print axioms QECCertificates.sum_two_hot
#print axioms QECCertificates.cycMat_ne_next
#print axioms QECCertificates.cycMat_mulVec_apply
#print axioms QECCertificates.cycMat_one_ker
#print axioms QECCertificates.cycMat_ker_const
#print axioms QECCertificates.cycMatT_mulVec_pred
#print axioms QECCertificates.cycMatT_ker_const
#print axioms QECCertificates.hammingNorm_const
#print axioms QECCertificates.cycMat_ker_min
#print axioms QECCertificates.cycMatT_ker_min
#print axioms QECCertificates.rank_cycMat
#print axioms QECCertificates.hgp_toric_family
#print axioms QECCertificates.toric16_dot
#print axioms QECCertificates.toric16_XW_weight
#print axioms QECCertificates.toric16_ZW_weight
#print axioms QECCertificates.hgp_toric16_k
#print axioms QECCertificates.hgp_toric16_dx_lb
#print axioms QECCertificates.hgp_toric16_dz_lb
#print axioms QECCertificates.hgp_toric16_X_logical
#print axioms QECCertificates.hgp_toric16_Z_logical
-- QECCertificates.Codes.LPAnchor
#print axioms QECCertificates.d6Index_code
#print axioms QECCertificates.d6Code_index
#print axioms QECCertificates.lpAnchor_css
#print axioms QECCertificates.lpAnchor2_css
#print axioms QECCertificates.lpAnchor_k
#print axioms QECCertificates.lpAnchor2_k
#print axioms QECCertificates.lpAnchor_lowerHyp
#print axioms QECCertificates.lpAnchor_lightCand_x
#print axioms QECCertificates.lpAnchor_lightCand_z
#print axioms QECCertificates.lpAnchor2_lightCand_x
#print axioms QECCertificates.lpAnchor2_lightCand_z
#print axioms QECCertificates.lpAnchor_dx
#print axioms QECCertificates.lpAnchor_dz
#print axioms QECCertificates.lpAnchor2_dx
#print axioms QECCertificates.lpAnchor2_dz
-- QECCertificates.Codes.MeasurementProtocol
#print axioms QECCertificates.mem_faultCand
#print axioms QECCertificates.noLightFault_of_faultCand_nil
#print axioms QECCertificates.bare_noLightFault
#print axioms QECCertificates.le_spacetimeWeight
#print axioms QECCertificates.spacetimeWeight_witness
#print axioms QECCertificates.separation_C2
-- QECCertificates.Codes.Separation
#print axioms QECCertificates.expansionOne_complete
#print axioms QECCertificates.not_expansionOne_path
#print axioms QECCertificates.expansionOne_cycle
#print axioms QECCertificates.not_expansionOne_two_edges
#print axioms QECCertificates.timeLikeVec_repCheck
#print axioms QECCertificates.timeLikeVec_ne_zero
#print axioms QECCertificates.hammingNorm_timeLikeVec
#print axioms QECCertificates.exists_undetectable_of_rounds_lt
#print axioms QECCertificates.exists_logicalFault_of_rounds_lt
#print axioms QECCertificates.no_light_undetectable_of_rounds_ge
#print axioms QECCertificates.separation_judgment
#print axioms QECCertificates.C2_not_C1
#print axioms QECCertificates.C1_not_C2
#print axioms QECCertificates.C3_C4_independent
-- QECCertificates.Codes.SeparationClosedForm
#print axioms QECCertificates.mem_completeEdges
#print axioms QECCertificates.cutSize_completeEdges_ge_compl
#print axioms QECCertificates.expansionOne_complete_gen
#print axioms QECCertificates.one_le_c1Witness
#print axioms QECCertificates.separation_closed
#print axioms QECCertificates.toric_family_separation_closed
#print axioms QECCertificates.c1Witness_completeEdges_four
#print axioms QECCertificates.cutSize_completeEdges_exact_four
#print axioms QECCertificates.completeEdges_four_agrees
#print axioms QECCertificates.family_time_component
-- QECCertificates.Codes.SeparationInstances
#print axioms QECCertificates.sepFail_not_C1
#print axioms QECCertificates.sepFail_lightLogical
#print axioms QECCertificates.sepFail_summary
#print axioms QECCertificates.sepKeep_not_C1
#print axioms QECCertificates.sepKeep_no_lightLogical
#print axioms QECCertificates.sepKeep_lightLogical_two
#print axioms QECCertificates.sepKeep_summary
#print axioms QECCertificates.sepFail_dx
#print axioms QECCertificates.sepFail_dz
#print axioms QECCertificates.sepKeep_dx
#print axioms QECCertificates.sepKeep_dz
#print axioms QECCertificates.sepFail_dx_ne_dz
#print axioms QECCertificates.sepKeep_dx_ne_dz
#print axioms QECCertificates.inKerB_e_of_zero_column
#print axioms QECCertificates.minWeight_le_one_of_zero_column
#print axioms QECCertificates.sepFail_dist_le_one_structural
#print axioms QECCertificates.sepFail_ancilla_nine_column_zero
#print axioms QECCertificates.sepKeepPath_not_C1
#print axioms QECCertificates.sepKeepPath_no_lightLogical
#print axioms QECCertificates.sepKeepPath_lightLogical_two
#print axioms QECCertificates.sepKeepPath_summary
#print axioms QECCertificates.shor_generators_independent
-- QECCertificates.Codes.TimeLikeInstance
#print axioms QECCertificates.timeLike34_witness_mem_ker
#print axioms QECCertificates.timeLike34_witness_ne_zero
#print axioms QECCertificates.timeLike34_witness_weight
#print axioms QECCertificates.timeLike34_d
#print axioms QECCertificates.timeLike34_block_witnesses
-- QECCertificates.Codes.ToricFamilySpatial
#print axioms QECCertificates.appendRow_castSucc
#print axioms QECCertificates.appendRow_last
#print axioms QECCertificates.mem_ker_toLin'_iff
#print axioms QECCertificates.mulVec_eq_zero_iff
#print axioms QECCertificates.mem_ker_appendRow
#print axioms QECCertificates.mulVec_appendRow_eq_zero_iff
#print axioms QECCertificates.rowSpace_appendRow_le
#print axioms QECCertificates.le_minWeight_of_lower_appendRow
#print axioms QECCertificates.le_minWeight_of_lower_rowSpace_appendRow
#print axioms QECCertificates.flatVec_apply
#print axioms QECCertificates.flatVec_comp
#print axioms QECCertificates.mulVec_submatrix
#print axioms QECCertificates.mem_ker_submatrix
#print axioms QECCertificates.hammingNorm_flatVec
#print axioms QECCertificates.dotProduct_flatVec
#print axioms QECCertificates.comp_symm_mem_rowSpace
#print axioms QECCertificates.unflatVec_mem_rowSpace
#print axioms QECCertificates.predIdx_val
#print axioms QECCertificates.predIdx_of_succ
#print axioms QECCertificates.succ_of_predIdx
#print axioms QECCertificates.cycMat_col_supp
#print axioms QECCertificates.cycMat_col_sum
#print axioms QECCertificates.cycMatT_one_ker_row
#print axioms QECCertificates.toricRW_inl
#print axioms QECCertificates.toricRW_inr
#print axioms QECCertificates.toricRWZ_inl
#print axioms QECCertificates.toricRWZ_inr
#print axioms QECCertificates.toricRW_ker
#print axioms QECCertificates.toricRWZ_ker
#print axioms QECCertificates.hammingNorm_toricRW
#print axioms QECCertificates.hammingNorm_toricRWZ
#print axioms QECCertificates.dot_toricRW_toricZW
#print axioms QECCertificates.dot_toricRW_toricRWZ
#print axioms QECCertificates.hgpToricXW_inl
#print axioms QECCertificates.hgpToricXW_inr
#print axioms QECCertificates.hgpToricZW_inl
#print axioms QECCertificates.hgpToricZW_inr
#print axioms QECCertificates.dot_toricXW_toricZW
#print axioms QECCertificates.hammingNorm_hgpToricZW
#print axioms QECCertificates.hammingNorm_hgpToricXW
#print axioms QECCertificates.mem_ker_toricHxRows
#print axioms QECCertificates.mem_ker_toricHzRows
#print axioms QECCertificates.rowSpace_toricHxRows
#print axioms QECCertificates.rowSpace_toricHzRows
#print axioms QECCertificates.rowSpace_toricHx_le_gaugedRows
#print axioms QECCertificates.toricRWFin_mem_ker
#print axioms QECCertificates.toricXWFin_not_mem_ker
#print axioms QECCertificates.toricRWFin_not_mem
#print axioms QECCertificates.toricRWZFin_not_mem
#print axioms QECCertificates.rowSpace_toricHxFin_le_gauged
#print axioms QECCertificates.toricGauged_dx_lower
#print axioms QECCertificates.toricGauged_dz_lower
#print axioms QECCertificates.toricRWZFin_mem_ker
#print axioms QECCertificates.hammingNorm_toricRWFin
#print axioms QECCertificates.hammingNorm_toricRWZFin
#print axioms QECCertificates.toric_family_deformed_dx
#print axioms QECCertificates.toric_family_deformed_dz
#print axioms QECCertificates.toric_family_space_bound
#print axioms QECCertificates.toric_family_separation_closed_spatial
#print axioms QECCertificates.space_fault_weight_ge_of_expansion
-- QECCertificates.GF2.Basic
#print axioms QECCertificates.add_eq_zero_iff_eq
#print axioms QECCertificates.mem_support
#print axioms QECCertificates.weight_eq_hammingNorm
#print axioms QECCertificates.add_self
#print axioms QECCertificates.eq_one_of_ne_zero
#print axioms QECCertificates.mem_spanL
#print axioms QECCertificates.subset_spanL
#print axioms QECCertificates.spanL_nil
#print axioms QECCertificates.spanL_append
#print axioms QECCertificates.spanL_singleton
#print axioms QECCertificates.spanL_append_singleton
#print axioms QECCertificates.spanL_mono_of_subset
#print axioms QECCertificates.add_add_left_cancel
#print axioms QECCertificates.add_add_same_left
#print axioms QECCertificates.add_add_same_right
#print axioms QECCertificates.mem_spanL_append_singleton_of_add_mem
#print axioms QECCertificates.spanL_append_eq_of_add_mem
#print axioms QECCertificates.spanL_ofFn_eq_span_range
#print axioms QECCertificates.Matrix.rowSpace_eq_spanL_ofFn
#print axioms QECCertificates.addSmul_apply
#print axioms QECCertificates.addSmul_zero_coord
#print axioms QECCertificates.addSmul_cancel
#print axioms QECCertificates.addSmul_mem_span
#print axioms QECCertificates.spanL_map_addSmul_append
-- QECCertificates.GF2.Canonical
#print axioms QECCertificates.readOff_nil
#print axioms QECCertificates.readOff_apply
#print axioms QECCertificates.readOff_add
#print axioms QECCertificates.readOff_smul
#print axioms QECCertificates.readOff_eq_of_mem_spanL
#print axioms QECCertificates.eq_zero_of_mem_spanL_of_piv_zero
#print axioms QECCertificates.ne_zero_of_piv_eq_one
#print axioms QECCertificates.leadIdx_le_of_ne_zero
#print axioms QECCertificates.eq_zero_of_lt_leadIdx
#print axioms QECCertificates.leadIdx_eq_piv_of_isEchelon
#print axioms QECCertificates.exists_piv_eq_leadIdx_of_mem_spanL
#print axioms QECCertificates.pivRow_mem_iff_of_spanL_eq
#print axioms QECCertificates.isEchelon_rowReduce
#print axioms QECCertificates.rowReduce_mem_iff_of_spanL_eq
-- QECCertificates.GF2.HGP
#print axioms QECCertificates.hgpHX_inl
#print axioms QECCertificates.hgpHX_inr
#print axioms QECCertificates.hgpHZ_inl
#print axioms QECCertificates.hgpHZ_inr
#print axioms QECCertificates.hgp_orthogonal
-- QECCertificates.GF2.HGPCleaning
#print axioms QECCertificates.mem_matRowList
#print axioms QECCertificates.exists_mulVec_of_mem_spanL_colList
#print axioms QECCertificates.mulVec_mem_spanL_colList
#print axioms QECCertificates.exists_coeff_of_mem_spanL_matRowList
#print axioms QECCertificates.preimage_spec
#print axioms QECCertificates.exists_mul_eq_of_rows_mem
#print axioms QECCertificates.dot_eq_zero_of_mem_kerL_of_mem_spanL
#print axioms QECCertificates.exists_ker_dot_ne_zero_of_not_mem
#print axioms QECCertificates.mem_spanL_of_forall_dot_eq_zero
#print axioms QECCertificates.rowDot_hammingNorm_le
#print axioms QECCertificates.colDot_hammingNorm_le
#print axioms QECCertificates.blockL_rows_mem_of_small
#print axioms QECCertificates.blockR_cols_mem_of_small
#print axioms QECCertificates.col_decomp
#print axioms QECCertificates.exists_cleaning_cert
#print axioms QECCertificates.sum_smul_hgpHZ_apply
#print axioms QECCertificates.mem_rowSpace_hgpHZ_of_blocks
#print axioms QECCertificates.hgp_X_distance_ge
#print axioms QECCertificates.blockL_rows_mem_of_H1Ker_trivial
#print axioms QECCertificates.blockL_rows_mem_of_H2Ker_trivial
#print axioms QECCertificates.blockR_cols_mem_of_adjoint_ker_trivial
#print axioms QECCertificates.blockR_cols_mem_of_H2TKer_trivial
#print axioms QECCertificates.hgp_X_distance_ge_of_rowClean_free
#print axioms QECCertificates.hgp_X_distance_ge_of_colClean_free
#print axioms QECCertificates.hgp_X_distance_ge_of_H1Ker_trivial
#print axioms QECCertificates.hgp_X_distance_ge_of_H2Ker_trivial
#print axioms QECCertificates.hgp_X_distance_ge_of_H2TKer_trivial
#print axioms QECCertificates.hgp_X_distance_ge_of_adjoint_ker_trivial
-- QECCertificates.GF2.HGPCleaningDual
#print axioms QECCertificates.swapBlocks_swapBlocks
#print axioms QECCertificates.swapBlocks_injective
#print axioms QECCertificates.hammingNorm_swapBlocks
#print axioms QECCertificates.hgpHZ_row_eq_swap
#print axioms QECCertificates.mulVec_swap_eq
#print axioms QECCertificates.hgpHZ_mulVec_eq_zero_iff_swap
#print axioms QECCertificates.mem_rowSpace_X_of_swap_mem_rowSpace_Z
#print axioms QECCertificates.hgp_Z_distance_ge
#print axioms QECCertificates.hgp_Z_distance_ge_of_H1Ker_trivial
#print axioms QECCertificates.hgp_Z_distance_ge_of_H2TKer_trivial
#print axioms QECCertificates.hgp_Z_distance_ge_of_H1TKer_trivial
#print axioms QECCertificates.hgp_Z_distance_ge_of_H2Ker_trivial
-- QECCertificates.GF2.HGPCompression
#print axioms QECCertificates.blockL_apply
#print axioms QECCertificates.blockR_apply
#print axioms QECCertificates.sum_prod_slice_snd
#print axioms QECCertificates.sum_prod_slice_fst
#print axioms QECCertificates.hgpHX_mulVec_apply
#print axioms QECCertificates.hgpHZ_mulVec_apply
#print axioms QECCertificates.hgpHX_mulVec_eq_zero_iff
#print axioms QECCertificates.hgpHZ_mulVec_eq_zero_iff
#print axioms QECCertificates.hgpHZ_transpose_inputs_apply
#print axioms QECCertificates.hammingNorm_le_of_injective
#print axioms QECCertificates.hgp_hammingNorm_ge_of_pure_left
#print axioms QECCertificates.hgp_hammingNorm_ge_of_pure_right
-- QECCertificates.GF2.HGPKunneth
#print axioms QECCertificates.range_mulLeft
#print axioms QECCertificates.range_mulRight
#print axioms QECCertificates.hgpHX_mulVecLin_eq_blocks
#print axioms QECCertificates.rank_hgpHX_add
#print axioms QECCertificates.rank_hgpHZ_eq
#print axioms QECCertificates.rank_hgpHZ_add
#print axioms QECCertificates.hgp_kunneth_int
#print axioms QECCertificates.hgp_kunneth
-- QECCertificates.GF2.KernelBasis
#print axioms QECCertificates.unitVec_apply
#print axioms QECCertificates.sum_mul_ite_self
#print axioms QECCertificates.sum_mul_ite_eq
#print axioms QECCertificates.sum_ite_self
#print axioms QECCertificates.mem_kerL
#print axioms QECCertificates.kerL_eq_of_spanL_eq
#print axioms QECCertificates.mem_pivCols
#print axioms QECCertificates.IsReduced.row_apply_piv
#print axioms QECCertificates.kerVec_apply
#print axioms QECCertificates.kerVec_apply_free
#print axioms QECCertificates.kerVec_apply_piv
#print axioms QECCertificates.kerVec_mem_kerL
#print axioms QECCertificates.kerVec_ne_zero
#print axioms QECCertificates.hammingNorm_kerVec_le
#print axioms QECCertificates.mem_kerBasis
#print axioms QECCertificates.eq_sum_of_piv_support
#print axioms QECCertificates.eq_zero_of_piv_support
#print axioms QECCertificates.kerL_le_spanL_kerBasis
#print axioms QECCertificates.kerL_rowReduce
#print axioms QECCertificates.exists_light_mem_kerL
#print axioms QECCertificates.exists_light_mem_kerL_apply
#print axioms QECCertificates.LinearMap.ker_eq_kerL_ofFn
#print axioms QECCertificates.LinearMap.ker_eq_spanL_kerBasis_ofFn
-- QECCertificates.GF2.KunnethCore
#print axioms QECCertificates.colOf_apply
#print axioms QECCertificates.rowOf_apply
#print axioms QECCertificates.colOf_add
#print axioms QECCertificates.colOf_smul
#print axioms QECCertificates.rowOf_add
#print axioms QECCertificates.rowOf_smul
#print axioms QECCertificates.mem_colsSub
#print axioms QECCertificates.mem_rowsSub
#print axioms QECCertificates.finrank_colsSub
#print axioms QECCertificates.finrank_rowsSub
#print axioms QECCertificates.linearMap_apply_eq_sum_single
#print axioms QECCertificates.exists_leftInverse_of_linearIndependent
#print axioms QECCertificates.vee_apply
#print axioms QECCertificates.wedge_apply
#print axioms QECCertificates.vee_wedge_of_coords
#print axioms QECCertificates.wedge_vee
#print axioms QECCertificates.rowOf_wedge_mem
#print axioms QECCertificates.rowOf_mem_of_wedge_rowOf_mem
#print axioms QECCertificates.finrank_colsRows
-- QECCertificates.GF2.LiftedProduct
#print axioms QECCertificates.mul_inv_eq_one_iff
#print axioms QECCertificates.inv_mul_eq_one_iff
#print axioms QECCertificates.leftMulMat_mul_rightMulMat
#print axioms QECCertificates.lpExpandR_apply
#print axioms QECCertificates.lpExpandL_apply
#print axioms QECCertificates.lpHX_inl
#print axioms QECCertificates.lpHX_inr
#print axioms QECCertificates.lpHZ_inl
#print axioms QECCertificates.lpHZ_inr
#print axioms QECCertificates.lp_orthogonal
#print axioms QECCertificates.lp2HX_inl
#print axioms QECCertificates.lp2HX_inr
#print axioms QECCertificates.lp2HZ_inl
#print axioms QECCertificates.lp2HZ_inr
#print axioms QECCertificates.lp2_orthogonal
#print axioms QECCertificates.lp_qubit_count
#print axioms QECCertificates.lp_row_count_X
#print axioms QECCertificates.lp_row_count_Z
#print axioms QECCertificates.lp2_qubit_count
#print axioms QECCertificates.lpExpandR_liftConst
#print axioms QECCertificates.lpExpandL_liftConst
#print axioms QECCertificates.lpHX_liftConst_inl
#print axioms QECCertificates.lpHX_liftConst_inr
#print axioms QECCertificates.lpHZ_liftConst_inl
#print axioms QECCertificates.lpHZ_liftConst_inr
#print axioms QECCertificates.lp_trivialGroup_eq_hgp
#print axioms QECCertificates.lp_trivialGroup_eq_hgp_Z
-- QECCertificates.GF2.LowerBound
#print axioms QECCertificates.mem_lightSet
#print axioms QECCertificates.mem_lightCand
#print axioms QECCertificates.lowerHyp_of_lightSet_card_zero
#print axioms QECCertificates.le_minWeight_of_lightSet_card_zero
#print axioms QECCertificates.lowerHyp_of_lightCand_nil
#print axioms QECCertificates.le_minWeight_of_lightCand_nil
#print axioms QECCertificates.eq_minWeight_of_lightCand_nil
#print axioms QECCertificates.eq_minWeight_of_decide
#print axioms QECCertificates.lightCand_length_le
#print axioms QECCertificates.lightSet_card_le
#print axioms QECCertificates.mem_ker_of_inKerB
#print axioms QECCertificates.not_mem_rowSpace_of_dualCheck
#print axioms QECCertificates.not_mem_rowSpace_of_inSpanB_false
-- QECCertificates.GF2.Membership
#print axioms QECCertificates.reduceAgainst_zero
#print axioms QECCertificates.reduceAgainst_add
#print axioms QECCertificates.reduceAgainst_smul
#print axioms QECCertificates.reduceAgainst_self_mem
#print axioms QECCertificates.reduceAgainst_eq_zero_of_mem_spanL
#print axioms QECCertificates.inSpanB_sound
#print axioms QECCertificates.inSpanB_complete
#print axioms QECCertificates.inSpanB_iff
#print axioms QECCertificates.inSpanB_eq_false_iff
#print axioms QECCertificates.inKerB_iff
-- QECCertificates.GF2.RankCertificate
#print axioms QECCertificates.nodupPiv_nil
#print axioms QECCertificates.map_piv_insertPivot
#print axioms QECCertificates.nodupPiv_insertPivot
#print axioms QECCertificates.nodupPiv_step
#print axioms QECCertificates.nodupPiv_rowReduceFrom
#print axioms QECCertificates.nodupPiv_rowReduce
#print axioms QECCertificates.IsReduced.tail
#print axioms QECCertificates.nodup_of_nodupPiv
#print axioms QECCertificates.linearIndependent_rowList_of_isReduced
#print axioms QECCertificates.range_get_eq_rowList
#print axioms QECCertificates.card_pivCols_eq_length
#print axioms QECCertificates.finrank_spanL_eq_length_of_isReduced
#print axioms QECCertificates.finrank_spanL_eq_length_rowReduce
#print axioms QECCertificates.length_rowReduce_le
#print axioms QECCertificates.Matrix.rank_eq_finrank_rowSpace
#print axioms QECCertificates.Matrix.rank_eq_length_rowReduce
#print axioms QECCertificates.exists_ne_zero_mulVec_eq_zero_of_rank_lt
-- QECCertificates.GF2.RankEchelon
#print axioms QECCertificates.rowList_insertPivotA
#print axioms QECCertificates.spanL_rowList_stepA
#print axioms QECCertificates.spanL_rowList_foldl_stepA
#print axioms QECCertificates.spanL_rowList_echelonFrom
#print axioms QECCertificates.EchSelf.tail
#print axioms QECCertificates.EchPair.tail
#print axioms QECCertificates.EchPair.head_rows
#print axioms QECCertificates.reduceAgainst_get_piv_eq_zero
#print axioms QECCertificates.linearIndependent_get_of_echelon
#print axioms QECCertificates.echSelf_nil
#print axioms QECCertificates.echPair_nil
#print axioms QECCertificates.length_append_singleton
#print axioms QECCertificates.get_append_singleton_cast
#print axioms QECCertificates.get_append_singleton_last
#print axioms QECCertificates.EchSelf_append
#print axioms QECCertificates.EchPair_append
#print axioms QECCertificates.EchSelf_stepA
#print axioms QECCertificates.EchPair_stepA
#print axioms QECCertificates.echSelf_echelonFrom_foldl
#print axioms QECCertificates.echelonFrom_ech
#print axioms QECCertificates.finrank_spanL_eq_length_echelonFrom
#print axioms QECCertificates.rankEchelon_eq_length_rowReduce
#print axioms QECCertificates.Matrix.rank_eq_rankEchelon
#print axioms QECCertificates.eq_zero_of_mem_spanL_of_piv_eq_zero
#print axioms QECCertificates.reduceAgainst_echelonFrom_eq_zero_of_mem_spanL
#print axioms QECCertificates.inSpanEch_sound
#print axioms QECCertificates.inSpanEch_complete
#print axioms QECCertificates.inSpanEch_iff
#print axioms QECCertificates.finrank_spanL_le_length
#print axioms QECCertificates.finrank_spanL_le_of_mem_of_subset
#print axioms QECCertificates.finrank_spanL_append_le_of_mem
#print axioms QECCertificates.length_le_finrank_spanL_of_certificate
#print axioms QECCertificates.inSpanEch_eq_false_iff
-- QECCertificates.GF2.RowReduce
#print axioms QECCertificates.rowList_nil
#print axioms QECCertificates.rowList_cons
#print axioms QECCertificates.rowList_append
#print axioms QECCertificates.isReduced_nil
#print axioms QECCertificates.IsReduced.pivot_inj
#print axioms QECCertificates.reduceAgainst_nil
#print axioms QECCertificates.reduceAgainst_cons
#print axioms QECCertificates.reduceAgainst_eq_zero_of_rows_zero
#print axioms QECCertificates.reduceAgainst_apply_piv
#print axioms QECCertificates.add_reduceAgainst_mem
#print axioms QECCertificates.support_nonempty
#print axioms QECCertificates.leadIdx_spec
#print axioms QECCertificates.leadIdx_eq_one
#print axioms QECCertificates.rowList_insertPivot
#print axioms QECCertificates.spanL_rowList_insertPivot
#print axioms QECCertificates.isReduced_insertPivot
#print axioms QECCertificates.spanL_rowList_step
#print axioms QECCertificates.isReduced_step
#print axioms QECCertificates.rowReduceFrom_nil
#print axioms QECCertificates.rowReduceFrom_cons
#print axioms QECCertificates.spanL_rowList_rowReduceFrom
#print axioms QECCertificates.isReduced_rowReduceFrom
#print axioms QECCertificates.spanL_rowReduce
#print axioms QECCertificates.isReduced_rowReduce
-- QECCertificates.GF2.WeightEnum
#print axioms QECCertificates.snocV_castSucc
#print axioms QECCertificates.castSuccEmb_apply
#print axioms QECCertificates.snocV_last
#print axioms QECCertificates.snocV_zero_zero
#print axioms QECCertificates.snocV_prefix_last
#print axioms QECCertificates.wtRec_zero
#print axioms QECCertificates.wtRec_succ
#print axioms QECCertificates.lightVecs_nil
#print axioms QECCertificates.lightVecs_zero
#print axioms QECCertificates.lightVecs_succ_succ
#print axioms QECCertificates.wtRec_eq_zero_iff
#print axioms QECCertificates.mem_lightVecs
#print axioms QECCertificates.wt_le_of_mem_lightVecs
#print axioms QECCertificates.wtRec_eq_card_support
#print axioms QECCertificates.wtRec_eq_hammingNorm
#print axioms QECCertificates.length_lightVecs
-- QECCertificates.GF2.Witness
#print axioms QECCertificates.DualWitness.not_mem_rowSpace
#print axioms QECCertificates.exists_dualWitness_iff
#print axioms QECCertificates.mem_image_hammingNorm_of_witness
#print axioms QECCertificates.minWeight_le_of_witness
#print axioms QECCertificates.le_minWeight_of_lower
#print axioms QECCertificates.eq_minWeight_of_bounds
-- QECCertificates.Pauli.Expr
#print axioms QECCertificates.Pauli.mul_I_left
#print axioms QECCertificates.Pauli.mul_I_right
#print axioms QECCertificates.Pauli.mul_self
#print axioms QECCertificates.Pauli.mul_comm
#print axioms QECCertificates.Pauli.mul_assoc
#print axioms QECCertificates.Pauli.symp_mul
#print axioms QECCertificates.Pauli.anti_self
#print axioms QECCertificates.Pauli.anti_comm
#print axioms QECCertificates.Pauli.anti_eq_symp
#print axioms QECCertificates.sympWord_fst
#print axioms QECCertificates.sympWord_snd
#print axioms QECCertificates.commutesWord_symm
#print axioms QECCertificates.commutesWord_self
#print axioms QECCertificates.commutesWord_iff_symplectic
#print axioms QECCertificates.PauliExpr.eval_one
#print axioms QECCertificates.PauliExpr.eval_mul
#print axioms QECCertificates.PauliExpr.toSymp_one
#print axioms QECCertificates.PauliExpr.toSymp_mul
#print axioms QECCertificates.PauliExpr.toSymp_atom
#print axioms QECCertificates.PauliExpr.commutes_iff_symplectic
-- QECCertificates.Reflect.Certified
#print axioms QECCertificates.LRAT.vecOf_apply_ne_zero
#print axioms QECCertificates.LRAT.support_vecOf_card
#print axioms QECCertificates.LRAT.cntS_cons
#print axioms QECCertificates.LRAT.even_one_add
#print axioms QECCertificates.LRAT.dotS_eq_false_iff_even
#print axioms QECCertificates.LRAT.natCast_zmod2_eq_zero_iff_even
#print axioms QECCertificates.LRAT.dotProduct_rowOf_vecOf
#print axioms QECCertificates.LRAT.sum_indicator_eq_cntS
#print axioms QECCertificates.LRAT.dotS_eq_false_iff_dotProduct
#print axioms QECCertificates.LRAT.zmod2_eq_one_of_ne_zero
#print axioms QECCertificates.LRAT.zmod2_indicator
#print axioms QECCertificates.LRAT.certAssign_lt
#print axioms QECCertificates.LRAT.certAssign_mid
#print axioms QECCertificates.LRAT.vecOf_certAssign
#print axioms QECCertificates.LRAT.vecOf_certAssign_shift
#print axioms QECCertificates.LRAT.vecOf_and
#print axioms QECCertificates.LRAT.rowOf_range
#print axioms QECCertificates.LRAT.all_of_mem_bounds
#print axioms QECCertificates.LRAT.all_of_mem_nodup
#print axioms QECCertificates.LRAT.all_of_mem_ne_nil
#print axioms QECCertificates.LRAT.no_light_logical_of_unsat
#print axioms QECCertificates.LRAT.rep7_no_light_logical_of_certificate
#print axioms QECCertificates.LRAT.steane_no_light_logical_of_certificate
#print axioms QECCertificates.LRAT.hgp_toric3Ker_rows_ne_toric3Hx
#print axioms QECCertificates.LRAT.hgp_toric3_no_light_logical_of_certificate
#print axioms QECCertificates.LRAT.bb18_no_light_logical_of_certificate
-- QECCertificates.Reflect.Complete
#print axioms QECCertificates.LRAT.chainFill_nil
#print axioms QECCertificates.LRAT.chainFill_cons
#print axioms QECCertificates.LRAT.chainFill_self
#print axioms QECCertificates.LRAT.chainFill_succ
#print axioms QECCertificates.LRAT.chainFill_eq_false_of_lt
#print axioms QECCertificates.LRAT.chainFill_congr
#print axioms QECCertificates.LRAT.chainAssign_of_lt
#print axioms QECCertificates.LRAT.chainAssign_succ
#print axioms QECCertificates.LRAT.chainAssign_self
#print axioms QECCertificates.LRAT.chainAssign_congr
#print axioms QECCertificates.LRAT.chainAssign_tail
#print axioms QECCertificates.LRAT.xorStepClauses_sat_of
#print axioms QECCertificates.LRAT.xorChainAux_complete
#print axioms QECCertificates.LRAT.xorChainAux_snd
#print axioms QECCertificates.LRAT.xorStepClauses_vars
#print axioms QECCertificates.LRAT.xorChainAux_vars_lt
#print axioms QECCertificates.LRAT.satClause_of_agree
#print axioms QECCertificates.LRAT.chainsFrom_complete
#print axioms QECCertificates.LRAT.prodFill_at
#print axioms QECCertificates.LRAT.prodClauses_three_sat
#print axioms QECCertificates.LRAT.prodFill_of_lt
#print axioms QECCertificates.LRAT.prodClauses_complete
#print axioms QECCertificates.LRAT.slotBase_succ
#print axioms QECCertificates.LRAT.slotBase_mono
#print axioms QECCertificates.LRAT.slotBase_pred
#print axioms QECCertificates.LRAT.slotVar_of_le
#print axioms QECCertificates.LRAT.slotVar_eq_none
#print axioms QECCertificates.LRAT.decide_imp
#print axioms QECCertificates.LRAT.decide_imp2
#print axioms QECCertificates.LRAT.sat_two_of_imp
#print axioms QECCertificates.LRAT.sat_three_of_imp
#print axioms QECCertificates.LRAT.sat_three_of_imp2
#print axioms QECCertificates.LRAT.sat_three_of_imp3
#print axioms QECCertificates.LRAT.slotClauses_eq_some_some
#print axioms QECCertificates.LRAT.slotClauses_eq_some_none
#print axioms QECCertificates.LRAT.slotClauses_eq_none_some
#print axioms QECCertificates.LRAT.slotClauses_eq_none_none
#print axioms QECCertificates.LRAT.rowClauses_complete
#print axioms QECCertificates.LRAT.rowFill_at
#print axioms QECCertificates.LRAT.rowFill_of_notMem
#print axioms QECCertificates.LRAT.rowFill_prev
#print axioms QECCertificates.LRAT.atMostK_complete
#print axioms QECCertificates.LRAT.xorChain_snd_ge
#print axioms QECCertificates.LRAT.chainsFrom_snd_ge
#print axioms QECCertificates.LRAT.chainsFrom_vars_lt
#print axioms QECCertificates.LRAT.prodClauses_vars_lt
#print axioms QECCertificates.LRAT.xorChain_vars_lt
#print axioms QECCertificates.LRAT.satFormula_of_agree
#print axioms QECCertificates.LRAT.agree_le_trans
#print axioms QECCertificates.LRAT.xorChain_complete
#print axioms QECCertificates.LRAT.buildPair_complete
-- QECCertificates.Reflect.Encode
#print axioms QECCertificates.LRAT.dotS_nil
#print axioms QECCertificates.LRAT.dotS_cons
#print axioms QECCertificates.LRAT.dotS_append
#print axioms QECCertificates.LRAT.cntS_nil
#print axioms QECCertificates.LRAT.cntS_append
#print axioms QECCertificates.LRAT.cntS_singleton_true
#print axioms QECCertificates.LRAT.cntS_singleton_false
#print axioms QECCertificates.LRAT.cntS_le_length
#print axioms QECCertificates.LRAT.sat_two
#print axioms QECCertificates.LRAT.sat_three
#print axioms QECCertificates.LRAT.xorStep_sat
#print axioms QECCertificates.LRAT.xorChainAux_sat
#print axioms QECCertificates.LRAT.xorChain_sat
#print axioms QECCertificates.LRAT.xorChain_sat'
#print axioms QECCertificates.LRAT.SlotOK.some_of
#print axioms QECCertificates.LRAT.SlotOK.none_of
#print axioms QECCertificates.LRAT.mem_rowClauses
#print axioms QECCertificates.LRAT.atMostKAux_sat
#print axioms QECCertificates.LRAT.atMostK_sat
#print axioms QECCertificates.LRAT.satFormula_append
#print axioms QECCertificates.LRAT.SatFormula.forall
#print axioms QECCertificates.LRAT.dotS_map
#print axioms QECCertificates.LRAT.dotS_congr
#print axioms QECCertificates.LRAT.cntS_map
#print axioms QECCertificates.LRAT.prod_sat
#print axioms QECCertificates.LRAT.prodClauses_sat
#print axioms QECCertificates.LRAT.chainsFrom_sat
#print axioms QECCertificates.LRAT.slotVar_ok
#print axioms QECCertificates.LRAT.buildPair_sat
-- QECCertificates.Reflect.Faithful
#print axioms QECCertificates.LRAT.rep7_eq
#print axioms QECCertificates.LRAT.steane_eq
#print axioms QECCertificates.LRAT.hgp_toric3_eq
#print axioms QECCertificates.LRAT.bb18_lb3_eq
#print axioms QECCertificates.LRAT.rep7_certified
#print axioms QECCertificates.LRAT.steane_certified
#print axioms QECCertificates.LRAT.hgp_toric3_certified
#print axioms QECCertificates.LRAT.bb18_lb3_certified
-- QECCertificates.Reflect.FaithfulCircuit
#print axioms QECCertificates.LRAT.timelike34_eq
#print axioms QECCertificates.LRAT.timelike34Ker_rows
#print axioms QECCertificates.LRAT.timelike34_certified
#print axioms QECCertificates.LRAT.bbgauge44_eq
#print axioms QECCertificates.LRAT.bbgauge44Ker_rows
#print axioms QECCertificates.LRAT.bbgauge44_certified
-- QECCertificates.Reflect.LRAT
#print axioms QECCertificates.LRAT.scanAux_spec
#print axioms QECCertificates.LRAT.scan_nil
#print axioms QECCertificates.LRAT.scan_singleton
#print axioms QECCertificates.LRAT.litFree_eq_false
#print axioms QECCertificates.LRAT.rupAux_sound
#print axioms QECCertificates.LRAT.checkAux_sound
#print axioms QECCertificates.LRAT.checkSteps_sound
#print axioms QECCertificates.LRAT.unsat_of_checkSteps
-- QECCertificates.Reflect.LRATData
#print axioms QECCertificates.LRAT.rep7_unsat
#print axioms QECCertificates.LRAT.steane_unsat
#print axioms QECCertificates.LRAT.hgp_toric3_unsat
#print axioms QECCertificates.LRAT.bb18_lb3_unsat
-- QECCertificates.Reflect.LRATDataCircuit
#print axioms QECCertificates.LRAT.bbgauge44_unsat
#print axioms QECCertificates.LRAT.timelike34_unsat
-- QECCertificates.Reflect.LexLeader
#print axioms QECCertificates.LRAT.satClause_three
#print axioms QECCertificates.LRAT.satClause_four
#print axioms QECCertificates.LRAT.satClause_one
#print axioms QECCertificates.LRAT.satClause_two
#print axioms QECCertificates.LRAT.head_iff
#print axioms QECCertificates.LRAT.step_iff
#print axioms QECCertificates.LRAT.mem_head
#print axioms QECCertificates.LRAT.mem_step
#print axioms QECCertificates.LRAT.mem_order
#print axioms QECCertificates.LRAT.mem_constraint
#print axioms QECCertificates.LRAT.eVar_spec
#print axioms QECCertificates.LRAT.lexClauses_sat
-- QECCertificates.Reflect.LexComplete
#print axioms QECCertificates.LRAT.eVal_spec
#print axioms QECCertificates.LRAT.eVal_succ
#print axioms QECCertificates.LRAT.eVal_one
#print axioms QECCertificates.LRAT.lexExtend_of_lt
#print axioms QECCertificates.LRAT.lexExtend_of_mem
#print axioms QECCertificates.LRAT.lexExtend_eVar
#print axioms QECCertificates.LRAT.idx_mem
#print axioms QECCertificates.LRAT.satClause_two_of
#print axioms QECCertificates.LRAT.satClause_three_of
#print axioms QECCertificates.LRAT.satClause_four_of
#print axioms QECCertificates.LRAT.lexClauses_complete
-- QECCertificates.Reflect.SBAssembly
#print axioms QECCertificates.LRAT.lexHead_length
#print axioms QECCertificates.LRAT.lexStep_length
#print axioms QECCertificates.LRAT.lexOrder_length
#print axioms QECCertificates.LRAT.lexConstraint_length
#print axioms QECCertificates.LRAT.length_flatMap_const
#print axioms QECCertificates.LRAT.lexClauses_length
#print axioms QECCertificates.LRAT.sbBlocks_length
#print axioms QECCertificates.LRAT.sbCNF_length
#print axioms QECCertificates.LRAT.sbBlocks_sat_cons
#print axioms QECCertificates.LRAT.sbBlocks_sat
#print axioms QECCertificates.LRAT.sbCNF_sat
#print axioms QECCertificates.LRAT.sbCNF_buildPair_sat
-- QECCertificates.Reflect.SymmetryBreak
#print axioms QECCertificates.mem_orbitOf
#print axioms QECCertificates.self_mem_orbitOf
#print axioms QECCertificates.exists_min_orbitOf
#print axioms QECCertificates.orbitMin_iff_exists
#print axioms QECCertificates.not_exists_of_not_exists_orbitMin
#print axioms QECCertificates.bb144Group_one_mem
#print axioms QECCertificates.bb144_isLogical_invariant
