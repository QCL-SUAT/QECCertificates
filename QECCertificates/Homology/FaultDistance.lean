/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
import QECCertificates.Homology.FaultComplex
import QECCertificates.Homology.FaultComplexKunneth
import QECCertificates.Homology.HypergraphSurgery
import QECCertificates.Homology.SubcodeLayer
import QECCertificates.GF2.LowerBound

open QECCertificates

/-!
# The **object layer** of the spacetime fault distance: one predicate, two special cases

## Which layer is missing

Item 1 of `the gauged-measurement companion development's `SurgeryProtocol` module` §5 records the gap in [14] Theorem 6.5 as three
layers; the first is: **the library has no object able to carry the predicate "minimum
weight over the spacetime fault complex"** -- the two existing distance objects each say
their own thing and are unconnected:

* the static code distance `min_weight_ker_not_mem_rowspace` (the `GF2/Witness.lean`
  line): the minimum weight over `ker M₁ \ rowSpace M₂`;
* the timelike `protocolTime_minWeight` (`Homology/HypergraphSurgery.lean`): the minimum
  weight over the "nonzero timelike faults".

The two have a similar shape (both are "the minimum weight over some GF(2) set"), yet
no theorem connects them. This module supplies that layer, and **proves the two to be
special cases of one predicate** (§3, §4).

## The predicate: three things, kept **separate**

The fault complex of [14], $F_3 \to F_2 \to F_1 \to F_0$ (`Homology/FaultComplex.lean`),
puts the **fault locations** (Pauli errors on data qubits, check errors on ancillas,
measurement errors) and the **detectors** ($F_0$ / $F_3$) on **different terms**. A fault
configuration is a GF(2) vector on one term, so the three things are each an independent
condition:

* where the fault sits **in spacetime**: the index type (e.g.
  `TimeFault k S = Fin k × Fin (S+1)`, i.e. "which law, which round"); as a vector,
  `f : ι → ZMod 2`.
* **undetectable** (the syndrome is all silent): the library's `inKerB` /
  `LinearMap.ker M.toLin'`; here `IsDetectorSilent Det f`.
* **flips the logical readout** (the readout functional takes value $1$): the readout
  predicate of `faultCand` / a dual witness; here `FlipsReadout R f`.

**These three things are separate in this library, and this module likewise keeps the
latter two separate** -- the two conjuncts of `IsUndetectedLogicalFault` are **not
merged**. "detectors all silent" and "flips the logical readout" are two problems, and
this is a fact the sister repository's
`QuantumCodeCertificates/the gauged-measurement companion development's `LineSideBBGauge` module` §4 already states in machine form
(`bbGaugeLine_kernel_nonlogical`: an element of the kernel of weight $8$ that does **not**
flip the readout); folding the two into one condition would erase that distinction.

The relation between the readout-functional entry and the subspace form is a
**duality**: $f \notin W$ if and only if there is a linear functional that takes $0$ on
all of $W$ and reads $1$ on $f$. This bridge has had its standard form in the library all
along (`DualWitness` and `exists_dualWitness_iff`, `GF2/Witness.lean`), and this module
wraps it as the statement "the family of readout functionals = the dual of $W$" (§2,
`flipsReadout_readoutsOf_iff`), so that "flips the logical readout" and "does not belong
to the trivial fault subspace" are **two ways of writing the same sentence**.

## The two special cases

* **Static side** (§3): when the time axis degenerates to a single time slice, take
  `Det = M₁` (the check matrix) and `Triv = M₂.rowSpace` ("those that are boundaries");
  the general predicate is **verbatim**
  $E \in \ker M_1 \wedge E \notin \mathrm{rowSpace}\,M_2$ -- exactly the set that
  `min_weight_ker_not_mem_rowspace` takes; the distances are therefore equal
  (`faultDistance_static`).
* **Timelike side** (§4): take `Det = timeLikeDetector k S` (the comparison of adjacent
  rounds of the same law: row index `Fin k × Fin S`, column index
  `Fin k × Fin (S + 1)` = `TimeFault k S`) and `Triv = ⊥` (on the timelike chain there is
  no notion of "boundary", so nonzero means logical); the general predicate is exactly
  the set of `protocolTime_minWeight`; the distances are therefore both $S + 1$
  (`faultDistance_timeLike`).

## The interface with the fault complex (§5)

`faultComplexDistanceZ` / `faultComplexDistanceX` place the general predicate **directly
on `FaultComplex`**: for the former the faults are elements of $F_1$, the detector is
$\partial_0$, and the trivial faults are the image of $\partial_1$; the latter is
symmetric ($F_2$, $\partial_1$, the image of $\partial_2$). Under the correspondence of
[14] p.63 they are the minimum weights on $H_1(F)$ (logical $\overline Z$ faults) and
$H^2(F)$ (logical $\overline X$ faults) respectively. The role of the complex condition
$\partial_0\partial_1 = 0$ is also exhibited explicitly there (`range_fd1_le_ker_fd0`):
**every trivial fault is undetectable**, so quotienting them out quotients out nothing
"detectable".

## Numerical identity at the complex layer (§6, §7)

Once §5 has put the predicate on the complex, there remains **one step of index
transport** (honest boundary 2 below): the fault index of the complex is a product / sum
type (like $\mathrm{Fin}\,k \times \mathrm{Fin}\,S$), while the index of
`min_weight_ker_not_mem_rowspace` is $\mathrm{Fin}\,k$. §6 supplies that layer as a
**general transport lemma** (relabelling, time-slice embedding and contraction, the slice
readings of Kronecker, the transpose row-space bridge), and §7 uses it to prove the two
distances on the **degenerate** (no coupling along the time direction) fault complex to be
the same number (`faultComplexDistanceZ_degenerate`).

## Honest boundaries (the paper text cites this paragraph)

1. **The two special cases are "one shape, different values", not "two theorems merged".**
   What the static and timelike sides share is only the **shape of the predicate**
   ("detectors silent and not trivial"); the source of their respective "trivial"
   subspaces is completely different -- on the static side it is the row space of another
   set of checks, on the timelike side it is $\bot$. This module does **not** claim that
   the two have a common physical interpretation, nor that in the general case the
   definition "logical = non-boundary" **is** the convention of [14].
2. **The numerical identity of `faultComplexDistanceZ` and
   `min_weight_ker_not_mem_rowspace` -- proved on the degenerate complex (§6, §7).** On
   the degenerate fault complex with **no coupling along the time direction** ($R_1 =
   \varnothing$, `degenerateFaultComplex`), $\partial_0$ is just $H_X \otimes 1_S$
   (`degenerateFaultComplex_d01_00`) and the image of $\partial_1$ is $H_Z$'s row space
   taken **time slice by time slice** (`degenerateFaultComplex_d02_01` +
   `degenerate_fd1_mem_range`), so the two distances give **the same number**:

   > `faultComplexDistanceZ_degenerate`:
   > `faultComplexDistanceZ (degenerateFaultComplex …)`
   > `= min_weight_ker_not_mem_rowspace Hx Hz`.

   The **transport layer** of this step (§6) is general lemmas: the relabelling between
   the index of $F_1$, $(\mathrm{Fin}\,m \times \mathrm{Fin}\,0) \oplus
   (\mathrm{Fin}\,k \times \mathrm{Fin}\,S)$, and the $\mathrm{Fin}\,k$ of
   `min_weight_ker_not_mem_rowspace` is carried by `hammingNorm_sum_inr` (sum type),
   `hammingNorm_sliceEmbed` ($\mathrm{Fin}\,k \leftrightarrow$ the $t_0$-th slice of
   $\mathrm{Fin}\,k \times \mathrm{Fin}\,S$) and `hammingNorm_slice_le` (slice
   contraction); "the image of $\partial_1$ = $H_Z$'s row space" is given by
   `mem_rowSpace_iff_exists_transpose_mulVec` (reusing
   `range_toLin'_eq_transpose_rowSpace` of `Homology/SubcodeLayer.lean`); the **slice
   readings** of Kronecker and block matrices are given by `kronecker_one_dot` /
   `kronecker_one_mulVec_apply` / `fd0_row_dot` / `fd1_row_dot`, and the time-slice
   description of $\ker\partial_0$ and $\mathrm{im}\,\partial_1$ is
   `degenerate_fd0_mem_ker` / `degenerate_fd1_mem_range`. The theorem carries the two
   hypotheses `0 < S` and `(undetectableSet Hx Hz).Nonempty` (the reason is the next
   item).

   **The case $R \ne 0$ is not inside this item** -- there the image of $\partial_1$ is no
   longer slicewise, and the slice argument of this item does not apply; this does not
   conflict with §3, "the static side is a special case", which is proved at the **general
   predicate** layer (both sides have $\mathrm{Fin}\,n$ indices, so nothing has to be
   transported): the two are one special case written at two layers. **That case is
   closed in §8 and §10**: when R is the repetition-code foliation the distance is exactly
   the number of rounds $+1$ -- §8 is the special case with $C$ trivial
   (`faultComplexDistanceZ_koszulTimeLike`), and §10 extends it to **arbitrary $C$**
   (`faultComplexDistanceZ_koszul_repR`, under the hypothesis
   $\mathrm{im}\,dC_1\ne\top$, i.e. $H_0(C)\ne0$). The conclusion is **independent of
   $C$**: $C$ only decides whether there is a fault, not how many. This cross-checks with
   `faultDistance_timeLike` of §4 ($S+1$).
3. **Two empty-set conventions.** Upstream `min_weight_ker_not_mem_rowspace` returns
   $n + 1$ when `ker M₁ \ rowSpace M₂` is empty (the `⊤` branch of `Finset.min`), whereas
   this module's `faultDistance` uses `sInf`, giving $0$ on the empty set (the $\bot$ of
   `ℕ`). The static-side theorem therefore carries a nonemptiness hypothesis
   (`faultDistance_static`) -- **this is not a technical hypothesis but exactly where the
   two definitions differ**: a statable version must say what the degenerate case takes,
   and this module chooses to write the nonemptiness out explicitly rather than quietly
   change the convention.
4. **The "flips the logical readout" entry is really used only on the static side**
   (there the family of readout functionals is the dual of $M_2$'s row space). The
   timelike side's `Triv = ⊥` corresponds to "the family of readout functionals = all
   functionals", i.e. "any nonzero fault flips some readout" -- this is the convention
   already in the library, in `bare_noLightFault` and `Codes/MeasurementProtocol.lean`
   (with no in-round checks, the single-round fault distance is $= 1$); this module
   follows it and adds no physical content.
5. **Not in this module**: the dimensions of $H_1$/$H^2$ and the Künneth formula are
   already in place in `Codes/FaultComplexKunneth` -- the four degrees on general $R$,
   instantiated at the two routine foliations used on p.63 (the repetition code and its
   dual), giving the count for each of the two fault types (that module's §4.21). The
   **fault-distance conclusion** of [14] Thm 6.5 itself is still not done; this module
   supplies only the object layer and the two special cases.

**Trusted base**: this module uses no `sorry` / `admit` / `native_decide` and introduces
no custom axioms; the `#print axioms` of the load-bearing theorems is declared by the root
module `QECCertificates.lean`.
-/

namespace QECCertificates.Homology

open scoped BigOperators

open _root_.Matrix

/-! ## 1. The predicate: detectors silent, readout flipped -/

/-- **All detectors silent**: the fault `f` is sent to zero by **every** detector, i.e.
the syndrome is zero.

The row index type `ρ` of the detector matrix is arbitrary (in the timelike instance it is
"law × adjacent round pair", `Fin k × Fin S`; in the static instance it is the check
label `Fin m`), and the index type `ι` of the fault vector is the **spacetime fault
location**. -/
def IsDetectorSilent {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (Det : Matrix ρ ι (ZMod 2)) (f : ι → ZMod 2) : Prop :=
  f ∈ LinearMap.ker Det.toLin'

/-- **The family of readout functionals**: the linear functionals that **vanish on all
of** the "trivial fault" subspace `Triv`.

Over GF(2) the dual space has the same dimension as the vector space and the pairing is
given by the dot product, so a functional is represented by a vector `r` (the readout is
`r ⬝ᵥ f`). This set is exactly the orthogonal complement of `Triv` under the dot-product
pairing. -/
def readoutsOf {ι : Type*} [Fintype ι] (Triv : Submodule (ZMod 2) (ι → ZMod 2)) :
    Set (ι → ZMod 2) :=
  {r | ∀ w ∈ Triv, r ⬝ᵥ w = 0}

/-- **Flips the logical readout**: some functional in the family of readout functionals
reads `1` on `f`. -/
def FlipsReadout {ι : Type*} [Fintype ι] (R : Set (ι → ZMod 2)) (f : ι → ZMod 2) : Prop :=
  ∃ r ∈ R, r ⬝ᵥ f = 1

/-- **An undetectable logical fault** (subspace form): the detectors are all silent **and**
the fault is not trivial (it does not lie in `Triv`, which is spanned by the faults "that
are the boundary of something").

The two conjuncts are **kept separate**: the first is "it was not found", the second is
"it really flipped the logic". Folding them into one condition would erase the
distinction of `QuantumCodeCertificates/the gauged-measurement companion development's `LineSideBBGauge` module` §4. -/
def IsUndetectedLogicalFault {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (Det : Matrix ρ ι (ZMod 2)) (Triv : Submodule (ZMod 2) (ι → ZMod 2))
    (f : ι → ZMod 2) : Prop :=
  IsDetectorSilent Det f ∧ f ∉ Triv

/-- **An undetectable logical fault** (readout-functional form): the detectors are all
silent **and** some readout reads `1`.

It is **equivalent** to the subspace form when `R = readoutsOf Triv` and `Triv` is a row
space (§2, `isUndetectedLogicalFaultR_iff_rowSpace`), i.e. "flips the logical readout" and
"does not belong to the trivial faults" are the same sentence, dually. -/
def IsUndetectedLogicalFaultR {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (Det : Matrix ρ ι (ZMod 2)) (R : Set (ι → ZMod 2)) (f : ι → ZMod 2) : Prop :=
  IsDetectorSilent Det f ∧ FlipsReadout R f

/-! ## 2. The fault distance and three basic bridges -/

/-- **The fault distance**: the minimum weight of an undetectable logical fault.

We take `sInf` rather than `Finset.min`: in general the predicate acts on an **infinite**
set of subspace type (`Triv` is a subspace, not a finite list), and on ℕ `sInf` gives `0`
on the empty set and the minimum on a nonempty one (see honest boundary 3 in the module
header). -/
noncomputable def faultDistance {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (Det : Matrix ρ ι (ZMod 2)) (Triv : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  sInf {w : ℕ | ∃ f : ι → ZMod 2, IsUndetectedLogicalFault Det Triv f ∧ hammingNorm f = w}

/-- **A value given by `IsLeast` is the fault distance**: once the weight set of the
predicate is proved to be `IsLeast` at a value, the distance automatically equals that
value. The special-case theorem of §4 takes this route. -/
theorem faultDistance_eq_of_isLeast {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (Det : Matrix ρ ι (ZMod 2)) (Triv : Submodule (ZMod 2) (ι → ZMod 2)) {d : ℕ}
    (h : IsLeast {w : ℕ | ∃ f : ι → ZMod 2, IsUndetectedLogicalFault Det Triv f ∧
      hammingNorm f = w} d) :
    faultDistance Det Triv = d := by
  unfold faultDistance
  exact IsLeast.csInf_eq h

/-- **An equivalent description of the distance**: writing the weight set as an image set
(`hammingNorm '' ·`) gives the same `sInf`. The static-side bridge (§3) takes this form,
because the upstream definition is built on the "image set of weights". -/
theorem sInf_hammingNorm_image {ι : Type*} [Fintype ι] (S : Set (ι → ZMod 2)) :
    sInf (hammingNorm '' S) = sInf {w : ℕ | ∃ f ∈ S, hammingNorm f = w} :=
  rfl

/-- **Readout-functional form ⟺ subspace form** (the case `Triv = M.rowSpace`).

The library's `GF2/Witness.lean` has already proved "$f$ is not in the row space $\iff$
there is a dual witness that commutes with every check yet pairs with $f$ to $1$";
this theorem translates that into the phrasing "a readout functional that reads $1$":
**"flips the logical readout" and "$f \notin \mathrm{rowSpace}\,M$" are two ways of
writing one thing**. -/
theorem flipsReadout_readoutsOf_iff {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (f : Vec n) :
    FlipsReadout (readoutsOf M.rowSpace) f ↔ f ∉ M.rowSpace := by
  constructor
  · rintro ⟨r, hr, hrf⟩ hf
    exact absurd (hr f hf) (by rw [hrf]; exact one_ne_zero)
  · intro hf
    obtain ⟨w, -⟩ := (exists_dualWitness_iff M f).mpr hf
    exact ⟨w.w, fun u hu => ker_dotProduct_rowSpace_eq_zero M w.w u w.mem_ker hu, w.pairing⟩

/-- The two forms of the general predicate agree when `R = readoutsOf Triv` and `Triv` is
a row space. -/
theorem isUndetectedLogicalFaultR_iff_rowSpace {n : ℕ} {ρ : Type*}
    (Det : Matrix ρ (Fin n) (ZMod 2)) {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (f : Vec n) :
    IsUndetectedLogicalFaultR Det (readoutsOf M.rowSpace) f ↔
      IsUndetectedLogicalFault Det M.rowSpace f :=
  and_congr_right fun _ => flipsReadout_readoutsOf_iff M f

/-! ## 3. Special case A: the static code distance (time axis degenerated to one slice) -/

section Static

variable {n m₁ m₂ : ℕ}

/-- **The static predicate is exactly the set the existing static distance takes**: with
`Det = M₁` (the check matrix, i.e. the kernel side) and `Triv = M₂.rowSpace` (operators
"that are combinations of the rows of $M_2$" count as trivial), the general predicate
becomes **verbatim** $E \in \ker M_1 \wedge E \notin \mathrm{rowSpace}\,M_2$.

(It is a definitional equality, so the proof is `Iff.rfl` -- the most direct evidence that
"the two special cases share one shape".) -/
theorem isUndetectedLogicalFault_static (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) (E : Vec n) :
    IsUndetectedLogicalFault M₁ M₂.rowSpace E ↔
      (E ∈ LinearMap.ker M₁.toLin' ∧ E ∉ M₂.rowSpace) :=
  Iff.rfl

/-- **The upstream definition (nonempty case) = the `sInf` of the weight image set**.

`min_weight_ker_not_mem_rowspace` is built on
`Finset.min (Finset.image hammingNorm s.toFinset)` (with `s = ker M₁ \ rowSpace M₂`,
returning `n + 1` when `s` is empty); this theorem says that when `s` is **nonempty** it
is `sInf (hammingNorm '' s)` -- the number this module's `faultDistance` uses. (The
nonemptiness hypothesis cannot be dropped: on the empty set the two sides are `n + 1` and
`0`; see honest boundary 3 in the module header.) -/
theorem sInf_image_undetectableSet_eq_minWeight (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) (hne : (undetectableSet M₁ M₂).Nonempty) :
    min_weight_ker_not_mem_rowspace M₁ M₂ = sInf (hammingNorm '' undetectableSet M₁ M₂) := by
  have hneImg : (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset).Nonempty := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨hammingNorm f, Finset.mem_image.mpr ⟨f, by rwa [Set.mem_toFinset], rfl⟩⟩
  have hnotTop :
      Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) ≠ ⊤ := by
    intro h
    rw [Finset.min_eq_top.mp h] at hneImg
    exact Finset.not_nonempty_empty hneImg
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hnotTop
  -- `ha : ↑a = min`
  have hmem : a ∈ hammingNorm '' undetectableSet M₁ M₂ := by
    have h1 := Finset.mem_of_min ha.symm
    rw [Finset.mem_image] at h1
    obtain ⟨f, hf, hfw⟩ := h1
    exact ⟨f, by rwa [Set.mem_toFinset] at hf, hfw⟩
  have hlower : a ≤ sInf (hammingNorm '' undetectableSet M₁ M₂) := by
    refine le_csInf ⟨a, hmem⟩ ?_
    rintro b ⟨f, hf, rfl⟩
    have h2 : hammingNorm f ∈ Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset :=
      Finset.mem_image.mpr ⟨f, by rwa [Set.mem_toFinset], rfl⟩
    have h3 := Finset.min_le h2
    rw [← ha] at h3
    exact WithTop.coe_le_coe.mp h3
  have hupper : sInf (hammingNorm '' undetectableSet M₁ M₂) ≤ a :=
    csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hmem
  have hval : min_weight_ker_not_mem_rowspace M₁ M₂ = a := by
    unfold min_weight_ker_not_mem_rowspace
    change (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
      | none => n + 1
      | some b => b) = a
    rw [← ha]
  rw [hval]
  exact le_antisymm hlower hupper

/-- **The static-side special case**: when the time axis degenerates to a single time
slice, the general fault distance **is** the static code distance.

This is the module's first special-case theorem: on `Fin n` indices the general predicate
(detector = the rows of `M₁`, trivial faults = the row space of `M₂`) gives the same
number as `min_weight_ker_not_mem_rowspace`. -/
theorem faultDistance_static (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) (hne : (undetectableSet M₁ M₂).Nonempty) :
    faultDistance M₁ M₂.rowSpace = min_weight_ker_not_mem_rowspace M₁ M₂ := by
  have hset : {w : ℕ | ∃ f : Vec n, IsUndetectedLogicalFault M₁ M₂.rowSpace f ∧
        hammingNorm f = w} = {w : ℕ | ∃ f ∈ undetectableSet M₁ M₂, hammingNorm f = w} := by
    ext w
    constructor
    · rintro ⟨f, hf, hw⟩
      exact ⟨f, ⟨hf.1, hf.2⟩, hw⟩
    · rintro ⟨f, hf, hw⟩
      exact ⟨f, ⟨hf.1, hf.2⟩, hw⟩
  unfold faultDistance
  rw [hset, ← sInf_hammingNorm_image]
  exact (sInf_image_undetectableSet_eq_minWeight M₁ M₂ hne).symm

/-- **The empty-set case: the two definitions part ways here** (the **machine form** of
honest boundary 3).

When `ker M₁ \ rowSpace M₂` is empty (the kernel lies entirely in the row space; there is
no undetectable nontrivial operator):

* the upstream `min_weight_ker_not_mem_rowspace` gives `n + 1` -- the `⊤` branch of
  `Finset.min`, a sentinel value "heavier than any operator";
* this module's `faultDistance` gives `0` -- the infimum of the empty set in `ℕ`.

So the special-case theorem of §3 **must** carry the nonemptiness hypothesis: this is not
a technical hypothesis but exactly the point on which the two definitions are not
intertranslatable in the degenerate case. This theorem writes it as a checkable
conjunction rather than as a sentence of prose. -/
theorem static_empty_divergence (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) (hemp : (undetectableSet M₁ M₂) = ∅) :
    min_weight_ker_not_mem_rowspace M₁ M₂ = n + 1
      ∧ faultDistance M₁ M₂.rowSpace = 0 := by
  have himg : Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset = ∅ := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨f, hf, -⟩ := hx
      rw [Set.mem_toFinset] at hf
      rw [hemp] at hf
      exact absurd hf (Set.notMem_empty f)
    · intro hx
      exact absurd hx (Finset.notMem_empty x)
  have hset : {w : ℕ | ∃ f : Vec n, IsUndetectedLogicalFault M₁ M₂.rowSpace f ∧
      hammingNorm f = w} = ∅ := by
    ext w
    constructor
    · rintro ⟨f, hf, -⟩
      have hmem : f ∈ undetectableSet M₁ M₂ := ⟨hf.1, hf.2⟩
      rw [hemp] at hmem
      exact hmem
    · intro hw
      exact absurd hw (Set.notMem_empty w)
  refine ⟨?_, ?_⟩
  · unfold min_weight_ker_not_mem_rowspace
    change (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
      | none => n + 1
      | some b => b) = n + 1
    split
    · rfl
    · rename_i b hb
      rw [himg] at hb
      exact absurd hb (by simp)
  · unfold faultDistance
    rw [hset]
    exact Nat.sInf_empty

end Static

/-! ## 4. Special case B: the timelike component (one check across $T = S + 1$ rounds) -/

section TimeLike

/-- The matrix form of the timelike adjacent-round check matrix: `Codes/Gauging.lean`'s
`repCheck` (its `i`-th row is `e_i + e_{i+1}`). -/
def repCheckMat (S : ℕ) : Matrix (Fin S) (Fin (S + 1)) (ZMod 2) :=
  fun i => repCheck S i

/-- **The timelike detector**: the comparison of the same law (Gauss law label `Fin k`)
between two adjacent rounds.

Row index `Fin k × Fin S` = "which law, which adjacent round pair"; column index
`Fin k × Fin (S + 1)` -- **exactly** the index type of `Homology/HypergraphSurgery.lean`'s
`TimeFault k S`, i.e. the spacetime position "which law, which round". So
`timeLikeDetector` is a "detector -- fault location" matrix that can be fed directly to
`faultDistance`.

It is `1 ⊗ repCheckMat S`: laws do not mix with one another (diagonal), and along the time
axis adjacent rounds are taken. -/
def timeLikeDetector (k S : ℕ) : Matrix (Fin k × Fin S) (Fin k × Fin (S + 1)) (ZMod 2) :=
  Matrix.kronecker (1 : Matrix (Fin k) (Fin k) (ZMod 2)) (repCheckMat S)

/-- **A row-by-row description of kernel membership** (general row index): `f` lies in the
kernel of `Det` ⟺ every row pairs with `f` to zero.

Upstream LeanQEC's `mem_ker_iff_dotProd_rows_eq_zero` is the special case of a `Fin` row
index; this module needs product row indices (`Fin k × Fin S`), so it is restated here.

**The `_rows` in the name is necessary**: `Codes/ToricFamilySpatial` already has a
`mem_ker_toLin'_iff` (stated as `x ∈ ker M.toLin' ↔ M *ᵥ x = 0`, matrix-vector form),
which is a **different statement** from this one; the same name would make the import fail
outright ("environment already contains"), so the two each take their own name. -/
theorem mem_ker_toLin'_iff_rows {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ρ ι (ZMod 2)) (f : ι → ZMod 2) :
    f ∈ LinearMap.ker M.toLin' ↔ ∀ r : ρ, M r ⬝ᵥ f = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h r
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_apply, Matrix.row_apply, dotProduct,
      Pi.zero_apply] using congrFun h r
  · intro h
    funext r
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_apply, Matrix.row_apply, dotProduct,
      Pi.zero_apply] using h r

/-- **One row of the timelike detector**: pairing the `(v, i)`-th row with a fault is the
sum of the two reports of the `v`-th law at rounds `i` and `i+1`. -/
theorem timeLikeDetector_row_dot (k S : ℕ) (r : Fin k × Fin S) (f : TimeFault k S) :
    (timeLikeDetector k S) r ⬝ᵥ f
      = repCheck S r.2 ⬝ᵥ (fun t : Fin (S + 1) => f (r.1, t)) := by
  simp only [timeLikeDetector, Matrix.kronecker, Matrix.kroneckerMap_apply, dotProduct,
    Matrix.one_apply, repCheckMat, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single r.1]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [ite_eq_left rfl, one_mul]
  · intro c1 _ hc1
    have hne : ¬ (r.1 = c1) := fun h => hc1 h.symm
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ r.1) h

/-- **The timelike detector is all silent ⟺ every law reads the same at adjacent rounds**
(reduces to `protocolTimeCheck`). -/
theorem isDetectorSilent_timeLike (k S : ℕ) (f : TimeFault k S) :
    IsDetectorSilent (timeLikeDetector k S) f
      ↔ ∀ (v : Fin k) (i : Fin S), f (v, Fin.castSucc i) + f (v, i.succ) = 0 := by
  rw [IsDetectorSilent, mem_ker_toLin'_iff_rows]
  constructor
  · intro h v i
    have h1 := h (v, i)
    rw [timeLikeDetector_row_dot, repCheck, add_dotProduct, unitVec_dot, unitVec_dot] at h1
    exact h1
  · intro h r
    rw [timeLikeDetector_row_dot, repCheck, add_dotProduct, unitVec_dot, unitVec_dot]
    exact h r.1 r.2

/-- `IsTimeLikeFault` is the per-law adjacent-round condition (definitional unfolding). -/
theorem isTimeLikeFault_iff {k m S : ℕ} (H : AuxHypergraph k m) (f : TimeFault k S) :
    IsTimeLikeFault H S f
      ↔ ∀ (v : Fin k) (i : Fin S), f (v, Fin.castSucc i) + f (v, i.succ) = 0 :=
  Iff.rfl

/-- **The timelike-side predicate is exactly the set `protocolTime_minWeight` takes**:
with `Det = timeLikeDetector k S` and `Triv = ⊥` (on the timelike chain there is no
notion of "boundary"), the general predicate becomes "nonzero ∧ orthogonal to every
timelike check".

The second conjunct `f ∉ (⊥ : Submodule …)` simplifies to `f ≠ 0` -- exactly the
convention already in the library, "nonzero means logical when there are no in-round
checks" (`bare_noLightFault`). -/
theorem isUndetectedLogicalFault_timeLike {k m S : ℕ} (H : AuxHypergraph k m)
    {f : TimeFault k S} :
    IsUndetectedLogicalFault (timeLikeDetector k S) (⊥ : Submodule (ZMod 2) (TimeFault k S)) f
      ↔ f ≠ 0 ∧ IsTimeLikeFault H S f := by
  have hbot : f ∉ (⊥ : Submodule (ZMod 2) (TimeFault k S)) ↔ f ≠ 0 := by
    simp
  rw [IsUndetectedLogicalFault, hbot, isTimeLikeFault_iff, isDetectorSilent_timeLike]
  exact and_comm

/-- **The timelike-side special case**: with one check across `S + 1` rounds, the general
fault distance **is** the number `S + 1` that `protocolTime_minWeight` gives.

This is the module's second special-case theorem: the minimum weight the general predicate
takes on the spacetime index "(law, round)" is the same number as the timelike-component
conclusion of `Homology/HypergraphSurgery.lean` -- **the proof only translates the set and
then calls the existing theorem**, so the two definitions really do coincide on this
instance. -/
theorem faultDistance_timeLike {k m : ℕ} (H : AuxHypergraph k m) (v₀ : Fin k) (S : ℕ) :
    faultDistance (timeLikeDetector k S) (⊥ : Submodule (ZMod 2) (TimeFault k S)) = S + 1 := by
  have hset : {w : ℕ | ∃ f : TimeFault k S,
        IsUndetectedLogicalFault (timeLikeDetector k S)
          (⊥ : Submodule (ZMod 2) (TimeFault k S)) f ∧ hammingNorm f = w}
      = {w : ℕ | ∃ x : TimeFault k S, x ≠ 0 ∧ IsTimeLikeFault H S x ∧ hammingNorm x = w} := by
    ext w
    constructor
    · rintro ⟨f, hf, hw⟩
      obtain ⟨hne, hfault⟩ := (isUndetectedLogicalFault_timeLike H).mp hf
      exact ⟨f, hne, hfault, hw⟩
    · rintro ⟨x, hx, hfault, hw⟩
      exact ⟨x, (isUndetectedLogicalFault_timeLike H).mpr ⟨hx, hfault⟩, hw⟩
  unfold faultDistance
  rw [hset]
  exact IsLeast.csInf_eq (protocolTime_minWeight H v₀ S)

/-- `repCheckMat 3` **is** the timelike-side differential `timeLikeRepR` of
`Homology/FaultComplex.lean` (the check matrix of the $l = 4$ round repetition code, "the
full-rank parity-check matrix for the repetition code" of [14] p.63).

Thus the timelike detector of §4 **is** the off-diagonal block of fault complex instance A
(timelike) -- it is the value on the **time axis** of that column of "blocks expanded
around the Koszul formula". -/
theorem repCheckMat_three_eq_timeLikeRepR : repCheckMat 3 = timeLikeRepR := by
  decide

/-- **The timelike detector of §4 = the off-diagonal block of the timelike fault complex**
(the instance $k = 3$, $4$ rounds): `Homology/FaultComplex.lean`'s
`timeLikeFaultComplex_d11_01` says the block is $1 \otimes$ `timeLikeRepR`, and the
previous item says `timeLikeRepR` is `repCheckMat 3`.

This is the **concrete point of contact** between the predicate of §4 and the fault
complex: the block of that instance is this module's detector. -/
theorem timeLikeDetector_three_eq_faultComplex_d11_01 :
    timeLikeDetector 3 3 = timeLikeFaultComplex.d11_01 := by
  rw [timeLikeDetector, timeLikeFaultComplex_d11_01, repCheckMat_three_eq_timeLikeRepR]

/-- **A concrete reading**: on the instance with $k = 3$ laws and $4$ rounds, the general
fault distance is $= 4$ ($=$ the number of rounds) -- the same number as `timeLike34_d` of
`Codes/TimeLikeInstance.lean`, but this time computed on **this module's general
predicate**.

(The auxiliary hypergraph enters the definition here but not the conclusion:
`IsTimeLikeFault` uses `protocolTimeCheck`, which does not look at `H.edge`; see
`timeComponent_aux_independent` of `Homology/HypergraphSurgery.lean`.) -/
theorem faultDistance_timeLike_four :
    faultDistance (timeLikeDetector 3 3) (⊥ : Submodule (ZMod 2) (TimeFault 3 3)) = 4 := by
  simpa using faultDistance_timeLike
    (graphOf fun _ : Fin 1 => ((0 : Fin 3), (1 : Fin 3))) (0 : Fin 3) 3

end TimeLike

/-! ## 5. The general predicate placed on the fault complex

§3 and §4 connected the general predicate to two existing distance objects. This section
places it **on `FaultComplex`**: the terms $F_1$ / $F_2$ of the fault complex are the fault
locations, and the differentials give the detectors and the "trivial faults".

Under the correspondence of [14] p.63:

* $H_1(F)$ = logical $\overline Z$ faults ($Z$ Pauli errors + $X$ check errors)
  $\Longrightarrow$ faults in $F_1 = F_{1,0} \oplus F_{0,1}$, detector
  $\partial_0 : F_1 \to F_0$, trivial = the image of $\partial_1$;
* $H^2(F)$ = logical $\overline X$ faults ($X$ Pauli errors + $Z$ check errors)
  $\Longrightarrow$ faults in $F_2 = F_{1,1} \oplus F_{0,2}$, detector
  $\partial_1 : F_2 \to F_1$, trivial = the image of $\partial_2$.

The **count** of the two types -- which cohomology dimension of the code complex gives each
of them, on the two routine foliations used on p.63 -- is in
`Codes/FaultComplexKunneth` §4.21. -/

section Complex

variable {F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂ : Type*}
variable [Fintype F₀₀] [Fintype F₀₁] [Fintype F₀₂]
variable [Fintype F₁₀] [Fintype F₁₁] [Fintype F₁₂]
variable [DecidableEq F₀₀] [DecidableEq F₀₁] [DecidableEq F₀₂]
variable [DecidableEq F₁₀] [DecidableEq F₁₁] [DecidableEq F₁₂]

omit [DecidableEq F₀₀] [DecidableEq F₁₂] in
/-- **The image of $\partial_1$ lies in the kernel of $\partial_0$**: the direct reading
of the complex condition $\partial_0\partial_1 = 0$.

Its meaning is that **every trivial fault is undetectable**: so "quotienting out the
trivial faults" only quotients out homology classes and quotients out nothing
"detectable" -- exactly why the two distance definitions of §5 make sense. -/
theorem range_fd1_le_ker_fd0 (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) :
    LinearMap.range (fd1 F.d11_10 F.d11_01 F.d02_01).toLin'
      ≤ LinearMap.ker (fd0 F.d10_00 F.d01_00).toLin' := by
  rintro x ⟨y, rfl⟩
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
    F.comp_d0_d1, Matrix.zero_mulVec]

/-- **The Z-side distance of the fault complex** (the minimum weight on $H_1(F)$ of [14]
p.63): the faults are elements of $F_1$, the detector is $\partial_0 : F_1 \to F_0$, and
the trivial faults are the image of $\partial_1$.

It corresponds to the timelike-side special case of §4: the index type of $F_1$ is a
spacetime position type like "(location, round)". -/
noncomputable def faultComplexDistanceZ (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) : ℕ :=
  faultDistance (fd0 F.d10_00 F.d01_00)
    (LinearMap.range (fd1 F.d11_10 F.d11_01 F.d02_01).toLin')

/-- **The X-side distance of the fault complex** (the minimum weight on $H^2(F)$ of [14]
p.63): the faults are elements of $F_2$, the detector is $\partial_1 : F_2 \to F_1$, and
the trivial faults are the image of $\partial_2$. -/
noncomputable def faultComplexDistanceX (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) : ℕ :=
  faultDistance (fd1 F.d11_10 F.d11_01 F.d02_01)
    (LinearMap.range (fd2 F.d12_11 F.d12_02).toLin')

omit [DecidableEq F₀₀] [DecidableEq F₁₂] in
/-- **The definitional unfolding of the Z-side distance**: it spreads out as the minimum
weight over "$\partial_0$ silent ∧ not in the image of $\partial_1$" -- the two special
cases of §3 and §4 are this shape's values on two concrete models. -/
theorem faultComplexDistanceZ_eq_sInf (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) :
    faultComplexDistanceZ F
      = sInf {w : ℕ | ∃ f : FaultTerm1 F₁₀ F₀₁ → ZMod 2,
          IsUndetectedLogicalFault (fd0 F.d10_00 F.d01_00)
            (LinearMap.range (fd1 F.d11_10 F.d11_01 F.d02_01).toLin') f ∧
          hammingNorm f = w} :=
  rfl

omit [DecidableEq F₀₀] [DecidableEq F₀₁] [DecidableEq F₁₀] in
/-- **The definitional unfolding of the X-side distance** (the symmetric one). -/
theorem faultComplexDistanceX_eq_sInf (F : FaultComplex F₀₀ F₀₁ F₀₂ F₁₀ F₁₁ F₁₂) :
    faultComplexDistanceX F
      = sInf {w : ℕ | ∃ f : FaultTerm2 F₁₁ F₀₂ → ZMod 2,
          IsUndetectedLogicalFault (fd1 F.d11_10 F.d11_01 F.d02_01)
            (LinearMap.range (fd2 F.d12_11 F.d12_02).toLin') f ∧
          hammingNorm f = w} :=
  rfl

end Complex

/-! ## 6. The transport layer: `ker` and `range` under relabelling / Kronecker

Once §5 has placed the general predicate on the fault complex, "`faultComplexDistanceZ`
equals the static code distance" is still **one step of index transport** away (module
header, honest boundary 2): the fault index of the complex is a product / sum type like
$F_1 = \mathrm{Fin}\,m \times \mathrm{Fin}\,0 \oplus \mathrm{Fin}\,k \times
\mathrm{Fin}\,S$, while the index of `min_weight_ker_not_mem_rowspace` is
$\mathrm{Fin}\,k$.

This section supplies that layer as **general lemmas**, grouped by use:

* **Relabelling** (`hammingNorm_comp_equiv`): Hamming weight is unchanged when indices are
  in bijection -- the master statement for all later transport. The two lemmas after it are
  the same thing in the two concrete index forms this section needs:
  `hammingNorm_sum_inr` (sum type: the empty half contributes no weight) and
  `hammingNorm_sliceEmbed` / `hammingNorm_slice_le` (putting $\mathrm{Fin}\,k$ into the
  $t_0$-th slice of a product index, and conversely taking a slice along one).
* **Row space ↔ image of the transpose** (`mem_rowSpace_iff_exists_transpose_mulVec`): the
  one reordering needed to replace "the image of $\partial_1$" by "$H_Z$'s row space"; it
  is the **membership form** of `Homology/SubcodeLayer.lean`'s
  `range_toLin'_eq_transpose_rowSpace` (reused rather than rebuilt).
* **Slice readings of Kronecker and block matrices**: `kronecker_one_dot` /
  `kronecker_one_mulVec_apply` (one row / one component of $(A \otimes 1_S)$ reads only
  **that one time slice**), `fd0_row_dot` / `fd1_row_dot` (the row dot products of `fd0` /
  `fd1` expand by the two blocks; since the two blocks have different types, the expansion
  is directly "the two rows of the matrix"). -/

section Transport

/-- `M.row i` is just `M i` (`Matrix.row` merely takes a row as a function). Use:
`Matrix.mulVec_apply` writes `M *ᵥ x` as `M.row i ⬝ᵥ x`, while the lemmas are stated on
`M i`. -/
theorem Matrix_row_eq_apply {m n : Type*} (M : Matrix m n (ZMod 2)) (i : m) :
    M.row i = M i := rfl

/-- The dot product over an empty index is zero. -/
theorem dotProduct_eq_zero_of_isEmpty {α : Type*} [Fintype α] [IsEmpty α]
    (M v : α → ZMod 2) : M ⬝ᵥ v = 0 := by
  unfold dotProduct
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- A `∀` simplification of addition over an empty index (right half of a sum type empty). -/
theorem forall_sum_inl_iff {α β : Type*} [IsEmpty β] (P : α ⊕ β → Prop) :
    (∀ x, P x) ↔ ∀ a : α, P (Sum.inl a) :=
  ⟨fun h a => h (Sum.inl a), fun h x => by
    rcases x with a | b
    · exact h a
    · exact (IsEmpty.false b).elim⟩

/-- **Hamming weight under relabelling**: the weight is unchanged when indices are in bijection. -/
theorem hammingNorm_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (f : ι → ZMod 2) :
    hammingNorm (f ∘ e) = hammingNorm f := by
  classical
  have h1 : hammingNorm (f ∘ e) = (Finset.univ.filter fun i => f (e i) ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm f = (Finset.univ.filter fun j => f j ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, h2]
  have hmap : (Finset.univ.filter fun i => f (e i) ≠ 0).map e.toEmbedding
      = Finset.univ.filter fun j => f j ≠ 0 := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hj
      exact ⟨e.symm j, by simpa using hj, by simp⟩
  rw [← hmap, Finset.card_map]

/-- **Zero-sum decomposition**: when `α` is empty the weight on `α ⊕ β` is the weight on
the `β` half.

Use: the fault index of the degenerate complex is $(F_{1,0} \oplus F_{0,1})$, and
$F_{1,0} = \varnothing$ (no differential along the time direction ⟹ no $X$ check fault
location), so the weight lives only on the $F_{0,1}$ half. -/
theorem hammingNorm_sum_inr {α β : Type*} [Fintype α] [Fintype β] [IsEmpty α]
    (f : α ⊕ β → ZMod 2) :
    hammingNorm f = hammingNorm (fun b : β => f (Sum.inr b)) := by
  classical
  have h1 : hammingNorm f = (Finset.univ.filter fun x : α ⊕ β => f x ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm (fun b : β => f (Sum.inr b))
      = (Finset.univ.filter fun b : β => f (Sum.inr b) ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, h2]
  refine Finset.card_nbij'
    (fun x : α ⊕ β => Sum.elim (fun a => (IsEmpty.false a).elim) (fun b => b) x)
    (fun b : β => Sum.inr b) ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with a | b
    · exact (IsEmpty.false a).elim
    · simpa using hx
  · intro b hb
    simpa using hb
  · intro x hx
    rcases x with a | b
    · exact (IsEmpty.false a).elim
    · rfl
  · intro b _
    rfl

/-- **A single-time-slice embedding preserves weight**: putting `Vec k` into the `t₀`-th
slice of the product index `Fin k × Fin S` leaves the Hamming weight unchanged -- the
concrete form of "relabelling" on time slices ($\mathrm{Fin}\,k$ is in bijection with the
$t_0$-th slice of that product index). -/
theorem hammingNorm_sliceEmbed {k S : ℕ} (t₀ : Fin S) (E : Vec k) :
    hammingNorm (fun q : Fin k × Fin S => if q.2 = t₀ then E q.1 else 0) = hammingNorm E := by
  classical
  have h1 : hammingNorm (fun q : Fin k × Fin S => if q.2 = t₀ then E q.1 else 0)
      = (Finset.univ.filter fun q : Fin k × Fin S =>
          (if q.2 = t₀ then E q.1 else 0) ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm E = (Finset.univ.filter fun b : Fin k => E b ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, h2]
  refine (Finset.card_nbij' (fun b : Fin k => (b, t₀)) (fun q : Fin k × Fin S => q.1)
    ?_ ?_ ?_ ?_).symm
  · intro b hb
    simpa using hb
  · intro q hq
    have hq' : (if q.2 = t₀ then E q.1 else 0) ≠ 0 := by simpa using hq
    have hE : E q.1 ≠ 0 := by
      by_cases h : q.2 = t₀
      · simpa [ite_eq_left h] using hq'
      · rw [ite_eq_right h] at hq'
        exact absurd rfl hq'
    simpa using hE
  · intro b _
    rfl
  · intro q hq
    have hq' : (if q.2 = t₀ then E q.1 else 0) ≠ 0 := by simpa using hq
    have h : q.2 = t₀ := by
      by_cases h : q.2 = t₀
      · exact h
      · rw [ite_eq_right h] at hq'
        exact absurd rfl hq'
    exact Prod.ext rfl h.symm

/-- **Slice contraction**: taking a slice along one time slice never increases the weight
(together with the previous item, "a slicewise condition" and "the static condition" give
the same number as a minimum weight). -/
theorem hammingNorm_slice_le {k S : ℕ} (g : Fin k × Fin S → ZMod 2) (t : Fin S) :
    hammingNorm (fun b : Fin k => g (b, t)) ≤ hammingNorm g := by
  classical
  have h1 : hammingNorm (fun b : Fin k => g (b, t))
      = (Finset.univ.filter fun b : Fin k => g (b, t) ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm g = (Finset.univ.filter fun q : Fin k × Fin S => g q ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, h2]
  refine Finset.card_le_card_of_injOn (fun b : Fin k => (b, t)) ?_ ?_
  · intro b hb
    simpa using hb
  · intro b₁ _ b₂ _ h
    simpa using h

/-- **The transpose row-space bridge (elementwise form)**: `y ∈ M.rowSpace` if and only if
`y` is the image of `Mᵀ` at some `z`. This is the membership form of
`Homology/SubcodeLayer.lean`'s `range_toLin'_eq_transpose_rowSpace`
(`LinearMap.range M.toLin' = M.rowSpace`) -- replacing "the image of $\partial_1$" by
"$H_Z$'s row space" and the row index by the column index (`z : Vec m` being the
"coefficients of the row combination") aligns it with `min_weight_ker_not_mem_rowspace`. -/
theorem mem_rowSpace_iff_exists_transpose_mulVec {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) (y : Vec n) :
    y ∈ M.rowSpace ↔ ∃ z : Vec m, M.transpose *ᵥ z = y := by
  have h := range_toLin'_eq_transpose_rowSpace M.transpose
  rw [Matrix.transpose_transpose] at h
  rw [← h, LinearMap.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rwa [Matrix.toLin'_apply] at hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rwa [Matrix.toLin'_apply]⟩

/-- The half of `∂₀`'s rows coming from $F_{0,0}$: the readout is the sum of the two
blocks $F_{1,0}$ and $F_{0,1}$. (The two blocks have different row indices, so they cannot
be merged into one dot product; in the degenerate case the first block's index is empty and
`dotProduct_eq_zero_of_isEmpty` sends it straight to zero.) -/
theorem fd0_row_dot {ρ ι₁ ι₂ : Type*} [Fintype ρ] [Fintype ι₁] [Fintype ι₂]
    (d10_00 : Matrix ρ ι₁ (ZMod 2)) (d01_00 : Matrix ρ ι₂ (ZMod 2))
    (f : ι₁ ⊕ ι₂ → ZMod 2) (c : ρ) :
    fd0 d10_00 d01_00 (Sum.inl c) ⬝ᵥ f
      = d10_00 c ⬝ᵥ (fun a => f (Sum.inl a)) + d01_00 c ⬝ᵥ (fun b => f (Sum.inr b)) := by
  simp only [fd0, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂]

/-- The half of `∂₁`'s rows coming from $F_{0,1}$: the readout is the sum of the two
blocks $F_{1,1}$ and $F_{0,2}$. -/
theorem fd1_row_dot {ρ₁ ρ₂ ι₁ ι₂ : Type*} [Fintype ρ₁] [Fintype ρ₂] [Fintype ι₁] [Fintype ι₂]
    (d11_10 : Matrix ρ₁ ι₁ (ZMod 2)) (d11_01 : Matrix ρ₂ ι₁ (ZMod 2))
    (d02_01 : Matrix ρ₂ ι₂ (ZMod 2)) (x : ι₁ ⊕ ι₂ → ZMod 2) (c : ρ₂) :
    fd1 d11_10 d11_01 d02_01 (Sum.inr c) ⬝ᵥ x
      = d11_01 c ⬝ᵥ (fun a => x (Sum.inl a)) + d02_01 c ⬝ᵥ (fun b => x (Sum.inr b)) := by
  simp only [fd1, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]

/-- **Row dot product of Kronecker × a single slice**: row `(c,i)` of `(A ⊗ 1_S)` reads
only the `i`-th slice of `v`, and the readout is the pairing of `A c` with that slice --
the step by which "$\partial_0$ is the Kronecker form of $H_X$" can be translated into "a
slicewise kernel condition". -/
theorem kronecker_one_dot {m k S : ℕ} (A : Matrix (Fin m) (Fin k) (ZMod 2))
    (v : Fin k × Fin S → ZMod 2) (c : Fin m) (i : Fin S) :
    (Matrix.kronecker A (1 : Matrix (Fin S) (Fin S) (ZMod 2))) (c, i) ⬝ᵥ v
      = A c ⬝ᵥ (fun b : Fin k => v (b, i)) := by
  simp only [dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, mul_one]
  · intro j _ hj
    rw [ite_eq_right (fun h : i = j => hj h.symm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Matrix-vector action of Kronecker × a single slice**: the `(y,j)`-th component of
`(A ⊗ 1_S) *ᵥ x` is determined only by the `j`-th slice of `x` (the column form of the
previous item). -/
theorem kronecker_one_mulVec_apply {m k S : ℕ} (A : Matrix (Fin m) (Fin k) (ZMod 2))
    (x : Fin k × Fin S → ZMod 2) (y : Fin m) (j : Fin S) :
    ((Matrix.kronecker A (1 : Matrix (Fin S) (Fin S) (ZMod 2))) *ᵥ x) (y, j)
      = (A *ᵥ (fun b : Fin k => x (b, j))) y := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  exact kronecker_one_dot A x y j

end Transport

/-! ## 7. The degenerate fault complex

$\partial_0$ is the Kronecker form of $H_X$, and the image of $\partial_1$ is $H_Z$'s row
space. Take $(R \otimes C)_\bullet$ with **no coupling along the time direction**: $R_0 =
\mathrm{Fin}\ S$ (keeping $S$ time slices) and $R_1 = \varnothing$ (no differential along
the time direction, so $\partial_{\mathcal R} = 0$); on the code side take the CSS complex
$\partial_1 = H_X$, $\partial_2 = H_Z^{\mathsf T}$. Then
$F_{1,0} = F_{1,1} = F_{1,2} = \varnothing$, and the faults reduce to the "data-qubit
fault" half. Thus:

* the detector block of $\partial_0$ is $H_X \otimes 1_S$
  (`degenerateFaultComplex_d01_00`);
* the trivial block of $\partial_1$ is $H_Z^{\mathsf T} \otimes 1_S$
  (`degenerateFaultComplex_d02_01`), whose image is $H_Z$'s row space taken **time slice
  by time slice** (`degenerate_fd1_mem_range`).

This section translates $\ker\partial_0$ and $\mathrm{im}\,\partial_1$ into conditions on
$\mathrm{Fin}\,k$ (`degenerate_fd0_mem_ker`, `degenerate_fd1_mem_range`), then squeezes the
$\mathrm{sInf}$ of the two weight sets to the same number
(`faultComplexDistanceZ_degenerate`). -/

/-- **The degenerate fault complex (no coupling along the time direction)**: see the note
at the start of this section. -/
def degenerateFaultComplex (m k rz S : ℕ)
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) :
    FaultComplex (Fin m × Fin S) (Fin k × Fin S) (Fin rz × Fin S)
      (Fin m × Fin 0) (Fin k × Fin 0) (Fin rz × Fin 0) :=
  koszulFaultComplex (C₀ := Fin m) (C₁ := Fin k) (C₂ := Fin rz)
    (R₀ := Fin S) (R₁ := Fin 0) (0 : Matrix (Fin S) (Fin 0) (ZMod 2)) Hx Hz.transpose hC

/-- **The detector block is the Kronecker form of $H_X$**: the $F_{0,0} \to F_{0,1}$ block
is $= H_X \otimes 1_S$. -/
theorem degenerateFaultComplex_d01_00 (m k rz S : ℕ)
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) :
    (degenerateFaultComplex m k rz S Hx Hz hC).d01_00
      = Matrix.kronecker Hx (1 : Matrix (Fin S) (Fin S) (ZMod 2)) := rfl

/-- **The trivial-fault block is the Kronecker form of $H_Z^{\mathsf T}$**: the
$F_{0,2} \to F_{0,1}$ block is $= H_Z^{\mathsf T} \otimes 1_S$ -- its image is exactly
"$H_Z$'s row space (slicewise)". -/
theorem degenerateFaultComplex_d02_01 (m k rz S : ℕ)
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) :
    (degenerateFaultComplex m k rz S Hx Hz hC).d02_01
      = Matrix.kronecker Hz.transpose (1 : Matrix (Fin S) (Fin S) (ZMod 2)) := rfl

/-- **$F_{1,0}$ (the $X$ check faults) is empty in the degenerate case**: $R_1 =
\varnothing$ makes $F_{1,0} = F_{1,1} = F_{1,2} = \varnothing$, leaving only "data-qubit
faults" in the degenerate complex, so the fault vector is supported only on the $F_{0,1}$
half (which is where `hammingNorm_sum_inr` comes in). -/
theorem degenerateFaultComplex_d10_00 (m k rz S : ℕ)
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) :
    (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
      = Matrix.kronecker (1 : Matrix (Fin m) (Fin m) (ZMod 2))
          (0 : Matrix (Fin S) (Fin 0) (ZMod 2)) := rfl

/-- **A slice description of $\ker\partial_0$**: a fault is sent to zero by $\partial_0$ if
and only if on **every time slice** it is orthogonal to every check of $H_X$ -- the static
kernel condition slice by slice. -/
theorem degenerate_fd0_mem_ker {m k rz S : ℕ}
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0)
    (f : FaultTerm1 (Fin m × Fin 0) (Fin k × Fin S) → ZMod 2) :
    IsDetectorSilent (fd0 (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
        (degenerateFaultComplex m k rz S Hx Hz hC).d01_00) f
      ↔ ∀ (c : Fin m) (i : Fin S), Hx c ⬝ᵥ (fun b : Fin k => f (Sum.inr (b, i))) = 0 := by
  have hd10 : (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
      = Matrix.kronecker (1 : Matrix (Fin m) (Fin m) (ZMod 2))
          (0 : Matrix (Fin S) (Fin 0) (ZMod 2)) := rfl
  have hd01 : (degenerateFaultComplex m k rz S Hx Hz hC).d01_00
      = Matrix.kronecker Hx (1 : Matrix (Fin S) (Fin S) (ZMod 2)) := rfl
  unfold IsDetectorSilent
  rw [mem_ker_toLin'_iff_rows]
  rw [forall_sum_inl_iff (P := fun rr => fd0 (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
      (degenerateFaultComplex m k rz S Hx Hz hC).d01_00 rr ⬝ᵥ f = 0)]
  constructor
  · intro h c i
    have h1 := h (c, i)
    have hz : (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) (ZMod 2))
        (0 : Matrix (Fin S) (Fin 0) (ZMod 2))) (c, i) ⬝ᵥ
          (fun a : Fin m × Fin 0 => f (Sum.inl a)) = 0 :=
      dotProduct_eq_zero_of_isEmpty _ _
    rw [fd0_row_dot, hd10, hz, zero_add, hd01, kronecker_one_dot] at h1
    exact h1
  · intro h c
    rw [fd0_row_dot, hd10, hd01]
    have hz : (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) (ZMod 2))
        (0 : Matrix (Fin S) (Fin 0) (ZMod 2))) (c.1, c.2) ⬝ᵥ
          (fun a : Fin m × Fin 0 => f (Sum.inl a)) = 0 :=
      dotProduct_eq_zero_of_isEmpty _ _
    rw [hz, zero_add, kronecker_one_dot]
    exact h c.1 c.2

/-- **A slice description of $\mathrm{im}\,\partial_1$**: a fault is in the image of
$\partial_1$ if and only if on **every time slice** it is an element of $H_Z$'s row space
-- the static triviality condition slice by slice. -/
theorem degenerate_fd1_mem_range {m k rz S : ℕ}
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0)
    (f : FaultTerm1 (Fin m × Fin 0) (Fin k × Fin S) → ZMod 2) :
    f ∈ LinearMap.range (fd1 (degenerateFaultComplex m k rz S Hx Hz hC).d11_10
        (degenerateFaultComplex m k rz S Hx Hz hC).d11_01
        (degenerateFaultComplex m k rz S Hx Hz hC).d02_01).toLin'
      ↔ ∀ i : Fin S, (fun b : Fin k => f (Sum.inr (b, i))) ∈ Hz.rowSpace := by
  have hd11 : (degenerateFaultComplex m k rz S Hx Hz hC).d11_01
      = Matrix.kronecker (1 : Matrix (Fin k) (Fin k) (ZMod 2))
          (0 : Matrix (Fin S) (Fin 0) (ZMod 2)) := rfl
  have hd02 : (degenerateFaultComplex m k rz S Hx Hz hC).d02_01
      = Matrix.kronecker Hz.transpose (1 : Matrix (Fin S) (Fin S) (ZMod 2)) := rfl
  have hdot : ∀ (x : FaultTerm2 (Fin k × Fin 0) (Fin rz × Fin S) → ZMod 2)
      (b : Fin k) (i : Fin S),
      (fd1 (degenerateFaultComplex m k rz S Hx Hz hC).d11_10
          (degenerateFaultComplex m k rz S Hx Hz hC).d11_01
          (degenerateFaultComplex m k rz S Hx Hz hC).d02_01 *ᵥ x) (Sum.inr (b, i))
        = (Hz.transpose *ᵥ (fun c' : Fin rz => x (Sum.inr (c', i)))) b := by
    intro x b i
    rw [Matrix.mulVec_apply, Matrix_row_eq_apply, fd1_row_dot, hd11, hd02,
      dotProduct_eq_zero_of_isEmpty, zero_add, kronecker_one_dot]
    rw [Matrix.mulVec_apply, Matrix_row_eq_apply]
  constructor
  · intro hf i
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hf
    rw [Matrix.toLin'_apply] at hx
    refine (mem_rowSpace_iff_exists_transpose_mulVec Hz _).mpr
      ⟨fun c' => x (Sum.inr (c', i)), ?_⟩
    funext b
    rw [← hdot x b i]
    exact congrFun hx (Sum.inr (b, i))
  · intro h
    choose z hz using fun i => (mem_rowSpace_iff_exists_transpose_mulVec Hz _).mp (h i)
    refine LinearMap.mem_range.mpr ⟨fun w => w.elim
      (fun u : Fin k × Fin 0 => (IsEmpty.false u.2).elim)
      (fun q : Fin rz × Fin S => z q.2 q.1), ?_⟩
    rw [Matrix.toLin'_apply]
    funext w
    rcases w with u | q
    · exact (IsEmpty.false u.2).elim
    · obtain ⟨b, i⟩ := q
      rw [hdot _ b i]
      have hz' : (fun c' : Fin rz => (fun w => w.elim
          (fun u : Fin k × Fin 0 => (IsEmpty.false u.2).elim)
          (fun q : Fin rz × Fin S => z q.2 q.1)) (Sum.inr (c', i))) = z i := by
        funext c'
        rfl
      rw [hz']
      exact congrFun (hz i) b

/-! ### §7 (continued): Z-side distance of the degenerate complex = static code distance

First the constructions on both sides (the single-time-slice embedding `sliceFaultEmbed`
and its three transport lemmas), then the squeezing of the two weight sets' `sInf` to the
same number (`faultComplexDistanceZ_degenerate`). -/

/-- **Single-time-slice embedding**: put the static operator `E : Vec k` into the `t₀`-th
time slice of the degenerate complex and zero on the remaining slices ($F_{1,0}$ is the
empty half, so its values are arbitrary).

This is the direction "static operator ⟶ spacetime fault": `hammingNorm_sliceFaultEmbed`
below says it **preserves weight**, and `degenerate_sliceFaultEmbed_mem_ker` /
`_notMem_range` say it transports the static "in the kernel ∧ not in the row space" into
the complex's "$\partial_0$ silent ∧ not in the image of $\partial_1$". -/
def sliceFaultEmbed (m k S : ℕ) (t₀ : Fin S) (E : Vec k) :
    FaultTerm1 (Fin m × Fin 0) (Fin k × Fin S) → ZMod 2 :=
  Sum.elim (fun u : Fin m × Fin 0 => (IsEmpty.false u.2).elim)
    (fun q : Fin k × Fin S => if q.2 = t₀ then E q.1 else 0)

/-- The component of the embedded fault on the `i`-th time slice. -/
theorem sliceFaultEmbed_slice_apply {m k S : ℕ} (t₀ : Fin S) (E : Vec k) (i : Fin S)
    (b : Fin k) :
    sliceFaultEmbed m k S t₀ E (Sum.inr (b, i)) = (if i = t₀ then E else 0) b := by
  by_cases h : i = t₀
  · rw [h, ite_eq_left rfl]
    change (if (b, t₀).2 = t₀ then E (b, t₀).1 else 0) = E b
    rw [ite_eq_left (show (b, t₀).2 = t₀ from rfl)]
  · rw [ite_eq_right h]
    change (if (b, i).2 = t₀ then E (b, i).1 else 0) = (0 : ZMod 2)
    rw [ite_eq_right (show ¬((b, i).2 = t₀) from fun hh => h (by simpa using hh))]

/-- The `i`-th time slice of the embedded fault. -/
theorem sliceFaultEmbed_slice {m k S : ℕ} (t₀ : Fin S) (E : Vec k) (i : Fin S) :
    (fun b : Fin k => sliceFaultEmbed m k S t₀ E (Sum.inr (b, i)))
      = (if i = t₀ then E else 0) := by
  funext b
  rw [sliceFaultEmbed_slice_apply]

/-- The embedding preserves weight (`hammingNorm_sum_inr` + `hammingNorm_sliceEmbed`). -/
theorem hammingNorm_sliceFaultEmbed {m k S : ℕ} (t₀ : Fin S) (E : Vec k) :
    hammingNorm (sliceFaultEmbed m k S t₀ E) = hammingNorm E := by
  rw [hammingNorm_sum_inr (f := sliceFaultEmbed m k S t₀ E)]
  exact hammingNorm_sliceEmbed t₀ E

/-- The embedded fault is sent to zero by $\partial_0$. -/
theorem degenerate_sliceFaultEmbed_mem_ker {m k rz S : ℕ}
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) (t₀ : Fin S) {E : Vec k}
    (hE : E ∈ LinearMap.ker Hx.toLin') :
    sliceFaultEmbed m k S t₀ E ∈ LinearMap.ker (fd0
      (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
      (degenerateFaultComplex m k rz S Hx Hz hC).d01_00).toLin' := by
  change IsDetectorSilent (fd0 (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
      (degenerateFaultComplex m k rz S Hx Hz hC).d01_00) (sliceFaultEmbed m k S t₀ E)
  rw [degenerate_fd0_mem_ker Hx Hz hC (sliceFaultEmbed m k S t₀ E)]
  intro c i
  rw [sliceFaultEmbed_slice]
  by_cases h : i = t₀
  · rw [ite_eq_left h]
    exact (mem_ker_toLin'_iff_rows Hx E).mp hE c
  · rw [ite_eq_right h]
    simp

/-- The embedded fault is not in the image of $\partial_1$. -/
theorem degenerate_sliceFaultEmbed_notMem_range {m k rz S : ℕ}
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) (t₀ : Fin S) {E : Vec k} (hE : E ∉ Hz.rowSpace) :
    sliceFaultEmbed m k S t₀ E ∉ LinearMap.range (fd1
      (degenerateFaultComplex m k rz S Hx Hz hC).d11_10
      (degenerateFaultComplex m k rz S Hx Hz hC).d11_01
      (degenerateFaultComplex m k rz S Hx Hz hC).d02_01).toLin' := by
  rw [degenerate_fd1_mem_range Hx Hz hC (sliceFaultEmbed m k S t₀ E)]
  intro h
  have h0 := h t₀
  rw [sliceFaultEmbed_slice t₀ E t₀, ite_eq_left rfl] at h0
  exact hE h0

/-- **Extracting a static undetectable operator from an undetectable logical fault**: as
soon as the fault is not in the image of $\partial_1$, there is a time slice whose slice
is not an element of $H_Z$'s row space (the image of $\partial_1$ is slicewise, so "not in
the image" must show up on some time slice). -/
theorem degenerate_exists_slice_notMem_rowSpace {m k rz S : ℕ}
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) {f : FaultTerm1 (Fin m × Fin 0) (Fin k × Fin S) → ZMod 2}
    (hf : f ∉ LinearMap.range (fd1 (degenerateFaultComplex m k rz S Hx Hz hC).d11_10
      (degenerateFaultComplex m k rz S Hx Hz hC).d11_01
      (degenerateFaultComplex m k rz S Hx Hz hC).d02_01).toLin') :
    ∃ i : Fin S, (fun b : Fin k => f (Sum.inr (b, i))) ∉ Hz.rowSpace := by
  by_contra h
  refine hf ((degenerate_fd1_mem_range Hx Hz hC f).mpr fun i => ?_)
  exact not_not.mp (not_exists.mp h i)

/-- Every time slice of a detector-silent fault lies in the kernel of `H_X`. -/
theorem degenerate_slice_mem_ker {m k rz S : ℕ}
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) {f : FaultTerm1 (Fin m × Fin 0) (Fin k × Fin S) → ZMod 2}
    (hf : f ∈ LinearMap.ker (fd0 (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
      (degenerateFaultComplex m k rz S Hx Hz hC).d01_00).toLin') (i : Fin S) :
    (fun b : Fin k => f (Sum.inr (b, i))) ∈ LinearMap.ker Hx.toLin' := by
  rw [mem_ker_toLin'_iff_rows]
  intro c
  exact (degenerate_fd0_mem_ker Hx Hz hC f).mp hf c i

/-- **The weight set of the undetectable logical faults on the degenerate complex**: the
set whose `sInf` is `faultDistance`. It is named as a `def` so that the main theorem below
can reason with set equalities instead of writing the unfolding out repeatedly. -/
def degenerateFaultWeightSet (m k rz S : ℕ)
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) : Set ℕ :=
  {w : ℕ | ∃ f : FaultTerm1 (Fin m × Fin 0) (Fin k × Fin S) → ZMod 2,
      IsUndetectedLogicalFault
        (fd0 (degenerateFaultComplex m k rz S Hx Hz hC).d10_00
          (degenerateFaultComplex m k rz S Hx Hz hC).d01_00)
        (LinearMap.range (fd1 (degenerateFaultComplex m k rz S Hx Hz hC).d11_10
          (degenerateFaultComplex m k rz S Hx Hz hC).d11_01
          (degenerateFaultComplex m k rz S Hx Hz hC).d02_01).toLin') f
      ∧ hammingNorm f = w}

/-- **The weight set of the static undetectable operators**: the set whose `Finset.min` is
`min_weight_ker_not_mem_rowspace`. -/
def undetectableWeightSet {n m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) : Set ℕ :=
  {w : ℕ | ∃ E ∈ undetectableSet M₁ M₂, hammingNorm E = w}

/-- **The Z-side distance of the degenerate fault complex is the static code distance**
(the gap of honest boundary 2 in the module header). On the degenerate fault complex with
no coupling along the time direction ($R_1 = \varnothing$), `faultComplexDistanceZ` and
`min_weight_ker_not_mem_rowspace` give **the same number**:

* one side ($\le$): embed the static undetectable operator $E$ in a single time slice
  (`sliceFaultEmbed`); `degenerate_sliceFaultEmbed_mem_ker` / `_notMem_range` give an
  undetectable logical fault on the complex, and `hammingNorm_sliceFaultEmbed` says the
  weight is unchanged -- the complex's distance is **at most** the static code distance;
* the other side ($\ge$): take any undetectable logical fault $f$ on the complex;
  `degenerate_exists_slice_notMem_rowSpace` gives a slice that is not in $H_Z$'s row
  space, which is automatically nonzero ($0$ is in the row space), and
  `degenerate_slice_mem_ker` says it is in the kernel of $H_X$, so it is a static
  undetectable operator, while `hammingNorm_slice_le` says its weight is at most that of
  $f$ -- the static code distance is **at most** the complex's distance.

**Why the two hypotheses** (honest boundary 3 in the module header):
`min_weight_ker_not_mem_rowspace` returns $n + 1$ when the set is empty, while
`faultDistance` uses `sInf` and gives $0$ on the empty set -- the two definitions part ways
on the empty set, so the nonemptiness is written out explicitly here; `0 < S` has the same
kind of reason (with no time slice at all the fault space itself is empty and this module
gives $0$, while the right-hand side is still $n + 1$ or the code distance).

**Boundary**: the case $R \ne 0$ (a real differential along the time direction, genuine
multi-round coupling) is **not inside this item** -- there $\mathrm{im}\,\partial_1$ is no
longer slicewise (the image on one slice can couple with the image on another), and this
item's slice argument does not apply. -/
theorem faultComplexDistanceZ_degenerate {m k rz S : ℕ} (hS : 0 < S)
    (Hx : Matrix (Fin m) (Fin k) (ZMod 2)) (Hz : Matrix (Fin rz) (Fin k) (ZMod 2))
    (hC : Hx * Hz.transpose = 0) (hne : (undetectableSet Hx Hz).Nonempty) :
    faultComplexDistanceZ (degenerateFaultComplex m k rz S Hx Hz hC)
      = min_weight_ker_not_mem_rowspace Hx Hz := by
  have hF : faultComplexDistanceZ (degenerateFaultComplex m k rz S Hx Hz hC)
      = sInf (degenerateFaultWeightSet m k rz S Hx Hz hC) := rfl
  have hS' : min_weight_ker_not_mem_rowspace Hx Hz = sInf (undetectableWeightSet Hx Hz) := by
    rw [sInf_image_undetectableSet_eq_minWeight Hx Hz hne, sInf_hammingNorm_image]
    rfl
  rw [hF, hS']
  refine le_antisymm ?_ ?_
  · refine le_csInf ?_ ?_
    · obtain ⟨E, hE⟩ := hne
      exact ⟨hammingNorm E, ⟨E, hE, rfl⟩⟩
    · rintro w ⟨E, hE, rfl⟩
      have hmem : hammingNorm (sliceFaultEmbed m k S ⟨0, hS⟩ E)
          ∈ degenerateFaultWeightSet m k rz S Hx Hz hC :=
        ⟨sliceFaultEmbed m k S ⟨0, hS⟩ E,
          ⟨degenerate_sliceFaultEmbed_mem_ker Hx Hz hC ⟨0, hS⟩ hE.1,
            degenerate_sliceFaultEmbed_notMem_range Hx Hz hC ⟨0, hS⟩ hE.2⟩, rfl⟩
      exact (csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hmem).trans_eq
        (hammingNorm_sliceFaultEmbed ⟨0, hS⟩ E)
  · refine le_csInf ?_ ?_
    · obtain ⟨E, hE⟩ := hne
      exact ⟨hammingNorm E, ⟨sliceFaultEmbed m k S ⟨0, hS⟩ E,
        ⟨degenerate_sliceFaultEmbed_mem_ker Hx Hz hC ⟨0, hS⟩ hE.1,
          degenerate_sliceFaultEmbed_notMem_range Hx Hz hC ⟨0, hS⟩ hE.2⟩,
        hammingNorm_sliceFaultEmbed ⟨0, hS⟩ E⟩⟩
    · rintro w ⟨f, hf, rfl⟩
      obtain ⟨i, hi⟩ := degenerate_exists_slice_notMem_rowSpace Hx Hz hC (f := f) hf.2
      have hker := degenerate_slice_mem_ker Hx Hz hC (f := f) hf.1 i
      have hle : hammingNorm (fun b : Fin k => f (Sum.inr (b, i))) ≤ hammingNorm f := by
        rw [hammingNorm_sum_inr (f := f)]
        exact hammingNorm_slice_le (fun q : Fin k × Fin S => f (Sum.inr q)) i
      have hmem : hammingNorm (fun b : Fin k => f (Sum.inr (b, i))) ∈ undetectableWeightSet Hx Hz :=
        ⟨_, ⟨hker, hi⟩, rfl⟩
      exact le_trans (csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hmem) hle

/-! ## 8. The first instance with $R \ne 0$: the timelike distance on the fault complex

The slice argument of §7 requires the image of $\partial_1$ to be **slicewise**, so it
holds only for $R = 0$ (no coupling along the time direction). That route fails for
$R \ne 0$, but the **time direction itself** can be computed independently: take $C$
trivial, i.e. $C_0 = \mathrm{Fin}\,1$ and $C_1 = C_2 = \varnothing$, so that
$\partial_0 = \mathrm{id}\otimes R$ and $\partial_1 = 0$; the fault complex degenerates to
"one bit times the time axis", and its Z-side distance is exactly the **number of time
slices $\ell+1$**:

$$\texttt{faultComplexDistanceZ}\ (\mathcal R \otimes C) = \ell + 1,$$

where $\ell + 1$ is the number of time slices (this draft identifies time slices with
rounds one to one, so it is also the number of rounds) and $R$ is the repetition-code check
matrix with $\ell + 1$ columns (`repR l`, $l = \ell$). This is the **same law** as the
$S + 1$ of `faultDistance_timeLike` in §4, but this time computed on a Koszul complex
**with a real differential $R \ne 0$**: two routes that had each said their own thing now
cross-check, and honest boundary 2's "$R \ne 0$ still not done" is closed on this family.

**Why it can be computed**: the kernel is **one-dimensional** -- $\ker R$ is spanned
exactly by the all-$1$ vector (`repR_ker_eq_span_allOnes`), so a nonzero fault in
$\ker\partial_0 = \{f : (\mathrm{id}\otimes R)f = 0\}$ can only be the constant $1$ along
the time axis, of weight exactly all $\ell + 1$ slices; and $\partial_1 = 0$ leaves zero as
the only trivial fault, so the lightest undetectable logical fault is that one.

**The general $C$ case: the branch $H_0(C)\ne0$ is machine-checked (§10); the probe below
fixes it numerically on arbitrary small CSS complexes.** Replacing $C$ by an arbitrary
small CSS complex ($R$ still `repR l`), the deposit probe
`paper/code/koszul_reduction/koszul_dist_probe.jl` exhaustively obtains, on **202 small
instances**, two **equivalent** closed forms with **zero counterexamples**: the distance
is $= (\ell+1)\cdot w_0$ ($w_0$ = the minimum weight of $C_0 \setminus
\mathrm{im}\,dC_1$), and the observed $w_0 \in \{0,1\}$ always holds, so this is equivalent
to "$\ell+1$ when $\mathrm{im}\,dC_1 \ne \top$, and $0$ otherwise". **Physical reading**:
under the repetition-code foliation the Z-side distance is **purely temporal** -- equal to
the number of time slices (that is, the number of rounds), independent of the code ($C$
only decides whether there is a nontrivial fault). **Boundary**: this is **numerical
fixing, not machine checking**; the author's "readout route" lower-bound argument has one
unfilled gap (the residual term lands in $\ker dC_1$ but not necessarily in
$\mathrm{im}\,dC_2$), and the scan has no counterexample to it, which says the gap can be
filled though the way is undecided. -/

/-- **Zero-sum decomposition (left)**: when `β` is empty the weight on `α ⊕ β` is the
weight on the `α` half (the mirror of `hammingNorm_sum_inr`). -/
theorem hammingNorm_sum_inl {α β : Type*} [Fintype α] [Fintype β] [IsEmpty β]
    (f : α ⊕ β → ZMod 2) :
    hammingNorm f = hammingNorm (fun a : α => f (Sum.inl a)) := by
  classical
  have h1 : hammingNorm f = (Finset.univ.filter fun x : α ⊕ β => f x ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm (fun a : α => f (Sum.inl a))
      = (Finset.univ.filter fun a : α => f (Sum.inl a) ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, h2]
  refine Finset.card_nbij'
    (fun x : α ⊕ β => Sum.elim (fun a => a) (fun b => (IsEmpty.false b).elim) x)
    (fun a : α => Sum.inl a) ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with a | b
    · simpa using hx
    · exact (IsEmpty.false b).elim
  · intro a ha
    simpa using ha
  · intro x hx
    rcases x with a | b
    · rfl
    · exact (IsEmpty.false b).elim
  · intro a _
    rfl

/-- The weight of the constant-$1$ vector. -/
theorem hammingNorm_one_const (n : ℕ) :
    hammingNorm (fun _ : Fin n => (1 : ZMod 2)) = n := by
  classical
  have h1 : hammingNorm (fun _ : Fin n => (1 : ZMod 2))
      = (Finset.univ.filter fun _ : Fin n => (1 : ZMod 2) ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, Finset.filter_true_of_mem (fun _ _ => one_ne_zero), Finset.card_univ,
    Fintype.card_fin]

/-- The weight on `Fin 1 × Fin n` is the weight on the `Fin n` half. -/
theorem hammingNorm_fin1_prod {n : ℕ} (g : Fin 1 × Fin n → ZMod 2) :
    hammingNorm g = hammingNorm (fun j : Fin n => g (0, j)) := by
  classical
  have h1 : hammingNorm g = (Finset.univ.filter fun p : Fin 1 × Fin n => g p ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm (fun j : Fin n => g (0, j))
      = (Finset.univ.filter fun j : Fin n => g (0, j) ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, h2]
  refine Finset.card_nbij' (fun p : Fin 1 × Fin n => p.2) (fun j : Fin n => (0, j)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨a, b⟩ := p
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simpa using hp
  · intro j hj
    simpa using hj
  · intro p hp
    obtain ⟨a, b⟩ := p
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rfl
  · intro j _
    rfl

/-! ### 8.1 The Koszul fault complex of the trivial $C$ -/

/-- The trivial $C$: $C_0 = \mathrm{Fin}\,1$, no checks. -/
abbrev trivialCSS₁ : Matrix (Fin 1) (Fin 0) (ZMod 2) := 0

/-- As above ($C_2 = \varnothing$). -/
abbrev trivialCSS₂ : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0

theorem trivialCSS_mul : trivialCSS₁ * trivialCSS₂ = 0 := by
  ext i j
  exact (IsEmpty.false j).elim

/-- **The Koszul fault complex over the trivial code complex**: one bit and no checks, so
$\partial_0 = \mathrm{id}\otimes R$ and $\partial_1 = 0$, and the complex is the time
direction itself. -/
abbrev koszulTimeLike (l : ℕ) :
    FaultComplex (Fin 1 × Fin l) (Fin 0 × Fin l) (Fin 0 × Fin l)
      (Fin 1 × Fin (l + 1)) (Fin 0 × Fin (l + 1)) (Fin 0 × Fin (l + 1)) :=
  koszulFaultComplex (repR l) trivialCSS₁ trivialCSS₂ trivialCSS_mul

/-- **The weight falls only on the $F_{1,0}$ half** ($C_1 = \varnothing$ makes $F_{0,1}$
empty). -/
theorem koszulTimeLike_weight (l : ℕ)
    (f : FaultTerm1 (Fin 1 × Fin (l + 1)) (Fin 0 × Fin l) → ZMod 2) :
    hammingNorm f = hammingNorm (fun j : Fin (l + 1) => f (Sum.inl (0, j))) := by
  rw [hammingNorm_sum_inl f]
  exact hammingNorm_fin1_prod (fun p : Fin 1 × Fin (l + 1) => f (Sum.inl p))

/-- **One-dimensionality of $\ker R$**: an element is either $0$ or all $1$. -/
theorem repR_ker_eq_zero_or_allOnes (l : ℕ) (y : Fin (l + 1) → ZMod 2)
    (hy : y ∈ LinearMap.ker (repR l).mulVecLin) : y = 0 ∨ y = 1 := by
  rw [repR_ker_eq_span_allOnes l] at hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz c with h | h
  · exact Or.inl (by rw [h, zero_smul] at hc; exact hc.symm)
  · exact Or.inr (by rw [h, one_smul] at hc; exact hc.symm)

/-- **The component reading of $\partial_0$**: the left half of the rows gives
$(\mathrm{id}\otimes R)x$, and the right half vanishes because $F_{0,1}$ is empty. -/
theorem koszulTimeLike_fd0_apply (l : ℕ)
    (f : FaultTerm1 (Fin 1 × Fin (l + 1)) (Fin 0 × Fin l) → ZMod 2) (a : Fin 1) (i : Fin l) :
    ((fd0 (koszulTimeLike l).d10_00 (koszulTimeLike l).d01_00) *ᵥ f) (Sum.inl (a, i))
      = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
          (repR l)) *ᵥ (fun p : Fin 1 × Fin (l + 1) => f (Sum.inl p))) (a, i) := by
  have hd10 : (koszulTimeLike l).d10_00
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))
          (repR l) := rfl
  simp only [fd0, hd10, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fintype.sum_sum_type,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.fromBlocks_apply₁₁]

/-- **Transport of the kernel condition**: $\partial_0 f = 0$ implies that the $(0,\cdot)$
slice of $f$ on the $F_{1,0}$ half lies in $\ker R$. -/
theorem koszulTimeLike_ker_reduce (l : ℕ)
    (f : FaultTerm1 (Fin 1 × Fin (l + 1)) (Fin 0 × Fin l) → ZMod 2)
    (hf : (fd0 (koszulTimeLike l).d10_00 (koszulTimeLike l).d01_00).toLin' f = 0) :
    (fun j : Fin (l + 1) => f (Sum.inl (0, j))) ∈ LinearMap.ker (repR l).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext i
  have hc : ((fd0 (koszulTimeLike l).d10_00 (koszulTimeLike l).d01_00) *ᵥ f)
      (Sum.inl (0, i)) = 0 := by
    have h1 := congrFun hf (Sum.inl (0, i))
    rwa [Matrix.toLin'_apply, Pi.zero_apply] at h1
  rw [koszulTimeLike_fd0_apply l f 0 i] at hc
  rw [kroneckerMap_one_left_mulVec_apply] at hc
  exact hc

/-- **The all-$1$ fault**: constantly $1$ along the time axis. -/
def koszulTimeLikeAllOnes (l : ℕ) :
    FaultTerm1 (Fin 1 × Fin (l + 1)) (Fin 0 × Fin l) → ZMod 2 := fun _ => 1

theorem koszulTimeLikeAllOnes_ne_zero (l : ℕ) : koszulTimeLikeAllOnes l ≠ 0 := by
  intro h
  have hc := congrFun h (Sum.inl ((0 : Fin 1), ⟨0, Nat.succ_pos l⟩))
  simp [koszulTimeLikeAllOnes] at hc

theorem koszulTimeLikeAllOnes_weight (l : ℕ) :
    hammingNorm (koszulTimeLikeAllOnes l) = l + 1 := by
  rw [koszulTimeLike_weight l (koszulTimeLikeAllOnes l)]
  exact hammingNorm_one_const (l + 1)

/-- The target space of `∂₁` is empty, so its image is only zero. -/
theorem koszulTimeLike_fd1_apply (l : ℕ)
    (x : FaultTerm2 (Fin 0 × Fin (l + 1)) (Fin 0 × Fin l) → ZMod 2) :
    (fd1 (koszulTimeLike l).d11_10 (koszulTimeLike l).d11_01 (koszulTimeLike l).d02_01).toLin' x
      = 0 := by
  funext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.univ_eq_empty,
    Finset.sum_empty, Pi.zero_apply]

theorem koszulTimeLikeAllOnes_silent (l : ℕ) :
    IsDetectorSilent (fd0 (koszulTimeLike l).d10_00 (koszulTimeLike l).d01_00)
      (koszulTimeLikeAllOnes l) := by
  rw [IsDetectorSilent, LinearMap.mem_ker]
  funext r
  rcases r with ⟨a, i⟩ | q
  · simp only [Matrix.toLin'_apply, Pi.zero_apply]
    rw [koszulTimeLike_fd0_apply l (koszulTimeLikeAllOnes l) a i]
    have h1 : (fun p : Fin 1 × Fin (l + 1) => koszulTimeLikeAllOnes l (Sum.inl p))
        = (fun _ => (1 : ZMod 2)) := rfl
    rw [h1, kroneckerMap_one_left_mulVec_apply]
    change (repR l *ᵥ (1 : Fin (l + 1) → ZMod 2)) i = 0
    exact congrFun (repR_allOnes_mem_ker l) i
  · exact Fin.elim0 q

theorem koszulTimeLikeAllOnes_notMem (l : ℕ) :
    koszulTimeLikeAllOnes l ∉ LinearMap.range
      (fd1 (koszulTimeLike l).d11_10 (koszulTimeLike l).d11_01
        (koszulTimeLike l).d02_01).toLin' := by
  rintro ⟨x, hx⟩
  rw [koszulTimeLike_fd1_apply l x] at hx
  exact koszulTimeLikeAllOnes_ne_zero l hx.symm

/-- The weight set over the trivial $C$. -/
def koszulTimeLikeWeightSet (l : ℕ) : Set ℕ :=
  {w : ℕ | ∃ f : FaultTerm1 (Fin 1 × Fin (l + 1)) (Fin 0 × Fin l) → ZMod 2,
    IsUndetectedLogicalFault (fd0 (koszulTimeLike l).d10_00 (koszulTimeLike l).d01_00)
      (LinearMap.range (fd1 (koszulTimeLike l).d11_10 (koszulTimeLike l).d11_01
        (koszulTimeLike l).d02_01).toLin') f
    ∧ hammingNorm f = w}

/-- **On the Koszul fault complex with $R \ne 0$, the Z-side fault distance is the number
of time slices $l+1$ (this draft identifies time slices with rounds one to one, so it is
also the number of rounds).**

This is the closure of honest boundary 2's "$R \ne 0$ still not done" on the **timelike
family**: the image of $\partial_1$ is no longer slicewise, so the slice argument of §7
does not apply, but the one-dimensionality of the kernel (`repR_ker_eq_span_allOnes`)
presses the candidates down to the single vector "constantly $1$ along the time axis", so
the distance can be computed exactly -- cross-checking with `faultDistance_timeLike`
($S + 1$) of §4, and this time the differential $R \ne 0$ is real. -/
theorem faultComplexDistanceZ_koszulTimeLike (l : ℕ) :
    faultComplexDistanceZ (koszulTimeLike l) = l + 1 := by
  have hdef : faultComplexDistanceZ (koszulTimeLike l) = sInf (koszulTimeLikeWeightSet l) := rfl
  have hmem : (l + 1) ∈ koszulTimeLikeWeightSet l :=
    ⟨koszulTimeLikeAllOnes l,
      ⟨koszulTimeLikeAllOnes_silent l, koszulTimeLikeAllOnes_notMem l⟩,
      koszulTimeLikeAllOnes_weight l⟩
  rw [hdef]
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hmem
  · refine le_csInf ⟨l + 1, hmem⟩ ?_
    rintro w ⟨f, hf, rfl⟩
    have hker : (fd0 (koszulTimeLike l).d10_00 (koszulTimeLike l).d01_00).toLin' f = 0 :=
      LinearMap.mem_ker.mp hf.1
    have hy := koszulTimeLike_ker_reduce l f hker
    rcases repR_ker_eq_zero_or_allOnes l (fun j : Fin (l + 1) => f (Sum.inl (0, j))) hy
      with h0 | h1
    · exfalso
      have hz : hammingNorm f = 0 := by
        rw [koszulTimeLike_weight l f, h0]
        exact hammingNorm_eq_zero.mpr rfl
      have hfz : f = 0 := hammingNorm_eq_zero.mp hz
      exact hf.2 (hfz ▸ Submodule.zero_mem _)
    · rw [koszulTimeLike_weight l f, h1]
      exact le_of_eq (hammingNorm_one_const (l + 1)).symm

variable {C₀ C₁ C₂ : Type*} [Fintype C₀] [Fintype C₁] [Fintype C₂]
variable [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂]

/-! ## 9. The toolkit layer for general $C$

It gives the component readings of $\partial_0/\partial_1$ and the "slice--quotient" map.
In §8, $C$ is trivial. The **distance** for general $C$ is given by the theorem of §10
(the branch $H_0(C)\ne0$, which takes another route); its lower bound is the hard part of
that theorem, and the author's "readout route" argument (mapping fault classes into
$C_0/\mathrm{im}\,dC_1$ and forcing injectivity by a Künneth dimension count) has one
further unfilled gap, see the README of the deposit probe `paper/code/koszul_reduction/`.
**This section only delivers the toolkit layer**: the component readings of $\partial_0$
and $\partial_1$ for general $C$, the linear map $M \to (C_0\to\mathbb F_2)/
\mathrm{im}\,dC_1$ that "takes the $j_0$-th slice and then the quotient", and two proved
properties -- it vanishes on $\mathrm{im}\,\partial_1$, and all-$1$ faults (`liftFault`)
lie in $\ker\partial_0$. The two component lemmas of §8 are this layer's special case when
$C$ is trivial. -/

/-- **The component reading of $\partial_0$ (general $C$)**: the left half gives
$(\mathrm{id}\otimes R)x$, the right half gives $(dC_1\otimes\mathrm{id})y$. -/
theorem koszulFaultComplex_fd0_apply (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (f : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2) (a : C₀) (i : Fin l) :
    ((fd0 (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00) *ᵥ f) (Sum.inl (a, i))
      = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₀ C₀ (ZMod 2)) (repR l)) *ᵥ
          (fun p : C₀ × Fin (l + 1) => f (Sum.inl p))) (a, i)
        + ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
            (1 : Matrix (Fin l) (Fin l) (ZMod 2))) *ᵥ
          (fun q : C₁ × Fin l => f (Sum.inr q))) (a, i) := by
  have hd10 : (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₀ C₀ (ZMod 2))
          (repR l) := rfl
  have hd01 : (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
          (1 : Matrix (Fin l) (Fin l) (ZMod 2)) := rfl
  simp only [fd0, hd10, hd01, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]

/-- **The component reading of $\partial_1$ (general $C$)**: the left half gives
$(dC_1\otimes\mathrm{id})a$. -/
theorem koszulFaultComplex_fd1_apply (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (a : FaultTerm2 (C₁ × Fin (l + 1)) (C₂ × Fin l) → ZMod 2) (c : C₀) (j : Fin (l + 1)) :
    ((fd1 (koszulFaultComplex (repR l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repR l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repR l) dC1 dC2 hC).d02_01) *ᵥ a) (Sum.inl (c, j))
      = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
            (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
          (fun p : C₁ × Fin (l + 1) => a (Sum.inl p))) (c, j) := by
  have hd11 : (koszulFaultComplex (repR l) dC1 dC2 hC).d11_10
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
          (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2)) := rfl
  simp only [fd1, hd11, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- The fault $(n\otimes\mathbf 1, 0)$ that spreads $n \in C_0\to\mathbb F_2$ constantly
along the time axis. -/
def liftFault (l : ℕ) (n : C₀ → ZMod 2) :
    FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2 :=
  Sum.elim (fun p => n p.1) (fun _ => 0)

/-- **This fault is undetectable**: $R\cdot\mathbf 1 = 0$ makes
$(n\otimes\mathbf 1,0)\in\ker\partial_0$. This is the machine form of "every $C_0$
direction can be spread out constantly along the time axis". -/
theorem liftFault_mem_ker (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (n : C₀ → ZMod 2) :
    liftFault l n ∈ LinearMap.ker
      (fd0 (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00).mulVecLin := by
  rw [LinearMap.mem_ker]
  funext r
  rcases r with ⟨a, i⟩ | q
  · rw [Matrix.mulVecLin_apply, Pi.zero_apply, koszulFaultComplex_fd0_apply]
    have hz : (fun q : C₁ × Fin l => liftFault l n (Sum.inr q)) = 0 := rfl
    rw [hz, Matrix.mulVec_zero, Pi.zero_apply, add_zero,
      kroneckerMap_one_left_mulVec_apply]
    simp only [liftFault, Sum.elim_inl]
    change (repR l *ᵥ (fun _ : Fin (l + 1) => n a)) i = 0
    have h1 : (fun _ : Fin (l + 1) => n a) = n a • (1 : Fin (l + 1) → ZMod 2) := by
      funext j
      simp
    have h2 : (repR l *ᵥ (1 : Fin (l + 1) → ZMod 2)) i = 0 :=
      congrFun (repR_allOnes_mem_ker l) i
    rw [h1, Matrix.mulVec_smul, Pi.smul_apply, h2, smul_zero]
  · exact Fin.elim0 q

/-- **"Take the $j_0$-th slice, then the quotient"**: $M \to (C_0\to\mathbb F_2)/
\mathrm{im}\,dC_1$. This is the readout route for general $C$ -- the information in the
$C_0$ directions is projected out and the rest is quotiented away. -/
noncomputable def sliceMod (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2)) (j₀ : Fin (l + 1)) :
    (FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2) →ₗ[ZMod 2]
      ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin) :=
  (LinearMap.range dC1.mulVecLin).mkQ.comp
    (LinearMap.pi fun c : C₀ =>
      LinearMap.proj (Sum.inl (⟨c, j₀⟩ : C₀ × Fin (l + 1))))

/-- **$\mathrm{im}\,\partial_1 \le \psi.\ker$**: the value of an element of
$\mathrm{im}\,\partial_1$ on the $j_0$-th slice lies in $\mathrm{im}\,dC_1$ (because it is
$dC_1$ times some vector). This says "the readout route is zero on trivial faults", and it
is the entire basis on which $\psi$ descends to the quotient. -/
theorem range_fd1_le_sliceMod_ker (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (j₀ : Fin (l + 1)) :
    LinearMap.range (fd1 (koszulFaultComplex (repR l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repR l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repR l) dC1 dC2 hC).d02_01).mulVecLin
      ≤ (sliceMod (C₀ := C₀) (C₁ := C₁) l dC1 j₀).ker := by
  rintro x ⟨a, rfl⟩
  rw [LinearMap.mem_ker]
  show Submodule.Quotient.mk (fun c : C₀ =>
      ((fd1 (koszulFaultComplex (repR l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repR l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repR l) dC1 dC2 hC).d02_01) *ᵥ a) (Sum.inl (c, j₀))) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨fun b : C₁ => a (Sum.inl (b, j₀)), ?_⟩
  funext c
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, koszulFaultComplex_fd1_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro y _ hy
    rw [ite_eq_right (fun h : j₀ = y => hy h.symm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] in
/-- **The value of the readout route on an all-$1$ fault**: $\psi(n\otimes\mathbf 1) =
[n]$. This turns "every $C_0$ direction can be spread along the time axis" into a witness
for "the readout route is surjective". -/
theorem sliceMod_liftFault (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2)) (j₀ : Fin (l + 1))
    (n : C₀ → ZMod 2) :
    sliceMod l dC1 j₀ (liftFault (C₁ := C₁) l n) = Submodule.Quotient.mk n := rfl

/-- **$\psi|_K$ is surjective**: every $C_0$ direction is witnessed by an undetectable
all-$1$ fault. -/
theorem sliceMod_surjective (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (j₀ : Fin (l + 1)) :
    Function.Surjective ⇑((sliceMod (C₁ := C₁) l dC1 j₀).comp
      (LinearMap.ker (fd0 (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00).mulVecLin).subtype) := by
  intro y
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range dC1.mulVecLin) y
  exact ⟨⟨liftFault l n, liftFault_mem_ker l dC1 dC2 hC n⟩, sliceMod_liftFault l dC1 j₀ n⟩

/-- **The core lemma (dimension route)**: if $x\in\ker\partial_0$ and its $j_0$-th slice
lies in $\mathrm{im}\,dC_1$, then $x$ is **trivial** ($\in\mathrm{im}\,\partial_1$).

**The proof does not go through an explicit construction** (that route has a gap: the
residual term lands in $\ker dC_1$ and not necessarily in $\mathrm{im}\,dC_2$), but
through dimensions: $\mathrm{im}\,\partial_1\le\psi.\ker$ and $\psi|_K$ surjective, with
rank-nullity plus `kunneth_H1` give
$\mathrm{finrank}\,(K\sqcap\psi.\ker)=\mathrm{finrank}\,I$, and
`Submodule.eq_of_le_of_finrank_le` then forces $I = K\sqcap\psi.\ker$. -/
theorem koszul_repR_slice_trivial (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (j₀ : Fin (l + 1))
    (x : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2)
    (hxK : x ∈ LinearMap.ker (fd0 (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00).mulVecLin)
    (hx : sliceMod l dC1 j₀ x = 0) :
    x ∈ LinearMap.range (fd1 (koszulFaultComplex (repR l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repR l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repR l) dC1 dC2 hC).d02_01).mulVecLin := by
  set F := koszulFaultComplex (repR l) dC1 dC2 hC with hF
  set K : Submodule (ZMod 2) (FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2) :=
    LinearMap.ker (fd0 F.d10_00 F.d01_00).mulVecLin with hKdef
  set I : Submodule (ZMod 2) (FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2) :=
    LinearMap.range (fd1 F.d11_10 F.d11_01 F.d02_01).mulVecLin with hIdef
  set ψ : (FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2) →ₗ[ZMod 2]
      ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin) := sliceMod l dC1 j₀ with hψdef
  have hIK : I ≤ K := range_fd1_le_ker_fd0 F
  have hIψ : I ≤ ψ.ker := range_fd1_le_sliceMod_ker l dC1 dC2 hC j₀
  have hsurj : (ψ.comp K.subtype).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact sliceMod_surjective l dC1 dC2 hC j₀
  have hrn := LinearMap.finrank_range_add_finrank_ker (ψ.comp K.subtype)
  rw [hsurj] at hrn
  have htop : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2)
        ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin))
      = Module.finrank (ZMod 2) ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin) :=
    (Submodule.topEquiv (R := ZMod 2)).finrank_eq
  rw [htop] at hrn
  have hk := kunneth_H1 (repR l) dC1 dC2 hC
  rw [repR_twoTermH1, repR_twoTermH0] at hk
  simp only [one_mul, zero_mul, add_zero] at hk
  have hFI : faultH1 F = Module.finrank (ZMod 2) ↥K - Module.finrank (ZMod 2) ↥I := rfl
  have hle : Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) ↥K :=
    Submodule.finrank_mono hIK
  have hq : threeTermH0 dC1 = Module.finrank (ZMod 2)
      ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin) := rfl
  have hk' : Module.finrank (ZMod 2) ↥K - Module.finrank (ZMod 2) ↥I
      = Module.finrank (ZMod 2) ((C₀ → ZMod 2) ⧸ LinearMap.range dC1.mulVecLin) := by
    rw [← hFI, hk, hq]
  have hfin : Module.finrank (ZMod 2) ↥((ψ.comp K.subtype).ker)
      = Module.finrank (ZMod 2) ↥I := by omega
  have hmap2 : K ⊓ ψ.ker = Submodule.map K.subtype (ψ.comp K.subtype).ker := by
    rw [LinearMap.ker_comp, Submodule.map_comap_eq, Submodule.range_subtype, inf_comm]
  have hfin2 : Module.finrank (ZMod 2) ↥(K ⊓ ψ.ker)
      ≤ Module.finrank (ZMod 2) ↥((ψ.comp K.subtype).ker) := by
    rw [hmap2]
    exact Submodule.finrank_map_le _ _
  have hxinf : x ∈ K ⊓ ψ.ker := ⟨hxK, hx⟩
  have heq : I = K ⊓ ψ.ker :=
    Submodule.eq_of_le_of_finrank_le (le_inf hIK hIψ) (le_trans hfin2 (le_of_eq hfin))
  exact heq.symm ▸ hxinf

/-! ## 10. The distance theorem for $R \ne 0$ with general $C$ (repetition-code foliation)

**Conclusion**: as soon as $\mathrm{im}\,dC_1\ne\top$ (equivalently $H_0(C)\ne0$;
**note** that this is **not** equivalent to "there is a nontrivial logical fault",
$H_1(C)\ne0$ -- the hypothesis of this theorem is the former), the Z-side fault distance is
**exactly the number of rounds $+1$**, **independent of $C$**:

$$\texttt{faultComplexDistanceZ}\ (\mathcal R\otimes C) = \ell + 1.$$

**Physical reading**: under the repetition-code foliation the Z-side distance is **purely
temporal** -- $C$ only decides "whether there is a nontrivial fault" (whether $H_0(C)$ is
$0$), not "how many". This is the same law as `faultDistance_timeLike` ($S+1$) of §4.

**The two halves of the proof** (neither takes the gapped route of "explicitly
constructing an element of $\mathrm{im}\,\partial_1$"):

* **Lower bound**: a nontrivial fault $f$ satisfies $f\notin I$, and by the contrapositive
  of the core lemma `koszul_repR_slice_trivial` of §9, its value on **every** time slice
  fails to lie in $\mathrm{im}\,dC_1$ and is therefore nonzero; so the weight is at least
  the number of slices $\ell+1$ (`card_le_hammingNorm_of_slices`).
* **Upper bound**: a proper subspace must miss some unit vector
  (`exists_single_notMem`); spreading it along the time axis gives an undetectable
  nontrivial fault of weight exactly $\ell+1$ (`hammingNorm_liftFault`). -/

omit [Fintype C₀] [Fintype C₁] [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂] in
/-- The weight of `Sum.elim g 0` is the weight of `g` (the right half is identically zero
and contributes no weight). -/
theorem hammingNorm_sumElim_zero {α β : Type*} [Fintype α] [Fintype β]
    (g : α → ZMod 2) :
    hammingNorm (Sum.elim g (0 : β → ZMod 2)) = hammingNorm g := by
  classical
  have h1 : hammingNorm (Sum.elim g (0 : β → ZMod 2))
      = (Finset.univ.filter fun p : α ⊕ β => Sum.elim g 0 p ≠ 0).card := by
    simp [hammingNorm]
  have h2 : hammingNorm g = (Finset.univ.filter fun a : α => g a ≠ 0).card := by
    simp [hammingNorm]
  have hkey : (Finset.univ.filter fun p : α ⊕ β => Sum.elim g 0 p ≠ 0)
      = (Finset.univ.filter fun a : α => g a ≠ 0).image Sum.inl := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      rcases p with a | b
      · exact ⟨a, by simpa using hp, rfl⟩
      · simp at hp
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  rw [h1, h2, hkey, Finset.card_image_of_injective _ Sum.inl_injective]

omit [DecidableEq C₀] [DecidableEq C₁] in
/-- **The weight of a fault spread constantly along the time axis**:
$(n\otimes\mathbf 1,0)$ copies $n$ on every time slice, so the weight is exactly
$(\ell+1)\cdot\mathrm{wt}(n)$. -/
theorem hammingNorm_liftFault (l : ℕ) (n : C₀ → ZMod 2) :
    hammingNorm (liftFault (C₁ := C₁) l n) = (l + 1) * hammingNorm n := by
  classical
  rw [show liftFault (C₁ := C₁) l n
      = Sum.elim (fun p : C₀ × Fin (l + 1) => n p.1) (0 : C₁ × Fin l → ZMod 2) from rfl]
  rw [hammingNorm_sumElim_zero]
  have h1 : hammingNorm (fun p : C₀ × Fin (l + 1) => n p.1)
      = (Finset.univ.filter fun p : C₀ × Fin (l + 1) => n p.1 ≠ 0).card := by
    simp [hammingNorm]
  rw [h1, Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ c : C₀, (∑ _ : Fin (l + 1), (if n c ≠ 0 then 1 else 0))
      = (l + 1) * (if n c ≠ 0 then 1 else 0) := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hinner]
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [hammingNorm, Finset.card_filter]

/-- **Every slice nonzero $\Rightarrow$ weight $\ge$ number of slices**: pick one nonzero
position in each of the $\ell+1$ distinct slices; they are pairwise distinct in the index
space, so the support has at least $\ell+1$ elements. -/
theorem card_le_hammingNorm_of_slices (l : ℕ)
    (x : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2)
    (h : ∀ j : Fin (l + 1), (fun c : C₀ => x (Sum.inl (c, j))) ≠ 0) :
    l + 1 ≤ hammingNorm x := by
  classical
  choose c hc using fun j => Function.ne_iff.mp (h j)
  have hinj : Function.Injective
      (fun j : Fin (l + 1) =>
        (Sum.inl (c j, j) : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l))) := by
    intro j1 j2 h12
    exact (Prod.mk.inj (Sum.inl.inj h12)).2
  have hsub : (Finset.univ.image
        (fun j : Fin (l + 1) =>
          (Sum.inl (c j, j) : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l))))
      ⊆ (Finset.univ.filter fun p => x p ≠ 0) := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc j⟩
  calc l + 1 = (Finset.univ : Finset (Fin (l + 1))).card := by simp
    _ = (Finset.univ.image (fun j : Fin (l + 1) =>
          (Sum.inl (c j, j) : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l)))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (Finset.univ.filter fun p => x p ≠ 0).card := Finset.card_le_card hsub
    _ = hammingNorm x := by simp [hammingNorm]

/-- **A proper subspace must miss some unit vector**: if every unit vector lies in $W$
then $W = \top$ (every vector is a linear combination of unit vectors). This is the source
of "$\mathrm{im}\,dC_1\ne\top$ gives a complementary direction of weight $1$", and the
existence of the upper-bound witness. -/
theorem exists_single_notMem {W : Submodule (ZMod 2) (C₀ → ZMod 2)} (hW : W ≠ ⊤) :
    ∃ c : C₀, (Pi.single c (1 : ZMod 2) : C₀ → ZMod 2) ∉ W := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hW
  rw [Submodule.eq_top_iff']
  intro z
  have hz : z = ∑ c, z c • (Pi.single c (1 : ZMod 2) : C₀ → ZMod 2) := by
    funext d
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro hd
      exact absurd (Finset.mem_univ d) hd
  rw [hz]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h c)

/-- A unit vector has weight $1$. -/
theorem hammingNorm_piSingle (c : C₀) :
    hammingNorm (Pi.single c (1 : ZMod 2) : C₀ → ZMod 2) = 1 := by
  classical
  have hset : (Finset.univ.filter fun d : C₀ =>
        (Pi.single c (1 : ZMod 2) : C₀ → ZMod 2) d ≠ 0) = {c} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hd
      by_contra hne
      exact hd (by rw [Pi.single_eq_of_ne hne])
    · intro hdc
      rw [hdc, Pi.single_eq_same]
      exact one_ne_zero
  rw [hammingNorm, hset, Finset.card_singleton]

/-- The weight set over general $C$. -/
def koszulWeightSet (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) : Set ℕ :=
  {w : ℕ | ∃ f : FaultTerm1 (C₀ × Fin (l + 1)) (C₁ × Fin l) → ZMod 2,
    IsUndetectedLogicalFault
      (fd0 (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00)
      (LinearMap.range (fd1 (koszulFaultComplex (repR l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repR l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repR l) dC1 dC2 hC).d02_01).toLin') f
    ∧ hammingNorm f = w}

/-- **General $C$, repetition-code foliation: with $R\ne0$ the Z-side fault distance is
exactly the number of rounds $+1$** (when $\mathrm{im}\,dC_1\ne\top$, i.e. $H_0(C)\ne0$).

This is the closure of honest boundary 2's "$R\ne0$ still not done" for **arbitrary $C$**:
the same conclusion as the trivial $C$ of §8, but $C$ is no longer trivial. **Independence
of $C$** is the content of this item -- $C$ only decides "whether there is a fault", not
"how many". -/
theorem faultComplexDistanceZ_koszul_repR (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (hne : LinearMap.range dC1.mulVecLin ≠ ⊤) :
    faultComplexDistanceZ (koszulFaultComplex (repR l) dC1 dC2 hC) = l + 1 := by
  have hdef : faultComplexDistanceZ (koszulFaultComplex (repR l) dC1 dC2 hC)
      = sInf (koszulWeightSet l dC1 dC2 hC) := rfl
  obtain ⟨c, hc⟩ := exists_single_notMem hne
  have hw : (l + 1) ∈ koszulWeightSet l dC1 dC2 hC := by
    refine ⟨liftFault l (Pi.single c (1 : ZMod 2)),
      ⟨liftFault_mem_ker l dC1 dC2 hC _, ?_⟩, ?_⟩
    · intro hmem
      have hψ : sliceMod l dC1 (⟨0, Nat.succ_pos l⟩ : Fin (l + 1))
          (liftFault l (Pi.single c (1 : ZMod 2))) ≠ 0 := by
        rw [sliceMod_liftFault, Ne, Submodule.Quotient.mk_eq_zero]
        exact hc
      exact hψ (range_fd1_le_sliceMod_ker l dC1 dC2 hC _ hmem)
    · rw [hammingNorm_liftFault, hammingNorm_piSingle, mul_one]
  rw [hdef]
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun b _ => Nat.zero_le b⟩ hw
  · refine le_csInf ⟨l + 1, hw⟩ ?_
    rintro w ⟨f, hf, rfl⟩
    have hker : f ∈ LinearMap.ker (fd0 (koszulFaultComplex (repR l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repR l) dC1 dC2 hC).d01_00).mulVecLin := hf.1
    refine card_le_hammingNorm_of_slices l f fun j => ?_
    intro hzero
    have hψ0 : sliceMod l dC1 j f = 0 := by
      rw [show sliceMod l dC1 j f
          = Submodule.Quotient.mk (fun c : C₀ => f (Sum.inl (c, j))) from rfl, hzero,
        Submodule.Quotient.mk_zero]
    exact hf.2 (koszul_repR_slice_trivial l dC1 dC2 hC j f hker hψ0)

/-! ## 11. The dual foliation: $R = (\texttt{repR}\ \ell)^{\mathsf T}$

The foliation of §10 is `repR l`: $\ell$ checks and $\ell+1$ time slices. There the Z-side
distance is **purely temporal**, exactly $\ell+1$ and independent of the code $C$. This
section switches the foliation to its **transpose** -- $\ell$ columns, $\ell+1$ rows -- so
that the sizes of the two halves $F_{1,0} = C_0\times\mathrm{Fin}\,\ell$ and
$F_{0,1} = C_1\times\mathrm{Fin}\,(\ell+1)$ are exactly interchanged with those of §10, and
the conclusion flips entirely:

$$\texttt{faultComplexDistanceZ}\ (\mathcal R\otimes C) = d_Z(C),$$

where $d_Z(C)$ is **the code's own Z distance**: the minimum weight of
$\ker dC_1\setminus\operatorname{im}dC_2$ (`codeZWeightSet`). That is, under the transpose
foliation the Z-side distance is **independent of the number of rounds** and the time
direction charges nothing extra. The two sections together say that "which foliation is
used" is a **modeling choice**, not a notational convention.

**The proof is one sentence: sum along time.** Every row of $R$ has exactly two $1$s, so
every column of $R^{\mathsf T}$ sums to $0$; summing $\partial_0 f = 0$ along the time
slices therefore makes the whole $(\mathrm{id}\otimes R^{\mathsf T})$ block vanish:

* **The invariant**: $f\in\ker\partial_0 \Rightarrow s(f) := \sum_i f_{0,1}(\cdot,i)\in
  \ker dC_1$; and $f\in\operatorname{im}\partial_1 \Rightarrow s(f)\in
  \operatorname{im}dC_2$ (each of the two needs only one component reading plus one sum;
  see `koszulRepRDual_dualTimeSum_mem_ker` and
  `koszulRepRDual_dualTimeSum_mem_range`). The second gives the **lower bound**: for a
  nontrivial fault, $s(f)$ lies in $\ker dC_1\setminus\operatorname{im}dC_2$, while
  $\operatorname{wt}(f)\ge\operatorname{wt}(s(f))$ (`hammingNorm_dualTimeSum_le`: the
  support of the sum lies in the image of the original support under the first-component
  projection).
* **Upper bound**: put $w\in\ker dC_1\setminus\operatorname{im}dC_2$ on a **single time
  slice** (`singleSliceFault`); then it is $\partial_0$-silent (the $F_{1,0}$ half being
  $0$), nontrivial (otherwise the previous item would put $w$ in
  $\operatorname{im}dC_2$), and of weight exactly $\operatorname{wt}(w)$.

The two sides' `sInf` are therefore equal, and **no hypothesis is needed**: when
$\ker dC_1\subseteq\operatorname{im}dC_2$ the lower-bound half directly gives
$\ker\partial_0\subseteq\operatorname{im}\partial_1$, both sides being $0$. -/

/-- **The dual foliation**: $R = (\texttt{repR}\ \ell)^{\mathsf T}$ -- $\ell$ columns,
$\ell+1$ rows, exactly opposite to `repR l`. -/
abbrev repRDual (l : ℕ) : Matrix (Fin (l + 1)) (Fin l) (ZMod 2) := (repR l).transpose

/-- **The code $C$'s own Z-side weight set**: the weights of the elements of
$\ker dC_1\setminus\operatorname{im}dC_2$. Its `sInf` is the code's Z distance; when
$\ker dC_1\subseteq\operatorname{im}dC_2$ the set is empty and `sInf` takes $0$, consistent
with the empty-set convention of this library's `faultDistance`. -/
def codeZWeightSet (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2)) : Set ℕ :=
  {w : ℕ | ∃ v : C₁ → ZMod 2,
    v ∈ LinearMap.ker dC1.mulVecLin ∧ v ∉ LinearMap.range dC2.mulVecLin
      ∧ hammingNorm v = w}

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂] in
/-- The membership unfolding of `codeZWeightSet` (the two sides are definitionally equal,
so `Iff.rfl`). -/
theorem mem_codeZWeightSet {dC1 : Matrix C₀ C₁ (ZMod 2)} {dC2 : Matrix C₁ C₂ (ZMod 2)}
    {w : ℕ} :
    w ∈ codeZWeightSet dC1 dC2 ↔ ∃ v : C₁ → ZMod 2,
      v ∈ LinearMap.ker dC1.mulVecLin ∧ v ∉ LinearMap.range dC2.mulVecLin
        ∧ hammingNorm v = w :=
  Iff.rfl

omit [Fintype C₀] [Fintype C₁] [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁]
  [DecidableEq C₂] in
/-- **Every row of `repR l` sums to zero**: each row has exactly two $1$s. Transposed,
this is "$R^{\mathsf T}$'s every column sums to zero" -- the entire source of the invariant
that "summing along time kills the whole $(\mathrm{id}\otimes R^{\mathsf T})$ block" in
this section. -/
theorem repR_row_sum (l : ℕ) (i : Fin l) :
    (∑ k : Fin (l + 1), (repR l) i k) = 0 := by
  have h : (repR l *ᵥ (1 : Fin (l + 1) → ZMod 2)) i = 0 :=
    congrFun (repR_allOnes_mem_ker l) i
  rw [Matrix.mulVec, dotProduct] at h
  simpa only [Pi.one_apply, mul_one, Matrix.row_apply] using h

omit [Fintype C₀] [Fintype C₁] [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁]
  [DecidableEq C₂] in
/-- **Every column of `repRDual l` sums to zero**: the transpose form of `repR_row_sum`,
the same identity (two $1$s per row). The entire source of every invariant in this section
that "summing along time kills $(\mathrm{id}\otimes R^{\mathsf T})$". -/
theorem repRDual_col_sum (l : ℕ) (j : Fin l) :
    (∑ i : Fin (l + 1), (repRDual l) i j) = 0 :=
  (Finset.sum_congr rfl fun i _ => (rfl : (repRDual l) i j = (repR l) j i)).trans
    (repR_row_sum l j)

omit [Fintype C₀] [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂] in
/-- **Sum along time**: the sum of the $F_{0,1} = C_1\times\mathrm{Fin}\,(\ell+1)$ half
along the time direction. It is the only invariant used throughout this section. -/
abbrev dualTimeSum (l : ℕ) (f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2) :
    C₁ → ZMod 2 :=
  fun b => ∑ i : Fin (l + 1), f (Sum.inr (b, i))

/-- **The component reading of $\partial_0$ (dual foliation)**: the left half gives
$(\mathrm{id}\otimes R^{\mathsf T})x$, the right half gives $(dC_1\otimes\mathrm{id})y$. -/
theorem koszulRepRDual_fd0_apply (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2) (a : C₀) (i : Fin (l + 1)) :
    ((fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00) *ᵥ f) (Sum.inl (a, i))
      = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₀ C₀ (ZMod 2)) (repRDual l)) *ᵥ
          (fun p : C₀ × Fin l => f (Sum.inl p))) (a, i)
        + ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
            (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
          (fun q : C₁ × Fin (l + 1) => f (Sum.inr q))) (a, i) := by
  have hd10 : (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₀ C₀ (ZMod 2))
          (repRDual l) := rfl
  have hd01 : (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
          (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2)) := rfl
  simp only [fd0, hd10, hd01, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]

/-- **The component reading of $\partial_1$ (dual foliation, left half)**: the
$F_{1,1}\to F_{1,0}$ block is $dC_1\otimes\mathrm{id}$. -/
theorem koszulRepRDual_fd1_apply_left (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (g : FaultTerm2 (C₁ × Fin l) (C₂ × Fin (l + 1)) → ZMod 2) (c : C₀) (j : Fin l) :
    ((fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01) *ᵥ g) (Sum.inl (c, j))
      = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
            (1 : Matrix (Fin l) (Fin l) (ZMod 2))) *ᵥ
          (fun p : C₁ × Fin l => g (Sum.inl p))) (c, j) := by
  have hd11 : (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
          (1 : Matrix (Fin l) (Fin l) (ZMod 2)) := rfl
  simp only [fd1, hd11, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- **The component reading of $\partial_1$ (dual foliation, right half)**: the
$F_{1,1}\to F_{0,1}$ block is the off-diagonal $\mathrm{id}\otimes R^{\mathsf T}$, and
$F_{0,2}\to F_{0,1}$ is $dC_2\otimes\mathrm{id}$. -/
theorem koszulRepRDual_fd1_apply_right (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (g : FaultTerm2 (C₁ × Fin l) (C₂ × Fin (l + 1)) → ZMod 2) (b : C₁) (i : Fin (l + 1)) :
    ((fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01) *ᵥ g) (Sum.inr (b, i))
      = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₁ C₁ (ZMod 2)) (repRDual l)) *ᵥ
          (fun p : C₁ × Fin l => g (Sum.inl p))) (b, i)
        + ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC2
            (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
          (fun q : C₂ × Fin (l + 1) => g (Sum.inr q))) (b, i) := by
  have hd11 : (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₁ C₁ (ZMod 2))
          (repRDual l) := rfl
  have hd02 : (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01
      = Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC2
          (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2)) := rfl
  simp only [fd1, hd11, hd02, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

omit [Fintype C₁] [Fintype C₂] [DecidableEq C₁] [DecidableEq C₂] in
/-- **The sum of $(\mathrm{id}\otimes R^{\mathsf T})x$ along time is zero**: every column
of $R^{\mathsf T}$ sums to $0$ (the transpose form of `repR_row_sum`). This is the
technical core of every cancellation in this section. -/
theorem koszulRepRDual_timeSum_kron_one (l : ℕ) (x : C₀ × Fin l → ZMod 2) (a : C₀) :
    (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
        (1 : Matrix C₀ C₀ (ZMod 2)) (repRDual l)) *ᵥ x) (a, i)) = 0 := by
  classical
  have hstep : ∀ i : Fin (l + 1),
      ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₀ C₀ (ZMod 2))
        (repRDual l)) *ᵥ x) (a, i) = ∑ j : Fin l, (repRDual l) i j * x (a, j) := by
    intro i
    rw [kroneckerMap_one_left_mulVec_apply]
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show (∑ i : Fin (l + 1), (repRDual l) i j * x (a, j))
      = (∑ i : Fin (l + 1), (repRDual l) i j) * x (a, j) from
    (Finset.sum_mul Finset.univ (fun i : Fin (l + 1) => (repRDual l) i j) (x (a, j))).symm,
    repRDual_col_sum, zero_mul]

omit [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂] in
/-- **The sum of $(A\otimes\mathrm{id})y$ along time**: it equals $A$ acting on the
**slicewise sum**. -/
theorem timeSum_kroneckerMap_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix C₀ C₁ (ZMod 2)) (y : C₁ × κ → ZMod 2) (a : C₀) :
    (∑ i : κ, ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) A
        (1 : Matrix κ κ (ZMod 2))) *ᵥ y) (a, i))
      = (A *ᵥ (fun b : C₁ => ∑ i : κ, y (b, i))) a := by
  classical
  have hstep : ∀ i : κ,
      ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) A
        (1 : Matrix κ κ (ZMod 2))) *ᵥ y) (a, i) = ∑ b : C₁, A a b * y (b, i) := by
    intro i
    rw [kroneckerMap_one_mulVec_apply]
  simp only [hstep]
  rw [Finset.sum_comm, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (Finset.mul_sum Finset.univ (fun i : κ => y (b, i)) (A a b)).symm

/-- **The invariant (kernel)**: $f$ sent to zero by $\partial_0$ $\Rightarrow$ its sum
along time lies in $\ker dC_1$. -/
theorem koszulRepRDual_dualTimeSum_mem_ker (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2)
    (hf : f ∈ LinearMap.ker (fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00).toLin') :
    dualTimeSum l f ∈ LinearMap.ker dC1.mulVecLin := by
  classical
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hf0 : (fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
      (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00) *ᵥ f = 0 := by
    have h := LinearMap.mem_ker.mp hf
    rwa [Matrix.toLin'_apply] at h
  funext a
  have hsum : (∑ i : Fin (l + 1),
      ((fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00) *ᵥ f)
        (Sum.inl (a, i))) = 0 := by
    rw [hf0]
    simp
  have hsplit : (∑ i : Fin (l + 1),
      ((fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00) *ᵥ f)
        (Sum.inl (a, i)))
      = (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₀ C₀ (ZMod 2)) (repRDual l)) *ᵥ
            (fun p : C₀ × Fin l => f (Sum.inl p))) (a, i))
        + (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
            (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
            (fun q : C₁ × Fin (l + 1) => f (Sum.inr q))) (a, i)) :=
    (Finset.sum_congr rfl fun i _ => koszulRepRDual_fd0_apply l dC1 dC2 hC f a i).trans
      Finset.sum_add_distrib
  rw [hsplit, koszulRepRDual_timeSum_kron_one,
    timeSum_kroneckerMap_one dC1 (fun q : C₁ × Fin (l + 1) => f (Sum.inr q)) a,
    zero_add] at hsum
  simpa using hsum

/-- **The invariant (image)**: $f$ in the image of $\partial_1$ $\Rightarrow$ its sum
along time lies in $\operatorname{im}dC_2$. This is the entire source of the **lower
bound**. -/
theorem koszulRepRDual_dualTimeSum_mem_range (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2)
    (hf : f ∈ LinearMap.range (fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01).toLin') :
    dualTimeSum l f ∈ LinearMap.range dC2.mulVecLin := by
  classical
  obtain ⟨g, hg⟩ := hf
  rw [Matrix.toLin'_apply] at hg
  refine ⟨fun c : C₂ => ∑ i : Fin (l + 1), g (Sum.inr (c, i)), ?_⟩
  rw [Matrix.mulVecLin_apply]
  funext b
  have hb : dualTimeSum l f b
      = ∑ i : Fin (l + 1), ((fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
          (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
          (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01) *ᵥ g) (Sum.inr (b, i)) := by
    show (∑ i : Fin (l + 1), f (Sum.inr (b, i))) = _
    exact Finset.sum_congr rfl fun i _ => by rw [hg]
  have hsplit : (∑ i : Fin (l + 1), ((fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01) *ᵥ g) (Sum.inr (b, i)))
      = (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₁ C₁ (ZMod 2)) (repRDual l)) *ᵥ
            (fun p : C₁ × Fin l => g (Sum.inl p))) (b, i))
        + (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC2
            (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
            (fun q : C₂ × Fin (l + 1) => g (Sum.inr q))) (b, i)) :=
    (Finset.sum_congr rfl fun i _ => koszulRepRDual_fd1_apply_right l dC1 dC2 hC g b i).trans
      Finset.sum_add_distrib
  rw [hb, hsplit, koszulRepRDual_timeSum_kron_one,
    timeSum_kroneckerMap_one dC2 (fun q : C₂ × Fin (l + 1) => g (Sum.inr q)) b, zero_add]

/-- **The upper-bound witness**: put $w$ on a **single time slice** $i_0$ and take $0$ on
the $F_{1,0}$ half. -/
def singleSliceFault (l : ℕ) (w : C₁ → ZMod 2) (i₀ : Fin (l + 1)) :
    FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun q => if q.2 = i₀ then w q.1 else 0)

omit [Fintype C₀] [Fintype C₁] [DecidableEq C₀] [DecidableEq C₁] in
/-- The equational lemma for `singleSliceFault` on the $F_{1,0}$ half. -/
theorem singleSliceFault_inl (l : ℕ) (w : C₁ → ZMod 2) (i₀ : Fin (l + 1))
    (p : C₀ × Fin l) : singleSliceFault (C₀ := C₀) l w i₀ (Sum.inl p) = 0 := rfl

omit [Fintype C₀] [Fintype C₁] [DecidableEq C₀] [DecidableEq C₁] in
/-- The equational lemma for `singleSliceFault` on the $F_{0,1}$ half. -/
theorem singleSliceFault_inr (l : ℕ) (w : C₁ → ZMod 2) (i₀ : Fin (l + 1)) (b : C₁)
    (i : Fin (l + 1)) :
    singleSliceFault (C₀ := C₀) l w i₀ (Sum.inr (b, i)) = if i = i₀ then w b else 0 := rfl

omit [Fintype C₀] [Fintype C₁] [DecidableEq C₀] [DecidableEq C₁] in
/-- **Summing along time reads it back as $w$**. -/
theorem dualTimeSum_singleSliceFault (l : ℕ) (w : C₁ → ZMod 2) (i₀ : Fin (l + 1)) :
    dualTimeSum l (singleSliceFault (C₀ := C₀) l w i₀) = w := by
  funext b
  show (∑ i : Fin (l + 1),
      singleSliceFault (C₀ := C₀) l w i₀ (Sum.inr (b, i))) = w b
  rw [Finset.sum_congr rfl fun i _ => singleSliceFault_inr l w i₀ b i,
    Finset.sum_ite_eq' Finset.univ i₀ (fun _ : Fin (l + 1) => w b),
    ite_eq_left (Finset.mem_univ i₀)]

/-- **The weight of the witness**: the support is exactly the image of $\{b : w_b\ne 0\}$
under $b\mapsto (b,i_0)$, so the weight is $\operatorname{wt}(w)$. -/
theorem hammingNorm_singleSliceFault (l : ℕ) (w : C₁ → ZMod 2) (i₀ : Fin (l + 1)) :
    hammingNorm (singleSliceFault (C₀ := C₀) l w i₀) = hammingNorm w := by
  classical
  have h1 : hammingNorm (singleSliceFault (C₀ := C₀) l w i₀)
      = (Finset.univ.filter fun p : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) =>
          singleSliceFault (C₀ := C₀) l w i₀ p ≠ 0).card := rfl
  have h2 : hammingNorm w = (Finset.univ.filter fun b : C₁ => w b ≠ 0).card := rfl
  have hset : (Finset.univ.filter fun p : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) =>
        singleSliceFault (C₀ := C₀) l w i₀ p ≠ 0)
      = (Finset.univ.filter fun b : C₁ => w b ≠ 0).image (fun b => Sum.inr (b, i₀)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      rcases p with q | q
      · exact absurd (singleSliceFault_inl l w i₀ q) hp
      · obtain ⟨b, i⟩ := q
        rw [singleSliceFault_inr] at hp
        by_cases hi : i = i₀
        · subst hi
          rw [ite_eq_left rfl] at hp
          exact ⟨b, hp, rfl⟩
        · rw [ite_eq_right hi] at hp
          exact absurd rfl hp
    · rintro ⟨b, hb, rfl⟩
      rw [singleSliceFault_inr, ite_eq_left rfl]
      exact hb
  have hinj : Function.Injective (fun b : C₁ =>
      (Sum.inr (b, i₀) : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)))) :=
    fun b₁ b₂ h => congrArg Prod.fst (Sum.inr_injective h)
  rw [h1, h2, hset, Finset.card_image_of_injective _ hinj]

/-- **The witness is $\partial_0$-silent**: the $F_{1,0}$ half is $0$, the $F_{0,1}$ half
is nonzero only on the slice $i_0$, where it takes the value $w$; and $w\in\ker dC_1$. -/
theorem singleSliceFault_mem_ker (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (w : C₁ → ZMod 2)
    (i₀ : Fin (l + 1)) (hw : w ∈ LinearMap.ker dC1.mulVecLin) :
    singleSliceFault (C₀ := C₀) l w i₀ ∈ LinearMap.ker
      (fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00).toLin' := by
  classical
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  funext r
  rcases r with ⟨a, i⟩ | q
  · rw [Pi.zero_apply, koszulRepRDual_fd0_apply]
    have hx0 : (fun p : C₀ × Fin l => singleSliceFault (C₀ := C₀) l w i₀ (Sum.inl p)) = 0 :=
      funext fun p => singleSliceFault_inl l w i₀ p
    rw [hx0, Matrix.mulVec_zero, Pi.zero_apply, zero_add,
      kroneckerMap_one_mulVec_apply]
    simp only [singleSliceFault_inr]
    have hw0 : (dC1 *ᵥ w) a = 0 := by
      have h : dC1.mulVecLin w = 0 := LinearMap.mem_ker.mp hw
      rw [Matrix.mulVecLin_apply] at h
      exact congrFun h a
    by_cases hi : i = i₀
    · have hsum : (∑ j : C₁, dC1 a j * (if i = i₀ then w j else 0))
          = ∑ j : C₁, dC1 a j * w j :=
        Finset.sum_congr rfl fun j _ => by rw [ite_eq_left hi]
      have h : (∑ j : C₁, dC1 a j * w j) = (dC1 *ᵥ w) a :=
        Finset.sum_congr rfl fun b _ => rfl
      rw [hsum, h, hw0]
    · have hsum : (∑ j : C₁, dC1 a j * (if i = i₀ then w j else 0)) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [ite_eq_right hi, mul_zero]
      rw [hsum]
  · exact Fin.elim0 q

/-- **The witness is nontrivial**: if it were in the image of $\partial_1$, then by the
invariant $w\in\operatorname{im}dC_2$. -/
theorem singleSliceFault_notMem_range (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (w : C₁ → ZMod 2)
    (i₀ : Fin (l + 1)) (hw : w ∉ LinearMap.range dC2.mulVecLin) :
    singleSliceFault (C₀ := C₀) l w i₀ ∉ LinearMap.range
      (fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01).toLin' := by
  intro hmem
  exact hw (by
    have h := koszulRepRDual_dualTimeSum_mem_range l dC1 dC2 hC _ hmem
    rwa [dualTimeSum_singleSliceFault] at h)

omit [DecidableEq C₀] [DecidableEq C₁] [DecidableEq C₂] in
/-- **The weight side of the lower bound**: the support of the sum along time lies in the
image of the original support under the first-component projection, so
$\operatorname{wt}(s(f))\le\operatorname{wt}(f)$. -/
theorem hammingNorm_dualTimeSum_le (l : ℕ)
    (f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2) :
    hammingNorm (dualTimeSum l f) ≤ hammingNorm f := by
  classical
  let g : C₁ → FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) := fun b =>
    Sum.inr (b, if h : ∃ i : Fin (l + 1), f (Sum.inr (b, i)) ≠ 0
      then Classical.choose h else 0)
  have hginj : Function.Injective g := fun b₁ b₂ h =>
    congrArg Prod.fst (Sum.inr_injective h)
  have hmem : ∀ b ∈ Finset.univ.filter (fun b : C₁ => dualTimeSum l f b ≠ 0),
      f (g b) ≠ 0 := by
    intro b hb
    have hb' : dualTimeSum l f b ≠ 0 := (Finset.mem_filter.mp hb).2
    have hex : ∃ i : Fin (l + 1), f (Sum.inr (b, i)) ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hb' (by simp [dualTimeSum, h])
    have hval : g b = Sum.inr (b, Classical.choose hex) := by
      simp only [g]
      rw [dite_eq_left hex]
    rw [hval]
    exact Classical.choose_spec hex
  have hsub : (Finset.univ.filter (fun b : C₁ => dualTimeSum l f b ≠ 0)).image g
      ⊆ (Finset.univ.filter fun p : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) =>
          f p ≠ 0) := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem b hb⟩
  have h1 : hammingNorm (dualTimeSum l f)
      = (Finset.univ.filter fun b : C₁ => dualTimeSum l f b ≠ 0).card := rfl
  have h2 : hammingNorm f
      = (Finset.univ.filter fun p : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) =>
          f p ≠ 0).card := rfl
  rw [h1, h2]
  calc (Finset.univ.filter fun b : C₁ => dualTimeSum l f b ≠ 0).card
      = ((Finset.univ.filter fun b : C₁ => dualTimeSum l f b ≠ 0).image g).card :=
        (Finset.card_image_of_injective _ hginj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### 11.1 Even-weight vectors are exactly the image of $R^{\mathsf T}$

The hard half of the lower bound
(`koszulRepRDual_mem_range_of_dualTimeSum_mem_range`) must solve an equation: given
$y\in F_{0,1}$ with **the time series of every coordinate of even weight**, find $a$ with
$(\mathrm{id}\otimes R^{\mathsf T})a = y$. This step is equivalent to "the image of
$R^{\mathsf T}$ = the even-weight subspace", and this subsection machine-checks it. -/

/-- The coordinate-sum functional $\sigma(v) = \sum_i v_i$. -/
def sumLin (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, v i
  map_add' v w := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

/-- $\sigma$ is surjective. -/
theorem sumLin_surjective (n : ℕ) : Function.Surjective (sumLin (n + 1)) := by
  intro y
  refine ⟨fun i : Fin (n + 1) => if i = 0 then y else 0, ?_⟩
  show (∑ i : Fin (n + 1), (if i = 0 then y else 0)) = y
  rw [Finset.sum_ite_eq' Finset.univ 0 (fun _ : Fin (n + 1) => y),
    ite_eq_left (Finset.mem_univ 0)]

/-- $\dim\ker\sigma = n$: rank-nullity plus the surjectivity of $\sigma$. -/
theorem finrank_ker_sumLin (n : ℕ) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (sumLin (n + 1))) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumLin (n + 1))
  have htop : LinearMap.range (sumLin (n + 1)) = ⊤ :=
    LinearMap.range_eq_top.mpr (sumLin_surjective n)
  rw [htop] at h
  have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) (ZMod 2)) = 1 :=
    (Submodule.topEquiv (R := ZMod 2)).finrank_eq.trans (Module.finrank_self (ZMod 2))
  have h2 : Module.finrank (ZMod 2) (Fin (n + 1) → ZMod 2) = n + 1 :=
    Module.finrank_fin_fun (ZMod 2)
  rw [h1, h2] at h
  omega

/-- **The image of $(\texttt{repR}\ \ell)^{\mathsf T}$ is exactly the even-weight
subspace**: the zero column sums give $\subseteq$; both sides have dimension $\ell$, hence
equality. -/
theorem repRDual_range_eq_ker_sumLin (l : ℕ) :
    LinearMap.range (repRDual l).mulVecLin = LinearMap.ker (sumLin (l + 1)) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro v ⟨A, rfl⟩
    show (∑ i : Fin (l + 1), ((repRDual l) *ᵥ A) i) = 0
    have hstep : ∀ i : Fin (l + 1),
        ((repRDual l) *ᵥ A) i = ∑ j : Fin l, (repRDual l) i j * A j := by
      intro i
      rw [Matrix.mulVec, dotProduct]
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show (∑ i : Fin (l + 1), (repRDual l) i j * A j)
        = (∑ i : Fin (l + 1), (repRDual l) i j) * A j from
      (Finset.sum_mul Finset.univ (fun i : Fin (l + 1) => (repRDual l) i j) (A j)).symm,
      repRDual_col_sum, zero_mul]
  · have h1 : Module.finrank (ZMod 2) ↥(LinearMap.range (repRDual l).mulVecLin) = l := by
      have h := matRank_transpose (repR l)
      rw [repR_matRank] at h
      exact h
    rw [h1, finrank_ker_sumLin l]

/-- **Every coordinatewise even-weight $y$ is hit by $(\mathrm{id}\otimes R^{\mathsf
T})$**: solve $R^{\mathsf T}A_b = Y_b$ coordinate by coordinate (existence from the
previous item), then verify entrywise. -/
theorem exists_kron_one_left_mulVec_eq_of_even (l : ℕ) (y : C₁ × Fin (l + 1) → ZMod 2)
    (hy : ∀ b : C₁, (∑ i : Fin (l + 1), y (b, i)) = 0) :
    ∃ a : C₁ × Fin l → ZMod 2,
      (Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₁ C₁ (ZMod 2))
        (repRDual l)) *ᵥ a = y := by
  classical
  have hb : ∀ b : C₁,
      (fun i : Fin (l + 1) => y (b, i)) ∈ LinearMap.range (repRDual l).mulVecLin := fun b => by
    rw [repRDual_range_eq_ker_sumLin]
    exact hy b
  choose A hA using hb
  refine ⟨fun q => A q.1 q.2, ?_⟩
  funext q
  obtain ⟨b, i⟩ := q
  rw [kroneckerMap_one_left_mulVec_apply]
  have h := congrFun (hA b) i
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h
  simpa only [] using h

/-! ### 11.2 The hard half of the lower bound

Two facts complete the lower bound: **the single-time-slice $F_{0,2}$ element sends the
time average onto $dC_2\beta$** (`dualTimeSum_fd1_singleSliceZ`), so the time average of
the remainder is zero and the time series of every coordinate becomes an even-weight
vector; the previous item then solves the $F_{1,1}$ half coordinate by coordinate, and the
equation $\partial_0$ together with the injectivity of $R^{\mathsf T}$ pins down the
$F_{1,0}$ half. -/

/-- **The single-time-slice $F_{0,2}$ element**: the $F_{1,1}$ half is $0$ and the $F_{0,2}$
half puts $\beta$ on the slice $i_0$ -- verbatim the same shape as `singleSliceFault` but
with the target space replaced by $F_2$. -/
def singleSliceZ (l : ℕ) (β : C₂ → ZMod 2) (i₀ : Fin (l + 1)) :
    FaultTerm2 (C₁ × Fin l) (C₂ × Fin (l + 1)) → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun q => if q.2 = i₀ then β q.1 else 0)

omit [Fintype C₁] [Fintype C₂] [DecidableEq C₁] [DecidableEq C₂] in
/-- The equational lemma for `singleSliceZ` on the $F_{1,1}$ half. -/
theorem singleSliceZ_inl (l : ℕ) (β : C₂ → ZMod 2) (i₀ : Fin (l + 1)) (p : C₁ × Fin l) :
    singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inl p) = 0 := rfl

omit [Fintype C₁] [Fintype C₂] [DecidableEq C₁] [DecidableEq C₂] in
/-- The equational lemma for `singleSliceZ` on the $F_{0,2}$ half. -/
theorem singleSliceZ_inr (l : ℕ) (β : C₂ → ZMod 2) (i₀ : Fin (l + 1)) (c : C₂)
    (i : Fin (l + 1)) :
    singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inr (c, i))
      = if i = i₀ then β c else 0 := rfl

omit [Fintype C₀] [Fintype C₁] [Fintype C₂] [DecidableEq C₀] [DecidableEq C₁]
  [DecidableEq C₂] in
/-- The time average of the $F_{0,2}$ half is exactly $\beta$. -/
theorem timeSum_singleSliceZ (l : ℕ) (β : C₂ → ZMod 2) (i₀ : Fin (l + 1)) :
    (fun c : C₂ => ∑ i : Fin (l + 1),
      singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inr (c, i))) = β := by
  funext c
  rw [Finset.sum_congr rfl fun i _ => singleSliceZ_inr (C₁ := C₁) l β i₀ c i,
    Finset.sum_ite_eq' Finset.univ i₀ (fun _ : Fin (l + 1) => β c),
    ite_eq_left (Finset.mem_univ i₀)]

/-- **The time average of a single-time-slice element of $\partial_1$**: the whole
$F_{1,1}$ half vanishes (`koszulRepRDual_timeSum_kron_one` with $C_1$), and the $F_{0,2}$
half gives $dC_2\beta$. -/
theorem dualTimeSum_fd1_singleSliceZ (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) (β : C₂ → ZMod 2)
    (i₀ : Fin (l + 1)) :
    dualTimeSum l ((fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01) *ᵥ
          singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀)
      = dC2 *ᵥ β := by
  classical
  funext b
  have hsplit : dualTimeSum l ((fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01) *ᵥ
          singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀) b
      = (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₁ C₁ (ZMod 2)) (repRDual l)) *ᵥ
            (fun p : C₁ × Fin l =>
              singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inl p))) (b, i))
        + (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC2
            (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
            (fun q : C₂ × Fin (l + 1) =>
              singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inr q))) (b, i)) :=
    (Finset.sum_congr rfl fun i _ =>
      koszulRepRDual_fd1_apply_right l dC1 dC2 hC _ b i).trans Finset.sum_add_distrib
  have hzero : (∑ i : Fin (l + 1), ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
        (1 : Matrix C₁ C₁ (ZMod 2)) (repRDual l)) *ᵥ
        (fun p : C₁ × Fin l =>
          singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inl p))) (b, i)) = 0 :=
    koszulRepRDual_timeSum_kron_one (C₀ := C₁) l
      (fun p : C₁ × Fin l =>
        singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inl p)) b
  have hstep : ∀ i : Fin (l + 1),
      ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC2
        (1 : Matrix (Fin (l + 1)) (Fin (l + 1)) (ZMod 2))) *ᵥ
        (fun q : C₂ × Fin (l + 1) =>
          singleSliceZ (C₁ := C₁) (C₂ := C₂) l β i₀ (Sum.inr q))) (b, i)
      = ∑ c : C₂, dC2 b c * (if i = i₀ then β c else 0) := by
    intro i
    rw [kroneckerMap_one_mulVec_apply]
    simp only [singleSliceZ_inr]
  rw [hsplit, hzero, zero_add]
  simp only [hstep]
  rw [Finset.sum_comm, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (∑ i : Fin (l + 1), dC2 b c * (if i = i₀ then β c else 0))
      = dC2 b c * (∑ i : Fin (l + 1), if i = i₀ then β c else 0) from
    (Finset.mul_sum Finset.univ (fun i : Fin (l + 1) => if i = i₀ then β c else 0)
      (dC2 b c)).symm,
    Finset.sum_ite_eq' Finset.univ i₀ (fun _ : Fin (l + 1) => β c),
    ite_eq_left (Finset.mem_univ i₀)]

/-- The $\partial_1$ used repeatedly in §11. An `abbrev`: its unfolding is the verbatim
`fd1` expression, so every statement matches the inline form word for word. -/
abbrev dualDel (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    Matrix (FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)))
      (FaultTerm2 (C₁ × Fin l) (C₂ × Fin (l + 1))) (ZMod 2) :=
  fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
    (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
    (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01

/-- Likewise: that $\partial_0$. -/
abbrev dualFd0 (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) :
    Matrix (FaultTerm0 (C₀ × Fin (l + 1)))
      (FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1))) (ZMod 2) :=
  fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
    (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00

/-- **The hard half of the lower bound**: $\partial_0 f = 0$ and the sum along time lying
in $\operatorname{im}dC_2$ $\Rightarrow f\in\operatorname{im}\partial_1$.

The construction is explicit: first use the single-time-slice $F_{0,2}$ element of
$\partial_1$ to subtract $dC_2\beta$ from $s(f)$; the remainder $F$ then has zero time
average and the time series of every coordinate becomes an even-weight vector, so
`exists_kron_one_left_mulVec_eq_of_even` solves the $F_{1,1}$ half coordinate by
coordinate; finally the equation $\partial_0 F = 0$ together with the injectivity of
$R^{\mathsf T}$ guarantees that what was solved is exactly the $F_{1,0}$ half. -/
theorem koszulRepRDual_mem_range_of_dualTimeSum_mem_range (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0)
    (f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2)
    (hf : f ∈ LinearMap.ker (fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00).toLin')
    (hs : dualTimeSum l f ∈ LinearMap.range dC2.mulVecLin) :
    f ∈ LinearMap.range (fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01).toLin' := by
  classical
  obtain ⟨β, hβ⟩ := hs
  rw [Matrix.mulVecLin_apply] at hβ
  set e₀ : Fin (l + 1) := ⟨0, Nat.succ_pos l⟩ with he₀
  set zβ : FaultTerm2 (C₁ × Fin l) (C₂ × Fin (l + 1)) → ZMod 2 :=
    singleSliceZ (C₁ := C₁) (C₂ := C₂) l β e₀ with hzβ
  set F : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2 :=
    f - dualDel l dC1 dC2 hC *ᵥ zβ with hF
  -- (1) $F$ is still sent to zero by $\partial_0$ ($K$ is a subspace)
  have hFker : F ∈ LinearMap.ker (dualFd0 l dC1 dC2 hC).toLin' := by
    rw [hF]
    exact Submodule.sub_mem _ hf
      (range_fd1_le_ker_fd0 _ ⟨zβ, rfl⟩)
  -- (2) the time average of $F$ is zero
  have hF0 : dualTimeSum l F = 0 := by
    have hsub : dualTimeSum l F
        = dualTimeSum l f - dualTimeSum l (dualDel l dC1 dC2 hC *ᵥ zβ) := by
      funext b
      simp only [hF, dualTimeSum, Pi.sub_apply, Finset.sum_sub_distrib]
    have h2 : dualTimeSum l (dualDel l dC1 dC2 hC *ᵥ zβ) = dC2 *ᵥ β := by
      rw [hzβ]
      exact dualTimeSum_fd1_singleSliceZ l dC1 dC2 hC β e₀
    rw [hsub, h2, hβ, sub_self]
  -- (3) solve the $F_{1,1}$ half coordinate by coordinate
  obtain ⟨a, ha⟩ := exists_kron_one_left_mulVec_eq_of_even (C₁ := C₁) l
    (fun q : C₁ × Fin (l + 1) => F (Sum.inr q)) (fun b => by
      have h := congrFun hF0 b
      simpa using h)
  -- (4) pin down the $F_{1,0}$ half from $\partial_0 F = 0$
  have hrow : ∀ c : C₀, (fun j : Fin l =>
        ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
          (1 : Matrix (Fin l) (Fin l) (ZMod 2))) *ᵥ a) (c, j))
      = fun j : Fin l => F (Sum.inl (c, j)) := by
    intro c
    apply repR_transpose_injective l
    funext i
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    have hentry : ∀ b : C₁,
        ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₁ C₁ (ZMod 2))
          (repRDual l)) *ᵥ a) (b, i) = F (Sum.inr (b, i)) :=
      fun b => congrFun ha (b, i)
    have hLHS : ((repRDual l) *ᵥ (fun j : Fin l =>
          ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) dC1
            (1 : Matrix (Fin l) (Fin l) (ZMod 2))) *ᵥ a) (c, j))) i
        = ∑ b : C₁, dC1 c b * ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b)
            (1 : Matrix C₁ C₁ (ZMod 2)) (repRDual l)) *ᵥ a) (b, i) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [kroneckerMap_one_mulVec_apply]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [kroneckerMap_one_left_mulVec_apply (repRDual l) a b i]
      simp_rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hker1 : ((dualFd0 l dC1 dC2 hC) *ᵥ F) (Sum.inl (c, i)) = 0 := by
      have h := LinearMap.mem_ker.mp hFker
      rw [Matrix.toLin'_apply] at h
      exact congrFun h (Sum.inl (c, i))
    rw [koszulRepRDual_fd0_apply, kroneckerMap_one_left_mulVec_apply,
      kroneckerMap_one_mulVec_apply] at hker1
    have hR : ((repRDual l) *ᵥ (fun j : Fin l => F (Sum.inl (c, j)))) i
        = ∑ b : C₁, dC1 c b * F (Sum.inr (b, i)) := by
      have h1 : ((repRDual l) *ᵥ (fun j : Fin l => F (Sum.inl (c, j)))) i
          = ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₀ C₀ (ZMod 2))
              (repRDual l)) *ᵥ (fun p : C₀ × Fin l => F (Sum.inl p))) (c, i) :=
        (kroneckerMap_one_left_mulVec_apply (repRDual l)
          (fun p : C₀ × Fin l => F (Sum.inl p)) c i).symm
      rw [h1, kroneckerMap_one_left_mulVec_apply]
      exact (add_eq_zero_iff_eq _ _).mp hker1
    have hentry' : ∀ b : C₁,
        ((Matrix.kroneckerMap (fun a b : ZMod 2 => a * b) (1 : Matrix C₁ C₁ (ZMod 2))
          (repRDual l)) *ᵥ a) (b, i) = F (Sum.inr (b, i)) := fun b => hentry b
    rw [hLHS]
    simp only [hentry']
    exact hR.symm
  -- (5) put it together: $F = \partial_1(a \oplus 0)$, while
  -- $f = F + \partial_1(0\oplus\beta\otimes e_0)$
  have ha_inl : (fun p : C₁ × Fin l =>
      Sum.elim a (0 : C₂ × Fin (l + 1) → ZMod 2) (Sum.inl p)) = a :=
    funext fun p => rfl
  have hz : (fun q : C₂ × Fin (l + 1) =>
      Sum.elim a (0 : C₂ × Fin (l + 1) → ZMod 2) (Sum.inr q)) = 0 :=
    funext fun q => rfl
  have hFa : F = dualDel l dC1 dC2 hC *ᵥ Sum.elim a (0 : C₂ × Fin (l + 1) → ZMod 2) := by
    funext r
    rcases r with ⟨c, j⟩ | ⟨b, i⟩
    · rw [koszulRepRDual_fd1_apply_left, ha_inl]
      exact (congrFun (hrow c) j).symm
    · rw [koszulRepRDual_fd1_apply_right, hz, Matrix.mulVec_zero, Pi.zero_apply, add_zero,
        ha_inl]
      exact (congrFun ha (b, i)).symm
  refine ⟨Sum.elim a (0 : C₂ × Fin (l + 1) → ZMod 2) + zβ, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.mulVec_add, ← hFa, hF]
  exact sub_add_cancel f (dualDel l dC1 dC2 hC *ᵥ zβ)

/-- The weight set of the faults on the §11 side (the same shape as
`koszulTimeLikeWeightSet` of §8 and `koszulWeightSet` of §10). -/
def repRDualWeightSet (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2)) (dC2 : Matrix C₁ C₂ (ZMod 2))
    (hC : dC1 * dC2 = 0) : Set ℕ :=
  {w : ℕ | ∃ f : FaultTerm1 (C₀ × Fin l) (C₁ × Fin (l + 1)) → ZMod 2,
    IsUndetectedLogicalFault
      (fd0 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d10_00
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d01_00)
      (LinearMap.range (fd1 (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_10
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d11_01
        (koszulFaultComplex (repRDual l) dC1 dC2 hC).d02_01).toLin') f
    ∧ hammingNorm f = w}

/-- **Under the dual foliation ($R = (\texttt{repR}\ \ell)^{\mathsf T}$), with $R\ne 0$
the Z-side fault distance is exactly the code $C$'s own Z distance** -- the minimum weight
of $\ker dC_1\setminus\operatorname{im}dC_2$, **independent of the number of rounds
$\ell$**.

The conclusion is **entirely flipped** relative to `faultComplexDistanceZ_koszul_repR` of
§10 ($R = \texttt{repR}\ \ell$: distance exactly $\ell+1$, independent of $C$): together
the two say that "which foliation is used" is a **modeling choice**, not a notational
convention. This theorem has **no hypothesis** -- when
$\ker dC_1\subseteq\operatorname{im}dC_2$ both sides are $0$. -/
theorem faultComplexDistanceZ_koszul_repRDual (l : ℕ) (dC1 : Matrix C₀ C₁ (ZMod 2))
    (dC2 : Matrix C₁ C₂ (ZMod 2)) (hC : dC1 * dC2 = 0) :
    faultComplexDistanceZ (koszulFaultComplex (repRDual l) dC1 dC2 hC)
      = sInf (codeZWeightSet dC1 dC2) := by
  classical
  have hdef : faultComplexDistanceZ (koszulFaultComplex (repRDual l) dC1 dC2 hC)
      = sInf (repRDualWeightSet l dC1 dC2 hC) := rfl
  rw [hdef]
  have hsub : codeZWeightSet dC1 dC2 ⊆ repRDualWeightSet l dC1 dC2 hC := by
    intro w hw
    obtain ⟨v, hvker, hvrange, rfl⟩ := mem_codeZWeightSet.mp hw
    refine ⟨singleSliceFault (C₀ := C₀) l v ⟨0, Nat.succ_pos l⟩,
      ⟨singleSliceFault_mem_ker l dC1 dC2 hC v _ hvker, ?_⟩,
      hammingNorm_singleSliceFault l v _⟩
    exact fun hmem => singleSliceFault_notMem_range l dC1 dC2 hC v _ hvrange hmem
  have hge : ∀ w ∈ repRDualWeightSet l dC1 dC2 hC,
      sInf (codeZWeightSet dC1 dC2) ≤ w := by
    rintro w ⟨f, hf, rfl⟩
    have hs : dualTimeSum l f ∈ LinearMap.ker dC1.mulVecLin :=
      koszulRepRDual_dualTimeSum_mem_ker l dC1 dC2 hC f hf.1
    have hsr : dualTimeSum l f ∉ LinearMap.range dC2.mulVecLin := fun hmem =>
      hf.2 (koszulRepRDual_mem_range_of_dualTimeSum_mem_range l dC1 dC2 hC f hf.1 hmem)
    exact le_trans (csInf_le ⟨0, fun c _ => Nat.zero_le c⟩
      (mem_codeZWeightSet.mpr ⟨dualTimeSum l f, hs, hsr, rfl⟩))
      (hammingNorm_dualTimeSum_le l f)
  by_cases hne : (codeZWeightSet dC1 dC2).Nonempty
  · exact le_antisymm
      (le_csInf hne fun b hb => csInf_le ⟨0, fun c _ => Nat.zero_le c⟩ (hsub hb))
      (le_csInf (hne.imp fun a₀ ha₀ => hsub ha₀) hge)
  · have hBe : repRDualWeightSet l dC1 dC2 hC = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨f, hf, -⟩
      have hs : dualTimeSum l f ∈ LinearMap.ker dC1.mulVecLin :=
        koszulRepRDual_dualTimeSum_mem_ker l dC1 dC2 hC f hf.1
      have hsr : dualTimeSum l f ∉ LinearMap.range dC2.mulVecLin := fun hmem =>
        hf.2 (koszulRepRDual_mem_range_of_dualTimeSum_mem_range l dC1 dC2 hC f hf.1 hmem)
      exact hne ⟨_, mem_codeZWeightSet.mpr ⟨dualTimeSum l f, hs, hsr, rfl⟩⟩
    have hAe : codeZWeightSet dC1 dC2 = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hBe, hAe]

end QECCertificates.Homology
