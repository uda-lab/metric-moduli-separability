-- Ext.UltraTransfer
--
-- Issue #82, scope items 3 and 4: Theorem 3.14 and Corollary 3.15 of
-- arXiv:2608.19618, by the compact-witness repair of the audit.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.14 (the
-- Theorem 3.14 paragraph, its *Gap*, and the *Repair* — including the
-- completeness sub-lemma formalised in `Ext/UltraGeneral.lean`), §2.14's
-- Corollary 3.15 paragraph, and §3 (E2, E4d).
--
-- **The printed proof of 3.14 is not formalised, because it does not close.**
-- Audit §2.14 records the gap: the final step needs Borelness to be pulled back
-- from `UCPM(Y;R)` to `UCPM(Z;R)`, and E2 — unlike E1 on the Archimedean side —
-- supplies no `UCPM`-level extensor to pull it back along.  What is formalised
-- here is the audit's repair, which is the sole verified route:
--
--   * `F := E(Ψ(2^ω ∖ S))` sits inside `UMet(Y;R)`, and `ι := E ∘ Ψ` is an
--     isometry of it with `(2^ω ∖ S, h)`;
--   * `ι` extends to the closure `P = cl(2^ω ∖ S)` because `UCPM(Y;R)` is
--     complete (`completeSpace_UCPMOn`, audit's sub-lemma);
--   * the extension is injective, its image `K` is compact, and
--     `K ∩ UMet(Y;R) = F`;
--   * Borelness of `UMet(Y;R)` therefore makes `2^ω ∖ S` Borel, contradicting
--     Proposition 2.2.
--
-- The audit's shortcut "separable metrizable spaces are absolutely Borel" is
-- false and is not used anywhere; `F ≅ 2^ω ∖ S` is itself a counterexample to
-- it.
--
-- Two presentational choices, both recorded because they change nothing
-- mathematically.
--
--   (1) The audit's compact parameter space `P = cl_{2^ω}(2^ω ∖ S)` appears
--       here as `codingClosure = cl(Φ(2^ω ∖ S))` inside `UCPM(Z;R)`.  The two
--       are the same compact space: `Φ` is a `𝒰𝒟^R`-isometry of `(2^ω,h)` onto
--       its image (Lemma 3.11), and `codingClosure_eq_image_closure` proves
--       `cl(Φ(2^ω ∖ S)) = Φ(P)` outright.  The extension is performed on that
--       side because there the domain is a subspace of an `EMetricSpace`, where
--       Mathlib's dense-uniform-extension machinery applies unchanged; `ῑ` is
--       `ultraExtend` composed with `Φ`.
--   (2) As in Theorems 3.12–3.13 (audit §7, #81), the final contradiction is
--       obtained by the *pullback* route rather than by the printed
--       relative-trace route: the compact `K` and the trace identity
--       `K ∩ UMet(Y;R) = F` are formalised (`isCompact_range_ultraExtend`,
--       `range_ultraExtend_inter_UMetOn`) but the theorem consumes the
--       equivalent preimage identity `ῑ⁻¹(UMet(Y;R)) = P ∖ S`
--       (`preimage_UMetOn_ultraExtend`), for which closedness of `P` is enough.
--
-- E2 is `IsUltraIsometricExtensor` (`Ext/UltraGeneral.lean`), a hypothesis
-- everywhere below; its proof stays external and it is never an axiom.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.UltraCoding
import IshikiConj51.Ext.UltraGeneral
import IshikiConj51.Ext.CompleteMetrizability

open Cardinal Set Filter
open scoped ENNReal Topology

namespace IshikiExt

noncomputable section

-- `ucpmMeasurableSpace`/`ucpmBorelSpace` (`Ext.UltraCoding`) and
-- `ucpmOnMeasurableSpace`/`ucpmOnBorelSpace` (`Ext.UltraGeneral`) are declared
-- `local instance` there, so they are re-registered here.  They are the same
-- constants, so `MeasurableSet` below means what it means in `umet_not_borel`.
attribute [local instance] ucpmMeasurableSpace ucpmBorelSpace
attribute [local instance] ucpmOnMeasurableSpace ucpmOnBorelSpace

variable {R : RangeSet} {r : ℕ → ℝ}

/-! ## The discrete witness and its closure

`codingWitness` is the audit's `Ψ(2^ω ∖ S)`, the closed copy of the parameter
complement inside `UMet(Z;R)` supplied by Lemma 3.11; `codingClosure` is its
closure in the ambient `UCPM(Z;R)`, which is the transported form of the
audit's compact `P`. -/

/-- The audit's `Ψ(2^ω ∖ S)`: the coded copy of the parameter complement. -/
def codingWitness (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    Set (UCPM (UltraIndex S) R) :=
  phiU hr S '' Sᶜ

/-- The closure of the witness in the ambient `UCPM(Z;R)`; `Φ(P)` for the
audit's `P = cl_{2^ω}(2^ω ∖ S)`, by `codingClosure_eq_image_closure`. -/
def codingClosure (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    Set (UCPM (UltraIndex S) R) :=
  closure (codingWitness hr S)

variable {S : Set (ℕ → Bool)}

theorem codingWitness_eq (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    codingWitness hr S = phiU hr S '' Sᶜ := rfl

theorem codingClosure_eq (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    codingClosure hr S = closure (codingWitness hr S) := rfl

theorem codingWitness_subset_codingClosure (hr : RangeSet.IsScale R r)
    (S : Set (ℕ → Bool)) : codingWitness hr S ⊆ codingClosure hr S :=
  subset_closure

theorem isClosed_codingClosure (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    IsClosed (codingClosure hr S) :=
  isClosed_closure

/-- The witness consists of compatible members: this is Lemma 3.10's
compatibility direction. -/
theorem codingWitness_subset_UMet (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    codingWitness hr S ⊆ UMet (UltraIndex S) R := by
  rintro _ ⟨t, htS, rfl⟩
  exact (isCompatible_phiU_iff hr S t).mpr htS

/-- **The trace identity at the discrete level.**  Passing to the closure adds
no compatible members: `cl(Ψ(2^ω∖S)) ∩ UMet(Z;R) = Ψ(2^ω∖S)`.  This is Lemma
3.11's closed image (`isClosed_image_phiU`) read in the ambient, and it is what
makes the trace identity for `K` in `UCPM(Y;R)` come out exactly. -/
theorem codingClosure_inter_UMet (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    codingClosure hr S ∩ UMet (UltraIndex S) R = codingWitness hr S := by
  refine Set.Subset.antisymm ?_
    (Set.subset_inter (codingWitness_subset_codingClosure hr S) (codingWitness_subset_UMet hr S))
  rintro d ⟨hdQ, hdU⟩
  have himg : (Subtype.val : ↥(UMet (UltraIndex S) R) → UCPM (UltraIndex S) R) ''
      (Subtype.val ⁻¹' codingWitness hr S) = codingWitness hr S := by
    rw [Subtype.image_preimage_coe]
    exact Set.inter_eq_right.mpr (codingWitness_subset_UMet hr S)
  have hclosed : IsClosed (Subtype.val ⁻¹' codingWitness hr S :
      Set ↥(UMet (UltraIndex S) R)) := isClosed_image_phiU hr S
  have hmem : (⟨d, hdU⟩ : ↥(UMet (UltraIndex S) R)) ∈
      closure (Subtype.val ⁻¹' codingWitness hr S) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, himg]
    exact hdQ
  rw [hclosed.closure_eq] at hmem
  exact hmem

/-- The closure is compact: it is a closed subset of the compact `Φ(2^ω)`. -/
theorem isCompact_codingClosure (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    IsCompact (codingClosure hr S) :=
  (isCompact_range_phiU hr S).of_isClosed_subset (isClosed_codingClosure hr S)
    (closure_minimal (Set.image_subset_range _ _) (isClosed_range_phiU hr S))

/-- **The audit's `P`, transported.**  `cl(Φ(2^ω ∖ S)) = Φ(cl(2^ω ∖ S))`: the
closure taken in the ambient is the image of the audit's compact parameter
space `P`.  Both inclusions are immediate from continuity of `Φ` and
compactness of `2^ω`, and the identity is what licenses reading every statement
about `codingClosure` below as a statement about `P`. -/
theorem codingClosure_eq_image_closure (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    codingClosure hr S = phiU hr S '' closure Sᶜ := by
  have hclosed : IsClosed (phiU hr S '' closure Sᶜ) :=
    (isClosed_closure.isCompact.image (continuous_phiU hr S)).isClosed
  rw [codingClosure_eq, codingWitness_eq]
  exact Set.Subset.antisymm (closure_minimal (Set.image_mono subset_closure) hclosed)
    (image_closure_subset_closure_image (continuous_phiU hr S))

/-! ## The extension of `E ∘ Ψ` to the closure

`ι := E ∘ Ψ` is an isometry of the dense subset `Ψ(2^ω∖S)` of the compact
`codingClosure` into the complete `UCPM(Y;R)`, so it extends to the closure.
The extension is Mathlib's dense-uniform extension; the three facts that the
repair uses are that it is isometric (hence injective), that it agrees with `E`
on the witness, and that restricting it along `ι : Z → Y` gives back the point
of the closure it was evaluated at. -/

section Extension

variable {Y : Type*} [TopologicalSpace Y] {ι : UltraIndex S → Y}

/-- The inclusion of the witness into its closure. -/
def codingInclusion (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    ↥(codingWitness hr S) → ↥(codingClosure hr S) :=
  Set.inclusion (codingWitness_subset_codingClosure hr S)

/-- `ι = E ∘ Ψ` of the audit: E2's extensor applied to the coded witness. -/
def codingExtensor (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    ↥(codingWitness hr S) → UCPMOn Y R :=
  fun d => hE.toUCPMOn ⟨d.1, codingWitness_subset_UMet hr S d.2⟩

/-- `ι` is an isometry: E2 clause (2) composed with Lemma 3.11's isometry, the
latter being invisible here because both sides are measured by `𝒰𝒟^R`. -/
theorem isometry_codingExtensor (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    Isometry (codingExtensor hr hE) := by
  intro d e
  exact hE.isometry_toUCPMOn ⟨d.1, codingWitness_subset_UMet hr S d.2⟩
    ⟨e.1, codingWitness_subset_UMet hr S e.2⟩

theorem isUniformInducing_codingInclusion (hr : RangeSet.IsScale R r)
    (S : Set (ℕ → Bool)) : IsUniformInducing (codingInclusion hr S) := by
  refine (isUniformInducing_val (codingClosure hr S)).of_comp_iff.mp ?_
  have hcomp : (Subtype.val : ↥(codingClosure hr S) → UCPM (UltraIndex S) R) ∘
      codingInclusion hr S = (Subtype.val : ↥(codingWitness hr S) → UCPM (UltraIndex S) R) :=
    Set.val_comp_inclusion (codingWitness_subset_codingClosure hr S)
  rw [hcomp]
  exact isUniformInducing_val _

theorem denseRange_codingInclusion (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    DenseRange (codingInclusion hr S) :=
  (denseRange_inclusion_iff (codingWitness_subset_codingClosure hr S)).mpr
    (subset_rfl : codingClosure hr S ⊆ closure (codingWitness hr S))

/-- **The audit's `ῑ`**: the extension of `ι = E ∘ Ψ` from the witness to its
closure.  It exists because `UCPM(Y;R)` is complete (audit §2.14's sub-lemma,
`completeSpace_UCPMOn`) and `ι` is uniformly continuous; completeness is used
in every statement about it below, which is why `R.IsCharacteristic` appears
there and not in the definition. -/
def ultraExtend (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    ↥(codingClosure hr S) → UCPMOn Y R :=
  IsDenseInducing.extend
    ((isUniformInducing_codingInclusion hr S).isDenseInducing (denseRange_codingInclusion hr S))
    (codingExtensor hr hE)

theorem ultraExtend_apply (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι)
    (d : ↥(codingWitness hr S)) :
    ultraExtend hr hE (codingInclusion hr S d) = codingExtensor hr hE d :=
  uniformly_extend_of_ind (isUniformInducing_codingInclusion hr S)
    (denseRange_codingInclusion hr S) (isometry_codingExtensor hr hE).uniformContinuous d

theorem uniformContinuous_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    UniformContinuous (ultraExtend hr hE) := by
  haveI : CompleteSpace (UCPMOn Y R) := completeSpace_UCPMOn hR
  exact uniformContinuous_uniformly_extend (isUniformInducing_codingInclusion hr S)
    (denseRange_codingInclusion hr S) (isometry_codingExtensor hr hE).uniformContinuous

theorem continuous_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    Continuous (ultraExtend hr hE) :=
  (uniformContinuous_ultraExtend hR hr hE).continuous

/-- **The extension is isometric**, as the audit states: two continuous
functions on `codingClosure × codingClosure` that agree on a dense subset. -/
theorem isometry_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    Isometry (ultraExtend hr hE) := by
  have hcont : Continuous (ultraExtend hr hE) := continuous_ultraExtend hR hr hE
  have heq : (fun p : ↥(codingClosure hr S) × ↥(codingClosure hr S) =>
        edist (ultraExtend hr hE p.1) (ultraExtend hr hE p.2))
      = fun p : ↥(codingClosure hr S) × ↥(codingClosure hr S) => edist p.1 p.2 := by
    refine Continuous.ext_on
      ((denseRange_codingInclusion hr S).prodMap (denseRange_codingInclusion hr S))
      ((hcont.comp continuous_fst).edist (hcont.comp continuous_snd))
      (continuous_fst.edist continuous_snd) ?_
    rintro _ ⟨⟨d, e⟩, rfl⟩
    show edist (ultraExtend hr hE (codingInclusion hr S d))
        (ultraExtend hr hE (codingInclusion hr S e)) = _
    rw [ultraExtend_apply, ultraExtend_apply]
    exact isometry_codingExtensor hr hE d e
  intro a b
  exact congrFun heq (a, b)

/-- **E2 clause (1), propagated to the closure.**  Restricting the extension
along `ι : Z → Y` returns the point of the closure: the two continuous maps
`UCPMOn.restrict ι ∘ ῑ` and the inclusion agree on the dense witness, where the
identity is clause (1).

This single identity carries the rest of the repair: it makes `ῑ` injective and
it computes `ῑ⁻¹(UMet(Y;R))`. -/
theorem restrict_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι)
    (q : ↥(codingClosure hr S)) :
    UCPMOn.restrict ι (ultraExtend hr hE q) = (q : UCPM (UltraIndex S) R) := by
  have heq : (fun q : ↥(codingClosure hr S) => UCPMOn.restrict ι (ultraExtend hr hE q))
      = (Subtype.val : ↥(codingClosure hr S) → UCPM (UltraIndex S) R) := by
    refine Continuous.ext_on (denseRange_codingInclusion hr S)
      ((UCPMOn.continuous_restrict ι).comp (continuous_ultraExtend hR hr hE))
      continuous_subtype_val ?_
    rintro _ ⟨d, rfl⟩
    show UCPMOn.restrict ι (ultraExtend hr hE (codingInclusion hr S d)) = _
    rw [ultraExtend_apply]
    exact hE.restrict_toUCPMOn _
  exact congrFun heq q

theorem injective_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    Function.Injective (ultraExtend hr hE) := by
  intro a b hab
  refine Subtype.ext ?_
  rw [← restrict_ultraExtend hR hr hE a, ← restrict_ultraExtend hR hr hE b, hab]

/-- **The exact pullback identity** `ῑ⁻¹(UMet(Y;R)) = P ∖ S`, in its transported
form.  `⊇` is E2 clause (5); `⊆` is the restriction argument: a compatible
member of `UCPM(Y;R)` restricts to a compatible member of `UCPM(Z;R)` along the
closed discrete embedding, and by `restrict_ultraExtend` that restriction *is*
the point of the closure, which the discrete-level trace identity then places in
the witness. -/
theorem preimage_UMetOn_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    ultraExtend hr hE ⁻¹' UMetOn Y R = Subtype.val ⁻¹' codingWitness hr S := by
  ext q
  constructor
  · intro hq
    have hemb : @Topology.IsEmbedding (UltraIndex S) Y ⊥ inferInstance ι := by
      letI : TopologicalSpace (UltraIndex S) := ⊥
      exact hE.closedEmbedding.toIsEmbedding
    have h1 : UCPMOn.restrict ι (ultraExtend hr hE q) ∈ UMet (UltraIndex S) R :=
      UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace (UltraIndex S))
        hemb hE.domain_discrete hq
    rw [restrict_ultraExtend hR hr hE q] at h1
    have h2 : (q : UCPM (UltraIndex S) R) ∈ codingClosure hr S ∩ UMet (UltraIndex S) R :=
      ⟨q.2, h1⟩
    rw [codingClosure_inter_UMet hr S] at h2
    exact h2
  · intro hq
    show ultraExtend hr hE q ∈ UMetOn Y R
    have hmem : ultraExtend hr hE (codingInclusion hr S ⟨q.1, hq⟩) ∈ UMetOn Y R := by
      rw [ultraExtend_apply]
      exact hE.umet_preservation _
    exact hmem

/-- **The compact witness `K = ῑ(P)`** of the audit's repair. -/
theorem isCompact_range_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    IsCompact (Set.range (ultraExtend hr hE)) := by
  haveI : CompactSpace ↥(codingClosure hr S) :=
    isCompact_iff_compactSpace.mp (isCompact_codingClosure hr S)
  exact isCompact_range (continuous_ultraExtend hR hr hE)

/-- **The trace identity `K ∩ UMet(Y;R) = F`** of the audit's repair, with
`F = E(Ψ(2^ω∖S))` the image of the witness.  It is the pullback identity read
forward; the theorem below consumes the pullback form, for which closedness of
`P` suffices. -/
theorem range_ultraExtend_inter_UMetOn (hR : R.IsCharacteristic)
    (hr : RangeSet.IsScale R r)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    Set.range (ultraExtend hr hE) ∩ UMetOn Y R
      = ultraExtend hr hE '' (Subtype.val ⁻¹' codingWitness hr S) := by
  rw [← preimage_UMetOn_ultraExtend hR hr hE, Set.image_preimage_eq_inter_range,
    Set.inter_comm]

/-! ## Theorem 3.14 -/

/-- **Theorem 3.14 (`thm:ultrametric-borel-separability`), core content**, by
the repair of audit §2.14.  A fixed E2 extensor out of the coded `ℵ₁`-sized
discrete carrier forbids Borelness of `UMet(Y;R)` in `UCPM(Y;R)`.

This is the contrapositive form and the one with mathematical content; the
separability statements below are corollaries of it.  The proof is the audit's
repair end to end: the extension `ῑ` of `E ∘ Ψ` to the closure of the witness
(available by completeness of `UCPM(Y;R)`), its exact pullback identity, and
then the pullback of Borelness along the continuous `Φ`, which returns
Proposition 2.2's non-Borel `S`.

Density of `S` is consumed twice, exactly where Lemma 3.11 consumes it: through
`isClosed_image_phiU` inside the discrete-level trace identity, and through
injectivity of `Φ` in the last step. -/
theorem IsUltraIsometricExtensor.not_measurableSet_UMetOn
    (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hS : Dense S) (hSnonmeas : ¬ MeasurableSet S)
    (hE : IsUltraIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) R ι) :
    ¬ MeasurableSet (UMetOn Y R) := by
  intro hMet
  have h1 : MeasurableSet (ultraExtend hr hE ⁻¹' UMetOn Y R) :=
    hMet.preimage (continuous_ultraExtend hR hr hE).measurable
  rw [preimage_UMetOn_ultraExtend hR hr hE] at h1
  have h2 : MeasurableSet ((Subtype.val : ↥(codingClosure hr S) → UCPM (UltraIndex S) R) ''
      (Subtype.val ⁻¹' codingWitness hr S)) :=
    ((isClosed_codingClosure hr S).measurableSet).subtype_image h1
  rw [Subtype.image_preimage_coe,
    Set.inter_eq_right.mpr (codingWitness_subset_codingClosure hr S)] at h2
  have h3 : MeasurableSet (phiU hr S ⁻¹' codingWitness hr S) :=
    h2.preimage (continuous_phiU hr S).measurable
  rw [codingWitness_eq, Set.preimage_image_eq _ (injective_phiU hr hS)] at h3
  exact hSnonmeas (by simpa using h3.compl)

end Extension

/-! ## From nonseparability to the coded carrier -/

/-- A nonseparable metric space contains a closed discrete copy of any carrier
of cardinality `ℵ₁`.

`exists_aleph1_closed_discrete_separated` produces the separated set; the
bijection with the carrier exists because both have cardinality `ℵ₁`, and it is
a homeomorphism because both carriers are discrete.  This is the carrier-generic
form of `exists_isClosedEmbedding_extIndex` (`Ext/GeneralSeparability.lean`),
which is stated for the Archimedean coded carrier; the non-Archimedean track
needs it for `UltraIndex S`. -/
theorem exists_isClosedEmbedding_of_card_aleph_one {Y : Type*} [MetricSpace Y] {C : Type*}
    (hC : #C = Cardinal.aleph 1) (hY : ¬ TopologicalSpace.SeparableSpace Y) :
    ∃ ι : C → Y, @Topology.IsClosedEmbedding C Y ⊥ inferInstance ι := by
  obtain ⟨ε, -, Z, hZcard, hZclosed, hZdisc, -⟩ :=
    exists_aleph1_closed_discrete_separated hY
  obtain ⟨e⟩ : Nonempty (C ≃ ↥Z) := by
    refine Cardinal.lift_mk_eq'.mp ?_
    rw [hC, hZcard]
    simp [Cardinal.lift_aleph]
  refine ⟨Subtype.val ∘ (e : C → ↥Z), ?_⟩
  letI : TopologicalSpace C := ⊥
  haveI : DiscreteTopology C := ⟨rfl⟩
  haveI : DiscreteTopology (↥Z) := hZdisc
  let h : C ≃ₜ (↥Z) :=
    { toEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have hemb : Topology.IsEmbedding (Subtype.val ∘ (e : C → ↥Z)) :=
    Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  have hrange : Set.range (Subtype.val ∘ (e : C → ↥Z)) = Z := by
    rw [Set.range_comp, Set.range_eq_univ.mpr e.surjective, Set.image_univ, Subtype.range_coe]
  refine ⟨hemb, ?_⟩
  rw [hrange]
  exact hZclosed

/-- **Theorem 3.14 (`thm:ultrametric-borel-separability`), conditional on E2.**
If `UMet(Y;R)` is Borel in `UCPM(Y;R)` then `Y` is separable.

`hE2` is E2 as audit §3 quotes it, in the shape the argument needs: *every*
closed discrete subspace of `Y` admits an isometric extensor of compatible
`R`-valued ultrametrics.  Quantifying rather than fixing it is what the argument
requires — the closed discrete subspace is produced by the separated-set
argument only after nonseparability is assumed, so no single extensor can be
named in advance.  E2's own proof stays external; it is never an axiom here.

The preprint's standing hypothesis that `Y` is ultrametrizable does **not**
appear, and its absence is deliberate: the repair never uses it.  It is E2 whose
hypotheses require it, and E2 is `hE2` here — so ultrametrizability enters
exactly where the audit says it does, through the availability of the extensor.
The statement below is therefore stronger than the preprint's 3.14 and implies
it, with no auxiliary bridge to discharge; carrying an `R`-valued surrogate such
as `(UMetOn Y R).Nonempty` instead would *weaken* it to a form that the audited
hypotheses cannot instantiate without an external equivalence. -/
theorem separable_of_measurableSet_UMetOn_of_ultraExtensors {Y : Type*} [MetricSpace Y]
    (hR : R.IsCharacteristic)
    (hMet : MeasurableSet (UMetOn Y R))
    (hE2 : ∀ (Z : Type) (ι : Z → Y), Nonempty Z →
      @Topology.IsClosedEmbedding Z Y ⊥ inferInstance ι →
      Nonempty (IsUltraIsometricExtensor (⊥ : TopologicalSpace Z) R ι)) :
    TopologicalSpace.SeparableSpace Y := by
  by_contra hY
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  obtain ⟨S, hSdense, hScard, hSnonmeas⟩ := exists_dense_aleph1_nonBorel_cantor
  obtain ⟨ι, hce⟩ :=
    exists_isClosedEmbedding_of_card_aleph_one (C := UltraIndex S) (card_ultraIndex hScard) hY
  obtain ⟨w, hw⟩ := hSdense.nonempty
  obtain ⟨hE⟩ := hE2 (UltraIndex S) ι ⟨(⟨w, hw⟩, none)⟩ hce
  exact hE.not_measurableSet_UMetOn hR hr hSdense hSnonmeas hMet

/-! ## Corollary 3.15 -/

/-- **Corollary 3.15 (`cor:ultrametric-space-complete-separability`), conditional
on E2.**  If `UMet(Y;R)` is completely metrizable then `Y` is separable.

The preprint omits the proof; audit §2.14 records it and it is what runs here.
`UMet(Y;R)` is a completely metrizable subspace of the metrizable `UCPM(Y;R)`,
hence `G_δ` in it by Alexandrov–Lavrentiev (E4d, Kechris Theorem 3.11, in the
arbitrary-metrizable-ambient form of
`isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace`), hence Borel; Theorem
3.14 then applies.  The corollary inherits the 3.14 repair and adds nothing to
it.

`Y` is metrizable, the preprint's hypothesis; Theorem 3.14 is delivered for a
metric space, so a compatible metric is chosen inside the proof, which changes
nothing because the two loci, the hypothesis and the conclusion are all
properties of the topology. -/
theorem separable_of_isCompletelyMetrizableSpace_UMetOn_of_ultraExtensors {Y : Type*}
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    (hR : R.IsCharacteristic)
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(UMetOn Y R))
    (hE2 : ∀ (Z : Type) (ι : Z → Y), Nonempty Z →
      @Topology.IsClosedEmbedding Z Y ⊥ inferInstance ι →
      Nonempty (IsUltraIsometricExtensor (⊥ : TopologicalSpace Z) R ι)) :
    TopologicalSpace.SeparableSpace Y := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  exact separable_of_measurableSet_UMetOn_of_ultraExtensors hR
    (measurableSet_of_isCompletelyMetrizableSpace hMet) hE2

end

end IshikiExt
