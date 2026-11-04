-- Ext.CompleteMetrizability
--
-- Issue #79: Corollary 3.6 and Corollary 3.7 of arXiv:2608.19618 — complete
-- metrizability of the metric locus forces separability, and the σ-compactness
-- equivalence for the bounded locus.
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` §2.9
-- (Corollary 3.6), §2.10 (Corollary 3.7, its gap and the repair this file
-- formalises), §3 (E1, E3, E4d).  E1 and E3 enter as explicit hypotheses; both
-- proofs stay external and neither becomes an axiom or an instance.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Conj51.GDeltaComplete
import IshikiConj51.Ext.GeneralSeparability

open Cardinal Set

namespace IshikiExt

noncomputable section

-- The measurable-space constants of `Ext.CPM` and `Ext.GeneralSeparability`
-- are `local instance`s there, so they are re-registered here.  They are the
-- same constants, so `MeasurableSet` below means what it means in
-- `met_not_borel`, `bmet_not_borel_cpm` and the transfer theorems.
attribute [local instance] cpmMeasurableSpace cpmBorelSpace
attribute [local instance] cpmOnMeasurableSpace cpmOnBorelSpace

/-! ## Alexandrov–Lavrentiev in a metrizable ambient (audit §3, E4d)

`Conj51/GDeltaComplete.lean` proves the Alexandrov–Lavrentiev direction — a
completely metrizable subspace of a metric space is `G_δ` in it — for a
`MetricSpace` ambient, with no separability assumption on either space.  That
file records the Mathlib inventory behind it: no Mathlib result concludes
`IsGδ` from a completeness hypothesis, in v4.32.2 or since.

The ambient needed here is `CPMOn X`, whose supremum distance takes the value
`∞` (audit §1), so it is an `EMetricSpace` and not a `MetricSpace`.  Its
topology is metrizable all the same, and metrizability is all the argument
uses: `TopologicalSpace.metrizableSpaceMetric` supplies a compatible metric,
and it replaces that metric's topology by the ambient one, so the `G_δ`
conclusion is about the topology the statement started from. -/

/-- **Alexandrov–Lavrentiev (E4d), for a metrizable ambient.**  A completely
metrizable subspace of a metrizable space is `G_δ`. -/
theorem isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace {Y : Type*}
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] {A : Set Y}
    (h : TopologicalSpace.IsCompletelyMetrizableSpace ↥A) : IsGδ A := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  exact isGδ_of_isCompletelyMetrizableSpace h

/-- The form in which Corollaries 3.6 and 3.7 use it: a completely metrizable
subspace of a metrizable Borel space is Borel. -/
theorem measurableSet_of_isCompletelyMetrizableSpace {Y : Type*}
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {A : Set Y}
    (h : TopologicalSpace.IsCompletelyMetrizableSpace ↥A) : MeasurableSet A :=
  (isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace h).measurableSet

/-! ## The bounded compatible-metric locus in the continuous ambient

`CPM.BMet D` (`Ext/CPM.lean`) is the preprint's `BMet(D)` for a discrete
carrier: the image in `CPM D` of the compatible members of the bounded ambient
`BCPM(D)`.  Corollary 3.7 needs the same locus for a general topological
space, inside the continuous-pseudometric ambient `CPMOn X`.  There it is
described directly — the members of `Met(X)` that are bounded — and
`CPM.mem_BMet_iff` rewrites the discrete-carrier definition into that shape,
which is what lets the two be matched across the relabelling and across the
discrete-carrier equivalence `CPMOn.equivCPM`. -/

/-- Boundedness of a pseudometric: the condition cutting `BMet` out of
`Met`. -/
def CPM.IsBdd {D : Type*} (d : CPM D) : Prop := ∃ C, ∀ x y, d.1 x y ≤ C

/-- `BMet(D)` is the bounded part of `Met(D)`.  The definition in `Ext/CPM.lean`
is an image, so the two directions build and destruct the bounded witness. -/
theorem CPM.mem_BMet_iff {D : Type*} {d : CPM D} :
    d ∈ CPM.BMet D ↔ d ∈ CPM.Met D ∧ d.IsBdd := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨he, e.2.bounded⟩
  · rintro ⟨hmet, C, hC⟩
    exact ⟨⟨d.1, ⟨d.2.dist_self, d.2.dist_comm, d.2.dist_triangle, ⟨C, hC⟩⟩⟩,
      hmet, rfl⟩

/-- The preprint's `BMet(X)` in the continuous-pseudometric ambient: the
bounded members of the topology-aware metric locus `Met(X)`.

This is Koshino's `AM(X)` (audit §2.10): the bounded metrics on `X` compatible
with its topology, with the supremum distance.  The identification is what
makes E3 applicable, and it is legitimate here — unlike the `Met(X)`
recollection warned about in `notes/literature.md`. -/
def CPM.BMetOn (X : Type*) [TopologicalSpace X] : Set (CPMOn X) :=
  {d | d ∈ CPM.MetOn X ∧ CPM.IsBdd d.1}

@[simp] theorem mem_CPM_BMetOn {X : Type*} [TopologicalSpace X] {d : CPMOn X} :
    d ∈ CPM.BMetOn X ↔ d ∈ CPM.MetOn X ∧ CPM.IsBdd d.1 := Iff.rfl

/-- On a discrete carrier the two descriptions of the bounded locus agree, in
the same sense in which `CPMOn.preimage_equivCPM_met` matches the two metric
loci: through the isometric equivalence `CPMOn D ≃ᵢ CPM D`. -/
theorem CPMOn.preimage_equivCPM_bmet (D : Type*) [TopologicalSpace D]
    [DiscreteTopology D] :
    CPMOn.equivCPM D ⁻¹' CPM.BMet D = CPM.BMetOn D := by
  have hmet : ∀ d : CPMOn D,
      CPMOn.equivCPM D d ∈ CPM.Met D ↔ d ∈ CPM.MetOn D :=
    fun d => Set.ext_iff.mp (CPMOn.preimage_equivCPM_met D) d
  ext d
  rw [Set.mem_preimage, CPM.mem_BMet_iff]
  exact and_congr (hmet d) Iff.rfl

/-- Relabelling preserves the bounded locus: the relabelled pseudometric takes
the same values, so the same constant bounds it. -/
theorem CPMOn.preimage_BMetOn_comap {D E : Type*} [TopologicalSpace D]
    [TopologicalSpace E] (σ : D ≃ₜ E) :
    CPMOn.comap σ ⁻¹' CPM.BMetOn D = CPM.BMetOn E := by
  have hmet : ∀ d : CPMOn E,
      CPMOn.comap σ d ∈ CPM.MetOn D ↔ d ∈ CPM.MetOn E :=
    fun d => Set.ext_iff.mp (CPMOn.preimage_MetOn_comap σ) d
  ext d
  simp only [Set.mem_preimage, mem_CPM_BMetOn]
  refine and_congr (hmet d) ⟨?_, ?_⟩
  · rintro ⟨C, hC⟩
    simp only [CPMOn.comap_coe, CPM.comap_val] at hC
    exact ⟨C, fun x y => by simpa using hC (σ.symm x) (σ.symm y)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun x y => hC (σ x) (σ y)⟩

/-! ## E1 clause (3)

`IsIsometricExtensorOn` (`Ext/GeneralSeparability.lean`) carries E1's clauses
(1), (2) and the inclusion half of its "furthermore" clause — Route M's share.
Audit §2.10's repair of Corollary 3.7 needs one more clause of the *same*
extensor, namely (3) `E(BMet(A)) ⊆ BMet(X)`, so it is added as a field rather
than as a second, unrelated hypothesis: E1 produces one map satisfying all its
clauses simultaneously.  Clause (4) stays omitted; it belongs to §2.12 and
carries the extra "`X` completely metrizable" hypothesis of the §3 caveat. -/

/-- **E1 with clause (3), for one closed subset.**  Ishiki, *An isometric
extensor of metrics*, arXiv:2407.03030, Theorem 1.1, clauses (1)–(3) and the
"furthermore" clause: the isometric extensor of continuous pseudometrics also
carries bounded compatible metrics to bounded compatible metrics.

Since `Ẽ|_{Met(A)} = E` and `BMet(A) ⊆ Met(A)`, the field below is literally
E1's `E(BMet(A)) ⊆ BMet(X)`. -/
structure IsBddIsometricExtensorOn {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set X)
    extends IsIsometricExtensorOn A where
  bmet_preservation : toCPM '' CPM.BMetOn ↥A ⊆ CPM.BMetOn X

/-- Clause (3) survives the transport of
`IsIsometricExtensorOn.toIsIsometricExtensor`: the transported extensor is the
E1 extensor precomposed with the relabelling `CPMOn.comap` and the
discrete-carrier equivalence `CPMOn.equivCPM`, and both preserve the bounded
locus (`CPMOn.preimage_BMetOn_comap`, `CPMOn.preimage_equivCPM_bmet`).

The transported clause is stated as a property of the transported map rather
than as a field of a second bundle, so that the `Met` side of the transport is
reused verbatim rather than rebuilt. -/
theorem IsBddIsometricExtensorOn.image_bmet_subset {A X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] {ι : A → X}
    (hι : @Topology.IsClosedEmbedding A X ⊥ inferInstance ι)
    (hE : IsBddIsometricExtensorOn (Set.range ι)) :
    (hE.toIsIsometricExtensorOn.toIsIsometricExtensor hι).toCPM ''
        CPM.BMet A ⊆ CPM.BMetOn X := by
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  let σ : A ≃ₜ ↥(Set.range ι) := hι.toIsEmbedding.toHomeomorph
  haveI : DiscreteTopology ↥(Set.range ι) := σ.symm.isEmbedding.discreteTopology
  rintro e ⟨d, hd, rfl⟩
  show hE.toCPM (CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d)) ∈ CPM.BMetOn X
  refine hE.bmet_preservation
    ⟨CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d), ?_, rfl⟩
  have hBMetOn : (CPMOn.equivCPM A).symm d ∈ CPM.BMetOn A := by
    rw [← CPMOn.preimage_equivCPM_bmet A]
    show CPMOn.equivCPM A ((CPMOn.equivCPM A).symm d) ∈ CPM.BMet A
    rw [IsometryEquiv.apply_symm_apply]
    exact hd
  rw [← CPMOn.preimage_BMetOn_comap σ.symm] at hBMetOn
  exact hBMetOn

/-! ## The bounded Borel transfer (audit §2.10, the repair)

Corollary 3.7 cannot be read off Corollary 3.6: `BMet(X)` is a clopen union of
components of `Met(X)`, and complete metrizability transfers in neither
direction between the two (audit §2.10).  What the repair supplies instead is
the `BMet` analogue of Theorem 3.5, proved by the argument of §2.8 with the
bounded locus in place of the metric locus throughout. -/

/-- The `BMet` analogue of `IsIsometricExtensor.image_met_eq_range_inter`:
`E(BMet(A)) = Ẽ(CPM(A)) ∩ BMet(X)`.

The inclusion `⊆` is E1 clause (3), supplied as `hbdd`.  The reverse inclusion
is derived, exactly as in the `Met` case: a pseudometric whose extension is a
compatible metric is itself a compatible metric, and it is bounded by whatever
bounds its extension, because `extension` makes its values values of the
extension. -/
theorem IsIsometricExtensor.image_bmet_eq_range_inter {A X : Type*}
    {tA : TopologicalSpace A} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {ι : A → X}
    (hE : IsIsometricExtensor tA ι)
    (hbdd : hE.toCPM '' CPM.BMet A ⊆ CPM.BMetOn X) :
    hE.toCPM '' CPM.BMet A = Set.range hE.toCPM ∩ CPM.BMetOn X := by
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, hbdd ⟨d, hd, rfl⟩⟩
  · rintro ⟨⟨d, rfl⟩, hmem⟩
    refine ⟨d, ?_, rfl⟩
    rw [CPM.mem_BMet_iff]
    constructor
    · have hmemMet : hE.toCPM d ∈ hE.toCPM '' CPM.Met A := by
        rw [hE.image_met_eq_range_inter]
        exact ⟨⟨d, rfl⟩, hmem.1⟩
      obtain ⟨d', hd', hdd'⟩ := hmemMet
      rwa [← hE.isometry_toCPM.injective hdd']
    · obtain ⟨C, hC⟩ := hmem.2
      exact ⟨C, fun x y => by rw [← hE.extension d x y]; exact hC _ _⟩

/-- **The `BMet` analogue of Theorem 3.5 (audit §2.10), bundle form.**  An
isometric extensor from the coded `ℵ₁`-sized discrete carrier into `X` that
preserves the bounded locus forbids Borelness of `BMet(X)` in `CPM(X)`.

The proof is §2.8's chain with `BMet` in place of `Met`: the domain `CPM(Z)` is
complete, so the isometric image is closed, hence Borel; intersecting with the
hypothesis and pulling back along the extensor makes `BMet(Z)` Borel in
`CPM(Z)`.  It ends at `bmet_not_borel_cpm`, the coded-carrier form of Theorem
3.3, which §2.10 records as the contradiction the bounded argument reaches
directly — no components are involved, unlike the route through Theorem 3.4.

`hbdd` is E1 clause (3) for this bundle; `IsBddIsometricExtensorOn.image_bmet_subset`
is what produces it from E1. -/
theorem IsIsometricExtensor.not_measurableSet_CPM_BMetOn {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hScard : #(↥S) = Cardinal.aleph 1) (hSnonmeas : ¬ MeasurableSet S)
    {ι : ExtIndex S → X}
    (hE : IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S)) ι)
    (hbdd : hE.toCPM '' CPM.BMet (ExtIndex S) ⊆ CPM.BMetOn X) :
    ¬ MeasurableSet (CPM.BMetOn X) := by
  intro hBMet
  have hclosed : IsClosed (Set.range hE.toCPM) :=
    isClosed_range_of_isometry_complete _ hE.isometry_toCPM
  have hinter : MeasurableSet (Set.range hE.toCPM ∩ CPM.BMetOn X) :=
    hclosed.measurableSet.inter hBMet
  rw [← hE.image_bmet_eq_range_inter hbdd] at hinter
  have hpre : MeasurableSet
      (hE.toCPM ⁻¹' (hE.toCPM '' CPM.BMet (ExtIndex S))) :=
    hinter.preimage hE.isometry_toCPM.continuous.measurable
  rw [Set.preimage_image_eq _ hE.isometry_toCPM.injective] at hpre
  exact bmet_not_borel_cpm hS hScard hSnonmeas hpre

/-- **The `BMet` analogue of Theorem 3.5, conditional on E1.**  For a
metrizable `X` admitting a closed discrete copy of the coded `ℵ₁`-sized
carrier, E1 with clause (3) forbids Borelness of `BMet(X)` in `CPM(X)`.

`hE1` is E1's statement for `X`, clauses (1)–(3): a hypothesis, never an
axiom. -/
theorem not_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hScard : #(↥S) = Cardinal.aleph 1) (hSnonmeas : ¬ MeasurableSet S)
    {ι : ExtIndex S → X}
    (hι : @Topology.IsClosedEmbedding (ExtIndex S) X ⊥ inferInstance ι)
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A)) :
    ¬ MeasurableSet (CPM.BMetOn X) := by
  letI : TopologicalSpace (ExtIndex S) := ⊥
  obtain ⟨hE⟩ := hE1 (Set.range ι) hι.isClosed_range
  exact (hE.toIsIsometricExtensorOn.toIsIsometricExtensor
    hι).not_measurableSet_CPM_BMetOn hS hScard hSnonmeas (hE.image_bmet_subset hι)

/-- **The separability form of the `BMet` analogue of Theorem 3.5.**
`BMet(X)` Borel in `CPM(X)` implies `X` separable, with E1 (clauses (1)–(3))
supplied as `hE1`.

Nonseparability is consumed exactly as in the `Met` case: it produces a closed
discrete copy of the coded carrier (`exists_isClosedEmbedding_extIndex`), and
the extensor is quantified over closed subsets rather than fixed, because the
subspace is only available after nonseparability is assumed.

`X` is metrizable, as in the preprint, rather than a metric space: the
separated-set lemma behind `exists_isClosedEmbedding_extIndex` needs distances,
so a compatible metric is chosen inside the proof.  Nothing in the statement
depends on the choice — both the hypothesis and the conclusion are properties
of the topology. -/
theorem separable_of_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hScard : #(↥S) = Cardinal.aleph 1) (hSnonmeas : ¬ MeasurableSet S)
    (hBMet : MeasurableSet (CPM.BMetOn X))
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A)) :
    TopologicalSpace.SeparableSpace X := by
  by_contra hX
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨ι, hce⟩ := exists_isClosedEmbedding_extIndex (S := S) hScard hX
  exact not_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn hS hScard
    hSnonmeas hce hE1 hBMet

/-! ## Corollary 3.6 -/

/-- **Corollary 3.6 (`cor:metric-space-complete-separability`), conditional on
E1.**  If `Met(X)` is completely metrizable, then `X` is separable.

The preprint gives no proof; audit §2.9 records the intended one, which is what
runs here.  `Met(X)` is a completely metrizable subspace of the metrizable
`CPM(X)`, hence `G_δ` in it by Alexandrov–Lavrentiev (E4d, Kechris Theorem
3.11 — the arbitrary-metrizable-ambient assertion, no separability of either
space), hence Borel; Theorem 3.5 then applies.

The non-Borel parameter set the transfer needs is produced internally by
`exists_aleph1_nonBorel`, so nothing about it survives into the statement: the
hypotheses are complete metrizability of the locus and E1 for `X`.  `X` is
metrizable, the preprint's hypothesis; Theorem 3.5 is delivered for a metric
space, so a compatible metric is chosen inside the proof, which changes nothing
because both the hypothesis and the conclusion are properties of the topology.

This is the corollary that settles Ishiki's Conjecture 5.1 (Ishiki 2024, §5)
in the strengthened Borel form (audit §2.9). -/
theorem separable_of_isCompletelyMetrizableSpace_CPM_MetOn_of_isometricExtensorOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X))
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsIsometricExtensorOn A)) :
    TopologicalSpace.SeparableSpace X := by
  obtain ⟨S, hSsub, hScard, hSnonmeas⟩ := exists_aleph1_nonBorel
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  exact separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn hSsub hScard
    hSnonmeas (measurableSet_of_isCompletelyMetrizableSpace hMet) hE1

/-! ## Corollary 3.7 -/

/-- The `BMet` half of Corollary 3.6, which is what Corollary 3.7 actually
needs (audit §2.10): if `BMet(X)` is completely metrizable then `X` is
separable.

Corollary 3.6 does not give this.  `BMet(X)` is a clopen union of components of
`Met(X)`, and complete metrizability transfers in neither direction between the
two, which is the gap §2.10 records in the preprint's proof of 3.7.  The
`BMet` analogue of Theorem 3.5 above is what closes it; Alexandrov–Lavrentiev
enters here in the same way as in 3.6. -/
theorem separable_of_isCompletelyMetrizableSpace_CPM_BMetOn_of_bddIsometricExtensorOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hBMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X))
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A)) :
    TopologicalSpace.SeparableSpace X := by
  obtain ⟨S, hSsub, hScard, hSnonmeas⟩ := exists_aleph1_nonBorel
  exact separable_of_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn hSsub
    hScard hSnonmeas (measurableSet_of_isCompletelyMetrizableSpace hBMet) hE1

/-- A σ-compact metrizable space is separable: countably many compact pieces,
each of them separable. -/
theorem separableSpace_of_sigmaCompactSpace {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] [SigmaCompactSpace X] :
    TopologicalSpace.SeparableSpace X := by
  rw [← TopologicalSpace.isSeparable_univ_iff, ← iUnion_compactCovering X]
  exact TopologicalSpace.IsSeparable.iUnion
    fun n => (isCompact_compactCovering X n).isSeparable

/-- **Corollary 3.7 (`cor:bounded-metric-complete-sigma-compact`), repaired
per audit §2.10, conditional on E1 and E3.**  For a metrizable `X`: `BMet(X)`
is completely metrizable if and only if `X` is σ-compact.

Both directions pass through E3 — Koshino's theorem, *for separable metrizable
`X`* — so both have to produce separability first, and that is where the
preprint's proof has a gap.  The `⇐` direction is fine as written: σ-compact
metrizable spaces are separable.  The `⇒` direction is the repaired one: it
runs through the `BMet` analogue of Theorem 3.5 rather than through Corollary
3.6, which concerns `Met(X)` and does not imply the `BMet` statement.

`hE3` is E3 for this `X`, as an explicit hypothesis: Koshino's object is
`AM(X)`, the bounded admissible metrics with the supremum distance, which is
`CPM.BMetOn X` here.  Two records from audit §2.10 that belong with any use of
it: the preprint cites "[Corollary 1.2]" of Koshino, whereas this repository's
verified literature record (`notes/literature.md`, checked against the arXiv
v2 = published text) finds the paper's main Theorem and Corollary unnumbered,
so the citation number needs checking against the published AGMS version; and
the `AM(X) = BMet(X)` identification is legitimate here, unlike the `Met(X)`
recollection that record warns about.

The hypotheses are satisfiable, so the statement is not vacuous: E1 holds for
every metrizable `X` and E3 for every separable metrizable `X`.  Both proofs
are external and neither is formalised. -/
theorem isCompletelyMetrizableSpace_CPM_BMetOn_iff_sigmaCompactSpace
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A))
    (hE3 : TopologicalSpace.SeparableSpace X →
      (SigmaCompactSpace X ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X))) :
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X) ↔
      SigmaCompactSpace X := by
  constructor
  · intro hBMet
    exact (hE3 (separable_of_isCompletelyMetrizableSpace_CPM_BMetOn_of_bddIsometricExtensorOn
      hBMet hE1)).mpr hBMet
  · intro hσ
    haveI := hσ
    exact (hE3 separableSpace_of_sigmaCompactSpace).mp hσ

end
end IshikiExt
