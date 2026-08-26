-- Ext.UltraCompleteTransfer
--
-- Issue #83, scope items 1, 3 and 4: the complete `R`-valued
-- compatible-ultrametric locus `UComp(Y;R)` in the preprint's continuous
-- ambient, and Corollary 3.17 of arXiv:2608.19618.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.15 (the
-- Corollary 3.17 paragraph, verdict FIX + EXTERNAL), §2.14 (the Theorem 3.14
-- ambient-transfer repair this corollary inherits verbatim) and §3 (E2,
-- including clause (N1), and E4d).
--
-- **What the corollary needs beyond Theorem 3.14.**  Audit §2.15: `Y` is
-- ultrametrizable with `UComp(Y;R) ≠ ∅`; nonemptiness makes `Y` completely
-- metrizable, which is exactly the hypothesis under which E2's clause (N1)
-- licenses choosing the extensor so that it preserves completeness.  With that
-- clause the whole 3.14 repair runs unchanged, with `Ψ` replaced by the 3.16
-- witness — i.e. with the coding family read as a family of *complete*
-- compatible ultrametrics (`preimage_UComp_phiU`, `Ext/UltraComplete.lean`).
--
-- Accordingly:
--   * `UCompOn` is the locus, in the same continuous ambient `UCPMOn Y R` that
--     Theorem 3.14 uses — not a convenient smaller one;
--   * `isCompletelyMetrizableSpace_of_mem_UCompOn` is the audit's "nonemptiness
--     ⇒ `Y` completely metrizable" step, and it is what supplies (N1)'s
--     hypothesis;
--   * `IsUltraCompIsometricExtensor` is `IsUltraIsometricExtensor`
--     (`Ext/UltraGeneral.lean`) with (N1) added as *one further field*, gated on
--     complete metrizability of `Y`, exactly as audit §3 quotes it.  E2 stays
--     external and is never an axiom, and no `UCPM`-level extensor is assumed —
--     the domain caveat of §3 is what forces the transfer repair in the first
--     place;
--   * `preimage_UCompOn_ultraExtend` and `range_ultraExtend_inter_UCompOn` are
--     the audit's `E(UComp(Z;R)) = E(UMet(Z;R)) ∩ UComp(Y;R)` in the transported
--     form the repair consumes; the reverse inclusion is where audit §3's
--     "restriction of a complete metric to a closed subspace is complete"
--     enters, through `isCompleteMetricOn_restrict`.
--
-- The extension map `ῑ` itself is *not* rebuilt: `ultraExtend`
-- (`Ext/UltraTransfer.lean`) depends only on the witness and on E2's clauses
-- (1), (2), so the complete branch reuses it and its whole lemma set unchanged.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.UltraComplete
import IshikiConj51.Ext.UltraTransfer

open Cardinal Set

namespace IshikiExt

noncomputable section

-- The measurable-space constants of `Ext.UltraCoding` and `Ext.UltraGeneral`
-- are `local instance`s there, so they are re-registered here.  They are the
-- same constants, so `MeasurableSet` below means what it means in
-- `ucomp_not_borel_of_card` and in the Theorem 3.14 transfer.
attribute [local instance] ucpmMeasurableSpace ucpmBorelSpace
attribute [local instance] ucpmOnMeasurableSpace ucpmOnBorelSpace

variable {Z Y : Type*} {R : RangeSet} {r : ℕ → ℝ}

/-! ## The complete compatible locus of a topological space

`UCompOn Y R` is the preprint's `UComp(Y;R)`: the complete members of
`UMet(Y;R)`, inside the continuous ambient `UCPMOn Y R` of
`Ext/UltraGeneral.lean`.  Both the ambient and the compatibility condition are
the ones Theorem 3.14 already uses; only completeness is added. -/

/-- `UComp(Y;R)` in the preprint's ambient: the complete members of
`UMet(Y;R)`. -/
def UCompOn (Y : Type*) [TopologicalSpace Y] (R : RangeSet) : Set (UCPMOn Y R) :=
  {d | d ∈ UMetOn Y R ∧ IsCompleteMetricOn d.1.1}

@[simp] theorem mem_UCompOn [TopologicalSpace Y] {d : UCPMOn Y R} :
    d ∈ UCompOn Y R ↔ d ∈ UMetOn Y R ∧ IsCompleteMetricOn d.1.1 := Iff.rfl

theorem UCompOn_subset_UMetOn (Y : Type*) [TopologicalSpace Y] (R : RangeSet) :
    UCompOn Y R ⊆ UMetOn Y R := fun _ h => h.1

/-- **Nonemptiness of `UComp(Y;R)` makes `Y` completely metrizable** (audit
§2.15).  A member of the locus is a complete metric inducing the topology of
`Y`, which is literally Mathlib's definition of complete metrizability.  This is
the step that supplies the hypothesis of E2 clause (N1). -/
theorem isCompletelyMetrizableSpace_of_mem_UCompOn [TopologicalSpace Y] {g : UCPMOn Y R}
    (hg : g ∈ UCompOn Y R) : TopologicalSpace.IsCompletelyMetrizableSpace Y := by
  obtain ⟨⟨hm, htop⟩, hcomplete⟩ := hg
  refine ⟨⟨hm.toMetricSpace, ?_, (isCompleteMetricOn_iff_completeSpace hm).mp hcomplete⟩⟩
  rw [← hm.topology_eq_metricSpace_topology]
  exact htop

/-! ## Restriction to a closed subspace

Audit §3 lists "restriction of a complete metric to a closed subspace is
complete" among the standard facts the preprint uses silently; Corollary 3.17
needs it for the reverse inclusion of `E(UComp(Z;R)) = E(UMet(Z;R)) ∩
UComp(Y;R)`.  `isCompleteMetricOn_restrict` (`Ext/Completeness.lean`) is that
fact; the two lemmas below are its `UCPM`-ambient readings, the non-Archimedean
twins of the `Met`-level restriction already used by Theorem 3.14. -/

/-- Restricting a complete member of `UCPM(Y;R)` along a closed embedding gives
a complete metric. -/
theorem isCompleteMetricOn_restrict_of_mem_UCompOn (tZ : TopologicalSpace Z)
    [TopologicalSpace Y] {ι : Z → Y}
    (hι : @Topology.IsClosedEmbedding Z Y tZ inferInstance ι) {g : UCPMOn Y R}
    (hg : g ∈ UCompOn Y R) : IsCompleteMetricOn (UCPMOn.restrict ι g).1 := by
  obtain ⟨⟨hm, htop⟩, hcomplete⟩ := hg
  exact isCompleteMetricOn_restrict hι hm htop hcomplete fun _ _ => rfl

/-- Restricting a complete compatible member of `UCPM(Y;R)` to a discrete closed
subspace lands in `UComp(Z;R)`: compatibility is
`UCPM.isCompatible_comap_of_mem_UMetOn` (`Ext/UltraGeneral.lean`) and
completeness is the lemma above. -/
theorem restrict_mem_UComp_of_mem_UCompOn (tZ : TopologicalSpace Z) [TopologicalSpace Y]
    {ι : Z → Y} (hι : @Topology.IsClosedEmbedding Z Y tZ inferInstance ι) (htZ : tZ = ⊥)
    {g : UCPMOn Y R} (hg : g ∈ UCompOn Y R) : UCPMOn.restrict ι g ∈ UComp Z R :=
  ⟨UCPM.isCompatible_comap_of_mem_UMetOn tZ hι.toIsEmbedding htZ hg.1,
    isCompleteMetricOn_restrict_of_mem_UCompOn tZ hι hg⟩

/-! ## E2 clause (N1) as one further hypothesis field (audit §3)

**E2** — Ishiki, *A factorization of metric spaces*, Colloq. Math. 174 (2023),
101–120 (arXiv:2212.13409), Theorem 4.7 — supplies clauses (1), (2), (5), which
are the three data fields of `IsUltraIsometricExtensor` (`Ext/UltraGeneral.lean`).
Its clause **(N1)** reads: *if `X` is completely metrizable, the auxiliary data
can be chosen so that `Σ(Cm(F)) ⊆ Cm(X)` and `Σ(UCM(F;S)) ⊆ UCM(X;S)`.*

Two things about that quotation are load-bearing and are encoded literally
below.  (N1) is a clause of the **same** extensor, so it is a field of a
structure extending the 3.14 bundle rather than a second, unrelated hypothesis.
And (N1) is available **only** for a completely metrizable ambient, so the
bundle carries that hypothesis explicitly; Corollary 3.17 discharges it from its
own nonemptiness hypothesis.  Nothing here is a `UCPM`-level extensor — E2 has
none, which is exactly why the transfer needs the repair. -/

/-- **E2 with clause (N1)**, for a completely metrizable ambient: the isometric
extensor of `Ext/UltraGeneral.lean` also carries complete compatible `R`-valued
ultrametrics to complete compatible `R`-valued ultrametrics.

The complete-metrizability hypothesis is an explicit argument rather than an
instance, because in Corollary 3.17 it is *derived* — from nonemptiness of
`UComp(Y;R)` — and so is not available when the corollary's E2 hypothesis is
stated.  The field is literally (N1)'s `Σ(UCM(F;R)) ⊆ UCM(Y;R)` restricted to
the extensor's actual domain, and it is a hypothesis, never an axiom. -/
structure IsUltraCompIsometricExtensor {Z Y : Type*} (tZ : TopologicalSpace Z)
    [TopologicalSpace Y] (hY : TopologicalSpace.IsCompletelyMetrizableSpace Y)
    (R : RangeSet) (ι : Z → Y) extends IsUltraIsometricExtensor tZ R ι where
  /-- Clause (N1): `Σ` carries the complete compatible locus into the complete
  compatible locus. -/
  ucomp_preservation : ∀ d : ↥(UMet Z R), (d : UCPM Z R) ∈ UComp Z R →
    toUCPMOn d ∈ UCompOn Y R

/-- **The audit's identity `E(UComp(Z;R)) = E(UMet(Z;R)) ∩ UComp(Y;R)`.**  The
inclusion `⊆` is clause (N1); the reverse inclusion is the restriction argument
of audit §3 — the extension restricts along the closed embedding to the metric
it extends (`restrict_toUCPMOn`), and a complete metric restricted to a closed
subspace is complete. -/
theorem IsUltraCompIsometricExtensor.image_ucomp_eq_range_inter {Z Y : Type*}
    {tZ : TopologicalSpace Z} [TopologicalSpace Y]
    {hY : TopologicalSpace.IsCompletelyMetrizableSpace Y} {ι : Z → Y}
    (hE : IsUltraCompIsometricExtensor tZ hY R ι) :
    hE.toUCPMOn '' {d : ↥(UMet Z R) | (d : UCPM Z R) ∈ UComp Z R}
      = Set.range hE.toUCPMOn ∩ UCompOn Y R := by
  ext g
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, hE.ucomp_preservation d hd⟩
  · rintro ⟨⟨d, rfl⟩, hmem⟩
    refine ⟨d, ⟨d.2, ?_⟩, rfl⟩
    have hcomplete : IsCompleteMetricOn
        (UCPMOn.restrict ι (hE.toIsUltraIsometricExtensor.toUCPMOn d)).1 :=
      isCompleteMetricOn_restrict_of_mem_UCompOn tZ
        hE.toIsUltraIsometricExtensor.closedEmbedding hmem
    rwa [hE.toIsUltraIsometricExtensor.restrict_toUCPMOn d] at hcomplete

/-! ## The transfer (audit §2.15, inheriting the §2.14 repair) -/

/-- Every member of the discrete witness `Ψ(2^ω ∖ S)` is complete: it is a
coding metric at a parameter off `S`, and Lemma 3.10's completeness clause
applies. -/
theorem codingWitness_subset_UComp (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    codingWitness hr S ⊆ UComp (UltraIndex S) R := by
  rw [codingWitness_eq hr S, ← preimage_UComp_phiU hr S]
  exact Set.image_preimage_subset _ _

section Extension

variable {S : Set (ℕ → Bool)} [TopologicalSpace Y] {ι : UltraIndex S → Y}
  {hY : TopologicalSpace.IsCompletelyMetrizableSpace Y}

/-- **The exact pullback identity `ῑ⁻¹(UComp(Y;R)) = P ∖ S`**, in the transported
form of audit §2.14's repair.  `⊇` is E2 clause (N1) applied to the witness,
whose members are complete; `⊆` needs nothing new — a complete compatible member
of `UCPM(Y;R)` is in particular compatible, and Theorem 3.14's pullback identity
already places the corresponding point of the closure in the witness. -/
theorem preimage_UCompOn_ultraExtend (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hE : IsUltraCompIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) hY R ι) :
    ultraExtend hr hE.toIsUltraIsometricExtensor ⁻¹' UCompOn Y R
      = Subtype.val ⁻¹' codingWitness hr S := by
  refine Set.Subset.antisymm (fun q hq => ?_) (fun q hq => ?_)
  · rw [← preimage_UMetOn_ultraExtend hR hr hE.toIsUltraIsometricExtensor]
    exact hq.1
  · show ultraExtend hr hE.toIsUltraIsometricExtensor q ∈ UCompOn Y R
    -- `q` *is* the inclusion of its own underlying point: the two differ only in
    -- the membership proof, so the identification is `rfl`.
    have hq' : q = codingInclusion hr S ⟨q.1, hq⟩ := rfl
    have hmem : ultraExtend hr hE.toIsUltraIsometricExtensor
        (codingInclusion hr S ⟨q.1, hq⟩) ∈ UCompOn Y R := by
      rw [ultraExtend_apply]
      exact hE.ucomp_preservation ⟨q.1, codingWitness_subset_UMet hr S hq⟩
        (codingWitness_subset_UComp hr S hq)
    exact hq' ▸ hmem

/-- **The trace identity `K ∩ UComp(Y;R) = E(Ψ(2^ω ∖ S))`** of the audit's
repair, with the same compact witness `K = ῑ(P)`
(`isCompact_range_ultraExtend`) that Theorem 3.14 uses. -/
theorem range_ultraExtend_inter_UCompOn (hR : R.IsCharacteristic)
    (hr : RangeSet.IsScale R r)
    (hE : IsUltraCompIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) hY R ι) :
    Set.range (ultraExtend hr hE.toIsUltraIsometricExtensor) ∩ UCompOn Y R
      = ultraExtend hr hE.toIsUltraIsometricExtensor ''
          (Subtype.val ⁻¹' codingWitness hr S) := by
  rw [← preimage_UCompOn_ultraExtend hR hr hE, Set.image_preimage_eq_inter_range,
    Set.inter_comm]

/-- **Corollary 3.17, core content**, by the repair of audit §2.14 with `Ψ`
replaced by the 3.16 witness.  A fixed E2 extensor with clause (N1) out of the
coded `ℵ₁`-sized discrete carrier forbids Borelness of `UComp(Y;R)` in
`UCPM(Y;R)`.

The proof is Theorem 3.14's end to end, with `UMet` replaced by `UComp`
throughout: the extension `ῑ` of `E ∘ Ψ` to the closure of the witness, its
exact pullback identity, and then the pullback of Borelness along the continuous
`Φ`, which returns Proposition 2.2's non-Borel `S`.  Density of `S` is consumed
in the same two places. -/
theorem IsUltraCompIsometricExtensor.not_measurableSet_UCompOn
    (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (hS : Dense S) (hSnonmeas : ¬ MeasurableSet S)
    (hE : IsUltraCompIsometricExtensor (⊥ : TopologicalSpace (UltraIndex S)) hY R ι) :
    ¬ MeasurableSet (UCompOn Y R) := by
  intro hComp
  have h1 : MeasurableSet
      (ultraExtend hr hE.toIsUltraIsometricExtensor ⁻¹' UCompOn Y R) :=
    hComp.preimage (continuous_ultraExtend hR hr hE.toIsUltraIsometricExtensor).measurable
  rw [preimage_UCompOn_ultraExtend hR hr hE] at h1
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

/-! ## Corollary 3.17 -/

/-- **Corollary 3.17 (`cor:complete-ultrametric-borel-separability`), conditional
on E2 with clause (N1).**  If `UComp(Y;R)` is nonempty and Borel in `UCPM(Y;R)`,
then `Y` is separable.

The nonemptiness hypothesis is the audited statement's own and is not
decorative: it is what makes `Y` completely metrizable
(`isCompletelyMetrizableSpace_of_mem_UCompOn`), and complete metrizability is
the hypothesis under which E2 clause (N1) holds (audit §3).  That is why `hE2`
is quantified over a proof of complete metrizability: the corollary supplies one
from `hne` and only then may invoke (N1).

`hE2` is otherwise the same shape as in Theorem 3.14: *every* closed discrete
subspace of `Y` admits such an extensor.  Quantifying rather than fixing it is
what the argument requires — the subspace is produced by the separated-set
argument only after nonseparability is assumed.  E2's own proof stays external;
it is never an axiom here.

As in Theorem 3.14 this is the **internal, bundle-conditional** form: the
preprint's standing hypothesis that `Y` is ultrametrizable does not appear,
because the repair never uses it — it is E2, here `hE2`, whose hypotheses
require it.  The printed Corollary 3.17 is
`separable_of_measurableSet_UCompOn_of_isUltrametrizableSpace`
(`Ext/UltraPublished.lean`), whose published hypotheses produce this
theorem's `hE2` via the bridge
`IsUltraCompIsometricExtensorOn.toIsUltraCompIsometricExtensor`; the printed
statement follows from this one, while this form itself — conditional on a
bundle the preprint never states — is not the printed statement. -/
theorem separable_of_measurableSet_UCompOn_of_ultraCompExtensors {Y : Type*} [MetricSpace Y]
    (hR : R.IsCharacteristic)
    (hne : (UCompOn Y R).Nonempty)
    (hComp : MeasurableSet (UCompOn Y R))
    (hE2 : ∀ (hY : TopologicalSpace.IsCompletelyMetrizableSpace Y) (Z : Type) (ι : Z → Y),
      Nonempty Z → @Topology.IsClosedEmbedding Z Y ⊥ inferInstance ι →
      Nonempty (IsUltraCompIsometricExtensor (⊥ : TopologicalSpace Z) hY R ι)) :
    TopologicalSpace.SeparableSpace Y := by
  obtain ⟨g, hg⟩ := hne
  have hY : TopologicalSpace.IsCompletelyMetrizableSpace Y :=
    isCompletelyMetrizableSpace_of_mem_UCompOn hg
  by_contra hYsep
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  obtain ⟨S, hSdense, hScard, hSnonmeas⟩ := exists_dense_aleph1_nonBorel_cantor
  obtain ⟨ι, hce⟩ :=
    exists_isClosedEmbedding_of_card_aleph_one (C := UltraIndex S) (card_ultraIndex hScard) hYsep
  obtain ⟨w, hw⟩ := hSdense.nonempty
  obtain ⟨hE⟩ := hE2 hY (UltraIndex S) ι ⟨(⟨w, hw⟩, none)⟩ hce
  exact hE.not_measurableSet_UCompOn hR hr hSdense hSnonmeas hComp

/-- **Corollary 3.17, the completely metrizable variant**, conditional on E2
with clause (N1).  If `UComp(Y;R)` is nonempty and completely metrizable, then
`Y` is separable.

Audit §2.15: "the completely-metrizable variant goes through Alexandrov as in
3.15".  `UComp(Y;R)` is a completely metrizable subspace of the metrizable
`UCPM(Y;R)`, hence `G_δ` in it by Alexandrov–Lavrentiev (E4d, Kechris Theorem
3.11, in the form of `isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace`),
hence Borel; the Borel form then applies and the variant adds nothing to it.

`Y` is metrizable here, which is *weaker* than the preprint's standing
hypothesis — the published Corollary 3.17 assumes `Y` ultrametrizable, and
the published-interface form is
`separable_of_isCompletelyMetrizableSpace_UCompOn_of_isUltrametrizableSpace`
(`Ext/UltraPublished.lean`).  The Borel form is delivered for a metric space,
so a compatible metric is chosen inside the proof, which changes nothing
because the two loci, the hypotheses and the conclusion are all properties of
the topology. -/
theorem separable_of_isCompletelyMetrizableSpace_UCompOn_of_ultraCompExtensors {Y : Type*}
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    (hR : R.IsCharacteristic)
    (hne : (UCompOn Y R).Nonempty)
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(UCompOn Y R))
    (hE2 : ∀ (hY : TopologicalSpace.IsCompletelyMetrizableSpace Y) (Z : Type) (ι : Z → Y),
      Nonempty Z → @Topology.IsClosedEmbedding Z Y ⊥ inferInstance ι →
      Nonempty (IsUltraCompIsometricExtensor (⊥ : TopologicalSpace Z) hY R ι)) :
    TopologicalSpace.SeparableSpace Y := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  exact separable_of_measurableSet_UCompOn_of_ultraCompExtensors hR hne
    (measurableSet_of_isCompletelyMetrizableSpace hMet) hE2

end

end IshikiExt
