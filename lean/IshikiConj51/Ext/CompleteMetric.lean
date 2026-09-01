-- Ext.CompleteMetric
--
-- Theorem 3.8 and Corollary 3.9 of the Borel preprint (arXiv:2608.19618):
-- the complete-metric branch.  For a discrete `Z` with `|Z| ≥ ℵ₁` every
-- component of `Met(Z)` meets `Comp(Z)` in a non-Borel set, hence `Comp(Z)`
-- itself is non-Borel; and for a completely metrizable `X`, Borelness of
-- `Comp(X)` in `CPM(X)` forces `X` to be separable.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.11
-- (Theorem 3.8, verdict FIX, with the repair formalised here), §2.12
-- (Corollary 3.9) and §3 (E1, whose clause (4) is the external input of 3.9).
--
-- **What the printed proof of 3.8 gets wrong, and what is formalised instead.**
-- The preprint amalgamates the star coding with an arbitrary representative
-- `d` of the component and asserts the amalgam is complete for `t ∉ S`.  Audit
-- §2.11 records that this is false as written: `m_t` restricted to
-- `(Z ∖ E) ∪ {z}` is `d`, which need not be complete, and the audit exhibits a
-- component where it is not.  The repair, which is what the development below
-- formalises, replaces the base by `d' := d + 1` off the diagonal — a complete
-- compatible metric at supremum distance `1` from `d`, hence in the same
-- component — and then proves completeness of the amalgam with that base.
-- The false step is not formalised anywhere.
--
-- The "consequently `Comp(Z)` is non-Borel" part likewise follows the audit:
-- it runs on the trace `L' ∩ Comp(Z) = Ψ([0,1] ∖ S)`, i.e. on the pullback
-- identity `Ψ⁻¹(Comp(Z)) = [0,1] ∖ S`, and **not** by intersecting with the
-- component, which is itself non-Borel.
--
-- The three completeness ingredients (normalised base, coding metrics,
-- amalgam) are in `Ext/Completeness.lean`; the component/amalgamation
-- machinery is `Ext/Component.lean` and `Ext/Amalgam.lean`, reused unchanged.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Completeness
import IshikiConj51.Ext.CompleteMetrizability

open Cardinal Set

namespace IshikiExt

noncomputable section

-- The measurable-space constants of `Ext.Component` and
-- `Ext.GeneralSeparability` are `local instance`s there, so they are
-- re-registered here.  They are the same constants — both unfold to `borel _`
-- — so `MeasurableSet` below means what it means in
-- `component_not_measurableSet` and in the transfer theorems.
attribute [local instance] componentCpmMeasurableSpace componentCpmBorelSpace
attribute [local instance] cpmOnMeasurableSpace cpmOnBorelSpace

variable {Z : Type*}

/-! ## The normalised component setup (audit §2.11)

`ComponentSetup` (`Ext/Component.lean`) bundles the data of the Theorem 3.4
construction: a base metric, an uncountable closed ball around a point, and a
relabelling of that ball onto the coded carrier.  Theorem 3.8 needs one more
property of the base, and only one: that it is complete.  It is added as a
field of an extending structure rather than to `ComponentSetup` itself,
because Theorem 3.4 holds for an arbitrary representative of the component and
must not acquire a hypothesis it does not need. -/

/-- The Theorem 3.4 setup with a **complete** base metric, which is what audit
§2.11's repair produces.  `exists_completeComponentSetup` builds one for every
component, by normalising an arbitrary representative. -/
structure CompleteComponentSetup (Z : Type*) extends ComponentSetup Z where
  /-- Audit §2.11: the base metric of the setup is complete.  This is the
  hypothesis the printed proof of Theorem 3.8 omits. -/
  hdcomplete : IsCompleteMetricOn d

namespace CompleteComponentSetup

variable (c : CompleteComponentSetup Z)

/-- The transported coding is complete for `t ∉ S`: completeness is a
relabelling invariant, and `d_t` is complete (audit §2.11). -/
theorem isCompleteMetricOn_ballMetric {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htS : t ∉ c.S) : IsCompleteMetricOn (c.ballMetric t) :=
  (isCompleteMetricOn_comap_iff c.θ (dExt c.S t)).mpr
    (isCompleteMetricOn_dExt c.hS ht htS)

/-- **The amalgam is complete for `t ∉ S`** — the step the printed proof gets
wrong, here with the normalised base of audit §2.11.  The uniform gap at the
glue point is `hout`, the setup's own field: every point outside `E` is at
base distance at least `1` from `z`. -/
theorem isCompleteMetricOn_metric {t : UnitParam} (htS : (t : ℝ) ∉ c.S) :
    IsCompleteMetricOn (c.metric t) :=
  isCompleteMetricOn_amalgam c.hz c.hd (c.isMetricOn_ballMetric t.2) c.hdbot
    c.hdcomplete (c.isCompleteMetricOn_ballMetric t.2 htS) one_pos c.hout

/-- The complete-metric analogue of `mem_Met_psi_iff`: the amalgam is a
complete compatible metric exactly when `t ∉ S`.  At `t ∈ S` it already fails
to be compatible, so it fails to lie in `Comp(Z) ⊆ Met(Z)`. -/
theorem mem_Comp_psi_iff (t : UnitParam) : c.psi t ∈ CPM.Comp Z ↔ (t : ℝ) ∉ c.S := by
  constructor
  · rintro ⟨hmet, -⟩
    exact (c.mem_Met_psi_iff t).mp hmet
  · intro htS
    exact ⟨(c.mem_Met_psi_iff t).mpr htS, c.isCompleteMetricOn_metric htS⟩

/-- **The pullback identity for `Comp(Z)`** `Ψ⁻¹(Comp(Z)) = [0,1] ∖ S`.  This
is the identity audit §2.11 identifies as the correct reading of the
preprint's "consequently": it does not mention the component at all. -/
theorem preimage_Comp_psi : c.psi ⁻¹' CPM.Comp Z = {t : UnitParam | (t : ℝ) ∉ c.S} := by
  ext t
  exact c.mem_Comp_psi_iff t

/-- The pullback identity for `𝔠 ∩ Comp(Z)`.  It is the same set of
parameters: the finite-distance clause of the component holds for every
parameter (`edist_psi_base_lt_top`), so it imposes no condition. -/
theorem preimage_component_inter_Comp_psi :
    c.psi ⁻¹' (CPM.component c.base ∩ CPM.Comp Z) = {t : UnitParam | (t : ℝ) ∉ c.S} := by
  rw [Set.preimage_inter, c.preimage_component_psi, c.preimage_Comp_psi, Set.inter_self]

/-- **The compact-witness trace identity** `L' ∩ Comp(Z) = Ψ([0,1] ∖ S)`
(audit §2.11).  The compact witness is `isCompact_range_psi`. -/
theorem range_inter_Comp :
    Set.range c.psi ∩ CPM.Comp Z = c.psi '' {t : UnitParam | (t : ℝ) ∉ c.S} := by
  rw [← c.preimage_Comp_psi, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- `L' ∩ (𝔠 ∩ Comp(Z)) = Ψ([0,1] ∖ S)`: the same trace, which is why the
component version and the component-free version reach the same
contradiction. -/
theorem range_inter_component_inter_Comp :
    Set.range c.psi ∩ (CPM.component c.base ∩ CPM.Comp Z)
      = c.psi '' {t : UnitParam | (t : ℝ) ∉ c.S} := by
  rw [← c.preimage_component_inter_Comp_psi, Set.image_preimage_eq_inter_range,
    Set.inter_comm]

/-- The obstruction for one setup, component-free form. -/
theorem not_measurableSet_Comp (hSnonmeas : ¬ MeasurableSet c.S) :
    ¬ MeasurableSet (CPM.Comp Z) := by
  intro hmeas
  have hpre : MeasurableSet (c.psi ⁻¹' CPM.Comp Z) := hmeas.preimage c.measurable_psi
  rw [c.preimage_Comp_psi] at hpre
  exact hSnonmeas
    (measurableSet_of_measurableSet_image c.hS (measurableSet_Icc.subtype_image hpre))

/-- The obstruction for one setup, component form. -/
theorem not_measurableSet_component_inter_Comp (hSnonmeas : ¬ MeasurableSet c.S) :
    ¬ MeasurableSet (CPM.component c.base ∩ CPM.Comp Z) := by
  intro hmeas
  have hpre : MeasurableSet (c.psi ⁻¹' (CPM.component c.base ∩ CPM.Comp Z)) :=
    hmeas.preimage c.measurable_psi
  rw [c.preimage_component_inter_Comp_psi] at hpre
  exact hSnonmeas
    (measurableSet_of_measurableSet_image c.hS (measurableSet_Icc.subtype_image hpre))

end CompleteComponentSetup

/-! ## Normalising an arbitrary representative (audit §2.11) -/

/-- **The repair, as a construction.**  Every component of `Met(Z)` on a
carrier of cardinality at least `ℵ₁` is the component of a *complete*
compatible metric, and carries the whole Theorem 3.4 setup over that metric.

This reuses `Ext/Component.lean`'s shared `exists_componentSetup` (the "share
the construction" step of the v2 ruling): that lemma already builds the
`ComponentSetup` over the normalised base `addOneOffDiag d`, so the only work
here is adding the completeness field, via the equality `c.d = addOneOffDiag
d.1` that `exists_componentSetup` exposes for exactly this purpose. -/
theorem exists_completeComponentSetup (hZ : aleph 1 ≤ #Z) (d : CPM Z)
    (hd : d ∈ CPM.Met Z) :
    ∃ c : CompleteComponentSetup Z,
      ¬ MeasurableSet c.S ∧ CPM.component c.base = CPM.component d := by
  obtain ⟨c, hcd, hSnonmeas, hbase⟩ := exists_componentSetup hZ d hd
  refine ⟨{ S := c.S
            hS := c.hS
            d := c.d
            hd := c.hd
            hdbot := c.hdbot
            E := c.E
            z := c.z
            hz := c.hz
            H := c.H
            hE := c.hE
            hout := c.hout
            θ := c.θ
            hθz := c.hθz
            hdcomplete := hcd ▸ isCompleteMetricOn_addOneOffDiag hd.1 }, hSnonmeas, hbase⟩

/-! ## Theorem 3.8 -/

/-- **Theorem 3.8** (audit §2.11), in the form "every representative
determines a component whose complete part is non-Borel", carrying the same
`|Z| ≥ ℵ₁` generalisation as Theorem 3.4 v2 (audit §7.5): the *published*
Theorem 3.8 is for `|Z| = ℵ₁`, and the `≥` form here is a Lean-only
consequence of sharing `exists_componentSetup`'s construction, not an
audited v2 change to the source statement.  For a discrete carrier `Z` with
`|Z| ≥ ℵ₁` and any `d ∈ Met(Z)`, the complete compatible metrics at finite
supremum distance from `d` do not form a Borel subset of `CPM(Z)`.

The base metric of the construction is not `d` but its normalisation
`addOneOffDiag d` (audit §2.11), which represents the same component; the
printed proof's use of an arbitrary base is the step the audit rejects. -/
theorem component_inter_comp_not_measurableSet (hZ : aleph 1 ≤ #Z) (d : CPM Z)
    (hd : d ∈ CPM.Met Z) : ¬ MeasurableSet (CPM.component d ∩ CPM.Comp Z) := by
  obtain ⟨c, hSnonmeas, hbase⟩ := exists_completeComponentSetup hZ d hd
  rw [← hbase]
  exact c.not_measurableSet_component_inter_Comp hSnonmeas

/-- **Theorem 3.8, quantified over every component** (Lean generalisation to
`|Z| ≥ ℵ₁`, forced by sharing `exists_componentSetup` with Theorem 3.4 v2 —
see `notes/borel-preprint-audit.md` §7.5; the *published* Theorem 3.8 is
stated for `|Z| = ℵ₁`, and this file does not audit a v2 change to it).  For a
discrete carrier `Z` with `|Z| ≥ ℵ₁`, *every* component `𝔠 ∈ 𝐌_{<∞}(Z)` has
`𝔠 ∩ Comp(Z)` non-Borel in `CPM(Z)`. -/
theorem componentSet_inter_comp_not_measurableSet (hZ : aleph 1 ≤ #Z)
    (comp : CPM.Components Z) :
    ¬ MeasurableSet (CPM.componentSet comp ∩ CPM.Comp Z) := by
  refine Quotient.inductionOn comp fun d => ?_
  rw [CPM.componentSet_mk]
  exact component_inter_comp_not_measurableSet hZ d.1 d.2

/-- **Theorem 3.8, the "consequently" part.**  For a discrete carrier `Z` with
`|Z| ≥ ℵ₁`, the complete compatible metrics `Comp(Z)` are not Borel in
`CPM(Z)`.

Audit §2.11: this does *not* follow by intersecting with a component, which is
itself non-Borel.  It follows from the trace identity
`Ψ⁻¹(Comp(Z)) = [0,1] ∖ S`, which is what `not_measurableSet_Comp` runs on;
the component plays no role, and the setup is built over the `0/1` metric
purely to have one. -/
theorem comp_not_measurableSet (hZ : aleph 1 ≤ #Z) : ¬ MeasurableSet (CPM.Comp Z) := by
  obtain ⟨c, hSnonmeas, -⟩ :=
    exists_completeComponentSetup hZ (CPM.discrete Z) (CPM.discrete_mem_Met Z)
  exact c.not_measurableSet_Comp hSnonmeas

/-- Neither statement of Theorem 3.8 is vacuous: a non-Borel set is nonempty,
so every component does meet `Comp(Z)` (audit §2.12 records this as part of
3.8's conclusion, which is what Corollary 3.9 uses). -/
theorem nonempty_component_inter_comp (hZ : aleph 1 ≤ #Z) (d : CPM Z)
    (hd : d ∈ CPM.Met Z) : (CPM.component d ∩ CPM.Comp Z).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  exact component_inter_comp_not_measurableSet hZ d hd (hempty ▸ MeasurableSet.empty)

/-! ## E1 clause (4)

`IsIsometricExtensorOn` (`Ext/GeneralSeparability.lean`) carries E1's clauses
(1), (2) and the inclusion half of its "furthermore" clause;
`IsBddIsometricExtensorOn` (`Ext/CompleteMetrizability.lean`) adds clause (3).
Corollary 3.9 needs clause (4), `E(Comp(A)) ⊆ Comp(X)`, of the *same*
extensor, so it is added the same way — as a field of an extending structure,
not as a second unrelated hypothesis.

**The audit §3 caveat, and how it is encoded.**  Clause (4) is printed in the
source without any hypothesis on `X`, but it cannot hold in that generality:
`X = ℚ`, `A = {0}` has `Comp(A) ≠ ∅` and `Comp(X) = ∅`.  The source's own
proof carries "`X` completely metrizable", and that is where its auxiliary
complete metrics come from.  The structure below therefore carries
`IsCompletelyMetrizableSpace X` as an instance hypothesis, so the bundle
cannot be asserted outside the range in which E1 justifies it; the preprint
uses (4) only in Corollary 3.9, where `X` is completely metrizable anyway. -/

/-- **E1 with clause (4), for one closed subset, under the hypothesis its
source proof carries.**  Ishiki, *An isometric extensor of metrics*,
arXiv:2407.03030, Theorem 1.1, clauses (1), (2), (4) and the "furthermore"
clause: for a completely metrizable `X` the isometric extensor of continuous
pseudometrics also carries complete compatible metrics to complete compatible
metrics.

Since `Ẽ|_{Met(A)} = E` and `Comp(A) ⊆ Met(A)`, the field below is literally
E1's `E(Comp(A)) ⊆ Comp(X)`.  It is never strengthened beyond that, and it is
a hypothesis, never an axiom. -/
structure IsCompIsometricExtensorOn {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] (A : Set X)
    extends IsIsometricExtensorOn A where
  comp_preservation : toCPM '' CPM.CompOn ↥A ⊆ CPM.CompOn X

/-- Clause (4) survives the transport of
`IsIsometricExtensorOn.toIsIsometricExtensor`, exactly as clause (3) does in
`IsBddIsometricExtensorOn.image_bmet_subset`: the transported extensor is the
E1 extensor precomposed with the relabelling `CPMOn.comap` and the
discrete-carrier equivalence `CPMOn.equivCPM`, and both preserve the complete
locus (`CPMOn.preimage_CompOn_comap`, `CPMOn.preimage_equivCPM_comp`). -/
theorem IsCompIsometricExtensorOn.image_comp_subset {A X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] {ι : A → X}
    (hι : @Topology.IsClosedEmbedding A X ⊥ inferInstance ι)
    (hE : IsCompIsometricExtensorOn (Set.range ι)) :
    (hE.toIsIsometricExtensorOn.toIsIsometricExtensor hι).toCPM ''
        CPM.Comp A ⊆ CPM.CompOn X := by
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  let σ : A ≃ₜ ↥(Set.range ι) := hι.toIsEmbedding.toHomeomorph
  haveI : DiscreteTopology ↥(Set.range ι) := σ.symm.isEmbedding.discreteTopology
  rintro e ⟨d, hd, rfl⟩
  show hE.toCPM (CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d)) ∈ CPM.CompOn X
  refine hE.comp_preservation
    ⟨CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d), ?_, rfl⟩
  have hCompOn : (CPMOn.equivCPM A).symm d ∈ CPM.CompOn A := by
    rw [← CPMOn.preimage_equivCPM_comp A]
    show CPMOn.equivCPM A ((CPMOn.equivCPM A).symm d) ∈ CPM.Comp A
    rw [IsometryEquiv.apply_symm_apply]
    exact hd
  rw [← CPMOn.preimage_CompOn_comap σ.symm] at hCompOn
  exact hCompOn

/-! ## The complete Borel transfer (audit §2.12) -/

/-- The `Comp` analogue of `IsIsometricExtensor.image_met_eq_range_inter`:
`E(Comp(A)) = Ẽ(CPM(A)) ∩ Comp(X)`.

The inclusion `⊆` is E1 clause (4), supplied as `hcomp`.  The reverse
inclusion is derived, and is where audit §3's "restriction of a complete
metric to a closed subspace is complete" enters: the compatible-metric half is
the `Met` identity, and the completeness half is `isCompleteMetricOn_restrict`
applied to the closed embedding the bundle carries. -/
theorem IsIsometricExtensor.image_comp_eq_range_inter {A X : Type*}
    {tA : TopologicalSpace A} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {ι : A → X}
    (hE : IsIsometricExtensor tA ι)
    (hcomp : hE.toCPM '' CPM.Comp A ⊆ CPM.CompOn X) :
    hE.toCPM '' CPM.Comp A = Set.range hE.toCPM ∩ CPM.CompOn X := by
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, hcomp ⟨d, hd, rfl⟩⟩
  · rintro ⟨⟨d, rfl⟩, hmem⟩
    refine ⟨d, ⟨?_, ?_⟩, rfl⟩
    · have hmemMet : hE.toCPM d ∈ hE.toCPM '' CPM.Met A := by
        rw [hE.image_met_eq_range_inter]
        exact ⟨⟨d, rfl⟩, hmem.1⟩
      obtain ⟨d', hd', hdd'⟩ := hmemMet
      rwa [← hE.isometry_toCPM.injective hdd']
    · obtain ⟨hm, htop⟩ := hmem.1
      exact isCompleteMetricOn_restrict hE.closedEmbedding hm htop hmem.2
        (hE.extension d)

/-- **The `Comp` analogue of Theorem 3.5 (audit §2.12), bundle form.**  An
isometric extensor from the coded `ℵ₁`-sized discrete carrier into `X` that
preserves the complete locus forbids Borelness of `Comp(X)` in `CPM(X)`.

The proof is §2.8's chain with `Comp` in place of `Met`: the domain `CPM(Z)`
is complete, so the isometric image is closed, hence Borel; intersecting with
the hypothesis and pulling back along the extensor makes `Comp(Z)` Borel in
`CPM(Z)`, contradicting Theorem 3.8's component-free consequence.  As audit
§2.12 notes, the component-free variant suffices, so no component is
intersected anywhere in this chain. -/
theorem IsIsometricExtensor.not_measurableSet_CPM_CompOn {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {S : Set ℝ} (hScard : #(↥S) = Cardinal.aleph 1)
    {ι : ExtIndex S → X}
    (hE : IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S)) ι)
    (hcomp : hE.toCPM '' CPM.Comp (ExtIndex S) ⊆ CPM.CompOn X) :
    ¬ MeasurableSet (CPM.CompOn X) := by
  intro hComp
  have hclosed : IsClosed (Set.range hE.toCPM) :=
    isClosed_range_of_isometry_complete _ hE.isometry_toCPM
  have hinter : MeasurableSet (Set.range hE.toCPM ∩ CPM.CompOn X) :=
    hclosed.measurableSet.inter hComp
  rw [← hE.image_comp_eq_range_inter hcomp] at hinter
  have hpre : MeasurableSet (hE.toCPM ⁻¹' (hE.toCPM '' CPM.Comp (ExtIndex S))) :=
    hinter.preimage hE.isometry_toCPM.continuous.measurable
  rw [Set.preimage_image_eq _ hE.isometry_toCPM.injective] at hpre
  exact comp_not_measurableSet (card_extIndex hScard).ge hpre

/-- **The `Comp` analogue of Theorem 3.5, conditional on E1.**  For a
completely metrizable `X` admitting a closed discrete copy of the coded
`ℵ₁`-sized carrier, E1 with clause (4) forbids Borelness of `Comp(X)` in
`CPM(X)`.

`hE1` is E1's statement for `X`, clauses (1), (2), (4): a hypothesis, never an
axiom.  Complete metrizability of `X` is carried by the bundle, per the audit
§3 caveat on clause (4). -/
theorem not_measurableSet_CPM_CompOn_of_compIsometricExtensorOn {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X]
    {S : Set ℝ} (hScard : #(↥S) = Cardinal.aleph 1)
    {ι : ExtIndex S → X}
    (hι : @Topology.IsClosedEmbedding (ExtIndex S) X ⊥ inferInstance ι)
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsCompIsometricExtensorOn A)) :
    ¬ MeasurableSet (CPM.CompOn X) := by
  letI : TopologicalSpace (ExtIndex S) := ⊥
  obtain ⟨hE⟩ := hE1 (Set.range ι) hι.isClosed_range
  exact (hE.toIsIsometricExtensorOn.toIsIsometricExtensor
    hι).not_measurableSet_CPM_CompOn hScard (hE.image_comp_subset hι)

/-! ## Corollary 3.9 -/

/-- **Corollary 3.9 (`cor:complete-metric-borel-separability`), conditional on
E1.**  For a **completely metrizable** `X`: if `Comp(X)` is Borel in `CPM(X)`,
then `X` is separable.

Audit §2.12.  Nonseparability produces a closed discrete copy of the coded
`ℵ₁`-sized carrier (`exists_isClosedEmbedding_extIndex`), E1 clause (4)
carries `Comp` of that copy into `Comp(X)`, and the closed isometric image
pulls a Borel `Comp(X)` back to a Borel `Comp(Z)` — contradicting Theorem 3.8
as repaired.  The extensor is quantified over closed subsets rather than
fixed, because the subspace is only available after nonseparability is
assumed.

The complete-metrizability hypothesis is the corollary's own, and it is also
what makes E1 clause (4) legitimate (audit §3); the parameter set is produced
internally by `exists_aleph1_nonBorel`, so nothing about it survives into the
statement.  A compatible metric is chosen inside the proof because the
separated-set lemma needs distances; both hypothesis and conclusion are
properties of the topology, so nothing depends on the choice. -/
theorem separable_of_measurableSet_CPM_CompOn_of_compIsometricExtensorOn {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X]
    (hComp : MeasurableSet (CPM.CompOn X))
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsCompIsometricExtensorOn A)) :
    TopologicalSpace.SeparableSpace X := by
  by_contra hX
  obtain ⟨S, -, hScard, -⟩ := exists_aleph1_nonBorel
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨ι, hce⟩ := exists_isClosedEmbedding_extIndex (S := S) hScard hX
  exact not_measurableSet_CPM_CompOn_of_compIsometricExtensorOn hScard hce hE1 hComp

end
end IshikiExt
