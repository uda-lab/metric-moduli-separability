-- Ext.GeneralComponent
--
-- Issue #107: the component-by-component non-Borelness statement for an
-- arbitrary nonseparable metrizable space, and the non-Borelness of `Met(X)`
-- that follows from it.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` (§1 ambient
-- and component conventions, §2.7 for the discrete input, §3 for the external
-- dependencies).  The statement being formalised is the 2026-08-27 received
-- manuscript's `cor:nonseparable-metric-nonborel`; the discrete input is
-- `Ext/Component.lean`'s `component_not_measurableSet` in its `ℵ₁ ≤ #Z` form.
--
-- Nothing here strengthens the E1 bundle `IsIsometricExtensorOn` of
-- `Ext/GeneralSeparability.lean`: the construction-controlled extensor is a
-- separate structure that *contains* an ordinary E1 bundle, and no existing
-- theorem acquires it as a hypothesis.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Component
import IshikiConj51.Ext.GeneralSeparability

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

-- `componentCpmMeasurableSpace`/`componentCpmBorelSpace` are the `local`
-- instances under which `Ext.Component`'s statements were elaborated, and
-- `cpmOnMeasurableSpace`/`cpmOnBorelSpace` are the ones
-- `Ext.GeneralSeparability` uses for the preprint's ambient.  A `local`
-- attribute does not survive an import, so both pairs are re-registered here;
-- they are the same constants, so the σ-algebras are the ones in the imported
-- statements.
attribute [local instance] componentCpmMeasurableSpace componentCpmBorelSpace
  cpmOnMeasurableSpace cpmOnBorelSpace

/-! ## Restricting a continuous pseudometric to a subspace -/

/-- The restriction of a continuous pseudometric on `X` to a subspace `A`.

The manuscript's component argument feeds the extensor with `d|_{A²}` for a
compatible `d` on `X`, and states the point estimate for the extension of that
particular restriction; this is the map `d ↦ d|_{A²}`. -/
def CPMOn.restrict {X : Type*} [TopologicalSpace X] (A : Set X) (d : CPMOn X) :
    CPMOn ↥A :=
  ⟨⟨fun a b => d.1.1 ↑a ↑b,
    { dist_self := fun a => d.1.2.dist_self ↑a
      dist_comm := fun a b => d.1.2.dist_comm ↑a ↑b
      dist_triangle := fun a b c => d.1.2.dist_triangle ↑a ↑b ↑c }⟩, by
    have huncurry : Function.uncurry (fun a b : ↥A => d.1.1 ↑a ↑b)
        = Function.uncurry d.1.1 ∘
          Prod.map (Subtype.val : ↥A → X) (Subtype.val : ↥A → X) := rfl
    rw [huncurry]
    exact d.2.comp (continuous_subtype_val.prodMap continuous_subtype_val)⟩

@[simp] theorem CPMOn.restrict_apply {X : Type*} [TopologicalSpace X] (A : Set X)
    (d : CPMOn X) (a b : ↥A) : (CPMOn.restrict A d).1.1 a b = d.1.1 ↑a ↑b := rfl

/-! ## The construction-controlled extensor bundle -/

/-- **The construction-controlled isometric extensor.**

An ordinary E1 extensor for the closed set `A`, together with the point
estimate that Ishiki's *construction* satisfies when the ambient metric `d` and
its restriction `d|_{A²}` are chosen as the base metrics.

Provenance, field by field.  `toExtensor` is E1 as audited
(`notes/borel-preprint-audit.md` §3), unchanged and unstrengthened.
`point_estimate` is **E1c** (same note, §3): Ishiki, *An isometric extensor of
metrics*, arXiv:2407.03030 **v4**, **Lemma 4.4**, printed p. 24, which gives
`L(J(x), J(y)) ≤ 4 w(x,y) + 1` for every `x` in the ambient space and every
`y` in the closed subset, `w` being the ambient base metric.  The owner's
primary-source verification of that printed bound is recorded on
uda-lab/metric-moduli-separability#111.

**E1c is construction-specific data taken from the proof of Theorem 1.1, not a
consequence of the theorem-level statement.**  E1 and E2 are theorem-level
bundles quantifying over extensors abstractly; Lemma 4.4 is an estimate
satisfied by the particular map built inside Theorem 1.1's proof, and it must
not be conflated with either — that is what the `c` suffix of the label
records.  It is also why the estimate is carried by a *new* structure
containing an `IsIsometricExtensorOn` rather than by a new field on it: adding
a field would silently strengthen every existing consumer of E1, and
`Ext/GeneralSeparability.lean`'s Route M transfer must keep the E1 it was
audited against.

The estimate is stated only for the extension of `CPMOn.restrict A d`, which
is the only member of `CPM(A)` the manuscript's argument applies it to. -/
structure IsComponentControlledExtensorOn {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set X) (d : CPMOn X) where
  toExtensor : IsIsometricExtensorOn A
  point_estimate : ∀ (x : X) (a : ↥A),
    (toExtensor.toCPM (CPMOn.restrict A d)).1.1 x ↑a ≤ 4 * d.1.1 x ↑a + 1

/-! ## Components of `MetOn(X)` -/

/-- The finite-distance component of `d` in the topology-aware metric locus.
For a discrete carrier this is transported from `CPM.component` along the
isometric equivalence `CPMOn.equivCPM`. -/
def CPMOn.component {X : Type*} [TopologicalSpace X] (d : CPMOn X) : Set (CPMOn X) :=
  {e | e ∈ CPM.MetOn X ∧ edist d e < ⊤}

theorem CPMOn.component_subset_MetOn {X : Type*} [TopologicalSpace X] (d : CPMOn X) :
    CPMOn.component d ⊆ CPM.MetOn X :=
  fun _ he => he.1

theorem CPMOn.self_mem_component {X : Type*} [TopologicalSpace X] {d : CPMOn X}
    (hd : d ∈ CPM.MetOn X) : d ∈ CPMOn.component d :=
  ⟨hd, by rw [edist_self]; exact ENNReal.zero_lt_top⟩

/-- The components partition `MetOn(X)`: any member of a component determines
the same component. -/
theorem CPMOn.component_eq_of_mem {X : Type*} [TopologicalSpace X] {d e : CPMOn X}
    (he : e ∈ CPMOn.component d) : CPMOn.component e = CPMOn.component d := by
  ext f
  constructor
  · rintro ⟨hf, hef⟩
    exact ⟨hf, lt_of_le_of_lt (edist_triangle d e f)
      (ENNReal.add_lt_top.mpr ⟨he.2, hef⟩)⟩
  · rintro ⟨hf, hdf⟩
    refine ⟨hf, lt_of_le_of_lt (edist_triangle e d f)
      (ENNReal.add_lt_top.mpr ⟨?_, hdf⟩)⟩
    rw [edist_comm]
    exact he.2

/-- **Theorem 3.4, transported to the topology-aware ambient.**  For a
discrete carrier `D` with `|D| ≥ ℵ₁`, the finite-distance component of every
compatible metric is not Borel in `CPMOn D`.  This is the result
`IshikiExt.component_not_measurableSet` from `Ext/Component.lean`, transported
along `CPMOn.equivCPM D`. -/
theorem CPMOn.component_not_measurableSet {D : Type*} [TopologicalSpace D]
    [DiscreteTopology D] (hD : Cardinal.aleph 1 ≤ #D) (d : CPMOn D)
    (hd : d ∈ CPM.MetOn D) : ¬ MeasurableSet (CPMOn.component d) := by
  have hbare : d.1 ∈ CPM.Met D := by
    have hpre : d ∈ CPMOn.equivCPM D ⁻¹' CPM.Met D := by
      rw [CPMOn.preimage_equivCPM_met D]
      exact hd
    simpa only [Set.mem_preimage, CPMOn.equivCPM_apply] using hpre
  have hcomponent : CPMOn.component d =
      CPMOn.equivCPM D ⁻¹' CPM.component d.1 := by
    ext e
    change (e ∈ CPM.MetOn D ∧ edist d e < ⊤) ↔
      (CPMOn.equivCPM D e ∈ CPM.Met D ∧
        CPM.edist d.1 (CPMOn.equivCPM D e) < ⊤)
    constructor
    · rintro ⟨he, hdist⟩
      refine ⟨?_, ?_⟩
      · have he' : e ∈ CPMOn.equivCPM D ⁻¹' CPM.Met D := by
          rw [CPMOn.preimage_equivCPM_met D]
          exact he
        exact he'
      · simpa only [CPMOn.edist_eq, CPMOn.equivCPM_apply] using hdist
    · rintro ⟨he, hdist⟩
      refine ⟨?_, ?_⟩
      · have he' : e ∈ CPMOn.equivCPM D ⁻¹' CPM.Met D := he
        rw [CPMOn.preimage_equivCPM_met D] at he'
        exact he'
      · simpa only [CPMOn.edist_eq, CPMOn.equivCPM_apply] using hdist
  intro hmeas
  have hpreimage : MeasurableSet
      (CPMOn.equivCPM D ⁻¹' CPM.component d.1) := by
    rw [← hcomponent]
    exact hmeas
  have hbaremeas : MeasurableSet (CPM.component d.1) := by
    have hdouble : MeasurableSet
        ((CPMOn.equivCPM D).symm ⁻¹'
          (CPMOn.equivCPM D ⁻¹' CPM.component d.1)) :=
      hpreimage.preimage
        ((CPMOn.equivCPM D).symm.isometry.continuous.measurable)
    simpa only [Set.preimage_preimage, IsometryEquiv.apply_symm_apply,
      Set.preimage_id'] using hdouble
  exact (IshikiExt.component_not_measurableSet hD d.1 hbare) hbaremeas

/-! ## Components and the extensor -/

/-- The extensor preserves the finite-distance metric component locus in both
directions.  The reverse implication is the restriction argument from
`Ext/GeneralSeparability.lean`; the forward implication is E1's
`met_preservation` field. -/
theorem IsIsometricExtensorOn.toCPM_mem_MetOn_iff {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {A : Set X} (hE : IsIsometricExtensorOn A)
    [DiscreteTopology ↥A] (e : CPMOn ↥A) :
    hE.toCPM e ∈ CPM.MetOn X ↔ e ∈ CPM.MetOn ↥A := by
  constructor
  · intro he
    have hbare : e.1 ∈ CPM.Met ↥A :=
      isMetricOn_restrict_of_mem_MetOn
        (ι := (Subtype.val : ↥A → X))
        (tA := (inferInstance : TopologicalSpace ↥A))
        (d := e.1)
        (e := hE.toCPM e)
        (hι := Topology.IsEmbedding.subtypeVal)
        (htA := DiscreteTopology.eq_bot)
        (he := he)
        (hrestrict := hE.extension e)
    rw [← CPMOn.preimage_equivCPM_met (↥A)]
    change CPMOn.equivCPM (↥A) e ∈ CPM.Met ↥A
    simpa only [CPMOn.equivCPM_apply] using hbare
  · intro he
    exact hE.met_preservation ⟨e, he, rfl⟩

/-- The extensor pulls back the finite-distance component of an extended
metric exactly to the component of the original metric. -/
theorem IsIsometricExtensorOn.preimage_component_eq {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] {A : Set X} (hE : IsIsometricExtensorOn A)
    [DiscreteTopology ↥A] (d : CPMOn ↥A) :
    hE.toCPM ⁻¹' CPMOn.component (hE.toCPM d) = CPMOn.component d := by
  ext e
  change
    (hE.toCPM e ∈ CPM.MetOn X ∧
      edist (hE.toCPM d) (hE.toCPM e) < ⊤) ↔
      (e ∈ CPM.MetOn ↥A ∧ edist d e < ⊤)
  rw [IsIsometricExtensorOn.toCPM_mem_MetOn_iff hE e, hE.isometry_toCPM d e]

end
end IshikiExt
