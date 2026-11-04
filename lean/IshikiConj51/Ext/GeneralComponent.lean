-- Ext.GeneralComponent
--
-- Issue #107: the component-by-component non-Borelness statement for an
-- arbitrary nonseparable metrizable space, and the non-Borelness of `Met(X)`
-- that follows from it.
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` (§1 ambient
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
import IshikiConj51.Ext.BMetClopen
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

theorem not_measurableSet_CPMOn_component_of_isComponentControlledExtensorOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hX : ¬ TopologicalSpace.SeparableSpace X)
    (hEx : ∀ (A : Set X), IsClosed A → ∀ e : CPMOn X, e ∈ CPM.MetOn X →
      Nonempty (IsComponentControlledExtensorOn A e))
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) :
    ¬ MeasurableSet (CPMOn.component d) := by
  obtain ⟨h, htop⟩ := id hd
  letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
  have hdist : ∀ x y : X, dist x y = d.1.1 x y := fun _ _ => rfl
  obtain ⟨ε, hε, D, hDcard, hDclosed, hDdisc, hDpair, hDnet⟩ :=
    exists_aleph1_closed_discrete_separated_net hX
  letI : DiscreteTopology D := hDdisc
  obtain ⟨bundle⟩ := hEx D hDclosed d hd
  let d_D : CPMOn D := CPMOn.restrict D d
  have hd_D_bare : d_D.1 ∈ CPM.Met D := by
    apply isMetricOn_restrict_of_mem_MetOn
      (ι := (Subtype.val : D → X))
      (tA := (inferInstance : TopologicalSpace D))
      (d := d_D.1)
      (e := d)
      (hι := Topology.IsEmbedding.subtypeVal)
      (htA := DiscreteTopology.eq_bot)
      (he := hd)
      (hrestrict := fun a b => by
        simp [d_D])
  have hd_D : d_D ∈ CPM.MetOn D := by
    obtain ⟨hm, htopbot⟩ := hd_D_bare
    exact ⟨hm, htopbot.trans DiscreteTopology.eq_bot.symm⟩
  let r : CPMOn X := bundle.toExtensor.toCPM d_D
  have hr_MetOn : r ∈ CPM.MetOn X := by
    change bundle.toExtensor.toCPM d_D ∈ CPM.MetOn X
    exact bundle.toExtensor.met_preservation ⟨d_D, hd_D, rfl⟩
  have hbound : ∀ x y : X, |r.1.1 x y - d.1.1 x y| ≤ 10 * ε + 2 := by
    intro x y
    obtain ⟨a, haD, hxa⟩ := hDnet x
    obtain ⟨b, hbD, hyb⟩ := hDnet y
    have hxa' : d.1.1 x a ≤ ε := by
      rw [← hdist x a]
      exact hxa
    have hyb' : d.1.1 y b ≤ ε := by
      rw [← hdist y b]
      exact hyb
    have hra : r.1.1 x a ≤ 4 * ε + 1 := by
      have hpoint := bundle.point_estimate x ⟨a, haD⟩
      have hpoint' : r.1.1 x a ≤ 4 * d.1.1 x a + 1 := by
        simpa [r, d_D] using hpoint
      linarith [hpoint', hxa']
    have hrb : r.1.1 y b ≤ 4 * ε + 1 := by
      have hpoint := bundle.point_estimate y ⟨b, hbD⟩
      have hpoint' : r.1.1 y b ≤ 4 * d.1.1 y b + 1 := by
        simpa [r, d_D] using hpoint
      linarith [hpoint', hyb']
    have hrab : r.1.1 a b = d.1.1 a b := by
      have hext := bundle.toExtensor.extension d_D ⟨a, haD⟩ ⟨b, hbD⟩
      simpa [r, d_D] using hext
    have hrby : r.1.1 b y ≤ 4 * ε + 1 := by
      rw [r.1.2.dist_comm b y]
      exact hrb
    have hdax : d.1.1 a x ≤ ε := by
      rw [d.1.2.dist_comm a x]
      exact hxa'
    have hdyb : d.1.1 y b ≤ ε := hyb'
    have hdby : d.1.1 b y ≤ ε := by
      rw [d.1.2.dist_comm b y]
      exact hdyb
    have hrxy : r.1.1 x y ≤
        r.1.1 x a + r.1.1 a b + r.1.1 b y := by
      linarith [r.1.2.dist_triangle x a y, r.1.2.dist_triangle a b y]
    have hdab : d.1.1 a b ≤
        d.1.1 a x + d.1.1 x y + d.1.1 y b := by
      linarith [d.1.2.dist_triangle a x b, d.1.2.dist_triangle x y b]
    have hru : r.1.1 x y ≤ d.1.1 x y + 10 * ε + 2 := by
      linarith [hrxy, hra, hrby, hrab, hdab, hdax, hdyb]
    have hdxy : d.1.1 x y ≤
        d.1.1 x a + d.1.1 a b + d.1.1 b y := by
      linarith [d.1.2.dist_triangle x a y, d.1.2.dist_triangle a b y]
    have hrax : r.1.1 a x ≤ 4 * ε + 1 := by
      rw [r.1.2.dist_comm a x]
      exact hra
    have hrab_upper : r.1.1 a b ≤
        r.1.1 a x + r.1.1 x y + r.1.1 y b := by
      linarith [r.1.2.dist_triangle a x b, r.1.2.dist_triangle x y b]
    have hdown : d.1.1 x y ≤ r.1.1 x y + 10 * ε + 2 := by
      linarith [hdxy, hxa', hdby, hrab, hrab_upper, hrax, hrb]
    rw [abs_sub_le_iff]
    constructor <;> linarith [hru, hdown]
  have hed : CPM.edist d.1 r.1 ≤ ENNReal.ofReal (10 * ε + 2) := by
    apply CPM.edist_le_ofReal
    intro x y
    rw [abs_sub_comm]
    exact hbound x y
  have hed' : CPM.edist d.1 r.1 < ⊤ :=
    lt_of_le_of_lt hed ENNReal.ofReal_lt_top
  have hedOn : edist d r < ⊤ := by
    rw [CPMOn.edist_eq]
    exact hed'
  have hr_in_component_d : r ∈ CPMOn.component d := ⟨hr_MetOn, hedOn⟩
  have hcompeq : CPMOn.component r = CPMOn.component d :=
    CPMOn.component_eq_of_mem hr_in_component_d
  have hpullback : bundle.toExtensor.toCPM ⁻¹' CPMOn.component r =
      CPMOn.component d_D := bundle.toExtensor.preimage_component_eq d_D
  have hpullback_d : bundle.toExtensor.toCPM ⁻¹' CPMOn.component d =
      CPMOn.component d_D := by
    rw [← hcompeq]
    exact hpullback
  have hD_not_meas : ¬ MeasurableSet (CPMOn.component d_D) :=
    CPMOn.component_not_measurableSet hDcard d_D hd_D
  intro hmeas
  have hpre_meas : MeasurableSet
      (bundle.toExtensor.toCPM ⁻¹' CPMOn.component d) :=
    hmeas.preimage bundle.toExtensor.isometry_toCPM.continuous.measurable
  rw [hpullback_d] at hpre_meas
  exact hD_not_meas hpre_meas

theorem not_measurableSet_CPM_MetOn_of_isComponentControlledExtensorOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hX : ¬ TopologicalSpace.SeparableSpace X)
    (hEx : ∀ (A : Set X), IsClosed A → ∀ e : CPMOn X, e ∈ CPM.MetOn X →
      Nonempty (IsComponentControlledExtensorOn A e)) :
    ¬ MeasurableSet (CPM.MetOn X) := by
  intro hmeas
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let d₀ : CPMOn X :=
    ⟨⟨dist, ⟨dist_self, dist_comm, dist_triangle⟩⟩, by
      change Continuous (fun p : X × X => dist p.1 p.2)
      exact continuous_dist⟩
  have hmetric : IsMetricOn (dist : X → X → ℝ) := by
    refine ⟨dist_self, ?_, dist_comm, dist_triangle⟩
    intro x y hxy
    exact dist_eq_zero.mp hxy
  have hmetric_toMetricSpace :
      hmetric.toMetricSpace = (inferInstance : MetricSpace X) := by
    apply MetricSpace.ext
    ext x y
    rfl
  have htop : hmetric.topology = (inferInstance : TopologicalSpace X) := by
    rw [hmetric.topology_eq_metricSpace_topology, hmetric_toMetricSpace]
    with_reducible_and_instances rfl
  have hd₀ : d₀ ∈ CPM.MetOn X := by
    change ∃ h : IsMetricOn (dist : X → X → ℝ),
      h.topology = (inferInstance : TopologicalSpace X)
    exact ⟨hmetric, htop⟩
  have hnot :=
    not_measurableSet_CPMOn_component_of_isComponentControlledExtensorOn
      hX hEx d₀ hd₀
  have hcomponent : CPMOn.component d₀ =
      CPM.MetOn X ∩ {e : CPMOn X | edist d₀ e < ⊤} := by
    rfl
  have hcompmeas : MeasurableSet (CPMOn.component d₀) := by
    rw [hcomponent]
    exact hmeas.inter (isClopen_setOf_edist_lt_top d₀).isOpen.measurableSet
  exact hnot hcompmeas

/-- The inclusion of a finite-distance component into the compatible metric
space is a closed embedding.  This is the "components are clopen in
`Met(X)`" step of `notes/borel-manuscript-20260827-audit.md` §2.16, feeding
the `met ⇒ each-component` direction of Issue #108's five-way equivalence.  The
Mathlib half is that a closed subspace of a completely metrizable space is
completely metrizable. -/
theorem CPMOn.isClosedEmbedding_component_inclusion {X : Type*} [TopologicalSpace X]
    (d : CPMOn X) :
    Topology.IsClosedEmbedding
      (fun e : ↥(CPMOn.component d) =>
        (⟨(e : CPMOn X), CPMOn.component_subset_MetOn d e.2⟩ : ↥(CPM.MetOn X))) := by
  let f : ↥(CPMOn.component d) → ↥(CPM.MetOn X) := fun e =>
    ⟨(e : CPMOn X), CPMOn.component_subset_MetOn d e.2⟩
  change Topology.IsClosedEmbedding f
  have hcomponent_embedding :
      Topology.IsEmbedding (fun e : ↥(CPMOn.component d) => (e : CPMOn X)) :=
    Topology.IsEmbedding.subtypeVal
  have hcomposition :
      Topology.IsEmbedding
        ((fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ∘ f) := by
    simpa [f, Function.comp_def] using hcomponent_embedding
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.of_comp_iff
      (f := f)
      (g := (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)))
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding
          (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)))).mp hcomposition
  refine ⟨hf, ?_⟩
  have hclosed :
      IsClosed
        ((fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
          {e : CPMOn X | edist d e < ⊤}) := by
    exact (isClopen_setOf_edist_lt_top d).isClosed.preimage continuous_subtype_val
  have hrange :
      Set.range f =
        (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
          {e : CPMOn X | edist d e < ⊤} := by
    ext e
    constructor
    · rintro ⟨a, rfl⟩
      change edist d (a : CPMOn X) < ⊤
      exact a.2.2
    · intro he
      change edist d (e : CPMOn X) < ⊤ at he
      refine ⟨⟨(e : CPMOn X), ⟨e.2, he⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  rw [hrange]
  exact hclosed

/-- The closed-embedding result above feeds the Mathlib theorem that a closed
subspace of a completely metrizable space is completely metrizable.  This is
the "components are clopen in `Met(X)`" step of
`notes/borel-manuscript-20260827-audit.md` §2.16, feeding the `met ⇒
each-component` direction of Issue #108's five-way equivalence. -/
theorem CPMOn.isCompletelyMetrizableSpace_component_of_isCompletelyMetrizableSpace_MetOn
    {X : Type*} [TopologicalSpace X]
    (h : TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X)) (d : CPMOn X) :
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d) := by
  letI : TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X) := h
  exact (CPMOn.isClosedEmbedding_component_inclusion d).IsCompletelyMetrizableSpace

/-- A compatible metric exists on every metrizable topological space.  This
is the nonemptiness input for the component clauses in the
`notes/borel-manuscript-20260827-audit.md` §2.16 five-way equivalence. -/
theorem exists_mem_CPM_MetOn (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    ∃ d : CPMOn X, d ∈ CPM.MetOn X := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let d₀ : CPMOn X :=
    ⟨⟨dist, ⟨dist_self, dist_comm, dist_triangle⟩⟩, by
      change Continuous (fun p : X × X => dist p.1 p.2)
      exact continuous_dist⟩
  have hmetric : IsMetricOn (dist : X → X → ℝ) := by
    refine ⟨dist_self, ?_, dist_comm, dist_triangle⟩
    intro x y hxy
    exact dist_eq_zero.mp hxy
  have hmetric_toMetricSpace :
      hmetric.toMetricSpace = (inferInstance : MetricSpace X) := by
    apply MetricSpace.ext
    ext x y
    rfl
  have htop : hmetric.topology = (inferInstance : TopologicalSpace X) := by
    rw [hmetric.topology_eq_metricSpace_topology, hmetric_toMetricSpace]
    with_reducible_and_instances rfl
  refine ⟨d₀, ?_⟩
  change ∃ h : IsMetricOn (dist : X → X → ℝ),
    h.topology = (inferInstance : TopologicalSpace X)
  exact ⟨hmetric, htop⟩

/-- The preimage in `MetOn(X)` of every finite-distance component is open.
This is the relative-open half of the clopen-component step in
`notes/borel-manuscript-20260827-audit.md` §2.16: the `MetOn(X)` conjunct in
the component definition is automatic in this preimage, leaving the open
finite-distance locus. -/
theorem CPMOn.isOpen_val_preimage_component {X : Type*} [TopologicalSpace X]
    (d : CPMOn X) :
    IsOpen
      ((fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
        CPMOn.component d) := by
  have hpreimage :
      (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
          CPMOn.component d =
        (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
          {e : CPMOn X | edist d e < ⊤} := by
    ext e
    constructor
    · intro he
      change (e : CPMOn X) ∈ CPMOn.component d at he
      exact he.2
    · intro he
      change edist d (e : CPMOn X) < ⊤ at he
      exact ⟨e.2, he⟩
  rw [hpreimage]
  exact (isClopen_setOf_edist_lt_top d).isOpen.preimage continuous_subtype_val

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- Restriction to a subset is nonexpansive for the extended supremum distance.
This is the restriction-map estimate required in
`notes/borel-manuscript-20260827-audit.md` §2.16: the maps `r_n` in Direction A
are 1-Lipschitz. -/
theorem CPMOn.edist_restrict_le {X : Type*} [TopologicalSpace X] (A : Set X)
    (d e : CPMOn X) : edist (CPMOn.restrict A d) (CPMOn.restrict A e) ≤ edist d e := by
  change CPM.edist (CPMOn.restrict A d).1 (CPMOn.restrict A e).1 ≤ CPM.edist d.1 e.1
  change (⨆ p : (↥A) × (↥A), ENNReal.ofReal
      |d.1.1 (p.1 : X) (p.2 : X) - e.1.1 (p.1 : X) (p.2 : X)|) ≤
    ⨆ p : X × X, ENNReal.ofReal |d.1.1 p.1 p.2 - e.1.1 p.1 p.2|
  refine iSup_le fun p => ?_
  exact le_iSup (fun q : X × X => ENNReal.ofReal
    |d.1.1 q.1 q.2 - e.1.1 q.1 q.2|) ((p.1 : X), (p.2 : X))

/-- Restriction to a subset is 1-Lipschitz for the extended supremum distance.
This is the Lipschitz form of the `r_n` infrastructure in
`notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem CPMOn.lipschitzWith_restrict {X : Type*} [TopologicalSpace X] (A : Set X) :
    LipschitzWith 1 (CPMOn.restrict A : CPMOn X → CPMOn ↥A) := by
  intro d e
  rw [ENNReal.coe_one, one_mul]
  exact CPMOn.edist_restrict_le A d e

/-- Restriction to a subset is continuous.  This is the continuity form of the
1-Lipschitz restriction maps `r_n` required in
`notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem CPMOn.continuous_restrict {X : Type*} [TopologicalSpace X] (A : Set X) :
    Continuous (CPMOn.restrict A : CPMOn X → CPMOn ↥A) :=
  (CPMOn.lipschitzWith_restrict A).continuous

end
end IshikiExt
