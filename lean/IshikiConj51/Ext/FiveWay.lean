-- Ext.FiveWay
--
-- Issue #108: the five-way complete-metrizability/component/σ-compactness
-- equivalence for the topology-aware metric loci.
--
-- Statement gate (frozen audit record): `notes/borel-manuscript-20260827-audit.md`
-- §2.16 (statement) and §4 rows E3, E5, and E6.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.CompleteMetrizability
import IshikiConj51.Ext.GeneralComponent
import IshikiConj51.Ext.GDeltaCompletelyMetrizable
import Mathlib.Topology.FiberPartition

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

attribute [local instance] cpmMeasurableSpace cpmBorelSpace
attribute [local instance] cpmOnMeasurableSpace cpmOnBorelSpace

/-! **E5, singleton interpolation.** -/

/-- **E5 (singleton form).**  This is Ishiki, *An interpolation of metrics and
spaces of metrics*, arXiv:2003.13227 v3, Theorem 1.1, specialised to a
singleton family and retaining clauses (1)–(2) only.  The completeness clause
is not used, as recorded by the audit's hypothesis-level check in §4.

The equality of extended distances, rather than an inequality `≤`, is
load-bearing: openness of the restriction map requires a preimage at exactly
the prescribed distance.  This interpolation property is a separate,
unrelated external input and must never be merged into
`IsIsometricExtensorOn` or `IsBddIsometricExtensorOn`. -/
structure IsMetricInterpolationOn {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set X) : Prop where
  exists_interpolant : ∀ d : CPMOn X, d ∈ CPM.MetOn X →
    ∀ e : CPMOn ↥A, e ∈ CPM.MetOn ↥A →
    ∃ m : CPMOn X, m ∈ CPM.MetOn X ∧ CPMOn.restrict A m = e ∧
      edist m d = edist e (CPMOn.restrict A d)

/-- **E6, Hausdorff's open-image theorem** (via Michael–Stone, *Quotients of
the space of irrationals*, Pacific J. Math. 28 (1969), §3.4, attributed to
Hausdorff): a metrizable continuous open image of a complete metric space is
completely metrizable — no separability restriction on the image.

Absent from Mathlib at inventory date 2026-09-02 (searched
`IsCompletelyMetrizableSpace`, `IsOpenMap`, `CompleteSpace`+`Quotient`,
`Polish`, `Topology/Metrizable/CompletelyMetrizable.lean` in full: no
open-image / quotient-completeness transfer theorem of any kind).  Not an
Ishiki dependency; formalising the theorem in general is a separate future
Issue, not this one.  Stated here only in the exact instance used: domain the
finite-distance component `↥(CPMOn.component d)` (with its `𝒟_X`-metric,
assumed complete), codomain `↥(CPM.BMetOn ↥A)`. -/
abbrev HausdorffOpenImageHypothesis {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] : Prop :=
  ∀ (A : Set X), IsClosed A → ∀ (d : CPMOn X), d ∈ CPM.MetOn X →
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d) →
    ∀ (f : ↥(CPMOn.component d) → ↥(CPM.BMetOn ↥A)),
      Continuous f → IsOpenMap f → Function.Surjective f →
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn ↥A)

/-- The `met ⇒ each-component` implication in Issue #108 follows from the
closed-embedding result for components, which is the "components are clopen
in `Met(X)`" step of `notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem isCompletelyMetrizableSpace_component_of_isCompletelyMetrizableSpace_CPM_MetOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X)) :
    ∀ d : CPMOn X, d ∈ CPM.MetOn X →
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d) :=
  fun d _ =>
    CPMOn.isCompletelyMetrizableSpace_component_of_isCompletelyMetrizableSpace_MetOn hMet d

/-- **Each-component ⇒ met** in Issue #108.  By the component partition from
`Ext/GeneralComponent.lean`, `MetOn(X)` is homeomorphic to the topological
disjoint union of its finite-distance components.  The disjoint union of
completely metrizable spaces is completely metrizable, as required by the
elementary implication in `notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem isCompletelyMetrizableSpace_CPM_MetOn_of_forall_component
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hC : ∀ d : CPMOn X, d ∈ CPM.MetOn X →
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) :
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X) := by
  let g : (↥(CPM.MetOn X)) → Set (CPMOn X) :=
    fun d => CPMOn.component (d : CPMOn X)
  have hfiber_open : ∀ c : Function.Fiber g, IsOpen c.val := by
    intro c
    let d₀ : ↥(CPM.MetOn X) := c.preimage g
    have hd₀_image : g d₀ = c.image := by
      simpa [d₀] using Function.Fiber.map_preimage_eq_image g c
    have hfiber :
        c.val =
          (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
            CPMOn.component (d₀ : CPMOn X) := by
      ext e
      constructor
      · intro he
        have he' : g e = c.image :=
          (Function.Fiber.mem_iff_eq_image g e c).mp he
        change CPMOn.component (e : CPMOn X) = c.image at he'
        change CPMOn.component (d₀ : CPMOn X) = c.image at hd₀_image
        have hcomponent : CPMOn.component (e : CPMOn X) =
            CPMOn.component (d₀ : CPMOn X) := he'.trans hd₀_image.symm
        have he_self : (e : CPMOn X) ∈ CPMOn.component (e : CPMOn X) :=
          CPMOn.self_mem_component e.2
        rw [hcomponent] at he_self
        simpa only [Set.mem_preimage] using he_self
      · intro he
        apply (Function.Fiber.mem_iff_eq_image g e c).mpr
        change CPMOn.component (e : CPMOn X) = c.image
        have he' : (e : CPMOn X) ∈ CPMOn.component (d₀ : CPMOn X) := by
          simpa only [Set.mem_preimage] using he
        exact (CPMOn.component_eq_of_mem he').trans hd₀_image
    rw [hfiber]
    exact CPMOn.isOpen_val_preimage_component (d₀ : CPMOn X)
  have hsigma_open :
      IsOpenMap (TopologicalSpace.Fiber.sigmaIsoHom g) := by
    rw [isOpenMap_sigma]
    intro c
    simpa only [TopologicalSpace.Fiber.sigmaIsoHom_apply] using
      (hfiber_open c).isOpenMap_subtype_val
  let sigmaEquiv :
      (Σ c : Function.Fiber g, c.val) ≃ ↥(CPM.MetOn X) :=
    Equiv.ofBijective (TopologicalSpace.Fiber.sigmaIsoHom g)
      ⟨TopologicalSpace.Fiber.sigmaIsoHom_inj g,
        TopologicalSpace.Fiber.sigmaIsoHom_surj g⟩
  have hsigma_continuous : Continuous sigmaEquiv := by
    simpa only [sigmaEquiv, Equiv.coe_ofBijective] using
      (TopologicalSpace.Fiber.sigmaIsoHom g).continuous
  have hsigma_open_equiv : IsOpenMap sigmaEquiv := by
    simpa only [sigmaEquiv, Equiv.coe_ofBijective] using hsigma_open
  let eSigma :
      (Σ c : Function.Fiber g, c.val) ≃ₜ ↥(CPM.MetOn X) :=
    sigmaEquiv.toHomeomorphOfContinuousOpen hsigma_continuous hsigma_open_equiv
  letI : ∀ c : Function.Fiber g,
      TopologicalSpace.IsCompletelyMetrizableSpace c.val := by
    intro c
    let d₀ : ↥(CPM.MetOn X) := c.preimage g
    have hcomponent :
        TopologicalSpace.IsCompletelyMetrizableSpace
          ↥(CPMOn.component (d₀ : CPMOn X)) :=
      hC (d₀ : CPMOn X) d₀.2
    let fcomponent : ↥(CPMOn.component (d₀ : CPMOn X)) →
        ↥(CPM.MetOn X) := fun e =>
      ⟨(e : CPMOn X), CPMOn.component_subset_MetOn (d₀ : CPMOn X) e.2⟩
    have hfcomponent : Topology.IsEmbedding fcomponent := by
      simpa [fcomponent] using
        (CPMOn.isClosedEmbedding_component_inclusion (d₀ : CPMOn X)).isEmbedding
    have hd₀_image : g d₀ = c.image := by
      simpa [d₀] using Function.Fiber.map_preimage_eq_image g c
    have hfiber :
        c.val =
          (fun e : ↥(CPM.MetOn X) => (e : CPMOn X)) ⁻¹'
            CPMOn.component (d₀ : CPMOn X) := by
      ext e
      constructor
      · intro he
        have he' : g e = c.image :=
          (Function.Fiber.mem_iff_eq_image g e c).mp he
        change CPMOn.component (e : CPMOn X) = c.image at he'
        change CPMOn.component (d₀ : CPMOn X) = c.image at hd₀_image
        have hcomponent : CPMOn.component (e : CPMOn X) =
            CPMOn.component (d₀ : CPMOn X) := he'.trans hd₀_image.symm
        have he_self : (e : CPMOn X) ∈ CPMOn.component (e : CPMOn X) :=
          CPMOn.self_mem_component e.2
        rw [hcomponent] at he_self
        simpa only [Set.mem_preimage] using he_self
      · intro he
        apply (Function.Fiber.mem_iff_eq_image g e c).mpr
        change CPMOn.component (e : CPMOn X) = c.image
        have he' : (e : CPMOn X) ∈ CPMOn.component (d₀ : CPMOn X) := by
          simpa only [Set.mem_preimage] using he
        exact (CPMOn.component_eq_of_mem he').trans hd₀_image
    have hrange : Set.range fcomponent = c.val := by
      rw [hfiber]
      ext e
      constructor
      · rintro ⟨a, rfl⟩
        change (a : CPMOn X) ∈ CPMOn.component (d₀ : CPMOn X)
        exact a.2
      · intro he
        change (e : CPMOn X) ∈ CPMOn.component (d₀ : CPMOn X) at he
        refine ⟨⟨(e : CPMOn X), he⟩, ?_⟩
        apply Subtype.ext
        rfl
    have hcomponent_homeomorph :
        (↥(CPMOn.component (d₀ : CPMOn X))) ≃ₜ c.val :=
      hfcomponent.toHomeomorph.trans (Homeomorph.setCongr hrange)
    exact isCompletelyMetrizableSpace_of_homeomorph
      hcomponent_homeomorph hcomponent
  have hsigma :
      TopologicalSpace.IsCompletelyMetrizableSpace
        (Σ c : Function.Fiber g, c.val) := inferInstance
  exact isCompletelyMetrizableSpace_of_homeomorph eSigma hsigma

/-- The `each-component ⇒ some-component` implication in Issue #108 uses the
nonemptiness of `CPM.MetOn X`, as in the component clauses of
`notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem exists_isCompletelyMetrizableSpace_component_of_forall
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hC : ∀ d : CPMOn X, d ∈ CPM.MetOn X →
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) :
    ∃ d : CPMOn X, d ∈ CPM.MetOn X ∧
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d) := by
  obtain ⟨d, hd⟩ := exists_mem_CPM_MetOn X
  exact ⟨d, hd, hC d hd⟩


end
end IshikiExt

namespace IshikiExt

noncomputable section

section DirectionABalls

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [SigmaCompactSpace X] [Nonempty X]

/-! ## The closed balls used in Direction A

The `MetOn` witness is used to install a concrete metric whose topology is the
given topology on `X`.  The resulting balls are the `A_n` of
`notes/borel-manuscript-20260827-audit.md` §2.16.  The dependence on `d` and
`hd` is intentional: the boundedness argument below uses the metric values
`d.1.1` on these balls. -/

/-- The `n`th closed ball for the compatible metric selected from `hd`. -/
noncomputable def Aball (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) : Set X :=
  let h := Classical.choose (mem_CPM_MetOn.mp hd)
  let htop := Classical.choose_spec (mem_CPM_MetOn.mp hd)
  @Metric.closedBall X (h.toMetricSpace.replaceTopology htop.symm).toPseudoMetricSpace o
    (2 ^ n : ℝ)

/-- The balls `A_n` are closed, as required in the Direction A construction
of `notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem isClosed_Aball (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) :
    IsClosed (Aball d hd o n) := by
  let h := Classical.choose (mem_CPM_MetOn.mp hd)
  have htop : h.topology = (inferInstance : TopologicalSpace X) :=
    Classical.choose_spec (mem_CPM_MetOn.mp hd)
  letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
  unfold Aball
  exact Metric.isClosed_closedBall

/-- Under E3, each bounded compatible-metric locus over a ball `A_n` is
`G_δ`.  This is the `BMet(A_n)` step of Direction A in
`notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem isGδ_CPM_BMetOn_Aball
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X)
    (hE3 : ∀ A : Set X, IsClosed A → TopologicalSpace.SeparableSpace ↥A →
      (SigmaCompactSpace ↥A ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn ↥A)))
    (n : ℕ) : IsGδ (CPM.BMetOn ↥(Aball d hd o n)) := by
  let h := Classical.choose (mem_CPM_MetOn.mp hd)
  have htop : h.topology = (inferInstance : TopologicalSpace X) :=
    Classical.choose_spec (mem_CPM_MetOn.mp hd)
  letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
  have hclosed : IsClosed (Aball d hd o n) := isClosed_Aball d hd o n
  letI : SigmaCompactSpace ↥(Aball d hd o n) := hclosed.sigmaCompactSpace
  letI : TopologicalSpace.SeparableSpace ↥(Aball d hd o n) :=
    separableSpace_of_sigmaCompactSpace
  have hcomplete :
      TopologicalSpace.IsCompletelyMetrizableSpace
        ↥(CPM.BMetOn ↥(Aball d hd o n)) :=
    (hE3 (Aball d hd o n) hclosed inferInstance).mp inferInstance
  exact isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace hcomplete

/-- Restricting a member of the finite-distance component to `A_n` lands in
`BMet(A_n)`.  This is the restriction-boundedness step of Direction A in
`notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem restrict_Aball_mem_BMetOn_of_mem_component
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) (p : CPMOn X)
    (hp : p ∈ CPMOn.component d) :
    CPMOn.restrict (Aball d hd o n) p ∈
      CPM.BMetOn ↥(Aball d hd o n) := by
  let h := Classical.choose (mem_CPM_MetOn.mp hd)
  have htop : h.topology = (inferInstance : TopologicalSpace X) :=
    Classical.choose_spec (mem_CPM_MetOn.mp hd)
  letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
  have hdist : ∀ x y : X, dist x y = d.1.1 x y := fun _ _ => rfl
  obtain ⟨hp_MetOn, hp_edist⟩ := hp
  refine mem_CPM_BMetOn.mpr ⟨?_, ?_⟩
  · exact isMetricOn_restrict_of_mem_MetOn_of_topologicalSpace
      (ι := (Subtype.val : ↥(Aball d hd o n) → X)) Topology.IsEmbedding.subtypeVal
      hp_MetOn (fun a b =>
        (CPMOn.restrict_apply (Aball d hd o n) p a b).symm)
  · refine ⟨2 * (2 ^ n : ℝ) + (edist p d).toReal, ?_⟩
    intro a b
    have hp_edist' : edist p d < ⊤ := by
      rw [edist_comm]
      exact hp_edist
    have hpa :
        |p.1.1 (↑a : X) (↑b : X) - d.1.1 (↑a : X) (↑b : X)| ≤
          (edist p d).toReal := by
      have hpt : ENNReal.ofReal
          |p.1.1 (↑a : X) (↑b : X) - d.1.1 (↑a : X) (↑b : X)| ≤ edist p d := by
        rw [CPMOn.edist_eq]
        exact CPM.ofReal_abs_sub_le_edist p.1 d.1 (↑a : X) (↑b : X)
      exact (ENNReal.ofReal_le_iff_le_toReal hp_edist'.ne).mp hpt
    have ha : d.1.1 (↑a : X) o ≤ (2 ^ n : ℝ) := by
      rw [← hdist]
      exact Metric.mem_closedBall.mp (by simpa [Aball] using a.2)
    have hb : d.1.1 o (↑b : X) ≤ (2 ^ n : ℝ) := by
      rw [← hdist]
      exact Metric.mem_closedBall'.mp (by simpa [Aball] using b.2)
    have htriangle :
        d.1.1 (↑a : X) (↑b : X) ≤
          d.1.1 (↑a : X) o + d.1.1 o (↑b : X) :=
      d.1.2.dist_triangle (↑a : X) o (↑b : X)
    rw [CPMOn.restrict_apply]
    have hupper :
        p.1.1 (↑a : X) (↑b : X) ≤
          d.1.1 (↑a : X) (↑b : X) + (edist p d).toReal := by
      have hpair := abs_le.mp hpa
      linarith [hpair.2]
    linarith

end DirectionABalls

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- **Each component ⇒ BMet** in Issue #108.  This is the elementary implication
recorded in `notes/borel-manuscript-20260827-audit.md` §2.16: the bounded
compatible metrics form exactly one finite-distance component, and that
component is nonempty because `min {d, 1}` remains compatible. -/
theorem isCompletelyMetrizableSpace_CPM_BMetOn_of_forall_component
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hC : ∀ d : CPMOn X, d ∈ CPM.MetOn X →
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) :
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X) := by
  obtain ⟨d, hd⟩ := exists_mem_CPM_MetOn X
  let m : X → X → ℝ := fun x y => min (d.1.1 x y) 1
  have hm_pseudo : IsPMetricOn m := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      change min (d.1.1 x x) 1 = 0
      rw [d.1.2.dist_self x]
      norm_num
    · intro x y
      change min (d.1.1 x y) 1 = min (d.1.1 y x) 1
      rw [d.1.2.dist_comm]
    · intro x y z
      change min (d.1.1 x z) 1 ≤
        min (d.1.1 x y) 1 + min (d.1.1 y z) 1
      by_cases hxy : 1 ≤ d.1.1 x y
      · calc
          min (d.1.1 x z) 1 ≤ 1 := min_le_right _ _
          _ ≤ min (d.1.1 x y) 1 + min (d.1.1 y z) 1 := by
            rw [min_eq_right hxy]
            have hnonneg : 0 ≤ min (d.1.1 y z) 1 :=
              le_min (d.1.2.nonneg y z) (by norm_num)
            linarith
      · by_cases hyz : 1 ≤ d.1.1 y z
        · calc
            min (d.1.1 x z) 1 ≤ 1 := min_le_right _ _
            _ ≤ min (d.1.1 x y) 1 + min (d.1.1 y z) 1 := by
              rw [min_eq_right hyz]
              have hnonneg : 0 ≤ min (d.1.1 x y) 1 :=
                le_min (d.1.2.nonneg x y) (by norm_num)
              linarith
        · have hxy' : d.1.1 x y < 1 := lt_of_not_ge hxy
          have hyz' : d.1.1 y z < 1 := lt_of_not_ge hyz
          rw [min_eq_left hxy'.le, min_eq_left hyz'.le]
          exact (min_le_left _ _).trans (d.1.2.dist_triangle x y z)
  let d' : CPMOn X :=
    ⟨⟨m, hm_pseudo⟩, by
      change Continuous (Function.uncurry m)
      show Continuous (fun b : X × X => min (d.1.1 b.1 b.2) 1)
      exact d.2.min (continuous_const : Continuous (fun _ : X × X => (1 : ℝ)))⟩
  have hd'_bdd : d'.1.IsBdd := by
    refine ⟨1, ?_⟩
    intro x y
    change min (d.1.1 x y) 1 ≤ 1
    exact min_le_right _ _
  have hd'_met : d' ∈ CPM.MetOn X := by
    obtain ⟨h, htop⟩ := mem_CPM_MetOn.mp hd
    have hmin : IsMetricOn m := by
      refine ⟨hm_pseudo.dist_self, ?_, hm_pseudo.dist_comm, hm_pseudo.dist_triangle⟩
      intro x y hxy
      change min (d.1.1 x y) 1 = 0 at hxy
      have hdxy : d.1.1 x y = 0 := by
        by_cases hle : d.1.1 x y ≤ 1
        · rw [min_eq_left hle] at hxy
          exact hxy
        · have hge : 1 ≤ d.1.1 x y := le_of_not_ge hle
          have hone : (1 : ℝ) = 0 := by
            rw [min_eq_right hge] at hxy
            exact hxy
          norm_num at hone
      exact h.eq_of_dist_eq_zero hdxy
    change ∃ hm : IsMetricOn m, hm.topology = (inferInstance : TopologicalSpace X)
    refine ⟨hmin, ?_⟩
    have hforward : @Continuous X X h.topology hmin.topology id := by
      rw [h.topology_eq_metricSpace_topology,
        hmin.topology_eq_metricSpace_topology]
      refine (@Metric.continuous_iff X X
        h.toMetricSpace.toPseudoMetricSpace
        hmin.toMetricSpace.toPseudoMetricSpace id).2 ?_
      intro b ε hε
      refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
      intro a hab
      change min (d.1.1 a b) 1 < ε
      change d.1.1 a b < min ε 1 at hab
      exact (lt_of_le_of_lt (min_le_left _ _) hab).trans_le (min_le_left _ _)
    have hbackward : @Continuous X X hmin.topology h.topology id := by
      rw [hmin.topology_eq_metricSpace_topology,
        h.topology_eq_metricSpace_topology]
      refine (@Metric.continuous_iff X X
        hmin.toMetricSpace.toPseudoMetricSpace
        h.toMetricSpace.toPseudoMetricSpace id).2 ?_
      intro b ε hε
      refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
      intro a hab
      change d.1.1 a b < ε
      change min (d.1.1 a b) 1 < min ε 1 at hab
      by_cases ha : 1 ≤ d.1.1 a b
      · have hone : (1 : ℝ) < min ε 1 := by
          rw [min_eq_right ha] at hab
          exact hab
        exact False.elim ((not_lt_of_ge (min_le_right ε 1)) hone)
      · have ha' : d.1.1 a b < 1 := lt_of_not_ge ha
        rw [min_eq_left ha'.le] at hab
        exact hab.trans_le (min_le_left ε 1)
    exact (le_antisymm (continuous_id_iff_le.mp hbackward)
      (continuous_id_iff_le.mp hforward)).trans htop
  have hBMetOn_eq_component : CPM.BMetOn X = CPMOn.component d' := by
    ext e
    constructor
    · intro he
      have he' : e ∈ CPM.MetOn X ∧ e.1.IsBdd := mem_CPM_BMetOn.mp he
      refine ⟨he'.1, ?_⟩
      have hfinite : CPM.edist d'.1 e.1 < ⊤ :=
        (CPM.isBdd_iff_edist_lt_top (d := d'.1) (e := e.1) hd'_bdd).mp he'.2
      simpa only [CPMOn.edist_eq] using hfinite
    · intro he
      apply mem_CPM_BMetOn.mpr
      refine ⟨he.1, ?_⟩
      apply (CPM.isBdd_iff_edist_lt_top (d := d'.1) (e := e.1) hd'_bdd).mpr
      simpa only [CPMOn.edist_eq] using he.2
  rw [hBMetOn_eq_component]
  exact hC d' hd'_met

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- **BMet ⇒ σ-compact** in Issue #108, as recorded in
`notes/borel-manuscript-20260827-audit.md` §2.16.  The existing two-way
theorem is reused after specializing the closed-subspace-quantified `hE3` to
`A = univ`; the subtype statements are transported across the tautological
homeomorphism and the induced relabelling homeomorphism on `BMetOn`. -/
theorem sigmaCompactSpace_of_isCompletelyMetrizableSpace_CPM_BMetOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A))
    (hE3 : ∀ A : Set X, IsClosed A → TopologicalSpace.SeparableSpace ↥A →
      (SigmaCompactSpace ↥A ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn ↥A)))
    (hBMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X)) :
    SigmaCompactSpace X := by
  let σ : (Set.univ : Set X) ≃ₜ X := Homeomorph.Set.univ X
  let H : CPMOn X ≃ₜ CPMOn (Set.univ : Set X) :=
    (CPMOn.relabelIsometry σ).toHomeomorph
  have hBMet' (d : CPMOn X) :
      d ∈ CPM.BMetOn X ↔ H d ∈ CPM.BMetOn (Set.univ : Set X) := by
    change d ∈ CPM.BMetOn X ↔
      CPMOn.comap σ d ∈ CPM.BMetOn (Set.univ : Set X)
    exact (Set.ext_iff.mp (CPMOn.preimage_BMetOn_comap σ) d).symm
  let τ : (↥(CPM.BMetOn X)) ≃ₜ
      (↥(CPM.BMetOn (Set.univ : Set X))) :=
    H.subtype (p := fun d : CPMOn X => d ∈ CPM.BMetOn X)
      (q := fun d : CPMOn (Set.univ : Set X) =>
        d ∈ CPM.BMetOn (Set.univ : Set X)) hBMet'
  have hseparable :
      TopologicalSpace.SeparableSpace (Set.univ : Set X) ↔
        TopologicalSpace.SeparableSpace X := by
    constructor
    · intro hU
      letI : TopologicalSpace.SeparableSpace (Set.univ : Set X) := hU
      exact σ.isOpenQuotientMap.isQuotientMap.separableSpace
    · intro hX
      letI : TopologicalSpace.SeparableSpace X := hX
      exact inferInstance
  have hsigma :
      SigmaCompactSpace X ↔ SigmaCompactSpace (Set.univ : Set X) := by
    constructor
    · intro hX
      letI : SigmaCompactSpace X := hX
      exact σ.isClosedEmbedding.sigmaCompactSpace
    · intro hU
      letI : SigmaCompactSpace (Set.univ : Set X) := hU
      exact σ.symm.isClosedEmbedding.sigmaCompactSpace
  have hcomplete :
      TopologicalSpace.IsCompletelyMetrizableSpace
          ↥(CPM.BMetOn (Set.univ : Set X)) ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X) := by
    constructor
    · intro hU
      exact isCompletelyMetrizableSpace_of_homeomorph τ.symm hU
    · intro hX
      exact isCompletelyMetrizableSpace_of_homeomorph τ hX
  have hE3univ : TopologicalSpace.SeparableSpace X →
      (SigmaCompactSpace X ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X)) := by
    intro hX
    have hU : TopologicalSpace.SeparableSpace (Set.univ : Set X) :=
      hseparable.mpr hX
    exact (hsigma.trans (hE3 (Set.univ : Set X) isClosed_univ hU)).trans hcomplete
  exact
    (isCompletelyMetrizableSpace_CPM_BMetOn_iff_sigmaCompactSpace hE1 hE3univ).mp
      hBMet

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- The continuous members form a closed subset of the continuous-pseudometric
ambient.  This is the Archimedean analogue of
`Ext/UltraGeneral.lean`'s `completeSpace_UCPMOn`: the proof uses uniform
approximation of a limit by continuous pseudometrics and
`EMetric.mem_closure_iff`.  This is `lem:cpm-complete` for the continuous
ambient in `notes/borel-manuscript-20260827-audit.md` §2.16, and is the
completeness input for the finite-distance set `P_d` in Direction A. -/
theorem isClosed_continuous_CPM {X : Type*} [TopologicalSpace X] :
    IsClosed {d : CPM X | Continuous (Function.uncurry d.1)} := by
  rw [← closure_subset_iff_isClosed]
  intro d hd
  show Continuous (Function.uncurry d.1)
  refine continuous_of_uniform_approx_of_continuous fun s hs => ?_
  obtain ⟨ε, hε0, hεs⟩ := Metric.mem_uniformity_dist.mp hs
  obtain ⟨e, he, hde⟩ := EMetric.mem_closure_iff.mp hd
    (ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε0)
  refine ⟨Function.uncurry e.1, he, fun p => hεs ?_⟩
  have habs : |d.1 p.1 p.2 - e.1 p.1 p.2| < ε / 2 :=
    CPM.abs_sub_lt_of_edist_lt (d := d) (e := e) (half_pos hε0) hde p.1 p.2
  rw [Real.dist_eq]
  exact lt_of_lt_of_le habs (by linarith)

/-- The continuous-pseudometric ambient is complete.  It is the closed-subtype
assembly corresponding to `completeSpace_UCPMOn` in
`Ext/UltraGeneral.lean`; this is `lem:cpm-complete` for the continuous
ambient, as needed for `P_d` in
`notes/borel-manuscript-20260827-audit.md` §2.16. -/
instance instCompleteSpace_CPMOn {X : Type*} [TopologicalSpace X] :
    CompleteSpace (CPMOn X) := by
  haveI : CompleteSpace (CPM X) := CPM.instCompleteSpace
  haveI : IsClosed {d : CPM X | Continuous (Function.uncurry d.1)} :=
    isClosed_continuous_CPM
  exact inferInstanceAs (CompleteSpace ↥{d : CPM X |
    Continuous (Function.uncurry d.1)})

/-- The finite-distance neighbourhood `P_d` is closed in the continuous
pseudometric ambient.  This is the closed finite-distance piece of the
`P_d` construction in `notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem isClosed_setOf_edist_lt_top_CPMOn {X : Type*} [TopologicalSpace X]
    (d : CPMOn X) :
    IsClosed {p : CPMOn X | edist p d < ⊤} := by
  have hset : {p : CPMOn X | edist p d < ⊤} =
      {p : CPMOn X | edist d p < ⊤} := by
    ext p
    change edist p d < ⊤ ↔ edist d p < ⊤
    constructor
    · intro hp
      rw [edist_comm p d] at hp
      exact hp
    · intro hp
      rw [edist_comm d p] at hp
      exact hp
  rw [hset]
  exact (isClopen_setOf_edist_lt_top d).isClosed

/-- The finite-distance neighbourhood `P_d` is complete for the ambient
extended supremum distance.  This is the `P_d`-completeness step in
`notes/borel-manuscript-20260827-audit.md` §2.16; it uses Mathlib's
`IsClosed.isComplete` and `IsComplete.completeSpace_coe`. -/
instance instCompleteSpace_setOf_edist_lt_top {X : Type*} [TopologicalSpace X]
    (d : CPMOn X) :
    CompleteSpace ↥{p : CPMOn X | edist p d < ⊤} :=
  (isClosed_setOf_edist_lt_top_CPMOn d).isComplete.completeSpace_coe

end
end IshikiExt

namespace IshikiExt

noncomputable section

private theorem mem_CPM_MetOn_of_forall_restrict_Aball_mem_BMetOn
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X] [Nonempty X]
    (d q : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X)
    (hqfinite : edist q d < ⊤)
    (hqball : ∀ n : ℕ, CPMOn.restrict (Aball d hd o n) q ∈
      CPM.BMetOn ↥(Aball d hd o n)) :
    q ∈ CPM.MetOn X := by
  let h := Classical.choose (mem_CPM_MetOn.mp hd)
  have htop : h.topology = (inferInstance : TopologicalSpace X) :=
    Classical.choose_spec (mem_CPM_MetOn.mp hd)
  let mX : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
  letI : MetricSpace X := mX
  have hdist : ∀ x y : X, dist x y = d.1.1 x y := fun _ _ => rfl
  have hmetric : IsMetricOn q.1.1 := by
    refine ⟨q.1.2.dist_self, ?_, q.1.2.dist_comm, q.1.2.dist_triangle⟩
    intro x y hxy
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
      (max (dist o x) (dist o y)) (by norm_num : (1 : ℝ) < 2)
    have hx : x ∈ Aball d hd o N := by
      have hx' : dist x o ≤ (2 ^ N : ℝ) := by
        rw [dist_comm]
        exact (le_max_left _ _).trans hN.le
      simpa [Aball] using hx'
    have hy : y ∈ Aball d hd o N := by
      have hy' : dist y o ≤ (2 ^ N : ℝ) := by
        rw [dist_comm]
        exact (le_max_right _ _).trans hN.le
      simpa [Aball] using hy'
    have hrestricted :
        CPMOn.restrict (Aball d hd o N) q ∈ CPM.MetOn ↥(Aball d hd o N) :=
      (mem_CPM_BMetOn.mp (hqball N)).1
    obtain ⟨hNmetric, _⟩ := mem_CPM_MetOn.mp hrestricted
    have hsub : (⟨x, hx⟩ : ↥(Aball d hd o N)) = ⟨y, hy⟩ :=
      hNmetric.eq_of_dist_eq_zero (by
        simpa only [CPMOn.restrict_apply] using hxy)
    exact congrArg Subtype.val hsub
  have hforward :
      @Continuous X X (inferInstance : TopologicalSpace X) hmetric.topology id := by
    rw [hmetric.topology_eq_metricSpace_topology]
    refine (@Metric.continuous_iff X X
      (inferInstance : PseudoMetricSpace X)
      hmetric.toMetricSpace.toPseudoMetricSpace id).2 ?_
    intro b ε hε
    have hsection : Continuous (fun a : X => q.1.1 a b) := by
      have hpair : Continuous (fun a : X => (a, b)) :=
        continuous_id.prodMk continuous_const
      have hcomp_eq :
          (Function.uncurry q.1.1 ∘ fun a : X => (a, b)) =
            (fun a : X => q.1.1 a b) := rfl
      exact hcomp_eq ▸ q.2.comp hpair
    obtain ⟨δ, hδ, hδq⟩ := (Metric.continuous_iff.mp hsection) b ε hε
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    have haq := hδq a ha
    rw [Real.dist_eq, q.1.2.dist_self, sub_zero,
      abs_of_nonneg (q.1.2.nonneg a b)] at haq
    have hdistq : @dist X hmetric.toMetricSpace.toDist a b = q.1.1 a b :=
      hmetric.dist_toMetricSpace a b
    change @dist X hmetric.toMetricSpace.toDist a b < ε
    rw [hdistq]
    exact haq
  have hbackward :
      @Continuous X X hmetric.topology (inferInstance : TopologicalSpace X) id := by
    rw [hmetric.topology_eq_metricSpace_topology]
    refine (@Metric.continuous_iff X X
      hmetric.toMetricSpace.toPseudoMetricSpace
      (inferInstance : PseudoMetricSpace X) id).2 ?_
    intro b ε hε
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
      (dist o b + (edist q d).toReal + 1) (by norm_num : (1 : ℝ) < 2)
    have hb : b ∈ Aball d hd o N := by
      have hb' : dist b o ≤ (2 ^ N : ℝ) := by
        rw [dist_comm]
        linarith [ENNReal.toReal_nonneg (a := edist q d)]
      simpa [Aball] using hb'
    have hpointwise : ∀ y : X,
        |q.1.1 b y - d.1.1 b y| ≤ (edist q d).toReal := by
      intro y
      have hle : ENNReal.ofReal |q.1.1 b y - d.1.1 b y| ≤ edist q d := by
        rw [CPMOn.edist_eq]
        exact CPM.ofReal_abs_sub_le_edist q.1 d.1 b y
      exact (ENNReal.ofReal_le_iff_le_toReal hqfinite.ne).mp hle
    have hfar : ∀ y : X, y ∉ Aball d hd o N → 1 < q.1.1 b y := by
      intro y hy
      have hyfar : (2 ^ N : ℝ) < dist y o := by
        apply lt_of_not_ge
        intro hy'
        apply hy
        simpa [Aball] using hy'
      rw [dist_comm y o] at hyfar
      have htriangle : dist o y ≤ dist o b + dist b y := dist_triangle o b y
      have hdistfar : (edist q d).toReal + 1 < dist b y := by
        linarith
      have habs := (abs_le.mp (hpointwise y)).1
      rw [← hdist b y] at habs
      linarith
    have hconfine : ∀ y : X, q.1.1 y b < 1 → y ∈ Aball d hd o N := by
      intro y hy
      by_contra hyA
      have hyfar := hfar y hyA
      rw [q.1.2.dist_comm b y] at hyfar
      linarith
    have hrestricted :
        CPMOn.restrict (Aball d hd o N) q ∈ CPM.MetOn ↥(Aball d hd o N) :=
      (mem_CPM_BMetOn.mp (hqball N)).1
    obtain ⟨hlocal, hlocal_top⟩ := mem_CPM_MetOn.mp hrestricted
    have hlocal_continuous :
        @Continuous ↥(Aball d hd o N) ↥(Aball d hd o N)
          hlocal.toMetricSpace.toUniformSpace.toTopologicalSpace
          (inferInstance : TopologicalSpace ↥(Aball d hd o N)) id := by
      rw [← hlocal.topology_eq_metricSpace_topology, hlocal_top]
      exact continuous_id
    obtain ⟨δ, hδ, hδlocal⟩ :=
      (@Metric.continuous_iff ↥(Aball d hd o N) ↥(Aball d hd o N)
        hlocal.toMetricSpace.toPseudoMetricSpace
        (inferInstance : PseudoMetricSpace ↥(Aball d hd o N)) id).mp
        hlocal_continuous ⟨b, hb⟩ ε hε
    refine ⟨min 1 δ, lt_min (by norm_num) hδ, ?_⟩
    intro a ha
    have haq : q.1.1 a b < min 1 δ := by
      rw [← hmetric.dist_toMetricSpace a b]
      exact ha
    have haA : a ∈ Aball d hd o N :=
      hconfine a (haq.trans_le (min_le_left _ _))
    have ha_source :
        @dist ↥(Aball d hd o N)
          hlocal.toMetricSpace.toDist ⟨a, haA⟩ ⟨b, hb⟩ < δ := by
      rw [hlocal.dist_toMetricSpace]
      change q.1.1 a b < δ
      exact haq.trans_le (min_le_right _ _)
    have ha' := hδlocal ⟨a, haA⟩ ha_source
    simpa only [id_eq, Subtype.dist_eq] using ha'
  exact mem_CPM_MetOn.mpr ⟨hmetric,
    le_antisymm (continuous_id_iff_le.mp hbackward)
      (continuous_id_iff_le.mp hforward)⟩

/-- **Direction A, `sigma-compact ⇒ each-component`.**  Following the
confinement argument checked in full in
`notes/borel-manuscript-20260827-audit.md` §2.16 ("New direction A"), the
compatible metrics in the finite-distance piece `P_d` are characterized by
bounded compatible restrictions to the closed balls `A_n`.  This makes the
component a `G_δ` subspace of the complete space `P_d`. -/
theorem isCompletelyMetrizableSpace_component_of_sigmaCompactSpace
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X]
    (hE3 : ∀ A : Set X, IsClosed A → TopologicalSpace.SeparableSpace ↥A →
      (SigmaCompactSpace ↥A ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn ↥A)))
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) :
    TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · letI : IsEmpty X := hX
    letI : Subsingleton (CPMOn X) := ⟨by
      intro p q
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact isEmptyElim x⟩
    letI : Subsingleton ↥(CPMOn.component d) := inferInstance
    exact inferInstance
  · letI : Nonempty X := hX
    let o : X := Classical.arbitrary X
    let Y := ↥{p : CPMOn X | edist p d < ⊤}
    let C : Set Y := {p | ((p : Y) : CPMOn X) ∈ CPM.MetOn X}
    let R : ∀ n : ℕ, Y → CPMOn ↥(Aball d hd o n) :=
      fun n p => CPMOn.restrict (Aball d hd o n) ((p : Y) : CPMOn X)
    have hRcontinuous : ∀ n : ℕ, Continuous (R n) := by
      intro n
      have hcomp_eq :
          (CPMOn.restrict (Aball d hd o n) ∘
              (Subtype.val : Y → CPMOn X)) =
            (fun p : Y => CPMOn.restrict (Aball d hd o n) (p : CPMOn X)) := rfl
      have hterm :
          Continuous (fun p : Y => CPMOn.restrict (Aball d hd o n) (p : CPMOn X)) :=
        hcomp_eq ▸
          (CPMOn.continuous_restrict (Aball d hd o n)).comp continuous_subtype_val
      simpa only [R] using hterm
    have hcharacterization :
        C = ⋂ n : ℕ, (R n) ⁻¹' (CPM.BMetOn ↥(Aball d hd o n)) := by
      ext p
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro hp n
        have hpcomponent : ((p : Y) : CPMOn X) ∈ CPMOn.component d := by
          refine ⟨?_, ?_⟩
          · simpa only [C, Set.mem_setOf_eq] using hp
          · rw [edist_comm]
            exact p.2
        simpa only [R] using
          restrict_Aball_mem_BMetOn_of_mem_component d hd o n
            ((p : Y) : CPMOn X) hpcomponent
      · intro hp
        have hpmet : ((p : Y) : CPMOn X) ∈ CPM.MetOn X :=
          mem_CPM_MetOn_of_forall_restrict_Aball_mem_BMetOn d
            ((p : Y) : CPMOn X) hd o p.2 (by
              intro n
              simpa only [R] using hp n)
        simpa only [C, Set.mem_setOf_eq] using hpmet
    have hCgdelta : IsGδ C := by
      rw [hcharacterization]
      exact IsGδ.iInter fun n =>
        (isGδ_CPM_BMetOn_Aball d hd o hE3 n).preimage (hRcontinuous n)
    letI : MetricSpace Y := metricSpaceEMetricBall d ⊤
    haveI := instCompleteSpace_setOf_edist_lt_top d
    have hYcomplete : TopologicalSpace.IsCompletelyMetrizableSpace Y := inferInstance
    have hCcomplete : TopologicalSpace.IsCompletelyMetrizableSpace ↥C :=
      isCompletelyMetrizableSpace_of_isGδ hYcomplete hCgdelta
    let fC : ↥C → CPMOn X := fun p => ((p.1 : Y) : CPMOn X)
    have hfC : Topology.IsEmbedding fC := by
      change Topology.IsEmbedding
        ((Subtype.val : Y → CPMOn X) ∘ (Subtype.val : ↥C → Y))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hrange : Set.range fC = CPMOn.component d := by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        refine ⟨?_, ?_⟩
        · simpa only [C, Set.mem_setOf_eq] using p.2
        · rw [edist_comm]
          exact p.1.2
      · intro hq
        refine ⟨⟨⟨q, ?_⟩, ?_⟩, rfl⟩
        · change edist q d < ⊤
          rw [edist_comm]
          exact hq.2
        · simpa only [C, Set.mem_setOf_eq] using hq.1
    let eC : ↥C ≃ₜ ↥(CPMOn.component d) :=
      hfC.toHomeomorph.trans (Homeomorph.setCongr hrange)
    exact isCompletelyMetrizableSpace_of_homeomorph eC hCcomplete

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- **Direction B, `hE1` restricted.**  As recorded in
`notes/borel-manuscript-20260827-audit.md` §2.16 ("New direction B",
"hE1 restricted"), the bounded isometric extensor supplied for every closed
subset of `X` also supplies one for every closed subset of a closed subspace
`A`, by applying it to the corresponding closed subset of `X` and restricting
its values back to `A`. -/
theorem exists_isBddIsometricExtensorOn_of_isClosed_subset
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {A : Set X} (hA : IsClosed A)
    (hE1 : ∀ B : Set X, IsClosed B → Nonempty (IsBddIsometricExtensorOn B)) :
    ∀ B : Set ↥A, IsClosed B → Nonempty (IsBddIsometricExtensorOn B) := by
  intro B hB
  let ιBX : ↥B → X := fun b => ((b : ↥A) : X)
  have hιBX_embedding : Topology.IsEmbedding ιBX :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hιBX_closed_range : IsClosed (Set.range ιBX) := by
    have hrange :
        Set.range ιBX = (Subtype.val : ↥A → X) '' B := by
      ext x
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b.1, b.2, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [hrange]
    exact hA.isClosedEmbedding_subtypeVal.isClosedMap B hB
  set B' : Set X := Set.range ιBX with hB'_def
  obtain ⟨E⟩ := hE1 B' hιBX_closed_range
  let σ : ↥B ≃ₜ ↥B' := hιBX_embedding.toHomeomorph
  have hσ_coe : ∀ b : ↥B, (σ b : X) = ιBX b := by
    intro b
    rfl
  let toCPM : CPMOn ↥B → CPMOn ↥A := fun d =>
    CPMOn.restrict A (E.toCPM (CPMOn.comap σ.symm d))
  have htoCPM_isometry : Isometry toCPM := by
    have hrecover : ∀ d : CPMOn ↥B, CPMOn.restrict B (toCPM d) = d := by
      intro d
      apply Subtype.ext
      apply Subtype.ext
      funext a b
      simp only [toCPM, CPMOn.restrict_apply]
      change
        (E.toCPM (CPMOn.comap σ.symm d)).1.1 (ιBX a) (ιBX b) =
          d.1.1 a b
      rw [← hσ_coe a, ← hσ_coe b,
        E.extension (CPMOn.comap σ.symm d) (σ a) (σ b)]
      have hσa : σ.symm.toEquiv (σ a) = a := σ.symm_apply_apply a
      have hσb : σ.symm.toEquiv (σ b) = b := σ.symm_apply_apply b
      simp only [CPMOn.comap_coe, CPM.comap_val, hσa, hσb]
    intro d e
    apply le_antisymm
    · calc
        edist (toCPM d) (toCPM e) ≤
            edist (E.toCPM (CPMOn.comap σ.symm d))
              (E.toCPM (CPMOn.comap σ.symm e)) :=
          CPMOn.edist_restrict_le A _ _
        _ = edist (CPMOn.comap σ.symm d) (CPMOn.comap σ.symm e) :=
          E.isometry_toCPM _ _
        _ = edist d e := CPMOn.isometry_comap σ.symm d e
    · calc
        edist d e =
            edist (CPMOn.restrict B (toCPM d))
              (CPMOn.restrict B (toCPM e)) := by
          rw [hrecover d, hrecover e]
        _ ≤ edist (toCPM d) (toCPM e) :=
          CPMOn.edist_restrict_le B _ _
  have htoCPM_extension : ∀ (d : CPMOn ↥B) (a b : ↥B),
      (toCPM d).1.1 (a : ↥A) (b : ↥A) = d.1.1 a b := by
    intro d a b
    simp only [toCPM, CPMOn.restrict_apply]
    change
      (E.toCPM (CPMOn.comap σ.symm d)).1.1 (ιBX a) (ιBX b) =
        d.1.1 a b
    rw [← hσ_coe a, ← hσ_coe b,
      E.extension (CPMOn.comap σ.symm d) (σ a) (σ b)]
    have hσa : σ.symm.toEquiv (σ a) = a := σ.symm_apply_apply a
    have hσb : σ.symm.toEquiv (σ b) = b := σ.symm_apply_apply b
    simp only [CPMOn.comap_coe, CPM.comap_val, hσa, hσb]
  have htoCPM_met : toCPM '' CPM.MetOn ↥B ⊆ CPM.MetOn ↥A := by
    rintro _ ⟨d, hd, rfl⟩
    have hcomap : CPMOn.comap σ.symm d ∈ CPM.MetOn ↥B' := by
      rw [← CPMOn.preimage_MetOn_comap σ.symm] at hd
      exact hd
    have hfull : E.toCPM (CPMOn.comap σ.symm d) ∈ CPM.MetOn X :=
      E.met_preservation ⟨CPMOn.comap σ.symm d, hcomap, rfl⟩
    exact isMetricOn_restrict_of_mem_MetOn_of_topologicalSpace
      (ι := (Subtype.val : ↥A → X)) Topology.IsEmbedding.subtypeVal hfull
      (fun a b =>
        (CPMOn.restrict_apply A
          (E.toCPM (CPMOn.comap σ.symm d)) a b).symm)
  have htoCPM_bmet : toCPM '' CPM.BMetOn ↥B ⊆ CPM.BMetOn ↥A := by
    rintro _ ⟨d, hd, rfl⟩
    have hcomap : CPMOn.comap σ.symm d ∈ CPM.BMetOn ↥B' := by
      rw [← CPMOn.preimage_BMetOn_comap σ.symm] at hd
      exact hd
    have hfull : E.toCPM (CPMOn.comap σ.symm d) ∈ CPM.BMetOn X :=
      E.bmet_preservation ⟨CPMOn.comap σ.symm d, hcomap, rfl⟩
    refine mem_CPM_BMetOn.mpr ⟨?_, ?_⟩
    · exact isMetricOn_restrict_of_mem_MetOn_of_topologicalSpace
        (ι := (Subtype.val : ↥A → X)) Topology.IsEmbedding.subtypeVal
        (mem_CPM_BMetOn.mp hfull).1
        (fun a b =>
          (CPMOn.restrict_apply A
            (E.toCPM (CPMOn.comap σ.symm d)) a b).symm)
    · obtain ⟨C, hC⟩ := (mem_CPM_BMetOn.mp hfull).2
      exact ⟨C, fun a b => by
        simpa only [toCPM, CPMOn.restrict_apply] using
          hC (a : X) (b : X)⟩
  exact ⟨
    { toIsIsometricExtensorOn :=
        { closed := hB
          toCPM := toCPM
          extension := htoCPM_extension
          isometry_toCPM := htoCPM_isometry
          met_preservation := htoCPM_met }
      bmet_preservation := htoCPM_bmet }⟩

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- **Direction B, restriction map.**  The map `R_n` from the compatible
metrics in the component of `d` to the bounded compatible metrics on `A_n`.
This is the restriction map from `notes/borel-manuscript-20260827-audit.md`
§2.16 ("New direction B"). -/
def restrictAballComponentMap
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X] [Nonempty X]
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) :
    ↥(CPMOn.component d) → ↥(CPM.BMetOn ↥(Aball d hd o n)) :=
  fun m => ⟨CPMOn.restrict (Aball d hd o n) (m : CPMOn X),
    restrict_Aball_mem_BMetOn_of_mem_component d hd o n
      (m : CPMOn X) m.2⟩

/-- The restriction map `R_n` is continuous, as required by the Direction B
argument in `notes/borel-manuscript-20260827-audit.md` §2.16. -/
theorem continuous_restrictAballComponentMap
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X] [Nonempty X]
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) :
    Continuous (restrictAballComponentMap d hd o n) := by
  have hcontinuous :
      Continuous (fun m : ↥(CPMOn.component d) =>
        CPMOn.restrict (Aball d hd o n) (m : CPMOn X)) := by
    have hcomp_eq :
        (fun m : ↥(CPMOn.component d) =>
            CPMOn.restrict (Aball d hd o n) (m : CPMOn X)) =
          (CPMOn.restrict (Aball d hd o n) :
              CPMOn X → CPMOn ↥(Aball d hd o n)) ∘
            (Subtype.val : ↥(CPMOn.component d) → CPMOn X) := rfl
    exact hcomp_eq ▸
      (CPMOn.continuous_restrict (Aball d hd o n)).comp
        continuous_subtype_val
  exact hcontinuous.subtype_mk (fun m =>
    restrict_Aball_mem_BMetOn_of_mem_component d hd o n
      (m : CPMOn X) m.2)

/-- **Direction B, interpolation core.**  If `e` is a bounded compatible
metric on `A_n`, interpolation extends it to a compatible metric in the
component of `d`, with the exact prescribed distance from `m`.  The bounded
hypothesis is what makes that prescribed distance finite.  This is the
load-bearing E5 step in `notes/borel-manuscript-20260827-audit.md` §2.16
("New direction B"). -/
theorem exists_component_interpolant
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X] [Nonempty X]
    (hE5 : ∀ A : Set X, IsClosed A → Nonempty (IsMetricInterpolationOn A))
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ)
    (m : CPMOn X) (hm : m ∈ CPMOn.component d)
    (e : CPMOn ↥(Aball d hd o n))
    (he : e ∈ CPM.BMetOn ↥(Aball d hd o n)) :
    ∃ M : CPMOn X, M ∈ CPMOn.component d ∧
      CPMOn.restrict (Aball d hd o n) M = e ∧
      edist M m = edist e (CPMOn.restrict (Aball d hd o n) m) := by
  obtain ⟨hIM⟩ := hE5 (Aball d hd o n) (isClosed_Aball d hd o n)
  obtain ⟨M, hM_MetOn, hM_restrict, hM_edist⟩ :=
    hIM.exists_interpolant m hm.1 e (mem_CPM_BMetOn.mp he).1
  have hrestrict :
      CPMOn.restrict (Aball d hd o n) m ∈
        CPM.BMetOn ↥(Aball d hd o n) :=
    restrict_Aball_mem_BMetOn_of_mem_component d hd o n m hm
  have hfinite : edist e (CPMOn.restrict (Aball d hd o n) m) < ⊤ := by
    have hfinite' :
        CPM.edist e.1 (CPMOn.restrict (Aball d hd o n) m).1 < ⊤ :=
      (CPM.isBdd_iff_edist_lt_top
        (d := e.1) (e := (CPMOn.restrict (Aball d hd o n) m).1)
        (mem_CPM_BMetOn.mp he).2).mp
        (mem_CPM_BMetOn.mp hrestrict).2
    simpa only [CPMOn.edist_eq] using hfinite'
  have hMm : edist m M < ⊤ := by
    rw [edist_comm, hM_edist]
    exact hfinite
  refine ⟨M, ⟨hM_MetOn, ?_⟩, hM_restrict, hM_edist⟩
  exact lt_of_le_of_lt (edist_triangle d m M)
    (ENNReal.add_lt_top.mpr ⟨hm.2, hMm⟩)

/-- **Direction B, surjectivity.**  The restriction map `R_n` is surjective
onto `BMet(A_n)` by the interpolation core from §2.16 of
`notes/borel-manuscript-20260827-audit.md` ("New direction B"). -/
theorem surjective_restrictAballComponentMap
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X] [Nonempty X]
    (hE5 : ∀ A : Set X, IsClosed A → Nonempty (IsMetricInterpolationOn A))
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) :
    Function.Surjective (restrictAballComponentMap d hd o n) := by
  intro e
  obtain ⟨M, hM_component, hM_restrict, _⟩ :=
    exists_component_interpolant hE5 d hd o n d
      (CPMOn.self_mem_component hd) e.1
      e.2
  refine ⟨⟨M, hM_component⟩, ?_⟩
  apply Subtype.ext
  exact hM_restrict

/-- **Direction B, openness.**  The image of every open `edist`-ball under
`R_n` contains the corresponding target ball, by exact-distance interpolation;
the reverse inclusion is its 1-Lipschitz restriction estimate.  This proves
the open-map clause audited in §2.16 of
`notes/borel-manuscript-20260827-audit.md` ("New direction B"). -/
theorem isOpenMap_restrictAballComponentMap
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SigmaCompactSpace X] [Nonempty X]
    (hE5 : ∀ A : Set X, IsClosed A → Nonempty (IsMetricInterpolationOn A))
    (d : CPMOn X) (hd : d ∈ CPM.MetOn X) (o : X) (n : ℕ) :
    IsOpenMap (restrictAballComponentMap d hd o n) := by
  intro U hU
  rw [EMetric.isOpen_iff] at hU ⊢
  intro y hy
  rcases hy with ⟨m, hmU, rfl⟩
  obtain ⟨ε, hε, hεU⟩ := hU m hmU
  refine ⟨ε, hε, ?_⟩
  intro e he
  have he' :
      edist e.1 (CPMOn.restrict (Aball d hd o n) (m : CPMOn X)) < ε := by
    exact Metric.mem_eball.mp he
  obtain ⟨M, hM_component, hM_restrict, hM_edist⟩ :=
    exists_component_interpolant hE5 d hd o n (m : CPMOn X) m.2 e.1
      e.2
  have hMball :
      (⟨M, hM_component⟩ : ↥(CPMOn.component d)) ∈ Metric.eball m ε := by
    rw [Metric.mem_eball]
    change edist M (m : CPMOn X) < ε
    rw [hM_edist]
    exact he'
  refine ⟨⟨M, hM_component⟩, hεU hMball, ?_⟩
  apply Subtype.ext
  exact hM_restrict

/-- **Direction B assembly.**  Under E1, E3, E5, and the Hausdorff open-image
hypothesis E6, a completely metrizable component of `Met(X)` forces `X` to be
σ-compact.  This is the `some-component ⇒ sigma-compact` direction in
§2.16 of `notes/borel-manuscript-20260827-audit.md` ("New direction B"). -/
theorem sigmaCompactSpace_of_exists_isCompletelyMetrizableSpace_component
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A))
    (hE3 : ∀ A : Set X, IsClosed A → TopologicalSpace.SeparableSpace ↥A →
      (SigmaCompactSpace ↥A ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn ↥A)))
    (hE5 : ∀ A : Set X, IsClosed A → Nonempty (IsMetricInterpolationOn A))
    (hE6 : HausdorffOpenImageHypothesis (X := X))
    (hex : ∃ d : CPMOn X, d ∈ CPM.MetOn X ∧
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) :
    SigmaCompactSpace X := by
  obtain ⟨d, hd, hcomponent⟩ := hex
  rcases isEmpty_or_nonempty X with hX | hX
  · letI : IsEmpty X := hX
    exact inferInstance
  · letI : Nonempty X := hX
    let o : X := Classical.arbitrary X
    have hclosed_Aball : ∀ n : ℕ, IsClosed (Aball d hd o n) := by
      intro n
      let h := Classical.choose (mem_CPM_MetOn.mp hd)
      have htop : h.topology = (inferInstance : TopologicalSpace X) :=
        Classical.choose_spec (mem_CPM_MetOn.mp hd)
      letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
      unfold Aball
      exact Metric.isClosed_closedBall
    have hrestrict_Aball :
        ∀ n : ℕ, ∀ p : CPMOn X, p ∈ CPMOn.component d →
          CPMOn.restrict (Aball d hd o n) p ∈
            CPM.BMetOn ↥(Aball d hd o n) := by
      intro n p hp
      let h := Classical.choose (mem_CPM_MetOn.mp hd)
      have htop : h.topology = (inferInstance : TopologicalSpace X) :=
        Classical.choose_spec (mem_CPM_MetOn.mp hd)
      letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
      have hdist : ∀ x y : X, dist x y = d.1.1 x y := fun _ _ => rfl
      obtain ⟨hp_MetOn, hp_edist⟩ := hp
      refine mem_CPM_BMetOn.mpr ⟨?_, ?_⟩
      · exact isMetricOn_restrict_of_mem_MetOn_of_topologicalSpace
          (ι := (Subtype.val : ↥(Aball d hd o n) → X)) Topology.IsEmbedding.subtypeVal
          hp_MetOn (fun a b =>
            (CPMOn.restrict_apply (Aball d hd o n) p a b).symm)
      · refine ⟨2 * (2 ^ n : ℝ) + (edist p d).toReal, ?_⟩
        intro a b
        have hp_edist' : edist p d < ⊤ := by
          rw [edist_comm]
          exact hp_edist
        have hpa :
            |p.1.1 (↑a : X) (↑b : X) - d.1.1 (↑a : X) (↑b : X)| ≤
              (edist p d).toReal := by
          have hpt : ENNReal.ofReal
              |p.1.1 (↑a : X) (↑b : X) - d.1.1 (↑a : X) (↑b : X)| ≤ edist p d := by
            rw [CPMOn.edist_eq]
            exact CPM.ofReal_abs_sub_le_edist p.1 d.1 (↑a : X) (↑b : X)
          exact (ENNReal.ofReal_le_iff_le_toReal hp_edist'.ne).mp hpt
        have ha : d.1.1 (↑a : X) o ≤ (2 ^ n : ℝ) := by
          rw [← hdist]
          exact Metric.mem_closedBall.mp (by simpa [Aball] using a.2)
        have hb : d.1.1 o (↑b : X) ≤ (2 ^ n : ℝ) := by
          rw [← hdist]
          exact Metric.mem_closedBall'.mp (by simpa [Aball] using b.2)
        have htriangle :
            d.1.1 (↑a : X) (↑b : X) ≤
              d.1.1 (↑a : X) o + d.1.1 o (↑b : X) :=
          d.1.2.dist_triangle (↑a : X) o (↑b : X)
        rw [CPMOn.restrict_apply]
        have hupper :
            p.1.1 (↑a : X) (↑b : X) ≤
              d.1.1 (↑a : X) (↑b : X) + (edist p d).toReal := by
          have hpair := abs_le.mp hpa
          linarith [hpair.2]
        linarith
    have hinterpolant :
        ∀ n : ℕ, ∀ (m : CPMOn X), m ∈ CPMOn.component d →
          ∀ (e : CPMOn ↥(Aball d hd o n)),
            e ∈ CPM.BMetOn ↥(Aball d hd o n) →
              ∃ M : CPMOn X, M ∈ CPMOn.component d ∧
                CPMOn.restrict (Aball d hd o n) M = e ∧
                edist M m = edist e (CPMOn.restrict (Aball d hd o n) m) := by
      intro n m hm e he
      obtain ⟨hIM⟩ := hE5 (Aball d hd o n) (hclosed_Aball n)
      obtain ⟨M, hM_MetOn, hM_restrict, hM_edist⟩ :=
        hIM.exists_interpolant m hm.1 e (mem_CPM_BMetOn.mp he).1
      have hrestrict :
          CPMOn.restrict (Aball d hd o n) m ∈
            CPM.BMetOn ↥(Aball d hd o n) :=
        hrestrict_Aball n m hm
      have hfinite : edist e (CPMOn.restrict (Aball d hd o n) m) < ⊤ := by
        have hfinite' :
            CPM.edist e.1 (CPMOn.restrict (Aball d hd o n) m).1 < ⊤ :=
          (CPM.isBdd_iff_edist_lt_top
            (d := e.1) (e := (CPMOn.restrict (Aball d hd o n) m).1)
            (mem_CPM_BMetOn.mp he).2).mp
            (mem_CPM_BMetOn.mp hrestrict).2
        simpa only [CPMOn.edist_eq] using hfinite'
      have hMm : edist m M < ⊤ := by
        rw [edist_comm, hM_edist]
        exact hfinite
      refine ⟨M, ⟨hM_MetOn, ?_⟩, hM_restrict, hM_edist⟩
      exact lt_of_le_of_lt (edist_triangle d m M)
        (ENNReal.add_lt_top.mpr ⟨hm.2, hMm⟩)
    let R : ∀ n : ℕ,
        ↥(CPMOn.component d) → ↥(CPM.BMetOn ↥(Aball d hd o n)) :=
      fun n m => ⟨CPMOn.restrict (Aball d hd o n) (m : CPMOn X),
        hrestrict_Aball n (m : CPMOn X) m.2⟩
    have hR_continuous : ∀ n : ℕ, Continuous (R n) := by
      intro n
      change Continuous (fun m : ↥(CPMOn.component d) =>
        (⟨CPMOn.restrict (Aball d hd o n) (m : CPMOn X),
          hrestrict_Aball n (m : CPMOn X) m.2⟩ :
          ↥(CPM.BMetOn ↥(Aball d hd o n))))
      have hcontinuous :
          Continuous (fun m : ↥(CPMOn.component d) =>
            CPMOn.restrict (Aball d hd o n) (m : CPMOn X)) := by
        have hcomp_eq :
            (fun m : ↥(CPMOn.component d) =>
                CPMOn.restrict (Aball d hd o n) (m : CPMOn X)) =
              (CPMOn.restrict (Aball d hd o n) :
                  CPMOn X → CPMOn ↥(Aball d hd o n)) ∘
                (Subtype.val : ↥(CPMOn.component d) → CPMOn X) := rfl
        exact hcomp_eq ▸
          (CPMOn.continuous_restrict (Aball d hd o n)).comp
            continuous_subtype_val
      exact hcontinuous.subtype_mk (fun m =>
        hrestrict_Aball n (m : CPMOn X) m.2)
    have hR_surjective : ∀ n : ℕ, Function.Surjective (R n) := by
      intro n
      change Function.Surjective (fun m : ↥(CPMOn.component d) =>
        (⟨CPMOn.restrict (Aball d hd o n) (m : CPMOn X),
          hrestrict_Aball n (m : CPMOn X) m.2⟩ :
          ↥(CPM.BMetOn ↥(Aball d hd o n))))
      intro e
      obtain ⟨M, hM_component, hM_restrict, _⟩ :=
        hinterpolant n d (CPMOn.self_mem_component hd) e.1 e.2
      refine ⟨⟨M, hM_component⟩, ?_⟩
      apply Subtype.ext
      exact hM_restrict
    have hR_open : ∀ n : ℕ, IsOpenMap (R n) := by
      intro n
      change IsOpenMap (fun m : ↥(CPMOn.component d) =>
        (⟨CPMOn.restrict (Aball d hd o n) (m : CPMOn X),
          hrestrict_Aball n (m : CPMOn X) m.2⟩ :
          ↥(CPM.BMetOn ↥(Aball d hd o n))))
      intro U hU
      rw [EMetric.isOpen_iff] at hU ⊢
      intro y hy
      rcases hy with ⟨m, hmU, rfl⟩
      obtain ⟨ε, hε, hεU⟩ := hU m hmU
      refine ⟨ε, hε, ?_⟩
      intro e he
      have he' :
          edist e.1 (CPMOn.restrict (Aball d hd o n) (m : CPMOn X)) < ε := by
        exact Metric.mem_eball.mp he
      obtain ⟨M, hM_component, hM_restrict, hM_edist⟩ :=
        hinterpolant n (m : CPMOn X) m.2 e.1 e.2
      have hMball :
          (⟨M, hM_component⟩ : ↥(CPMOn.component d)) ∈ Metric.eball m ε := by
        rw [Metric.mem_eball]
        change edist M (m : CPMOn X) < ε
        rw [hM_edist]
        exact he'
      refine ⟨⟨M, hM_component⟩, hεU hMball, ?_⟩
      apply Subtype.ext
      exact hM_restrict
    have hAn_sigma : ∀ n : ℕ, SigmaCompactSpace ↥(Aball d hd o n) := by
      intro n
      have hclosed : IsClosed (Aball d hd o n) := hclosed_Aball n
      have hR_continuous :
          Continuous (R n) := hR_continuous n
      have hR_surjective :
          Function.Surjective (R n) := hR_surjective n
      have hR_open :
          IsOpenMap (R n) := hR_open n
      have hBMet_complete :
          TopologicalSpace.IsCompletelyMetrizableSpace
            ↥(CPM.BMetOn ↥(Aball d hd o n)) :=
        hE6 (Aball d hd o n) hclosed d hd hcomponent
          (R n) hR_continuous hR_open
          hR_surjective
      have hE1' :
          ∀ B : Set ↥(Aball d hd o n), IsClosed B →
            Nonempty (IsBddIsometricExtensorOn B) :=
        exists_isBddIsometricExtensorOn_of_isClosed_subset hclosed hE1
      have hAn_separable :
          TopologicalSpace.SeparableSpace ↥(Aball d hd o n) :=
        separable_of_isCompletelyMetrizableSpace_CPM_BMetOn_of_bddIsometricExtensorOn
          hBMet_complete hE1'
      exact (hE3 (Aball d hd o n) hclosed hAn_separable).mpr
        hBMet_complete
    let h := Classical.choose (mem_CPM_MetOn.mp hd)
    have htop : h.topology = (inferInstance : TopologicalSpace X) :=
      Classical.choose_spec (mem_CPM_MetOn.mp hd)
    letI : MetricSpace X := h.toMetricSpace.replaceTopology htop.symm
    have hballs : (⋃ n : ℕ, Aball d hd o n) = (Set.univ : Set X) := by
      rw [eq_univ_iff_forall]
      intro x
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
        (dist o x) (by norm_num : (1 : ℝ) < 2)
      have hx : dist x o ≤ (2 ^ N : ℝ) := by
        rw [dist_comm]
        exact hN.le
      refine mem_iUnion.2 ⟨N, ?_⟩
      simpa [Aball] using hx
    have hUnion : IsSigmaCompact (⋃ n : ℕ, Aball d hd o n) :=
      isSigmaCompact_iUnion (fun n : ℕ => Aball d hd o n) (fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mpr (hAn_sigma n))
    rw [hballs] at hUnion
    exact isSigmaCompact_univ_iff.mp hUnion

end
end IshikiExt

namespace IshikiExt

noncomputable section

/-- **Five-way complete-metrizability/component/σ-compactness equivalence.**
This strengthens the existing two-way theorem
`isCompletelyMetrizableSpace_CPM_BMetOn_iff_sigmaCompactSpace` in
`Ext/CompleteMetrizability.lean` to a five-way `List.TFAE`.

The hypotheses `hE1`, `hE3`, `hE5`, and `hE6` are E1, E3, E5, and E6 as
audited in `notes/borel-manuscript-20260827-audit.md` §2.16 and §4.  The
hypothesis `hE3` is quantified over closed subspaces `A` of `X`, as it is used
later at the balls `A_n`, but it is still exactly E3.  The existing theorem's
`hE3` for `X` alone is the case `A = univ`, up to the subtype equivalence.
This theorem must not rewrite or duplicate the existing theorem; it only
reuses its lemma chain later.  The route connecting the five clauses is
recorded in the audit note cited above; this file is currently a
statement-shape draft. -/
theorem tfae_isCompletelyMetrizableSpace_iff_sigmaCompactSpace
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsBddIsometricExtensorOn A))
    (hE3 : ∀ A : Set X, IsClosed A → TopologicalSpace.SeparableSpace ↥A →
      (SigmaCompactSpace ↥A ↔
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn ↥A)))
    (hE5 : ∀ A : Set X, IsClosed A → Nonempty (IsMetricInterpolationOn A))
    (hE6 : HausdorffOpenImageHypothesis (X := X)) :
    List.TFAE
      [ TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X),
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X),
        ∀ d : CPMOn X, d ∈ CPM.MetOn X →
          TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d),
      ∃ d : CPMOn X, d ∈ CPM.MetOn X ∧
          TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d),
        SigmaCompactSpace X ] := by
  have hAB :
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X) →
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X) :=
    fun hA =>
      isCompletelyMetrizableSpace_CPM_BMetOn_of_forall_component
        (isCompletelyMetrizableSpace_component_of_isCompletelyMetrizableSpace_CPM_MetOn
          hA)
  have hBC :
      TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.BMetOn X) →
        (∀ d : CPMOn X, d ∈ CPM.MetOn X →
          TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) :=
    fun hB d hd =>
      @isCompletelyMetrizableSpace_component_of_sigmaCompactSpace X _ _
        (sigmaCompactSpace_of_isCompletelyMetrizableSpace_CPM_BMetOn hE1 hE3 hB)
        hE3 d hd
  have hCD :
      (∀ d : CPMOn X, d ∈ CPM.MetOn X →
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) →
      (∃ d : CPMOn X, d ∈ CPM.MetOn X ∧
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) :=
    exists_isCompletelyMetrizableSpace_component_of_forall
  have hDE :
      (∃ d : CPMOn X, d ∈ CPM.MetOn X ∧
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPMOn.component d)) →
      SigmaCompactSpace X :=
    sigmaCompactSpace_of_exists_isCompletelyMetrizableSpace_component hE1 hE3 hE5 hE6
  have hEA :
      SigmaCompactSpace X →
        TopologicalSpace.IsCompletelyMetrizableSpace ↥(CPM.MetOn X) :=
    fun hE =>
      isCompletelyMetrizableSpace_CPM_MetOn_of_forall_component
        (fun d hd =>
          @isCompletelyMetrizableSpace_component_of_sigmaCompactSpace X _ _ hE hE3 d hd)
  exact List.tfae_of_cycle
    (by
      simp only [List.isChain_cons_cons]
      exact ⟨hAB, ⟨hBC, ⟨hCD, ⟨hDE, List.isChain_singleton _⟩⟩⟩⟩)
    (by
      simpa only [List.getLastD_cons, List.getLastD_nil] using hEA)


end
end IshikiExt
