-- Ext.UltraComponentGeneral
--
-- Issue #110 / `cor:nonseparable-ultrametric-nonborel`, per
-- `notes/borel-manuscript-20260827-audit.md` §2.19 and §4 (E2c).
-- This module is currently at the B0 fidelity-gate stage: signatures only,
-- `sorry`-filled, and pending orchestrator approval before proof work.
-- The 2026-08-27 received source is reference-only; it is not called an
-- arXiv version and is not copied here beyond the short provenance clause in
-- the E2c docstring.
--
-- Proposed declarations for review:
--   * `IsUltraComponentControlledExtensorOn`
--   * `not_measurableSet_UCPMOn_component_of_isUltraComponentControlledExtensorOn`
--   * `not_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn`

import IshikiConj51.Ext.UltraPublished
import IshikiConj51.Ext.GeneralSpace

open Set
open scoped ENNReal Topology

namespace IshikiExt

noncomputable section

variable {R : RangeSet}

-- `ucpmOnMeasurableSpace`/`ucpmOnBorelSpace` are the existing ambient
-- instances from `Ext.UltraGeneral`; they are local there, so register the
-- same instances for the statements below rather than introducing a new
-- measurable-space convention.
attribute [local instance] ucpmOnMeasurableSpace ucpmOnBorelSpace

/-! ## The general-space ultrametric component -/

/-- The finite-distance component of `d` in the topology-aware ultrametric
ambient.  This is the general-space analogue of `CPMOn.component` and the
discrete-carrier `UComponent`: the compatible members at finite
`𝒰𝒟^R`-distance from `d`. -/
def UCPMOn.component {Y : Type*} [TopologicalSpace Y] (R : RangeSet)
    (d : UCPMOn Y R) : Set (UCPMOn Y R) :=
  {e | e ∈ UMetOn Y R ∧ edist d e < ⊤}

@[simp] theorem UCPMOn.mem_component {Y : Type*} [TopologicalSpace Y]
    (R : RangeSet) (d e : UCPMOn Y R) :
    e ∈ UCPMOn.component R d ↔ e ∈ UMetOn Y R ∧ edist d e < ⊤ := by
  sorry

theorem UCPMOn.component_subset_UMetOn {Y : Type*} [TopologicalSpace Y]
    (R : RangeSet) (d : UCPMOn Y R) :
    UCPMOn.component R d ⊆ UMetOn Y R := by
  sorry

theorem UCPMOn.self_mem_component {Y : Type*} [TopologicalSpace Y]
    (R : RangeSet) {d : UCPMOn Y R} (hd : d ∈ UMetOn Y R) :
    d ∈ UCPMOn.component R d := by
  sorry

/-- Components are constant along their own finite-distance locus.  The
statement is included at B0 so later proof blocks have the intended
component interface visible. -/
theorem UCPMOn.component_eq_of_mem {Y : Type*} [TopologicalSpace Y]
    (R : RangeSet) {d e : UCPMOn Y R} (he : e ∈ UCPMOn.component R d) :
    UCPMOn.component R e = UCPMOn.component R d := by
  sorry

/-! ## E2c: construction-controlled data for a general space -/

/-- **E2c, the construction-controlled ultrametric extensor data.**

This is “construction data from the proofs of Theorem 3.1 and Theorem 4.7 of
Ishiki, *A factorization of metric spaces*”, as recorded in §4 of the active
audit note.  It is attached to a compatible ambient ultrametric `d`, a
nonzero `a ∈ R`, and a closed discrete maximal `a`-separated set `A`.

The contained ordinary bundle is `IsUltraIsometricExtensor`, using the bottom
topology on `↥A`: its domain is already the bare `UMet ↥A R` used by the
construction and its `restrict_toUCPMOn` interface has exactly the restriction
shape consumed here.  The closed embedding carried by that bundle, together
with the explicit fields below, records that `A` is a closed discrete carrier
in `Y`.

This is a separate, construction-specific package.  E2c must never become a
field of either ordinary E2 bundle, `IsUltraIsometricExtensor` or
`IsUltraIsometricExtensorOn`; adding these estimates there would silently
strengthen every existing consumer of E2.

The package is now exactly `toExtensor` plus the component-control estimate.
The restriction, isometry, and compatibility facts are derived one-line
theorems from `toExtensor` immediately below this structure, rather than
independent fields, since `IsUltraIsometricExtensor` already supplies them. -/
structure IsUltraComponentControlledExtensorOn
    {Y : Type*} [TopologicalSpace Y] (R : RangeSet) (A : Set Y)
    (d : UCPMOn Y R) (a : ℝ) where
  /-- (a) The ordinary E2 extensor value for the closed discrete carrier `A`. -/
  toExtensor :
    IsUltraIsometricExtensor (⊥ : TopologicalSpace ↥A) R
      (Subtype.val : ↥A → Y)
  /-- (e) The extension of `d|_{A²}` lies in the component of `d`.

  The subtype proof in this field is the compatibility of the restriction,
  supplied by the explicit ambient membership argument and the closed embedding
  in `toExtensor`; the statement
  exposes only the required finiteness bound, not a numerical bound. -/
  component_control :
    ∀ (hd : d ∈ UMetOn Y R),
      edist
          (toExtensor.toUCPMOn
            ⟨UCPMOn.restrict (Subtype.val : ↥A → Y) d,
              UCPM.isCompatible_comap_of_mem_UMetOn
                (⊥ : TopologicalSpace ↥A)
                (by
                  letI : TopologicalSpace ↥A := ⊥
                  exact toExtensor.closedEmbedding.toIsEmbedding :
                    @Topology.IsEmbedding ↥A Y ⊥ inferInstance
                      (Subtype.val : ↥A → Y))
                toExtensor.domain_discrete hd⟩)
          d < ⊤

theorem IsUltraComponentControlledExtensorOn.restrict
    {Y : Type*} [TopologicalSpace Y] {A : Set Y} {d : UCPMOn Y R} {a : ℝ}
    (E : IsUltraComponentControlledExtensorOn R A d a)
    (u : ↥(UMet ↥A R)) :
    UCPMOn.restrict (Subtype.val : ↥A → Y) (E.toExtensor.toUCPMOn u) =
      (u : UCPM ↥A R) := E.toExtensor.restrict_toUCPMOn u

theorem IsUltraComponentControlledExtensorOn.isometry_toUCPMOn
    {Y : Type*} [TopologicalSpace Y] {A : Set Y} {d : UCPMOn Y R} {a : ℝ}
    (E : IsUltraComponentControlledExtensorOn R A d a)
    (u v : ↥(UMet ↥A R)) :
    edist (E.toExtensor.toUCPMOn u) (E.toExtensor.toUCPMOn v) = edist u v :=
  E.toExtensor.isometry_toUCPMOn u v

theorem IsUltraComponentControlledExtensorOn.umet_preservation
    {Y : Type*} [TopologicalSpace Y] {A : Set Y} {d : UCPMOn Y R} {a : ℝ}
    (E : IsUltraComponentControlledExtensorOn R A d a) (u : ↥(UMet ↥A R)) :
    E.toExtensor.toUCPMOn u ∈ UMetOn Y R := E.toExtensor.umet_preservation u

/-! ## B1: the maximal separated net and its centre map -/

/-- A compatible ultrametric on a nonseparable space has a maximal separated
net at a characteristic scale.  The strict separation retained in the first
clause is the form supplied by `exists_maximal_separated`; its non-strict
version is used to derive closedness and discreteness exactly through the
standard metric lemmas. -/
theorem exists_maximal_aScale_separated_net
    {Y : Type*} [TopologicalSpace Y] (d : UCPMOn Y R)
    (hd : d ∈ UMetOn Y R)
    (hY : ¬ TopologicalSpace.SeparableSpace Y)
    (hR : R.IsCharacteristic) :
    ∃ a : ℝ, a ∈ R.carrier ∧ a ≠ 0 ∧ ∃ A : Set Y,
      A.Pairwise (fun x y => a < d.1.1 x y) ∧
        (∀ x : Y, ∃ y ∈ A, d.1.1 x y ≤ a) ∧
          ¬ A.Countable ∧ IsClosed A ∧ DiscreteTopology ↥A := by
  obtain ⟨hmetric, htop⟩ := hd
  letI : MetricSpace Y := hmetric.toMetricSpace.replaceTopology htop.symm
  obtain ⟨ε, hε, hεnet⟩ := exists_pos_no_countable_net hY
  let a : ℝ := RangeSet.smallElt R hR ε
  have ha_mem : a ∈ R.carrier := by
    exact RangeSet.smallElt_mem R hR hε
  have ha_pos : 0 < a := by
    exact RangeSet.smallElt_pos R hR hε
  have ha_lt : a < ε := by
    exact RangeSet.smallElt_lt R hR hε
  obtain ⟨A, hAsep, hAnet⟩ :=
    exists_maximal_separated (X := Y) a ha_pos
  have hAsep_le : A.Pairwise (fun x y => a ≤ d.1.1 x y) := by
    intro x hx y hy hxy
    exact (hAsep hx hy hxy).le
  have hAunc : ¬ A.Countable := by
    intro hAcount
    apply hεnet
    refine ⟨A, hAcount, ?_⟩
    intro x
    obtain ⟨y, hyA, hxy⟩ := hAnet x
    exact ⟨y, hyA, hxy.trans ha_lt.le⟩
  have hAclosed : IsClosed A :=
    Metric.isClosed_of_pairwise_le_dist ha_pos hAsep_le
  letI : DiscreteTopology (A) :=
    DiscreteTopology.of_forall_le_dist ha_pos (by
      intro x y hxy
      exact hAsep_le x.2 y.2 (by
        intro hxy'
        exact hxy (Subtype.ext hxy')))
  exact ⟨a, ha_mem, ne_of_gt ha_pos, A, hAsep, hAnet, hAunc, hAclosed,
    inferInstance⟩

/-- Choose, from an `a`-net, one point of the net at `d`-distance at most
`a` from each point.  The definition is expressed using `d.1.1`, so it is
available without making a particular transported `MetricSpace` instance
part of the declaration's type. -/
noncomputable def centreMap
    {Y : Type*} [TopologicalSpace Y] (d : UCPMOn Y R) (a : ℝ) (A : Set Y)
    (hnet : ∀ x : Y, ∃ y ∈ A, d.1.1 x y ≤ a) : Y → ↥A :=
  fun x =>
    ⟨Classical.choose (hnet x), (Classical.choose_spec (hnet x)).1⟩

/-- The chosen centre is within the net radius of its source point. -/
theorem centreMap_dist_le
    {Y : Type*} [TopologicalSpace Y] (d : UCPMOn Y R) (a : ℝ) (A : Set Y)
    (hnet : ∀ x : Y, ∃ y ∈ A, d.1.1 x y ≤ a) (x : Y) :
    d.1.1 x (centreMap d a A hnet x : Y) ≤ a := by
  exact (Classical.choose_spec (hnet x)).2

/-- The centre map is continuous for the topology induced by a compatible
ultrametric.  The proof uses the clopen equal-radius closed-ball partition:
the chosen centre is in a closed `a`-ball, and strict separation makes two
such centre balls disjoint unless their centres agree. -/
theorem continuous_centreMap
    {Y : Type*} [TopologicalSpace Y] (d : UCPMOn Y R)
    (hd : d ∈ UMetOn Y R) (a : ℝ) (A : Set Y) (ha : 0 < a)
    (hAsep : A.Pairwise (fun x y => a < d.1.1 x y))
    (hnet : ∀ x : Y, ∃ y ∈ A, d.1.1 x y ≤ a) :
    Continuous (centreMap d a A hnet) := by
  obtain ⟨hmetric, htop⟩ := hd
  letI : MetricSpace Y := hmetric.toMetricSpace.replaceTopology htop.symm
  have hUltra : @IsUltrametricDist Y ⟨d.1.1⟩ :=
    d.1.2.toIsUltrametricDist
  letI : IsUltrametricDist Y := hUltra
  have hlocal : ∀ x x' : Y, x' ∈ Metric.closedBall x a →
      centreMap d a A hnet x' = centreMap d a A hnet x := by
    intro x x' hx'
    have hx'dist : dist x' x ≤ a := by
      simpa only [Metric.mem_closedBall] using hx'
    have hx'centre : x' ∈ Metric.closedBall
        (centreMap d a A hnet x : Y) a := by
      rw [Metric.mem_closedBall]
      exact (dist_triangle_max x' x (centreMap d a A hnet x : Y)).trans
        (max_le hx'dist (by
          change d.1.1 x (centreMap d a A hnet x : Y) ≤ a
          exact centreMap_dist_le d a A hnet x))
    have hx'centre' : x' ∈ Metric.closedBall
        (centreMap d a A hnet x' : Y) a := by
      rw [Metric.mem_closedBall]
      change d.1.1 x' (centreMap d a A hnet x' : Y) ≤ a
      exact centreMap_dist_le d a A hnet x'
    rcases IsUltrametricDist.closedBall_eq_or_disjoint
        (x := (centreMap d a A hnet x : Y))
        (y := (centreMap d a A hnet x' : Y)) (r := a) with hballs | hdisj
    · have hcentre : (centreMap d a A hnet x' : Y) ∈
          Metric.closedBall (centreMap d a A hnet x : Y) a := by
        rw [hballs]
        exact Metric.mem_closedBall_self ha.le
      have hcentre_dist : dist (centreMap d a A hnet x' : Y)
          (centreMap d a A hnet x : Y) ≤ a := by
        simpa only [Metric.mem_closedBall] using hcentre
      apply Subtype.ext
      by_contra hne
      have hlt : a < dist (centreMap d a A hnet x' : Y)
          (centreMap d a A hnet x : Y) := by
        exact hAsep (centreMap d a A hnet x').property
          (centreMap d a A hnet x).property hne
      exact (not_lt_of_ge hcentre_dist) hlt
    · exact (hdisj.le_bot ⟨hx'centre, hx'centre'⟩).elim
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  refine Filter.EventuallyEq.continuousAt
    (y := centreMap d a A hnet x) ?_
  filter_upwards [Metric.closedBall_mem_nhds x ha] with x' hx'
  exact hlocal x x' hx'

/-! ## B0 capstone statement signatures -/

/-- The component clause of `cor:nonseparable-ultrametric-nonborel` from audit
§2.19: every finite-distance component of `UMetOn Y R` is non-Borel in the
existing `UCPMOn Y R` measurable space, under the separately named E2c
construction package. -/
theorem not_measurableSet_UCPMOn_component_of_isUltraComponentControlledExtensorOn
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y)
    (hYsep : ¬ TopologicalSpace.SeparableSpace Y)
    (hR : R.IsCharacteristic)
    (hEx : ∀ (d : UCPMOn Y R), d ∈ UMetOn Y R →
      ∀ (a : ℝ), a ∈ R.carrier → a ≠ 0 →
        ∀ (A : Set Y),
          A.Nonempty → IsClosed A → DiscreteTopology ↥A →
            A.Pairwise (fun x y => a ≤ d.1.1 x y) →
            (∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a) →
          Nonempty (IsUltraComponentControlledExtensorOn R A d a)) :
    ∀ d ∈ UMetOn Y R, ¬ MeasurableSet (UCPMOn.component R d) := by
  sorry

/-- The whole-locus clause of `cor:nonseparable-ultrametric-nonborel` from
audit §2.19: `UMetOn Y R` itself is non-Borel in the same existing ambient
measurable space, under the same E2c package. -/
theorem not_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y)
    (hYsep : ¬ TopologicalSpace.SeparableSpace Y)
    (hR : R.IsCharacteristic)
    (hEx : ∀ (d : UCPMOn Y R), d ∈ UMetOn Y R →
      ∀ (a : ℝ), a ∈ R.carrier → a ≠ 0 →
        ∀ (A : Set Y),
          A.Nonempty → IsClosed A → DiscreteTopology ↥A →
            A.Pairwise (fun x y => a ≤ d.1.1 x y) →
            (∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a) →
          Nonempty (IsUltraComponentControlledExtensorOn R A d a)) :
    ¬ MeasurableSet (UMetOn Y R) := by
  sorry

end
end IshikiExt
