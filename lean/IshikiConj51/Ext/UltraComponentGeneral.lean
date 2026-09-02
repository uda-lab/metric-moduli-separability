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
strengthen every existing consumer of E2. -/
structure IsUltraComponentControlledExtensorOn
    {Y : Type*} [TopologicalSpace Y] (R : RangeSet) (A : Set Y)
    (d : UCPMOn Y R) (a : ℝ) where
  /-- (a) The ordinary E2 extensor value for the closed discrete carrier `A`. -/
  toExtensor :
    IsUltraIsometricExtensor (⊥ : TopologicalSpace ↥A) R
      (Subtype.val : ↥A → Y)
  /-- (b) Restricting the extensor to `A²` returns the input ultrametric. -/
  restrict : ∀ u : ↥(UMet ↥A R),
    UCPMOn.restrict (Subtype.val : ↥A → Y) (toExtensor.toUCPMOn u) =
      (u : UCPM ↥A R)
  /-- (c) The extensor is an exact isometry for the `𝒰𝒟^R` ambient distance. -/
  isometry_toUCPMOn : ∀ u v : ↥(UMet ↥A R),
    edist (toExtensor.toUCPMOn u) (toExtensor.toUCPMOn v) = edist u v
  /-- (d) The extensor preserves compatibility. -/
  umet_preservation : ∀ u : ↥(UMet ↥A R),
    toExtensor.toUCPMOn u ∈ UMetOn Y R
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
