-- Ext.GeneralSeparability
--
-- Issue #57, phase 2: the general-space transfer for the Borel metric locus.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.8, §3
-- (E1), and §7.  E1 is represented below by an explicit hypothesis bundle;
-- it is not added to Lean as an axiom or an instance.

import IshikiConj51.Ext.CPM
import IshikiConj51.Ext.GeneralSpace

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

-- `cpmMeasurableSpace`/`cpmBorelSpace` are already declared (as `local
-- instance`s) by the `Ext.CPM` import above; no need to repeat them here.

/-! ## The topology-aware metric locus -/

/-- The compatible metrics on a topological space, viewed in `CPM X`.

`CPM.Met` in `Ext.CPM` is the special case for a bare discrete carrier.  The
general-space theorem needs the topology supplied by the ambient `X`, so it
uses this explicitly parameterised version. -/
def CPM.MetOn (X : Type*) [TopologicalSpace X] : Set (CPM X) :=
  {d | ∃ h : IsMetricOn d.1, h.topology = (inferInstance : TopologicalSpace X)}

/- `#print axioms IshikiExt.CPM.MetOn`:
   `[propext, Classical.choice, Quot.sound]`. -/

@[simp] theorem mem_CPM_MetOn {X : Type*} [TopologicalSpace X] {d : CPM X} :
    d ∈ CPM.MetOn X ↔ ∃ h : IsMetricOn d.1,
      h.topology = (inferInstance : TopologicalSpace X) := Iff.rfl

/- `#print axioms IshikiExt.mem_CPM_MetOn`:
   `[propext, Classical.choice, Quot.sound]`. -/

/-! ## The explicit E1 hypothesis bundle -/

/-- An explicit isometric extensor from a closed discrete carrier into `X`.

The topology `tA` is an explicit parameter because `CPM A` itself is defined
for a bare carrier.  `domain_discrete` records that the carrier is the closed
discrete subspace selected in the general-space argument.  The final field is
the only E1 input used by the Borel transfer theorem. -/
structure IsIsometricExtensor {A X : Type*} (tA : TopologicalSpace A)
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] (ι : A → X) where
  closedEmbedding : @Topology.IsClosedEmbedding A X tA inferInstance ι
  domain_discrete : tA = ⊥
  toCPM : CPM A → CPM X
  extension : ∀ (d : CPM A) (a b : A),
    (toCPM d).1 (ι a) (ι b) = d.1 a b
  isometry_toCPM : Isometry toCPM
  met_preservation : toCPM '' CPM.Met A ⊆ CPM.MetOn X

/- `#print axioms IshikiExt.IsIsometricExtensor`:
   `[propext, Classical.choice, Quot.sound]`.  (The bundle is a plain
   structure, not a `Prop`: `toCPM` is data, and a `Prop`-valued structure
   cannot expose a data-valued field via projection.) -/

private theorem isMetricOn_restrict_of_mem_MetOn
    {A X : Type*} {tA : TopologicalSpace A} [TopologicalSpace X]
    {ι : A → X} (hι : @Topology.IsEmbedding A X tA inferInstance ι)
    (htA : tA = ⊥) {d : CPM A} {e : CPM X}
    (he : e ∈ CPM.MetOn X)
    (hrestrict : ∀ a b : A, e.1 (ι a) (ι b) = d.1 a b) :
    d ∈ CPM.Met A := by
  obtain ⟨hmetric, htop⟩ := he
  have hmetric' : IsMetricOn d.1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      rw [← hrestrict a a, hmetric.dist_self]
    · intro a b hab
      apply hι.injective
      apply hmetric.eq_of_dist_eq_zero
      rw [hrestrict]
      exact hab
    · intro a b
      rw [← hrestrict a b, ← hrestrict b a, hmetric.dist_comm]
    · intro a b c
      rw [← hrestrict a c, ← hrestrict a b, ← hrestrict b c]
      exact hmetric.dist_triangle _ _ _
  have htop_induced : hmetric'.topology = tA := by
    let mA : MetricSpace A := MetricSpace.induced ι hι.injective hmetric.toMetricSpace
    have hmA : hmetric'.toMetricSpace = mA := by
      apply MetricSpace.ext
      ext a b
      change d.1 a b = (hmetric.toMetricSpace).dist (ι a) (ι b)
      exact (hrestrict a b).symm
    rw [hmetric'.topology_eq_metricSpace_topology, hmA]
    change TopologicalSpace.induced ι hmetric.topology = tA
    rw [htop]
    exact hι.eq_induced.symm
  exact ⟨hmetric', htop_induced.trans htA⟩

/-- The `Met` image identity is derived from extension and restriction; it is
not an additional hypothesis of `IsIsometricExtensor`. -/
theorem IsIsometricExtensor.image_met_eq_range_inter
    {A X : Type*} {tA : TopologicalSpace A} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X]
    {ι : A → X} (hE : IsIsometricExtensor tA ι) :
    hE.toCPM '' CPM.Met A = Set.range hE.toCPM ∩ CPM.MetOn X := by
  ext e
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, rfl⟩, hE.met_preservation ⟨d, hd, rfl⟩⟩
  · rintro ⟨⟨d, rfl⟩, hd⟩
    refine ⟨d, ?_, rfl⟩
    exact isMetricOn_restrict_of_mem_MetOn hE.closedEmbedding.toIsEmbedding
      hE.domain_discrete hd (hE.extension d)

/- `#print axioms IshikiExt.IsIsometricExtensor.image_met_eq_range_inter`:
   `[propext, Classical.choice, Quot.sound]`. -/

/-! ## The Borel transfer -/

/-
  Deferred capstone (exact intended statement, with no weakened proxy):

  theorem separable_of_measurableSet_CPM_MetOn
      {X : Type*} [MetricSpace X]
      {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
      (hSnonmeas : ¬ MeasurableSet S)
      (hMet : MeasurableSet (CPM.MetOn X))
      {ι : ExtIndex S → X}
      (hE : IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S))
        ι) :
      TopologicalSpace.SeparableSpace X

  The remaining proof must use `met_not_borel hS hSnonmeas`, completeness of
  `CPM (ExtIndex S)`, the closed range of `hE.toCPM`, and the derived image
  identity above.  It is deferred to a follow-up issue: a `CompleteSpace
  (CPM D)` instance is not yet available.  The CPM-level relabelling layer
  needed to restate it for an arbitrary carrier landed with Issue #63
  (`Ext/Relabel.lean`), so only the completeness prerequisite remains.
-/

end
end IshikiExt
