-- Ext.GeneralSeparability
--
-- Issue #57, phase 2, Issue #66 and Issue #72: the general-space transfer for
-- the Borel metric locus, the Route M theorems, and the bridge that makes them
-- conditional on E1 as audited rather than on a transported bundle.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §1 (ambient
-- conventions), §2.8 (Theorem 3.5), §3 (E1), §4 (Route M), and §7.  E1 is
-- represented below by an explicit hypothesis bundle; it is not added to Lean
-- as an axiom or an instance.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.CPM
import IshikiConj51.Ext.GeneralSpace
import IshikiConj51.Ext.Relabel

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

-- `cpmMeasurableSpace`/`cpmBorelSpace` are declared as `local instance`s in
-- `Ext.CPM`; a `local` attribute does not survive the import, so the two
-- constants have to be re-registered here.  They are the same constants, so the
-- σ-algebra in `met_not_borel`'s statement is the one used below.
attribute [local instance] cpmMeasurableSpace cpmBorelSpace

/-! ## The continuous-pseudometric ambient of a topological space

`CPM X` from `Ext.CPM` is the space of *all* finite-valued pseudometrics on the
bare type `X`.  That is the preprint's `CPM(X)` only when `X` is discrete, which
is the case `Ext.CPM` was written for.  For a general topological space the
preprint's ambient is the space of **continuous** pseudometrics
(`notes/borel-preprint-audit.md` §1: `d : X × X → [0,∞)` continuous, with the
extended-valued supremum metric `𝒟_X`), and the hypothesis "`Met(X)` is Borel"
of Theorem 3.5 refers to that smaller space.  Borelness in the larger
all-pseudometrics ambient is a strictly stronger hypothesis, so it must not be
substituted here.

`CPMOn X` is that space: the subtype of `CPM X` cut out by joint continuity.
Mathlib's subtype `EMetricSpace` instance restricts the distance
(`Subtype.edist_eq` is `rfl`), so the metric is literally `𝒟_X`.

The extensor's *domain* stays the bare `CPM A`: E1 is applied to a closed
**discrete** subspace `A`, where every map is continuous, so the preprint's
`CPM(A)` is the set of all pseudometrics on `A` — the existing `CPM A`.  (The
two subtypes `CPMOn A` and `CPM A` are then isometrically equivalent, but not
definitionally identical; the equivalence is not needed anywhere below.) -/

/-- The preprint's `CPM(X)`: the continuous pseudometrics on a topological
space `X`, with the extended supremum distance. -/
def CPMOn (X : Type*) [TopologicalSpace X] : Type _ :=
  {d : CPM X // Continuous (Function.uncurry d.1)}

namespace CPMOn

variable {X : Type*} [TopologicalSpace X]

noncomputable instance : EMetricSpace (CPMOn X) :=
  inferInstanceAs (EMetricSpace {d : CPM X // Continuous (Function.uncurry d.1)})

/-- The distance of `CPMOn X` is the restriction of the distance of `CPM X`. -/
@[simp] theorem edist_eq (d e : CPMOn X) : edist d e = CPM.edist d.1 e.1 := rfl

end CPMOn

local instance cpmOnMeasurableSpace (X : Type*) [TopologicalSpace X] :
    MeasurableSpace (CPMOn X) := borel (CPMOn X)

local instance cpmOnBorelSpace (X : Type*) [TopologicalSpace X] :
    BorelSpace (CPMOn X) := ⟨rfl⟩

/-! ## The topology-aware metric locus -/

/-- The compatible metrics on a topological space, viewed in `CPMOn X`.

`CPM.Met` in `Ext.CPM` is the corresponding locus for a bare discrete carrier.
The general-space theorem needs the topology supplied by the ambient `X`, so it
uses this explicitly parameterised version. -/
def CPM.MetOn (X : Type*) [TopologicalSpace X] : Set (CPMOn X) :=
  {d | ∃ h : IsMetricOn d.1.1, h.topology = (inferInstance : TopologicalSpace X)}

/- `#print axioms IshikiExt.CPM.MetOn`:
   `[propext, Classical.choice, Quot.sound]`. -/

@[simp] theorem mem_CPM_MetOn {X : Type*} [TopologicalSpace X] {d : CPMOn X} :
    d ∈ CPM.MetOn X ↔ ∃ h : IsMetricOn d.1.1,
      h.topology = (inferInstance : TopologicalSpace X) := Iff.rfl

/- `#print axioms IshikiExt.mem_CPM_MetOn`:
   `[propext, Classical.choice, Quot.sound]`. -/

/-! ## Discrete carriers: the two ambients agree

The two results here justify keeping the extensor's *domain* at the bare
`CPM A` rather than at `CPMOn A`: on a discrete carrier the continuity
constraint is vacuous, so the preprint's `CPM(A)` really is the set of all
pseudometrics on `A`, and the two metric loci correspond.  The correspondence
is an isometric equivalence, not a definitional identity, which is why it is
recorded rather than assumed.

Neither result is consumed by the transfer theorems themselves — the transfer
never has to cross between the ambients, which is by design.  Both are consumed
by the E1 bridge (`IsIsometricExtensorOn.toIsIsometricExtensor`), where crossing
is exactly the point. -/

/-- On a discrete carrier the continuity constraint is vacuous: `CPMOn D` and
the bare pseudometric ambient `CPM D` are isometrically equivalent. -/
noncomputable def CPMOn.equivCPM (D : Type*) [TopologicalSpace D]
    [DiscreteTopology D] : CPMOn D ≃ᵢ CPM D where
  toEquiv := Equiv.ofBijective (Subtype.val : CPMOn D → CPM D)
    ⟨Subtype.coe_injective,
      fun d => ⟨⟨d, continuous_of_discreteTopology⟩, rfl⟩⟩
  isometry_toFun := fun _ _ => rfl

@[simp] theorem CPMOn.equivCPM_apply {D : Type*} [TopologicalSpace D]
    [DiscreteTopology D] (d : CPMOn D) : CPMOn.equivCPM D d = d.1 := rfl

/-- Under that equivalence the topology-aware metric locus of a discrete
carrier is the bare-discrete metric locus of `Ext.CPM`. -/
theorem CPMOn.preimage_equivCPM_met (D : Type*) [TopologicalSpace D]
    [DiscreteTopology D] :
    CPMOn.equivCPM D ⁻¹' CPM.Met D = CPM.MetOn D := by
  have hbot : (inferInstance : TopologicalSpace D) = ⊥ := DiscreteTopology.eq_bot
  ext d
  constructor
  · rintro ⟨h, htop⟩
    exact ⟨h, htop.trans hbot.symm⟩
  · rintro ⟨h, htop⟩
    exact ⟨h, htop.trans hbot⟩

/-- The inverse of `CPMOn.equivCPM` forgets nothing: it re-attaches the
continuity proof that a discrete carrier supplies for free. -/
@[simp] theorem CPMOn.coe_equivCPM_symm {D : Type*} [TopologicalSpace D]
    [DiscreteTopology D] (d : CPM D) : ((CPMOn.equivCPM D).symm d).1 = d :=
  (CPMOn.equivCPM D).apply_symm_apply d

/-! ## Relabelling the continuous-pseudometric ambient

`Ext/Relabel.lean` transports `BddPMet` and `CPM` along a bijection of bare
carriers.  `CPMOn` also carries a topology, so its transport needs a
homeomorphism `σ : D ≃ₜ E`; the pseudometric content is `CPM.comap σ`, and the
continuity field transports because `σ × σ` is continuous.  The supremum
distance is the one `CPM` already has (`CPMOn.edist_eq`), so `CPM.edist_comap`
supplies the isometry unchanged.

The metric-locus identity is the one place where the extra topology does work.
For bare carriers `Ext/Relabel.lean` only has to preserve "`d` induces the
discrete topology", the same condition at both ends; here the condition is
"`d` induces the topology of its carrier", and the two carriers have different
topologies.  `topology_comap` is what crosses between them: a relabelled metric
induces the relabelled topology, and `σ` being a homeomorphism identifies that
with the topology of `D`. -/

namespace CPMOn

variable {D E : Type*} [TopologicalSpace D] [TopologicalSpace E]

/-- Relabelling along a homeomorphism `σ : D ≃ₜ E` pulls a continuous
pseudometric on `E` back to a continuous pseudometric on `D`. -/
def comap (σ : D ≃ₜ E) (d : CPMOn E) : CPMOn D :=
  ⟨CPM.comap σ.toEquiv d.1, by
    have huncurry : Function.uncurry (CPM.comap σ.toEquiv d.1).1
        = Function.uncurry d.1.1 ∘ Prod.map (σ : D → E) (σ : D → E) := rfl
    rw [huncurry]
    exact d.2.comp (σ.continuous.prodMap σ.continuous)⟩

@[simp] theorem comap_coe (σ : D ≃ₜ E) (d : CPMOn E) :
    (comap σ d).1 = CPM.comap σ.toEquiv d.1 := rfl

theorem isometry_comap (σ : D ≃ₜ E) : Isometry (comap σ : CPMOn E → CPMOn D) :=
  fun d e => CPM.edist_comap σ.toEquiv d.1 e.1

/-- `CPM(E) ≃ CPM(D)` for any homeomorphism `σ : D ≃ₜ E`, in the preprint's
continuous-pseudometric ambient. -/
def relabelEquiv (σ : D ≃ₜ E) : CPMOn E ≃ CPMOn D where
  toFun := comap σ
  invFun := comap σ.symm
  left_inv _ := Subtype.ext (Subtype.ext (by funext x y; simp))
  right_inv _ := Subtype.ext (Subtype.ext (by funext x y; simp))

@[simp] theorem relabelEquiv_apply (σ : D ≃ₜ E) (d : CPMOn E) :
    relabelEquiv σ d = comap σ d := rfl

/-- The relabelling bijection is an isometry of the supremum distance, hence a
homeomorphism `CPM(E) ≃ₜ CPM(D)`. -/
def relabelIsometry (σ : D ≃ₜ E) : CPMOn E ≃ᵢ CPMOn D where
  toEquiv := relabelEquiv σ
  isometry_toFun := isometry_comap σ

end CPMOn

/-- Relabelling preserves the topology-aware metric locus, in both directions.
This is the `CPMOn` analogue of `CPM.preimage_Met_comap`: there the condition
transported is "induces the discrete topology", here it is "induces the
topology of the ambient", and `topology_comap_eq_iff` is what matches the two
ambients' topologies across `σ`. -/
theorem CPMOn.preimage_MetOn_comap {D E : Type*} [TopologicalSpace D]
    [TopologicalSpace E] (σ : D ≃ₜ E) :
    CPMOn.comap σ ⁻¹' CPM.MetOn D = CPM.MetOn E := by
  ext d
  show (∃ h : IsMetricOn fun x y => d.1.1 (σ.toEquiv x) (σ.toEquiv y),
      h.topology = (inferInstance : TopologicalSpace D)) ↔
    (∃ h : IsMetricOn d.1.1, h.topology = (inferInstance : TopologicalSpace E))
  constructor
  · rintro ⟨h, htop⟩
    exact ⟨isMetricOn_of_comap σ.toEquiv h,
      (topology_comap_eq_iff σ (isMetricOn_of_comap σ.toEquiv h)).mp htop⟩
  · rintro ⟨h, htop⟩
    exact ⟨isMetricOn_comap σ.toEquiv h, (topology_comap_eq_iff σ h).mpr htop⟩

/-! ## The explicit E1 hypothesis bundle -/

/-- An explicit isometric extensor from a closed discrete carrier into `X`.

The topology `tA` is an explicit parameter because `CPM A` itself is defined
for a bare carrier.  `domain_discrete` records that the carrier is the closed
discrete subspace selected in the general-space argument; on such a carrier the
preprint's `CPM(A)` is exactly `CPM A` (`CPMOn.equivCPM` above), which is why
the domain of `toCPM` is not a `CPMOn`.  The last field is the only E1 clause
used by the Borel transfer theorem beyond `extension` and `isometry_toCPM`.

Scope, stated exactly.  This bundle is *not* E1 (audit §3): E1 quantifies over
an arbitrary closed subset `A ⊆ X` and supplies `Ẽ : CPM(A) → CPM(X)`, whereas
this bundle fixes an abstract carrier `A` together with a closed embedding `ι`
and takes the extensor already transported along `ι`.  E1 itself is
`IsIsometricExtensorOn` below, and
`IsIsometricExtensorOn.toIsIsometricExtensor` performs the transport, so the
theorems of this file are available in both forms. -/
structure IsIsometricExtensor {A X : Type*} (tA : TopologicalSpace A)
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] (ι : A → X) where
  closedEmbedding : @Topology.IsClosedEmbedding A X tA inferInstance ι
  domain_discrete : tA = ⊥
  toCPM : CPM A → CPMOn X
  extension : ∀ (d : CPM A) (a b : A),
    (toCPM d).1.1 (ι a) (ι b) = d.1 a b
  isometry_toCPM : Isometry toCPM
  met_preservation : toCPM '' CPM.Met A ⊆ CPM.MetOn X

/- `#print axioms IshikiExt.IsIsometricExtensor`:
   `[propext, Classical.choice, Quot.sound]`.  (The bundle is a plain
   structure, not a `Prop`: `toCPM` is data, and a `Prop`-valued structure
   cannot expose a data-valued field via projection.) -/

/-! ## E1 itself -/

/-- **E1 (audit §3), for one closed subset.**  Ishiki, *An isometric extensor
of metrics*, arXiv:2407.03030, Theorem 1.1: for a metrizable `X` and a closed
`A ⊆ X` there is an isometric extensor `Ẽ : CPM(A) → CPM(X)` of continuous
pseudometrics restricting to the identity on `A²` and carrying `Met(A)` into
`Met(X)`.

Field by field against the source statement: `extension` is clause (1)
(`Ẽ(d)|_{A²} = d`), `isometry_toCPM` is clause (2)
(`𝒟_A(d,e) = 𝒟_X(Ẽd,Ẽe)`, at the extended-metric level `𝒟` lives at), and
`met_preservation` is the inclusion half of the "furthermore" clause
`Ẽ(Met(A)) = Ẽ(CPM(A)) ∩ Met(X)`.  The reverse inclusion is deliberately not a
field: the transfer does not need it, and its transported form comes back out
as `IsIsometricExtensor.image_met_eq_range_inter`.  E1's clauses (3) and (4) —
`BMet` and `Comp` preservation — are also omitted: they are used only by the
§2.10 and §2.12 extensions, and (4) additionally needs "`X` completely
metrizable" per the caveat in audit §3.

What is left is Route M's share of E1 (audit §4), with no carrier-specific
choices: `A` ranges over the subsets of `X`, and both ambients are the
preprint's continuous-pseudometric ones.  Quantifying over the closed `A` is
how the theorems at the end of this file take it. -/
structure IsIsometricExtensorOn {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set X) where
  closed : IsClosed A
  toCPM : CPMOn ↥A → CPMOn X
  extension : ∀ (d : CPMOn ↥A) (a b : ↥A), (toCPM d).1.1 ↑a ↑b = d.1.1 a b
  isometry_toCPM : Isometry toCPM
  met_preservation : toCPM '' CPM.MetOn ↥A ⊆ CPM.MetOn X

/- `#print axioms IshikiExt.IsIsometricExtensorOn`:
   `[propext, Classical.choice, Quot.sound]`. -/

/-- **The E1 bridge.**  E1 applied to the closed subset `Set.range ι` yields the
transported bundle the transfer theorems consume, for any closed embedding `ι`
of a discrete carrier.

Two moves, in this order.  `ι` is an embedding, so it is a homeomorphism onto
`↥(Set.range ι)`; `CPMOn.comap` relabels the extensor's domain along it, which
is where the `CPMOn`-level relabelling layer is used.  The relabelled domain
`CPMOn A` is then dropped to the bare `CPM A` by `CPMOn.equivCPM`, which is an
isometric equivalence because `A` is discrete.  `met_preservation` follows the
same two steps through `CPMOn.preimage_equivCPM_met` and
`CPMOn.preimage_MetOn_comap`.

`↥(Set.range ι)` is discrete because `ι` is an embedding out of a `⊥`-space, so
`CPMOn.equivCPM`'s hypothesis is met after the relabelling as well. -/
noncomputable def IsIsometricExtensorOn.toIsIsometricExtensor
    {A X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {ι : A → X} (hι : @Topology.IsClosedEmbedding A X ⊥ inferInstance ι)
    (hE : IsIsometricExtensorOn (Set.range ι)) :
    IsIsometricExtensor (⊥ : TopologicalSpace A) ι := by
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  let σ : A ≃ₜ ↥(Set.range ι) := hι.toIsEmbedding.toHomeomorph
  haveI : DiscreteTopology ↥(Set.range ι) := σ.symm.isEmbedding.discreteTopology
  have hσ : ∀ x : A, σ.symm ⟨ι x, x, rfl⟩ = x := fun x => by
    have : σ x = (⟨ι x, x, rfl⟩ : ↥(Set.range ι)) := Subtype.ext rfl
    rw [← this, Homeomorph.symm_apply_apply]
  refine
    { closedEmbedding := hι
      domain_discrete := rfl
      toCPM := fun d => hE.toCPM (CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d))
      extension := ?_
      isometry_toCPM := ?_
      met_preservation := ?_ }
  · intro d a b
    rw [hE.extension (CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d))
      ⟨ι a, a, rfl⟩ ⟨ι b, b, rfl⟩]
    show ((CPMOn.equivCPM A).symm d).1.1 (σ.symm ⟨ι a, a, rfl⟩)
      (σ.symm ⟨ι b, b, rfl⟩) = d.1 a b
    rw [hσ a, hσ b, CPMOn.coe_equivCPM_symm]
  · exact hE.isometry_toCPM.comp
      ((CPMOn.isometry_comap σ.symm).comp (CPMOn.equivCPM A).symm.isometry)
  · rintro e ⟨d, hd, rfl⟩
    refine hE.met_preservation
      ⟨CPMOn.comap σ.symm ((CPMOn.equivCPM A).symm d), ?_, rfl⟩
    have hMetOn : (CPMOn.equivCPM A).symm d ∈ CPM.MetOn A := by
      rw [← CPMOn.preimage_equivCPM_met A]
      show CPMOn.equivCPM A ((CPMOn.equivCPM A).symm d) ∈ CPM.Met A
      rw [IsometryEquiv.apply_symm_apply]
      exact hd
    rw [← CPMOn.preimage_MetOn_comap σ.symm] at hMetOn
    exact hMetOn

/- `#print axioms IshikiExt.IsIsometricExtensorOn.toIsIsometricExtensor`:
   `[propext, Classical.choice, Quot.sound]`. -/

private theorem isMetricOn_restrict_of_mem_MetOn
    {A X : Type*} {tA : TopologicalSpace A} [TopologicalSpace X]
    {ι : A → X} (hι : @Topology.IsEmbedding A X tA inferInstance ι)
    (htA : tA = ⊥) {d : CPM A} {e : CPMOn X}
    (he : e ∈ CPM.MetOn X)
    (hrestrict : ∀ a b : A, e.1.1 (ι a) (ι b) = d.1 a b) :
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

/-! ## The Borel transfer (audit §2.8, Route M) -/

/-- **Route M, core content of Theorem 3.5.**  An isometric extensor from the
coded `ℵ₁`-sized discrete carrier into `X` forbids Borelness of the metric
locus of `X`.

This is the contrapositive form, and it is the one with mathematical content.
Its hypotheses are satisfiable: E1 produces such a bundle for any closed
discrete copy of the coded carrier inside a metrizable `X`, so the conclusion
is not vacuous — unlike the separability phrasing recorded below, whose
hypotheses are contradictory.  That production is
`IsIsometricExtensorOn.toIsIsometricExtensor`, and
`not_measurableSet_CPM_MetOn_of_isometricExtensorOn` at the end of this file is
the resulting E1-conditional form; E1 itself stays external.  The proof is the
audit's §1 chain — complete domain, closed isometric image, closed sets are Borel,
intersect with the hypothesis, pull back along the (continuous, injective)
extensor — ending at `met_not_borel`, which is consumed verbatim because the
domain of the extensor is the bare `CPM (ExtIndex S)`.

E1 is the hypothesis `hE`; the theorem is conditional on it by design, matching
the audit's EXTERNAL verdict for Theorem 3.5. -/
theorem IsIsometricExtensor.not_measurableSet_CPM_MetOn
    {X : Type*} [MetricSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hSnonmeas : ¬ MeasurableSet S)
    {ι : ExtIndex S → X}
    (hE : IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S)) ι) :
    ¬ MeasurableSet (CPM.MetOn X) := by
  intro hMet
  have hclosed : IsClosed (Set.range hE.toCPM) :=
    isClosed_range_of_isometry_complete _ hE.isometry_toCPM
  have hinter : MeasurableSet (Set.range hE.toCPM ∩ CPM.MetOn X) :=
    hclosed.measurableSet.inter hMet
  rw [← hE.image_met_eq_range_inter] at hinter
  have hpre : MeasurableSet (hE.toCPM ⁻¹' (hE.toCPM '' CPM.Met (ExtIndex S))) :=
    hinter.preimage hE.isometry_toCPM.continuous.measurable
  rw [Set.preimage_image_eq _ hE.isometry_toCPM.injective] at hpre
  exact met_not_borel hS hSnonmeas hpre

/-- A *fixed* extensor bundle out of the coded carrier already refutes
separability, with no Borel hypothesis at all.

A non-Borel `S` is uncountable, so the closed embedding carried by `hE`
exhibits an uncountable closed discrete subspace of `X`; a separable metric
space is second countable, and a second-countable discrete space is countable.

This is stated in order to make the vacuity of the next theorem's hypotheses a
checked fact rather than a remark. -/
theorem IsIsometricExtensor.not_separableSpace
    {X : Type*} [MetricSpace X] {S : Set ℝ}
    (hSnonmeas : ¬ MeasurableSet S)
    {ι : ExtIndex S → X}
    (hE : IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S)) ι) :
    ¬ TopologicalSpace.SeparableSpace X := by
  intro hsep
  haveI := hsep
  letI : TopologicalSpace (ExtIndex S) := ⊥
  haveI : DiscreteTopology (ExtIndex S) := ⟨rfl⟩
  haveI : TopologicalSpace.SeparableSpace (ExtIndex S) :=
    hE.closedEmbedding.toIsEmbedding.separableSpace
  obtain ⟨s, hscount, hsdense⟩ :=
    TopologicalSpace.exists_countable_dense (α := ExtIndex S)
  have hsuniv : s = Set.univ := by
    rw [← (isClosed_discrete s).closure_eq, hsdense.closure_eq]
  rw [hsuniv] at hscount
  haveI : Countable (ExtIndex S) := Set.countable_univ_iff.mp hscount
  have hinj : Function.Injective
      (fun a : ↥S => (Sum.inr (a, none) : ExtIndex S)) := by
    intro a b hab
    simpa using hab
  exact hSnonmeas (Set.countable_coe_iff.mp hinj.countable).measurableSet

/-- **Ex falso; the literal statement of Issue #66.**

Its hypotheses are jointly inconsistent, and
`IsIsometricExtensor.not_separableSpace` above proves it —
`hE` alone contradicts `SeparableSpace X`, independently of `hMet`.  The Lean
proof accordingly reaches the conclusion through `False.elim`.  Nothing is
unsound here — the pair `(hMet, hE)` being contradictory *is* the content of
Theorem 3.5 — but this corollary is not the result; the result is
`IsIsometricExtensor.not_measurableSet_CPM_MetOn` above, and the non-vacuous
separability statement is `separable_of_measurableSet_CPM_MetOn_of_extensors`
below, where the extensor is quantified rather than fixed. -/
theorem separable_of_measurableSet_CPM_MetOn
    {X : Type*} [MetricSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hSnonmeas : ¬ MeasurableSet S)
    (hMet : MeasurableSet (CPM.MetOn X))
    {ι : ExtIndex S → X}
    (hE : IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S)) ι) :
    TopologicalSpace.SeparableSpace X :=
  ((hE.not_measurableSet_CPM_MetOn hS hSnonmeas) hMet).elim

/-- A nonseparable metric space contains a closed discrete copy of the coded
carrier `ExtIndex S`, for any parameter set `S` of cardinality `ℵ₁`.

This is where the passage from an arbitrary `ℵ₁`-sized closed discrete
subspace to the coded carrier happens.  `exists_aleph1_closed_discrete_separated`
produces the separated set; the bijection with the coded carrier exists because
both have cardinality `ℵ₁`, and it is a homeomorphism because both carriers are
discrete, so composing with the inclusion of the separated set gives a closed
embedding.  No `CPM`-level relabelling is involved: the bijection is absorbed
into the embedding.

Both transfer theorems consume nonseparability only through this lemma — the
`Met` one below, and the `BMet` one of `Ext/CompleteMetrizability.lean`. -/
theorem exists_isClosedEmbedding_extIndex {X : Type*} [MetricSpace X]
    {S : Set ℝ} (hScard : #(↥S) = Cardinal.aleph 1)
    (hX : ¬ TopologicalSpace.SeparableSpace X) :
    ∃ ι : ExtIndex S → X,
      @Topology.IsClosedEmbedding (ExtIndex S) X ⊥ inferInstance ι := by
  obtain ⟨ε, -, Z, hZcard, hZclosed, hZdisc, -⟩ :=
    exists_aleph1_closed_discrete_separated hX
  -- The coded carrier and the separated set both have cardinality `ℵ₁`.
  have hlift : Cardinal.lift.{_, 0} #(ExtIndex S) = Cardinal.lift.{0, _} #(↥Z) := by
    rw [card_extIndex hScard, hZcard]
    simp [Cardinal.lift_aleph]
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.mp hlift
  refine ⟨Subtype.val ∘ (e : ExtIndex S → ↥Z), ?_⟩
  letI : TopologicalSpace (ExtIndex S) := ⊥
  haveI : DiscreteTopology (ExtIndex S) := ⟨rfl⟩
  haveI : DiscreteTopology (↥Z) := hZdisc
  let h : ExtIndex S ≃ₜ (↥Z) :=
    { toEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have hemb : Topology.IsEmbedding (Subtype.val ∘ (e : ExtIndex S → ↥Z)) :=
    Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  have hrange : Set.range (Subtype.val ∘ (e : ExtIndex S → ↥Z)) = Z := by
    rw [Set.range_comp, Set.range_eq_univ.mpr e.surjective, Set.image_univ,
      Subtype.range_coe]
  refine ⟨hemb, ?_⟩
  rw [hrange]
  exact hZclosed

/- `#print axioms IshikiExt.exists_isClosedEmbedding_extIndex`:
   `[propext, Classical.choice, Quot.sound]`. -/

/-- **The conclusion of Theorem 3.5 (`thm:borel-separability`), conditional on
`hEx`.**

`Met(X)` Borel in `CPM(X)` implies `X` separable, with the extensor input
supplied as `hEx`: *every* closed discrete copy of the coded `ℵ₁`-sized
carrier inside `X` admits an `IsIsometricExtensor` bundle.  Quantifying rather
than fixing the extensor is what the preprint's argument needs
(`notes/borel-preprint-audit.md` §2.8): the closed discrete subspace is
produced by the separated-set argument only *after* nonseparability is
assumed, so no single extensor can be named in advance.  This is also the only
variant in which `exists_aleph1_closed_discrete_separated` is consumed, and it
needs no `CPM`-level relabelling — the bijection between the coded carrier and
the separated set is absorbed into `ι`.

`hEx` is **not** E1 verbatim; it is what E1 yields for closed discrete
subspaces after the transport of
`IsIsometricExtensorOn.toIsIsometricExtensor`.  The E1-conditional form is
`separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn` at the end of
this file, which is this theorem with `hEx` derived from E1.

Unlike `separable_of_measurableSet_CPM_MetOn`, the hypotheses here are not
jointly inconsistent.  `hEx` holds vacuously whenever `X` admits no closed
embedding of the (uncountable, discrete) coded carrier, and `hMet` is
available in that range as well — a one-point `X` has a one-point `CPMOn X`,
in which every subset is measurable.  That witness is a remark, not a Lean
declaration. -/
theorem separable_of_measurableSet_CPM_MetOn_of_extensors
    {X : Type*} [MetricSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hScard : #(↥S) = Cardinal.aleph 1)
    (hSnonmeas : ¬ MeasurableSet S)
    (hMet : MeasurableSet (CPM.MetOn X))
    (hEx : ∀ ι : ExtIndex S → X,
      @Topology.IsClosedEmbedding (ExtIndex S) X ⊥ inferInstance ι →
      Nonempty (IsIsometricExtensor (⊥ : TopologicalSpace (ExtIndex S)) ι)) :
    TopologicalSpace.SeparableSpace X := by
  by_contra hX
  obtain ⟨ι, hce⟩ := exists_isClosedEmbedding_extIndex (S := S) hScard hX
  obtain ⟨hE⟩ := hEx _ hce
  exact (hE.not_measurableSet_CPM_MetOn hS hSnonmeas) hMet

/-! ## The same two theorems, conditional on E1

`IsIsometricExtensor` is a transported bundle; `IsIsometricExtensorOn` is E1's
own shape, quantified below over the closed subsets of `X` as E1 quantifies it.
E1 implies that hypothesis directly — nothing has to be moved onto a chosen
carrier first, because `IsIsometricExtensorOn.toIsIsometricExtensor` does the
moving inside the proof.  These are therefore the delivered forms of Theorem
3.5, conditional on E1 as audited in §3 and on nothing else. -/

/-- **Route M, core content of Theorem 3.5, conditional on E1.**  For a
metrizable `X` admitting a closed discrete copy of the coded `ℵ₁`-sized
carrier, E1 forbids Borelness of the metric locus of `X`.

`hE1` is E1's statement for `X`: every closed `A ⊆ X` admits an isometric
extensor of continuous pseudometrics.  It is a hypothesis, never an axiom —
E1's proof stays external.

The hypotheses are satisfiable, so the theorem is not vacuous: `hE1` holds for
every metrizable `X` by E1, and a discrete `X` of cardinality `ℵ₁` admits the
closed embedding `hι`.  That E1 holds is external and is not formalised. -/
theorem not_measurableSet_CPM_MetOn_of_isometricExtensorOn
    {X : Type*} [MetricSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hSnonmeas : ¬ MeasurableSet S)
    {ι : ExtIndex S → X}
    (hι : @Topology.IsClosedEmbedding (ExtIndex S) X ⊥ inferInstance ι)
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsIsometricExtensorOn A)) :
    ¬ MeasurableSet (CPM.MetOn X) := by
  letI : TopologicalSpace (ExtIndex S) := ⊥
  obtain ⟨hE⟩ := hE1 (Set.range ι) hι.isClosed_range
  exact (hE.toIsIsometricExtensor hι).not_measurableSet_CPM_MetOn hS hSnonmeas

/-- **Theorem 3.5 (`thm:borel-separability`), conditional on E1.**  `Met(X)`
Borel in `CPM(X)` implies `X` separable, with E1 supplied as `hE1`.

This is `separable_of_measurableSet_CPM_MetOn_of_extensors` with its extensor
hypothesis replaced by E1 itself; the quantification over closed embeddings
that theorem needs is recovered by applying `hE1` to `Set.range ι`, which is
closed because `ι` is a closed embedding.

The hypotheses are not jointly inconsistent.  A one-point `X` satisfies all of
them: its `CPMOn X` is a one-point space, in which every subset is measurable,
and E1 is available for its two closed subsets.  That witness is a remark, not
a Lean declaration. -/
theorem separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn
    {X : Type*} [MetricSpace X]
    {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hScard : #(↥S) = Cardinal.aleph 1)
    (hSnonmeas : ¬ MeasurableSet S)
    (hMet : MeasurableSet (CPM.MetOn X))
    (hE1 : ∀ A : Set X, IsClosed A → Nonempty (IsIsometricExtensorOn A)) :
    TopologicalSpace.SeparableSpace X := by
  letI : TopologicalSpace (ExtIndex S) := ⊥
  refine separable_of_measurableSet_CPM_MetOn_of_extensors hS hScard hSnonmeas
    hMet ?_
  intro ι hι
  obtain ⟨hE⟩ := hE1 (Set.range ι) hι.isClosed_range
  exact ⟨hE.toIsIsometricExtensor hι⟩

end
end IshikiExt
