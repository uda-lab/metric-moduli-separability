-- Ext.UltraPublished
--
-- Issue #96, scope items 3–4: the published-interface layer for Theorem 3.14
-- and Corollaries 3.15 and 3.17 of arXiv:2608.19618.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.14–§2.15
-- (the printed statements: `Y` *ultrametrizable* is the standing hypothesis of
-- the whole 3.14/3.15/3.17 line) and §3 (E2 = Ishiki, *A factorization of
-- metric spaces*, Colloq. Math. 174 (2023), arXiv:2212.13409, Theorem 4.7,
-- quoted there exactly and verified against the full text).
--
-- The theorems of `Ext/UltraTransfer.lean` and `Ext/UltraCompleteTransfer.lean`
-- are *internal, bundle-conditional* forms: they take the transported extensor
-- family (`IsUltraIsometricExtensor` on the coded discrete carrier) as an
-- explicit hypothesis and carry no ultrametrizability hypothesis, because the
-- compact-witness repair never consumes one.  This file closes the distance to
-- the *printed* statements:
--
--   * `IsUltrametrizableSpace` renders the standing hypothesis "`Y` is
--     ultrametrizable" (an existential over metric-space structures, in the
--     shape of Mathlib's `MetrizableSpace`);
--   * `IsUltraIsometricExtensorOn` is E2 in its own closed-subset shape —
--     nonempty closed `F ⊆ Y`, extensor out of the subspace locus
--     `UMet(F;R)` — and `IsUltraCompIsometricExtensorOn` adds clause (N1),
--     gated on complete metrizability of `Y` exactly as the source gates it;
--   * the `toIsUltraIsometricExtensor`/`toIsUltraCompIsometricExtensor`
--     bridges derive the transported bundles from the E2-shaped input along a
--     closed embedding of a discrete carrier, as
--     `IsIsometricExtensorOn.toIsIsometricExtensor` does on the Archimedean
--     side (`Ext/GeneralSeparability.lean`);
--   * the four `…_of_isUltrametrizableSpace` wrappers are Theorem 3.14,
--     Corollary 3.15 and Corollary 3.17 (both printed variants) in the
--     preprint's hypothesis form: ultrametrizable `Y`, E2 as a closed-subset
--     hypothesis, and — for 3.17 — the printed nonemptiness of `UComp(Y;R)`.
--
-- The proof engine is unchanged: everything runs through the internal
-- theorems, i.e. through the `ultraExtend` compact-witness/completion repair.
-- No `UCPM`-level extensor is assumed anywhere (E2 has none — audit §3's
-- domain caveat), and E2 stays an explicit hypothesis, never an axiom.
--
-- Status: sorry-free; no custom axioms.

import Mathlib.Topology.MetricSpace.Ultra.Basic
import IshikiConj51.Ext.UltraCompleteTransfer

open Cardinal Set
open scoped ENNReal Topology

namespace IshikiExt

noncomputable section

-- The measurable-space constants of `Ext.UltraCoding` and `Ext.UltraGeneral`
-- are `local instance`s there, so they are re-registered here; they are the
-- same constants, so `MeasurableSet` below means what it means in the
-- internal transfer theorems.
attribute [local instance] ucpmMeasurableSpace ucpmBorelSpace
attribute [local instance] ucpmOnMeasurableSpace ucpmOnBorelSpace

variable {Y : Type*} {R : RangeSet}

/-! ## The standing hypothesis: `Y` is ultrametrizable -/

/-- **Ultrametrizability**, the preprint's standing hypothesis for the
3.14/3.15/3.17 line: some metric-space structure on `Y` satisfies the strong
triangle inequality (Mathlib's `IsUltrametricDist`) and induces the ambient
topology.  The shape is that of `TopologicalSpace.MetrizableSpace`'s defining
existential, so the `letI` idiom of the internal wrappers applies
(`IsUltrametrizableSpace.metricSpace` below).

This is deliberately *not* the surrogate `(UMetOn Y R).Nonempty`: that would
tie the hypothesis to the range set `R` and change the statement (the
rejection is recorded at
`separable_of_measurableSet_UMetOn_of_ultraExtensors`,
`Ext/UltraTransfer.lean`). -/
def IsUltrametrizableSpace (Y : Type*) [t : TopologicalSpace Y] : Prop :=
  ∃ m : MetricSpace Y, @IsUltrametricDist Y m.toPseudoMetricSpace.toDist ∧
    m.toUniformSpace.toTopologicalSpace = t

/-- A compatible metric-space structure chosen from ultrametrizability, with
the ambient topology installed definitionally
(`MetricSpace.replaceTopology`, the `metrizableSpaceMetric` idiom). -/
@[reducible] def IsUltrametrizableSpace.metricSpace [t : TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y) : MetricSpace Y :=
  hY.choose.replaceTopology hY.choose_spec.2.symm

/-- An ultrametrizable space is metrizable — the hypothesis under which the
internal completely-metrizable-locus variants are stated. -/
theorem IsUltrametrizableSpace.metrizableSpace [t : TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y) : TopologicalSpace.MetrizableSpace Y := by
  obtain ⟨m, -, hm⟩ := hY
  have h : @TopologicalSpace.MetrizableSpace Y m.toUniformSpace.toTopologicalSpace := by
    letI := m
    infer_instance
  exact hm ▸ h

/-! ## E2 in its own closed-subset shape (audit §3)

**E2** (Ishiki 2023, arXiv:2212.13409, Theorem 4.7; audit §3): *for an
ultrametrizable `X`, a nonempty closed `F ⊆ X`, a characteristic `S` and a
`v ∈ UMet(X/F;S)`, the map `Σ : Met(F) → Met(X)`, `Σ(d) = Φ*(d ×_∞ v)`,
satisfies (1) `Σ(d)|_{F²} = d`, (2) `𝒰𝒟^S_X(Σd,Σe) = 𝒰𝒟^S_F(d,e)`,
(3) monotone, (4) `Σ(d ∨ e) = Σ(d) ∨ Σ(e)`, (5)
`Σ(UMet(F;S)) ⊆ UMet(X;S)`; and (N1) if `X` is completely metrizable, the
auxiliary data can be chosen so that `Σ(Cm(F)) ⊆ Cm(X)` and
`Σ(UCM(F;S)) ⊆ UCM(X;S)`.*

The bundle below is that statement in the shape the preprint cites it (audit
§2.14: "the restriction to `UMet(Z;R)` of E2's `Σ : Met(Z) → Met(Y)`, using
clauses (1), (2), (5)"):

* the closed subset `F` is a set parameter with its nonemptiness and
  closedness as fields, as in the Archimedean `IsIsometricExtensorOn`;
* the domain is the subspace locus `UMet(F;R)` inside the continuous ambient
  `UCPM(F;R)` — the restriction of `Σ`'s domain that the preprint's proofs
  actually consume, and the locus on which the source's `𝒰𝒟^S` is defined.
  Assuming only the restriction assumes strictly *less* than E2 provides, so
  E2 instantiates the bundle;
* clauses (3), (4) and the auxiliary data `λ`, `v`, the quotient `X/F` and
  the embedding `Φ` are E2-internal and consumed by nothing in this track, so
  they are not modelled — the external boundary stays visible as exactly the
  three cited clauses;
* there is deliberately **no** `UCPM`-level field: E2 has no
  pseudo-ultrametric-level extensor (audit §3's domain caveat), which is what
  forces the compact-witness repair. -/

/-- **The published E2 interface** (audit §3, clauses (1), (2), (5)), for one
nonempty closed subset `F ⊆ Y`: an isometric extensor
`Σ : UMet(F;R) → UMet(Y;R)`.

`extension` is clause (1) restricted to `UMet(F;R)`, `isometry_toUCPMOn` is
clause (2) at the `𝒰𝒟^R` level both ambients carry, and `umet_preservation`
is clause (5); the codomain of `toUCPMOn` is the ambient `UCPM(Y;R)`, with
membership in `UMet(Y;R)` recorded separately rather than built into the
type.  E2 supplies this bundle for every nonempty closed subset of an
ultrametrizable `Y`; ultrametrizability is carried by the wrappers below,
next to the quantified hypothesis, as the preprint carries its standing
hypothesis. -/
structure IsUltraIsometricExtensorOn {Y : Type*} [TopologicalSpace Y]
    (F : Set Y) (R : RangeSet) where
  /-- E2 applies to nonempty closed subsets: nonemptiness. -/
  nonempty : F.Nonempty
  /-- E2 applies to nonempty closed subsets: closedness. -/
  closed : IsClosed F
  /-- E2's `Σ`, restricted to the compatible locus of the subspace `F`. -/
  toUCPMOn : ↥(UMetOn ↥F R) → UCPMOn Y R
  /-- Clause (1): the extension restricts to the given ultrametric on `F²`. -/
  extension : ∀ (d : ↥(UMetOn ↥F R)) (a b : ↥F),
    (toUCPMOn d).1.1 ↑a ↑b = d.1.1.1 a b
  /-- Clause (2): `Σ` is a `𝒰𝒟^R`-isometry. -/
  isometry_toUCPMOn : Isometry toUCPMOn
  /-- Clause (5): `Σ` carries compatible ultrametrics to compatible
  ultrametrics. -/
  umet_preservation : ∀ d, toUCPMOn d ∈ UMetOn Y R

/-- **E2 with clause (N1), in the closed-subset shape**: the extensor also
carries complete compatible ultrametrics to complete compatible ultrametrics.
As in the transported `IsUltraCompIsometricExtensor`
(`Ext/UltraCompleteTransfer.lean`), the clause is a field of a structure
*extending* the plain bundle — (N1) is a property of the same `Σ` — and the
complete-metrizability hypothesis on `Y` is an explicit parameter, because
(N1) is available only for a completely metrizable ambient and Corollary 3.17
*derives* that from its printed nonemptiness hypothesis before invoking
(N1). -/
structure IsUltraCompIsometricExtensorOn {Y : Type*} [TopologicalSpace Y]
    (F : Set Y) (hY : TopologicalSpace.IsCompletelyMetrizableSpace Y)
    (R : RangeSet) extends IsUltraIsometricExtensorOn F R where
  /-- Clause (N1): `Σ` carries the complete compatible locus of `F` into the
  complete compatible locus of `Y`. -/
  ucomp_preservation : ∀ d : ↥(UMetOn ↥F R),
    (d : UCPMOn ↥F R) ∈ UCompOn ↥F R → toUCPMOn d ∈ UCompOn Y R

/-! ## The E2 bridge

E2 applied to the closed subset `Set.range ι` yields the transported bundle
the internal transfer theorems consume, for any closed embedding `ι` of a
discrete carrier — the non-Archimedean twin of
`IsIsometricExtensorOn.toIsIsometricExtensor`.  The relabelling layer is
`UCPM.comap` along the homeomorphism `Z ≃ₜ ↥(Set.range ι)`; on the discrete
range the continuity constraint of `UCPMOn` is vacuous and compatibility with
the subspace topology is compatibility with `⊥`, so the subspace locus
`UMet(range ι; R)` is the relabelled bare locus `UMet(Z;R)` — the same
observation that lets the transported bundle take the bare locus as its
domain (`Ext/UltraGeneral.lean`). -/

/-- **The E2 bridge.**  The closed-subset bundle on `Set.range ι` transports
to the discrete-carrier bundle along a closed embedding `ι` out of a discrete
carrier. -/
noncomputable def IsUltraIsometricExtensorOn.toIsUltraIsometricExtensor
    {Z : Type*} [TopologicalSpace Y] {ι : Z → Y}
    (hι : @Topology.IsClosedEmbedding Z Y ⊥ inferInstance ι)
    (hE : IsUltraIsometricExtensorOn (Set.range ι) R) :
    IsUltraIsometricExtensor (⊥ : TopologicalSpace Z) R ι := by
  letI : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  let σ : Z ≃ₜ ↥(Set.range ι) := hι.toIsEmbedding.toHomeomorph
  haveI : DiscreteTopology ↥(Set.range ι) := σ.symm.isEmbedding.discreteTopology
  have hσ : ∀ x : Z, σ.symm.toEquiv ⟨ι x, x, rfl⟩ = x := fun x => by
    have hx : σ.toEquiv x = (⟨ι x, x, rfl⟩ : ↥(Set.range ι)) := Subtype.ext rfl
    rw [← hx]
    exact σ.toEquiv.symm_apply_apply x
  have hmem : ∀ d : ↥(UMet Z R),
      (⟨UCPM.comap (⇑σ.symm.toEquiv) d.1, continuous_of_discreteTopology⟩ :
        UCPMOn ↥(Set.range ι) R) ∈ UMetOn ↥(Set.range ι) R := by
    intro d
    obtain ⟨h, hbot⟩ := (UCPM.isCompatible_comap_iff σ.symm.toEquiv d.1).mpr d.2
    exact ⟨h, hbot.trans DiscreteTopology.eq_bot.symm⟩
  refine
    { closedEmbedding := hι
      domain_discrete := rfl
      toUCPMOn := fun d =>
        hE.toUCPMOn ⟨⟨UCPM.comap (⇑σ.symm.toEquiv) d.1,
          continuous_of_discreteTopology⟩, hmem d⟩
      extension := ?_
      isometry_toUCPMOn := ?_
      umet_preservation := ?_ }
  · intro d a b
    rw [hE.extension ⟨⟨UCPM.comap (⇑σ.symm.toEquiv) d.1,
      continuous_of_discreteTopology⟩, hmem d⟩ ⟨ι a, a, rfl⟩ ⟨ι b, b, rfl⟩]
    show d.1.1 (σ.symm.toEquiv ⟨ι a, a, rfl⟩) (σ.symm.toEquiv ⟨ι b, b, rfl⟩)
      = d.1.1 a b
    rw [hσ a, hσ b]
  · intro d e
    have hcomap : edist
        (⟨⟨UCPM.comap (⇑σ.symm.toEquiv) d.1, continuous_of_discreteTopology⟩,
          hmem d⟩ : ↥(UMetOn ↥(Set.range ι) R))
        (⟨⟨UCPM.comap (⇑σ.symm.toEquiv) e.1, continuous_of_discreteTopology⟩,
          hmem e⟩ : ↥(UMetOn ↥(Set.range ι) R)) = edist d e := by
      show UCPM.edist (UCPM.comap (⇑σ.symm.toEquiv) d.1)
          (UCPM.comap (⇑σ.symm.toEquiv) e.1) = UCPM.edist d.1 e.1
      exact UCPM.edist_comap σ.symm.toEquiv d.1 e.1
    rw [← hcomap]
    exact hE.isometry_toUCPMOn _ _
  · intro d
    exact hE.umet_preservation _

/-- **The E2(N1) bridge**: the closed-subset bundle with clause (N1)
transports to the discrete-carrier bundle with clause (N1).  Completeness of
the relabelled member is `isCompleteMetricOn_comap_iff`
(`Ext/Completeness.lean`): relabelling along a bijection preserves
completeness. -/
noncomputable def IsUltraCompIsometricExtensorOn.toIsUltraCompIsometricExtensor
    {Z : Type*} [TopologicalSpace Y]
    {hY : TopologicalSpace.IsCompletelyMetrizableSpace Y} {ι : Z → Y}
    (hι : @Topology.IsClosedEmbedding Z Y ⊥ inferInstance ι)
    (hE : IsUltraCompIsometricExtensorOn (Set.range ι) hY R) :
    IsUltraCompIsometricExtensor (⊥ : TopologicalSpace Z) hY R ι := by
  letI : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  let σ : Z ≃ₜ ↥(Set.range ι) := hι.toIsEmbedding.toHomeomorph
  haveI : DiscreteTopology ↥(Set.range ι) := σ.symm.isEmbedding.discreteTopology
  have hmem : ∀ d : ↥(UMet Z R),
      (⟨UCPM.comap (⇑σ.symm.toEquiv) d.1, continuous_of_discreteTopology⟩ :
        UCPMOn ↥(Set.range ι) R) ∈ UMetOn ↥(Set.range ι) R := by
    intro d
    obtain ⟨h, hbot⟩ := (UCPM.isCompatible_comap_iff σ.symm.toEquiv d.1).mpr d.2
    exact ⟨h, hbot.trans DiscreteTopology.eq_bot.symm⟩
  refine
    { toIsUltraIsometricExtensor :=
        hE.toIsUltraIsometricExtensorOn.toIsUltraIsometricExtensor hι
      ucomp_preservation := ?_ }
  intro d hd
  show hE.toIsUltraIsometricExtensorOn.toUCPMOn
      ⟨⟨UCPM.comap (⇑σ.symm.toEquiv) d.1, continuous_of_discreteTopology⟩,
        hmem d⟩ ∈ UCompOn Y R
  refine hE.ucomp_preservation _ ⟨hmem d, ?_⟩
  exact (isCompleteMetricOn_comap_iff σ.symm.toEquiv d.1.1).mpr hd.2

/-! ## Satisfiability of the closed-subset bundle

As with `nonempty_isUltraIsometricExtensor_id` (`Ext/UltraGeneral.lean`), the
witness below is *not* E2 — E2's content is the existence of extensors into
strictly larger ultrametrizable spaces, which stays external — but it makes
the no-smuggle check on the published bundle a proved fact: the hypothesis of
the wrappers is not a disguised `False`. -/

/-- On a nonempty discrete carrier, `F = univ` with the relabelled identity is
an extensor, so `IsUltraIsometricExtensorOn` is satisfiable. -/
theorem nonempty_isUltraIsometricExtensorOn_univ (Y : Type*) [TopologicalSpace Y]
    [DiscreteTopology Y] [Nonempty Y] (R : RangeSet) :
    Nonempty (IsUltraIsometricExtensorOn (Set.univ : Set Y) R) := by
  let e : Y ≃ ↥(Set.univ : Set Y) := (Equiv.Set.univ Y).symm
  have hmem : ∀ d : ↥(UMetOn ↥(Set.univ : Set Y) R),
      (⟨UCPM.comap (⇑e) d.1.1, continuous_of_discreteTopology⟩ :
        UCPMOn Y R) ∈ UMetOn Y R := by
    intro d
    have hd : UCPM.IsCompatible d.1.1 := by
      obtain ⟨h, htop⟩ := d.2
      exact ⟨h, htop.trans DiscreteTopology.eq_bot⟩
    obtain ⟨h, hbot⟩ := (UCPM.isCompatible_comap_iff e d.1.1).mpr hd
    exact ⟨h, hbot.trans DiscreteTopology.eq_bot.symm⟩
  refine ⟨{ nonempty := Set.univ_nonempty
            closed := isClosed_univ
            toUCPMOn := fun d =>
              ⟨UCPM.comap (⇑e) d.1.1, continuous_of_discreteTopology⟩
            extension := ?_
            isometry_toUCPMOn := ?_
            umet_preservation := hmem }⟩
  · intro d a b
    show d.1.1.1 (e ↑a) (e ↑b) = d.1.1.1 a b
    have ha : e ↑a = a := Subtype.ext rfl
    have hb : e ↑b = b := Subtype.ext rfl
    rw [ha, hb]
  · intro d d'
    show UCPM.edist (UCPM.comap (⇑e) d.1.1) (UCPM.comap (⇑e) d'.1.1)
      = UCPM.edist d.1.1 d'.1.1
    exact UCPM.edist_comap e d.1.1 d'.1.1

/-! ## The published-interface wrappers

Each wrapper is the printed statement of audit §2.14/§2.15: the standing
hypothesis `IsUltrametrizableSpace Y`, the printed hypothesis on the locus,
and E2 as the closed-subset hypothesis `hE2`, quantified over the nonempty
closed subsets of `Y` exactly as E2 quantifies its `F`.  Quantifying rather
than fixing the subset is what the argument needs: the closed discrete
subspace is produced by the separated-set argument only after nonseparability
is assumed.  E2's own proof stays external; it is never an axiom.

The internal bundle-conditional theorems remain available as reusable
results; the wrappers derive their extensor-family hypotheses from `hE2` via
the bridge, so the published hypotheses are formally shown to produce the
internal bundles. -/

/-- **Theorem 3.14 (`thm:ultrametric-borel-separability`), published
interface.**  Let `Y` be ultrametrizable and let E2 hold for `Y` (as the
closed-subset hypothesis `hE2`).  If `UMet(Y;R)` is Borel in `UCPM(Y;R)`,
then `Y` is separable.

The internal form is `separable_of_measurableSet_UMetOn_of_ultraExtensors`
(`Ext/UltraTransfer.lean`); this wrapper chooses a compatible metric from
ultrametrizability and transports `hE2` along each closed embedding via
`IsUltraIsometricExtensorOn.toIsUltraIsometricExtensor`. -/
theorem separable_of_measurableSet_UMetOn_of_isUltrametrizableSpace
    {Y : Type*} [TopologicalSpace Y] (hY : IsUltrametrizableSpace Y)
    (hR : R.IsCharacteristic)
    (hMet : MeasurableSet (UMetOn Y R))
    (hE2 : ∀ F : Set Y, F.Nonempty → IsClosed F →
      Nonempty (IsUltraIsometricExtensorOn F R)) :
    TopologicalSpace.SeparableSpace Y := by
  letI : MetricSpace Y := hY.metricSpace
  refine separable_of_measurableSet_UMetOn_of_ultraExtensors hR hMet ?_
  intro Z ι hZne hce
  haveI : Nonempty Z := hZne
  letI : TopologicalSpace Z := ⊥
  obtain ⟨hE⟩ := hE2 (Set.range ι) (Set.range_nonempty ι) hce.isClosed_range
  exact ⟨hE.toIsUltraIsometricExtensor hce⟩

/-- **Corollary 3.15 (`cor:ultrametric-space-complete-separability`),
published interface.**  Let `Y` be ultrametrizable and let E2 hold for `Y`.
If `UMet(Y;R)` is completely metrizable, then `Y` is separable.

Metrizability of `Y`, which the internal
`separable_of_isCompletelyMetrizableSpace_UMetOn_of_ultraExtensors` assumes,
is here derived from the printed ultrametrizability hypothesis. -/
theorem separable_of_isCompletelyMetrizableSpace_UMetOn_of_isUltrametrizableSpace
    {Y : Type*} [TopologicalSpace Y] (hY : IsUltrametrizableSpace Y)
    (hR : R.IsCharacteristic)
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(UMetOn Y R))
    (hE2 : ∀ F : Set Y, F.Nonempty → IsClosed F →
      Nonempty (IsUltraIsometricExtensorOn F R)) :
    TopologicalSpace.SeparableSpace Y := by
  haveI : TopologicalSpace.MetrizableSpace Y := hY.metrizableSpace
  refine separable_of_isCompletelyMetrizableSpace_UMetOn_of_ultraExtensors hR hMet ?_
  intro Z ι hZne hce
  haveI : Nonempty Z := hZne
  letI : TopologicalSpace Z := ⊥
  obtain ⟨hE⟩ := hE2 (Set.range ι) (Set.range_nonempty ι) hce.isClosed_range
  exact ⟨hE.toIsUltraIsometricExtensor hce⟩

/-- **Corollary 3.17 (`cor:complete-ultrametric-borel-separability`), Borel
variant, published interface.**  Let `Y` be ultrametrizable with
`UComp(Y;R) ≠ ∅`, and let E2 with clause (N1) hold for `Y`.  If `UComp(Y;R)`
is Borel in `UCPM(Y;R)`, then `Y` is separable.

The printed nonemptiness hypothesis is what makes `Y` completely metrizable
(`isCompletelyMetrizableSpace_of_mem_UCompOn`), and complete metrizability is
the hypothesis under which E2's clause (N1) holds; that is why `hE2` is
quantified over a proof of complete metrizability, as in the internal
`separable_of_measurableSet_UCompOn_of_ultraCompExtensors`. -/
theorem separable_of_measurableSet_UCompOn_of_isUltrametrizableSpace
    {Y : Type*} [TopologicalSpace Y] (hY : IsUltrametrizableSpace Y)
    (hR : R.IsCharacteristic)
    (hne : (UCompOn Y R).Nonempty)
    (hComp : MeasurableSet (UCompOn Y R))
    (hE2 : ∀ (hYc : TopologicalSpace.IsCompletelyMetrizableSpace Y) (F : Set Y),
      F.Nonempty → IsClosed F →
      Nonempty (IsUltraCompIsometricExtensorOn F hYc R)) :
    TopologicalSpace.SeparableSpace Y := by
  letI : MetricSpace Y := hY.metricSpace
  refine separable_of_measurableSet_UCompOn_of_ultraCompExtensors hR hne hComp ?_
  intro hYc Z ι hZne hce
  haveI : Nonempty Z := hZne
  letI : TopologicalSpace Z := ⊥
  obtain ⟨hE⟩ := hE2 hYc (Set.range ι) (Set.range_nonempty ι) hce.isClosed_range
  exact ⟨hE.toIsUltraCompIsometricExtensor hce⟩

/-- **Corollary 3.17, completely metrizable variant, published interface.**
Let `Y` be ultrametrizable with `UComp(Y;R) ≠ ∅`, and let E2 with clause (N1)
hold for `Y`.  If `UComp(Y;R)` is completely metrizable, then `Y` is
separable. -/
theorem separable_of_isCompletelyMetrizableSpace_UCompOn_of_isUltrametrizableSpace
    {Y : Type*} [TopologicalSpace Y] (hY : IsUltrametrizableSpace Y)
    (hR : R.IsCharacteristic)
    (hne : (UCompOn Y R).Nonempty)
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(UCompOn Y R))
    (hE2 : ∀ (hYc : TopologicalSpace.IsCompletelyMetrizableSpace Y) (F : Set Y),
      F.Nonempty → IsClosed F →
      Nonempty (IsUltraCompIsometricExtensorOn F hYc R)) :
    TopologicalSpace.SeparableSpace Y := by
  haveI : TopologicalSpace.MetrizableSpace Y := hY.metrizableSpace
  refine separable_of_isCompletelyMetrizableSpace_UCompOn_of_ultraCompExtensors
    hR hne hMet ?_
  intro hYc Z ι hZne hce
  haveI : Nonempty Z := hZne
  letI : TopologicalSpace Z := ⊥
  obtain ⟨hE⟩ := hE2 hYc (Set.range ι) (Set.range_nonempty ι) hce.isClosed_range
  exact ⟨hE.toIsUltraCompIsometricExtensor hce⟩

end

end IshikiExt
