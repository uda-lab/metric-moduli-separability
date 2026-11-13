-- Ext.UltraPublished
--
-- Issue #96, scope items 3–4: the published-interface layer for Theorem 3.14
-- and Corollaries 3.15 and 3.17 of arXiv:2608.19618.
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` §2.14–§2.15
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

-- The rescale API lemmas are placed under the `RangeSet.IsScale` namespace.
-- This block is placed *before* `nonempty_UMetOn_of_isUltrametrizableSpace` below,
-- since that theorem's proof depends on `RangeSet.rescale` and its API.
noncomputable def RangeSet.rescale {R : RangeSet} {r : ℕ → ℝ}
    (hr : R.IsScale r) (t : ℝ) : ℝ :=
  if ht : 0 < t then r (Nat.find (hr.exists_lt ht) - 1) else 0

theorem RangeSet.IsScale.rescale_mem {R : RangeSet} {r : ℕ → ℝ}
    (hr : R.IsScale r) (t : ℝ) :
    RangeSet.rescale hr t ∈ R.carrier := by
  unfold RangeSet.rescale
  split_ifs with ht
  · exact hr.mem _
  · exact R.zero_mem

theorem RangeSet.IsScale.rescale_eq_zero {R : RangeSet} {r : ℕ → ℝ}
    (hr : R.IsScale r) (t : ℝ) :
    RangeSet.rescale hr t = 0 ↔ t ≤ 0 := by
  unfold RangeSet.rescale
  split_ifs with ht
  · exact iff_of_false (hr.pos _).ne' (not_le.mpr ht)
  · exact iff_of_true rfl (not_lt.mp ht)

/-- Corrected statement: the naive `0 ≤ t → t ≤ rescale hr t` is false once `t`
exceeds the clamp value `r 0` (e.g. `r n = 1/(n+1)`, `t = 5` gives
`rescale hr t = r 0 = 1 < 5`). The universally true lower bound is
`min t (r 0) ≤ rescale hr t`, which is all the downstream topology-equivalence
argument actually needs. -/
theorem RangeSet.IsScale.le_rescale {R : RangeSet} {r : ℕ → ℝ}
    (hr : R.IsScale r) (t : ℝ) :
    min t (r 0) ≤ RangeSet.rescale hr t := by
  unfold RangeSet.rescale
  split_ifs with ht
  · set hp := hr.exists_lt ht with hp_def
    rcases Nat.eq_zero_or_pos (Nat.find hp) with hm0 | hmpos
    · have h0 : Nat.find hp - 1 = 0 := by omega
      rw [h0]
      exact min_le_right t (r 0)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      have hkm : k < Nat.find hp := by omega
      have hnotp : ¬ r k < t := Nat.find_min hp hkm
      have htk : t ≤ r k := not_lt.mp hnotp
      have hsub : Nat.find hp - 1 = k := by omega
      rw [hsub]
      exact (min_le_left t (r 0)).trans htk
  · exact (min_le_left t (r 0)).trans (not_lt.mp ht)

theorem RangeSet.IsScale.monotoneOn_rescale {R : RangeSet} {r : ℕ → ℝ}
    (hr : R.IsScale r) :
    MonotoneOn (RangeSet.rescale hr) (Set.Ici 0) := by
  intro t1 ht1 t2 ht2 hle
  simp only [Set.mem_Ici] at ht1 ht2
  unfold RangeSet.rescale
  by_cases hc1 : 0 < t1
  · have hc2 : 0 < t2 := hc1.trans_le hle
    rw [dite_eq_left hc1, dite_eq_left hc2]
    set hp1 := hr.exists_lt hc1 with hp1_def
    set hp2 := hr.exists_lt hc2 with hp2_def
    have hspec1 : r (Nat.find hp1) < t1 := Nat.find_spec hp1
    have hlt2 : r (Nat.find hp1) < t2 := hspec1.trans_le hle
    have hle21 : Nat.find hp2 ≤ Nat.find hp1 := Nat.find_min' hp2 hlt2
    have hsub_le : Nat.find hp2 - 1 ≤ Nat.find hp1 - 1 := by omega
    exact hr.antitone hsub_le
  · rw [dite_eq_right hc1]
    by_cases hc2 : 0 < t2
    · rw [dite_eq_left hc2]
      exact hr.nonneg _
    · simp [dite_eq_right hc2]

theorem RangeSet.IsScale.tendsto_rescale {R : RangeSet} {r : ℕ → ℝ}
    (hr : R.IsScale r) :
    Filter.Tendsto (RangeSet.rescale hr)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hr.exists_lt hε
  refine ⟨r n, hr.pos n, fun t ht hdist => ?_⟩
  simp only [Set.mem_Ioi] at ht
  rw [Real.dist_eq, sub_zero, abs_of_pos ht] at hdist
  have hnn0 : 0 ≤ RangeSet.rescale hr t := by
    unfold RangeSet.rescale
    rw [dite_eq_left ht]
    exact hr.nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn0]
  unfold RangeSet.rescale
  rw [dite_eq_left ht]
  set hp := hr.exists_lt ht with hp_def
  have hspecm : r (Nat.find hp) < t := Nat.find_spec hp
  have hnm : n < Nat.find hp := by
    by_contra hcon
    push Not at hcon
    have hran : r n ≤ r (Nat.find hp) := hr.antitone hcon
    linarith
  have hnle : n ≤ Nat.find hp - 1 := by omega
  have hcompare : r (Nat.find hp - 1) ≤ r n := hr.antitone hnle
  linarith

theorem nonempty_UMetOn_of_isUltrametrizableSpace
    {Y : Type*} [TopologicalSpace Y] (hY : IsUltrametrizableSpace Y)
    (hR : R.IsCharacteristic) :
    (UMetOn Y R).Nonempty := by
  letI : MetricSpace Y := hY.metricSpace
  haveI hultra : IsUltrametricDist Y := hY.choose_spec.1
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  let d0 : Y → Y → ℝ := fun x y => RangeSet.rescale hr (dist x y)
  have hrescale_nonneg : ∀ t : ℝ, 0 ≤ RangeSet.rescale hr t :=
    fun t => R.nonneg (hr.rescale_mem t)
  -- Step A: `d0` is an `R`-valued pseudo-ultrametric.
  have hupmet : IsUltraPMetOn R d0 := by
    have hrescale_max : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        RangeSet.rescale hr (max a b) = max (RangeSet.rescale hr a) (RangeSet.rescale hr b) := by
      intro a b ha hb
      rcases le_total a b with hab | hab
      · rw [max_eq_right hab,
          max_eq_right (hr.monotoneOn_rescale (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hab)]
      · rw [max_eq_left hab,
          max_eq_left (hr.monotoneOn_rescale (Set.mem_Ici.mpr hb) (Set.mem_Ici.mpr ha) hab)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      show RangeSet.rescale hr (dist x x) = 0
      rw [dist_self]
      exact (hr.rescale_eq_zero 0).mpr le_rfl
    · intro x y
      show RangeSet.rescale hr (dist x y) = RangeSet.rescale hr (dist y x)
      rw [dist_comm]
    · intro x y z
      show RangeSet.rescale hr (dist x z) ≤
        max (RangeSet.rescale hr (dist x y)) (RangeSet.rescale hr (dist y z))
      have hxy0 : (0 : ℝ) ≤ dist x y := dist_nonneg
      have hyz0 : (0 : ℝ) ≤ dist y z := dist_nonneg
      have hxz0 : (0 : ℝ) ≤ dist x z := dist_nonneg
      have hmax0 : (0 : ℝ) ≤ max (dist x y) (dist y z) := le_trans hxy0 (le_max_left _ _)
      rw [← hrescale_max (dist x y) (dist y z) hxy0 hyz0]
      exact hr.monotoneOn_rescale (Set.mem_Ici.mpr hxz0) (Set.mem_Ici.mpr hmax0)
        (dist_triangle_max x y z)
    · intro x y
      exact hr.rescale_mem (dist x y)
  -- Step B: `d0` is a genuine (separated) metric.
  have hmin : IsMetricOn d0 := by
    apply hupmet.toIsMetricOn
    intro x y hxy
    have hxy' : RangeSet.rescale hr (dist x y) = 0 := hxy
    have hxy0 : dist x y ≤ 0 := (hr.rescale_eq_zero (dist x y)).mp hxy'
    have hxy0' : (0 : ℝ) ≤ dist x y := dist_nonneg
    exact dist_eq_zero.mp (le_antisymm hxy0 hxy0')
  -- The original ambient metric, packaged as an `IsMetricOn` witness whose induced
  -- topology is, by construction of `hY.metricSpace`, the ambient topology.
  have horig : IsMetricOn (dist : Y → Y → ℝ) :=
    ⟨dist_self, fun {x y} hxy => dist_eq_zero.mp hxy, dist_comm, dist_triangle⟩
  have horig_toMetricSpace : horig.toMetricSpace = (inferInstance : MetricSpace Y) := by
    apply MetricSpace.ext
    ext x y
    rfl
  have horig_top : horig.topology = (inferInstance : TopologicalSpace Y) := by
    rw [horig.topology_eq_metricSpace_topology, horig_toMetricSpace]
    with_reducible_and_instances rfl
  -- Step C: `hmin.topology` is the ambient topology, via the two-directional
  -- continuity-of-identity argument (mirrors `Ext/FiveWay.lean`'s analogous step).
  have hforward : @Continuous Y Y horig.topology hmin.topology id := by
    rw [horig.topology_eq_metricSpace_topology, hmin.topology_eq_metricSpace_topology]
    refine (@Metric.continuous_iff Y Y
      horig.toMetricSpace.toPseudoMetricSpace
      hmin.toMetricSpace.toPseudoMetricSpace id).2 ?_
    intro b ε hε
    obtain ⟨δ, hδpos, hδspec⟩ := Metric.tendsto_nhdsWithin_nhds.mp hr.tendsto_rescale ε hε
    refine ⟨δ, hδpos, fun a hab => ?_⟩
    have hab' : dist a b < δ := hab
    show RangeSet.rescale hr (dist a b) < ε
    have hab0 : (0 : ℝ) ≤ dist a b := dist_nonneg
    rcases eq_or_lt_of_le hab0 with hc0 | hc0
    · rw [← hc0, (hr.rescale_eq_zero 0).mpr le_rfl]
      exact hε
    · have hmemIoi : dist a b ∈ Set.Ioi (0 : ℝ) := hc0
      have hxdist : dist (dist a b) (0 : ℝ) < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hc0]
        exact hab'
      have hspec := hδspec hmemIoi hxdist
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hrescale_nonneg (dist a b))] at hspec
  have hbackward : @Continuous Y Y hmin.topology horig.topology id := by
    rw [hmin.topology_eq_metricSpace_topology, horig.topology_eq_metricSpace_topology]
    refine (@Metric.continuous_iff Y Y
      hmin.toMetricSpace.toPseudoMetricSpace
      horig.toMetricSpace.toPseudoMetricSpace id).2 ?_
    intro b ε hε
    refine ⟨min ε (r 0), lt_min hε (hr.pos 0), fun a hab => ?_⟩
    have hab' : RangeSet.rescale hr (dist a b) < min ε (r 0) := hab
    show dist a b < ε
    have hle := hr.le_rescale (dist a b)
    have hlt_r0 : min (dist a b) (r 0) < r 0 :=
      lt_of_le_of_lt hle (lt_of_lt_of_le hab' (min_le_right ε (r 0)))
    have hdlt : dist a b < r 0 := by
      by_contra hge
      push Not at hge
      rw [min_eq_right hge] at hlt_r0
      exact lt_irrefl _ hlt_r0
    have hmin_eq : min (dist a b) (r 0) = dist a b := min_eq_left hdlt.le
    have hle' : dist a b ≤ RangeSet.rescale hr (dist a b) :=
      calc dist a b = min (dist a b) (r 0) := hmin_eq.symm
        _ ≤ RangeSet.rescale hr (dist a b) := hle
    exact lt_of_le_of_lt hle' (lt_of_lt_of_le hab' (min_le_left ε (r 0)))
  have hminTop : hmin.topology = (inferInstance : TopologicalSpace Y) :=
    (le_antisymm (continuous_id_iff_le.mp hbackward)
      (continuous_id_iff_le.mp hforward)).trans horig_top
  -- Step D: assemble `d0` into a member of `UCPMOn Y R`, hence of `UMetOn Y R`.
  have d0cont : Continuous (Function.uncurry d0) := by
    have hneq : hmin.toMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace Y) :=
      hmin.topology_eq_metricSpace_topology.symm.trans hminTop
    have hcd := @continuous_dist Y hmin.toMetricSpace.toPseudoMetricSpace
    rw [hneq] at hcd
    have hfe : (fun p : Y × Y => @dist Y hmin.toMetricSpace.toPseudoMetricSpace.toDist p.1 p.2)
        = Function.uncurry d0 := by
      funext p
      exact hmin.dist_toMetricSpace p.1 p.2
    rwa [hfe] at hcd
  let d : UCPMOn Y R := ⟨⟨d0, hupmet⟩, d0cont⟩
  exact ⟨d, hmin, hminTop⟩

end

end IshikiExt
