-- Ext.UltraGeneral
--
-- Issue #82, scope items 1 and 2: the general-space ambient of the
-- non-Archimedean track of arXiv:2608.19618, its completeness, and the E2
-- interface used by Theorem 3.14.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §1 (ambient
-- conventions), §2.14 (the completeness sub-lemma, whose three steps are
-- transcribed below) and §3 (E2, together with its domain caveat).
-- `report/report-ja.md` is *not* the source of truth here: it stays frozen as
-- the Conjecture 5.1 archival report by the Issue #46 decision.
--
-- `Ext/UltraPMet.lean` builds `UCPM Z R` for a *bare* carrier, which is the
-- preprint's `UCPM(Z;R)` when `Z` is discrete — the only case Theorems
-- 3.10–3.13 need.  Theorem 3.14 works over a general topological space `Y`,
-- where the preprint's ambient is the space of **continuous** `R`-valued
-- pseudo-ultrametrics; `UCPMOn Y R` below is that space, and `UMetOn Y R` is
-- its compatible locus.  The distinction matters for the same reason it does
-- in `Ext/GeneralSeparability.lean` for `CPMOn`: Borelness in the larger
-- all-pseudo-ultrametrics ambient is a strictly stronger hypothesis, so it may
-- not be substituted for the preprint's.
--
-- Layering:
--   `UCPMOn`, `UMetOn`               — the general-space ambient and locus;
--   `completeSpace_UCPM`             — audit §2.14's sub-lemma, steps (i)–(iii);
--   `completeSpace_UCPMOn`           — the form Theorem 3.14 consumes;
--   `UCPM.edist_comap_le`,
--   `UCPM.isCompatible_comap_of_mem_UMetOn`
--                                    — the restriction map along a discrete
--                                      closed subspace, and what it does to the
--                                      compatible locus;
--   `IsUltraIsometricExtensor`       — E2 as an explicit hypothesis bundle.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.UltraPMet

open Set Filter
open scoped ENNReal Topology

namespace IshikiExt

noncomputable section

variable {Z W Y : Type*} {R : RangeSet}

/-! ## The continuous ambient of a topological space

`UCPMOn Y R` is the preprint's `UCPM(Y;R)`: the `R`-valued pseudo-ultrametrics
on `Y` that are continuous as functions `Y × Y → ℝ`.  Mathlib's subtype
`EMetricSpace` instance restricts the distance, so the ambient distance is
literally `𝒰𝒟^R`. -/

/-- The preprint's `UCPM(Y;R)` over a general topological space: the continuous
`R`-valued pseudo-ultrametrics, with the non-Archimedean uniform distance. -/
def UCPMOn (Y : Type*) [TopologicalSpace Y] (R : RangeSet) : Type _ :=
  {d : UCPM Y R // Continuous (Function.uncurry d.1)}

namespace UCPMOn

variable [TopologicalSpace Y]

instance : EMetricSpace (UCPMOn Y R) :=
  inferInstanceAs (EMetricSpace {d : UCPM Y R // Continuous (Function.uncurry d.1)})

/-- The distance of `UCPM(Y;R)` is the restriction of `𝒰𝒟^R`. -/
@[simp] theorem edist_eq (d e : UCPMOn Y R) : edist d e = UCPM.edist d.1 e.1 := rfl

end UCPMOn

local instance ucpmOnMeasurableSpace (Y : Type*) [TopologicalSpace Y] (R : RangeSet) :
    MeasurableSpace (UCPMOn Y R) := borel (UCPMOn Y R)

local instance ucpmOnBorelSpace (Y : Type*) [TopologicalSpace Y] (R : RangeSet) :
    BorelSpace (UCPMOn Y R) := ⟨rfl⟩

/-- The preprint's `UMet(Y;R)`: the members of `UCPM(Y;R)` that are metrics
inducing the topology of `Y`.  Compatibility is the repository-wide
`IsMetricOn` + `.topology` condition of `Conj51/MetD.lean`, with the ambient
topology of `Y` in place of the discrete one — exactly as `CPM.MetOn` states it
on the Archimedean side. -/
def UMetOn (Y : Type*) [TopologicalSpace Y] (R : RangeSet) : Set (UCPMOn Y R) :=
  {d | ∃ h : IsMetricOn d.1.1, h.topology = (inferInstance : TopologicalSpace Y)}

@[simp] theorem mem_UMetOn [TopologicalSpace Y] {d : UCPMOn Y R} :
    d ∈ UMetOn Y R ↔ ∃ h : IsMetricOn d.1.1,
      h.topology = (inferInstance : TopologicalSpace Y) := Iff.rfl

/-! ## Completeness of `UCPM(Y;R)` (audit §2.14, sub-lemma)

The preprint uses completeness of the ambient without proof; the audit supplies
it in three steps, and those three steps are the three blocks below.  It is the
hypothesis that makes the repair of Theorem 3.14 possible at all, so it is
proved for an arbitrary carrier and an arbitrary characteristic `R`, and both
the bare and the continuous ambient are recorded. -/

/-- **Step (i).**  A bound on `𝒰𝒟^R` is a *uniform* bound on the difference:
from `d ≤ e ∨ ε` either `d ≤ e` or `d ≤ ε`, and in both cases `d − e ≤ ε`
because `e ≥ 0`.  So a `𝒰𝒟^R`-Cauchy sequence is uniformly Cauchy. -/
theorem UCPM.abs_sub_le_of_edist_le {d e : UCPM Z R} {c : ℝ} (hc : 0 ≤ c)
    (h : UCPM.edist d e ≤ ENNReal.ofReal c) (x y : Z) : |d.1 x y - e.1 x y| ≤ c := by
  have hde := UCPM.le_max_of_edist_le hc h x y
  have hed := UCPM.le_max_of_edist_le hc (by rwa [UCPM.edist_comm] at h) x y
  rw [abs_sub_le_iff]
  constructor
  · rcases max_cases (e.1 x y) c with ⟨hmax, -⟩ | ⟨hmax, -⟩
    · rw [hmax] at hde; linarith
    · rw [hmax] at hde; have := e.nonneg x y; linarith
  · rcases max_cases (d.1 x y) c with ⟨hmax, -⟩ | ⟨hmax, -⟩
    · rw [hmax] at hed; linarith
    · rw [hmax] at hed; have := d.nonneg x y; linarith

/-- The `𝒰𝒟^R`-Cauchy condition in the pointwise max-form the audit's steps
(ii) and (iii) both consume. -/
theorem UCPM.exists_forall_le_max_of_cauchySeq {u : ℕ → UCPM Z R} (hu : CauchySeq u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ∀ x y, (u j).1 x y ≤ max ((u k).1 x y) ε := by
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu (ENNReal.ofReal ε) (by simpa using hε)
  refine ⟨N, fun j hj k hk x y => ?_⟩
  exact UCPM.le_max_of_edist_le hε.le (hN j hj k hk).le x y

/-- **Completeness of `UCPM(Z;R)` for a characteristic `R`** (audit §2.14,
sub-lemma).  Step (i) makes a `𝒰𝒟^R`-Cauchy sequence uniformly Cauchy, so it
has a pointwise limit satisfying the strong triangle inequality; step (ii)
shows the limit is `R`-valued because at a pair where the limit is positive the
values are *eventually constant*; step (iii) converts uniform convergence back
into `𝒰𝒟^R`-convergence.

Both step (ii) and step (iii) consume `R.IsCharacteristic`, and neither is
available without it: (ii) needs a member of `R ∖ {0}` below the limit value,
(iii) needs members of `R ∖ {0}` below an arbitrary positive bound. -/
theorem completeSpace_UCPM (hR : R.IsCharacteristic) : CompleteSpace (UCPM Z R) := by
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- Step (i): the sequence is uniformly Cauchy, hence pointwise convergent.
  have hpt : ∀ x y : Z, ∃ v : ℝ, Tendsto (fun k => (u k).1 x y) atTop (𝓝 v) := by
    intro x y
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := UCPM.exists_forall_le_max_of_cauchySeq hu (half_pos hε)
    refine ⟨N, fun j hj k hk => ?_⟩
    have hle : ∀ x y, (u j).1 x y ≤ max ((u k).1 x y) (ε / 2) := hN j hj k hk
    have hle' : ∀ x y, (u k).1 x y ≤ max ((u j).1 x y) (ε / 2) := hN k hk j hj
    have h1 : (u j).1 x y - (u k).1 x y ≤ ε / 2 := by
      rcases max_cases ((u k).1 x y) (ε / 2) with ⟨hmax, -⟩ | ⟨hmax, -⟩
      · have := hle x y; rw [hmax] at this; linarith
      · have := hle x y; rw [hmax] at this; have := (u k).nonneg x y; linarith
    have h2 : (u k).1 x y - (u j).1 x y ≤ ε / 2 := by
      rcases max_cases ((u j).1 x y) (ε / 2) with ⟨hmax, -⟩ | ⟨hmax, -⟩
      · have := hle' x y; rw [hmax] at this; linarith
      · have := hle' x y; rw [hmax] at this; have := (u j).nonneg x y; linarith
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  choose L hL using hpt
  -- The pointwise limit obeys the ultrametric axioms.
  have hself : ∀ x, L x x = 0 := by
    intro x
    have h0 : (fun k => (u k).1 x x) = fun _ : ℕ => (0 : ℝ) :=
      funext fun k => (u k).2.dist_self x
    have hx := hL x x
    rw [h0] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds
  have hcomm : ∀ x y, L x y = L y x := by
    intro x y
    have h0 : (fun k => (u k).1 y x) = fun k => (u k).1 x y :=
      funext fun k => ((u k).2.dist_comm x y).symm
    have hyx := hL y x
    rw [h0] at hyx
    exact tendsto_nhds_unique (hL x y) hyx
  have htri : ∀ x y z, L x z ≤ max (L x y) (L y z) := by
    intro x y z
    exact le_of_tendsto_of_tendsto' (hL x z) ((hL x y).max (hL y z))
      fun k => (u k).2.dist_triangle_max x y z
  have hnonneg : ∀ x y, 0 ≤ L x y :=
    fun x y => ge_of_tendsto' (hL x y) fun k => (u k).nonneg x y
  -- Step (ii): the limit is `R`-valued, by eventual constancy of the values.
  have hmem : ∀ x y, L x y ∈ R.carrier := by
    intro x y
    rcases eq_or_lt_of_le (hnonneg x y) with hzero | hpos
    · rw [← hzero]; exact R.zero_mem
    obtain ⟨ε, hεR, hε0, hεv⟩ := hR (L x y) hpos
    have hgt : ∀ᶠ k in atTop, ε < (u k).1 x y :=
      (hL x y).eventually (eventually_gt_nhds hεv)
    obtain ⟨N₁, hN₁⟩ := hgt.exists_forall_of_atTop
    obtain ⟨N₂, hN₂⟩ := UCPM.exists_forall_le_max_of_cauchySeq hu hε0
    set N := max N₁ N₂ with hNdef
    have hconst : ∀ k ≥ N, (u k).1 x y = (u N).1 x y := by
      intro k hk
      have hkN₂ : N₂ ≤ k := le_trans (le_max_right N₁ N₂) hk
      have hNN₂ : N₂ ≤ N := le_max_right N₁ N₂
      have hkN₁ : N₁ ≤ k := le_trans (le_max_left N₁ N₂) hk
      have hNN₁ : N₁ ≤ N := le_max_left N₁ N₂
      have h1 := hN₂ k hkN₂ N hNN₂ x y
      have h2 := hN₂ N hNN₂ k hkN₂ x y
      rw [max_eq_left (le_of_lt (hN₁ N hNN₁))] at h1
      rw [max_eq_left (le_of_lt (hN₁ k hkN₁))] at h2
      exact le_antisymm h1 h2
    have : L x y = (u N).1 x y :=
      tendsto_nhds_unique (hL x y) (tendsto_atTop_of_eventually_const hconst)
    rw [this]
    exact (u N).2.mem_range x y
  refine ⟨⟨L, ⟨hself, hcomm, htri, hmem⟩⟩, ?_⟩
  -- Step (iii): uniform convergence is `𝒰𝒟^R`-convergence.
  rw [EMetric.tendsto_atTop]
  intro δ hδ
  obtain ⟨c, hc0, hcδ⟩ : ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c < δ := by
    obtain ⟨q, hq0, hqδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
    exact ⟨(q : ℝ), by exact_mod_cast ENNReal.coe_pos.mp hq0, by rwa [ENNReal.ofReal_coe_nnreal]⟩
  obtain ⟨ε, hεR, hε0, hεc⟩ := hR c hc0
  obtain ⟨N, hN⟩ := UCPM.exists_forall_le_max_of_cauchySeq hu hε0
  refine ⟨N, fun j hj => lt_of_le_of_lt ?_ (lt_trans ((ENNReal.ofReal_lt_ofReal_iff hc0).mpr hεc) hcδ)⟩
  refine UCPM.edist_le_ofReal ⟨hεR, fun x y => ⟨?_, ?_⟩⟩
  · refine ge_of_tendsto ((hL x y).max tendsto_const_nhds) ?_
    filter_upwards [eventually_ge_atTop N] with k hk using hN j hj k hk x y
  · refine le_of_tendsto (hL x y) ?_
    filter_upwards [eventually_ge_atTop N] with k hk using hN k hk j hj x y

/-- The continuous members form a closed subset of the ambient: a `𝒰𝒟^R`-limit
is a uniform limit by step (i), and a uniform limit of continuous functions is
continuous. -/
theorem isClosed_continuous_UCPM [TopologicalSpace Y] :
    IsClosed {d : UCPM Y R | Continuous (Function.uncurry d.1)} := by
  rw [← closure_subset_iff_isClosed]
  intro d hd
  show Continuous (Function.uncurry d.1)
  refine continuous_of_uniform_approx_of_continuous fun s hs => ?_
  obtain ⟨ε, hε0, hεs⟩ := Metric.mem_uniformity_dist.mp hs
  obtain ⟨e, he, hde⟩ := EMetric.mem_closure_iff.mp hd (ENNReal.ofReal (ε / 2))
    (by simpa using half_pos hε0)
  refine ⟨Function.uncurry e.1, he, fun p => hεs ?_⟩
  have := UCPM.abs_sub_le_of_edist_le (half_pos hε0).le hde.le p.1 p.2
  rw [Real.dist_eq]
  exact lt_of_le_of_lt this (by linarith)

/-- **Completeness of the preprint's `UCPM(Y;R)`.**  This is the form Theorem
3.14 uses: the extension of the coding isometry to the compact closure takes its
values here. -/
theorem completeSpace_UCPMOn [TopologicalSpace Y] (hR : R.IsCharacteristic) :
    CompleteSpace (UCPMOn Y R) := by
  haveI : CompleteSpace (UCPM Y R) := completeSpace_UCPM hR
  haveI : IsClosed {d : UCPM Y R | Continuous (Function.uncurry d.1)} :=
    isClosed_continuous_UCPM
  exact inferInstanceAs (CompleteSpace ↥{d : UCPM Y R | Continuous (Function.uncurry d.1)})

/-! ## Restriction along a discrete closed subspace

E2 supplies an extensor, not a retraction; what goes the other way is the
restriction map `g ↦ g|_{Z²}`, which is `UCPM.comap` along the embedding.  Two
facts about it are needed: it does not increase `𝒰𝒟^R` (so it is continuous),
and it carries the compatible locus of `Y` into the compatible locus of a
discrete closed subspace.  Together with E2's clause (1) they are what pins the
extension down on the closure. -/

/-- Every tolerance for a pair is a tolerance for the restricted pair. -/
theorem UCPM.tolerances_subset_comap (f : Z → W) (d e : UCPM W R) :
    UCPM.tolerances d e ⊆ UCPM.tolerances (UCPM.comap f d) (UCPM.comap f e) :=
  fun _ hr => ⟨hr.1, fun x y => hr.2 (f x) (f y)⟩

/-- Restriction along an arbitrary map does not increase `𝒰𝒟^R`. -/
theorem UCPM.edist_comap_le (f : Z → W) (d e : UCPM W R) :
    UCPM.edist (UCPM.comap f d) (UCPM.comap f e) ≤ UCPM.edist d e :=
  le_iInf₂ fun _ hr => UCPM.edist_le_ofReal (UCPM.tolerances_subset_comap f d e hr)

/-- The restriction map `UCPM(Y;R) → UCPM(Z;R)` along `ι : Z → Y`. -/
def UCPMOn.restrict [TopologicalSpace Y] (ι : Z → Y) (g : UCPMOn Y R) : UCPM Z R :=
  UCPM.comap ι g.1

@[simp] theorem UCPMOn.restrict_val [TopologicalSpace Y] (ι : Z → Y) (g : UCPMOn Y R) :
    (UCPMOn.restrict ι g).1 = fun a b => g.1.1 (ι a) (ι b) := rfl

theorem UCPMOn.lipschitzWith_restrict [TopologicalSpace Y] (ι : Z → Y) :
    LipschitzWith 1 (UCPMOn.restrict ι : UCPMOn Y R → UCPM Z R) := by
  intro g g'
  rw [ENNReal.coe_one, one_mul]
  exact UCPM.edist_comap_le ι g.1 g'.1

theorem UCPMOn.continuous_restrict [TopologicalSpace Y] (ι : Z → Y) :
    Continuous (UCPMOn.restrict ι : UCPMOn Y R → UCPM Z R) :=
  (UCPMOn.lipschitzWith_restrict ι).continuous

/-- **Restriction to a discrete subspace preserves compatibility.**  If `g` is a
metric inducing the topology of `Y` and `ι` embeds a discrete carrier `Z` into
`Y`, then `g|_{Z²}` is a metric inducing the discrete topology, i.e. a member of
`UMet(Z;R)`.

This is the non-Archimedean twin of the restriction step used inside
`IsIsometricExtensor.image_met_eq_range_inter` (`Ext/GeneralSeparability.lean`);
the argument is the same and is stated here for the `UCPM` ambient, where the
Archimedean one does not apply. -/
theorem UCPM.isCompatible_comap_of_mem_UMetOn (tZ : TopologicalSpace Z)
    [TopologicalSpace Y] {ι : Z → Y} (hι : @Topology.IsEmbedding Z Y tZ inferInstance ι)
    (htZ : tZ = ⊥) {g : UCPMOn Y R} (hg : g ∈ UMetOn Y R) :
    UCPMOn.restrict ι g ∈ UMet Z R := by
  obtain ⟨hmetric, htop⟩ := hg
  have hmetric' : IsMetricOn fun a b => g.1.1 (ι a) (ι b) := by
    refine ⟨fun a => hmetric.dist_self _, fun {a b} hab => hι.injective ?_,
      fun a b => hmetric.dist_comm _ _, fun a b c => hmetric.dist_triangle _ _ _⟩
    exact hmetric.eq_of_dist_eq_zero hab
  have htop_induced : hmetric'.topology = tZ := by
    letI mZ : MetricSpace Z := MetricSpace.induced ι hι.injective hmetric.toMetricSpace
    have hmZ : hmetric'.toMetricSpace = mZ := by
      apply MetricSpace.ext
      ext a b
      rfl
    rw [hmetric'.topology_eq_metricSpace_topology, hmZ]
    change TopologicalSpace.induced ι hmetric.topology = tZ
    rw [htop]
    exact hι.eq_induced.symm
  exact ⟨hmetric', htop_induced.trans htZ⟩

/-! ## E2 as an explicit hypothesis bundle (audit §3)

**E2** — Ishiki, *A factorization of metric spaces*, Colloq. Math. 174 (2023),
101–120 (arXiv:2212.13409), Theorem 4.7 — supplies, for an ultrametrizable `Y`,
a nonempty closed `F ⊆ Y` and a characteristic `R`, a map `Σ : Met(F) → Met(Y)`
with (1) `Σ(d)|_{F²} = d`, (2) `𝒰𝒟^R_Y(Σ d, Σ e) = 𝒰𝒟^R_F(d,e)`, and (5)
`Σ(UMet(F;R)) ⊆ UMet(Y;R)`.  Those three clauses, restricted to `UMet(F;R)`,
are the three data fields below; nothing else about E2 is assumed anywhere in
this track, and E2 is never an axiom.

**The domain caveat is the whole point.**  `Σ` is defined on `Met(F)`; E2 has
no pseudo-ultrametric-level extensor, so this bundle deliberately has *no*
`UCPM`-level field.  The Archimedean bundle `IsIsometricExtensor` does have one
(`toCPM : CPM A → CPMOn X`) because E1 supplies `Ẽ : CPM(A) → CPM(X)`; assuming
the same here would be assuming a map E2 does not provide, and it is exactly
that missing map which forces the compact-witness repair of audit §2.14.

As in the Archimedean bundle, the carrier is abstract and the closed embedding
is a field, so that the coded carrier of Lemma 3.10 can be used directly.  The
domain is the bare `UMet(Z;R)` of `Ext/UltraPMet.lean` rather than a
topology-aware locus on the subspace `ι(Z) ⊆ Y` for the reason recorded in
`Ext/GeneralSeparability.lean` for `CPM(A)`: `Z` is discrete, so the continuity
constraint on its pseudo-ultrametrics is vacuous and the two descriptions of
E2's domain agree. -/

/-- **The E2 interface** (audit §3, clauses (1), (2), (5)): an isometric
extensor `E : UMet(Z;R) → UMet(Y;R)` along a closed embedding of a discrete
carrier.

`extension` is clause (1) restricted to `UMet(Z;R)`, `isometry_toUCPMOn` is
clause (2) at the `𝒰𝒟^R` level the ambient carries, and `umet_preservation` is
clause (5).  Nothing here is stronger than what E2 gives: every field is a
restriction of an E2 clause to the compatible locus, and the codomain of
`toUCPMOn` is the *ambient* `UCPM(Y;R)`, with membership in `UMet(Y;R)` recorded
separately rather than built into the type. -/
structure IsUltraIsometricExtensor {Z Y : Type*} (tZ : TopologicalSpace Z)
    [TopologicalSpace Y] (R : RangeSet) (ι : Z → Y) where
  /-- The carrier is a closed subspace of `Y`; E2 applies to closed subsets. -/
  closedEmbedding : @Topology.IsClosedEmbedding Z Y tZ inferInstance ι
  /-- The carrier is discrete, so its `UCPM(Z;R)` is the bare one of
  `Ext/UltraPMet.lean`. -/
  domain_discrete : tZ = ⊥
  /-- E2's `Σ`, restricted to the compatible locus — its actual domain. -/
  toUCPMOn : ↥(UMet Z R) → UCPMOn Y R
  /-- Clause (1): the extension restricts to the given metric on `Z²`. -/
  extension : ∀ (d : ↥(UMet Z R)) (a b : Z), (toUCPMOn d).1.1 (ι a) (ι b) = d.1.1 a b
  /-- Clause (2): `Σ` is a `𝒰𝒟^R`-isometry. -/
  isometry_toUCPMOn : Isometry toUCPMOn
  /-- Clause (5): `Σ` carries compatible ultrametrics to compatible
  ultrametrics. -/
  umet_preservation : ∀ d, toUCPMOn d ∈ UMetOn Y R

namespace IsUltraIsometricExtensor

variable [TopologicalSpace Y] {ι : Z → Y} {tZ : TopologicalSpace Z}

/-- Clause (1), in the form the transfer uses: restricting the extension along
`ι` returns the original member of `UMet(Z;R)`.  This is the identity that
identifies the extension on the closure. -/
theorem restrict_toUCPMOn (hE : IsUltraIsometricExtensor tZ R ι) (d : ↥(UMet Z R)) :
    UCPMOn.restrict ι (hE.toUCPMOn d) = (d : UCPM Z R) :=
  Subtype.ext (funext fun a => funext fun b => hE.extension d a b)

theorem injective_toUCPMOn (hE : IsUltraIsometricExtensor tZ R ι) :
    Function.Injective hE.toUCPMOn := by
  intro d e hde
  refine Subtype.ext ?_
  rw [← hE.restrict_toUCPMOn d, ← hE.restrict_toUCPMOn e, hde]

end IsUltraIsometricExtensor

/-- **The bundle is satisfiable.**  On a discrete carrier the identity is an
isometric extensor, so the hypothesis of the transfer theorems is not a
disguised `False` and those theorems are not vacuously true.

This witness is *not* E2 — E2's content is the existence of an extensor into a
strictly larger ultrametrizable space, which stays external — but it is what
makes the no-smuggle check on the bundle a proved fact rather than a remark.
Its consistency with the transfer theorems is Theorem 3.12: for a discrete `Z`
of cardinality `ℵ₁` those theorems then say that `UMet(Z;R)` is not Borel in
`UCPM(Z;R)`, which is what #81 proves outright. -/
theorem nonempty_isUltraIsometricExtensor_id (Z : Type*) (R : RangeSet) :
    letI : TopologicalSpace Z := ⊥
    Nonempty (IsUltraIsometricExtensor (⊥ : TopologicalSpace Z) R id) := by
  letI : TopologicalSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  exact
    ⟨{ closedEmbedding := Topology.IsClosedEmbedding.id
       domain_discrete := rfl
       toUCPMOn := fun d => ⟨d.1, continuous_of_discreteTopology⟩
       extension := fun _ _ _ => rfl
       isometry_toUCPMOn := fun _ _ => rfl
       umet_preservation := fun d => d.2 }⟩

end

end IshikiExt
