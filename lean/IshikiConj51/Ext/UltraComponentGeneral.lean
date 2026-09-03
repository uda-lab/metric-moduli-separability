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
import IshikiConj51.Ext.Component
import IshikiConj51.Ext.GeneralSpace

open Cardinal Set
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

/-! ## B2: coding on an `ℵ₁`-subset of an uncountable ball

The subset `H` need not itself be a ball.  The component estimate remembers an
enclosing `d`-ball, while compatibility below uses a uniform separation bound
on the whole carrier and never infers a distance bound from `x ∉ H`. -/

/-- Select an `ℵ₁`-sized `H` containing `z` inside an uncountable closed
ball and identify it with the carrier of the ultrametric coding. -/
theorem exists_aleph1_subset_uBall_equiv
    {Z : Type*} (d : UCPM Z R) (z : Z) (hZ : ¬ Countable Z)
    {S : Set (ℕ → Bool)} (hScard : #(↥S) = Cardinal.aleph 1) :
    ∃ q ∈ R.carrier, ∃ H : Set Z,
      H ⊆ uBall d z q ∧ z ∈ H ∧ #(↥H) = Cardinal.aleph 1 ∧
        Nonempty (↥H ≃ UltraIndex S) := by
  obtain ⟨q, hqR, hqunc⟩ := exists_radius_not_countable d z hZ
  have hq : 0 ≤ q := R.nonneg hqR
  have hballcard : Cardinal.aleph 1 ≤ #(↥(uBall d z q)) := by
    exact Cardinal.aleph_one_le_iff.mpr
      (Cardinal.aleph0_lt_mk_iff.mpr (not_countable_iff.mp hqunc))
  obtain ⟨H, hHsub, hzH, hHcard⟩ :=
    exists_aleph1_subset (mem_uBall_self d z hq) hballcard
  refine ⟨q, hqR, H, hHsub, hzH, hHcard, ?_⟩
  refine Cardinal.lift_mk_eq'.mp ?_
  rw [hHcard, card_ultraIndex hScard]
  simp

section SubsetCoding

variable {Z : Type*} {r : ℕ → ℝ} {S : Set (ℕ → Bool)}

/-- The Lemma 3.10 coding transported to `H`, then max-amalgamated with the
base ultrametric on the whole carrier. -/
def mCoding (hr : RangeSet.IsScale R r) (d : UCPM Z R) (H : Set Z)
    (z : Z) (hz : z ∈ H) (θ : ↥H → UltraIndex S) (t : ℕ → Bool) : UCPM Z R :=
  hAmalgam d H z hz θ (phiU hr S t)

theorem mCoding_val (hr : RangeSet.IsScale R r) {d : UCPM Z R}
    {H : Set Z} {z : Z} {hz : z ∈ H} (θ : ↥H → UltraIndex S)
    (t : ℕ → Bool) (x y : Z) :
    (mCoding hr d H z hz θ t).1 x y
      = max (d.1 (hRetract H z x) (hRetract H z y))
        (dU r S t (θ (hInto H z hz x)) (θ (hInto H z hz y))) := rfl

theorem mCoding_in_in (hr : RangeSet.IsScale R r) {d : UCPM Z R}
    {H : Set Z} {z : Z} {hz : z ∈ H} {θ : ↥H → UltraIndex S}
    {t : ℕ → Bool} {x y : Z} (hx : x ∈ H) (hy : y ∈ H) :
    (mCoding hr d H z hz θ t).1 x y = dU r S t (θ ⟨x, hx⟩) (θ ⟨y, hy⟩) :=
  hAmalgam_in_in (d := d) (H := H) (z := z) (hz := hz)
    (κ := θ) (e := phiU hr S t) hx hy

theorem mCoding_out_out (hr : RangeSet.IsScale R r) {d : UCPM Z R}
    {H : Set Z} {z : Z} {hz : z ∈ H} {θ : ↥H → UltraIndex S}
    {t : ℕ → Bool} {x y : Z} (hx : x ∉ H) (hy : y ∉ H) :
    (mCoding hr d H z hz θ t).1 x y = d.1 x y :=
  hAmalgam_out_out (d := d) (H := H) (z := z) (hz := hz)
    (κ := θ) (e := phiU hr S t) hx hy

/-- On a pair pulled back through the coding equivalence, the amalgam is
exactly the original Lemma 3.10 coding. -/
theorem mCoding_val_symm (hr : RangeSet.IsScale R r) {d : UCPM Z R}
    {H : Set Z} {z : Z} {hz : z ∈ H} (θ : ↥H ≃ UltraIndex S)
    (t : ℕ → Bool) (u v : UltraIndex S) :
    (mCoding hr d H z hz θ t).1 (θ.symm u : Z) (θ.symm v : Z) = dU r S t u v := by
  rw [mCoding_in_in hr (θ.symm u).2 (θ.symm v).2, Subtype.coe_eta,
    Subtype.coe_eta, θ.apply_symm_apply, θ.apply_symm_apply]

/-- Compatibility for `t ∉ S`.  The strict `a`-separation of the base carrier
supplies the uniform isolating radius in every branch crossing or outside
`H`; no ball-membership implication is used. -/
theorem mCoding_topology_eq_bot (hr : RangeSet.IsScale R r)
    {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
    (θ : ↥H ≃ UltraIndex S) {a : ℝ} (ha : 0 < a)
    (hsep : ∀ x y : Z, x ≠ y → a < d.1 x y)
    {t : ℕ → Bool} (htS : t ∉ S) :
    UCPM.IsCompatible (mCoding hr d H z hz θ t) := by
  have hdm : IsMetricOn d.1 := by
    refine d.2.toIsMetricOn fun x y hxy => ?_
    by_contra hne
    exact absurd hxy (ne_of_gt (ha.trans (hsep x y hne)))
  have hbase : ∀ x y : Z,
      d.1 (hRetract H z x) (hRetract H z y) ≤
        (mCoding hr d H z hz θ t).1 x y :=
    base_le_hAmalgam (d := d) (H := H) (z := z) (hz := hz)
      (κ := θ) (e := phiU hr S t)
  have hcm : IsMetricOn (mCoding hr d H z hz θ t).1 := by
    refine (mCoding hr d H z hz θ t).2.toIsMetricOn fun x y hxy => ?_
    by_cases hx : x ∈ H
    · by_cases hy : y ∈ H
      · rw [mCoding_in_in hr hx hy] at hxy
        have hθ := (dU_isMetricOn hr S t).eq_of_dist_eq_zero hxy
        exact congrArg Subtype.val (θ.injective hθ)
      · exfalso
        have hle := hbase x y
        rw [hRetract_of_mem hx, hRetract_of_notMem hy, hxy] at hle
        have hzy : z ≠ y := fun h => hy (h ▸ hz)
        exact (not_lt_of_ge hle) (ha.trans (hsep z y hzy))
    · by_cases hy : y ∈ H
      · exfalso
        have hle := hbase x y
        rw [hRetract_of_notMem hx, hRetract_of_mem hy, hxy] at hle
        have hxz : x ≠ z := fun h => hx (h ▸ hz)
        exact (not_lt_of_ge hle) (ha.trans (hsep x z hxz))
      · rw [mCoding_out_out hr hx hy] at hxy
        exact hdm.eq_of_dist_eq_zero hxy
  refine ⟨hcm, hcm.topology_eq_bot_iff.mpr fun u => ?_⟩
  by_cases hu : u ∈ H
  · obtain ⟨ε, hε, hall⟩ :=
      (dU_isMetricOn hr S t).topology_eq_bot_iff.mp
        (dU_topology_eq_bot hr htS) (θ ⟨u, hu⟩)
    refine ⟨min ε a, lt_min hε ha, fun v hv => ?_⟩
    by_cases hvH : v ∈ H
    · rw [mCoding_in_in hr hvH hu] at hv
      have hθ := hall _ (lt_of_lt_of_le hv (min_le_left _ _))
      exact congrArg Subtype.val (θ.injective hθ)
    · exfalso
      have hle := hbase v u
      rw [hRetract_of_notMem hvH, hRetract_of_mem hu] at hle
      have hvz : v ≠ z := fun h => hvH (h ▸ hz)
      have hvza : d.1 v z < a :=
        lt_of_le_of_lt hle (lt_of_lt_of_le hv (min_le_right _ _))
      exact (not_lt_of_ge (hsep v z hvz).le) hvza
  · refine ⟨a, ha, fun v hv => ?_⟩
    by_cases hvH : v ∈ H
    · exfalso
      have hle := hbase v u
      rw [hRetract_of_mem hvH, hRetract_of_notMem hu] at hle
      have hzu : z ≠ u := fun h => hu (h ▸ hz)
      exact (not_lt_of_ge (hsep z u hzu).le) (lt_of_le_of_lt hle hv)
    · rw [mCoding_out_out hr hvH hu] at hv
      by_contra hvu
      exact (not_lt_of_ge (hsep v u hvu).le) hv

/-- Compatibility fails for `t ∈ S`; the non-isolated coding centre and its
approaching spokes all lie inside `H`. -/
theorem mCoding_topology_ne_bot (hr : RangeSet.IsScale R r)
    {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
    (θ : ↥H ≃ UltraIndex S) {t : ℕ → Bool} (htS : t ∈ S) :
    ¬ UCPM.IsCompatible (mCoding hr d H z hz θ t) := by
  rintro ⟨hcm, hbot⟩
  obtain ⟨ε, hε, hall⟩ :=
    hcm.topology_eq_bot_iff.mp hbot
      (θ.symm ((⟨t, htS⟩ : ↥S), none) : Z)
  obtain ⟨n, hn⟩ := hr.exists_lt hε
  have hval : dU r S t ((⟨t, htS⟩ : ↥S), some n) ((⟨t, htS⟩ : ↥S), none) = r n := by
    rw [dU_same, clusterDist, if_neg (by simp : (some n : Option ℕ) ≠ none)]
    show max (uRadius r t t (some n)) (uRadius r t t none) = r n
    rw [uRadius_some, uRadius_none, cantorDist_self, max_eq_right (hr.nonneg n),
      max_eq_left (hr.nonneg n)]
  have hlt : (mCoding hr d H z hz θ t).1
      (θ.symm ((⟨t, htS⟩ : ↥S), some n) : Z)
      (θ.symm ((⟨t, htS⟩ : ↥S), none) : Z) < ε := by
    rw [mCoding_val_symm hr θ t, hval]
    exact hn
  have heq := hall _ hlt
  have hinj := θ.symm.injective (Subtype.ext heq)
  simp at hinj

/-- **Amalgamated-coding compatibility.** -/
theorem mem_UMet_mCoding_iff (hr : RangeSet.IsScale R r)
    {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
    (θ : ↥H ≃ UltraIndex S) {a : ℝ} (ha : 0 < a)
    (hsep : ∀ x y : Z, x ≠ y → a < d.1 x y) (t : ℕ → Bool) :
    mCoding hr d H z hz θ t ∈ UMet Z R ↔ t ∉ S :=
  ⟨fun h htS => mCoding_topology_ne_bot hr θ htS h,
    fun htS => mCoding_topology_eq_bot hr θ ha hsep htS⟩

/-- **Amalgamated-coding component bound.**  The subset `H` is only assumed
to lie in the selected closed ball.  The proof splits on membership in that
enclosing ball, not on membership in `H`. -/
theorem edist_mCoding_base_le (hr : RangeSet.IsScale R r)
    {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
    {θ : ↥H → UltraIndex S} {q : ℝ} (hqR : q ∈ R.carrier)
    (hHball : H ⊆ uBall d z q) (t : ℕ → Bool) :
    UCPM.edist d (mCoding hr d H z hz θ t) ≤
      ENNReal.ofReal (max q (r 0)) := by
  have hq : 0 ≤ q := R.nonneg hqR
  have hret_mem : ∀ {x : Z}, x ∈ uBall d z q → hRetract H z x ∈ uBall d z q := by
    intro x hx
    by_cases hxH : x ∈ H
    · rw [hRetract_of_mem hxH]
      exact mem_uBall_self d z hq
    · rw [hRetract_of_notMem hxH]
      exact hx
  refine UCPM.edist_le_ofReal ⟨R.max_mem hqR (hr.mem 0), fun x y => ?_⟩
  by_cases hx : x ∈ uBall d z q
  · by_cases hy : y ∈ uBall d z q
    · rw [mCoding_val hr]
      exact
        ⟨le_max_of_le_right (le_max_of_le_left (uBall_dist_le hx hy)),
          le_max_of_le_right (max_le
            (le_max_of_le_left (uBall_dist_le (hret_mem hx) (hret_mem hy)))
            (le_max_of_le_right (dU_le_head hr S t _ _)))⟩
    · have hyH : y ∉ H := fun hy' => hy (hHball hy')
      by_cases hxH : x ∈ H
      · have hzy : d.1 z y = d.1 x y := by
          rw [d.2.dist_comm z y, ← uBall_isosceles hy hx]
          exact d.2.dist_comm y x
        rw [mCoding_val hr, hRetract_of_mem hxH, hRetract_of_notMem hyH,
          hInto_of_mem hxH, hInto_of_notMem hyH, hzy]
        exact
          ⟨le_max_of_le_left (le_max_left _ _),
            max_le (le_max_left _ _)
              (le_max_of_le_right (le_max_of_le_right (dU_le_head hr S t _ _)))⟩
      · rw [mCoding_out_out hr hxH hyH]
        exact ⟨le_max_left _ _, le_max_left _ _⟩
  · have hxH : x ∉ H := fun hx' => hx (hHball hx')
    by_cases hy : y ∈ uBall d z q
    · by_cases hyH : y ∈ H
      · have hxz : d.1 x z = d.1 x y := (uBall_isosceles hx hy).symm
        rw [mCoding_val hr, hRetract_of_notMem hxH, hRetract_of_mem hyH,
          hInto_of_notMem hxH, hInto_of_mem hyH, hxz]
        exact
          ⟨le_max_of_le_left (le_max_left _ _),
            max_le (le_max_left _ _)
              (le_max_of_le_right (le_max_of_le_right (dU_le_head hr S t _ _)))⟩
      · rw [mCoding_out_out hr hxH hyH]
        exact ⟨le_max_left _ _, le_max_left _ _⟩
    · have hyH : y ∉ H := fun hy' => hy (hHball hy')
      rw [mCoding_out_out hr hxH hyH]
      exact ⟨le_max_left _ _, le_max_left _ _⟩

/-- The upper half of the coding-family isometry. -/
theorem edist_mCoding_le (hr : RangeSet.IsScale R r)
    {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
    {θ : ↥H → UltraIndex S} (s t : ℕ → Bool) :
    UCPM.edist (mCoding hr d H z hz θ s) (mCoding hr d H z hz θ t) ≤
      ENNReal.ofReal (cantorDist r s t) := by
  refine UCPM.edist_le_ofReal ⟨cantorDist_mem hr s t, fun x y => ⟨?_, ?_⟩⟩
  · rw [mCoding_val hr, mCoding_val hr]
    refine max_le (le_max_of_le_left (le_max_left _ _)) ?_
    refine (dU_le_max hr S s t _ _).trans ?_
    exact max_le (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _)
  · rw [mCoding_val hr, mCoding_val hr]
    refine max_le (le_max_of_le_left (le_max_left _ _)) ?_
    have h := dU_le_max hr S t s (θ (hInto H z hz x)) (θ (hInto H z hz y))
    rw [cantorDist_comm r t s] at h
    exact h.trans
      (max_le (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _))

/-- **Amalgamated-coding isometry.**  The separating pair lies in `H`, where
the amalgam agrees exactly with the transported Lemma 3.10 coding. -/
theorem edist_mCoding (hr : RangeSet.IsScale R r) (hS : Dense S)
    {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
    (θ : ↥H ≃ UltraIndex S) (s t : ℕ → Bool) :
    UCPM.edist (mCoding hr d H z hz θ s) (mCoding hr d H z hz θ t) =
      ENNReal.ofReal (cantorDist r s t) := by
  refine le_antisymm (edist_mCoding_le hr s t) ?_
  rcases eq_or_ne s t with rfl | hst
  · simp
  obtain ⟨u, v, hus, hut⟩ := exists_separating_pair hr hS hst
  refine UCPM.ofReal_le_edist fun c hc => ?_
  refine UCPM.le_of_mem_tolerances hc (θ.symm u : Z) (θ.symm v : Z) ?_ ?_
  · rw [mCoding_val_symm hr θ s]
    exact hus
  · rw [mCoding_val_symm hr θ t]
    exact hut

end SubsetCoding

/-! ## B3: extension of the coding family from the dense complement -/

section DenseCodingExtension

variable {Y : Type*} [TopologicalSpace Y] {A : Set Y}
variable {r : ℕ → ℝ} {S : Set (ℕ → Bool)}

/-- The E2c image of the amalgamated coding, restricted to the dense
complement of the bad parameter set. -/
def F {d : UCPMOn Y R} {a : ℝ}
    (hd : d ∈ UMetOn Y R) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y) :
    ↥(Sᶜ) → UCPMOn Y R := by
  let dA := UCPMOn.restrict (Subtype.val : ↥A → Y) d
  have hdA : dA ∈ UMet ↥A R := by
    exact UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace ↥A)
      (by
        letI : TopologicalSpace ↥A := ⊥
        exact E2c.toExtensor.closedEmbedding.toIsEmbedding)
      E2c.toExtensor.domain_discrete hd
  have hsepA : ∀ x y : ↥A, x ≠ y → a < dA.1 x y := by
    intro x y hxy
    simpa [dA] using hsep x y hxy
  intro s
  rcases s with ⟨t, ht⟩
  exact E2c.toExtensor.toUCPMOn
    ⟨mCoding hr dA H z hz θ t,
      (mem_UMet_mCoding_iff hr θ ha hsepA t).mpr ht⟩

/-/ The exact distance formula for `F`; the density of `S` is the lower-bound
input in `edist_mCoding`. -/
theorem isometry_F {d : UCPMOn Y R} {a : ℝ}
    (hd : d ∈ UMetOn Y R) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y) (hS : Dense S) :
    ∀ s t : ↥(Sᶜ),
      edist (F hd hr E2c H z hz θ ha hsep s)
          (F hd hr E2c H z hz θ ha hsep t) =
        ENNReal.ofReal (cantorDist r s.1 t.1) := by
  let dA := UCPMOn.restrict (Subtype.val : ↥A → Y) d
  have hdA : dA ∈ UMet ↥A R := by
    exact UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace ↥A)
      (by
        letI : TopologicalSpace ↥A := ⊥
        exact E2c.toExtensor.closedEmbedding.toIsEmbedding)
      E2c.toExtensor.domain_discrete hd
  have hsepA : ∀ x y : ↥A, x ≠ y → a < dA.1 x y := by
    intro x y hxy
    simpa [dA] using hsep x y hxy
  intro s t
  change edist
      (E2c.toExtensor.toUCPMOn
        ⟨mCoding hr dA H z hz θ s.1,
          (mem_UMet_mCoding_iff hr θ ha hsepA s.1).mpr s.2⟩)
      (E2c.toExtensor.toUCPMOn
        ⟨mCoding hr dA H z hz θ t.1,
          (mem_UMet_mCoding_iff hr θ ha hsepA t.1).mpr t.2⟩) = _
  rw [E2c.toExtensor.isometry_toUCPMOn]
  exact edist_mCoding hr hS θ s.1 t.1

/-- A dense-complement coding family has a uniformly continuous extension to
the whole Cantor space.  The two displayed facts are kept local because only
the extension and its restriction identity are consumed downstream. -/
theorem exists_continuous_Fbar {d : UCPMOn Y R} {a : ℝ}
    (hd : d ∈ UMetOn Y R) (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y)
    (hS : Dense S) (hG : Dense Sᶜ) :
    ∃ Fbar : (ℕ → Bool) → UCPMOn Y R,
      Continuous Fbar ∧
        ∀ (t : ℕ → Bool) (ht : t ∈ Sᶜ),
          Fbar t = F hd hr E2c H z hz θ ha hsep ⟨t, ht⟩ := by
  letI : MetricSpace (ℕ → Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity
      (fun _ => DiscreteUniformity.eq_principal_setRelId (X := Bool))
  letI : Dense (Sᶜ) := hG
  let Fbar := (‹Dense (Sᶜ)›).extend
    (F hd hr E2c H z hz θ ha hsep)
  have hFuc : UniformContinuous (F hd hr E2c H z hz θ ha hsep) := by
    rw [EMetric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨c, hc, hcε⟩ : ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c < ε := by
      obtain ⟨q, hq, hqε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
      refine ⟨(q : ℝ), by exact_mod_cast ENNReal.coe_pos.mp hq, ?_⟩
      rwa [ENNReal.ofReal_coe_nnreal]
    obtain ⟨n, hn⟩ := hr.exists_lt hc
    refine ⟨ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)), by positivity, ?_⟩
    intro s t hst
    have hst' : dist (s : ℕ → Bool) (t : ℕ → Bool) <
        (1 / 2 : ℝ) ^ (n + 1) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
      simpa only [edist_dist, Subtype.dist_eq] using hst
    have hagree : ∀ m ≤ n, s.1 m = t.1 m := by
      intro m hm
      exact PiNat.apply_eq_of_dist_lt hst' (Nat.le_succ_of_le hm)
    have hcantor : cantorDist r s.1 t.1 < r n :=
      (cantorDist_lt_iff hr s.1 t.1 n).mpr hagree
    rw [isometry_F hd hr E2c H z hz θ ha hsep hS s t]
    exact ((ENNReal.ofReal_lt_ofReal_iff hc).mpr (hcantor.trans hn)).trans hcε
  haveI : CompleteSpace (UCPMOn Y R) := completeSpace_UCPMOn hR
  have hFbar_uc : UniformContinuous Fbar :=
    Dense.uniformContinuous_extend (‹Dense (Sᶜ)›) hFuc
  have Continuous_Fbar : Continuous Fbar := hFbar_uc.continuous
  have Fbar_apply : ∀ (t : ℕ → Bool) (ht : t ∈ Sᶜ),
      Fbar t = F hd hr E2c H z hz θ ha hsep ⟨t, ht⟩ := by
    intro t ht
    simpa [Fbar] using
      (Dense.extend_of_ind (‹Dense (Sᶜ)›) hFuc ⟨t, ht⟩)
  exact ⟨Fbar, Continuous_Fbar, Fbar_apply⟩

end DenseCodingExtension

/-! ## B4: exact pullback of the finite-distance component -/

section ExactComponentPullback

variable {Y : Type*} [TopologicalSpace Y] {A : Set Y}
variable {r : ℕ → ℝ} {S : Set (ℕ → Bool)}

/-- The extension of the coding family restricts to the original amalgamated
coding for every Cantor parameter, including parameters in the bad set `S`. -/
theorem restrict_Fbar_eq_mCoding {d : UCPMOn Y R} {a : ℝ}
    (hd : d ∈ UMetOn Y R) (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y)
    (hS : Dense S) (hG : Dense Sᶜ)
    (Fbar : (ℕ → Bool) → UCPMOn Y R) (hFbar : Continuous Fbar)
    (hFbar_apply : ∀ (t : ℕ → Bool) (ht : t ∈ Sᶜ),
      Fbar t = F hd hr E2c H z hz θ ha hsep ⟨t, ht⟩)
    (t : ℕ → Bool) :
    UCPMOn.restrict (Subtype.val : ↥A → Y) (Fbar t) =
      mCoding hr (UCPMOn.restrict (Subtype.val : ↥A → Y) d) H z hz θ t := by
  let dA := UCPMOn.restrict (Subtype.val : ↥A → Y) d
  have hdA : dA ∈ UMet ↥A R := by
    exact UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace ↥A)
      (by
        letI : TopologicalSpace ↥A := ⊥
        exact E2c.toExtensor.closedEmbedding.toIsEmbedding)
      E2c.toExtensor.domain_discrete hd
  have hsepA : ∀ x y : ↥A, x ≠ y → a < dA.1 x y := by
    intro x y hxy
    simpa [dA] using hsep x y hxy
  have heq :
      (fun t : ℕ → Bool => UCPMOn.restrict (Subtype.val : ↥A → Y) (Fbar t)) =
        fun t : ℕ → Bool => mCoding hr dA H z hz θ t := by
    refine Continuous.ext_on hG
      ((UCPMOn.lipschitzWith_restrict
        (Subtype.val : ↥A → Y)).continuous.comp hFbar)
      (continuous_of_edist_le_cantorDist hr fun s t => edist_mCoding_le hr s t) ?_
    intro u hu
    show UCPMOn.restrict (Subtype.val : ↥A → Y) (Fbar u) =
      mCoding hr dA H z hz θ u
    rw [hFbar_apply u hu]
    change UCPMOn.restrict (Subtype.val : ↥A → Y)
        (E2c.toExtensor.toUCPMOn
          ⟨mCoding hr dA H z hz θ u,
            (mem_UMet_mCoding_iff hr θ ha hsepA u).mpr hu⟩) =
      mCoding hr dA H z hz θ u
    exact E2c.restrict _
  simpa [dA] using congrFun heq t

/-- Compatibility of the extended coding is pulled back exactly to the dense
complement of `S`. -/
theorem mem_UMetOn_Fbar_iff {d : UCPMOn Y R} {a : ℝ}
    (hd : d ∈ UMetOn Y R) (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y)
    (hS : Dense S) (hG : Dense Sᶜ)
    (Fbar : (ℕ → Bool) → UCPMOn Y R) (hFbar : Continuous Fbar)
    (hFbar_apply : ∀ (t : ℕ → Bool) (ht : t ∈ Sᶜ),
      Fbar t = F hd hr E2c H z hz θ ha hsep ⟨t, ht⟩)
    (t : ℕ → Bool) :
    Fbar t ∈ UMetOn Y R ↔ t ∈ Sᶜ := by
  let dA := UCPMOn.restrict (Subtype.val : ↥A → Y) d
  have hdA : dA ∈ UMet ↥A R := by
    exact UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace ↥A)
      (by
        letI : TopologicalSpace ↥A := ⊥
        exact E2c.toExtensor.closedEmbedding.toIsEmbedding)
      E2c.toExtensor.domain_discrete hd
  have hsepA : ∀ x y : ↥A, x ≠ y → a < dA.1 x y := by
    intro x y hxy
    simpa [dA] using hsep x y hxy
  constructor
  · intro ht
    have hrestrict : UCPMOn.restrict (Subtype.val : ↥A → Y) (Fbar t) ∈
        UMet ↥A R := by
      exact UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace ↥A)
        (by
          letI : TopologicalSpace ↥A := ⊥
          exact E2c.toExtensor.closedEmbedding.toIsEmbedding)
        E2c.toExtensor.domain_discrete ht
    rw [restrict_Fbar_eq_mCoding hd hR hr E2c H z hz θ ha hsep hS hG
      Fbar hFbar hFbar_apply t] at hrestrict
    exact (mem_UMet_mCoding_iff hr θ ha hsepA t).mp hrestrict
  · intro ht
    rw [hFbar_apply t ht]
    change E2c.toExtensor.toUCPMOn
        ⟨mCoding hr dA H z hz θ t,
          (mem_UMet_mCoding_iff hr θ ha hsepA t).mpr ht⟩ ∈ UMetOn Y R
    exact E2c.umet_preservation _

/-- Every value of the extended coding family lies at finite distance from
the base metric.  The ball hypotheses are exactly the B2 data used by
`edist_mCoding_base_le`; they are not needed by the B3 extension itself. -/
theorem edist_Fbar_lt_top {d : UCPMOn Y R} {a q : ℝ}
    (hd : d ∈ UMetOn Y R) (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y)
    (hS : Dense S) (hG : Dense Sᶜ)
    (hqR : q ∈ R.carrier)
    (hHball : H ⊆ uBall
      (UCPMOn.restrict (Subtype.val : ↥A → Y) d) z q)
    (Fbar : (ℕ → Bool) → UCPMOn Y R) (hFbar : Continuous Fbar)
    (hFbar_apply : ∀ (t : ℕ → Bool) (ht : t ∈ Sᶜ),
      Fbar t = F hd hr E2c H z hz θ ha hsep ⟨t, ht⟩)
    (t : ℕ → Bool) :
    edist d (Fbar t) < ⊤ := by
  let dA := UCPMOn.restrict (Subtype.val : ↥A → Y) d
  have hdA : dA ∈ UMet ↥A R := by
    exact UCPM.isCompatible_comap_of_mem_UMetOn (⊥ : TopologicalSpace ↥A)
      (by
        letI : TopologicalSpace ↥A := ⊥
        exact E2c.toExtensor.closedEmbedding.toIsEmbedding)
      E2c.toExtensor.domain_discrete hd
  have hsepA : ∀ x y : ↥A, x ≠ y → a < dA.1 x y := by
    intro x y hxy
    simpa [dA] using hsep x y hxy
  let dHat := E2c.toExtensor.toUCPMOn (⟨dA, hdA⟩ : ↥(UMet ↥A R))
  have hdHat : edist d dHat < ⊤ := by
    rw [edist_comm]
    exact E2c.component_control hd
  have hfinite_on_compl : ∀ u ∈ Sᶜ, edist d (Fbar u) < ⊤ := by
    intro u hu
    have hdHat_Fbar : edist dHat (Fbar u) < ⊤ := by
      rw [hFbar_apply u hu]
      change edist
          (E2c.toExtensor.toUCPMOn (⟨dA, hdA⟩ : ↥(UMet ↥A R)))
          (E2c.toExtensor.toUCPMOn
            ⟨mCoding hr dA H z hz θ u,
              (mem_UMet_mCoding_iff hr θ ha hsepA u).mpr hu⟩) < ⊤
      rw [E2c.isometry_toUCPMOn]
      exact lt_of_le_of_lt (edist_mCoding_base_le hr hqR hHball u)
        ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt (edist_triangle d dHat (Fbar u))
      (ENNReal.add_lt_top.mpr ⟨hdHat, hdHat_Fbar⟩)
  have hfinite_closed : IsClosed {e : UCPMOn Y R | edist d e < ⊤} := by
    rw [← isOpen_compl_iff, EMetric.isOpen_iff]
    intro e he
    refine ⟨1, one_pos, fun f hf hfd => he ?_⟩
    have hfe : edist f e < ⊤ :=
      lt_of_lt_of_le (Metric.mem_eball.mp hf) le_top
    calc edist d e ≤ edist d f + edist f e := edist_triangle d f e
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hfd, hfe⟩
  have hclosure : closure (Sᶜ) ⊆
      Fbar ⁻¹' {e : UCPMOn Y R | edist d e < ⊤} :=
    closure_minimal hfinite_on_compl (hfinite_closed.preimage hFbar)
  exact hclosure (hG t)

/-- The literal pullback identity
`Fbar ⁻¹' UCPMOn.component R d = Sᶜ`. -/
theorem preimage_UCPMOn_component_Fbar {d : UCPMOn Y R} {a q : ℝ}
    (hd : d ∈ UMetOn Y R) (hR : R.IsCharacteristic) (hr : RangeSet.IsScale R r)
    (E2c : IsUltraComponentControlledExtensorOn R A d a)
    (H : Set (↥A)) (z : ↥A) (hz : z ∈ H)
    (θ : ↥H ≃ UltraIndex S) (ha : 0 < a)
    (hsep : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y)
    (hS : Dense S) (hG : Dense Sᶜ)
    (hqR : q ∈ R.carrier)
    (hHball : H ⊆ uBall
      (UCPMOn.restrict (Subtype.val : ↥A → Y) d) z q)
    (Fbar : (ℕ → Bool) → UCPMOn Y R) (hFbar : Continuous Fbar)
    (hFbar_apply : ∀ (t : ℕ → Bool) (ht : t ∈ Sᶜ),
      Fbar t = F hd hr E2c H z hz θ ha hsep ⟨t, ht⟩) :
    Fbar ⁻¹' UCPMOn.component R d = Sᶜ := by
  ext t
  constructor
  · intro ht
    exact (mem_UMetOn_Fbar_iff hd hR hr E2c H z hz θ ha hsep hS hG
      Fbar hFbar hFbar_apply t).mp ht.1
  · intro ht
    exact ⟨(mem_UMetOn_Fbar_iff hd hR hr E2c H z hz θ ha hsep hS hG
        Fbar hFbar hFbar_apply t).mpr ht,
      edist_Fbar_lt_top hd hR hr E2c H z hz θ ha hsep hS hG hqR hHball
        Fbar hFbar hFbar_apply t⟩

end ExactComponentPullback

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
            (∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y ≤ a) →
          Nonempty (IsUltraComponentControlledExtensorOn R A d a)) :
    ∀ d ∈ UMetOn Y R, ¬ MeasurableSet (UCPMOn.component R d) := by
  intro d hd
  obtain ⟨a, haR, ha_ne, A, hAsep, hAnet, hAunc, hAclosed, hAdisc⟩ :=
    exists_maximal_aScale_separated_net d hd hYsep hR
  have hAsep_le : A.Pairwise (fun x y => a ≤ d.1.1 x y) := by
    intro x hx y hy hxy
    exact (hAsep hx hy hxy).le
  have hAnet' : ∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y ≤ a := by
    rintro x -
    exact hAnet x
  obtain ⟨z⟩ : Nonempty (↥A) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have hAeq : A = ∅ := Set.isEmpty_coe_sort.mp hne
    exact hAunc (hAeq.symm ▸ Set.countable_empty)
  obtain ⟨E2c⟩ :=
    hEx d hd a haR ha_ne A ⟨(z : Y), z.property⟩ hAclosed hAdisc hAsep_le hAnet'
  obtain ⟨S, hS, hG, hScard, hSnonmeas⟩ :=
    exists_bidense_aleph1_nonBorel_cantor
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  let dA : UCPM (↥A) R :=
    UCPMOn.restrict (Subtype.val : ↥A → Y) d
  obtain ⟨q, hqR, H, hHball, hzH, hHcard, ⟨θ⟩⟩ :=
    exists_aleph1_subset_uBall_equiv dA z hAunc hScard
  have ha : 0 < a := lt_of_le_of_ne (R.nonneg haR) (Ne.symm ha_ne)
  have hsepA : ∀ x y : ↥A, x ≠ y → a < d.1.1 x y := by
    intro x y hxy
    exact hAsep x.property y.property (by
      intro hxy'
      exact hxy (Subtype.ext hxy'))
  obtain ⟨Fbar, hFbar, hFbar_apply⟩ :=
    exists_continuous_Fbar hd hR hr E2c H z hzH θ ha hsepA hS hG
  have hpull : Fbar ⁻¹' UCPMOn.component R d = Sᶜ :=
    preimage_UCPMOn_component_Fbar hd hR hr E2c H z hzH θ ha hsepA hS hG
      hqR hHball Fbar hFbar hFbar_apply
  intro hcomp
  have hpre : MeasurableSet (Fbar ⁻¹' UCPMOn.component R d) :=
    hcomp.preimage hFbar.measurable
  rw [hpull] at hpre
  exact hSnonmeas (by simpa using hpre.compl)

/-- The whole-locus clause of `cor:nonseparable-ultrametric-nonborel` from
audit §2.19: `UMetOn Y R` itself is non-Borel in the same existing ambient
measurable space, under the same E2c package. -/
theorem not_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y)
    (hYsep : ¬ TopologicalSpace.SeparableSpace Y)
    (hR : R.IsCharacteristic)
    (hne : (UMetOn Y R).Nonempty)
    (hEx : ∀ (d : UCPMOn Y R), d ∈ UMetOn Y R →
      ∀ (a : ℝ), a ∈ R.carrier → a ≠ 0 →
        ∀ (A : Set Y),
          A.Nonempty → IsClosed A → DiscreteTopology ↥A →
            A.Pairwise (fun x y => a ≤ d.1.1 x y) →
            (∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y ≤ a) →
          Nonempty (IsUltraComponentControlledExtensorOn R A d a)) :
    ¬ MeasurableSet (UMetOn Y R) := by
  sorry

end
end IshikiExt
