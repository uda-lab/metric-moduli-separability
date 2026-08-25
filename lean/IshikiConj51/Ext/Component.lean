-- Ext.Component
--
-- Theorem 3.4 of the Borel preprint (arXiv:2608.19618,
-- `thm:metric-component-nonborel`): for a discrete `Z` with `|Z| = ℵ₁`, every
-- finite-sup-distance component of `Met(Z)` is non-Borel in `CPM(Z)`.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.7, whose
-- verdict is PASS and which records the two steps the preprint leaves
-- implicit — (i) the amalgam stays at finite sup distance from the base
-- metric, (ii) membership in the component is equivalent to compatibility,
-- which is what makes the trace identity exact.  Both are proved below.
--
-- Theorem 3.4 is *not* a prerequisite of Theorem 3.5: audit §2.8 records that
-- the verified route to the separability theorem runs through `Met(Z)`
-- itself.  Nothing in this file is consumed by `Ext/GeneralSeparability.lean`.
--
-- The construction (audit §2.7).  Fix `d ∈ 𝔠` and `z ∈ Z`.  Some closed
-- `d`-ball `E` around `z` has `|E| = ℵ₁` (a countable union of countable balls
-- would exhaust `Z`).  Transfer the star coding of `Ext/BoundedCoding.lean` to
-- `E` along a bijection sending the coding's anchor `p` to `z`, and amalgamate
-- the result with `d` along `z` (`Ext/Amalgam.lean`).  The amalgamated family
-- `Ψ : [0,1] → CPM(Z)` is `2`-Lipschitz, has compact range, and satisfies the
-- exact pullback identity `Ψ⁻¹(𝔠) = [0,1] ∖ S`, so a Borel `𝔠` would make the
-- non-Borel parameter set `S` Borel.
--
-- Component convention (audit §1): `d ∼ e` iff `𝒟_Z(d,e) < ∞`, the supremum
-- distance being `[0,∞]`-valued.  `CPM.component` is the class of a member of
-- `Met(Z)` and `CPM.componentSet` is the same set indexed by the quotient
-- `𝐌_{<∞}(Z)`, which is the form in which "every component" is stated.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Amalgam
import IshikiConj51.Ext.Relabel

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

local instance componentCpmMeasurableSpace (Z : Type*) : MeasurableSpace (CPM Z) :=
  borel (CPM Z)

local instance componentCpmBorelSpace (Z : Type*) : BorelSpace (CPM Z) :=
  ⟨rfl⟩

/-! ## Components of `Met(Z)` -/

variable {Z : Type*}

/-- The finite-sup-distance component of `d`: the members of `Met(Z)` at
finite supremum distance from `d`.  For `d ∈ Met(Z)` this is exactly the
`∼`-class of `d` in the sense of audit §1. -/
def CPM.component (d : CPM Z) : Set (CPM Z) :=
  {e | e ∈ CPM.Met Z ∧ CPM.edist d e < ⊤}

theorem CPM.component_subset_Met (d : CPM Z) : CPM.component d ⊆ CPM.Met Z :=
  fun _ he => he.1

theorem CPM.self_mem_component {d : CPM Z} (hd : d ∈ CPM.Met Z) : d ∈ CPM.component d :=
  ⟨hd, by rw [CPM.edist_self]; exact ENNReal.zero_lt_top⟩

/-- The components partition `Met(Z)`: any member of a component determines
the same component.  Together with `CPM.self_mem_component` this identifies
the sets `CPM.component d`, `d ∈ Met(Z)`, with the `∼`-classes. -/
theorem CPM.component_eq_of_mem {d e : CPM Z} (he : e ∈ CPM.component d) :
    CPM.component e = CPM.component d := by
  ext f
  constructor
  · rintro ⟨hf, hef⟩
    exact ⟨hf, lt_of_le_of_lt (CPM.edist_triangle d e f)
      (ENNReal.add_lt_top.mpr ⟨he.2, hef⟩)⟩
  · rintro ⟨hf, hdf⟩
    refine ⟨hf, lt_of_le_of_lt (CPM.edist_triangle e d f)
      (ENNReal.add_lt_top.mpr ⟨?_, hdf⟩)⟩
    rw [CPM.edist_comm]
    exact he.2

/-- The relation `d ∼ e ⟺ 𝒟_Z(d,e) < ∞` on `Met(Z)` (audit §1). -/
def CPM.metSetoid (Z : Type*) : Setoid ↥(CPM.Met Z) where
  r d e := CPM.edist d.1 e.1 < ⊤
  iseqv :=
    { refl := fun d => by
        show CPM.edist d.1 d.1 < ⊤
        rw [CPM.edist_self]
        exact ENNReal.zero_lt_top
      symm := fun {d e} h => by
        show CPM.edist e.1 d.1 < ⊤
        rwa [CPM.edist_comm]
      trans := fun {d e f} h1 h2 =>
        lt_of_le_of_lt (CPM.edist_triangle d.1 e.1 f.1)
          (ENNReal.add_lt_top.mpr ⟨h1, h2⟩) }

/-- `𝐌_{<∞}(Z) = Met(Z)/∼`, the set of finite-sup-distance components. -/
def CPM.Components (Z : Type*) : Type _ := Quotient (CPM.metSetoid Z)

/-- A component, read as a subset of the ambient `CPM(Z)`.  The class is named
`comp` rather than `𝔠` because that glyph is Mathlib's notation for the
continuum. -/
def CPM.componentSet (comp : CPM.Components Z) : Set (CPM Z) :=
  Subtype.val '' {e : ↥(CPM.Met Z) | Quotient.mk (CPM.metSetoid Z) e = comp}

theorem CPM.componentSet_mk (d : ↥(CPM.Met Z)) :
    CPM.componentSet (Quotient.mk (CPM.metSetoid Z) d) = CPM.component d.1 := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    have hed : CPM.edist e.1 d.1 < ⊤ := Quotient.exact he
    refine ⟨e.2, ?_⟩
    rwa [CPM.edist_comm]
  · rintro ⟨hx, hlt⟩
    refine ⟨⟨x, hx⟩, Quotient.sound ?_, rfl⟩
    show CPM.edist x d.1 < ⊤
    rwa [CPM.edist_comm]

/-! ## Nonvacuity: the `0/1` metric -/

open Classical in
/-- The `0/1` metric on a bare carrier, as a bare function.  It is a named
definition so that every statement below refers to the same `Decidable`
instance. -/
def discreteFn (Z : Type*) : Z → Z → ℝ := fun x y => if x = y then 0 else 1

@[simp] theorem discreteFn_self {Z : Type*} (x : Z) : discreteFn Z x x = 0 := by
  simp [discreteFn]

theorem discreteFn_of_ne {Z : Type*} {x y : Z} (h : x ≠ y) : discreteFn Z x y = 1 := by
  simp [discreteFn, h]

theorem discreteFn_nonneg {Z : Type*} (x y : Z) : 0 ≤ discreteFn Z x y := by
  by_cases h : x = y
  · rw [h, discreteFn_self]
  · rw [discreteFn_of_ne h]
    norm_num

theorem isMetricOn_discreteFn (Z : Type*) : IsMetricOn (discreteFn Z) where
  dist_self x := discreteFn_self x
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    rw [discreteFn_of_ne hne] at h
    norm_num at h
  dist_comm x y := by
    by_cases h : x = y
    · rw [h]
    · rw [discreteFn_of_ne h, discreteFn_of_ne (Ne.symm h)]
  dist_triangle x y z := by
    by_cases hxz : x = z
    · rw [hxz, discreteFn_self]
      linarith [discreteFn_nonneg z y, discreteFn_nonneg y z]
    · rw [discreteFn_of_ne hxz]
      by_cases hxy : x = y
      · rw [discreteFn_of_ne (fun h => hxz (hxy.trans h))]
        linarith [discreteFn_nonneg x y]
      · rw [discreteFn_of_ne hxy]
        linarith [discreteFn_nonneg y z]

theorem topology_discreteFn_eq_bot (Z : Type*) :
    (isMetricOn_discreteFn Z).topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  intro u
  refine ⟨1, one_pos, fun v hv => ?_⟩
  by_contra hne
  rw [discreteFn_of_ne hne] at hv
  exact absurd hv (lt_irrefl 1)

/-- The `0/1` metric as a member of the ambient. -/
def CPM.discrete (Z : Type*) : CPM Z :=
  ⟨discreteFn Z, IsMetricOn.toIsPMetricOn (isMetricOn_discreteFn Z)⟩

theorem CPM.discrete_mem_Met (Z : Type*) : CPM.discrete Z ∈ CPM.Met Z :=
  ⟨isMetricOn_discreteFn Z, topology_discreteFn_eq_bot Z⟩

/-- `Met(Z)` is never empty, so neither `component_not_measurableSet` nor its
quotient form below is vacuous. -/
theorem CPM.nonempty_Met (Z : Type*) : (CPM.Met Z).Nonempty :=
  ⟨CPM.discrete Z, CPM.discrete_mem_Met Z⟩

theorem CPM.nonempty_Components (Z : Type*) : Nonempty (CPM.Components Z) :=
  ⟨Quotient.mk (CPM.metSetoid Z) ⟨CPM.discrete Z, CPM.discrete_mem_Met Z⟩⟩

/-! ## An `ℵ₁`-sized closed ball -/

/-- **The uncountable-ball step** (audit §2.7).  For a metric on a carrier of
cardinality `ℵ₁` and any centre, some closed ball of radius at least `1` again
has cardinality `ℵ₁`: the balls of integer radius exhaust the carrier, and a
countable union of countable sets cannot.

Only finiteness of the values of `d z ·` is used, so no metric hypothesis is
imposed; the statement is about the sublevel sets of one real-valued
function. -/
theorem exists_aleph1_ball (hZ : #Z = aleph 1) (d : Z → Z → ℝ)
    (z : Z) : ∃ H : ℝ, 1 ≤ H ∧ #(↥{x : Z | d z x ≤ H}) = aleph 1 := by
  have hexists : ∃ n : ℕ, ¬ ({x : Z | d z x ≤ (n : ℝ)}).Countable := by
    by_contra hall
    push Not at hall
    have hcov : (Set.univ : Set Z) = ⋃ n : ℕ, {x : Z | d z x ≤ (n : ℝ)} := by
      ext x
      simp only [Set.mem_univ, true_iff, Set.mem_iUnion, Set.mem_setOf_eq]
      exact exists_nat_ge (d z x)
    have hcount : (Set.univ : Set Z).Countable := by
      rw [hcov]
      exact Set.countable_iUnion hall
    have hle : #(↥(Set.univ : Set Z)) ≤ Cardinal.aleph0 :=
      Cardinal.le_aleph0_iff_set_countable.mpr hcount
    rw [Cardinal.mk_univ, hZ] at hle
    exact absurd hle (not_le_of_gt Cardinal.aleph0_lt_aleph_one)
  obtain ⟨n, hn⟩ := hexists
  have hge : aleph 1 ≤ #(↥{x : Z | d z x ≤ (n : ℝ)}) := by
    refine Cardinal.aleph_one_le_iff.mpr ?_
    by_contra hcon
    push Not at hcon
    exact hn (Cardinal.le_aleph0_iff_set_countable.mp hcon)
  have hsub : {x : Z | d z x ≤ (n : ℝ)} ⊆ {x : Z | d z x ≤ max (n : ℝ) 1} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact le_trans hx (le_max_left _ _)
  exact ⟨max (n : ℝ) 1, le_max_right _ _,
    le_antisymm ((Cardinal.mk_set_le _).trans_eq hZ)
      (hge.trans (Cardinal.mk_le_mk_of_subset hsub))⟩

/-! ## The coding's anchor gap -/

/-- Every point other than the anchor `p` is at distance at least `1` from
`p` in the star coding: the partner anchor is at distance `1 + t`, and points
of any star at distance `4`.  This is the uniform gap the amalgamation needs
on the `E` side. -/
theorem one_le_dExt_anchor {S : Set ℝ} {t : ℝ} (ht0 : 0 ≤ t) {u : ExtIndex S}
    (hu : u ≠ Sum.inl true) : 1 ≤ dExt S t (Sum.inl true) u := by
  rcases u with b | p
  · cases b
    · rw [dExt_anchor]; linarith
    · exact absurd rfl hu
  · norm_num [dExt]

/-! ## The component construction

All the data of audit §2.7's proof, bundled so that the individual steps can
be stated — and reused by the complete-metric branch — without repeating a
long hypothesis list.  Nothing in the bundle presupposes any part of the
conclusion: the fields are the base metric, a subset `E` trapped between two
`d`-balls around a point `z`, and a relabelling of `E` onto the coded
carrier. -/
structure ComponentSetup (Z : Type*) where
  /-- The parameter set carrying the descriptive-set-theoretic obstruction. -/
  S : Set ℝ
  hS : S ⊆ Set.Icc (0 : ℝ) 1
  /-- The base metric, a representative of the component. -/
  d : Z → Z → ℝ
  hd : IsMetricOn d
  hdbot : hd.topology = ⊥
  /-- The subset carrying the transported coding, and the point it is glued
  along. -/
  E : Set Z
  z : Z
  hz : z ∈ E
  /-- `E` lies in the closed `d`-ball of radius `H` around `z` … -/
  H : ℝ
  hE : ∀ x ∈ E, d z x ≤ H
  /-- … and everything outside `E` is at `d`-distance at least `1` from `z`. -/
  hout : ∀ x ∉ E, 1 ≤ d z x
  /-- The relabelling of `E` onto the coded carrier, sending `z` to the coding's
  anchor. -/
  θ : ↥E ≃ ExtIndex S
  hθz : θ ⟨z, hz⟩ = Sum.inl true

namespace ComponentSetup

variable (c : ComponentSetup Z)

/-- The base metric as a member of the ambient `CPM(Z)`. -/
def base : CPM Z := ⟨c.d, IsMetricOn.toIsPMetricOn c.hd⟩

@[simp] theorem base_val : (c.base).1 = c.d := rfl

/-! ### The coding transported to `E` -/

/-- The star coding of `Ext/BoundedCoding.lean`, relabelled onto `E`. -/
def ballMetric (t : ℝ) : ↥c.E → ↥c.E → ℝ := fun x y => dExt c.S t (c.θ x) (c.θ y)

theorem isMetricOn_ballMetric {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsMetricOn (c.ballMetric t) :=
  isMetricOn_comap c.θ (dExt_isMetricOn c.hS ht)

theorem ballMetric_le_four {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x y : ↥c.E) :
    c.ballMetric t x y ≤ 4 :=
  dExt_le_four c.hS ht _ _

theorem ballMetric_topology_eq_bot {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (htS : t ∉ c.S) :
    (c.isMetricOn_ballMetric ht).topology = ⊥ :=
  topology_comap_eq_bot c.θ (dExt_isMetricOn c.hS ht) (dExt_topology_eq_bot c.hS ht htS)

theorem ballMetric_topology_ne_bot {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (htS : t ∈ c.S)
    (h : IsMetricOn (c.ballMetric t)) : h.topology ≠ ⊥ := fun hbot =>
  dExt_topology_ne_bot c.hS ht htS
    (topology_eq_bot_of_comap (d := dExt c.S t) c.θ h hbot)

/-- The anchor gap, transported: every point of `E` other than `z` is at
`ballMetric`-distance at least `1` from `z`. -/
theorem one_le_ballMetric_base {t : ℝ} (ht0 : 0 ≤ t) (y : ↥c.E) (hy : y ≠ ⟨c.z, c.hz⟩) :
    1 ≤ c.ballMetric t ⟨c.z, c.hz⟩ y := by
  have hne : c.θ y ≠ Sum.inl true := by
    rw [← c.hθz]
    exact fun hcon => hy (c.θ.injective hcon)
  show 1 ≤ dExt c.S t (c.θ ⟨c.z, c.hz⟩) (c.θ y)
  rw [c.hθz]
  exact one_le_dExt_anchor ht0 hne

theorem abs_ballMetric_sub_le (t s : ℝ) (x y : ↥c.E) :
    |c.ballMetric t x y - c.ballMetric s x y| ≤ 2 * |t - s| :=
  dExt_sub_le c.S t s _ _

/-! ### The amalgamated family `Ψ : [0,1] → CPM(Z)` -/

/-- The amalgam `m_t` of the base metric with the transported coding. -/
def metric (t : UnitParam) : Z → Z → ℝ :=
  amalgam c.E c.z c.hz c.d (c.ballMetric (t : ℝ))

theorem isMetricOn_metric (t : UnitParam) : IsMetricOn (c.metric t) :=
  isMetricOn_amalgam c.hz c.hd (c.isMetricOn_ballMetric t.2)

/-- The parameter map `Ψ`. -/
def psi (t : UnitParam) : CPM Z :=
  ⟨c.metric t, IsMetricOn.toIsPMetricOn (c.isMetricOn_metric t)⟩

@[simp] theorem psi_val (t : UnitParam) : (c.psi t).1 = c.metric t := rfl

theorem metric_topology_eq_bot {t : UnitParam} (htS : (t : ℝ) ∉ c.S) :
    (c.isMetricOn_metric t).topology = ⊥ :=
  amalgam_topology_eq_bot c.hz c.hd (c.isMetricOn_ballMetric t.2) c.hdbot
    (c.ballMetric_topology_eq_bot t.2 htS) one_pos
    (fun y hy => c.one_le_ballMetric_base t.2.1 y hy) c.hout

/-- **Audit §2.7 (ii), first half.**  `m_t` is compatible with the discrete
topology exactly when `t ∉ S`.  The failure at `t ∈ S` comes from the `E`
side, where `m_t` restricts to the coding. -/
theorem mem_Met_psi_iff (t : UnitParam) : c.psi t ∈ CPM.Met Z ↔ (t : ℝ) ∉ c.S := by
  constructor
  · rintro ⟨h, hbot⟩ htS
    exact c.ballMetric_topology_ne_bot t.2 htS (c.isMetricOn_ballMetric t.2)
      (topology_eq_bot_of_amalgam (d := c.d) c.hz (c.isMetricOn_ballMetric t.2) h hbot)
  · intro htS
    exact ⟨c.isMetricOn_metric t, c.metric_topology_eq_bot htS⟩

/-! ### Finite distance from the base metric (audit §2.7 (i)) -/

theorem abs_metric_sub_base_le (t : UnitParam) (x y : Z) :
    |c.metric t x y - c.d x y| ≤ 4 + 2 * c.H :=
  abs_amalgam_sub_le c.hz c.hd (c.isMetricOn_ballMetric t.2)
    (c.ballMetric_le_four t.2) c.hE x y

/-- The explicit quantitative bound: `𝒟_Z(m_t, d) ≤ 4 + 2H`, where `4` bounds
the coding and `H` is the radius of the ball carrying it. -/
theorem edist_psi_base_le (t : UnitParam) :
    CPM.edist (c.psi t) c.base ≤ ENNReal.ofReal (4 + 2 * c.H) :=
  CPM.edist_le_ofReal (c.abs_metric_sub_base_le t)

theorem edist_psi_base_lt_top (t : UnitParam) : CPM.edist (c.psi t) c.base < ⊤ :=
  lt_of_le_of_lt (c.edist_psi_base_le t) ENNReal.ofReal_lt_top

/-! ### The parameter map is Lipschitz -/

theorem lipschitzWith_psi : LipschitzWith 2 c.psi := by
  intro t s
  have hk : (0 : ℝ) ≤ 2 * |(t : ℝ) - (s : ℝ)| := by positivity
  have hbound : ∀ x y : Z, |(c.psi t).1 x y - (c.psi s).1 x y| ≤ 2 * |(t : ℝ) - (s : ℝ)| :=
    fun x y => abs_amalgam_sub_amalgam_le c.hz c.d hk
      (fun u v => c.abs_ballMetric_sub_le (t : ℝ) (s : ℝ) u v) x y
  have hcoe : ((2 : NNReal) : ℝ≥0∞) * edist t s = ENNReal.ofReal (2 * |(t : ℝ) - (s : ℝ)|) := by
    rw [edist_dist, Subtype.dist_eq, Real.dist_eq,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  rw [hcoe]
  exact CPM.edist_le_ofReal hbound

theorem continuous_psi : Continuous c.psi := c.lipschitzWith_psi.continuous

theorem measurable_psi : Measurable c.psi := c.continuous_psi.measurable

/-! ### The trace identity and the obstruction -/

/-- **Audit §2.7 (ii), second half — the exact pullback identity.**
`Ψ⁻¹(𝔠) = {t ∈ [0,1] : t ∉ S}`: membership in the component is equivalent to
compatibility, because the finite-distance clause holds for *every*
parameter. -/
theorem preimage_component_psi :
    c.psi ⁻¹' CPM.component c.base = {t : UnitParam | (t : ℝ) ∉ c.S} := by
  ext t
  constructor
  · rintro ⟨hmet, -⟩
    exact (c.mem_Met_psi_iff t).mp hmet
  · intro htS
    refine ⟨(c.mem_Met_psi_iff t).mpr htS, ?_⟩
    rw [CPM.edist_comm]
    exact c.edist_psi_base_lt_top t

/-- The compact witness `L' = Ψ([0,1])` of audit §2.7. -/
theorem isCompact_range_psi : IsCompact (Set.range c.psi) :=
  isCompact_range c.continuous_psi

/-- **The compact-witness trace identity** `L' ∩ 𝔠 = Ψ([0,1] ∖ S)`. -/
theorem range_inter_component :
    Set.range c.psi ∩ CPM.component c.base = c.psi '' {t : UnitParam | (t : ℝ) ∉ c.S} := by
  rw [← c.preimage_component_psi, Set.image_preimage_eq_inter_range, Set.inter_comm]

end ComponentSetup

/-- Pushing a parameter subset of `[0,1]` forward into `ℝ` turns the pullback
identity into the statement that `S` itself is Borel. -/
theorem measurableSet_of_measurableSet_image {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (h : MeasurableSet (Subtype.val '' {t : UnitParam | (t : ℝ) ∉ S})) : MeasurableSet S := by
  have himage_eq :
      Subtype.val '' {t : UnitParam | (t : ℝ) ∉ S} = Set.Icc (0 : ℝ) 1 \ S := by
    ext x
    constructor
    · rintro ⟨t, htS, rfl⟩
      exact ⟨t.2, htS⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, hx2, rfl⟩
  rw [himage_eq] at h
  have heq : S = Set.Icc (0 : ℝ) 1 \ (Set.Icc (0 : ℝ) 1 \ S) := by
    ext x
    constructor
    · intro hx
      exact ⟨hS hx, fun hx' => hx'.2 hx⟩
    · intro hx
      by_contra hxn
      exact hx.2 ⟨hx.1, hxn⟩
  rw [heq]
  exact measurableSet_Icc.diff h

namespace ComponentSetup

variable (c : ComponentSetup Z)

/-- The obstruction for one setup: if the parameter set is non-Borel then so
is the component of the base metric. -/
theorem not_measurableSet_component (hSnonmeas : ¬ MeasurableSet c.S) :
    ¬ MeasurableSet (CPM.component c.base) := by
  intro hmeas
  have hpre : MeasurableSet (c.psi ⁻¹' CPM.component c.base) :=
    hmeas.preimage c.measurable_psi
  rw [c.preimage_component_psi] at hpre
  exact hSnonmeas
    (measurableSet_of_measurableSet_image c.hS (measurableSet_Icc.subtype_image hpre))

end ComponentSetup

/-! ## Theorem 3.4 -/

/-- **Theorem 3.4** (audit §2.7), in the form "every representative determines
a non-Borel component".  For a discrete carrier `Z` with `|Z| = ℵ₁` and any
`d ∈ Met(Z)`, the set of compatible metrics at finite supremum distance from
`d` is not Borel in `CPM(Z)`.

As in `met_not_borel_of_card`, discreteness of `Z` is carried by the
membership condition itself (`Met(Z)` consists of the metrics inducing the
discrete topology), so no topology on `Z` appears; and no hypothesis on a
parameter set is left in the statement, the non-Borel `S ⊆ [0,1]` being
produced internally by `exists_aleph1_nonBorel`. -/
theorem component_not_measurableSet (hZ : #Z = aleph 1) (d : CPM Z)
    (hd : d ∈ CPM.Met Z) : ¬ MeasurableSet (CPM.component d) := by
  obtain ⟨hdm, hdbot⟩ := hd
  have hpos : (0 : Cardinal) < #Z := by
    rw [hZ]
    exact lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_aleph 1)
  obtain ⟨z⟩ : Nonempty Z := Cardinal.mk_ne_zero_iff.mp hpos.ne'
  obtain ⟨H, hH1, hHcard⟩ := exists_aleph1_ball hZ d.1 z
  have hzE : z ∈ {x : Z | d.1 z x ≤ H} := by
    show d.1 z z ≤ H
    rw [hdm.dist_self]
    linarith
  obtain ⟨S, hSsub, -, hSnonmeas, ⟨σ⟩⟩ := exists_equiv_extIndex_of_card hHcard
  let c : ComponentSetup Z :=
    { S := S
      hS := hSsub
      d := d.1
      hd := hdm
      hdbot := hdbot
      E := {x : Z | d.1 z x ≤ H}
      z := z
      hz := hzE
      H := H
      hE := fun _ hx => hx
      hout := fun x hx => by
        have hgt : H < d.1 z x := not_le.mp hx
        linarith
      θ := σ.trans (Equiv.swap (σ ⟨z, hzE⟩) (Sum.inl true))
      hθz := by simp }
  have hbase : c.base = d := Subtype.ext rfl
  rw [← hbase]
  exact c.not_measurableSet_component hSnonmeas

/-- **Theorem 3.4, literally.**  For a discrete carrier `Z` with `|Z| = ℵ₁`,
*every* component `𝔠 ∈ 𝐌_{<∞}(Z)` is non-Borel in `CPM(Z)`, the component
being read as a subset of the ambient. -/
theorem componentSet_not_measurableSet (hZ : #Z = aleph 1) (comp : CPM.Components Z) :
    ¬ MeasurableSet (CPM.componentSet comp) := by
  refine Quotient.inductionOn comp fun d => ?_
  rw [CPM.componentSet_mk]
  exact component_not_measurableSet hZ d.1 d.2

end
end IshikiExt
