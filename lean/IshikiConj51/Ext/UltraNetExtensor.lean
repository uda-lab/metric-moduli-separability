-- Ext.UltraNetExtensor
--
-- Issue #132 / `lem:ultrametric-extensor-preserving-component` (4.5 of the
-- 2026-11-03 received source).
-- Statement gate: `notes/borel-manuscript-20261103-audit.md` §2.2 (the audit
-- observation on 4.5: the elementary extensor `E′`) and §4 (E2c′); bare
-- "audit §" references below are to that note.
--
-- This module discharges the E2c hypothesis `hEx` of
-- `Ext/UltraComponentGeneral.lean` with no external input.  For a compatible
-- `R`-valued ultrametric `d`, a nonzero `a ∈ R` and a maximal `a`-separated
-- `A` with centre map `π`, put
--
--   v′(x,y)   = d(x,y)              if π x = π y,
--             = ρ(x) ∨ ρ(y)         otherwise,       ρ(x) = d(x, π x),
--   E′(w)(x,y) = w(π x, π y) ∨ v′(x,y).
--
-- `E′(w)` is an `R`-valued ultrametric inducing the topology of `Y` whenever
-- `w ∈ UMet(A;R)`; `E′(w)|_{A²} = w`; `E′` preserves the admissible tolerances
-- exactly, so it is a `𝒰𝒟^R`-isometry; and `E′(d|_{A²}) = d`, so the
-- component bound of 4.5 holds with `τ = 0`.  No metric quotient, no
-- zero-dimensionality and none of Ishiki's Propositions 2.3/2.6/2.8 (E2c′) is
-- used.
--
-- `IsUltraComponentControlledExtensorOn` and the `hEx`-taking theorems of
-- `Ext/UltraComponentGeneral.lean` are unchanged; this file supplies `hEx` and
-- restates their four consumers without it.  The restatements are stronger
-- than the printed dependency of 4.6–4.8 on E2c′ (audit §7.1).
--
-- Public declarations:
--   * `centre_eq_of_dist_lt`, `centre_eq_iff`, `dist_eq_centre_of_ne`,
--     `centreMap_dist_lt`
--   * `netPMet` (`v′`), `netExtend` (`E′`) and their API
--   * `netExtensor`, `netExtensor_toUCPMOn_val`, `netExtensor_toUCPMOn_restrict`
--   * `exists_isUltraComponentControlledExtensorOn`
--   * `not_measurableSet_UCPMOn_component`, `not_measurableSet_UMetOn`,
--     `separable_of_measurableSet_UMetOn`,
--     `separable_of_isCompletelyMetrizableSpace_UMetOn`

import IshikiConj51.Ext.UltraComponentGeneral

open Set
open scoped ENNReal Topology

namespace IshikiExt

noncomputable section

variable {R : RangeSet}

attribute [local instance] ucpmOnMeasurableSpace ucpmOnBorelSpace

/-! ## The centre of a point -/

section Centre

variable {Y : Type*} {A : Set Y} {a : ℝ}

/-- **Uniqueness of the centre.** A point of `A` within `a` of `x` is the
centre of `x`, by the `a`-separation of `A`. -/
theorem centre_eq_of_dist_lt {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    {x : Y} {b : ↥A} (h : d.1 x b < a) : π x = b := by
  by_contra hne
  have hlt : d.1 (π x) b < a :=
    lt_of_le_of_lt (d.2.dist_triangle_max _ x _)
      (max_lt (by rw [d.2.dist_comm]; exact hπ x) h)
  exact (not_le.mpr hlt) (hAsep (π x).2 b.2 fun h' => hne (Subtype.ext h'))

/-- Points of `A` are their own centres. -/
theorem centre_apply_coe {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    (b : ↥A) : π b = b :=
  centre_eq_of_dist_lt hAsep hπ (by
    rw [d.2.dist_self]
    exact lt_of_le_of_lt (d.nonneg _ _) (hπ b))

/-- Two points share a centre exactly when they are within `a`. -/
theorem centre_eq_iff {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    {x y : Y} : π x = π y ↔ d.1 x y < a := by
  constructor
  · intro h
    refine lt_of_le_of_lt (d.2.dist_triangle_max x (π x) y) (max_lt (hπ x) ?_)
    rw [h, d.2.dist_comm]
    exact hπ y
  · intro h
    refine (centre_eq_of_dist_lt hAsep hπ ?_).symm
    refine lt_of_le_of_lt (d.2.dist_triangle_max y x _) (max_lt ?_ (hπ x))
    rw [d.2.dist_comm]
    exact h

/-- **Across two centre classes** `d` is the distance of the centres, and both
radii `ρ` are strictly below it (isosceles property). -/
theorem dist_eq_centre_of_ne {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    {x y : Y} (h : π x ≠ π y) :
    d.1 x y = d.1 (π x) (π y) ∧
      max (d.1 x (π x)) (d.1 y (π y)) < d.1 (π x) (π y) := by
  have hsep : a ≤ d.1 (π x) (π y) :=
    hAsep (π x).2 (π y).2 fun h' => h (Subtype.ext h')
  have hx : d.1 x (π x) < d.1 (π x) (π y) := lt_of_lt_of_le (hπ x) hsep
  have hy : d.1 y (π y) < d.1 (π x) (π y) := lt_of_lt_of_le (hπ y) hsep
  refine ⟨le_antisymm ?_ ?_, max_lt hx hy⟩
  · calc d.1 x y ≤ max (d.1 x (π x)) (d.1 (π x) y) := d.2.dist_triangle_max _ _ _
      _ ≤ max (d.1 x (π x)) (max (d.1 (π x) (π y)) (d.1 (π y) y)) :=
          max_le_max le_rfl (d.2.dist_triangle_max _ _ _)
      _ ≤ d.1 (π x) (π y) := by
          rw [d.2.dist_comm (π y : Y) y]
          exact max_le hx.le (max_le le_rfl hy.le)
  · by_contra hlt
    push Not at hlt
    have hle : d.1 (π x) (π y) ≤ max (d.1 (π x) x) (max (d.1 x y) (d.1 y (π y))) :=
      (d.2.dist_triangle_max _ x _).trans (max_le_max le_rfl (d.2.dist_triangle_max _ _ _))
    rw [d.2.dist_comm (π x : Y) x] at hle
    exact absurd hle (not_le.mpr (max_lt hx (max_lt hlt hy)))

end Centre

/-! ## The net pseudo-ultrametric `v′` -/

section NetPMet

variable {Y : Type*} {A : Set Y}

open Classical in
/-- The underlying function of `v′`: `d` inside a centre class and the larger
of the two radii `ρ(x) = d(x, π x)`, `ρ(y)` across classes. -/
def netPMetFun (d : UCPM Y R) (π : Y → ↥A) (x y : Y) : ℝ :=
  if π x = π y then d.1 x y else max (d.1 x (π x)) (d.1 y (π y))

theorem netPMetFun_of_eq {d : UCPM Y R} {π : Y → ↥A} {x y : Y} (h : π x = π y) :
    netPMetFun d π x y = d.1 x y := by
  unfold netPMetFun
  exact if_pos h

theorem netPMetFun_of_ne {d : UCPM Y R} {π : Y → ↥A} {x y : Y} (h : π x ≠ π y) :
    netPMetFun d π x y = max (d.1 x (π x)) (d.1 y (π y)) := by
  unfold netPMetFun
  exact if_neg h

/-- `v′` is an `R`-valued pseudo-ultrametric for an arbitrary map `π`; no
property of the net is needed. -/
theorem isUltraPMetOn_netPMetFun (d : UCPM Y R) (π : Y → ↥A) :
    IsUltraPMetOn R (netPMetFun d π) where
  dist_self x := by rw [netPMetFun_of_eq rfl, d.2.dist_self]
  dist_comm x y := by
    by_cases h : π x = π y
    · rw [netPMetFun_of_eq h, netPMetFun_of_eq h.symm, d.2.dist_comm]
    · rw [netPMetFun_of_ne h, netPMetFun_of_ne (Ne.symm h), max_comm]
  dist_triangle_max x y z := by
    by_cases hxz : π x = π z
    · rw [netPMetFun_of_eq hxz]
      by_cases hxy : π x = π y
      · rw [netPMetFun_of_eq hxy, netPMetFun_of_eq (hxy.symm.trans hxz)]
        exact d.2.dist_triangle_max x y z
      · have hyz : π y ≠ π z := fun h => hxy (hxz.trans h.symm)
        rw [netPMetFun_of_ne hxy, netPMetFun_of_ne hyz]
        have h1 : d.1 x z ≤ max (d.1 x (π x)) (d.1 z (π z)) := by
          calc d.1 x z ≤ max (d.1 x (π x)) (d.1 (π x) z) := d.2.dist_triangle_max _ _ _
            _ = max (d.1 x (π x)) (d.1 z (π z)) := by
                rw [hxz, d.2.dist_comm (π z : Y) z]
        exact h1.trans (max_le_max (le_max_left _ _) (le_max_right _ _))
    · rw [netPMetFun_of_ne hxz]
      by_cases hxy : π x = π y
      · have hyz : π y ≠ π z := fun h => hxz (hxy.trans h)
        rw [netPMetFun_of_eq hxy, netPMetFun_of_ne hyz]
        have h1 : d.1 x (π x) ≤ max (d.1 x y) (d.1 y (π y)) := by
          rw [hxy]
          exact d.2.dist_triangle_max _ _ _
        exact max_le (h1.trans (max_le_max le_rfl (le_max_left _ _)))
          ((le_max_right _ _).trans (le_max_right _ _))
      · by_cases hyz : π y = π z
        · rw [netPMetFun_of_ne hxy, netPMetFun_of_eq hyz]
          have h1 : d.1 z (π z) ≤ max (d.1 y z) (d.1 y (π y)) := by
            rw [← hyz, d.2.dist_comm y z]
            exact d.2.dist_triangle_max _ _ _
          refine max_le ((le_max_left _ _).trans (le_max_left _ _)) (h1.trans ?_)
          exact max_le (le_max_right _ _) ((le_max_right _ _).trans (le_max_left _ _))
        · rw [netPMetFun_of_ne hxy, netPMetFun_of_ne hyz]
          exact max_le ((le_max_left _ _).trans (le_max_left _ _))
            ((le_max_right _ _).trans (le_max_right _ _))
  mem_range x y := by
    by_cases h : π x = π y
    · rw [netPMetFun_of_eq h]
      exact d.2.mem_range x y
    · rw [netPMetFun_of_ne h]
      exact R.max_mem (d.2.mem_range _ _) (d.2.mem_range _ _)

/-- The net pseudo-ultrametric `v′` of audit §2.2. -/
def netPMet (d : UCPM Y R) (π : Y → ↥A) : UCPM Y R :=
  ⟨netPMetFun d π, isUltraPMetOn_netPMetFun d π⟩

/-- With the centre properties, `v′ = min d (ρ x ∨ ρ y)`: the closed form
used for continuity. -/
theorem netPMetFun_eq_min {a : ℝ} {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    (x y : Y) :
    netPMetFun d π x y = min (d.1 x y) (max (d.1 x (π x)) (d.1 y (π y))) := by
  by_cases h : π x = π y
  · rw [netPMetFun_of_eq h]
    refine (min_eq_left ?_).symm
    calc d.1 x y ≤ max (d.1 x (π x)) (d.1 (π x) y) := d.2.dist_triangle_max _ _ _
      _ = max (d.1 x (π x)) (d.1 y (π y)) := by rw [h, d.2.dist_comm (π y : Y) y]
  · obtain ⟨heq, hlt⟩ := dist_eq_centre_of_ne hAsep hπ h
    rw [netPMetFun_of_ne h]
    refine (min_eq_right ?_).symm
    rw [heq]
    exact hlt.le

end NetPMet

/-! ## The extension `E′(w) = w(π ·, π ·) ∨ v′` -/

section NetExtend

variable {Y : Type*} {A : Set Y}

/-- The extension `E′(w)(x,y) = w(π x, π y) ∨ v′(x,y)` of audit §2.2, at the
level of `R`-valued pseudo-ultrametrics. -/
def netExtend (d : UCPM Y R) (π : Y → ↥A) (w : UCPM ↥A R) : UCPM Y R :=
  UCPM.sup (UCPM.comap π w) (netPMet d π)

theorem netExtend_apply (d : UCPM Y R) (π : Y → ↥A) (w : UCPM ↥A R) (x y : Y) :
    (netExtend d π w).1 x y = max (w.1 (π x) (π y)) (netPMetFun d π x y) := rfl

/-- Inside a centre class `E′(w)` is `d`. -/
theorem netExtend_apply_of_eq (d : UCPM Y R) {π : Y → ↥A} (w : UCPM ↥A R)
    {x y : Y} (h : π x = π y) : (netExtend d π w).1 x y = d.1 x y := by
  rw [netExtend_apply, netPMetFun_of_eq h, h, w.2.dist_self]
  exact max_eq_right (d.nonneg x y)

variable {a : ℝ}

/-- **Extension.** `E′(w)|_{A²} = w`. -/
theorem netExtend_apply_coe {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    (w : UCPM ↥A R) (b c : ↥A) : (netExtend d π w).1 b c = w.1 b c := by
  have hb := centre_apply_coe hAsep hπ b
  have hc := centre_apply_coe hAsep hπ c
  have hv : netPMetFun d π b c = 0 := by
    by_cases h : π b = π c
    · rw [netPMetFun_of_eq h]
      rw [hb, hc] at h
      rw [h, d.2.dist_self]
    · rw [netPMetFun_of_ne h, hb, hc, d.2.dist_self, d.2.dist_self, max_self]
  rw [netExtend_apply, hv, hb, hc]
  exact max_eq_left (w.nonneg b c)

theorem comap_netExtend {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    (w : UCPM ↥A R) : UCPM.comap (Subtype.val : ↥A → Y) (netExtend d π w) = w :=
  Subtype.ext (funext fun b => funext fun c => netExtend_apply_coe hAsep hπ w b c)

/-- **Isometry, tolerance form.** An `ε ∈ R` is admissible for
`(E′ w₁, E′ w₂)` exactly when it is admissible for `(w₁, w₂)`. -/
theorem tolerances_netExtend {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    (w₁ w₂ : UCPM ↥A R) :
    UCPM.tolerances (netExtend d π w₁) (netExtend d π w₂) = UCPM.tolerances w₁ w₂ := by
  apply Set.Subset.antisymm
  · intro r hr
    have h := UCPM.tolerances_subset_comap (Subtype.val : ↥A → Y) _ _ hr
    rwa [comap_netExtend hAsep hπ, comap_netExtend hAsep hπ] at h
  · intro r hr
    refine ⟨hr.1, fun x y => ⟨?_, ?_⟩⟩
    · rw [netExtend_apply, netExtend_apply]
      refine max_le ((hr.2 (π x) (π y)).1.trans ?_) ?_
      · exact max_le_max (le_max_left _ _) le_rfl
      · exact (le_max_right _ _).trans (le_max_left _ _)
    · rw [netExtend_apply, netExtend_apply]
      refine max_le ((hr.2 (π x) (π y)).2.trans ?_) ?_
      · exact max_le_max (le_max_left _ _) le_rfl
      · exact (le_max_right _ _).trans (le_max_left _ _)

/-- **Isometry.** `𝒰𝒟^R_Y(E′ w₁, E′ w₂) = 𝒰𝒟^R_A(w₁, w₂)`. -/
theorem edist_netExtend {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a)
    (w₁ w₂ : UCPM ↥A R) :
    UCPM.edist (netExtend d π w₁) (netExtend d π w₂) = UCPM.edist w₁ w₂ := by
  rw [UCPM.edist, UCPM.edist, tolerances_netExtend hAsep hπ]

/-- **Exact recovery.** `E′(d|_{A²}) = d`: across two centre classes the
isosceles property gives `d(x,y) = d(π x, π y) > ρ(x) ∨ ρ(y)`. -/
theorem netExtend_comap_self {d : UCPM Y R} {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1 x y) (hπ : ∀ x, d.1 x (π x) < a) :
    netExtend d π (UCPM.comap (Subtype.val : ↥A → Y) d) = d := by
  refine Subtype.ext (funext fun x => funext fun y => ?_)
  change max (d.1 (π x) (π y)) (netPMetFun d π x y) = d.1 x y
  by_cases h : π x = π y
  · rw [netPMetFun_of_eq h, h, d.2.dist_self]
    exact max_eq_right (d.nonneg x y)
  · obtain ⟨heq, hlt⟩ := dist_eq_centre_of_ne hAsep hπ h
    rw [netPMetFun_of_ne h, max_eq_left hlt.le, heq]

end NetExtend

/-! ## Continuity and compatibility on a topological space -/

section Topology

variable {Y : Type*} [TopologicalSpace Y] {A : Set Y} {a : ℝ}

/-- `E′(w)` is continuous on `Y × Y` for every `w`: the `w`-term factors
through the continuous centre map into the discrete `A × A`, and `v′` is
`min d (ρ x ∨ ρ y)`. -/
theorem continuous_netExtend [DiscreteTopology ↥A] (d : UCPMOn Y R) {π : Y → ↥A}
    (hAsep : A.Pairwise fun x y => a ≤ d.1.1 x y) (hπ : ∀ x, d.1.1 x (π x) < a)
    (hπc : Continuous π) (w : UCPM ↥A R) :
    Continuous (Function.uncurry (netExtend d.1 π w).1) := by
  have hρ : Continuous fun x : Y => d.1.1 x (π x) :=
    d.2.comp (continuous_id.prodMk (continuous_subtype_val.comp hπc))
  have hw : Continuous fun p : Y × Y => w.1 (π p.1) (π p.2) :=
    (continuous_of_discreteTopology (f := Function.uncurry w.1)).comp
      ((hπc.comp continuous_fst).prodMk (hπc.comp continuous_snd))
  have hv : Continuous fun p : Y × Y => netPMetFun d.1 π p.1 p.2 := by
    have hfun : (fun p : Y × Y => netPMetFun d.1 π p.1 p.2) = fun p =>
        min (d.1.1 p.1 p.2) (max (d.1.1 p.1 (π p.1)) (d.1.1 p.2 (π p.2))) :=
      funext fun p => netPMetFun_eq_min hAsep hπ p.1 p.2
    rw [hfun]
    exact d.2.min ((hρ.comp continuous_fst).max (hρ.comp continuous_snd))
  exact hw.max hv

/-- **Compatibility.** For `w ∈ UMet(A;R)`, `E′(w)` is a metric inducing the
topology of `Y`: within `a` it agrees with `d`, and `E′(w)(x, y) < η` forces
`π x = π y` once `η` isolates `π y` for `w`. -/
theorem exists_isMetricOn_netExtend {d : UCPMOn Y R} (hd : d ∈ UMetOn Y R) (ha : 0 < a)
    {π : Y → ↥A} (hAsep : A.Pairwise fun x y => a ≤ d.1.1 x y)
    (hπ : ∀ x, d.1.1 x (π x) < a) {w : UCPM ↥A R} (hw : w ∈ UMet ↥A R) :
    ∃ h : IsMetricOn (netExtend d.1 π w).1,
      h.topology = (inferInstance : TopologicalSpace Y) := by
  obtain ⟨hm, htop⟩ := hd
  obtain ⟨hwm, hwtop⟩ := hw
  have hE : IsMetricOn (netExtend d.1 π w).1 := by
    refine (netExtend d.1 π w).2.toIsMetricOn fun x y hxy => ?_
    rw [netExtend_apply] at hxy
    by_cases h : π x = π y
    · rw [netPMetFun_of_eq h] at hxy
      exact hm.eq_of_dist_eq_zero
        (le_antisymm ((le_max_right _ _).trans hxy.le) (d.1.nonneg x y))
    · exact absurd (hwm.eq_of_dist_eq_zero
        (le_antisymm ((le_max_left _ _).trans hxy.le) (w.nonneg _ _))) h
  refine ⟨hE, ?_⟩
  rw [← htop]
  have hforward : @Continuous Y Y hm.topology hE.topology id := by
    rw [hm.topology_eq_metricSpace_topology, hE.topology_eq_metricSpace_topology]
    refine (@Metric.continuous_iff Y Y
      hm.toMetricSpace.toPseudoMetricSpace
      hE.toMetricSpace.toPseudoMetricSpace id).2 ?_
    intro b ε hε
    refine ⟨min ε a, lt_min hε ha, fun x hx => ?_⟩
    have hx' : d.1.1 x b < min ε a := hx
    show (netExtend d.1 π w).1 x b < ε
    rw [netExtend_apply_of_eq d.1 w
      ((centre_eq_iff hAsep hπ).2 (lt_of_lt_of_le hx' (min_le_right _ _)))]
    exact lt_of_lt_of_le hx' (min_le_left _ _)
  have hbackward : @Continuous Y Y hE.topology hm.topology id := by
    rw [hE.topology_eq_metricSpace_topology, hm.topology_eq_metricSpace_topology]
    refine (@Metric.continuous_iff Y Y
      hE.toMetricSpace.toPseudoMetricSpace
      hm.toMetricSpace.toPseudoMetricSpace id).2 ?_
    intro b ε hε
    obtain ⟨η, hη, hηiso⟩ := (hwm.topology_eq_bot_iff.mp hwtop) (π b)
    refine ⟨min ε η, lt_min hε hη, fun x hx => ?_⟩
    have hx' : (netExtend d.1 π w).1 x b < min ε η := hx
    have hwx : w.1 (π x) (π b) < η := by
      have := lt_of_lt_of_le hx' (min_le_right _ _)
      rw [netExtend_apply] at this
      exact lt_of_le_of_lt (le_max_left _ _) this
    rw [netExtend_apply_of_eq d.1 w (hηiso (π x) hwx)] at hx'
    show d.1.1 x b < ε
    exact lt_of_lt_of_le hx' (min_le_left _ _)
  exact le_antisymm (continuous_id_iff_le.mp hbackward) (continuous_id_iff_le.mp hforward)

/-- Every point is strictly within `a` of its chosen centre. -/
theorem centreMap_dist_lt (d : UCPMOn Y R) (A : Set Y)
    (hnet : ∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a) (ha : 0 < a) (x : Y) :
    d.1.1 x (centreMap d a A hnet x : Y) < a := by
  classical
  by_cases hx : x ∈ A
  · rw [centreMap, dif_pos hx, d.1.2.dist_self]
    exact ha
  · rw [centreMap, dif_neg hx]
    exact (Classical.choose_spec (hnet x hx)).2

/-! ## The isometric extensor of 4.5 -/

/-- **The isometric extensor `E′ : UMet(A;R) → UMet(Y;R)` of
`lem:ultrametric-extensor-preserving-component`**, in the E2 interface
`IsUltraIsometricExtensor`, along the centre map of a maximal `a`-separated
closed discrete `A`. -/
def netExtensor (d : UCPMOn Y R) (hd : d ∈ UMetOn Y R) (ha : 0 < a)
    (hAclosed : IsClosed A) [DiscreteTopology ↥A]
    (hAsep : A.Pairwise fun x y => a ≤ d.1.1 x y)
    (hnet : ∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a) :
    IsUltraIsometricExtensor (⊥ : TopologicalSpace ↥A) R (Subtype.val : ↥A → Y) where
  closedEmbedding := by
    have h := hAclosed.isClosedEmbedding_subtypeVal
    rwa [DiscreteTopology.eq_bot (α := ↥A)] at h
  domain_discrete := rfl
  toUCPMOn u :=
    ⟨netExtend d.1 (centreMap d a A hnet) u.1,
      continuous_netExtend d hAsep (centreMap_dist_lt d A hnet ha)
        (continuous_centreMap d hd a A ha hAsep hnet) u.1⟩
  extension u b c :=
    netExtend_apply_coe (d := d.1) hAsep (centreMap_dist_lt d A hnet ha) u.1 b c
  isometry_toUCPMOn u v := by
    show UCPM.edist _ _ = UCPM.edist u.1 v.1
    exact edist_netExtend (d := d.1) hAsep (centreMap_dist_lt d A hnet ha) u.1 v.1
  umet_preservation u :=
    exists_isMetricOn_netExtend hd ha hAsep (centreMap_dist_lt d A hnet ha) u.2

theorem netExtensor_toUCPMOn_val (d : UCPMOn Y R) (hd : d ∈ UMetOn Y R) (ha : 0 < a)
    (hAclosed : IsClosed A) [DiscreteTopology ↥A]
    (hAsep : A.Pairwise fun x y => a ≤ d.1.1 x y)
    (hnet : ∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a) (u : ↥(UMet ↥A R)) :
    ((netExtensor d hd ha hAclosed hAsep hnet).toUCPMOn u).1 =
      netExtend d.1 (centreMap d a A hnet) u.1 := rfl

/-- **The component bound of 4.5 with `τ = 0`.** The extensor returns `d`
itself from `d|_{A²}`. -/
theorem netExtensor_toUCPMOn_restrict (d : UCPMOn Y R) (hd : d ∈ UMetOn Y R) (ha : 0 < a)
    (hAclosed : IsClosed A) [DiscreteTopology ↥A]
    (hAsep : A.Pairwise fun x y => a ≤ d.1.1 x y)
    (hnet : ∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a)
    (hdA : UCPMOn.restrict (Subtype.val : ↥A → Y) d ∈ UMet ↥A R) :
    (netExtensor d hd ha hAclosed hAsep hnet).toUCPMOn
      ⟨UCPMOn.restrict (Subtype.val : ↥A → Y) d, hdA⟩ = d :=
  Subtype.ext (netExtend_comap_self (d := d.1) hAsep (centreMap_dist_lt d A hnet ha))

end Topology

/-- **`lem:ultrametric-extensor-preserving-component` (4.5), E2c form.**
The hypotheses are exactly the premises of the E2c provider `hEx` of
`Ext/UltraComponentGeneral.lean`, so this theorem *is* `hEx`; it needs no
external input.  Nonemptiness of `A` is part of that interface but is not
used. -/
theorem exists_isUltraComponentControlledExtensorOn
    {Y : Type*} [TopologicalSpace Y]
    (d : UCPMOn Y R) (hd : d ∈ UMetOn Y R)
    (a : ℝ) (haR : a ∈ R.carrier) (ha0 : a ≠ 0)
    (A : Set Y) (_hAne : A.Nonempty) (hAclosed : IsClosed A)
    (hAdisc : DiscreteTopology ↥A)
    (hAsep : A.Pairwise (fun x y => a ≤ d.1.1 x y))
    (hnet : ∀ x : Y, x ∉ A → ∃ y ∈ A, d.1.1 x y < a) :
    Nonempty (IsUltraComponentControlledExtensorOn R A d a) := by
  have ha : 0 < a := lt_of_le_of_ne (R.nonneg haR) (Ne.symm ha0)
  haveI := hAdisc
  refine ⟨⟨netExtensor d hd ha hAclosed hAsep hnet, fun _ => ?_⟩⟩
  rw [netExtensor_toUCPMOn_restrict, edist_self]
  exact ENNReal.zero_lt_top

/-! ## The E2c consumers without `hEx` -/

/-- **`cor:nonseparable-ultrametric-nonborel` (4.6), component clause**, with
no extensor hypothesis: for ultrametrizable nonseparable `Y` and
characteristic `R`, every finite-distance component of `UMet(Y;R)` is
non-Borel in `UCPM(Y;R)`. -/
theorem not_measurableSet_UCPMOn_component
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y)
    (hYsep : ¬ TopologicalSpace.SeparableSpace Y)
    (hR : R.IsCharacteristic) :
    ∀ d ∈ UMetOn Y R, ¬ MeasurableSet (UCPMOn.component R d) :=
  not_measurableSet_UCPMOn_component_of_isUltraComponentControlledExtensorOn
    hY hYsep hR exists_isUltraComponentControlledExtensorOn

/-- **`cor:nonseparable-ultrametric-nonborel` (4.6), whole-locus clause**, with
no extensor hypothesis: `UMet(Y;R)` is non-Borel in `UCPM(Y;R)`. -/
theorem not_measurableSet_UMetOn
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y)
    (hYsep : ¬ TopologicalSpace.SeparableSpace Y)
    (hR : R.IsCharacteristic) :
    ¬ MeasurableSet (UMetOn Y R) :=
  not_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn
    hY hYsep hR exists_isUltraComponentControlledExtensorOn

/-- **`thm:ultrametric-borel-separability` (4.7)**, with no extensor
hypothesis: if `UMet(Y;R)` is Borel in `UCPM(Y;R)`, then `Y` is separable. -/
theorem separable_of_measurableSet_UMetOn
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y)
    (hR : R.IsCharacteristic) :
    MeasurableSet (UMetOn Y R) → TopologicalSpace.SeparableSpace Y :=
  separable_of_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn
    hY hR exists_isUltraComponentControlledExtensorOn

/-- **`cor:ultrametric-space-complete-separability` (4.8)**, with no extensor
hypothesis.  The Borelness step is the forward direction of E4d
(Alexandrov–Lavrentiev), proved as `measurableSet_of_isCompletelyMetrizableSpace`. -/
theorem separable_of_isCompletelyMetrizableSpace_UMetOn
    {Y : Type*} [TopologicalSpace Y]
    (hY : IsUltrametrizableSpace Y) (hR : R.IsCharacteristic)
    (hMet : TopologicalSpace.IsCompletelyMetrizableSpace ↥(UMetOn Y R)) :
    TopologicalSpace.SeparableSpace Y :=
  separable_of_isCompletelyMetrizableSpace_UMetOn_of_isUltraComponentControlledExtensorOn
    hY hR exists_isUltraComponentControlledExtensorOn hMet

end

end IshikiExt
