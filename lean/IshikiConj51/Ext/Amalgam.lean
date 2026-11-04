-- Ext.Amalgam
--
-- One-point amalgamation of metrics: reusable machinery for the component
-- statements of the Borel preprint (arXiv:2608.19618, Theorems 3.4 and 3.8).
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` §2.7, which
-- records the construction and the two facts the preprint leaves implicit.
--
-- Setting.  A metric `d` on a carrier `Z`, a subset `E ⊆ Z`, a metric `e` on
-- `E`, and a point `z ∈ E` common to both.  The amalgam
--
--     m(x,y) = e(x,y)                     (x, y ∈ E)
--     m(x,y) = d(x,y)                     (x, y ∉ E)
--     m(x,y) = e(x,z) + d(z,y)            (x ∈ E, y ∉ E)
--
-- is the metric obtained by gluing `(E, e)` and `(Z, d)` along `z`: paths
-- between the two sides are routed through the common point.  Nothing here
-- refers to the star coding, and `d` is an arbitrary metric on `Z` — the
-- audit's `m_t` is the special case where `e` is the coding transported to an
-- uncountable closed `d`-ball.
--
-- What is proved here:
--   `isMetricOn_amalgam`             — `m` is a metric (no extra hypotheses).
--   `amalgam_topology_eq_bot`        — `m` is compatible with the discrete
--                                      topology, given that `d` and `e` are
--                                      and that the two sides are uniformly
--                                      separated at `z`.
--   `topology_eq_bot_of_amalgam`     — the converse on the `E` side: `m`
--                                      discrete forces `e` discrete.
--   `abs_amalgam_sub_le`             — the quantitative finite-distance bound
--                                      `|m − d| ≤ B + 2H` (audit §2.7 (i)).
--   `abs_amalgam_sub_amalgam_le`     — `m` depends on `e` pointwise
--                                      `1`-Lipschitzly, which carries the
--                                      Lipschitz estimate of the parameter map.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.CPM

namespace IshikiExt

variable {Z : Type*}

/-! ## Two facts about `IsMetricOn` used throughout -/

theorem IsMetricOn.nonneg {d : Z → Z → ℝ} (h : IsMetricOn d) (x y : Z) : 0 ≤ d x y := by
  have htri := h.dist_triangle x y x
  rw [h.dist_self x, h.dist_comm y x] at htri
  linarith

/-- A metric is in particular a finite-valued pseudometric, hence a member of
the ambient `CPM`. -/
theorem IsMetricOn.toIsPMetricOn {d : Z → Z → ℝ} (h : IsMetricOn d) : IsPMetricOn d :=
  ⟨h.dist_self, h.dist_comm, h.dist_triangle⟩

/-! ## The amalgam -/

open Classical in
/-- The one-point amalgamation of `d` on `Z` with `e` on `E ⊆ Z` along the
common point `z ∈ E`. -/
noncomputable def amalgam (E : Set Z) (z : Z) (hz : z ∈ E) (d : Z → Z → ℝ)
    (e : ↥E → ↥E → ℝ) : Z → Z → ℝ := fun x y =>
  if hx : x ∈ E then
    if hy : y ∈ E then e ⟨x, hx⟩ ⟨y, hy⟩ else e ⟨x, hx⟩ ⟨z, hz⟩ + d z y
  else
    if hy : y ∈ E then d x z + e ⟨z, hz⟩ ⟨y, hy⟩ else d x y

variable {E : Set Z} {z : Z} {d : Z → Z → ℝ} {e : ↥E → ↥E → ℝ}

theorem amalgam_mem_mem (hz : z ∈ E) {x y : Z} (hx : x ∈ E) (hy : y ∈ E) :
    amalgam E z hz d e x y = e ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp only [amalgam]
  rw [dif_pos hx, dif_pos hy]

theorem amalgam_mem_notMem (hz : z ∈ E) {x y : Z} (hx : x ∈ E) (hy : y ∉ E) :
    amalgam E z hz d e x y = e ⟨x, hx⟩ ⟨z, hz⟩ + d z y := by
  simp only [amalgam]
  rw [dif_pos hx, dif_neg hy]

theorem amalgam_notMem_mem (hz : z ∈ E) {x y : Z} (hx : x ∉ E) (hy : y ∈ E) :
    amalgam E z hz d e x y = d x z + e ⟨z, hz⟩ ⟨y, hy⟩ := by
  simp only [amalgam]
  rw [dif_neg hx, dif_pos hy]

theorem amalgam_notMem_notMem (hz : z ∈ E) {x y : Z} (hx : x ∉ E) (hy : y ∉ E) :
    amalgam E z hz d e x y = d x y := by
  simp only [amalgam]
  rw [dif_neg hx, dif_neg hy]

/-- **The amalgam is a metric.**  No hypothesis beyond `d` and `e` being
metrics is needed: routing cross pairs through `z` is exactly what makes the
triangle inequality hold in the six mixed configurations. -/
theorem isMetricOn_amalgam (hz : z ∈ E) (hd : IsMetricOn d) (he : IsMetricOn e) :
    IsMetricOn (amalgam E z hz d e) := by
  have hdnn := IsMetricOn.nonneg hd
  have henn := IsMetricOn.nonneg he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ E
    · rw [amalgam_mem_mem hz hx hx]; exact he.dist_self _
    · rw [amalgam_notMem_notMem hz hx hx]; exact hd.dist_self _
  · intro x y hxy
    by_cases hx : x ∈ E <;> by_cases hy : y ∈ E
    · rw [amalgam_mem_mem hz hx hy] at hxy
      exact congrArg Subtype.val (he.eq_of_dist_eq_zero hxy)
    · rw [amalgam_mem_notMem hz hx hy] at hxy
      have h1 := henn ⟨x, hx⟩ ⟨z, hz⟩
      have h2 := hdnn z y
      have hzy : d z y = 0 := by linarith
      exact absurd (hd.eq_of_dist_eq_zero hzy ▸ hz) hy
    · rw [amalgam_notMem_mem hz hx hy] at hxy
      have h1 := hdnn x z
      have h2 := henn ⟨z, hz⟩ ⟨y, hy⟩
      have hxz : d x z = 0 := by linarith
      exact absurd (hd.eq_of_dist_eq_zero hxz ▸ hz) hx
    · rw [amalgam_notMem_notMem hz hx hy] at hxy
      exact hd.eq_of_dist_eq_zero hxy
  · intro x y
    by_cases hx : x ∈ E <;> by_cases hy : y ∈ E
    · rw [amalgam_mem_mem hz hx hy, amalgam_mem_mem hz hy hx]
      exact he.dist_comm _ _
    · rw [amalgam_mem_notMem hz hx hy, amalgam_notMem_mem hz hy hx,
        he.dist_comm ⟨x, hx⟩ ⟨z, hz⟩, hd.dist_comm z y]
      ring
    · rw [amalgam_notMem_mem hz hx hy, amalgam_mem_notMem hz hy hx,
        he.dist_comm ⟨z, hz⟩ ⟨y, hy⟩, hd.dist_comm x z]
      ring
    · rw [amalgam_notMem_notMem hz hx hy, amalgam_notMem_notMem hz hy hx]
      exact hd.dist_comm _ _
  · intro u v w
    by_cases hu : u ∈ E <;> by_cases hv : v ∈ E <;> by_cases hw : w ∈ E
    · rw [amalgam_mem_mem hz hu hw, amalgam_mem_mem hz hu hv, amalgam_mem_mem hz hv hw]
      exact he.dist_triangle _ _ _
    · rw [amalgam_mem_notMem hz hu hw, amalgam_mem_mem hz hu hv,
        amalgam_mem_notMem hz hv hw]
      linarith [he.dist_triangle ⟨u, hu⟩ ⟨v, hv⟩ ⟨z, hz⟩]
    · rw [amalgam_mem_mem hz hu hw, amalgam_mem_notMem hz hu hv,
        amalgam_notMem_mem hz hv hw]
      linarith [he.dist_triangle ⟨u, hu⟩ ⟨z, hz⟩ ⟨w, hw⟩, hdnn z v, hdnn v z]
    · rw [amalgam_mem_notMem hz hu hw, amalgam_mem_notMem hz hu hv,
        amalgam_notMem_notMem hz hv hw]
      linarith [hd.dist_triangle z v w]
    · rw [amalgam_notMem_mem hz hu hw, amalgam_notMem_mem hz hu hv,
        amalgam_mem_mem hz hv hw]
      linarith [he.dist_triangle ⟨z, hz⟩ ⟨v, hv⟩ ⟨w, hw⟩]
    · rw [amalgam_notMem_notMem hz hu hw, amalgam_notMem_mem hz hu hv,
        amalgam_mem_notMem hz hv hw]
      linarith [hd.dist_triangle u z w, henn ⟨z, hz⟩ ⟨v, hv⟩, henn ⟨v, hv⟩ ⟨z, hz⟩]
    · rw [amalgam_notMem_mem hz hu hw, amalgam_notMem_notMem hz hu hv,
        amalgam_notMem_mem hz hv hw]
      linarith [hd.dist_triangle u v z]
    · rw [amalgam_notMem_notMem hz hu hw, amalgam_notMem_notMem hz hu hv,
        amalgam_notMem_notMem hz hv hw]
      exact hd.dist_triangle _ _ _

/-! ## Compatibility with the discrete topology -/

/-- **The amalgam is compatible with the discrete topology.**  Besides
compatibility of the two pieces this needs a uniform gap `c > 0` between the
two sides: every point of `E` other than `z` is `e`-far from `z`, and every
point outside `E` is `d`-far from `z`.  Then the isolating radius of a point
is the minimum of its radius on its own side and `c`. -/
theorem amalgam_topology_eq_bot (hz : z ∈ E) (hd : IsMetricOn d) (he : IsMetricOn e)
    (hdbot : hd.topology = ⊥) (hebot : he.topology = ⊥) {c : ℝ} (hc : 0 < c)
    (hesep : ∀ y : ↥E, y ≠ ⟨z, hz⟩ → c ≤ e ⟨z, hz⟩ y)
    (hdsep : ∀ y : Z, y ∉ E → c ≤ d z y) :
    (isMetricOn_amalgam hz hd he).topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  intro u
  by_cases hu : u ∈ E
  · obtain ⟨ε, hε, hall⟩ := he.topology_eq_bot_iff.mp hebot ⟨u, hu⟩
    refine ⟨min ε c, lt_min hε hc, fun v hv => ?_⟩
    by_cases hvE : v ∈ E
    · rw [amalgam_mem_mem hz hvE hu] at hv
      exact congrArg Subtype.val (hall ⟨v, hvE⟩ (lt_of_lt_of_le hv (min_le_left _ _)))
    · exfalso
      rw [amalgam_notMem_mem hz hvE hu] at hv
      have hlt := lt_of_lt_of_le hv (min_le_right _ _)
      have hdvz := IsMetricOn.nonneg hd v z
      have henn := IsMetricOn.nonneg he ⟨z, hz⟩ ⟨u, hu⟩
      by_cases huz : (⟨u, hu⟩ : ↥E) = ⟨z, hz⟩
      · have h0 : e ⟨z, hz⟩ ⟨u, hu⟩ = 0 := by rw [huz]; exact he.dist_self _
        have h1 : c ≤ d v z := by rw [hd.dist_comm]; exact hdsep v hvE
        linarith
      · linarith [hesep ⟨u, hu⟩ huz]
  · obtain ⟨ε, hε, hall⟩ := hd.topology_eq_bot_iff.mp hdbot u
    refine ⟨min ε c, lt_min hε hc, fun v hv => ?_⟩
    by_cases hvE : v ∈ E
    · exfalso
      rw [amalgam_mem_notMem hz hvE hu] at hv
      have hlt := lt_of_lt_of_le hv (min_le_right _ _)
      linarith [hdsep u hu, IsMetricOn.nonneg he ⟨v, hvE⟩ ⟨z, hz⟩]
    · rw [amalgam_notMem_notMem hz hvE hu] at hv
      exact hall v (lt_of_lt_of_le hv (min_le_left _ _))

/-- The converse on the `E` side: the amalgam restricts to `e` on `E`, so if
the amalgam is compatible with the discrete topology then so is `e`.  This is
the direction that turns a parameter in the coding set into a *failure* of
compatibility for the amalgam. -/
theorem topology_eq_bot_of_amalgam (hz : z ∈ E) (he : IsMetricOn e)
    (h : IsMetricOn (amalgam E z hz d e)) (hbot : h.topology = ⊥) : he.topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  intro u
  obtain ⟨ε, hε, hall⟩ := h.topology_eq_bot_iff.mp hbot u.1
  refine ⟨ε, hε, fun v hv => ?_⟩
  have hlt : amalgam E z hz d e v.1 u.1 < ε := by
    rw [amalgam_mem_mem hz v.2 u.2]
    simpa using hv
  exact Subtype.ext (hall v.1 hlt)

/-! ## The quantitative bounds -/

/-- **Finite distance from the base metric** (audit §2.7 (i)).  If `e` is
bounded by `B` and `E` sits inside the closed `d`-ball of radius `H` around
`z`, then the amalgam differs from `d` by at most `B + 2H` at every pair.
The bound is stated explicitly because the complete-metric branch reuses
it. -/
theorem abs_amalgam_sub_le (hz : z ∈ E) (hd : IsMetricOn d) (he : IsMetricOn e)
    {B H : ℝ} (hB : ∀ x y, e x y ≤ B) (hH : ∀ x ∈ E, d z x ≤ H) (x y : Z) :
    |amalgam E z hz d e x y - d x y| ≤ B + 2 * H := by
  have hB0 : 0 ≤ B := le_trans (IsMetricOn.nonneg he ⟨z, hz⟩ ⟨z, hz⟩) (hB _ _)
  have hH0 : 0 ≤ H := le_trans (IsMetricOn.nonneg hd z z) (hH z hz)
  rw [abs_le]
  by_cases hx : x ∈ E <;> by_cases hy : y ∈ E
  · rw [amalgam_mem_mem hz hx hy]
    have h1 : d x z ≤ H := by rw [hd.dist_comm]; exact hH x hx
    have h2 : d z y ≤ H := hH y hy
    constructor <;>
      linarith [hd.dist_triangle x z y, IsMetricOn.nonneg hd x y,
        IsMetricOn.nonneg he ⟨x, hx⟩ ⟨y, hy⟩, hB ⟨x, hx⟩ ⟨y, hy⟩]
  · rw [amalgam_mem_notMem hz hx hy]
    have h1 : d x z ≤ H := by rw [hd.dist_comm]; exact hH x hx
    have h2 : d z x ≤ H := hH x hx
    constructor <;>
      linarith [hd.dist_triangle x z y, hd.dist_triangle z x y,
        IsMetricOn.nonneg he ⟨x, hx⟩ ⟨z, hz⟩, hB ⟨x, hx⟩ ⟨z, hz⟩]
  · rw [amalgam_notMem_mem hz hx hy]
    have h1 : d z y ≤ H := hH y hy
    have h2 : d y z ≤ H := by rw [hd.dist_comm]; exact hH y hy
    constructor <;>
      linarith [hd.dist_triangle x z y, hd.dist_triangle x y z,
        IsMetricOn.nonneg he ⟨z, hz⟩ ⟨y, hy⟩, hB ⟨z, hz⟩ ⟨y, hy⟩]
  · rw [amalgam_notMem_notMem hz hx hy]
    constructor <;> linarith

/-- The amalgam depends on the `E`-side metric pointwise `1`-Lipschitzly: a
uniform bound on `|e − f|` bounds `|m_e − m_f|` by the same constant.  This is
what transports the coding's Lipschitz estimate in the parameter to the
amalgamated family. -/
theorem abs_amalgam_sub_amalgam_le (hz : z ∈ E) (b : Z → Z → ℝ) {e₁ e₂ : ↥E → ↥E → ℝ}
    {k : ℝ} (hk : 0 ≤ k) (h : ∀ x y, |e₁ x y - e₂ x y| ≤ k) (x y : Z) :
    |amalgam E z hz b e₁ x y - amalgam E z hz b e₂ x y| ≤ k := by
  by_cases hx : x ∈ E <;> by_cases hy : y ∈ E
  · rw [amalgam_mem_mem hz hx hy, amalgam_mem_mem hz hx hy]
    exact h _ _
  · rw [amalgam_mem_notMem hz hx hy, amalgam_mem_notMem hz hx hy,
      show e₁ ⟨x, hx⟩ ⟨z, hz⟩ + b z y - (e₂ ⟨x, hx⟩ ⟨z, hz⟩ + b z y)
        = e₁ ⟨x, hx⟩ ⟨z, hz⟩ - e₂ ⟨x, hx⟩ ⟨z, hz⟩ by ring]
    exact h _ _
  · rw [amalgam_notMem_mem hz hx hy, amalgam_notMem_mem hz hx hy,
      show b x z + e₁ ⟨z, hz⟩ ⟨y, hy⟩ - (b x z + e₂ ⟨z, hz⟩ ⟨y, hy⟩)
        = e₁ ⟨z, hz⟩ ⟨y, hy⟩ - e₂ ⟨z, hz⟩ ⟨y, hy⟩ by ring]
    exact h _ _
  · rw [amalgam_notMem_notMem hz hx hy, amalgam_notMem_notMem hz hx hy]
    simpa using hk

end IshikiExt
