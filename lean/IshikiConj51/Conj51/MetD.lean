-- Conj51.MetD
--
-- Base module holding the Lean representation of the source's `Met(D)`
-- (Ishiki, arXiv:2407.03030, §1.1; verified in Issue #2).
--
-- `IsMetricOn`, `IsMetricOn.topology`, `MetD` and its `EMetricSpace`
-- instance were introduced by Issue #6 inside `MainTheorem.lean`.  They are
-- moved here **unchanged** (Issue #7) purely to break an import cycle:
-- `MainTheorem.lean` imports the claim modules `MetricConstruction.lean` and
-- `ClosedEmbedding.lean`, so those modules cannot import it back — yet they
-- are exactly the modules that must *construct* elements of `Met(D)`.  No
-- definition or statement below differs from the Issue #6 text; only its
-- location changed.
--
-- Source-faithfulness notes (see notes/literature.md for the full record):
--   * Each element of `Met(D)` is an ordinary, finite real-valued metric on
--     `D` that induces the discrete topology on `D` — no boundedness and no
--     uniform-discreteness restriction. This is `IsMetricOn` below, plus the
--     `.topology = ⊥` (discrete) condition.
--   * The *ambient* supremum distance on the space `Met(D)` itself is
--     genuinely extended-valued: it can be `∞` between unbounded metrics
--     whose values differ unboundedly (Issue #2/#4 finding). Hence `MetD D`
--     is equipped with an `EMetricSpace` (extended metric), not a
--     `MetricSpace`, matching `ρ(d₁,d₂) = sup_{x,y} |d₁(x,y) − d₂(x,y)|`.
--
-- This module additionally provides the general bridge lemma
-- `IsMetricOn.topology_eq_bot_iff`, which converts the `.topology = ⊥`
-- condition into the elementary "every point has an isolating radius"
-- criterion used by both Issue #7 and Issue #9.  It is stated for an
-- arbitrary `IsMetricOn`, not for the star family, so that it is reusable.
--
-- Issue #9 added the small generic API for the ambient supremum distance at
-- the end of the `MetD` namespace (`edist_def`, `ofReal_abs_sub_le_edist`,
-- `edist_le_of_forall`, `lipschitzWith_apply`, `exists_isMetricOn_of_val_eq`).
-- These are consumed by both `ClosedEmbedding.lean` and `Relabel.lean`, so
-- they live here rather than in either one.  Nothing in the Issue #6 material
-- above them was altered.

import Mathlib

open scoped ENNReal

/-- `d` satisfies the axioms of an ordinary (finite-valued) metric on `D`.
Stated for a bare function, rather than bundling a `MetricSpace` structure,
so that we can separately ask whether the topology it induces is discrete. -/
structure IsMetricOn {D : Type*} (d : D → D → ℝ) : Prop where
  dist_self : ∀ x, d x x = 0
  eq_of_dist_eq_zero : ∀ {x y}, d x y = 0 → x = y
  dist_comm : ∀ x y, d x y = d y x
  dist_triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The topology on `D` induced by a metric-axiom-satisfying function `d`. -/
@[implicit_reducible] noncomputable def IsMetricOn.topology {D : Type*} {d : D → D → ℝ}
    (h : IsMetricOn d) : TopologicalSpace D :=
  (UniformSpace.ofDist d h.dist_self h.dist_comm h.dist_triangle).toTopologicalSpace

/-- The `MetricSpace` structure carried by a metric-axiom-satisfying function.

`PseudoMetricSpace`'s `toUniformSpace` field defaults to
`UniformSpace.ofDist dist dist_self dist_comm dist_triangle`, which is
precisely the uniformity used by `IsMetricOn.topology`; hence the topology of
this instance is *definitionally* `h.topology` (see
`IsMetricOn.topology_eq_metricSpace_topology`). -/
@[implicit_reducible] noncomputable def IsMetricOn.toMetricSpace {D : Type*} {d : D → D → ℝ}
    (h : IsMetricOn d) : MetricSpace D where
  dist := d
  dist_self := h.dist_self
  dist_comm := h.dist_comm
  dist_triangle := h.dist_triangle
  eq_of_dist_eq_zero := h.eq_of_dist_eq_zero

theorem IsMetricOn.topology_eq_metricSpace_topology {D : Type*} {d : D → D → ℝ}
    (h : IsMetricOn d) :
    h.topology = h.toMetricSpace.toUniformSpace.toTopologicalSpace := rfl

theorem IsMetricOn.dist_toMetricSpace {D : Type*} {d : D → D → ℝ} (h : IsMetricOn d)
    (x y : D) : @dist D h.toMetricSpace.toDist x y = d x y := rfl

/-- **Discreteness criterion.** The topology induced by a metric `d` is the
discrete topology exactly when every point has a radius that isolates it.
This is the elementary criterion used in the report (§3.3 (C2)): `d` induces the
discrete topology iff `δ(u) := inf_{v ≠ u} d(u,v) > 0` for every `u`.

Stated generally (for any `IsMetricOn`) because Issue #7 needs both
directions and Issue #9 reuses it. -/
theorem IsMetricOn.topology_eq_bot_iff {D : Type*} {d : D → D → ℝ} (h : IsMetricOn d) :
    h.topology = ⊥ ↔ ∀ u : D, ∃ ε > 0, ∀ v : D, d v u < ε → v = u := by
  letI : MetricSpace D := h.toMetricSpace
  constructor
  · intro hbot u
    have hopen : @IsOpen D h.topology ({u} : Set D) := by rw [hbot]; trivial
    exact Metric.isOpen_singleton_iff.mp hopen
  · intro hall
    refine eq_bot_of_singletons_open (t := h.topology) fun u => ?_
    exact Metric.isOpen_singleton_iff.mpr (hall u)

/-- `MetD D`: the metrics on `D` compatible with the discrete topology, i.e.
whose induced topology equals `⊥` (the discrete topology; Mathlib's topology
lattice has `⊥` as discrete, `⊤` as indiscrete). This is exactly the source's
`Met(D)`: ordinary finite-valued metrics generating the discrete topology,
with no boundedness or uniform-discreteness restriction smuggled in. -/
def MetD (D : Type*) : Type _ :=
  {d : D → D → ℝ // ∃ h : IsMetricOn d, h.topology = ⊥}

namespace MetD

variable {D : Type*}

/-- The (extended) supremum distance on `Met(D)`, matching the source's
`ρ(d₁,d₂) = sup_{x,y} |d₁(x,y) − d₂(x,y)|` (Ishiki, §1.1). Genuinely
extended-valued: `⨆` over `D × D` of a nonnegative real cast to `ℝ≥0∞`, which
can be `∞` when `D` is infinite and the two metrics are unboundedly apart. -/
noncomputable def edist (d e : MetD D) : ℝ≥0∞ :=
  ⨆ p : D × D, ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2|

theorem edist_self (d : MetD D) : edist d d = 0 := by
  simp [edist]

theorem edist_comm (d e : MetD D) : edist d e = edist e d := by
  simp only [edist, abs_sub_comm]

theorem edist_triangle (d e f : MetD D) : edist d f ≤ edist d e + edist e f := by
  apply iSup_le
  intro p
  calc ENNReal.ofReal |d.1 p.1 p.2 - f.1 p.1 p.2|
      ≤ ENNReal.ofReal (|d.1 p.1 p.2 - e.1 p.1 p.2| + |e.1 p.1 p.2 - f.1 p.1 p.2|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2| + ENNReal.ofReal |e.1 p.1 p.2 - f.1 p.1 p.2| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ edist d e + edist e f :=
        add_le_add (le_iSup (fun q : D × D => ENNReal.ofReal |d.1 q.1 q.2 - e.1 q.1 q.2|) p)
          (le_iSup (fun q : D × D => ENNReal.ofReal |e.1 q.1 q.2 - f.1 q.1 q.2|) p)

theorem eq_of_edist_eq_zero {d e : MetD D} (h : edist d e = 0) : d = e := by
  have hpt : ∀ p : D × D, ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2| = 0 :=
    ENNReal.iSup_eq_zero.mp h
  apply Subtype.ext
  funext x y
  have hxy := hpt (x, y)
  rw [ENNReal.ofReal_eq_zero] at hxy
  have hnn : 0 ≤ |d.1 x y - e.1 x y| := abs_nonneg _
  have habs0 : |d.1 x y - e.1 x y| = 0 := le_antisymm hxy hnn
  have hsub0 : d.1 x y - e.1 x y = 0 := abs_eq_zero.mp habs0
  linarith

noncomputable instance : EDist (MetD D) := ⟨edist⟩

noncomputable instance : PseudoEMetricSpace (MetD D) where
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle

noncomputable instance : EMetricSpace (MetD D) where
  eq_of_edist_eq_zero := eq_of_edist_eq_zero

/-! ### Generic API for the ambient supremum distance (Issue #9)

Small reusable facts about `ρ`, needed by both `ClosedEmbedding.lean` (to see
the image of the parameter map as a closed set) and `Relabel.lean` (to see
relabelling as an isometry). -/

/-- Unfolding of the ambient supremum distance on `Met(D)`. -/
theorem edist_def (e f : MetD D) :
    edist e f = ⨆ p : D × D, ENNReal.ofReal |e.1 p.1 p.2 - f.1 p.1 p.2| := rfl

/-- Each pair contributes a term to the supremum defining `ρ`. -/
theorem ofReal_abs_sub_le_edist (e f : MetD D) (u v : D) :
    ENNReal.ofReal |e.1 u v - f.1 u v| ≤ edist e f := by
  rw [edist_def]
  exact le_iSup (fun p : D × D => ENNReal.ofReal |e.1 p.1 p.2 - f.1 p.1 p.2|) (u, v)

/-- A uniform bound over all pairs bounds `ρ`. -/
theorem edist_le_of_forall {e f : MetD D} {c : ℝ≥0∞}
    (h : ∀ u v, ENNReal.ofReal |e.1 u v - f.1 u v| ≤ c) : edist e f ≤ c := by
  rw [edist_def]
  exact iSup_le fun p => h p.1 p.2

/-- Evaluation at a fixed pair is `1`-Lipschitz on `Met(D)`. -/
theorem lipschitzWith_apply (u v : D) : LipschitzWith 1 (fun e : MetD D => e.1 u v) := by
  intro e f
  simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq]
  exact ofReal_abs_sub_le_edist e f u v

/-- A metric that agrees pointwise with a member of `Met(D)` is itself
compatible with the discrete topology. -/
theorem exists_isMetricOn_of_val_eq {d : D → D → ℝ} (e : MetD D) (h : e.1 = d) :
    ∃ hm : IsMetricOn d, hm.topology = ⊥ := by
  subst h; exact e.2

end MetD
