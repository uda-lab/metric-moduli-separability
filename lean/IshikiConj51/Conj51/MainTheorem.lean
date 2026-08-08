-- Conj51.MainTheorem
--
-- Defines `MetD D` — the Lean representation of the source's `Met(D)`
-- (Ishiki, arXiv:2407.03030, §1.1; verified in Issue #2) — and states
-- `THM-CONJ51`.
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
--   * "Completely metrizable" is nonetheless the ordinary (finite-metric)
--     notion applied to the *topology* `MetD D` carries — Mathlib's
--     `TopologicalSpace.IsCompletelyMetrizableSpace` asks only whether some
--     compatible finite-valued `MetricSpace` structure realises that
--     topology completely; it does not require the topology to have been
--     built from a finite-valued distance in the first place.
--
-- Status: `MetD`, its `EMetricSpace` instance, and `thm_conj51`'s statement
-- are complete and sorry-free. `thm_conj51`'s *proof* carries a tracked
-- `sorry` (see notes/proof-audit.md sorry tracker) pending LEM-STAR-METRIC
-- and LEM-CLOSED-IMAGE (Issues #7, #9). Per Issue #6's acceptance criteria,
-- proving THM-CONJ51 is out of scope here.

import Mathlib
import IshikiConj51.Conj51.Cardinality
import IshikiConj51.Conj51.MetricConstruction
import IshikiConj51.Conj51.ClosedEmbedding

open Cardinal
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

end MetD

/-- **THM-CONJ51.** For a discrete space `D` of cardinality `ℵ₁`,
`Met(D)` — equipped with the supremum-metric topology — is not completely
metrizable.

This matches the report's (`report/report-ja.md` §2) and the source's
(Ishiki, arXiv:2407.03030, Conjecture 5.1) statement exactly: no bounded,
uniformly-discrete, or otherwise weakened proxy is substituted.

Status: statement only (Issue #6). The proof depends on LEM-A-EXISTS
(complete, `Cardinality.lean`), LEM-STAR-METRIC and LEM-CLOSED-IMAGE (both
still open, `MetricConstruction.lean` / `ClosedEmbedding.lean`), and the
closed-subspace-inheritance argument audited in Issue #4. Tracked as a
`sorry` in notes/proof-audit.md; not claimed as proved by this issue. -/
theorem thm_conj51 (D : Type) (hD : #D = Cardinal.aleph 1) :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D) := by
  sorry
