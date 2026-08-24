-- Ext.BddPMet
--
-- The ambient space in which the Ishiki-extension coding of Layer 1 lives:
-- the *bounded* pseudometrics on a set `D`, carrying the supremum distance
--
--     ρ(d, e) = sup_{u,v} |d(u,v) − e(u,v)|.
--
-- Mathematical source of truth for this track: `notes/borel-preprint-audit.md`
-- §7 items 1–2 (Issue #56), which gates the Borel-preprint extension track.
-- `report/report-ja.md` is *not* the
-- source of truth here: it stays frozen as the Conjecture 5.1 archival
-- report by the Issue #46 decision, and carries no extension claim.
--
-- The draft writes `BCPM(D)` for the bounded *continuous* pseudometrics on
-- `D` and `BMet(D)` for the bounded metrics compatible with the topology
-- of `D`.
--
-- Naming note (this is a mathematical identification, not a convention): the
-- carrier `D` of Layer 1 is a discrete set, and every function on a discrete
-- space is continuous, so on such a `D` the continuity requirement in
-- `BCPM(D)` is vacuous and `BCPM(D)` is exactly the bounded pseudometrics.
-- The Lean name `BddPMet` records what is actually assumed rather than
-- claiming a continuity condition that is not stated.
--
-- Unlike `Conj51/MetD.lean` — where `Met(D)` consists of arbitrary, possibly
-- unbounded metrics and the supremum distance is therefore `ℝ≥0∞`-valued
-- — every element here is bounded, so `ρ` is a real number and
-- `BddPMet D` is a `MetricSpace`.  That is what the bounded coding is
-- for: it lets the parameter map be Lipschitz into a real metric space.
--
-- `IsMetricOn` and `IsMetricOn.topology` are reused verbatim from
-- `Conj51/MetD.lean` so that "compatible with the discrete topology" has one
-- definition across the repository.  Nothing in `Conj51/` is modified.
--
-- Status: sorry-free.

import Mathlib
import IshikiConj51.Conj51.MetD

namespace IshikiExt

variable {D : Type*}

/-! ## Bounded pseudometrics -/

/-- `d` satisfies the axioms of a bounded pseudometric on `D`: symmetric,
vanishing on the diagonal, triangle inequality, and uniformly bounded.  Points
are *not* required to be separated — that extra condition is what distinguishes
`BMet(D)` from `BCPM(D)` in the draft, and it is carried by `IsCompatible`
below (through `IsMetricOn`). -/
structure IsBddPMetOn (d : D → D → ℝ) : Prop where
  dist_self : ∀ x, d x x = 0
  dist_comm : ∀ x y, d x y = d y x
  dist_triangle : ∀ x y z, d x z ≤ d x y + d y z
  bounded : ∃ C, ∀ x y, d x y ≤ C

theorem IsBddPMetOn.nonneg {d : D → D → ℝ} (h : IsBddPMetOn d) (x y : D) : 0 ≤ d x y := by
  have htri := h.dist_triangle x y x
  rw [h.dist_self x, h.dist_comm y x] at htri
  linarith

/-- The bound may always be taken nonnegative; this removes a case split on
whether `D` is empty. -/
theorem IsBddPMetOn.exists_bound {d : D → D → ℝ} (h : IsBddPMetOn d) :
    ∃ C, 0 ≤ C ∧ ∀ x y, d x y ≤ C := by
  obtain ⟨C, hC⟩ := h.bounded
  exact ⟨max C 0, le_max_right _ _, fun x y => (hC x y).trans (le_max_left _ _)⟩

/-- A metric that happens to be bounded is a bounded pseudometric. -/
theorem IsMetricOn.toIsBddPMetOn {d : D → D → ℝ} (h : IsMetricOn d) {C : ℝ}
    (hC : ∀ x y, d x y ≤ C) : IsBddPMetOn d :=
  ⟨h.dist_self, h.dist_comm, h.dist_triangle, ⟨C, hC⟩⟩

/-- `BddPMet D`: the draft's `BCPM(D)` for a discrete carrier `D` — the
bounded pseudometrics on `D`. -/
def BddPMet (D : Type*) : Type _ := {d : D → D → ℝ // IsBddPMetOn d}

namespace BddPMet

/-- The supremum distance `ρ(d,e) = sup_{u,v} |d(u,v) − e(u,v)|`.  It is a
real number because both arguments are bounded. -/
noncomputable def supDist (d e : BddPMet D) : ℝ :=
  ⨆ p : D × D, |d.1 p.1 p.2 - e.1 p.1 p.2|

theorem bddAbove_absSub (d e : BddPMet D) :
    BddAbove (Set.range fun p : D × D => |d.1 p.1 p.2 - e.1 p.1 p.2|) := by
  obtain ⟨C, hC0, hC⟩ := d.2.exists_bound
  obtain ⟨E, hE0, hE⟩ := e.2.exists_bound
  refine ⟨C + E, ?_⟩
  rintro _ ⟨p, rfl⟩
  rw [abs_sub_le_iff]
  exact ⟨by linarith [hC p.1 p.2, e.2.nonneg p.1 p.2],
    by linarith [hE p.1 p.2, d.2.nonneg p.1 p.2]⟩

/-- Every pair contributes a term to the supremum. -/
theorem le_supDist (d e : BddPMet D) (u v : D) :
    |d.1 u v - e.1 u v| ≤ supDist d e :=
  le_ciSup (bddAbove_absSub d e) (u, v)

/-- A uniform bound over all pairs bounds `ρ`. -/
theorem supDist_le {d e : BddPMet D} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u v, |d.1 u v - e.1 u v| ≤ c) : supDist d e ≤ c :=
  Real.iSup_le (fun p => h p.1 p.2) hc

theorem supDist_nonneg (d e : BddPMet D) : 0 ≤ supDist d e :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem supDist_self (d : BddPMet D) : supDist d d = 0 :=
  le_antisymm (supDist_le le_rfl (by simp)) (supDist_nonneg d d)

theorem supDist_comm (d e : BddPMet D) : supDist d e = supDist e d := by
  simp only [supDist, abs_sub_comm]

theorem supDist_triangle (d e f : BddPMet D) :
    supDist d f ≤ supDist d e + supDist e f := by
  refine supDist_le (by linarith [supDist_nonneg d e, supDist_nonneg e f]) fun u v => ?_
  calc |d.1 u v - f.1 u v|
      ≤ |d.1 u v - e.1 u v| + |e.1 u v - f.1 u v| := abs_sub_le _ _ _
    _ ≤ supDist d e + supDist e f := add_le_add (le_supDist d e u v) (le_supDist e f u v)

theorem eq_of_supDist_eq_zero {d e : BddPMet D} (h : supDist d e = 0) : d = e := by
  apply Subtype.ext
  funext u v
  have hle : |d.1 u v - e.1 u v| ≤ 0 := (le_supDist d e u v).trans h.le
  have := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  linarith

noncomputable instance : MetricSpace (BddPMet D) where
  dist := supDist
  dist_self := supDist_self
  dist_comm := supDist_comm
  dist_triangle := supDist_triangle
  eq_of_dist_eq_zero := eq_of_supDist_eq_zero

theorem dist_eq_supDist (d e : BddPMet D) : dist d e = supDist d e := rfl

/-- Evaluation at a fixed pair is `1`-Lipschitz: each pair is one term of the
supremum defining `ρ`. -/
theorem le_dist (d e : BddPMet D) (u v : D) : |d.1 u v - e.1 u v| ≤ dist d e :=
  le_supDist d e u v

/-- A uniform pairwise bound bounds the ambient distance. -/
theorem dist_le {d e : BddPMet D} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u v, |d.1 u v - e.1 u v| ≤ c) : dist d e ≤ c :=
  supDist_le hc h

end BddPMet

/-! ## The compatible members: `BMet(D)` -/

/-- A bounded pseudometric is *compatible* when it is in fact a metric and the
topology it induces is the discrete one.  For a discrete carrier `D` this is
literally the draft's condition `d ∈ BMet(D)`: no boundedness beyond the
ambient one, no uniform discreteness, and the topology condition is
`IsMetricOn.topology = ⊥` from `Conj51/MetD.lean`. -/
def IsCompatible (d : BddPMet D) : Prop := ∃ h : IsMetricOn d.1, h.topology = ⊥

/-- The draft's `BMet(D) ⊆ BCPM(D)`, as a subset of the ambient metric
space. -/
def BMet (D : Type*) : Set (BddPMet D) := {d | IsCompatible d}

@[simp] theorem mem_BMet {d : BddPMet D} : d ∈ BMet D ↔ IsCompatible d := Iff.rfl

end IshikiExt
