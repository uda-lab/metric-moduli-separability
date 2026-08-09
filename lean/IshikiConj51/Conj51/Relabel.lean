-- Conj51.Relabel
--
-- Transport of `Met(D)` along a bijection of the underlying discrete set.
--
-- THM-CONJ51 is stated for an *arbitrary* `D` with `|D| = ℵ₁`, whereas the
-- star construction of `MetricConstruction.lean` produces one particular such
-- set, `StarIndex A`.  `Met(D)` depends on `D` only through its cardinality:
-- a bijection `σ : D ≃ E` relabels metrics, preserves the metric axioms and
-- discreteness, and preserves the supremum distance *exactly* (the supremum
-- is over `D × D`, which `σ` reindexes bijectively).  So `Met(E) ≃ᵢ Met(D)`.
--
-- The report makes the same remark informally in §3.2/§3.8: the enumeration
-- `A = {a_α : α < ω₁}` is a bijection, so indexing the stars by `A` or by `ω₁`
-- gives the same construction up to relabelling, and `|A| = ℵ₁` is used only
-- for indexing and the cardinality computation.
--
-- Status: sorry-free.

import Mathlib
import IshikiConj51.Conj51.MetD

open scoped ENNReal

namespace MetD

variable {D E : Type*}

/-- Relabelling along a bijection `σ : D ≃ E` pulls a member of `Met(E)` back
to a member of `Met(D)`.  Both the metric axioms and compatibility with the
discrete topology are preserved: the isolating radius of `σ u` serves as the
isolating radius of `u`. -/
noncomputable def comap (σ : D ≃ E) (e : MetD E) : MetD D :=
  ⟨fun x y => e.1 (σ x) (σ y), by
    obtain ⟨hm, hbot⟩ := e.2
    have hm' : IsMetricOn (fun x y => e.1 (σ x) (σ y)) :=
      { dist_self := fun x => hm.dist_self _
        eq_of_dist_eq_zero := fun {_ _} h => σ.injective (hm.eq_of_dist_eq_zero h)
        dist_comm := fun _ _ => hm.dist_comm _ _
        dist_triangle := fun _ _ _ => hm.dist_triangle _ _ _ }
    refine ⟨hm', ?_⟩
    rw [IsMetricOn.topology_eq_bot_iff]
    intro u
    obtain ⟨ε, hε, hall⟩ := hm.topology_eq_bot_iff.mp hbot (σ u)
    exact ⟨ε, hε, fun v hv => σ.injective (hall (σ v) hv)⟩⟩

@[simp] theorem comap_val (σ : D ≃ E) (e : MetD E) :
    (comap σ e).1 = fun x y => e.1 (σ x) (σ y) := rfl

/-- Relabelling preserves the supremum distance exactly: `σ × σ` reindexes the
supremum bijectively. -/
theorem edist_comap (σ : D ≃ E) (e f : MetD E) :
    edist (comap σ e) (comap σ f) = edist e f := by
  rw [edist_def, edist_def]
  simp only [comap_val]
  exact Equiv.iSup_comp (g := fun q : E × E => ENNReal.ofReal |e.1 q.1 q.2 - f.1 q.1 q.2|)
    (σ.prodCongr σ)

/-- `Met(E) ≃ Met(D)` for any bijection `σ : D ≃ E`. -/
noncomputable def relabelEquiv (σ : D ≃ E) : MetD E ≃ MetD D where
  toFun := comap σ
  invFun := comap σ.symm
  left_inv e := Subtype.ext (by funext x y; simp)
  right_inv f := Subtype.ext (by funext x y; simp)

@[simp] theorem relabelEquiv_apply (σ : D ≃ E) (e : MetD E) :
    relabelEquiv σ e = comap σ e := rfl

/-- The relabelling bijection is an isometry of the supremum distance, hence a
homeomorphism `Met(E) ≃ₜ Met(D)`. -/
noncomputable def relabelIsometry (σ : D ≃ E) : MetD E ≃ᵢ MetD D where
  toEquiv := relabelEquiv σ
  isometry_toFun e f := edist_comap σ e f

end MetD
