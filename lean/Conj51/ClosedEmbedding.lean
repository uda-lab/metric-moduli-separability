-- Conj51.ClosedEmbedding
-- Formalises the bi-Lipschitz embedding Y → Met(D) and proves its image
-- is closed.
--
-- Key claim: LEM-CLOSED-IMAGE
--   The map φ : Y → Met(D), t ↦ d_t, is a bi-Lipschitz embedding
--   whose image is closed in Met(D).
--
-- Status: sorry-stub pending audit.

import Mathlib
import IshikiConj51.Conj51.MetricConstruction

/-- LEM-CLOSED-IMAGE: The parameterised metric family induces a bi-Lipschitz
    embedding of Y into Met(D) with closed image.
    Precise statement: the map φ : Y → PseudoMetricSpace D, t ↦ d_t constructed
    in MetricConstruction is a topological embedding whose image is a closed subset.
    This is a placeholder — the exact type signature will be refined once
    LEM-STAR-METRIC provides a concrete metric family.
    Status: SORRY — proof pending audit of LEM-STAR-METRIC and construction. -/
theorem lem_closed_image
    (A : Set ℝ) (hA₁ : A ⊆ Set.Icc 0 1) (hA₂ : #A = Cardinal.aleph 1)
    (hA₃ : ¬ IsSigmaCompact A) :
    -- Placeholder: the actual claim is about the embedding Y → Met(D) being
    -- bi-Lipschitz with closed image.  Stated as True until the metric space
    -- for Met(D) is set up in Lean.
    True := by
  sorry
