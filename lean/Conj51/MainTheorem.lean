-- Conj51.MainTheorem
-- Assembles the formalisation of Ishiki Conjecture 5.1.
--
-- THM-CONJ51: For |D| = ℵ₁, Met(D) is not completely metrizable.
--
-- Proof structure:
--   1. LEM-A-EXISTS    → A ⊆ [0,1], |A| = ℵ₁, A not Fσ
--   2. Y = [0,1] \ A not Gδ  → Y not completely metrizable
--   3. LEM-STAR-METRIC         → metric family on D
--   4. LEM-CLOSED-IMAGE        → bi-Lipschitz closed embedding Y → Met(D)
--   5. Closed subspace obstruction → contradiction
--
-- Status: sorry-stub pending all lemmas.

import Mathlib
import IshikiConj51.Conj51.Cardinality
import IshikiConj51.Conj51.MetricConstruction
import IshikiConj51.Conj51.ClosedEmbedding

/-- THM-CONJ51 (Ishiki Conjecture 5.1 — proof candidate):
    Let D be a discrete space of cardinality ℵ₁.
    Then Met(D), equipped with the supremum-metric topology,
    is not completely metrizable.

    Note on Lean statement: formalising "Met(D) is not completely metrizable"
    requires first constructing a suitable type for Met(D) (the space of metrics
    on D with the supremum topology) and the correct notion of complete
    metrizability for that type.  As a placeholder we assert False with sorry,
    which is replaced with a properly typed statement once LEM-CLOSED-IMAGE
    is in place.

    Status: SORRY — all lemmas pending independent audit. -/
theorem thm_conj51
    (D : Type*) [TopologicalSpace D] [DiscreteTopology D]
    (hD : #D = Cardinal.aleph 1) :
    -- TODO: replace with the correct statement once Met(D) is formalised.
    -- The intended claim is: the type of metrics on D with the sup-metric
    -- topology does not admit a complete metric.
    False := by
  sorry
