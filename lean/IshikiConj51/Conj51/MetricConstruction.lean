-- Conj51.MetricConstruction
-- Placeholder module for the star-type metric family construction.
--
-- Target claim (LEM-STAR-METRIC):
--   Let D be a discrete space, |D| = ℵ₁, and let Y = [0,1] \ A where A is
--   the set from LEM-A-EXISTS.  There exists a family {d_t}_{t ∈ Y} of metrics
--   on D, each compatible with the discrete topology on D, such that the
--   induced map φ : Y → Met(D), t ↦ d_t, is bi-Lipschitz.
--
-- The theorem named `lem_star_metric` will be stated here only once:
--   (a) the star-type metric construction is written down and audited, and
--   (b) `Met(D)` has been defined as a type in Lean (see MainTheorem.lean).
-- Until then this file holds only the import and a comment skeleton.
--
-- See notes/proof-audit.md for the open proof obligation and sorry tracker.

import Mathlib
import IshikiConj51.Conj51.Cardinality

-- TODO (LEM-STAR-METRIC): Define the star-type metric family on D
-- parametrised by Y, prove bi-Lipschitz properties, and state the lemma.
