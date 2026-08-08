-- Conj51.MainTheorem
--
-- States `THM-CONJ51`.
--
-- `MetD D` — the Lean representation of the source's `Met(D)` (Ishiki,
-- arXiv:2407.03030, §1.1; verified in Issue #2) — was introduced here by
-- Issue #6 and now lives, unchanged, in `Conj51/MetD.lean`.  It had to move
-- to a module the claim files can import: this file imports
-- `MetricConstruction.lean` and `ClosedEmbedding.lean`, and those are exactly
-- the modules that construct elements of `Met(D)`.  See `MetD.lean` for the
-- source-faithfulness notes on `IsMetricOn`, the `.topology = ⊥` condition,
-- and the extended-valued supremum distance.
--
-- Source-faithfulness note specific to this file:
--   * "Completely metrizable" is the ordinary (finite-metric)
--     notion applied to the *topology* `MetD D` carries — Mathlib's
--     `TopologicalSpace.IsCompletelyMetrizableSpace` asks only whether some
--     compatible finite-valued `MetricSpace` structure realises that
--     topology completely; it does not require the topology to have been
--     built from a finite-valued distance in the first place.
--
-- Status: `thm_conj51`'s statement is complete and sorry-free; its *proof*
-- carries a tracked `sorry` (see notes/proof-audit.md sorry tracker).
-- LEM-STAR-METRIC (Issue #7) is now proved in `MetricConstruction.lean`;
-- LEM-CLOSED-IMAGE (Issue #9) is still open, so the assembly cannot be
-- completed here yet.

import Mathlib
import IshikiConj51.Conj51.MetD
import IshikiConj51.Conj51.Cardinality
import IshikiConj51.Conj51.MetricConstruction
import IshikiConj51.Conj51.ClosedEmbedding

open Cardinal
open scoped ENNReal


/-- **THM-CONJ51.** For a discrete space `D` of cardinality `ℵ₁`,
`Met(D)` — equipped with the supremum-metric topology — is not completely
metrizable.

This matches the report's (`report/report-ja.md` §2) and the source's
(Ishiki, arXiv:2407.03030, Conjecture 5.1) statement exactly: no bounded,
uniformly-discrete, or otherwise weakened proxy is substituted.

Status: statement only. The proof depends on LEM-A-EXISTS
(`Cardinality.lean`), LEM-STAR-METRIC (proved, `MetricConstruction.lean`,
Issue #7), LEM-CLOSED-IMAGE (still open, `ClosedEmbedding.lean`, Issue #9),
and the closed-subspace-inheritance argument audited in Issue #4. Tracked as
a `sorry` in notes/proof-audit.md; not claimed as proved. -/
theorem thm_conj51 (D : Type*) (hD : #D = Cardinal.aleph 1) :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D) := by
  sorry
