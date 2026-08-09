# Project Status

**Updated:** 2026-08-09

## Overall

| Item | Status |
|------|--------|
| Conjecture statement verified (arXiv:2407.03030) | ✅ done |
| LEM-A-EXISTS audited | ✅ done |
| Gδ / complete-metrizability implication audited | ✅ done |
| Star-metric construction written | ✅ done |
| Closed-embedding argument audited | ✅ done |
| Japanese report complete | ✅ done |
| Met(D) type defined in Lean | ✅ done |
| Lean formalisation complete | ⬜ pending |
| English paper drafted | ⬜ pending |
| Independent end-to-end review | ⬜ pending |

## Proof candidate

The proposed argument for THM-CONJ51 proceeds through six steps:

1. **LEM-A-EXISTS** — ZFC existence of A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
2. Y = [0,1] \ A is not Gδ in [0,1] (Fσ/Gδ complement duality), hence not
   completely metrizable (Alexandrov–Lavrentiev, applied to the separable
   ambient space [0,1] only).
3. A parameterised star-type family of compatible metrics on D
   (**LEM-STAR-METRIC**) — explicitly: a reference pair {p,q} at distance
   1+t, plus one star per element of A with centre-to-endpoint distance
   s_n(α,t) = min(1, |t−a_α| + 1/n).
4. A bi-Lipschitz embedding Y → Met(D): |t−s| ≤ ρ(d_t,d_s) ≤ 2|t−s|.
5. The image is closed in Met(D) (**LEM-CLOSED-IMAGE**) — the reference pair
   recovers the limit parameter t, and d_t ceasing to be compatible for
   t ∈ A rules out the boundary case.
6. A closed subspace of a completely metrizable space is completely
   metrizable — proved directly (no separability needed, since Met(D) is
   not separable) — contradiction (**THM-CONJ51**).

**Note on Met(D):** Met(D) denotes metrics on D *compatible with the discrete
topology*, not all metrics on the underlying set. Met(D) is not separable;
see `notes/literature.md` and `notes/proof-audit.md` (Issue #4) for why this
matters for step 6.

All six steps are now written out in full in `report/report-ja.md`
(2026-08-09); no mathematically unwritten step remains. Steps 1–2 and 6
(LEM-A-EXISTS; the Gδ / complete-metrizability implication; closed-subspace
inheritance) additionally completed an internal audit (Issues #3, #4). Steps
3–5 (LEM-STAR-METRIC, LEM-CLOSED-IMAGE, report §3.1–§3.8) are newly written
and have had no review beyond the PR review for Issue #5.

The argument remains a **proof candidate**: end-to-end independent review
(Issue #10) and the Lean formalisation (Issues #6–#9) are both outstanding,
so the conjecture must not be described externally as solved.

## Open obligations

See `notes/proof-audit.md` for detailed open items.

## Lean

Lean project initialised (Mathlib v4.32.2, `lean/lakefile.toml`).
`lem_A_exists` (LEM-A-EXISTS) is now **sorry-free** (Issue #8, 2026-08-09;
`#print axioms` shows only `[propext, Classical.choice, Quot.sound]`). `Met(D)`
is now constructed as `MetD` (`IshikiConj51/Conj51/MetD.lean`; relocated there
from `MainTheorem.lean` in Issue #7 so the claim modules can import it), with a
sorry-free `EMetricSpace` instance matching the source's (extended) supremum
distance, unblocking Lean statements for the remaining claim IDs. `THM-CONJ51`
itself is now stated (`thm_conj51`, with a tracked `sorry` for the proof).
LEM-STAR-METRIC is now stated and **sorry-free** (`lem_star_metric`,
`IshikiConj51/Conj51/MetricConstruction.lean`, Issue #7, 2026-08-09);
LEM-CLOSED-IMAGE is now stated and **sorry-free** (`lem_closed_image`,
`IshikiConj51/Conj51/ClosedEmbedding.lean`, Issue #9, 2026-08-09), together
with a supporting new module `IshikiConj51/Conj51/Relabel.lean` (`Met(D)`
transports along any bijection of the index set, so the concrete
`StarIndex A` construction reaches an arbitrary `D` of the same cardinality).

**Every claim ID now has a Lean statement, and the repository contains
exactly one `sorry`:** `thm_conj51`. The whole of report §4 is assembled and
proved in `thm_conj51_of_lavrentiev` (Issue #9), which differs from
`thm_conj51` only by carrying the Alexandrov–Lavrentiev direction as an
explicit hypothesis about subsets of ℝ. Discharging that hypothesis is
Issue #23; when it lands, `thm_conj51` becomes a one-line application. Until
then the Lean chain is **not** complete, and the conjecture must still not be
described as solved. See `notes/proof-audit.md` sorry tracker.

A Mathlib v4.32.2 inventory for Issues #7–#9 is recorded in
`notes/proof-audit.md`'s Mathlib library gaps table (Issue #19): the
Alexandrov–Lavrentiev direction needed for the closed-subspace obstruction
(a completely metrizable subspace is Gδ in its ambient space) is **confirmed
absent** from Mathlib (re-confirmed in Issue #9) and must be proved from
scratch — now tracked as its own Issue #23; the
Cantor–Bendixson theorem, perfect-set cardinality-continuum fact, `ℵ₁ ≤ 𝔠`,
and closed-subspace-of-complete-space are all confirmed **available** with
exact declaration names recorded.

## GitHub Issue work queue

1. #2 Verify Conjecture 5.1 statement and bibliography
2. #3 Audit LEM-A-EXISTS in ZFC
3. #4 Audit the Gδ / complete-metrizability step
4. #5 Complete the self-contained Japanese proof report
5. #6 Define Met(D) in Lean and state THM-CONJ51 faithfully
6. #7 Implement LEM-STAR-METRIC in Lean
7. #8 Formalise cardinality and descriptive-set prerequisites in Lean
8. #9 Formalise LEM-CLOSED-IMAGE and the final obstruction
9. #10 Perform independent end-to-end mathematical review
10. #11 Draft the English paper after mathematical audit passes
11. #19 Record Mathlib inventory findings for Lean formalisation prep (Issues #7–#9)
12. #23 Formalise the Alexandrov–Lavrentiev direction (completely metrizable subspace ⟹ Gδ)
