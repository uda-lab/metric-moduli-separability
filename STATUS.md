# Project Status

**Updated:** 2026-08-09

## Overall

| Item | Status |
|------|--------|
| Conjecture statement verified (arXiv:2407.03030) | ✅ done |
| LEM-A-EXISTS audited | ⬜ pending |
| Gδ / complete-metrizability implication audited | ⬜ pending |
| Star-metric construction written | ⬜ pending |
| Closed-embedding argument audited | ⬜ pending |
| Japanese report complete | ⬜ pending |
| Met(D) type defined in Lean | ⬜ pending |
| Lean formalisation complete | ⬜ pending |
| English paper drafted | ⬜ pending |
| Independent end-to-end review | ⬜ pending |

## Proof candidate

The proposed argument for THM-CONJ51 proceeds through six steps:

1. **LEM-A-EXISTS** — ZFC existence of A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
2. Y = [0,1] \ A is not Gδ, hence not completely metrizable (Alexandrov's theorem).
3. A parameterised star-type family of compatible metrics on D (**LEM-STAR-METRIC**).
4. A bi-Lipschitz embedding Y → Met(D).
5. The image is closed in Met(D) (**LEM-CLOSED-IMAGE**).
6. Closed subspace of a completely metrizable space is completely metrizable
   (corollary of Alexandrov) — contradiction (**THM-CONJ51**).

**Note on Met(D):** Met(D) denotes metrics on D *compatible with the discrete
topology*, not all metrics on the underlying set.

None of these steps has completed independent audit yet.

## Open obligations

See `notes/proof-audit.md` for detailed open items.

## Lean

Lean project initialised (Mathlib v4.32.2, `lean/lakefile.toml`).  Only
`lem_A_exists` (LEM-A-EXISTS) has a Lean statement (with `sorry`).  The other
three stable claim IDs (LEM-STAR-METRIC, LEM-CLOSED-IMAGE, THM-CONJ51) do not
yet have Lean statements because the required type for Met(D) has not been
constructed.  See `notes/proof-audit.md` Lean TODO tracker.

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
