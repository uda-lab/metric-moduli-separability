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
`lem_A_exists` (LEM-A-EXISTS) has a Lean statement (with `sorry`). `Met(D)`
is now constructed as `MetD` (`IshikiConj51/Conj51/MainTheorem.lean`), with a
sorry-free `EMetricSpace` instance matching the source's (extended) supremum
distance, unblocking Lean statements for the remaining claim IDs. `THM-CONJ51`
itself is now stated (`thm_conj51`, with a tracked `sorry` for the proof).
LEM-STAR-METRIC and LEM-CLOSED-IMAGE still have no Lean statement (Issues #7,
#9). See `notes/proof-audit.md` Lean TODO / sorry trackers.

A Mathlib v4.32.2 inventory for Issues #7–#9 is recorded in
`notes/proof-audit.md`'s Mathlib library gaps table (Issue #19): the
Alexandrov–Lavrentiev direction needed for the closed-subspace obstruction
(a completely metrizable subspace is Gδ in its ambient space) is **confirmed
absent** from Mathlib and must be proved from scratch (Issue #9); the
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
