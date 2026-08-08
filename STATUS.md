# Project Status

**Updated:** 2026-08-08

## Overall

| Item | Status |
|------|--------|
| Conjecture statement verified | ⬜ pending |
| LEM-A-EXISTS audited | ⬜ pending |
| Gδ / complete-metrizability implication audited | ⬜ pending |
| Star-metric construction written | ⬜ pending |
| Closed-embedding argument audited | ⬜ pending |
| Japanese report complete | ⬜ pending |
| Lean formalisation complete | ⬜ pending |
| English paper drafted | ⬜ pending |
| Independent end-to-end review | ⬜ pending |

## Proof candidate

The proposed argument proceeds through six steps:

1. **LEM-A-EXISTS** — ZFC existence of A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
2. Y = [0,1] \ A is not Gδ, hence not completely metrizable.
3. A parameterised star-type family of metrics on D (**LEM-STAR-METRIC**).
4. A bi-Lipschitz embedding Y → Met(D).
5. The image is closed in Met(D) (**LEM-CLOSED-IMAGE**).
6. Closed subspace of a completely metrizable space is completely metrizable —
   contradiction (**THM-CONJ51**).

None of these steps has completed independent audit yet.

## Open obligations

See `notes/proof-audit.md` for detailed open items.

## Lean

Lean project initialised; all theorems are `sorry`-stubs pending formalisation.
