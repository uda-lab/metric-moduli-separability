# Literature Notes

Status: references being verified — do not cite without checking.

---

## Primary source

### Ishiki (2024) — arXiv:2407.03030

| Field | Value |
|-------|-------|
| Author | Ishiki, Yoshito |
| Title | *An isometric extensor of metrics* |
| Year | 2024 |
| arXiv | [2407.03030](https://arxiv.org/abs/2407.03030) |
| Venue | (under verification — not yet confirmed journal/proceedings) |
| Conjecture 5.1 location | (page / theorem number under verification) |
| Status | **arXiv number confirmed by project initiator; statement and location under verification** |

**Action required (Issue #1):** Read arXiv:2407.03030, confirm the exact statement
of Conjecture 5.1, and record the page/theorem location here.

---

## Background results needed

| Result | Proposed source | Verified? |
|--------|-----------------|-----------|
| Alexandrov's theorem: a subspace of a Polish space is Polish iff it is Gδ | Kechris, *Classical Descriptive Set Theory*, Thm. 3.11 | ⬜ |
| Closed subspace of a completely metrizable space is completely metrizable | Standard (consequence of Alexandrov or direct argument) | ⬜ |
| Every uncountable closed subset of ℝ has cardinality **c** (continuum) | Perfect set theorem; Kechris §6 or Kunen | ⬜ |
| Every Gδ subset of a Polish space is Polish (Alexandrov) | Kechris, Thm. 3.11 | ⬜ |

---

## Mathlib coverage (v4.32.2)

| Result | Mathlib identifier | Status |
|--------|-------------------|--------|
| `IsPolishSpace` | `Mathlib.Topology.Polish.Basic` | available — preferred for "Polish space" |
| `CompleteSpace` / `PseudoMetricSpace` | `Mathlib.Topology.UniformSpace.*` | available |
| Cardinals / `Cardinal.aleph` | `Mathlib.SetTheory.Cardinal.Aleph` | available |
| Gδ: `IsGdelta` | `Mathlib.Topology.GDelta.Basic` | available |
| Closed subspace of Polish is Polish | `IsPolishSpace.isClosed_univ` or similar | **verify** |
| `IsFSigma` predicate | — | **absent** — defined locally in `Conj51/Cardinality.lean` |

---

*Update this file whenever a reference is located or verified.*
