# Proof Audit

This file records:
- Open proof obligations
- Failed or abandoned proof attempts
- Independent audit findings

Do not record research history in the main report or paper.

---

## Open obligations

| ID | Claim | Status | Notes |
|----|-------|--------|-------|
| LEM-A-EXISTS | ∃ A ⊆ [0,1], \|A\| = ℵ₁, A not Fσ | ⬜ not audited | CH non-assumption case unclear |
| — | Y = [0,1] \ A not Gδ → not completely metrizable | ⬜ not audited | Needs precise Alexandrov reference |
| LEM-STAR-METRIC | Star-type metric family construction | ⬜ not audited | Construction not yet written |
| LEM-CLOSED-IMAGE | Bi-Lipschitz embedding with closed image | ⬜ not audited | Depends on LEM-STAR-METRIC |
| THM-CONJ51 | Full assembly | ⬜ not audited | Depends on all above |

---

## Failed / abandoned attempts

*(none yet — add entries here as attempts are made and abandoned)*

Template:
```
### [Date] Attempt: <short description>
- Approach: ...
- Why it failed: ...
- What was learned: ...
```

---

## Audit findings

*(none yet)*

---

## sorry tracker (Lean)

| File | Line | Claim | Priority |
|------|------|-------|----------|
| `Conj51/Cardinality.lean` | `lem_A_exists` | LEM-A-EXISTS | high |
| `Conj51/MetricConstruction.lean` | `lem_star_metric` | LEM-STAR-METRIC | high |
| `Conj51/ClosedEmbedding.lean` | `lem_closed_image` | LEM-CLOSED-IMAGE | high |
| `Conj51/MainTheorem.lean` | `thm_conj51` | THM-CONJ51 | highest |

No `sorry` must remain in the final formalisation.

## Mathlib library gaps

| Gap | Description | File | Status |
|-----|-------------|------|--------|
| `IsFSigma` predicate | Mathlib v4.32.2 has no single `IsFSigma` predicate; the definition is inlined in `Cardinality.lean` as `∃ (F : ℕ → Set ℝ), (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n`. Verify before formalisation whether a better match exists. | `Conj51/Cardinality.lean` | open |
| Met(D) type | There is no canonical Lean/Mathlib type for the space of metrics on D with the sup-metric topology.  Needs explicit construction before `thm_conj51` can be given a correct type. | `Conj51/MainTheorem.lean` | open |
