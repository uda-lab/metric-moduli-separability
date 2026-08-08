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
| LEM-A-EXISTS | ∃ A ⊆ [0,1], \|A\| = ℵ₁, A not Fσ | ⬜ not audited | See case-split sketch in report §3; both CH and non-CH cases need verification |
| — | Y = [0,1] \ A not Gδ → not completely metrizable | ⬜ not audited | Needs Alexandrov's theorem reference confirmed |
| LEM-STAR-METRIC | Star-type family of compatible metrics on D parametrised by Y | ⬜ not written | Construction not yet written; blocked on mathematical audit |
| LEM-CLOSED-IMAGE | Bi-Lipschitz embedding with closed image | ⬜ not written | Blocked on LEM-STAR-METRIC and Met(D) type in Lean |
| THM-CONJ51 | Full assembly | ⬜ not written | Blocked on all above |

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

## Lean sorry tracker

| File | Declaration | Claim ID | Priority |
|------|-------------|----------|----------|
| `IshikiConj51/Conj51/Cardinality.lean` | `lem_A_exists` | LEM-A-EXISTS | high |

No `sorry` must remain in the final formalisation.

## Lean TODO tracker (no theorem statement yet)

The following claim IDs do **not** yet have Lean theorem statements because
the required mathematical objects (notably the `Met(D)` type) are not yet
formalised.  The stable IDs will be attached to theorems only once the
statements faithfully represent the mathematical claims.

| File | Claim ID | Blocked on |
|------|----------|------------|
| `IshikiConj51/Conj51/MetricConstruction.lean` | LEM-STAR-METRIC | star-type construction + audit |
| `IshikiConj51/Conj51/ClosedEmbedding.lean` | LEM-CLOSED-IMAGE | LEM-STAR-METRIC + Met(D) type |
| `IshikiConj51/Conj51/MainTheorem.lean` | THM-CONJ51 | all above + Met(D) type |

## Mathlib library gaps (v4.32.2)

| Gap | Description | File | Status |
|-----|-------------|------|--------|
| `IsFSigma` predicate | No canonical Mathlib built-in; defined locally as `∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n`. | `IshikiConj51/Conj51/Cardinality.lean` | open |
| `Met(D)` as a type | No Mathlib type for the space of compatible metrics on D with the sup-metric topology.  Must be constructed explicitly. | `IshikiConj51/Conj51/MainTheorem.lean` | open |
