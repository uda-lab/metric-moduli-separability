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
| LEM-A-EXISTS | ∃ A ⊆ [0,1], \|A\| = ℵ₁, A not Fσ | ✅ audited (2026-08-09) | See report §3; CH case via irrationals + Baire category, non-CH case via the perfect-set-theorem counting argument. Lean proof still pending (`sorry`), tracked below. |
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

### [2026-08-09] LEM-A-EXISTS — non-CH branch was incomplete, now fixed

- **Finding.** The report's previous non-CH branch sketch (§3, pre-audit) tried
  to derive a contradiction "directly from the Fσ structure" without
  specifying the mechanism, and explicitly flagged this step as "要検証"
  (needs verification). As written, no contradiction was actually
  demonstrated — it observed that a candidate closed superset could have
  cardinality up to 𝔠 without immediately explaining why that is
  impossible for a set of the required cardinality ℵ₁.
- **Fix.** Replaced with a complete counting argument: if ℵ₁ < 𝔠, then
  *any* A ⊆ [0,1] with |A| = ℵ₁ is automatically not Fσ, because every
  Fσ-piece F_n ⊆ A satisfies |F_n| ≤ ℵ₁ < 𝔠, so by the perfect set theorem
  (an uncountable closed subset of [0,1] has cardinality 𝔠, a consequence
  of the Cantor–Bendixson theorem) each F_n must be countable, making
  A = ⋃F_n countable — contradicting |A| = ℵ₁. This requires no
  case-specific set (e.g. no Bernstein-set construction), only the
  cardinality bound ℵ₁ < 𝔠 and the existence of *some* ℵ₁-sized subset of
  [0,1] (always true since ℵ₁ ≤ 𝔠 in ZFC).
- **Note on the CH branch.** The CH branch's argument (irrationals ∩ [0,1],
  not Fσ by the Baire category theorem) was already correct as stated and
  is independent of CH — CH is only used to get |irrationals ∩ [0,1]| = 𝔠
  = ℵ₁. No change was needed there beyond adding precise references.
- **Not used: uniform Bernstein-set argument.** A single construction
  working uniformly across both CH and ¬CH (e.g., enumerating all perfect
  subsets of [0,1] via transfinite recursion and diagonalizing against
  them) was considered as an alternative that avoids the case split, but
  was not pursued: it requires more machinery (transfinite recursion over
  up to 𝔠-many perfect sets) for no proof-strength gain over the
  elementary two-case argument above, which is already fully rigorous.
  Left as a remark in case a future audit prefers a case-split-free proof.

---

## Lean sorry tracker

| File | Declaration | Claim ID | Priority | Notes |
|------|-------------|----------|----------|-------|
| `IshikiConj51/Conj51/Cardinality.lean` | `lem_A_exists` | LEM-A-EXISTS | high | Mathematical audit complete (report §3, 2026-08-09); Lean formalisation of the two-case argument is still open (Issue #8). |

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
