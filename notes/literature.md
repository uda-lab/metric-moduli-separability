# Literature Notes

Status: primary source and directly cited literature verified against the
arXiv v4 PDF (Issue #2, 2026-08-09). Update this file if the primary source
is revised to a new version.

---

## Primary source

### Ishiki (2024) — arXiv:2407.03030

| Field | Value |
|-------|-------|
| Author | Ishiki, Yoshito |
| Title | *An isometric extensor of metrics* |
| Year | 2024 (v1: 2024-07-03; v2: 2024-07-16; v3: 2024-07-29; v4: 2024-09-20, current) |
| arXiv | [2407.03030](https://arxiv.org/abs/2407.03030) (math.MG) |
| Venue | None — arXiv preprint only, no journal/proceedings listed on the abstract page (arXiv-issued DOI via DataCite only) |
| Conjecture 5.1 location | Section 5 ("Questions"), p. 32 of the v4 PDF, stated immediately after the discussion of Koshino's theorem |
| Status | **Verified against the v4 PDF full text** |

**Exact statement (Conjecture 5.1, verbatim from the v4 PDF, p. 32):**

> Recall that ℵ₁ stands for the first uncountable cardinality, and let
> $D_{\aleph_1}$ denote the discrete space of cardinality of ℵ₁. Under this
> notation, the space $\operatorname{Met}(D_{\aleph_1})$ is not completely
> metrizable.

Immediately preceding context (p. 32): Koshino [29] proved that for
*separable* $X$, $\operatorname{Met}(X)$ is completely metrizable iff $X$ is
σ-compact. Conjecture 5.1 is proposed to remove the separability hypothesis.
Immediately following context: the author notes that a non-separable
metrizable $X$ contains $D_{\aleph_1}$ as a closed subset, so by Theorem 1.1
(the paper's main isometric-extensor result) $\operatorname{Met}(X)$ contains
$\operatorname{Met}(D_{\aleph_1})$ as a closed subset; if Conjecture 5.1 holds,
$\operatorname{Met}(X)$ would then fail to be completely metrizable, which is
the author's stated reason for supporting the conjecture. This is background
motivation only — it is **not** part of the conjecture statement and is not a
route to a proof of it.

**Definition of $\operatorname{Met}(Z)$ (§1.1, p. 1, verbatim source
paraphrase):** for a metrizable space $Z$, $\operatorname{Met}(Z)$ is "the set
of all metrics on $Z$ that generate the same topology of $Z$," equipped with
the supremum metric $\mathcal{D}_Z(d,e) = \sup_{x,y\in Z} |d(x,y) - e(x,y)|$.
This matches the project's usage: **metrics compatible with (i.e. inducing)
the discrete topology on $D$, under the sup-metric topology.**

**Source-level nuance for the Lean model (acceptance criterion 3):**

- $\operatorname{Met}(Z)$ consists of *ordinary, finite real-valued* metrics
  ($d : Z \times Z \to [0,\infty)$, i.e. codomain is the reals, not the
  extended reals). The paper never uses an extended metric (codomain
  $[0,\infty]$ with $+\infty$ allowed) for $\operatorname{Met}(Z)$ itself.
  Extended-valued objects only appear as the separate, more general class
  $\operatorname{CPM}(X)$ of continuous pseudometrics $d : X\times X \to
  [0,\infty)$ (still finite-valued, merely dropping the triangle-inequality /
  positive-definiteness-only-on-the-diagonal restriction to metric, and
  requiring continuity rather than topology-generation). Consequently a
  faithful Lean model should use Mathlib's finite-valued `MetricSpace` /
  `PseudoMetricSpace` (`dist : α → α → ℝ`), **not** `EMetricSpace`
  (`edist : α → α → ℝ≥0∞`).
- **No boundedness restriction.** $\operatorname{BMet}(Z) \subseteq
  \operatorname{Met}(Z)$ is a strictly smaller, separately named subset for
  bounded metrics; $\operatorname{Met}(Z)$ itself imposes no boundedness. Do
  not silently narrow $\operatorname{Met}(D)$ to bounded metrics.
- **No uniform-discreteness restriction.** Compatibility with the discrete
  topology on $D$ only requires that the metric topology equal the discrete
  topology — equivalently, every singleton is open, i.e. every point has some
  metric ball around it containing only that point. It does **not** require a
  single uniform lower bound on all pairwise distances (uniform discreteness
  is strictly stronger and is not the source's condition). Any Lean
  formalization of "compatible with the discrete topology" must use the
  topology-equality condition, not a uniform-gap condition.
- These two "no silent narrowing" points are the operative constraints for
  Issue #6 (`Met(D)` construction in Lean): the type must range over
  arbitrary (unbounded, non-uniformly-discrete) real-valued metrics on `D`
  that induce the discrete topology.

This matches `README.md` and `report/report-ja.md`, which already state the
"compatible with the discrete topology" / sup-metric-topology definition
correctly; no changes to those files were needed for the conjecture statement
itself.

**Correction:** this file previously read "Action required (Issue #1)" — that
was a stale mis-reference; Issue #1 was the (already-merged) scaffold PR, and
the verification action described belongs to **Issue #2** (this issue), now
complete.

---

## Directly relevant cited literature (verified against the v4 PDF)

### Koshino (2024) — "On the Borel complexity and the complete metrizability of spaces of metrics" [ref. 29]

| Field | Value |
|-------|-------|
| Author | Koshino, K. |
| Title | *On the Borel complexity and the complete metrizability of spaces of metrics* |
| Year | 2024, 5 pages |
| arXiv / DOI | **None given in the citing paper**, and none found via the arXiv API (`export.arxiv.org` search for author Koshino + "metrics" returns no matching title) as of 2026-08-09. Appears to be an unpublished manuscript/preprint not deposited on arXiv at the time Ishiki's paper cites it. |
| Role | States, for separable $X$, that $\operatorname{Met}(X)$ is completely metrizable iff $X$ is σ-compact — the direct motivating result Conjecture 5.1 generalizes (removing separability). |
| Status | Bibliographic metadata as cited is verified (title/author match the citing paper's reference list); independent arXiv/DOI confirmation was **not possible** with the tools available in this environment (general web search is disabled here; the Semantic Scholar API returned HTTP 429 for every retry; NASA ADS renders citation data client-side and returned empty content to the fetch tool). Flagged for re-check if this precise reference becomes load-bearing for a proof step. |

### Koshino (2022) — "Recognizing the topologies of spaces of metrics with the topology of uniform convergence" [ref. 28]

| Field | Value |
|-------|-------|
| Author | Koshino, K. |
| Title | *Recognizing the topologies of spaces of metrics with the topology of uniform convergence* |
| Venue | Bull. Pol. Acad. Sci. Math. **70** (2022), no. 2, 165–171 |
| DOI | 10.4064/ba220523-18-4 |
| Status | Verified against the v4 PDF reference list |

### Ishiki (2024) — "Spaces of metrics are Baire" [ref. 24]

| Field | Value |
|-------|-------|
| Author | Ishiki, Yoshito |
| Title | *Spaces of metrics are Baire* |
| arXiv | [2402.04565](https://arxiv.org/abs/2402.04565) (v1: 2024-02-07, current v3: 2024-06-01) |
| Venue | None — arXiv preprint only |
| Role | Proves $\operatorname{Met}(X)$ is comeager in $\operatorname{CPM}(X)$; used in the proof of the primary source's Theorem 1.1 ("furthermore" part), which in turn is the basis for the closed-image fact used in the project's own proof sketch step 5 (LEM-CLOSED-IMAGE draws on the same closed-subset-of-Met idea). Not itself a source of any project claim ID, but directly relevant background. |
| Status | Verified against the arXiv abstract page |

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
