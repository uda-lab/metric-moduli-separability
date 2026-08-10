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

- **Each element of $\operatorname{Met}(Z)$ is an ordinary, finite real-valued
  metric on $Z$** ($d : Z \times Z \to [0,\infty)$): a genuine metric
  satisfying the triangle inequality and $d(x,y)=0 \iff x=y$, with no
  individual value equal to $+\infty$. So each member of $\operatorname{Met}(D)$
  is faithfully modeled by Mathlib's `MetricSpace` (`dist : α → α → ℝ`) on
  `D`, not `EMetricSpace`.
- **The ambient supremum distance on the space $\operatorname{Met}(Z)$ itself
  is genuinely extended-valued.** $\mathcal{D}_Z(d,e) = \sup_{x,y}
  |d(x,y)-e(x,y)|$ can equal $+\infty$ when $d,e$ are unbounded and differ
  unboundedly — e.g. on $\mathbb{N}$, $d(m,n)=|m-n|$ and $e(m,n)=|2^m-2^n|$
  give $\mathcal{D}(d,e)=\infty$. The source paper confirms this explicitly in
  §2.2 ("Components of spaces of metrics", p. 4): it defines $d \sim e
  \iff \mathcal{D}_Z(d,e) < \infty$ as an equivalence relation, writes
  $\mathbf{M}_{<\infty}(Z) = \operatorname{Met}(Z)/{\sim}$, and notes each
  class in $\mathbf{M}_{<\infty}(Z)$ is a (path-)connected **clopen** subset
  of $\operatorname{Met}(Z)$ — i.e. $\operatorname{Met}(Z)$ is *not* a single
  finite-distance metric space; it is a disjoint union of clopen
  finite-distance components. **A faithful Lean model of "$\operatorname{Met}(D)$
  with the sup-metric topology" therefore needs an extended metric
  (`EMetricSpace`, `edist : α → α → ℝ≥0∞`) on $\operatorname{Met}(D)$ itself
  (or an equivalent topology built from the clopen-component decomposition
  above) — even though each individual metric `d : D → D → ℝ` in
  $\operatorname{Met}(D)$ is finite-valued.** Do not conflate the two levels:
  finite-valued metrics *on* `D`, extended-valued sup-distance *on the space
  of metrics* $\operatorname{Met}(D)$.
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
| Author | Koshino, Katsuhisa |
| Title | *On the Borel complexity and the complete metrizability of spaces of metrics* |
| Venue | Anal. Geom. Metr. Spaces **12** (2024), no. 1, art. 20240014 (published 2024-11-11, CC-BY 4.0) |
| DOI / arXiv | [10.1515/agms-2024-0014](https://doi.org/10.1515/agms-2024-0014); [arXiv:2403.07421](https://arxiv.org/abs/2403.07421) (v1: 2024-03-12, v2: 2024-04-07, math.GN) |
| Role | A direct motivation for Conjecture 5.1, which addresses the least uncountable discrete case of the nonseparable problem. |
| Statement caveat | The published paper studies $AM(X)$ = **bounded** admissible (continuous) metrics with the sup-metric. Its main **Theorem and Corollary are unnumbered** ("Theorem." / "Corollary."). The Corollary (verbatim, arXiv v2 p. 2 = published version): "Let $X$ be a separable metrizable space. Then $X$ is $\sigma$-compact if and only if $AM(X)$ is completely metrizable." The $\operatorname{Met}(X)$ form is how Ishiki (arXiv:2407.03030, §5) recalls the result; the paper cites Koshino for the $AM(X)$ statement and attributes the $\operatorname{Met}(X)$ form to Ishiki's recollection — do not silently identify the two spaces. |
| Status | **Verified against the arXiv v2 PDF full text and the Crossref record of the DOI** (2026-08-10, Issue #36). Supersedes the 2026-08-09 "no arXiv/DOI found" record: the earlier arXiv API search missed the deposit (primary class math.GN). Now cited directly as `Koshino2024` in `paper/references.bib`. |

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
| Alexandrov–Lavrentiev, forward direction: X metrizable, S ⊆ X completely metrizable ⇒ S is Gδ in X (no separability on X) | Kechris, *Classical Descriptive Set Theory*, Thm. 3.11 (§3.C, p. 17) — stated there in exactly this metrizable-X generality; general form also in Engelking, *General Topology*, Thm. 4.3.23–4.3.24; Willard, *General Topology*, Thm. 24.12, p. 179 | ✅ Engelking/Willard citations independently verified (Issue #4, 2026-08-09); Kechris Thm. 3.11 verified at full-statement level against a numbering-preserving transcription of the book (Issue #27 / E10, 2026-08-09 — see below), and re-confirmed with section/page (§3.C starting p. 17, via the book's printed table of contents, d-nb.info/941717364/04) in Issue #34 (2026-08-09); report 定理 1.1 and paper Thm. 2.1 now state this metrizable-X form and cite Kechris as primary |
| Closed subspace of a completely metrizable space is completely metrizable — no separability needed | Elementary direct argument (a complete metric restricted to a closed subset is complete); see report §1 定理 1.2 | ✅ audited (Issue #4, 2026-08-09) — this is the version actually used for Met(D), since Met(D) is not separable |
| Every uncountable closed subset of ℝ has cardinality **c** (continuum) — perfect set theorem | Cantor–Bendixson theorem, Kechris, *Classical Descriptive Set Theory* (GTM 156, 1995), §6 (Thm. 6.4 in §6.B, from p. 32; Thm. 6.2/Cor. 6.3 in §6.A, from p. 31; section pages re-confirmed via the printed table of contents in Issue #34) | ✅ used in report 補題 3.1, applied in the non-CH branch of 補題 3.2 (= LEM-A-EXISTS) (Issue #3, 2026-08-09) |

### References verified for the Gδ / complete-metrizability step (Issue #4, 2026-08-09)

| Result | Source | Role |
|--------|--------|------|
| Gδ characterisation of completely metrizable subspaces, general (not-necessarily-separable) form | Engelking, *General Topology*, revised ed., Thm. 4.3.23–4.3.24, p. 274; Willard, *General Topology*, Thm. 24.12, p. 179 | Confirms a Gδ-style theorem exists even without separability, though the report does not rely on it for Met(D) — see below |
| Elementary fact: a closed subset of a complete metric space is complete (with the restricted metric) | Standard, elementary (proof included directly in report §1, background theorem 2); no non-elementary citation needed | Used for the Met(D) closed-subspace step (report §4 step 5), specifically because it needs no separability hypothesis |
| Fσ/Gδ complement duality (De Morgan) | Elementary, immediate from the definitions; no external citation needed | Report §4 step 2 |

**On why the report avoids applying the general Engelking/Willard theorem to
Met(D) despite it not requiring separability:** using the elementary closed-
subspace argument is simpler and fully self-contained for what step 5 needs
(only closed sets, not general Gδ sets), and avoids depending on a citation
whose exact scope (e.g. whether it is stated for arbitrary — possibly very
large or exotic — metric spaces, or with implicit hypotheses) I have not
independently audited beyond the one Wikipedia-sourced citation above. The
original report bug was citing a **Polish-specific** source (implicitly, by
mislabelling "completely metrizable" as "Polish") for a claim about the
non-separable Met(D); the fix does not depend on resolving whether some
general non-separable Gδ theorem also happens to work.

**On Met(D)'s non-separability (used above, not a separate claim ID):** for
$|D|=\aleph_1$, perturbing a base compatible metric independently near each
point of $D$ produces an uncountable subset of $\operatorname{Met}(D)$ whose
elements are pairwise bounded away from each other by a fixed constant, in
the sup-metric $\rho$; a separable metric space cannot contain such an
uncountable uniformly-separated set (a standard fact: any $\varepsilon$-net
of a separable space is countable, and an uncountable $\varepsilon$-separated
set cannot be covered by a countable $\varepsilon/2$-net). This claim is not
formally part of any of the four stable IDs and was not re-derived in full
formal detail here; flagged for double-checking whenever $\operatorname{Met}(D)$
is formally constructed in Lean (Issue #6).

### References verified for LEM-A-EXISTS (Issue #3, 2026-08-09)

| Result | Source | Role |
|--------|--------|------|
| Cantor–Bendixson theorem (every closed subset of a Polish space decomposes as a perfect set plus a countable set) | Kechris, *Classical Descriptive Set Theory*, GTM 156 (Springer, 1995), §6; perfect set property discussed around p. 150 | Non-CH branch: every uncountable closed F ⊆ [0,1] has \|F\| = 𝔠 |
| Baire category theorem (a nonempty complete metric space is not meager in itself) | Kelley, *General Topology*, Theorem 34, p. 200; equivalently Willard, *General Topology*, Corollary 25.4 | CH branch: [0,1] \ ℚ is not Fσ |
| ℵ₁ ≤ 𝔠 and Cantor's theorem ℵ₀ < 𝔠 | Standard ZFC cardinal arithmetic (ℵ₁ is the least uncountable cardinal; 𝔠 = 2^ℵ₀ is uncountable by Cantor's theorem) | Both branches |
| κ infinite, λ ≤ κ countable ⇒ κ = \|A\|+λ forces \|A\|=κ; countable union of countable sets is countable | Standard ZFC cardinal arithmetic (uses countable choice, available in ZFC) | CH branch cardinality count; non-CH branch final contradiction |
| Bernstein set (a set meeting every uncountable closed set, whose complement also meets every uncountable closed set; exists in ZFC by a length-𝔠 transfinite recursion) | Oxtoby, *Measure and Category*, 2nd ed. (Springer GTM 2), p. 24 (definition) | Case-split-free alternative proof (report §3, "別証" remark): a subset of a Bernstein set of size ℵ₁ contains no perfect set, hence is not Fσ by Cantor–Bendixson |

**Update (Issue #27 / E10, 2026-08-09): Kechris theorem numbers verified at
full-statement level.** The previously unpinned numbers are now confirmed
against a full-text transcription of the book that preserves its numbering
(M. Sleziak's "kechris" transcription notes,
`thales.doa.fmph.uniba.sk/sleziak/texty/rozne/pozn/books/kechris.pdf`,
retrieved 2026-08-09), corroborated by independent citing literature:

* **Thm 3.11 = the Alexandrov–Lavrentiev Gδ characterisation.** Transcription
  states verbatim: "If X is metrizable and Y ⊆ X is completely metrizable,
  then Y is a Gδ in X. Conversely, if X is completely metrizable and Y ⊆ X
  is a Gδ, then Y is completely metrizable. In particular, a subspace of a
  Polish space is Polish iff it is a Gδ." Corroboration: arXiv:2010.01573
  (§4) cites "[Kechris], Theorem 3.11" for exactly this (Alexandroff's
  lemma). This covers the direction and the case the paper cites it for
  (paper Theorem 2.1, applied to [0,1]).
* **Thm 6.2 / Cor 6.3 = Cantor-scheme embedding and perfect-set
  cardinality.** "(6.2) Let X be a nonempty perfect Polish space. Then there
  is an embedding of C into X." "(6.3) If X is a nonempty perfect Polish
  space, then card X = 2^ℵ₀. In particular, a nonempty perfect subset of a
  Polish space has the cardinality of the continuum." This is the
  "cardinality 𝔠 via the standard Cantor-scheme embedding" step of the
  paper's Lemma 3.1, Case 2.
* **Thm 6.4 = Cantor–Bendixson, §6.B.** "(6.4) Let X be a Polish space. Then
  X can be uniquely written as X = P ∪ C, with P a perfect subset of X and C
  countable open." Corroborated by multiple descriptive-set-theory sources
  quoting the same numbering.

**Load-bearing status (recorded per the PR #33 codex review).** In the
paper's non-CH branch (Lemma 3.1, Case 2), the perfect subset of an
uncountable closed set is obtained *from the cited Cantor–Bendixson theorem*
— the citation is load-bearing for the natural-language paper, not a
convenience pointer; the paper now cites it number-precisely
(\cite[Theorem 6.4]{Kechris1995}, and \cite[Theorem 6.2, Corollary
6.3]{Kechris1995} for the cardinality step). Independent safety nets, for
the mathematics rather than the bibliography: the Gate B reviewer re-derived
the non-CH branch from scratch (proof-audit, Issue #10 entry §2), and the
Lean chain proves the corresponding step through Mathlib
(`IsClosed.exists_nat_bool_injection_of_not_countable`) with no book
citation. The verification above is of a faithful transcription, not a scan
of the printed book; page numbers are not cited anywhere, so no page-level
check is required.

Original Issue #3 record (kept for provenance): I could not independently pin exact Kechris theorem/page numbers beyond the
"§6 / p. 150" region confirmed via a secondary source (Wikipedia's citation
of Kechris 1995, p. 150 for the perfect set property) — general web search
is unavailable in this environment and I did not have independent access to
paginate the book itself. The Kelley/Willard citations for the Baire category
theorem, and the Oxtoby p. 24 citation for the Bernstein set definition, are
quoted directly from sources that cite them with exact theorem/page numbers,
so those are higher-confidence. An earlier draft of this audit (relayed via
the orchestrator) suggested more specific numbers — Kechris Thm 6.4 / Cor 6.5
for Cantor–Bendixson, Kechris Thm 8.4 for Baire category, Oxtoby Ch. 5 for
Bernstein sets — but those specific numbers could not be independently
confirmed with the tools available in this environment (general web search
disabled; no direct access to paginate either book), so they are intentionally
**not** asserted here to avoid false precision. Re-verify against a
physical/PDF copy of both books before citing exact theorem numbers in the
paper.

**Update (Issue #34, 2026-08-09): citation set finalised for the reader-facing
artifacts.** The report's bibliography is now self-contained (report §5 lists
Ishiki, Kechris, Engelking, Willard, Oxtoby; no pointer to this file). The
Baire category theorem is cited to Willard, Cor. 25.4 only — the redundant
Kelley (Thm. 34, p. 200) citation was dropped from both report and paper, and
the `Kelley1955` entry was removed from `paper/references.bib` (the Kelley
verification record above remains valid as provenance). Kechris Thm. 3.11 is
now the primary citation for the background Gδ theorem in both report (定理
1.1) and paper (Thm. 2.1), stated in its metrizable-X form; its verbatim
statement ("If X is metrizable and Y ⊆ X is completely metrizable, then Y is
a Gδ in X. ...") was re-confirmed against the numbering-preserving
transcription and independent citing literature, and its location (§3.C,
p. 17) against the printed table of contents (d-nb.info/941717364/04).

---

## Mathlib coverage (v4.32.2)

| Result | Mathlib identifier | Status |
|--------|-------------------|--------|
| `IsPolishSpace` | `Mathlib.Topology.Polish.Basic` | available — preferred for "Polish space" |
| `CompleteSpace` / `PseudoMetricSpace` | `Mathlib.Topology.UniformSpace.*` | available |
| Cardinals / `Cardinal.aleph` | `Mathlib.SetTheory.Cardinal.Aleph` | available |
| Gδ: `IsGdelta` | `Mathlib.Topology.GDelta.Basic` | available |
| Closed subspace of Polish is Polish | ~~`IsPolishSpace.isClosed_univ` or similar — verify~~ | superseded (Issue #9 / E10, Issue #27): no Polish-specific lemma needed — the assembly uses `Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace` (no separability hypothesis), see `notes/proof-audit.md` Mathlib gaps table |
| `IsFSigma` predicate | — | **absent** — defined locally in `Conj51/Cardinality.lean` |

---

*Update this file whenever a reference is located or verified.*
