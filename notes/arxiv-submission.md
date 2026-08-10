# arXiv v1 Submission — Metadata Draft and Owner Checklist

Issue #38. Manuscript frozen in #36 (merge `36635b9`). The bundle is produced
by `paper/make-arxiv-bundle.sh` (main.tex + main.bbl only; the pre-generated
`main.bbl` is supplied so arXiv's TeX system does not need to process
`references.bib`, which is deliberately excluded). **Agent-side preparation
is complete**; the owner actions below remain — endorsement (Track A),
acknowledgement consent, license choice (Track D), metadata entry (Track C),
the upload/compile/inspect dry run (Track E) — ending with the deliberate
final submit click.

## Track C — metadata (copy into the arXiv submission form)

| Field | Value |
|-------|-------|
| Title | On Ishiki's Conjecture 5.1: Failure of Complete Metrizability of $\mathrm{Met}(D)$ for $\lvert D\rvert = \aleph_1$ |
| Authors | Tomoki Uda (Nanzan University) |
| Primary category | math.GN (General Topology) |
| Cross-list (optional) | math.LO — the proof is ZFC-sensitive (CH case split, cardinal arithmetic); owner's call, not required |
| MSC 2020 (optional) | 54E35 (Primary) 54E50, 54H05 (Secondary) |
| Comments | 11 pages. The argument is machine-checked in the Lean 4 proof assistant. |
| ORCID | 0000-0002-6073-1572 — confirm it is linked to the submitting arXiv account (arXiv account settings), matching the manuscript footnote |
| Journal-ref / DOI | **leave empty** (do not invent) |
| Repository link | **intentionally omitted** (owner decision, 2026-08-10): v1 does not mention the repository anywhere, including metadata |

Abstract (substantively identical to the manuscript abstract; arXiv-flavoured
TeX with macros expanded):

> For a discrete topological space $D$, let $\mathrm{Met}(D)$ denote the set
> of metrics on $D$ that are compatible with the discrete topology, equipped
> with the topology induced by the supremum distance. Ishiki's Conjecture 5.1
> asserts that $\mathrm{Met}(D)$ is not completely metrizable when
> $|D| = \aleph_1$. We prove this in ZFC by constructing a set
> $A \subseteq [0,1]$ of cardinality $\aleph_1$ that is not $F_\sigma$ and
> transporting the resulting non-$G_\delta$ obstruction into
> $\mathrm{Met}(D)$ via an explicit closed embedding. The argument has been
> machine-checked in the Lean 4 proof assistant.

## Track A — endorsement (owner)

1. Log into arXiv, start a new submission, select `math.GN`.
2. If the account is already endorsed / auto-endorsed for math.GN: record
   "endorsement: not required" on issue #38 and continue.
3. If endorsement is required: first confirm the intended endorser is
   eligible — use the "Which of these authors are endorsers?" link at the
   bottom of the abstract page of an arXiv paper of theirs (e.g.
   arXiv:2403.07421 or arXiv:2407.03030 for math.GN). If Yoshito Ishiki is
   eligible, use the arXiv-generated request and send it **privately** to
   him; otherwise pick another personally known, eligible subject-area
   endorser. Record only pass/fail on the issue — never endorsement codes
   or e-mail contents.
4. Endorsement is an arXiv access mechanism, not peer review.

## Track D — license (owner decision; do not delegate)

arXiv offers: (1) arXiv.org perpetual non-exclusive license (minimal),
(2) CC BY 4.0, (3) CC BY-SA 4.0, (4) CC BY-NC-SA 4.0, (5) CC BY-NC-ND 4.0,
(6) CC0.

Consideration for the recorded journal targets (*Topology and its
Applications*, Elsevier; *Fundamenta Mathematicae*): every arXiv license,
including the minimal one, is irrevocable for the posted version. The
**minimal arXiv non-exclusive license** grants arXiv the narrowest rights
and therefore generally preserves the most flexibility for a later
publisher agreement, while CC licenses grant broader reuse rights that some
publishers cannot accommodate; the minimal license is the conservative
default. Verify the target journal's current preprint policy at submission
time. **The choice is the owner's; record it on issue #38 before
submitting.**

## Track E — arXiv dry run (owner, with agent support on failures)

1. Run `paper/make-arxiv-bundle.sh`; upload `paper/arxiv-v1.tar.gz` to an
   incomplete arXiv submission.
2. Let arXiv compile; inspect the compilation log for errors/warnings.
3. Inspect the arXiv-generated PDF **page by page** against the local
   `paper/main.pdf` at `36635b9`: title, author footnote (affiliation,
   e-mail, ORCID link), abstract, all theorem/lemma statements, the
   construction table, references, hyperlinks.
4. If anything differs or fails, report on issue #38 — fixes go through a
   normal PR, then rebuild the bundle and repeat.
5. The arXiv-generated PDF is the authoritative compatibility check.

## Final pre-submit checklist (owner)

- [ ] Endorsement resolved (Track A) — record pass/not-required on #38
- [ ] **Ishiki's consent to being named in the acknowledgement obtained**
      (wording approved in PR #39; consent is the outstanding half)
- [ ] License selected and recorded (Track D)
- [ ] Metadata entered exactly as in Track C
- [ ] arXiv compile clean; generated PDF inspected page by page (Track E)
- [ ] Press submit. Then: record the arXiv id on issue #38, close #38, and
      #37 (post-arXiv research) may begin.
