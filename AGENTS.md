# Agent Guidelines

<!-- Do not restructure or delete sections. Update individual values in-place when they change. -->

## Core Principles

- Keep this file under 20-30 lines of visible guidance.
- Keep only repo-specific, non-obvious instructions here.

## Project Overview

- Active goal: Lean-assisted verification of Ishiki–Uda, **Borelness of Moduli Spaces of Metrics Implies Separability**. Mathematical SoT: `notes/borel-manuscript-20260827-audit.md`, auditing the manuscript source received 2026-09-02 (archive timestamp 2026-08-27); `notes/borel-preprint-audit.md` is the frozen arXiv:2608.19618 v1 record and keeps the per-declaration Lean package in its §7. Do not accept top-level theorem statements until they are checked against the successor note. The received source is reference-only, lives outside the repository, and is never called "arXiv v2" — arXiv carries v1 only.
- The original Conjecture 5.1 proof is an archival verified core: `report/report-ja.md` + `lean/IshikiConj51/Conj51/`. Stable IDs `LEM-A-EXISTS`, `LEM-STAR-METRIC`, `LEM-CLOSED-IMAGE`, `THM-CONJ51` belong to that archival track.
- The analytic/coanalytic track is superseded; `notes/borel-manuscript-20260827-audit.md` §5 lists the claims that must not be reinstated. The `IshikiExt` namespace it left behind is reusable only for the pointclass-free coding statements it actually proves.

## Commands

~~~sh
cd lean && lake exe cache get   # mathlib oleans; NEVER cold-build mathlib here
flock /tmp/lean-build.lock lake build   # container-wide single build; need ≥2GiB free
~~~

## Code Conventions

- Preserve the published `Met`/`BMet`/`CPM` hypotheses exactly; never replace them by bounded, uniformly discrete, separable or other proxies unless the audit note shows the source theorem has that hypothesis.
- If an external extensor/descriptive-set theorem is absent from Mathlib, expose it as an explicit hypothesis or formalise it separately; never hide it behind a custom axiom.
- Accepted Lean results must be sorry-free with an explained `#print axioms` audit; the axiom footprint must be a subset of `propext`/`Classical.choice`/`Quot.sound` — no `sorryAx`, no custom axioms. The reviewer/shepherd re-runs the audit independently in a throwaway untracked scratch file (`import IshikiConj51` + `#print axioms`), never committed. Record failed proof attempts in audit notes, not reader-facing reports.
- Japanese mathematical prose uses comma/period punctuation; `notes/terminology.md` is the terminology SoT for both tracks (`notes/descriptive-set-theory-ja.md` is the expository reference).

## Architecture

- Issue-driven: statement audit → focused PR → independent review → merge; no direct pushes to main.
- Two review gates, two triggers. The local pre-PR codex gate fires on *content*: skip it when `git rev-parse HEAD^{tree}` equals the reviewed tree hash, and when the base has moved compare branch contributions with `git range-diff` and review only what that reports — a rebase alone never re-triggers it (`A...B` is merge-base-relative, so it is the wrong test here). The broker gate fires on *head change*. Cite the reviewed tree hash next to the thread id so the next agent can tell what is already covered.
- `Conj51/` is archival provenance. New public-preprint formalisation belongs under a separate extension/publication namespace, reusing `IshikiExt` infrastructure only where statement fidelity is clear.

## Maintenance Notes

- GitHub Issues/PRs are the sole work-queue and execution-evidence record; keep no status dashboard, completion matrix, or freshness timestamp in repository documents.
- Docs carry only durable mathematical/architectural/reference content; build and axiom-check evidence stays in the PR/issue discussion, never in a committed ledger. Archival records (`notes/proof-audit.md`, `notes/arxiv-submission.md`, `report/`, `paper/`) are frozen provenance, exempt from cleanup.
- Delete stale or inferable guidance; update commands and architecture when workflows change; keep durable rules here and detail in dedicated docs.
