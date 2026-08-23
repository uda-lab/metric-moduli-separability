# Agent Guidelines

<!-- Do not restructure or delete sections. Update individual values in-place when they change. -->

## Core Principles

- Keep this file under 20-30 lines of visible guidance.
- Keep only repo-specific, non-obvious instructions here.

## Project Overview

- Active goal: Lean-assisted verification of Ishiki–Uda, **Borelness of Moduli Spaces of Metrics Implies Separability**, arXiv:2608.19618. Mathematical SoT for this track: `notes/borel-preprint-audit.md` (the #55 statement gate); do not accept top-level theorem statements until they are checked against it and the public preprint.
- Active work queue: #72 bridges the general-space capstone's extensor hypothesis to the published E1 theorem, and closes #57 when it lands; #58 handles repo metadata/rename. #55 theorem map, #56 discrete Borel core, #66 general-space capstone (bundle-conditional), and #48/PR #49 terminology note are complete (`STATUS.md`).
- The original Conjecture 5.1 proof is an archival verified core: `report/report-ja.md` + `lean/IshikiConj51/Conj51/`. Stable IDs `LEM-A-EXISTS`, `LEM-STAR-METRIC`, `LEM-CLOSED-IMAGE`, `THM-CONJ51` belong to that archival track.
- The old analytic/coanalytic track (#46/#47, PR #50) is superseded. Do not resurrect its ZFC theorem package. Merged PR #52 (`IshikiExt`) is reusable only for the pointclass-free coding statements it actually proves.

## Commands

~~~sh
cd lean && lake exe cache get   # mathlib oleans; NEVER cold-build mathlib here
flock /tmp/lean-build.lock lake build   # container-wide single build; need ≥2GiB free
~~~

## Code Conventions

- Preserve the published `Met`/`BMet`/`CPM` hypotheses exactly; never replace them by bounded, uniformly discrete, separable or other proxies unless #55 shows the source theorem has that hypothesis.
- If an external extensor/descriptive-set theorem is absent from Mathlib, expose it as an explicit hypothesis or formalise it separately; never hide it behind a custom axiom.
- Accepted Lean results must be sorry-free with an explained `#print axioms` audit. Record failed proof attempts in audit notes, not reader-facing reports.
- Japanese mathematical prose uses comma/period punctuation; `notes/descriptive-set-theory-ja.md` (#48, merged in PR #49) is the terminology reference for the public-preprint track.

## Architecture

- Issue-driven: statement audit → focused PR → independent review → merge; no direct pushes to main.
- `Conj51/` is archival provenance. New public-preprint formalisation belongs under a separate extension/publication namespace, reusing `IshikiExt` infrastructure only where statement fidelity is clear.

## Maintenance Notes

- Delete stale or inferable guidance.
- Update commands and architecture when workflows change.
- Keep durable rules here; move detail to dedicated docs.
