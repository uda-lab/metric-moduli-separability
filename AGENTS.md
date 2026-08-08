# Agent Guidelines

<!-- Do not restructure or delete sections. Update individual values in-place when they change. -->

## Core Principles

- Keep this file under 20-30 lines of visible guidance.
- Keep only repo-specific, non-obvious instructions here.

## Project Overview

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- Goal: resolve Ishiki Conjecture 5.1 (arXiv:2407.03030): for discrete D with |D| = ℵ₁, Met(D) (metrics **compatible with the discrete topology**, sup-metric topology) is not completely metrizable. Current argument is a PROOF CANDIDATE; never state "solved" externally until Gates A–C of the project plan pass.
- Source of truth: mathematical claims = `report/report-ja.md` + Lean theorem statements (must agree); English wording = `paper/main.tex`; progress = GitHub Issues + `STATUS.md`. The Google Docs plan ("Conjecture 5.1 論文化・形式化プロジェクト計画書") is planning-only, never mathematical SoT.
- Stable claim IDs `LEM-A-EXISTS`, `LEM-STAR-METRIC`, `LEM-CLOSED-IMAGE`, `THM-CONJ51` are shared across report, Lean, and paper; never change a claim in one place only — reopen dependent issues on any change.

## Commands

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
~~~sh
cd lean && lake exe cache get   # mathlib oleans; NEVER cold-build mathlib here
flock /tmp/lean-build.lock lake build   # container-wide single build; need ≥2GiB free (free -h)
~~~

## Code Conventions

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- Fσ has no Mathlib predicate (v4.32.2): use the local `IsFSigma` in `Conj51/Cardinality.lean`; `IsSigmaCompact` is NOT a valid proxy.
- A claim ID may be attached to a Lean declaration only when the statement faithfully matches the report; do not silently weaken (e.g. to bounded or uniformly discrete metrics). Final result must be sorry-free with an explained `#print axioms` audit.
- Japanese report follows `notes/terminology.md` (完全距離化可能 = completely metrizable); use wabun-math-style / math-claim-integrity skills for report edits.
- Record failed proof attempts in `notes/proof-audit.md`, never in the report or paper.

## Architecture

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- Issue-driven: all work ships as issue → PR → independent codex review (`python3 "$REVIEW_ACQUIRE_SCRIPT" uda-lab/ishiki-conjecture <PR> codex`) → merge, per github-driven-workflow skill; no direct pushes to main.
- `lean/IshikiConj51/Conj51/{Cardinality,MetricConstruction,ClosedEmbedding,MainTheorem}.lean` map 1:1 to the four claim IDs; `Met(D)` type must be constructed before the last three get Lean statements.

## Maintenance Notes

<!-- This section is permanent. Do not delete. -->
- Delete stale or inferable guidance.
- Update commands and architecture when workflows change.
- Keep durable rules here; move detail to dedicated docs.
