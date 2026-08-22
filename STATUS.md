# Project Status

**Updated:** 2026-08-23

## Overall

The active project is the Lean-assisted verification of Y. Ishiki and T. Uda,
*Borelness of Moduli Spaces of Metrics Implies Separability*, arXiv:2608.19618
v1 (20 Aug 2026).

| Item | Status |
|------|--------|
| Theorem-by-theorem audit of arXiv:2608.19618 (#55) | ✅ complete; merged in PR #60 at `b8ef88a` |
| Discrete Borel obstruction (#56) | 🔄 open; Lean implementation in progress |
| General-space Borel/separability transfer (#57) | ⏸ open; waiting on #56's ambient-faithfulness and relabelling layers |
| Japanese Borel/descriptive-set-theory note (#48 / PR #49) | 🔄 open; draft evolving |
| Repository metadata and rename (#58) | 🔄 open; PR #59 merged, repository rename still requires an owner action |
| `IshikiExt` Layer 1 coding infrastructure (PR #52) | ✅ merged; reusable for #56 |

## Active Borel track

`notes/borel-preprint-audit.md` is the mathematical source of truth and the
statement gate for #56 and #57. It audits every theorem in the preprint,
records PASS/FIX/EXTERNAL verdicts, and identifies the repairs that must be
carried into formalisation. The Lean work is following the audit's minimal
Archimedean route for the headline Borel obstruction and separability result.

Issue #56 covers the discrete core:

- existence of an ℵ₁-sized non-Borel subset of `[0,1]`;
- the non-Borelness of `BMet` in the bounded pseudometric ambient, using the
  star-metric coding;
- the bridge from the bounded Lean ambient to the preprint's `CPM` ambient;
- relabelling isometries needed for the statement on an arbitrary discrete
  carrier of cardinality ℵ₁.

Issue #57 covers Theorem 3.5, the transfer from the discrete obstruction to a
general metrizable space. Its Lean statement takes an `IsIsometricExtensor`
hypothesis bundle for the external extensor theorem as an explicit
hypothesis, not a custom axiom. The issue depends on the
ambient-faithfulness and relabelling work in #56.

The non-Archimedean analogues and the finer component and complete-metric
statements are recorded in the audit for later work. They are not part of the
current #56/#57 delivery.

## Lean

The only Borel-track theorem development merged so far is `IshikiExt` Layer 1
from PR #52:

- `lean/IshikiConj51/Ext/BddPMet.lean` defines the bounded pseudometric ambient;
- `lean/IshikiConj51/Ext/BoundedCoding.lean` formalises the bounded star-metric
  family and its metricity, compatibility criterion, Lipschitz estimates,
  exact pullback identity, closed image, and ℵ₁ carrier cardinality.

This layer formalises coding only. It does not yet prove a non-Borelness
statement or the general-space transfer; those are the
targets of #56 and #57. The merged development is sorry-free and its audit
uses only the standard Lean axioms reported by `#print axioms`.

External mathematical results used by the Borel track will enter Lean as
explicit hypotheses or separately formalised results. In particular, the
published `Met`/`BMet`/`CPM` distinctions and their ambient topologies remain
part of the statements.

## Archival verified core: Ishiki Conjecture 5.1

The repository retains a completed formalisation of Conjecture 5.1 from
Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030. For a discrete
space `D` of cardinality ℵ₁, `Met(D)` with the supremum-metric topology is
not completely metrizable.

The result is fully proved and sorry-free. Gates A–C passed, and the
proof-candidate label was lifted on 2026-08-09. The archival record is:

- `report/report-ja.md` — the self-contained Japanese proof report;
- `lean/IshikiConj51/Conj51/` — the Lean formalisation;
- `notes/proof-audit.md` — the proof and formalisation audit.

This core is frozen for the Borel track. The earlier manuscript and arXiv
submission records under `paper/` and `notes/arxiv-submission.md` are archival
history, not active work.

## Superseded analytic/coanalytic track

Issues #46–#47 and PR #50 concern an earlier analytic/coanalytic draft and are
closed. Two findings from that work remain relevant to the project boundary:

1. The claim that an ℵ₁-sized set of reals is both non-analytic and
   non-coanalytic is not a ZFC theorem. In the ¬CH branch, the thin
   Π¹₁ coanalytic countermodel supplies a set of the prescribed size.
2. Classical analytic/coanalytic pointclasses are the wrong framework for the
   nonseparable ambient metric spaces in question; their usual separability
   restrictions make the intended ambient statement vacuous or ill-posed.

The published preprint replaces that package with Borel statements, whose
ambient Borel σ-algebra does not require a Polish ambient space. The old
pointclass package is not a verification target. The pointclass-free metric
coding from PR #52 survives as reusable infrastructure.

## GitHub Issue work queue

The original Conjecture 5.1 queue (#2–#31) is closed; its outcome and
evidence are summarised in `notes/proof-audit.md` and the archival files.

1. **#55** — theorem-by-theorem audit of arXiv:2608.19618: **closed**;
   merged through **PR #60**.
2. **#56** — formalise the discrete Borel obstruction: **open**, in progress.
3. **#57** — formalise the general-space Borel/separability transfer:
   **open**, waiting on #56 items 3–4.
4. **#48** — Japanese Borel/descriptive-set-theory study note: **open**;
   **PR #49** is open and evolving.
5. **#58** — repository metadata cleanup and rename to
   `metric-moduli-separability`: **open**. **PR #59** reset `README.md` and
   `AGENTS.md` and is merged; the repository rename itself remains an owner
   action.
