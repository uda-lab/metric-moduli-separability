# Project Status

**Updated:** 2026-08-23

## Overall

The active project is the Lean-assisted verification of Y. Ishiki and T. Uda,
*Borelness of Moduli Spaces of Metrics Implies Separability*, arXiv:2608.19618
v1 (20 Aug 2026).

| Item | Status |
|------|--------|
| Theorem-by-theorem audit of arXiv:2608.19618 (#55) | ✅ complete; merged in PR #60 at `b8ef88a` |
| Discrete Borel obstruction, items 1–3 (#56) | ✅ complete; merged in PR #64 at `8868eaa` |
| Discrete Borel obstruction, item 4 — relabelling (#63) | ✅ complete |
| General-space transfer, supporting lemmas (#57) | ✅ complete; merged in PR #67 at `a27d7f1` |
| General-space transfer, capstone theorem (#57) | ⏸ open; deferred to #66 |
| Japanese Borel/descriptive-set-theory note (#48 / PR #49) | ✅ complete; merged in PR #49 at `2b8acf4` |
| Repository metadata and rename (#58) | 🔄 open; PR #59 merged, repository rename still requires an owner action |
| `IshikiExt` Layer 1 coding infrastructure (PR #52) | ✅ merged; consumed by #56 |

## Active Borel track

`notes/borel-preprint-audit.md` is the mathematical source of truth and the
statement gate for #56 and #57. It audits every theorem in the preprint,
records PASS/FIX/EXTERNAL verdicts, and identifies the repairs that must be
carried into formalisation. The Lean work follows the audit's minimal
Archimedean route (Route M) for the headline Borel obstruction and
separability result.

Issue #56 (discrete core), items 1–3 are done:

- existence of an ℵ₁-sized non-Borel subset of `[0,1]` (`exists_aleph1_nonBorel`);
- non-Borelness of `BMet` in the bounded pseudometric ambient, using the
  star-metric coding (`bmet_not_borel`);
- the bridge from the bounded ambient to the preprint's unbounded `CPM`
  ambient, and the literal, unbounded `Met(D)` non-Borelness statement
  (`bmet_not_borel_cpm`, `met_not_borel`) — this matches the content of
  Theorem 3.3 and the abstract's `Met(Z)` claim on the concrete carrier the
  construction produces.

Item 4 (#63) relabels those results onto an arbitrary discrete carrier of
cardinality ℵ₁, which is what the preprint's theorems quantify over. The
repository therefore now states Theorem 3.3 and the abstract's `Met(Z)`
claim in their universal form: for *every* `D` with `|D| = ℵ₁`,
`met_not_borel_of_card` says `Met(D)` is not Borel in `CPM(D)`, with no
residual hypothesis on a parameter set and with the hypothesis `|D| = ℵ₁`
shown satisfiable (`exists_carrier_aleph_one`).

Issue #57 (Theorem 3.5, the transfer from the discrete obstruction to a
general metrizable space) has its supporting lemmas done: the
nonseparable-space closed-discrete-subset lemma, the closed-isometric-image
lemma, the topology-aware `CPM.MetOn` locus, and the `IsIsometricExtensor`
hypothesis bundle for the external extensor theorem (E1), including the
`Met`-image identity derived from it rather than assumed. The capstone
theorem itself (`Met(X)` Borel ⇒ `SeparableSpace X`) is open, tracked as
#66, along with three concrete prerequisites found during review:
`CPM.MetOn` needs a continuity-restricted ambient for non-discrete `X` (it
currently reuses #56's bare-discrete `CPM`, which has no continuity
constraint); the closed-isometric-image lemma needs an `EMetricSpace`
generalisation to apply to `CPM`'s extended-valued sup distance; and a
`CompleteSpace (CPM D)` instance, needed by that same closed-image argument,
does not yet exist in the repository.

The non-Archimedean analogues and the finer component and complete-metric
statements are recorded in the audit for later work. They are not part of the
current #56/#57 delivery.

## Lean

Borel-track theorem development, `lean/IshikiConj51/Ext/`, `IshikiExt`
namespace:

- `BddPMet.lean` (PR #52) — the bounded pseudometric ambient `BddPMet D`.
- `BoundedCoding.lean` (PR #52) — the bounded star-metric family, its
  metricity, compatibility criterion, Lipschitz estimates, and the exact
  pullback identity `Φ⁻¹(BMet) = [0,1] \ S`.
- `Borel.lean` (PR #64, #56 items 1–2) — `exists_aleph1_nonBorel` (ZFC, via
  the Borel Isomorphism Theorem, no Bernstein sets or perfect-set-theorem
  argument needed) and `bmet_not_borel` (non-Borelness of `BMet` in the
  bounded ambient).
- `CPM.lean` (PR #64, #56 item 3) — the unbounded pseudometric ambient
  `CPM D`, the bridge lemma identifying its extended sup distance with
  `BddPMet`'s real-valued one on bounded pairs, and `bmet_not_borel_cpm`,
  `met_not_borel` (the literal, unbounded `Met(D)` non-Borelness statement).
- `Relabel.lean` (#63, #56 item 4) — relabelling of both ambients along a
  bijection of the carrier (`BddPMet.relabelIsometry`, `CPM.relabelIsometry`)
  with the `BMet`/`Met` preimage identities, and the arbitrary-carrier
  theorems `bmet_not_borel_of_card`, `bmet_not_borel_cpm_of_card`,
  `met_not_borel_of_card`.
- `GeneralSpace.lean`, `GeneralSeparability.lean` (PR #67, #57 supporting
  lemmas) — the nonseparable-space closed-discrete-subset lemma, the
  closed-isometric-image lemma, `CPM.MetOn`, and the `IsIsometricExtensor`
  hypothesis bundle with its derived `Met`-image identity.

Not yet done: #57's capstone theorem together with the continuity-ambient and
`EMetricSpace` prerequisites found on review (#66).

Every declaration above is sorry-free; `#print axioms` shows only the
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), recorded
in `notes/lean-axioms-borel.md`. External mathematical results (the E1
isometric extensor) enter Lean only as an explicit hypothesis bundle
(`IsIsometricExtensor`), never as a custom axiom.

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
2. **#56** — formalise the discrete Borel obstruction: all four items
   delivered; items 1–3 merged through **PR #64** at `8868eaa`, item 4
   (relabelling) through **#63**.
3. **#57** — formalise the general-space Borel/separability transfer:
   **open**; supporting lemmas merged through **PR #67** at `a27d7f1`, the
   capstone theorem deferred to **#66**.
4. **#48** — Japanese Borel/descriptive-set-theory study note: **closed**;
   merged through **PR #49** at `2b8acf4`.
5. **#58** — repository metadata cleanup and rename to
   `metric-moduli-separability`: **open**. **PR #59** reset `README.md` and
   `AGENTS.md` and is merged; the repository rename itself remains an owner
   action.
