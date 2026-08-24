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
| General-space transfer, main theorem (#66) | ✅ bundle-conditional theorem complete; E1 bridge (#72) open |
| Japanese Borel/descriptive-set-theory note (#48 / PR #49) | ✅ complete; merged in PR #49 at `2b8acf4` |
| Repository metadata and rename (#58) | 🔄 open; PR #59 merged, repository rename still requires an owner action |
| E1 bridge: bundle → published extensor theorem (#72) | 🔄 open |
| `IshikiExt` Layer 1 coding infrastructure (PR #52) | ✅ merged; consumed by #56 |

## Active Borel track

`notes/borel-preprint-audit.md` is the mathematical source of truth and the
statement gate for #56, #57 and #66. It audits every theorem in the preprint,
records PASS/FIX/EXTERNAL verdicts, and identifies the repairs required in
formalisation. The Lean work follows the audit's minimal route (Route M) for
the Borel obstruction and separability result.

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
repository therefore now states, for *every* `D` with `|D| = ℵ₁` and with no
residual hypothesis on a parameter set, both the body's Theorem 3.3
(`bmet_not_borel_cpm_of_card`: `BMet(D)` is not Borel in `CPM(D)`) and the
abstract's and introduction's `Met(Z)` claim (`met_not_borel_of_card`). The
split follows audit §2.6, which records that the `Met` phrasing appears only
in the abstract and introduction. The hypothesis `|D| = ℵ₁` is shown
satisfiable (`exists_carrier_aleph_one`), so neither statement is vacuous.

Issue #57 (Theorem 3.5, the transfer from the discrete obstruction to a
general metrizable space) delivered the supporting lemmas: the
nonseparable-space closed-discrete-subset lemma, the closed-isometric-image
lemma, the topology-aware `CPM.MetOn` locus, and the `IsIsometricExtensor`
hypothesis bundle for the external extensor theorem (E1), including the
`Met`-image identity derived from it rather than assumed.

Issue #66 closes that transfer. Three prerequisites found on review were
resolved first: a continuity-restricted ambient `CPMOn X` (the preprint's
`CPM(X)` — `CPM.MetOn` previously reused #56's bare-discrete `CPM`, which has
no continuity constraint and so encodes a strictly stronger, non-published
hypothesis for non-discrete `X`); an `EMetricSpace` generalisation of the
closed-isometric-image lemma, needed because `CPM`'s sup distance is
extended-valued; and a `CompleteSpace (CPM D)` instance, the audit's §2.8
"uniform limits of pseudometrics" step. The delivered theorem is
`IsIsometricExtensor.not_measurableSet_CPM_MetOn`: an isometric extensor out
of the coded ℵ₁-sized discrete carrier forbids Borelness of `Met(X)` in
`CPM(X)`. Its separability form,
`separable_of_measurableSet_CPM_MetOn_of_extensors`, quantifies the extensor
over closed discrete copies of the carrier, which is how the audit's §2.8
uses E1 and the only form in which the ℵ₁-separated-set lemma is consumed.
Both are conditional on the `IsIsometricExtensor` hypothesis bundle, which
enters as an explicit hypothesis and never as an axiom. That bundle is E1
transported onto a fixed carrier; the transport itself (CPMOn-level
relabelling, audit §7 item 4) is not yet formalised, so the checked claim is
"Theorem 3.5 modulo the bundle", not "modulo E1". The literal statement of the issue text is recorded
as a corollary and marked as having jointly inconsistent hypotheses —
`IsIsometricExtensor.not_separableSpace` proves that a fixed extensor already
refutes separability — so it is not presented as the result.

The non-Archimedean analogues and the finer component and complete-metric
statements are recorded in the audit for later work. They are not part of the
current #56/#57/#66 delivery.

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
- `CPM.lean` (PR #64, #56 item 3; extended by #66) — the unbounded
  pseudometric ambient `CPM D`, the bridge lemma identifying its extended sup
  distance with `BddPMet`'s real-valued one on bounded pairs,
  `bmet_not_borel_cpm`, `met_not_borel` (the literal, unbounded `Met(D)`
  non-Borelness statement), and `CPM.instCompleteSpace` (audit §2.8).
- `Relabel.lean` (#63, #56 item 4) — relabelling of both ambients along a
  bijection of the carrier (`BddPMet.relabelIsometry`, `CPM.relabelIsometry`)
  with the `BMet`/`Met` preimage identities, and the arbitrary-carrier
  theorems `bmet_not_borel_of_card`, `bmet_not_borel_cpm_of_card`,
  `met_not_borel_of_card`.
- `GeneralSpace.lean`, `GeneralSeparability.lean` (PR #67, #57 supporting
  lemmas; #66 package) — the nonseparable-space closed-discrete-subset
  lemma, the closed-isometric-image lemma (now at `EMetricSpace` level), the
  continuous-pseudometric ambient `CPMOn X`, `CPM.MetOn` inside it, the
  `IsIsometricExtensor` hypothesis bundle with its derived `Met`-image
  identity, and the transfer theorems
  `IsIsometricExtensor.not_measurableSet_CPM_MetOn` and
  `separable_of_measurableSet_CPM_MetOn_of_extensors`.

Not yet done on this track: Corollary 3.6 (completely metrizable ⇒ Borel via
Alexandrov–Lavrentiev), the `BMet`/`Comp` variants of the transfer that
audit §2.10 and §2.12 need, and the whole chain 3.10–3.17.

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
coding from PR #52 remains reusable infrastructure.

## GitHub Issue work queue

The original Conjecture 5.1 queue (#2–#31) is closed; its outcome and
evidence are summarised in `notes/proof-audit.md` and the archival files.

1. **#55** — theorem-by-theorem audit of arXiv:2608.19618: **closed**;
   merged through **PR #60**.
2. **#56** — formalise the discrete Borel obstruction: all four items
   delivered; items 1–3 merged through **PR #64** at `8868eaa`, item 4
   (relabelling) through **#63**.
3. **#57** — formalise the general-space Borel/separability transfer:
   supporting lemmas merged through **PR #67** at `a27d7f1`; the main
   theorem was deferred to **#66**. #57's acceptance criterion is the exact
   published theorem/interface, which the bundle-conditional form delivered
   by #66 does not yet meet (see #72); **#57 stays open until #72 lands**.
4. **#66** — the Route M package (continuity-aware ambient `CPMOn`,
   `CompleteSpace (CPM D)`, the `EMetricSpace` closed-range generalisation,
   and the two transfer theorems): **delivered, conditional on the
   `IsIsometricExtensor` bundle** (not on E1 verbatim — see #72).
5. **#48** — Japanese Borel/descriptive-set-theory study note: **closed**;
   merged through **PR #49** at `2b8acf4`.
6. **#58** — repository metadata cleanup and rename to
   `metric-moduli-separability`: **open**. **PR #59** reset `README.md` and
   `AGENTS.md` and is merged; the repository rename itself remains an owner
   action.
7. **#72** — bridge the transported `IsIsometricExtensor` bundle to the
   published E1 theorem (audit §7 item 4's CPMOn-level relabelling
   obligation): **open**.
