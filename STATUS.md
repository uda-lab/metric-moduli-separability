# Project Status

**Updated:** 2026-08-25

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
| General-space transfer, main theorem (#66) | ✅ bundle-conditional theorem complete |
| Japanese Borel/descriptive-set-theory note (#48 / PR #49) | ✅ complete; merged in PR #49 at `2b8acf4` |
| Repository metadata and rename (#58) | 🔄 open; PR #59 merged, repository rename still requires an owner action |
| E1 bridge: bundle → published extensor theorem (#72) | ✅ complete |
| Corollaries 3.6 and 3.7, with the audit §2.10 repair (#79) | ✅ complete |
| Theorem 3.4: non-Borel components of `Met(Z)` (#84) | ✅ complete |
| `IshikiExt` Layer 1 coding infrastructure (PR #52) | ✅ merged; consumed by #56 |
| Discrete ultrametric core, Prop. 2.2, Lemmas 3.10–3.11, Theorems 3.12–3.13 (#81) | ✅ complete |

## Active Borel track

`notes/borel-preprint-audit.md` is the mathematical source of truth and the
statement gate for #56, #57, #66, #72, #79, #84 and #81. It audits every theorem in the preprint,
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
enters as an explicit hypothesis and never as an axiom. The literal statement
of the issue text is recorded as a corollary and marked as having jointly
inconsistent hypotheses — `IsIsometricExtensor.not_separableSpace` proves that
a fixed extensor already refutes separability — so it is not presented as the
result.

Issue #72 removes the distance between that bundle and E1. The bundle is E1
transported onto a fixed carrier, and the transport is now formalised:
`CPMOn.relabelIsometry` and `CPMOn.preimage_MetOn_comap` supply audit §7
item 4 at the continuous-pseudometric level, `IsIsometricExtensorOn` states E1
for one closed subset with no carrier-specific choices, and
`IsIsometricExtensorOn.toIsIsometricExtensor` produces the bundle from it. The
delivered forms of Theorem 3.5 are therefore
`not_measurableSet_CPM_MetOn_of_isometricExtensorOn` and
`separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn`, which
hypothesise `∀ A, IsClosed A → Nonempty (IsIsometricExtensorOn A)` — E1
quantified over the closed subsets of `X`, as E1 quantifies itself. The checked
claim is "Theorem 3.5 modulo E1". E1's proof stays external and is never an
axiom.

Issue #79 takes the chain to its two corollaries. Corollary 3.6 — `Met(X)`
completely metrizable implies `X` separable — is the step that settles Ishiki's
Conjecture 5.1 in the strengthened Borel form, and it needs
Alexandrov–Lavrentiev in the exact ambient of the preprint: the archival
track's `isGδ_of_isCompletelyMetrizableSpace` is stated for a `MetricSpace`
ambient, while `CPMOn X` is only an `EMetricSpace`, so it is restated for a
metrizable ambient. Corollary 3.7 is delivered with the repair audit §2.10
requires: its `⇒` direction cannot come from Corollary 3.6, because `BMet(X)`
is a clopen union of components of `Met(X)` and complete metrizability
transfers in neither direction, so the `BMet` analogue of Theorem 3.5 is
formalised — E1 clause (3) gives the image identity
`E(BMet(Z)) = Ẽ(CPM(Z)) ∩ BMet(X)`, and the pullback contradicts the discrete
`BMet` obstruction `bmet_not_borel_cpm` directly. Koshino's theorem (E3) enters
Corollary 3.7 as an explicit hypothesis with its separability assumption
intact, never as an axiom or an instance, and the audit's caveat on its
citation number is recorded rather than resolved.

Issue #84 formalises Theorem 3.4, the finer component statement, which audit
§2.8 records as *not* a prerequisite of Theorem 3.5. For a carrier of
cardinality ℵ₁, every finite-sup-distance component of `Met(Z)` is non-Borel
in `CPM(Z)`: `component_not_measurableSet` states this for the component of
an arbitrary representative, `componentSet_not_measurableSet` over the
quotient `𝐌_{<∞}(Z)` itself. The proof transfers the star coding to an
uncountable closed ball of the base metric and amalgamates it with that
metric along one common point; the two steps the preprint leaves implicit —
the amalgam stays at finite supremum distance from the base metric, and
membership in the component reduces to compatibility — are the separate
lemmas `edist_psi_base_le` (with the explicit bound `4 + 2H`) and
`mem_Met_psi_iff`. The amalgamation layer is carrier-agnostic and is what the
complete-metric statement (Theorem 3.8) will consume.

The complete-metric statements (Theorems 3.8 and 3.16) are recorded in the
audit for later work.

## Non-Archimedean track

Issue #81 formalises the discrete non-Archimedean core: Proposition 2.2,
Lemmas 3.10–3.11 and Theorems 3.12–3.13, gated by audit §2.2 and §§2.13–2.14.

The ambient is new, not a reuse of the Archimedean one. The preprint's
`UCPM(Z;R)` consists of `R`-valued pseudo-ultrametrics, and its distance
`𝒰𝒟^R(d,e) = inf {ε ∈ R ∪ {∞} : d ≤ e ∨ ε, e ≤ d ∨ ε}` is not the supremum of
`|d − e|`; Mathlib has neither notion. Both are defined from scratch, with the
range set `R` and the characteristic hypothesis stated exactly as the preprint
states them — `exists_isScale` and `isCharacteristic_of_isScale` prove both
directions of "a strictly decreasing `r : ℕ → R∖{0}` with `r n → 0` exists
exactly when `R` is characteristic", so nothing stronger is assumed. What is
reused from the Archimedean side is the compatibility predicate (`IsMetricOn`
plus discrete induced topology, from `Conj51/MetD.lean`) and its relabelling
transport (`Ext/Relabel.lean`).

Proposition 2.2 needs the audit's §2.2 repair: the preprint's Borel
isomorphism `2^ω ≅ [0,1]` transfers non-Borelness and cardinality but not
density. The delivered statement carries density
(`exists_dense_aleph1_nonBorel_cantor`), obtained by running the CH/¬CH
dichotomy in `2^ω` and then adding a countable dense set. Density is not
decoration: Lemma 3.11's lower bound consumes it (`exists_separating_pair`),
and the Archimedean observation that density is dispensable there is not
imported.

Theorem 3.12 (`umet_not_borel_of_card`) and Theorem 3.13
(`ucomponent_not_borel_of_card`) are stated for an arbitrary discrete carrier
of cardinality ℵ₁ and an arbitrary characteristic range set, with no residual
hypothesis on a parameter set. `exists_mem_UMet_of_card` shows the hypotheses
are satisfiable, so neither is vacuous. Both are proved through the exact
parameter pullback identities (`preimage_UMet_phiU`,
`preimage_UComponent_psiU`); the printed proofs' compact traces and closed
images are formalised alongside rather than assumed.

Theorems 3.14–3.17 remain future work, including the 3.14 ambient-transfer
repair that audit §2.14 records as not mechanizable from the paper's text.

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
- `Relabel.lean` (#63, #56 item 4; extended by #72) — relabelling of both
  ambients along a bijection of the carrier (`BddPMet.relabelIsometry`,
  `CPM.relabelIsometry`) with the `BMet`/`Met` preimage identities, the
  arbitrary-carrier theorems `bmet_not_borel_of_card`,
  `bmet_not_borel_cpm_of_card`, `met_not_borel_of_card`, and `topology_comap`
  (a relabelled metric induces the relabelled topology), which #72 needs where
  the carriers are not discrete.
- `Amalgam.lean` (#84) — the one-point amalgamation of a metric on a carrier
  with a metric on a subset, glued along a common point: its metric axioms,
  its compatibility criterion in both directions, the explicit bound
  `|m − d| ≤ B + 2H` on the distance to the base metric, and its pointwise
  Lipschitz dependence on the glued-in metric. Carrier-agnostic; it mentions
  neither the coding nor any cardinality.
- `Component.lean` (#84, Theorem 3.4) — the component locus `CPM.component`
  and the quotient `CPM.Components`, the uncountable-ball lemma
  `exists_aleph1_ball`, the `ComponentSetup` bundle with the parameter map
  `Ψ`, its pullback identity and compact-range trace identity, and the two
  forms of Theorem 3.4.
- `GeneralSpace.lean`, `GeneralSeparability.lean` (PR #67, #57 supporting
  lemmas; #66 package; #72 E1 bridge) — the nonseparable-space
  closed-discrete-subset lemma, the closed-isometric-image lemma (now at
  `EMetricSpace` level), the continuous-pseudometric ambient `CPMOn X` with
  its relabelling layer, `CPM.MetOn` inside it, the `IsIsometricExtensor`
  hypothesis bundle with its derived `Met`-image identity, E1 itself as
  `IsIsometricExtensorOn` with the derivation
  `IsIsometricExtensorOn.toIsIsometricExtensor`, and the transfer theorems in
  both their bundle-conditional and E1-conditional forms.
- `CompleteMetrizability.lean` (#79) — Alexandrov–Lavrentiev for a metrizable
  ambient (lifting `Conj51/GDeltaComplete.lean`, which is stated for a
  `MetricSpace`), the bounded locus `CPM.BMetOn X` with its transport lemmas,
  E1 clause (3) as `IsBddIsometricExtensorOn`, the `BMet` analogue of Theorem
  3.5 that audit §2.10 requires, and Corollaries 3.6 and 3.7.

Non-Archimedean track (#81):

- `UltraPMet.lean` — the range set `R` with its characteristic hypothesis and
  scales, the ambient `UCPM Z R` of `R`-valued pseudo-ultrametrics with the
  preprint's `𝒰𝒟^R` distance and its strong triangle inequality, the two
  reusable operations `UCPM.comap` and `UCPM.sup`, the loci `UMet Z R` and
  `UComponent d`, and the relabelling isometry with its preimage identities.
- `CantorUltra.lean` — Proposition 2.2 with the audit §2.2 density repair
  (`exists_dense_aleph1_nonBorel_cantor`), the CH/¬CH dichotomy stated once for
  an arbitrary standard Borel space of cardinality `𝔠`, and the `R`-valued
  Cantor ultrametric `cantorDist` with the ball description that ties it to the
  product topology.
- `UltraCoding.lean` — Lemma 3.10 (ultrametricity, `R`-valuedness,
  compatibility iff `t ∉ S`, completeness for `t ∉ S`), Lemma 3.11 (the exact
  `𝒰𝒟^R`-isometry and the closed image) and Theorem 3.12 on both the coded and
  an arbitrary ℵ₁-sized carrier.
- `UltraComponent.lean` — Theorem 3.13: the closed-ball selection, the
  ultrametric one-point max-amalgam, the audited component bound
  `𝒰𝒟^R(m_t,d) ≤ q ∨ r 0`, and non-Borelness of every `R`-component.

Not yet done on this track: Theorem 3.8 (the complete-metric component
statement, with the audit §2.11 repair), the `Comp` variant of the transfer
that audit §2.12 needs, and the non-Archimedean chain 3.14–3.17.

Every declaration above is sorry-free; `#print axioms` shows only the
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), recorded
in `notes/lean-axioms-borel.md`. External mathematical results (the E1
isometric extensor, and Koshino's theorem E3 in Corollary 3.7) enter Lean only
as explicit hypotheses (`IsIsometricExtensorOn`, `IsBddIsometricExtensorOn`,
the transported `IsIsometricExtensor`, and E3's iff as a hypothesis of the
statement that uses it), never as a custom axiom.

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
   by #66 did not meet; **#72 meets it**, so #57 closes with #72.
4. **#66** — the Route M package (continuity-aware ambient `CPMOn`,
   `CompleteSpace (CPM D)`, the `EMetricSpace` closed-range generalisation,
   and the two transfer theorems): **delivered, conditional on the
   `IsIsometricExtensor` bundle**; #72 supplies that bundle from E1.
5. **#48** — Japanese Borel/descriptive-set-theory study note: **closed**;
   merged through **PR #49** at `2b8acf4`.
6. **#58** — repository metadata cleanup and rename to
   `metric-moduli-separability`: **open**. **PR #59** reset `README.md` and
   `AGENTS.md` and is merged; the repository rename itself remains an owner
   action.
7. **#72** — bridge the transported `IsIsometricExtensor` bundle to the
   published E1 theorem (audit §7 item 4's CPMOn-level relabelling
   obligation): **delivered**; `IsIsometricExtensorOn` states E1,
   `IsIsometricExtensorOn.toIsIsometricExtensor` performs the transport, and
   the two transfer theorems are restated with E1 as the hypothesis.
8. **#79** — Corollaries 3.6 and 3.7: **delivered**. Corollary 3.6 runs the
   audit §2.9 derivation (Alexandrov–Lavrentiev, then Theorem 3.5); Corollary
   3.7 is delivered with the §2.10 repair, its `BMet` analogue of Theorem 3.5
   formalised from E1 clause (3), and E3 kept as an explicit hypothesis.
9. **#84** — formalise Theorem 3.4 (every finite-sup-distance component of
   `Met(Z)` is non-Borel in `CPM(Z)`): **delivered**, with the one-point
   amalgamation split out as reusable machinery for Theorem 3.8.
10. **#81** — formalise the discrete non-Archimedean core (Proposition 2.2,
   Lemmas 3.10–3.11, Theorems 3.12–3.13): **delivered**. The `UCPM`/`𝒰𝒟^R`
   ambient and the one-point max-amalgam layers are written to be reused by
   the follow-on non-Archimedean issues.
