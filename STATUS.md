# Project Status

**Updated:** 2026-08-09

## Overall

| Item | Status |
|------|--------|
| Conjecture statement verified (arXiv:2407.03030) | ✅ done |
| LEM-A-EXISTS audited | ✅ done |
| Gδ / complete-metrizability implication audited | ✅ done |
| Star-metric construction written | ✅ done |
| Closed-embedding argument audited | ✅ done |
| Japanese report complete | ✅ done |
| Met(D) type defined in Lean | ✅ done |
| Lean formalisation complete | ✅ done (sorry-free, 2026-08-09) |
| English paper drafted | ✅ done (Issue #11, 2026-08-09) |
| Independent end-to-end review | ✅ done (Gate B passed, Issue #10, 2026-08-09) |
| Proof-candidate label | ✅ lifted (owner decision, PR #29 comment, 2026-08-09) |
| E9 cross-artifact consistency (paper ↔ report ↔ Lean) | ✅ done (Issue #26, 2026-08-09; recorded in `notes/proof-audit.md`) |
| E10 submission readiness audit | ✅ **go** (Issue #27, 2026-08-09; see `notes/proof-audit.md`) |

## The proof

The argument for THM-CONJ51 proceeds through six steps:

1. **LEM-A-EXISTS** — ZFC existence of A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
2. Y = [0,1] \ A is not Gδ in [0,1] (Fσ/Gδ complement duality), hence not
   completely metrizable (Alexandrov–Lavrentiev, applied to the separable
   ambient space [0,1] only).
3. A parameterised star-type family of compatible metrics on D
   (**LEM-STAR-METRIC**) — explicitly: a reference pair {p,q} at distance
   1+t, plus one star per element of A with centre-to-endpoint distance
   s_n(α,t) = min(1, |t−a_α| + 1/n).
4. A bi-Lipschitz embedding Y → Met(D): |t−s| ≤ ρ(d_t,d_s) ≤ 2|t−s|.
5. The image is closed in Met(D) (**LEM-CLOSED-IMAGE**) — the reference pair
   recovers the limit parameter t, and d_t ceasing to be compatible for
   t ∈ A rules out the boundary case.
6. A closed subspace of a completely metrizable space is completely
   metrizable — proved directly (no separability needed, since Met(D) is
   not separable) — contradiction (**THM-CONJ51**).

**Note on Met(D):** Met(D) denotes metrics on D *compatible with the discrete
topology*, not all metrics on the underlying set. Met(D) is not separable;
see `notes/literature.md` and `notes/proof-audit.md` (Issue #4) for why this
matters for step 6.

All six steps are now written out in full in `report/report-ja.md`
(2026-08-09); no mathematically unwritten step remains. Steps 1–2 and 6
(LEM-A-EXISTS; the Gδ / complete-metrizability implication; closed-subspace
inheritance) additionally completed an internal audit (Issues #3, #4).

The Lean formalisation of all six steps is complete and sorry-free
(Issues #6–#9, #23; 2026-08-09).

**Gates A, B and C are all passed.** In the submission-audit naming
(Issue #27): Gate A — the report is a self-contained natural-language proof —
and Gate B — independent end-to-end mathematical review — were both decided
**PASS** by the Issue #10 review (2026-08-09; verdict table in
`notes/proof-audit.md`, Issue #10 entry). Gate C — Lean sorry-free with an
explained `#print axioms` audit — is **PASS** via Issues #6–#9/#23 (zero
`sorry`, every declaration depending only on `[propext, Classical.choice,
Quot.sound]`; per-claim table in `notes/proof-audit.md`), independently
re-run by the Issue #10 reviewer on a from-scratch rebuild. An independent
end-to-end review, carried out by an agent uninvolved in Issues #2–#9 working
only from the arXiv source and the repository's primary documents, found **no
mathematical gap**: all six steps were reconstructed from scratch, nine
adversarial attacks (ambient ℝ vs [0,1], non-separability, extended-valued
sup metric, uniform discreteness, the boundary case t ∈ A, cardinal arithmetic
without CH, consistency with Koshino's separable theorem, and two Lean-vs-report
mismatches) all failed to break the argument, and the four claim IDs were
confirmed to be formalised faithfully rather than by a weakened proxy. Evidence
is recorded in `notes/proof-audit.md` (Issue #10 entry).

**The proof-candidate label has been lifted by owner decision** (comment by
t-uda on PR #29, 2026-08-09), on the basis of the Gate A–C verdicts above.
The result may be stated in ordinary declarative theorem language. Wording
that implies *external* peer validation is still to be avoided: verification
to date consists of the project's internal independent audit (Issue #10) and
the machine-checked Lean formalisation, not review by an outside party or a
journal.

## Open obligations

None remain (E10 submission readiness audit, Issue #27, 2026-08-09):
the obligations table in `notes/proof-audit.md` is fully resolved, the Lean
sorry count is 0, and the superseded PR #30 was closed. The E10 entry in
`notes/proof-audit.md` records the go/no-go judgment (**go**, with
owner-side submission-time notes: fill `\author{}`/date, keep the
no-external-review framing, optionally pin Kechris page numbers against a
physical copy).

## Lean

Lean project initialised (Mathlib v4.32.2, `lean/lakefile.toml`).
`lem_A_exists` (LEM-A-EXISTS) is now **sorry-free** (Issue #8, 2026-08-09;
`#print axioms` shows only `[propext, Classical.choice, Quot.sound]`). `Met(D)`
is now constructed as `MetD` (`IshikiConj51/Conj51/MetD.lean`; relocated there
from `MainTheorem.lean` in Issue #7 so the claim modules can import it), with a
sorry-free `EMetricSpace` instance matching the source's (extended) supremum
distance, unblocking Lean statements for the remaining claim IDs. `THM-CONJ51`
itself is now both stated and proved (`thm_conj51`, sorry-free as of Issue #9).
LEM-STAR-METRIC is now stated and **sorry-free** (`lem_star_metric`,
`IshikiConj51/Conj51/MetricConstruction.lean`, Issue #7, 2026-08-09);
LEM-CLOSED-IMAGE is now stated and **sorry-free** (`lem_closed_image`,
`IshikiConj51/Conj51/ClosedEmbedding.lean`, Issue #9, 2026-08-09), together
with a supporting new module `IshikiConj51/Conj51/Relabel.lean` (`Met(D)`
transports along any bijection of the index set, so the concrete
`StarIndex A` construction reaches an arbitrary `D` of the same cardinality).

**Every claim ID now has a Lean statement and a sorry-free proof; the
repository contains zero `sorry` and zero custom axioms.** The whole of report
§4 is assembled and proved in `thm_conj51_of_lavrentiev` (Issue #9), which
differs from `thm_conj51` only by carrying the Alexandrov–Lavrentiev direction
as an explicit hypothesis about subsets of ℝ. That hypothesis is discharged by
`isGδ_of_isCompletelyMetrizableSpace` (Issue #23,
`IshikiConj51/Conj51/GDeltaComplete.lean`, merged in PR #25) instantiated at
the ambient space `X := ℝ`, making `thm_conj51` a one-line application.

`#print axioms thm_conj51` reports `[propext, Classical.choice, Quot.sound]` —
the three standard Lean axioms only, with no `sorryAx`. The full per-claim
axiom table is in `notes/proof-audit.md`.

The Lean chain is therefore complete, and Gate B (Issue #10) has re-run
`#print axioms` independently on a from-scratch rebuild of the merged `main`
and confirmed the three standard axioms with no `sorryAx`, as well as checking
that the Lean statements render the source's notions faithfully (no bounded /
uniformly discrete proxy; `#D = ℵ₁` exact; the `lavrentiev` hypothesis of
`thm_conj51_of_lavrentiev` is discharged non-circularly).

A Mathlib v4.32.2 inventory for Issues #7–#9 is recorded in
`notes/proof-audit.md`'s Mathlib library gaps table (Issue #19): the
Alexandrov–Lavrentiev direction needed for the closed-subspace obstruction
(a completely metrizable subspace is Gδ in its ambient space) is **confirmed
absent** from Mathlib (re-confirmed in Issue #9) and must be proved from
scratch — now tracked as its own Issue #23; the
Cantor–Bendixson theorem, perfect-set cardinality-continuum fact, `ℵ₁ ≤ 𝔠`,
and closed-subspace-of-complete-space are all confirmed **available** with
exact declaration names recorded.

## English paper

`paper/main.tex` (Issue #11, 2026-08-09) now carries the full proof of all
four claim IDs, transcribed from the audited `report/report-ja.md` with no
altered hypotheses or conclusions. This fixes the three documentation
defects recorded as finding F1 of the Issue #10 audit
(`notes/proof-audit.md`): the Polish-only "Alexandrov's theorem" misuse is
replaced by the report's separable/non-separable split
(Theorems 2.1–2.2); the LEM-STAR-METRIC statement now matches the report's
claim instead of the placeholder "suitable bi-Lipschitz properties"
wording; and the stale "all theorems are stubs (`sorry`)" appendix claim
and `A \subset` notation are both corrected. `references.bib` gained
entries for the four textbooks the transcribed proofs actually cite
(Kechris, Engelking, Willard, Kelley) plus a short, source-verified
related-work paragraph (Koshino 2022; Ishiki arXiv:2402.04565); the
bibliographically unverifiable Koshino manuscript remains uncited, per
`notes/literature.md`. The paper compiles cleanly with `latexmk -pdf`
(after adding `lmodern`/`booktabs` to the preamble). Following the owner's
2026-08-09 decision lifting the proof-candidate label (Issue #31), the paper
states the theorem and its proof in ordinary declarative form, while avoiding
wording that would imply external peer validation.

## GitHub Issue work queue

1. #2 Verify Conjecture 5.1 statement and bibliography
2. #3 Audit LEM-A-EXISTS in ZFC
3. #4 Audit the Gδ / complete-metrizability step
4. #5 Complete the self-contained Japanese proof report
5. #6 Define Met(D) in Lean and state THM-CONJ51 faithfully
6. #7 Implement LEM-STAR-METRIC in Lean
7. #8 Formalise cardinality and descriptive-set prerequisites in Lean
8. #9 Formalise LEM-CLOSED-IMAGE and the final obstruction
9. #10 Perform independent end-to-end mathematical review
10. #11 Draft the English paper after mathematical audit passes
11. #19 Record Mathlib inventory findings for Lean formalisation prep (Issues #7–#9)
12. #23 Formalise the Alexandrov–Lavrentiev direction (completely metrizable subspace ⟹ Gδ)
13. #26 E9: Cross-check paper ↔ report ↔ Lean claim consistency
14. #31 Lift proof-candidate status per owner decision (Gates A–C passed)
15. #27 E10: Submission readiness audit
