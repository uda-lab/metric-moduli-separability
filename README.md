# Metric moduli / separability project

Research repository for Lean-assisted verification of results on spaces of
compatible metrics.

## Public-preprint track

The active external source is the joint preprint by Yoshito Ishiki and Tomoki
Uda, **Borelness of Moduli Spaces of Metrics Implies Separability**,
arXiv:2608.19618 (2026), together with the latest manuscript source received
on 2026-11-03, which is reference-only and lives outside this repository
(arXiv carries v1 only). The repository verifies it theorem by theorem:
`notes/borel-manuscript-20261103-audit.md` is the mathematical source of truth
(statements, verdicts, verified repairs, external-theorem dependencies, and
the label-level Lean correspondence) for that source;
`notes/borel-manuscript-20260827-audit.md` is the frozen record of the
previous received source (2026-08-27) and holds the exact external
statements; `notes/borel-preprint-audit.md` is the frozen arXiv v1 record and
carries the per-declaration Lean package; and the
Lean development under `lean/IshikiConj51/Ext/`
(namespace `IshikiExt`) formalises the audited statements. The audit notes
record, per theorem, exactly what is formalised and modulo which explicit
external theorems — including where a Lean statement deliberately differs
from the printed one (a density-free parameter set, audited proof-route
repairs, or statements stronger than the preprint's that imply them). The
published `Met`/`BMet`/`CPM` ambient hypotheses are preserved exactly, never
replaced by proxies. Two families of results are covered:

- **Archimedean chain** (v1 numbering: Proposition 2.1, Lemmas 3.1–3.2, Theorems 3.3–3.5
  and 3.8, Corollaries 3.6–3.7 and 3.9): the discrete non-Borelness
  obstruction for `Met(Z)`/`BMet(Z)` in `CPM(Z)`, its component and
  complete-metric refinements, and the transfer "moduli space Borel ⇒ base
  space separable". Ishiki's isometric-extensor theorem (E1,
  arXiv:2407.03030) and Koshino's theorem (E3) enter the Lean statements
  only as explicit hypotheses, never as axioms.
- **Non-Archimedean/ultrametric chain** (v1 numbering: Proposition 2.2, Lemmas 3.10–3.11,
  Theorems 3.12–3.14 and 3.16, Corollaries 3.15 and 3.17): the same
  programme for `R`-valued ultrametrics, with the `UCPM`/`𝒰𝒟^R` ambient
  built from scratch. Ishiki's factorization theorem (E2, Colloq. Math.
  2023) enters as an explicit hypothesis bundle.

Where the audit found a printed proof with a repairable gap, the Lean
development formalises the audited repair rather than the printed route; the
audit note records every such deviation next to the theorem it concerns.
Terminology for both tracks is fixed in `notes/terminology.md`.

## Archival verified core: Ishiki Conjecture 5.1

This repository originally proved and formalised Conjecture 5.1 from Ishiki,
*An isometric extensor of metrics*, arXiv:2407.03030:

> For a discrete space `D` of cardinality `ℵ₁`, `Met(D)` — the metrics compatible
> with the discrete topology, with the supremum-metric topology — is not completely
> metrizable.

That result passed the project's independent mathematical audit and has a sorry-free
Lean 4 formalisation. It is retained as an archival verified core rather than the
active research target.

Archival artifacts:

- `report/report-ja.md` — self-contained Japanese proof report;
- `lean/IshikiConj51/Conj51/` — Lean formalisation of the Conjecture 5.1 proof;
- `notes/proof-audit.md` — historical proof and formalisation audit record;
- `paper/` — the earlier single-author manuscript workspace.

Do not rewrite those artifacts to match the newer joint preprint unless a dedicated
issue explicitly requires a provenance-preserving change.

## Superseded analytic/coanalytic track

An earlier draft attempted a stronger analytic/coanalytic theorem package.
That track is closed and must not be treated as a source of truth: the Borel
statement replaces it, and §5 of `notes/borel-manuscript-20261103-audit.md`
records the claims that must not be reinstated — in particular, the draft's
"not coanalytic" half is not a ZFC theorem. The pointclass-free metric coding
that work produced remains reusable `IshikiExt` infrastructure.

## Repository layout

| Path | Role |
|---|---|
| `lean/IshikiConj51/Ext/` | Lean formalisation of the public-preprint track (`IshikiExt`) |
| `lean/IshikiConj51/Conj51/` | archival Lean proof of Conjecture 5.1 |
| `report/report-ja.md` | archival Japanese Conjecture 5.1 proof |
| `notes/` | mathematical audit, terminology, and literature references |
| `paper/` | archival earlier manuscript workspace |

Module map for `lean/IshikiConj51/Ext/` (v1 theorem numbers are retained for
orientation; labels are the stable identifiers, and the correspondence column
uses the labels of the 2026-11-03 received source):

| Modules | Content | Received-source correspondence |
|---|---|---|
| `BddPMet`, `BoundedCoding` | bounded pseudometric ambient; the star-metric coding and its exact pullback identity | `lem:metric-coding`, `lem:closed-parameter-embedding`, `thm:bounded-discrete-nonborel` → `BddPMet`, `BoundedCoding`; received-source pullback repairs are already reflected in the existing route |
| `Borel`, `CPM`, `Relabel` | discrete non-Borel obstruction (Theorem 3.3) in the bounded and unbounded ambients; arbitrary-carrier relabelling | `thm:bounded-discrete-nonborel`, `cor:discrete-metric-nonborel` → `Borel`, `CPM`, `Relabel`; v1 coverage retained, with the received-source pullback and relative-Borel repairs already reflected in the route |
| `Amalgam`, `Component` | one-point amalgamation; component non-Borelness (Theorem 3.4) | `lem:one-point-amalgamation`, `thm:metric-component-nonborel` → `Amalgam`, `Component`; strengthened to `|Z| ≥ ℵ₁` (#106, PR #114) |
| `Completeness`, `CompleteMetric` | complete-metric branch (Theorem 3.8, Corollary 3.9) | `thm:complete-metric-nonborel`, `cor:complete-metric-borel-separability` → `Completeness`, `CompleteMetric`; received-source complete-amalgam repair is already reflected in this route |
| `GeneralSpace`, `GeneralSeparability` | general-space Borel/separability transfer (Theorem 3.5), E1 as explicit hypothesis | `thm:borel-separability` → `GeneralSpace`, `GeneralSeparability`; received-source BMet transfer and pullback repairs are already reflected in the existing route. `cor:nonseparable-metric-nonborel` → `GeneralComponent` (E1, E1c) |
| `CompleteMetrizability` | Alexandrov–Lavrentiev for a metrizable ambient; Corollaries 3.6 and 3.7 | `thm:complete-metrizability-g-delta`, `cor:metric-space-complete-separability` → `CompleteMetrizability`, `GDeltaCompletelyMetrizable`; `cor:bounded-metric-complete-sigma-compact`'s five-way form → `FiveWay` (E1, E3, E5, E6) |
| `UltraPMet`, `CantorUltra`, `UltraCoding`, `UltraComponent` | discrete ultrametric core (Proposition 2.2, Lemmas 3.10–3.11, Theorems 3.12–3.13) | `prop:dense-aleph1-nonborel-cantor`, `lem:ultrametric-coding`, `lem:closed-ultrametric-parameter-embedding`, `thm:discrete-ultrametric-nonborel`, `thm:ultrametric-component-nonborel` → `UltraPMet`, `CantorUltra`, `UltraCoding`, `UltraComponent`; Cantor witness strengthened to bi-density (#109, PR #116) |
| `UltraGeneral`, `UltraTransfer` | ultrametric transfer (Theorem 3.14, Corollary 3.15), E2 as explicit hypothesis | `thm:ultrametric-borel-separability`, `cor:ultrametric-space-complete-separability` → `UltraGeneral`, `UltraTransfer`; the v1 ambient-transfer repair remains reflected here as an alternative route. `cor:nonseparable-ultrametric-nonborel` and the E2c-route forms of both theorems → `UltraComponentGeneral` (E2c as the explicit hypothesis `hEx`); `lem:ultrametric-extensor-preserving-component` → `UltraNetExtensor`, which proves `hEx` and gives the extensor-hypothesis-free forms of 4.6–4.8 |
| `UltraComplete`, `UltraCompleteTransfer` | complete-ultrametric branch (Theorem 3.16, Corollary 3.17) | `thm:complete-ultrametric-nonborel`, `cor:complete-ultrametric-borel-separability` → `UltraComplete`, `UltraCompleteTransfer`, `UltraPublished` (E2(N1); both the Borel and the completely-metrizable claim) |

## Workflow

GitHub Issues and Pull Requests are the sole work queue and
execution-evidence record; repository documents carry only durable
mathematical, architectural and reference content. Mathematical statement
changes are gated by the corresponding audit note and land through focused,
independently reviewed PRs. Accepted Lean results are sorry-free, introduce
no custom axioms, and include an explained `#print axioms` check recorded in
the PR review trail.

## Lean build

```sh
cd lean
lake exe cache get   # fetch mathlib oleans; never cold-build mathlib
lake build
```

No CI is configured; validation is local/manual.

## License

See `LICENSE`.
