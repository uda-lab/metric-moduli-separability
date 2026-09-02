# Metric moduli / separability project

Research repository for Lean-assisted verification of results on spaces of
compatible metrics.

## Public-preprint track

The active external source is the joint preprint by Yoshito Ishiki and Tomoki
Uda, **Borelness of Moduli Spaces of Metrics Implies Separability**,
arXiv:2608.19618 (2026), together with the later manuscript source received on
2026-09-02 (archive timestamp 2026-08-27), which is reference-only and lives
outside this repository. The repository verifies it theorem by theorem:
`notes/borel-manuscript-20260827-audit.md` is the mathematical source of truth
(exact statements, verdicts, verified repairs, and external-theorem
dependencies) for the received source, `notes/borel-preprint-audit.md` is the
frozen arXiv v1 record and carries the per-declaration Lean package, and the
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
statement replaces it, and §5 of `notes/borel-manuscript-20260827-audit.md`
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

Module map for `lean/IshikiConj51/Ext/` (theorem numbers are v1's):

| Modules | Content |
|---|---|
| `BddPMet`, `BoundedCoding` | bounded pseudometric ambient; the star-metric coding and its exact pullback identity |
| `Borel`, `CPM`, `Relabel` | discrete non-Borel obstruction (Theorem 3.3) in the bounded and unbounded ambients; arbitrary-carrier relabelling |
| `Amalgam`, `Component` | one-point amalgamation; component non-Borelness (Theorem 3.4) |
| `Completeness`, `CompleteMetric` | complete-metric branch (Theorem 3.8, Corollary 3.9) |
| `GeneralSpace`, `GeneralSeparability` | general-space Borel/separability transfer (Theorem 3.5), E1 as explicit hypothesis |
| `CompleteMetrizability` | Alexandrov–Lavrentiev for a metrizable ambient; Corollaries 3.6 and 3.7 |
| `UltraPMet`, `CantorUltra`, `UltraCoding`, `UltraComponent` | discrete ultrametric core (Proposition 2.2, Lemmas 3.10–3.11, Theorems 3.12–3.13) |
| `UltraGeneral`, `UltraTransfer` | ultrametric transfer (Theorem 3.14, Corollary 3.15), E2 as explicit hypothesis |
| `UltraComplete`, `UltraCompleteTransfer` | complete-ultrametric branch (Theorem 3.16, Corollary 3.17) |

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
