# Metric moduli / separability project

Research repository for Lean-assisted verification of results on spaces of compatible metrics.

## Current project

The active external source is the joint preprint by Yoshito Ishiki and Tomoki Uda,
**Borelness of Moduli Spaces of Metrics Implies Separability**, arXiv:2608.19618 (2026).

The repository is being realigned to that public preprint after an earlier, stronger
analytic/coanalytic draft was abandoned. The exact public theorem package is being
re-audited in **Issue #55** before new top-level Lean statements are accepted.

Current work queue:

- **#55** — theorem-by-theorem audit of arXiv:2608.19618 and Lean target map;
- **#56** — formalise the published discrete Borel obstruction;
- **#57** — formalise the general-space Borel/separability transfer;
- **#48 / PR #49** — Borel-first Japanese descriptive-set-theory study note;
- **#58** — repository metadata cleanup and proposed rename to `metric-moduli-separability`.

The merged `IshikiExt` Layer 1 development (PR #52) remains reusable: it proves the
bounded star-metric coding, Lipschitz estimates and the exact pullback identity for
an arbitrary parameter set, without assuming any analytic/coanalytic pointclass.

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

Issues #46–#47 and draft PR #50 record the August 2026 attempt to prove a stronger
analytic/coanalytic theorem package. That track is closed and must not be treated as
the active source of truth. In particular, the draft's recipe-based claim that a
dense `ℵ₁`-sized set of reals is simultaneously non-analytic and non-coanalytic is
not a ZFC theorem: in any ccc forcing extension of `L` keeping `ω₁^L = ω₁` (e.g.
adding `ℵ₂` Cohen reals), the largest thin `Π¹₁` set `C₁` (Kechris 1975; Guaspari;
Sacks) is a coanalytic dense set of cardinality `ℵ₁`, a legitimate output of the
recipe — so no ZFC proof of the "not coanalytic" half can exist for that recipe. By
Mansfield–Solovay, a ZFC-safe repair would need `S ⊄ L[a]` for every real `a`, which
the recipe does not supply. Only the asymmetric "not analytic" half (from
`ℵ₁ < 𝔠` and Souslin's perfect set theorem) survives in ZFC. See
`notes/borel-preprint-audit.md` §5 for the full account. The repair this raised was
an author-level decision point in the superseded draft; the published joint preprint
replaces the whole package. Valid pointclass-free metric coding from that work
survives separately in PR #52.

## Repository layout

| Path | Role |
|---|---|
| `lean/IshikiConj51/Conj51/` | archival Lean proof of Conjecture 5.1 |
| `lean/IshikiConj51/Ext/` | reusable coding infrastructure for the joint-work track |
| `report/report-ja.md` | archival Japanese Conjecture 5.1 proof |
| `notes/` | literature, audit and terminology records |
| `STATUS.md` | project status; being reset under #58 after #55 fixes the theorem map |
| `paper/` | archival earlier manuscript workspace |

## Workflow

GitHub Issues are the work queue. Mathematical statement changes should be gated by
the corresponding audit issue and then implemented through a focused PR. Do not
introduce custom axioms; accepted Lean verification should be sorry-free and include
an explained `#print axioms` check.

## Lean build

```sh
cd lean
lake build
```

No CI is configured; validation is local/manual.

## License

See `LICENSE`.
