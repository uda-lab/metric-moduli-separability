# ishiki-conjecture

Research repository for **Conjecture 5.1** from Ishiki,
*An isometric extensor of metrics*, arXiv:2407.03030 (2024).

## Statement under investigation

> For a discrete space D of cardinality ℵ₁, the space Met(D) — the set of
> metrics on D **compatible with the discrete topology**, equipped with the
> supremum-metric topology — is **not** completely metrizable.

**Note on Met(D):** A metric $d$ on $D$ is *compatible with the discrete topology*
if the metric topology induced by $d$ equals the discrete topology.
For an infinite set $D$ this is a non-trivial condition: not every metric on the
underlying set $D$ is compatible with the discrete topology.

The argument has passed the project's internal verification gates: an
independent end-to-end mathematical audit (Issue #10) and a sorry-free Lean 4
formalisation whose `#print axioms` shows only the three standard axioms.
On this basis the owner lifted the **proof candidate** label on 2026-08-09
(PR #29 comment).  The result has not yet been reviewed by any outside party
or journal.  See `STATUS.md` for the current state and
`notes/proof-audit.md` for the audit records.

## Repository layout

| Path | Role |
|------|------|
| `report/report-ja.md` | Self-contained Japanese proof report — **mathematical source of truth** |
| `lean/` | Lean 4 / Mathlib formalisation |
| `paper/main.tex` | Submission-ready English paper (draft after audit passes) |
| `notes/literature.md` | Verified references |
| `notes/proof-audit.md` | Open proof obligations and failed attempts |
| `notes/terminology.md` | Notation and terminology reference |
| `STATUS.md` | Concise current project state |

## Stable claim IDs

| ID | Description |
|----|-------------|
| `LEM-A-EXISTS` | ∃ A ⊆ [0,1] with \|A\| = ℵ₁ and A not Fσ |
| `LEM-STAR-METRIC` | Parameterised star-type family of compatible metrics on D |
| `LEM-CLOSED-IMAGE` | The bi-Lipschitz embedding Y → Met(D) has closed image |
| `THM-CONJ51` | Met(D) is not completely metrizable (for \|D\| = ℵ₁) |

The same IDs are used in the report, Lean source, and paper.

## Workflow

* GitHub Issues are the work queue.
* Commits should correspond to one issue or one coherent mathematical change.
* Do not alter a claim without checking the report statement **and** any Lean
  theorem already depending on it.
* Record failed proof attempts in `notes/proof-audit.md`.
* Do not introduce custom axioms; use `sorry` only during exploration and track
  every instance explicitly.

## Lean build

```sh
cd lean
lake build
```

No CI is configured.  Local / manual validation is sufficient at this stage.

## Building PDF / TeX Report

To compile `report/report-ja.md` into PDF or TeX using Pandoc and LuaLaTeX:

```sh
cd report

# Compile to PDF
pandoc report-ja.md -o report-ja.pdf --pdf-engine=lualatex -V documentclass=bxjsarticle -V classoption=lualatex,ja=standard

# Generate TeX file
pandoc report-ja.md -o report-ja.tex -s --pdf-engine=lualatex -V documentclass=bxjsarticle -V classoption=lualatex,ja=standard
```

## License

See `LICENSE`.
