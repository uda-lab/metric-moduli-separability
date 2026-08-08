# ishiki-conjecture

Research repository for **Conjecture 5.1** from Ishiki (2021), which concerns the
complete metrizability of the space Met(D) of metrics on a discrete space D.

## Statement under investigation

> For a discrete space D of cardinality ℵ₁, the space Met(D) equipped with the
> supremum-metric topology is **not** completely metrizable.

The current argument is a **proof candidate** only.  It has not yet survived
independent mathematical audit.  See `STATUS.md` for the current state and
`notes/proof-audit.md` for open obligations.

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
| `LEM-STAR-METRIC` | Parameterised star-type metric family on D |
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

## License

See `LICENSE`.
