# Axiom audit — Issue #56 (discrete Borel obstruction)

> Mandated by `notes/borel-preprint-audit.md` §7: "Record `#print axioms`
> output for every top-level theorem ... the expected set is the three
> standard Lean axioms only."

All four capstone theorems below were checked with `#print axioms <name>`
against the built `IshikiConj51` library (toolchain
`leanprover/lean4:v4.32.2`), independently of Codex's own build/axiom claims
— each command was re-run by the shepherding agent in a throwaway,
untracked `.lean` file (`import IshikiConj51` plus the `#print axioms`
lines), never committed.

| theorem | file | audit §7 item | axioms |
|---|---|---|---|
| `IshikiExt.exists_aleph1_nonBorel` | `Ext/Borel.lean` | 1 | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.bmet_not_borel` | `Ext/Borel.lean` | 2 | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.bmet_not_borel_cpm` | `Ext/CPM.lean` | 3 | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.met_not_borel` | `Ext/CPM.lean` | 3 | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` and no custom axioms anywhere in the axiom closure of any of
the four theorems — only the three standard Lean/Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`), which is the same footprint
as every other top-level result in this repository (`Conj51/MainTheorem.lean`,
`Ext/BoundedCoding.lean`).

Item 4 (relabelling to arbitrary discrete carriers) is not included: it was
not completed in this issue and carries no theorems (see the PR body and
the item-4 follow-up issue for scope).
