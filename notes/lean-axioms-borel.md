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

Item 4 (relabelling to arbitrary discrete carriers) is not included here: it
was not completed in this issue. It is audited separately below.

# Axiom audit — Issue #57 (general-space transfer, partial)

Checked with `#print axioms <name>` against the built `IshikiConj51`
library (toolchain `leanprover/lean4:v4.32.2`), in a throwaway, untracked
`.lean` file (`import IshikiConj51` plus the `#print axioms` lines), never
committed.

| declaration | file | axioms |
|---|---|---|
| `IshikiExt.exists_aleph1_closed_discrete_separated` | `Ext/GeneralSpace.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.isClosed_range_of_isometry_complete` | `Ext/GeneralSpace.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.MetOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.mem_CPM_MetOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor.image_met_eq_range_inter` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` and no custom axioms in the closure of any declaration above —
only the three standard Lean/Mathlib axioms. `grep -rn sorry` on both files
turns up only the word inside a status comment, not a `sorry` term.

This audit covers everything that landed in #57: the ℵ₁-sized closed
discrete separated set lemma, the closed-isometric-image lemma, the
topology-aware metric locus `CPM.MetOn`, the `IsIsometricExtensor` E1
hypothesis bundle, and the derived `Met`-image identity. The capstone
theorem (`Met(X)` Borel → `SeparableSpace X`) did **not** land in this issue
and is not included above; see the PR body and the follow-up issue for its
exact statement and remaining prerequisites.

# Axiom audit — Issue #63 (#56 item 4, relabelling to arbitrary carriers)

Checked with `#print axioms <name>` against the built `IshikiConj51`
library (toolchain `leanprover/lean4:v4.32.2`), in a throwaway, untracked
`.lean` file (`import IshikiConj51` plus the `#print axioms` lines), never
committed.

| declaration | file | axioms |
|---|---|---|
| `IshikiExt.BddPMet.supDist_comap` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.BddPMet.relabelIsometry` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.preimage_BMet_comap` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.edist_comap` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.relabelIsometry` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.preimage_Met_comap` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.preimage_BMet_comap` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.exists_carrier_aleph_one` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.exists_equiv_extIndex_of_card` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.bmet_not_borel_of_card` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.bmet_not_borel_cpm_of_card` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.met_not_borel_of_card` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` and no custom axioms in the closure of any declaration above —
only the three standard Lean/Mathlib axioms. `grep -rn sorry
lean/IshikiConj51/` turns up only the word inside status comments.

With `met_not_borel_of_card` the repository states the preprint's Theorem 3.3
and its abstract's `Met(Z)` claim in the universal form: for every `D` with
`#D = ℵ₁`, `Met(D)` is not Borel in `CPM(D)`. The hypothesis is satisfiable
(`exists_carrier_aleph_one`), so the statement is not vacuous.
