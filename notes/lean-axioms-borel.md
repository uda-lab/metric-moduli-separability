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

Attribution, following audit §2.6 (which records that the preprint's body
states Theorem 3.3 for `BMet(Z)` while the `Met(Z)` phrasing appears only in
the abstract and introduction):

* `bmet_not_borel_cpm_of_card` is **Theorem 3.3** in universal form — for
  every `D` with `#D = ℵ₁`, `BMet(D)` is not Borel in `CPM(D)`;
* `met_not_borel_of_card` is the **abstract/introduction `Met(Z)` claim** in
  universal form — `Met(D)` is not Borel in `CPM(D)`;
* `bmet_not_borel_of_card` is the bounded-ambient statement of §7 item 2,
  which the preprint does not state in that ambient.

The hypothesis `#D = ℵ₁` is satisfiable (`exists_carrier_aleph_one`), so none
of the three is vacuous.

# Axiom audit — Issue #66 (Route M capstone)

Checked with `#print axioms <name>` against the built `IshikiConj51` library
(toolchain `leanprover/lean4:v4.32.2`), in a throwaway module inside the build
target (`import IshikiConj51.Ext.GeneralSeparability` plus the `#print axioms`
lines), deleted before committing.

| declaration | file | axioms |
|---|---|---|
| `IshikiExt.CPM.ofReal_abs_sub_le_edist` | `Ext/CPM.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.abs_sub_lt_of_edist_lt` | `Ext/CPM.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.edist_le_ofReal` | `Ext/CPM.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.instCompleteSpace` | `Ext/CPM.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.instEMetricSpace` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.edist_eq` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.equivCPM` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.equivCPM_apply` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.preimage_equivCPM_met` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.cpmOnMeasurableSpace` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.cpmOnBorelSpace` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.MetOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.mem_CPM_MetOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor.image_met_eq_range_inter` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor.not_measurableSet_CPM_MetOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor.not_separableSpace` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_measurableSet_CPM_MetOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_measurableSet_CPM_MetOn_of_extensors` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.isClosed_range_of_isometry_complete` | `Ext/GeneralSpace.lean` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` and no custom axioms in the closure of any declaration above —
only the three standard Lean/Mathlib axioms. `grep -rn sorry
lean/IshikiConj51/` turns up only the word inside status comments.

The last five rows are re-checks: `CPM.MetOn`, `mem_CPM_MetOn`,
`IsIsometricExtensor`, `image_met_eq_range_inter` and
`isClosed_range_of_isometry_complete` were audited under #57, and all five
statements changed in this issue (`CPM.MetOn` and the extensor's codomain
moved to the continuous-pseudometric ambient `CPMOn X`;
`isClosed_range_of_isometry_complete` was generalised to `EMetricSpace`), so
the earlier rows in the #57 section above are superseded by these.

Attribution, following audit §2.6 and §2.8:

* `IsIsometricExtensor.not_measurableSet_CPM_MetOn` and
  `separable_of_measurableSet_CPM_MetOn_of_extensors` target **Theorem 3.5**
  (`thm:borel-separability`, the general-space separability statement) — the
  first contrapositively, the second in the published phrasing. They are not
  Theorem 3.3; the preprint's body states 3.3 as the `BMet(Z)` claim on a
  discrete carrier, which is `Ext/Relabel.lean`'s
  `bmet_not_borel_cpm_of_card`.
* **What the conditionality is, exactly.** Both are conditional on the
  `IsIsometricExtensor` bundle (resp. on `hEx`, which quantifies that bundle
  over closed embeddings of the coded carrier). That bundle is **not E1
  verbatim**. E1 (Ishiki 2024, Theorem 1.1; audit §3) quantifies over an
  arbitrary closed subset `A ⊆ X` and supplies `Ẽ : CPM(A) → CPM(X)` on the
  continuous-pseudometric ambient of `A`; the Lean bundle fixes an abstract
  carrier with a closed embedding `ι` and takes the extensor already
  transported along `ι`, with a bare `CPM A` domain. For a closed *discrete*
  `A` the two are equivalent — `CPMOn.equivCPM` (proved here) removes the
  continuity constraint on the discrete domain, and relabelling along `ι`
  moves the domain from `↥A` to the abstract carrier — but that second step
  needs a CPMOn-level relabelling layer, which is the outstanding obligation
  of audit §7 item 4 and is **not formalised**. So E1 implies the Lean
  hypothesis (making the Lean theorem at least as strong as the
  E1-conditional statement), but Lean has not checked that implication. The
  claim "Lean discharges Theorem 3.5 modulo E1" would overstate what is
  proved; what is proved is "Lean discharges it modulo the bundle".
* No custom axiom is introduced for E1 or for the bundle.

Vacuity:

* `separable_of_measurableSet_CPM_MetOn` (the literal statement of the issue
  text) **has jointly inconsistent hypotheses**, and this is proved, not
  merely asserted: `IsIsometricExtensor.not_separableSpace` shows that a
  fixed extensor bundle out of the coded carrier already refutes
  `SeparableSpace X`, with no Borel hypothesis. Its Lean proof therefore runs
  through `False.elim`. It is recorded as a labelled corollary and is not the
  result of the issue.
* `separable_of_measurableSet_CPM_MetOn_of_extensors` quantifies the extensor
  over closed discrete copies of the carrier instead of fixing one, and its
  hypotheses are not jointly inconsistent: `hEx` is satisfiable vacuously
  whenever `X` admits no closed embedding of the (uncountable, discrete)
  coded carrier — which is exactly the situation the conclusion asserts. This
  is the form in which `exists_aleph1_closed_discrete_separated` is consumed.
