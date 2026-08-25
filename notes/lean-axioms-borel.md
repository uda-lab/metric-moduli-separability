# Axiom audit — Issue #56 (discrete Borel obstruction)

> Mandated by `notes/borel-preprint-audit.md` §7: "Record `#print axioms`
> output for every top-level theorem ... the expected set is the three
> standard Lean axioms only."

All four theorems below were checked with `#print axioms <name>`
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
hypothesis bundle, and the derived `Met`-image identity. The main theorem
(`Met(X)` Borel → `SeparableSpace X`) did **not** land in this issue and is
not included above; see the PR body and the follow-up issue for its exact
statement and remaining prerequisites.

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

# Axiom audit — Issue #66 (Route M package)

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
* **Conditionality.** Both are conditional on the `IsIsometricExtensor`
  bundle (resp. on `hEx`, which quantifies that bundle over closed
  embeddings of the coded carrier). That bundle is **not E1 verbatim**. E1 (Ishiki 2024, Theorem 1.1; audit §3) quantifies over an
  arbitrary closed subset `A ⊆ X` and supplies `Ẽ : CPM(A) → CPM(X)` on the
  continuous-pseudometric ambient of `A`; the Lean bundle fixes an abstract
  carrier with a closed embedding `ι` and takes the extensor already
  transported along `ι`, with a bare `CPM A` domain. For a closed *discrete*
  `A` the two are equivalent — `CPMOn.equivCPM` (proved here) removes the
  continuity constraint on the discrete domain, and relabelling along `ι`
  moves the domain from `↥A` to the abstract carrier — but that second step
  needs a CPMOn-level relabelling layer, which is the outstanding obligation
  of audit §7 item 4 and is **not formalised** *as of this issue*. So E1
  implies the Lean hypothesis (making the Lean theorem at least as strong as
  the E1-conditional statement), but #66 did not check that implication. The
  claim "Lean discharges Theorem 3.5 modulo E1" would overstate what #66
  proves; what it proves is "Lean discharges it modulo the bundle". **This
  paragraph is superseded by the #72 section below**, which closes the gap and
  restates both theorems with E1 itself as the hypothesis.
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

# Axiom audit — Issue #72 (the E1 bridge)

Checked with `#print axioms <name>` against the built `IshikiConj51` library
(toolchain `leanprover/lean4:v4.32.2`), in a throwaway module inside the build
target (`import IshikiConj51.Ext.GeneralSeparability` plus the `#print axioms`
lines), deleted before committing.

| declaration | file | axioms |
|---|---|---|
| `IshikiExt.topology_comap` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.topology_comap_eq_iff` | `Ext/Relabel.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.coe_equivCPM_symm` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.comap` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.comap_coe` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.isometry_comap` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.relabelEquiv` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.relabelEquiv_apply` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.relabelIsometry` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.preimage_MetOn_comap` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensorOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensorOn.toIsIsometricExtensor` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.not_measurableSet_CPM_MetOn_of_isometricExtensorOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` and no custom axioms in the closure of any declaration above —
only the three standard Lean/Mathlib axioms. `grep -rn sorry
lean/IshikiConj51/` turns up only the word inside status comments.

Attribution, superseding the "Conditionality" paragraph of the #66 section:

* `IsIsometricExtensorOn` is **E1's own shape, for one closed subset**, with no
  carrier-specific choices: `A` ranges over subsets of a metrizable `X`, the
  domain is the preprint's `CPM(A)` (`CPMOn ↥A`), and the fields are E1's
  clauses (1) `extension`, (2) `isometry_toCPM` and the inclusion half of the
  "furthermore" clause, `met_preservation` — Route M's share of E1 (audit §4).
  The reverse inclusion of `Ẽ(Met(A)) = Ẽ(CPM(A)) ∩ Met(X)` is not assumed; its
  transported form is derived, in
  `IsIsometricExtensor.image_met_eq_range_inter`. Clauses (3) and (4) are
  omitted; they belong to the §2.10 and §2.12 extensions, and (4) carries the
  extra "`X` completely metrizable" hypothesis of the audit §3 caveat. So the
  hypothesis is implied by E1 and assumes nothing E1 does not give.
* `IsIsometricExtensorOn.toIsIsometricExtensor` is the transport that #66
  described but did not check: for a closed embedding `ι` of a `⊥`-topologised
  carrier, `CPMOn.comap` relabels the domain from `↥(range ι)` to the carrier
  along the homeomorphism `ι` induces, and `CPMOn.equivCPM` then drops it to
  the bare `CPM A`. The relabelling layer is audit §7 item 4 at `CPMOn` level:
  `CPMOn.relabelIsometry` for the ambient, `CPMOn.preimage_MetOn_comap` for
  the locus. The latter rests on `topology_comap` — a relabelled metric induces
  the relabelled topology — which is the general form of `Ext/Relabel.lean`'s
  discrete-carrier `topology_comap_eq_bot`.
* `not_measurableSet_CPM_MetOn_of_isometricExtensorOn` and
  `separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn` are the
  delivered forms of **Theorem 3.5**, hypothesising
  `∀ A, IsClosed A → Nonempty (IsIsometricExtensorOn A)` — E1 quantified as E1
  quantifies itself, over the closed subsets of `X`. "Lean discharges Theorem
  3.5 modulo E1" is accurate for these two: no Lean-side transport is left
  between the hypothesis and the external theorem. The bundle-conditional #66
  theorems remain as the machinery they run on.
* E1's proof stays external. No custom axiom is introduced for it, and the
  hypothesis is discharged nowhere in the repository.

Vacuity:

* `not_measurableSet_CPM_MetOn_of_isometricExtensorOn` has satisfiable
  hypotheses: E1 holds for every metrizable `X`, and a discrete `X` of
  cardinality `ℵ₁` admits the closed embedding `hι`. That E1 holds is
  external, so this is a remark, not a Lean declaration.
* `separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn` inherits the
  situation of the `hEx` version: a one-point `X` satisfies `hMet` (its
  `CPMOn X` is a one-point space) and E1 for both of its closed subsets. Also
  a remark.

# Axiom audit — Issue #79 (Corollaries 3.6 and 3.7)

Checked with `#print axioms <name>` against the built `IshikiConj51` library
(toolchain `leanprover/lean4:v4.32.2`), in a throwaway module inside the build
target (`import IshikiConj51` plus the `#print axioms` lines), deleted before
committing. Every declaration added by this issue is listed, together with the
three delivered capstones of #66/#72 whose proofs this issue refactored, as a
regression pin.

| declaration | file | axioms |
|---|---|---|
| `IshikiExt.exists_isClosedEmbedding_extIndex` | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.measurableSet_of_isCompletelyMetrizableSpace` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.IsBdd` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.mem_BMet_iff` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.BMetOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.mem_CPM_BMetOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.preimage_equivCPM_bmet` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPMOn.preimage_BMetOn_comap` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsBddIsometricExtensorOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsBddIsometricExtensorOn.image_bmet_subset` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor.image_bmet_eq_range_inter` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsIsometricExtensor.not_measurableSet_CPM_BMetOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.not_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_isCompletelyMetrizableSpace_CPM_MetOn_of_isometricExtensorOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_isCompletelyMetrizableSpace_CPM_BMetOn_of_bddIsometricExtensorOn` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separableSpace_of_sigmaCompactSpace` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.isCompletelyMetrizableSpace_CPM_BMetOn_iff_sigmaCompactSpace` | `Ext/CompleteMetrizability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_measurableSet_CPM_MetOn_of_extensors` (regression pin) | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn` (regression pin) | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.not_measurableSet_CPM_MetOn_of_isometricExtensorOn` (regression pin) | `Ext/GeneralSeparability.lean` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` and no custom axioms in the closure of any declaration above —
only the three standard Lean/Mathlib axioms. `grep -rn sorry
lean/IshikiConj51/` turns up only the word inside status comments.

Attribution:

* **E4d** is not hypothesised anywhere: `isGδ_of_isCompletelyMetrizableSpace`
  (`Conj51/GDeltaComplete.lean`) is a proof, and
  `isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace` only moves it to a
  metrizable ambient, which is what `CPMOn X` is. So Corollary 3.6's
  Alexandrov–Lavrentiev step is discharged, not assumed.
* **E1** enters as `IsIsometricExtensorOn` (clauses (1), (2), the inclusion half
  of the "furthermore" clause) and, for the bounded transfer, as
  `IsBddIsometricExtensorOn`, which adds clause (3) `Ẽ(BMet(A)) ⊆ BMet(X)` to
  the same extensor. Clause (4) is not assumed anywhere. Both are hypotheses of
  the statements that use them; neither is an axiom or an instance.
* **E3** (Koshino) enters Corollary 3.7 as the hypothesis
  `SeparableSpace X → (SigmaCompactSpace X ↔ IsCompletelyMetrizableSpace
  ↥(CPM.BMetOn X))` — the theorem for this `X`, separability hypothesis intact.
  It is used in both directions of the corollary and is discharged nowhere.
  Audit §2.10's caveat on its citation number is recorded, not resolved.
* The `⇒` direction of Corollary 3.7 does **not** route through Corollary 3.6.
  `separable_of_isCompletelyMetrizableSpace_CPM_BMetOn_of_bddIsometricExtensorOn`
  is proved from the `BMet` analogue of Theorem 3.5, which is what audit §2.10
  identifies as the missing link in the preprint.

Vacuity:

* Both corollaries have satisfiable hypotheses: E1 holds for every metrizable
  `X`, E3 for every separable metrizable `X`, and each corollary's own
  hypothesis holds for a one-point `X`: its `CPMOn X` is a one-point space, so
  every subset of it is completely metrizable, and it is σ-compact. That E1 and
  E3 hold is external, so this is a remark, not a Lean declaration.

# Axiom audit — Issue #84 (Theorem 3.4, components and amalgamation)

Checked with `#print axioms <name>` against the built `IshikiConj51` library
(toolchain `leanprover/lean4:v4.32.2`), in a throwaway, untracked `.lean` file
(`import IshikiConj51` plus the `#print axioms` lines), never committed. The
same locked session ran `lake build` immediately before, so the audit is
against the artifacts the build produced: `Build completed successfully
(8672 jobs)`.

All 61 top-level declarations introduced by `Ext/Amalgam.lean` and
`Ext/Component.lean` are listed. Every one of them reports exactly
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`, no custom
axiom, and no declaration with a different footprint.

| declaration | file | axioms |
|---|---|---|
| `IshikiExt.IsMetricOn.nonneg` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.IsMetricOn.toIsPMetricOn` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.amalgam` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.amalgam_mem_mem` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.amalgam_mem_notMem` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.amalgam_notMem_mem` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.amalgam_notMem_notMem` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.isMetricOn_amalgam` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.amalgam_topology_eq_bot` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.topology_eq_bot_of_amalgam` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.abs_amalgam_sub_le` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.abs_amalgam_sub_amalgam_le` | `Ext/Amalgam.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.component` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.component_subset_Met` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.self_mem_component` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.component_eq_of_mem` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.metSetoid` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.Components` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.componentSet` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.componentSet_mk` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.discreteFn` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.discreteFn_self` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.discreteFn_of_ne` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.discreteFn_nonneg` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.isMetricOn_discreteFn` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.topology_discreteFn_eq_bot` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.discrete` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.discrete_mem_Met` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.nonempty_Met` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.CPM.nonempty_Components` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.exists_aleph1_ball` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.one_le_dExt_anchor` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.base` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.base_val` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.ballMetric` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.isMetricOn_ballMetric` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.ballMetric_le_four` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.ballMetric_topology_eq_bot` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.ballMetric_topology_ne_bot` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.one_le_ballMetric_base` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.abs_ballMetric_sub_le` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.metric` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.isMetricOn_metric` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.psi` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.psi_val` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.metric_topology_eq_bot` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.mem_Met_psi_iff` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.abs_metric_sub_base_le` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.edist_psi_base_le` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.edist_psi_base_lt_top` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.lipschitzWith_psi` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.continuous_psi` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.measurable_psi` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.preimage_component_psi` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.isCompact_range_psi` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.range_inter_component` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.measurableSet_of_measurableSet_image` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.ComponentSetup.not_measurableSet_component` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.component_not_measurableSet` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |
| `IshikiExt.componentSet_not_measurableSet` | `Ext/Component.lean` | `[propext, Classical.choice, Quot.sound]` |

`grep -n sorry` on both files matches only the phrase "sorry-free" in their
status headers.

Scope note: `Ext/Amalgam.lean` is carrier-agnostic machinery — one-point
amalgamation of a metric on a carrier with a metric on a subset — and
`Ext/Component.lean` is Theorem 3.4 itself, in the representative form
(`component_not_measurableSet`) and over the quotient `𝐌_{<∞}(Z)`
(`componentSet_not_measurableSet`). Neither is in the import graph of
`Ext/GeneralSeparability.lean`, so the Theorem 3.5 package's axiom footprint
is unchanged by this issue.

# Axiom audit — Issue #81 (discrete non-Archimedean core, 3.10–3.13)

Every new top-level declaration of this issue was checked with
`#print axioms <name>` against the built `IshikiConj51` library (toolchain
`leanprover/lean4:v4.32.2`), in a throwaway, untracked `.lean` file
(`import IshikiConj51` plus one `#print axioms` line per declaration),
deleted before committing.  182 declarations were checked; 180 report
exactly `[propext, Classical.choice, Quot.sound]` and 2 report
"does not depend on any axioms" (`IshikiExt.UltraIndex`,
`IshikiExt.exists_spoke`).  No `sorryAx` and no custom axiom appears in the
closure of any of them.

The declarations, in file order:

`Ext/UltraPMet.lean`:

* `IshikiExt.RangeSet`
* `IshikiExt.RangeSet.max_mem`
* `IshikiExt.RangeSet.IsCharacteristic`
* `IshikiExt.RangeSet.IsScale`
* `IshikiExt.RangeSet.IsScale.antitone`
* `IshikiExt.RangeSet.IsScale.lt_iff_lt`
* `IshikiExt.RangeSet.IsScale.le_head`
* `IshikiExt.RangeSet.IsScale.nonneg`
* `IshikiExt.RangeSet.IsScale.exists_lt`
* `IshikiExt.RangeSet.smallElt`
* `IshikiExt.RangeSet.smallElt_mem`
* `IshikiExt.RangeSet.smallElt_pos`
* `IshikiExt.RangeSet.smallElt_lt`
* `IshikiExt.RangeSet.scale`
* `IshikiExt.RangeSet.scale_pos`
* `IshikiExt.RangeSet.scale_mem`
* `IshikiExt.RangeSet.scale_lt_succ`
* `IshikiExt.RangeSet.scale_lt_one_div`
* `IshikiExt.RangeSet.tendsto_scale`
* `IshikiExt.RangeSet.exists_isScale`
* `IshikiExt.RangeSet.isCharacteristic_of_isScale`
* `IshikiExt.IsUltraPMetOn`
* `IshikiExt.IsUltraPMetOn.nonneg`
* `IshikiExt.IsUltraPMetOn.dist_triangle`
* `IshikiExt.IsUltraPMetOn.eq_of_lt`
* `IshikiExt.IsUltraPMetOn.toIsMetricOn`
* `IshikiExt.UCPM`
* `IshikiExt.UCPM.nonneg`
* `IshikiExt.UCPM.tolerances`
* `IshikiExt.UCPM.edist`
* `IshikiExt.UCPM.tolerances_comm`
* `IshikiExt.UCPM.edist_le_ofReal`
* `IshikiExt.UCPM.ofReal_le_edist`
* `IshikiExt.UCPM.le_max_of_edist_le`
* `IshikiExt.UCPM.le_of_mem_tolerances`
* `IshikiExt.UCPM.edist_self`
* `IshikiExt.UCPM.edist_comm`
* `IshikiExt.UCPM.max_mem_tolerances`
* `IshikiExt.UCPM.ofReal_max`
* `IshikiExt.UCPM.iInf_ofReal_max_le`
* `IshikiExt.UCPM.edist_triangle_max`
* `IshikiExt.UCPM.edist_triangle`
* `IshikiExt.UCPM.eq_of_edist_eq_zero`
* `IshikiExt.UCPM.instEDist`
* `IshikiExt.UCPM.instPseudoEMetricSpace`
* `IshikiExt.UCPM.instEMetricSpace`
* `IshikiExt.UCPM.edist_eq`
* `IshikiExt.UCPM.comap`
* `IshikiExt.UCPM.comap_val`
* `IshikiExt.UCPM.sup`
* `IshikiExt.UCPM.sup_val`
* `IshikiExt.UCPM.tolerances_comap`
* `IshikiExt.UCPM.edist_comap`
* `IshikiExt.UCPM.isometry_comap`
* `IshikiExt.UCPM.IsCompatible`
* `IshikiExt.UCPM.isCompatible_comap_iff`
* `IshikiExt.UMet`
* `IshikiExt.mem_UMet`
* `IshikiExt.UComponent`
* `IshikiExt.mem_UComponent`
* `IshikiExt.preimage_UMet_comap`
* `IshikiExt.preimage_UComponent_comap`
* `IshikiExt.completeSpace_of_cauchySeq_eventually_const`

`Ext/CantorUltra.lean`:

* `IshikiExt.cardinal_measurableSet_le_continuum`
* `IshikiExt.cardinal_eq_continuum_of_measurableSet`
* `IshikiExt.exists_aleph1_nonMeasurable`
* `IshikiExt.mk_cantor`
* `IshikiExt.exists_dense_aleph1_nonBorel_cantor`
* `IshikiExt.cantorDist`
* `IshikiExt.cantorDist_self`
* `IshikiExt.cantorDist_of_ne`
* `IshikiExt.cantorDist_comm`
* `IshikiExt.cantorDist_nonneg`
* `IshikiExt.cantorDist_pos_of_ne`
* `IshikiExt.cantorDist_eq_zero_iff`
* `IshikiExt.cantorDist_mem`
* `IshikiExt.cantorDist_le_head`
* `IshikiExt.cantorDist_triangle_max`
* `IshikiExt.cantorDist_isosceles`
* `IshikiExt.cantorDist_lt_iff`
* `IshikiExt.cantorDist_lt_of_mem_cylinder`
* `IshikiExt.exists_mem_cantorDist_lt`
* `IshikiExt.continuous_of_edist_le_cantorDist`

`Ext/UltraCoding.lean`:

* `IshikiExt.UltraIndex`  (no axioms)
* `IshikiExt.card_ultraIndex`
* `IshikiExt.uRadius`
* `IshikiExt.uRadius_none`
* `IshikiExt.uRadius_some`
* `IshikiExt.uRadius_nonneg`
* `IshikiExt.uRadius_le_head`
* `IshikiExt.uRadius_mem`
* `IshikiExt.cantorDist_le_uRadius`
* `IshikiExt.head_le_uRadius`
* `IshikiExt.clusterDist`
* `IshikiExt.clusterDist_self`
* `IshikiExt.clusterDist_comm`
* `IshikiExt.clusterDist_nonneg`
* `IshikiExt.clusterDist_le`
* `IshikiExt.le_clusterDist_of_ne`
* `IshikiExt.exists_spoke`  (no axioms)
* `IshikiExt.clusterDist_triangle_max`
* `IshikiExt.exists_head_le_clusterDist`
* `IshikiExt.cantorDist_le_clusterDist`
* `IshikiExt.exists_isolating_radius`
* `IshikiExt.dU`
* `IshikiExt.dU_of_fst_eq`
* `IshikiExt.dU_of_fst_ne`
* `IshikiExt.dU_same`
* `IshikiExt.dU_diff`
* `IshikiExt.dU_self`
* `IshikiExt.dU_comm`
* `IshikiExt.dU_nonneg`
* `IshikiExt.dU_le_head`
* `IshikiExt.dU_mem`
* `IshikiExt.dU_triangle_max`
* `IshikiExt.dU_isUltraPMetOn`
* `IshikiExt.dU_pos_of_ne`
* `IshikiExt.dU_isMetricOn`
* `IshikiExt.dU_topology_eq_bot`
* `IshikiExt.dU_topology_ne_bot`
* `IshikiExt.dU_completeSpace`
* `IshikiExt.phiU`
* `IshikiExt.phiU_val`
* `IshikiExt.uRadius_le_max`
* `IshikiExt.dU_le_max`
* `IshikiExt.edist_phiU_le`
* `IshikiExt.exists_separating_pair`
* `IshikiExt.le_edist_phiU`
* `IshikiExt.edist_phiU`
* `IshikiExt.continuous_phiU`
* `IshikiExt.injective_phiU`
* `IshikiExt.isCompatible_phiU_iff`
* `IshikiExt.preimage_UMet_phiU`
* `IshikiExt.isCompact_range_phiU`
* `IshikiExt.isClosed_range_phiU`
* `IshikiExt.image_compl_eq_range_inter_UMet`
* `IshikiExt.isClosed_image_phiU`
* `IshikiExt.ucpmMeasurableSpace`
* `IshikiExt.ucpmBorelSpace`
* `IshikiExt.umet_not_borel`
* `IshikiExt.exists_equiv_ultraIndex_of_card`
* `IshikiExt.umet_not_borel_of_card`
* `IshikiExt.exists_mem_UMet_of_card`

`Ext/UltraComponent.lean`:

* `IshikiExt.exists_countable_cofinal`
* `IshikiExt.uBall`
* `IshikiExt.mem_uBall`
* `IshikiExt.mem_uBall_self`
* `IshikiExt.uBall_dist_le`
* `IshikiExt.uBall_isosceles`
* `IshikiExt.exists_radius_not_countable`
* `IshikiExt.uRetract`
* `IshikiExt.uInto`
* `IshikiExt.uRetract_of_mem`
* `IshikiExt.uRetract_of_notMem`
* `IshikiExt.uInto_of_mem`
* `IshikiExt.uInto_of_notMem`
* `IshikiExt.uAmalgam`
* `IshikiExt.uAmalgam_val`
* `IshikiExt.base_le_uAmalgam`
* `IshikiExt.coding_le_uAmalgam`
* `IshikiExt.uAmalgam_in_in`
* `IshikiExt.uAmalgam_out_out`
* `IshikiExt.edist_uAmalgam_le`
* `IshikiExt.psiU`
* `IshikiExt.psiU_val`
* `IshikiExt.psiU_in_in`
* `IshikiExt.psiU_out_out`
* `IshikiExt.psiU_val_symm`
* `IshikiExt.edist_psiU_lt_top`
* `IshikiExt.psiU_topology_eq_bot`
* `IshikiExt.psiU_topology_ne_bot`
* `IshikiExt.isCompatible_psiU_iff`
* `IshikiExt.edist_psiU_le`
* `IshikiExt.edist_psiU`
* `IshikiExt.continuous_psiU`
* `IshikiExt.preimage_UComponent_psiU`
* `IshikiExt.isCompact_range_psiU`
* `IshikiExt.image_compl_eq_range_inter_UComponent`
* `IshikiExt.isClosed_image_psiU`
* `IshikiExt.ucomponentMeasurableSpace`
* `IshikiExt.ucomponentBorelSpace`
* `IshikiExt.ucomponent_not_borel_of_card`

