# Comparator pilot contract (issue #139)

## Scope

A scoped Comparator pilot on one `IshikiExt` result: `lean/scripts/check-comparator.sh`
(`lake comparator`) checks that `IshikiExt.isClopen_setOf_edist_lt_top`
(`lean/IshikiConj51/Ext/BMetClopen.lean`) still proves the frozen statement in
`lean/ComparatorChallenge/Reference.lean`, using only the permitted axioms. It is optional and
manual: this repository has no gate script and no CI, and none is added by this pilot.

## What is frozen

- **Statement gate.** `notes/borel-manuscript-20261103-audit.md` §2.2 `def:finite-distance-components`
  (**PASS**) and the §7.1 correspondence row for "standard lemma … 2.12 (clopen)". The target proves
  a general fact about extended pseudometric spaces (no `IshikiExt`/`CPM`/`Met` object beyond
  `PseudoEMetricSpace`), so `definition_names` is empty — this pilot does not exercise drift of a
  project-defined object.
- **Reference.** `lean/ComparatorChallenge/Reference.lean`, imports only Mathlib, never
  `IshikiConj51`. Authored from the audit note's description, not copied from or derived against
  `BMetClopen.lean`; closed by an independent proof. A different model from the implementer compared
  it against the audit note and the production statement before the pull request opened (see the
  pull request for the reviewer identity and the reviewed blob SHA).
- **Config.** `lean/comparator.json`: `challenge_module = "ComparatorChallenge.Reference"`,
  `solution_module = "IshikiConj51.Ext.BMetClopen"` (the defining module, not the library root, to
  bound export cost), `theorem_names = ["IshikiExt.isClopen_setOf_edist_lt_top"]`,
  `definition_names = []`, `permitted_axioms = ["propext", "Classical.choice", "Quot.sound"]`.
  `lean/scripts/check-comparator.sh` refuses any config that drifts from this exact shape.

## What Comparator does and does not establish

Agreement with the already-reviewed reference, not fidelity to the manuscript:

- **Source fidelity** (does the reference correctly translate the audit note) is established only
  by the independent reviewer reading the source, before any proof work on the reference — never by
  Comparator, which never reads the manuscript or the audit note.
- **Proof construction and kernel checking** (does the production theorem actually hold, sorry-free,
  with only the permitted axioms) is established by the ordinary build and the `#print axioms` audit
  recorded on the pull request — independently of whether the statement is faithful to any source.
- **Comparator agreement** (does the production theorem, as built, still state exactly the already
  reviewed reference's statement and use only the permitted axioms) is the only thing
  `lean/scripts/check-comparator.sh` establishes. A clean Comparator run never substitutes for either
  of the first two checks.

## Pilot finding: Comparator's statement match is exact on universe-parameter names

`lake comparator` (`Lake.Check.compareAt`) accepts a theorem target only when the challenge's and
solution's exported `ConstantVal`s are *literally* equal, including the list of universe parameter
*names* — Lean's kernel represents universe polymorphism by name, not by de Bruijn position, so two
declarations that are the identical proposition up to a consistent universe renaming are exported as
unequal `ConstantVal`s whenever an auto-bound universe variable happens to receive a different name
on each side.

The production theorem's universe variable is named `u_2`, not the otherwise-expected `u_1`, because
its host file (`BMetClopen.lean`) carries an unrelated, unused ambient `variable {Z : Type*}` that
reserves `u_1` for the rest of that file's section, even though `Z` never appears in this theorem's
statement. The reference in `Reference.lean` pins its own universe parameter to the same name
(`theorem isClopen_setOf_edist_lt_top.{u_2} {X : Type u_2} …`) to match; leaving it as an unpinned
`Type*` exports it as `u_1` and Comparator rejects the match with "Challenge and solution theorem
statement do not match" despite the two statements being the same proposition.

This pin is coupled to `BMetClopen.lean`'s *current* section-variable layout, not to the reviewed
mathematics: if that file's section variables are ever reordered, reindexing which auto-bound name
this theorem's universe receives, the pin in `Reference.lean` would need to be re-derived (compare
`set_option pp.universes true in #print IshikiExt.isClopen_setOf_edist_lt_top` from each module in an
untracked scratch file) and is not otherwise detected — nothing else in this repository checks it. A
future Comparator target should prefer a statement with no universe parameter (as the pilot this
ported from did) to avoid this class of false rejection entirely.

## Contract change

A change to the target theorem, the reference statement, `definition_names`, or
`permitted_axioms` needs a scoped Issue, an independently authored replacement reference, and a
source ↔ Lean review by a model other than the implementer, before any proof work on the new
reference.
