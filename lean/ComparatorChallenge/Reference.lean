import Mathlib.Topology.EMetricSpace.Defs

/-!
# Frozen Comparator reference: the finite-distance locus is clopen

Independently authored statement, **not derived from or copied against**
`IshikiConj51/Ext/BMetClopen.lean`. It restates, in its own words and its own
proof, the general fact behind `notes/borel-manuscript-20261103-audit.md`
§2.2 `def:finite-distance-components` (**PASS**) and the §7.1 correspondence
row for "standard lemma … 2.12 (clopen)": in an extended pseudometric space,
the set of points at finite distance from a fixed point is clopen, because
both that set and its complement absorb the radius-`1` ball around every one
of their points.

This module is the frozen Comparator target for the pilot authorised on
issue #139. It imports only Mathlib, and must never import `IshikiConj51`.
Comparator kernel-compares two independent exports of the *same* fully
qualified declaration name, one from this challenge module and one from the
production solution module, so this theorem is declared in the `IshikiExt`
namespace to match `IshikiExt.isClopen_setOf_edist_lt_top`
(`IshikiConj51/Ext/BMetClopen.lean`) — a name collision required by
Comparator's own comparison mechanism, not a dependency on that module.

**Pilot finding (not a pre-existing contract, discovered while wiring this
target): the explicit universe parameter name `u_2` below is load-bearing.**
`lake comparator` (`Lake.Check.compareAt`) accepts a theorem target only when
the challenge's and solution's exported `ConstantVal`s are literally equal,
including the `levelParams` *names* — Lean's kernel represents universe
polymorphism by name, not by de Bruijn position, so two declarations that are
alpha-equivalent up to a consistent universe renaming are exported as
*unequal* `ConstantVal`s if an auto-bound universe variable happened to pick
different names. The production `isClopen_setOf_edist_lt_top` sits in a
section with an unrelated, unused ambient `variable {Z : Type*}`
(`IshikiConj51/Ext/BMetClopen.lean`, module-wide, consumed by other
declarations in that file); that variable's own type is auto-named `u_1`,
pushing this theorem's own `{X : Type*}` to the next free name, `u_2`, even
though `Z` never appears in its statement. Naming this file's own `X`
unpinned (`Type*`) exports it as `u_1` instead and Comparator rejects the
match with "Challenge and solution theorem statement do not match" despite
the two statements being the identical proposition up to a universe
renaming. Pinning `u_2` here is therefore coupled to the *current* section
layout of the host file of the solution module, not to anything in the
reviewed mathematics; if that file's section variables are ever reordered,
this pin would need to be re-derived from the production export, and the PR
documents this as a limitation of Comparator for universe-polymorphic
targets, not a property of the statement itself.
-/

open scoped ENNReal

namespace IshikiExt

/-- **The finite-`edist`-distance locus of a point is clopen.** For a fixed
`x` in an extended pseudometric space, `{y | edist x y < ⊤}` is both open and
closed: a point of the set keeps every point within distance `1` of it inside
the set (the two finite distances add to something finite), and a point
outside the set keeps every point within distance `1` of it outside the set
as well (an infinite distance cannot be rescued by adding a finite one). -/
theorem isClopen_setOf_edist_lt_top.{u_2} {X : Type u_2} [PseudoEMetricSpace X] (x : X) :
    IsClopen {y : X | edist x y < ⊤} := by
  have hopen : IsOpen {y : X | edist x y < ⊤} := by
    rw [EMetric.isOpen_iff]
    rintro y (hy : edist x y < ⊤)
    refine ⟨1, one_pos, fun z hz => ?_⟩
    have hyz : edist y z < 1 := Metric.mem_eball'.mp hz
    show edist x z < ⊤
    exact (edist_triangle x y z).trans_lt (ENNReal.add_lt_top.mpr ⟨hy, hyz.trans_le le_top⟩)
  have hclosed : IsClosed {y : X | edist x y < ⊤} := by
    rw [← isOpen_compl_iff, EMetric.isOpen_iff]
    rintro y (hy : ¬ edist x y < ⊤)
    rw [not_lt_top_iff] at hy
    refine ⟨1, one_pos, fun z hz => ?_⟩
    have hyz : edist y z < 1 := Metric.mem_eball'.mp hz
    show ¬ edist x z < ⊤
    rw [not_lt_top_iff]
    by_contra hxz
    have hfin : edist x z + edist y z < ⊤ :=
      ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hxz, hyz.trans_le le_top⟩
    have htri : edist x y ≤ edist x z + edist z y := edist_triangle x z y
    rw [edist_comm z y, hy] at htri
    exact absurd htri (not_le.mpr hfin)
  exact ⟨hclosed, hopen⟩

end IshikiExt
