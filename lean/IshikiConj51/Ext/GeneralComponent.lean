-- Ext.GeneralComponent
--
-- Issue #107: the component-by-component non-Borelness statement for an
-- arbitrary nonseparable metrizable space, and the non-Borelness of `Met(X)`
-- that follows from it.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` (§1 ambient
-- and component conventions, §2.7 for the discrete input, §3 for the external
-- dependencies).  The statement being formalised is the 2026-08-27 received
-- manuscript's `cor:nonseparable-metric-nonborel`; the discrete input is
-- `Ext/Component.lean`'s `component_not_measurableSet` in its `ℵ₁ ≤ #Z` form.
--
-- Nothing here strengthens the E1 bundle `IsIsometricExtensorOn` of
-- `Ext/GeneralSeparability.lean`: the construction-controlled extensor is a
-- separate structure that *contains* an ordinary E1 bundle, and no existing
-- theorem acquires it as a hypothesis.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Component
import IshikiConj51.Ext.GeneralSeparability

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

-- `componentCpmMeasurableSpace`/`componentCpmBorelSpace` are the `local`
-- instances under which `Ext.Component`'s statements were elaborated, and
-- `cpmOnMeasurableSpace`/`cpmOnBorelSpace` are the ones
-- `Ext.GeneralSeparability` uses for the preprint's ambient.  A `local`
-- attribute does not survive an import, so both pairs are re-registered here;
-- they are the same constants, so the σ-algebras are the ones in the imported
-- statements.
attribute [local instance] componentCpmMeasurableSpace componentCpmBorelSpace
  cpmOnMeasurableSpace cpmOnBorelSpace

/-! ## Restricting a continuous pseudometric to a subspace -/

/-- The restriction of a continuous pseudometric on `X` to a subspace `A`.

The manuscript's component argument feeds the extensor with `d|_{A²}` for a
compatible `d` on `X`, and states the point estimate for the extension of that
particular restriction; this is the map `d ↦ d|_{A²}`. -/
def CPMOn.restrict {X : Type*} [TopologicalSpace X] (A : Set X) (d : CPMOn X) :
    CPMOn ↥A :=
  ⟨⟨fun a b => d.1.1 ↑a ↑b,
    { dist_self := fun a => d.1.2.dist_self ↑a
      dist_comm := fun a b => d.1.2.dist_comm ↑a ↑b
      dist_triangle := fun a b c => d.1.2.dist_triangle ↑a ↑b ↑c }⟩, by
    have huncurry : Function.uncurry (fun a b : ↥A => d.1.1 ↑a ↑b)
        = Function.uncurry d.1.1 ∘
          Prod.map (Subtype.val : ↥A → X) (Subtype.val : ↥A → X) := rfl
    rw [huncurry]
    exact d.2.comp (continuous_subtype_val.prodMap continuous_subtype_val)⟩

@[simp] theorem CPMOn.restrict_apply {X : Type*} [TopologicalSpace X] (A : Set X)
    (d : CPMOn X) (a b : ↥A) : (CPMOn.restrict A d).1.1 a b = d.1.1 ↑a ↑b := rfl

/-! ## The construction-controlled extensor bundle -/

/-- **The construction-controlled isometric extensor.**

An ordinary E1 extensor for the closed set `A`, together with the point
estimate that Ishiki's *construction* satisfies when the ambient metric `d` and
its restriction `d|_{A²}` are chosen as the base metrics.

Provenance, field by field.  `toExtensor` is E1 as audited
(`notes/borel-preprint-audit.md` §3), unchanged and unstrengthened.
`point_estimate` is **E1c** (same note, §3): Ishiki, *An isometric extensor of
metrics*, arXiv:2407.03030 **v4**, **Lemma 4.4**, printed p. 24, which gives
`L(J(x), J(y)) ≤ 4 w(x,y) + 1` for every `x` in the ambient space and every
`y` in the closed subset, `w` being the ambient base metric.  The owner's
primary-source verification of that printed bound is recorded on
uda-lab/metric-moduli-separability#111.

**E1c is construction-specific data taken from the proof of Theorem 1.1, not a
consequence of the theorem-level statement.**  E1 and E2 are theorem-level
bundles quantifying over extensors abstractly; Lemma 4.4 is an estimate
satisfied by the particular map built inside Theorem 1.1's proof, and it must
not be conflated with either — that is what the `c` suffix of the label
records.  It is also why the estimate is carried by a *new* structure
containing an `IsIsometricExtensorOn` rather than by a new field on it: adding
a field would silently strengthen every existing consumer of E1, and
`Ext/GeneralSeparability.lean`'s Route M transfer must keep the E1 it was
audited against.

The estimate is stated only for the extension of `CPMOn.restrict A d`, which
is the only member of `CPM(A)` the manuscript's argument applies it to. -/
structure IsComponentControlledExtensorOn {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] (A : Set X) (d : CPMOn X) where
  toExtensor : IsIsometricExtensorOn A
  point_estimate : ∀ (x : X) (a : ↥A),
    (toExtensor.toCPM (CPMOn.restrict A d)).1.1 x ↑a ≤ 4 * d.1.1 x ↑a + 1

end
end IshikiExt
