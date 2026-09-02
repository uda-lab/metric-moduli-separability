-- Ext.GeneralSpace
--
-- Metric-space support for Issue #57 and Issue #107.  This file deliberately
-- does not import or define the CPM/extensor layer: every result below is
-- independent of it.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.8 and §7.
-- Status: sorry-free; no custom axioms.

import Mathlib.Order.TeichmullerTukey
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

open Cardinal Set

namespace IshikiExt

noncomputable section

/--
  **Maximal `ε`-separated sets.**  For every `ε > 0` a metric space has a
  subset that is `ε`-separated and, by maximality, an `ε`-net.

  The maximal sets are obtained from the finite-character version of Zorn's
  lemma; Mathlib's packing-number maximal-set API is only available under a
  finiteness hypothesis and is therefore not applicable here.

  Both existence results below are derived from this one lemma, so the net
  clause and the separation clause always come from the same set.
-/
private theorem exists_maximal_separated {X : Type*} [MetricSpace X]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Set X, s.Pairwise (fun x y => ε < dist x y) ∧
      ∀ x : X, ∃ y ∈ s, dist x y ≤ ε := by
  let F : Set (Set X) := {s | s.Pairwise (fun x y => ε < dist x y)}
  have hF : Order.IsOfFiniteCharacter F := by
    intro s
    constructor
    · intro hs t hts htfinite
      exact hs.mono hts
    · intro hfinite x hx y hy hxy
      have hxy_mem : ({x, y} : Set X) ⊆ s := by
        intro z hz
        simp only [mem_insert_iff, mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      have hxy_pair : ({x, y} : Set X).Pairwise
          (fun x y => ε < dist x y) :=
        hfinite {x, y} hxy_mem (Set.toFinite _)
      exact hxy_pair (by simp) (by simp) hxy
  obtain ⟨s, _, hsmax⟩ :=
    Order.IsOfFiniteCharacter.exists_maximal (x := (∅ : Set X)) hF (by simp [F])
  have hs : s.Pairwise (fun x y => ε < dist x y) := by
    simpa [F] using hsmax.1
  refine ⟨s, hs, ?_⟩
  intro x
  by_cases hx : x ∈ s
  · exact ⟨x, hx, by simpa using (le_of_lt hε)⟩
  · by_contra hcover
    push Not at hcover
    have hsinsert : (insert x s).Pairwise (fun x y => ε < dist x y) := by
      haveI : Std.Symm (fun x y : X => ε < dist x y) := by
        simp [symm_def, dist_comm]
      refine (pairwise_insert_of_symm_of_notMem hx).2 ⟨hs, ?_⟩
      intro y hy
      exact hcover y hy
    have hsinsertF : insert x s ∈ F := by
      simpa [F] using hsinsert
    exact hx (hsmax.mem_of_prop_insert hsinsertF)

/--
  A nonseparable metric space has, for some `ε > 0`, an `ε`-separated closed
  discrete `ε`-net of cardinality at least `ℵ₁`.

  This is the form the general-space *component* argument of Issue #107 needs.
  `exists_aleph1_closed_discrete_separated` below shrinks the net to a subset
  of cardinality exactly `ℵ₁` and therefore cannot keep the net clause: an
  `ℵ₁`-sized subset of a maximal `ε`-separated set is in general no longer an
  `ε`-net.  The two statements are accordingly siblings — this one is the
  unshrunk maximal set, and the other is derived from it — rather than one
  being obtainable from the other after the fact.

  The cardinality clause is `ℵ₁ ≤ #↥D`, not an equality, and no selection is
  performed to obtain it.  Nonseparability supplies an `ε` admitting no
  countable `ε`-net, so *every* `ε`-net for that `ε` is uncountable, and an
  uncountable set has cardinality at least `ℵ₁`.  That `≥` form is what
  `Ext/Component.lean`'s `component_not_measurableSet` takes, which is why
  the shrink is unnecessary here.

  The separation is a positive real lower bound on distances, so the set is
  closed and its subtype carries the discrete topology, exactly as in the
  sibling.
-/
theorem exists_aleph1_closed_discrete_separated_net
    {X : Type*} [MetricSpace X] (hX : ¬TopologicalSpace.SeparableSpace X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : Set X,
      Cardinal.aleph 1 ≤ #(↥D) ∧
        IsClosed D ∧
          DiscreteTopology D ∧
            D.Pairwise (fun x y => ε ≤ dist x y) ∧
              ∀ x : X, ∃ a ∈ D, dist x a ≤ ε := by
  choose A hA hAcover using fun n : ℕ =>
    exists_maximal_separated (X := X) (1 / ((n : ℝ) + 1)) (by positivity)
  have hunc : ∃ n : ℕ, ¬(A n).Countable := by
    by_contra h
    push Not at h
    have hcount : (⋃ n, A n).Countable := countable_iUnion h
    have hdense : Dense (⋃ n, A n) := by
      rw [Metric.dense_iff]
      intro x r hr
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
      have hnr : 1 / ((n : ℝ) + 1) < r := by
        apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
        have hmul : 1 < (n : ℝ) * r := (div_lt_iff₀ hr).mp hn
        nlinarith
      obtain ⟨y, hyA, hy⟩ := hAcover n x
      refine ⟨y, ?_, ?_⟩
      · simpa [Metric.mem_ball, dist_comm] using hy.trans_lt hnr
      · exact mem_iUnion_of_mem n hyA
    exact hX ⟨⟨_, hcount, hdense⟩⟩
  obtain ⟨n, hn⟩ := hunc
  have hAle : Cardinal.aleph 1 ≤ #(↥(A n)) := by
    apply le_of_not_gt
    intro hlt
    exact hn (Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hlt))
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hApair : (A n).Pairwise (fun x y => 1 / ((n : ℝ) + 1) ≤ dist x y) := by
    intro x hx y hy hxy
    exact le_of_lt (hA n hx hy hxy)
  have hAclosed : IsClosed (A n) := Metric.isClosed_of_pairwise_le_dist hε hApair
  letI : DiscreteTopology (A n) :=
    DiscreteTopology.of_forall_le_dist hε (by
      intro x y hxy
      exact hApair x.2 y.2 (by
        intro hxy'
        exact hxy (Subtype.ext hxy')))
  exact ⟨1 / ((n : ℝ) + 1), hε, A n, hAle, hAclosed, inferInstance, hApair, hAcover n⟩

/- `#print axioms exists_aleph1_closed_discrete_separated_net`:
   `[propext, Classical.choice, Quot.sound]`. -/

/--
  A nonseparable metric space contains an `ℵ₁`-sized uniformly separated set.

  The separation is stated as a positive real lower bound on distances.  Thus
  the set is closed, and its subtype carries the discrete topology.

  The separated set is the maximal one of
  `exists_aleph1_closed_discrete_separated_net`, cut down to cardinality
  exactly `ℵ₁`.  The cut loses the net clause and is not reversible, so
  consumers that need the net take the sibling directly.
-/
theorem exists_aleph1_closed_discrete_separated
    {X : Type*} [MetricSpace X] (hX : ¬TopologicalSpace.SeparableSpace X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Z : Set X,
      #(↥Z) = Cardinal.aleph 1 ∧
        IsClosed Z ∧
          DiscreteTopology Z ∧
            Z.Pairwise (fun x y => ε ≤ dist x y) := by
  obtain ⟨ε, hε, D, hDcard, -, -, hDpair, -⟩ :=
    exists_aleph1_closed_discrete_separated_net hX
  obtain ⟨Z, hZD, hZcard⟩ := Cardinal.le_mk_iff_exists_subset.mp hDcard
  have hZpair : Z.Pairwise (fun x y => ε ≤ dist x y) := hDpair.mono hZD
  have hZclosed : IsClosed Z := Metric.isClosed_of_pairwise_le_dist hε hZpair
  letI : DiscreteTopology Z :=
    DiscreteTopology.of_forall_le_dist hε (by
      intro x y hxy
      exact hZpair x.2 y.2 (by
        intro hxy'
        exact hxy (Subtype.ext hxy')))
  exact ⟨ε, hε, Z, hZcard, hZclosed, inferInstance, hZpair⟩

/- `#print axioms exists_aleph1_closed_discrete_separated`:
   `[propext, Classical.choice, Quot.sound]`. -/

/-- The range of an isometric map from a complete extended-metric space is
closed.

The extended-metric level is what the general-space transfer needs: the
supremum distance on `CPM` takes the value `∞`, so its isometries are not
`MetricSpace` isometries.  A `MetricSpace` instance supplies an
`EMetricSpace` instance, so ordinary metric spaces are still covered. -/
theorem isClosed_range_of_isometry_complete
    {Z Y : Type*} [EMetricSpace Z] [CompleteSpace Z] [EMetricSpace Y]
    (f : Z → Y) (hf : Isometry f) : IsClosed (Set.range f) :=
  hf.isClosedEmbedding.isClosed_range

/- `#print axioms isClosed_range_of_isometry_complete`:
   `[propext, Classical.choice, Quot.sound]`. -/

end
end IshikiExt
