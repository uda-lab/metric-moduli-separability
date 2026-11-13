-- Ext.Completeness
--
-- Completeness for the bare metrics of the Borel-preprint track
-- (arXiv:2608.19618), and the complete-compatible-metric locus `Comp` in both
-- ambients: `CPM.Comp Z` for a discrete carrier and `CPM.CompOn X` for the
-- preprint's continuous-pseudometric ambient of a topological space.
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` §1 (ambient
-- conventions, `Comp(X)` = the complete members of `Met(X)`), §2.11 (the
-- repair of Theorem 3.8, whose three completeness ingredients are proved
-- here) and §3 (the standard facts used silently by the preprint: one-point
-- amalgamation, and restriction of a complete metric to a closed subspace).
--
-- The whole track states metrics as bare functions satisfying `IsMetricOn`
-- (`Conj51/MetD.lean`), so completeness is stated for a bare function too:
-- `IsCompleteMetricOn d`.  `isCompleteMetricOn_iff_completeSpace` pins that
-- elementary definition to Mathlib's `CompleteSpace` for the `MetricSpace`
-- structure the function carries, so nothing weaker is being formalised.
--
-- What is proved here:
--   `isCompleteMetricOn_iff_completeSpace` — the definition is Mathlib's.
--   `isCompleteMetricOn_comap_iff`         — completeness is a relabelling
--                                            invariant.
--   `isCompleteMetricOn_addOneOffDiag`     — audit §2.11's normalisation
--                                            `d' := addOneOffDiag d` (`d + 1`
--                                            off the diagonal) is complete.
--                                            `d'`'s definition, compatibility
--                                            and `≤ 1` supremum-distance-
--                                            from-`d` bound are proved in
--                                            `Ext/Component.lean`, not here
--                                            (Theorem 3.4 v2 needs them too);
--                                            this file adds only the
--                                            completeness property, via the
--                                            uniform-separation criterion.
--   `isCompleteMetricOn_dExt`              — the coding metrics `d_t` are
--                                            complete for `t ∉ S` (audit
--                                            §2.11, the part of the printed
--                                            proof that is correct).
--   `isCompleteMetricOn_amalgam`           — the one-point amalgam of a
--                                            complete compatible base with a
--                                            complete `E`-side metric is
--                                            complete.
--   `isCompleteMetricOn_restrict`          — restriction of a complete metric
--                                            to a closed subspace is complete.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Component
import IshikiConj51.Ext.GeneralSeparability

open Cardinal Set

namespace IshikiExt

noncomputable section

variable {Z : Type*}

/-! ## Cauchy sequences and completeness for a bare metric

Metrics on this track are bare functions `d : Z → Z → ℝ` satisfying
`IsMetricOn`, so that "the topology `d` induces" can be spoken about
separately (`Conj51/MetD.lean`).  Completeness is stated in the same style.
`isCompleteMetricOn_iff_completeSpace` below identifies it with Mathlib's
`CompleteSpace` for the `MetricSpace` structure `d` carries, which is the
statement gate for everything that follows: `Comp(X)` means the complete
members of `Met(X)` in the ordinary sense, not a convenient proxy. -/

/-- A Cauchy sequence for a bare metric. -/
def IsCauchySeqOn (d : Z → Z → ℝ) (u : ℕ → Z) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, d (u m) (u n) < ε

/-- `x` is a limit of the sequence `u` for a bare metric. -/
def IsLimitOn (d : Z → Z → ℝ) (u : ℕ → Z) (x : Z) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d (u n) x < ε

/-- **Completeness of a bare metric**: every Cauchy sequence converges. -/
def IsCompleteMetricOn (d : Z → Z → ℝ) : Prop :=
  ∀ u : ℕ → Z, IsCauchySeqOn d u → ∃ x, IsLimitOn d u x

/-- The definition is Mathlib's.  A metric-axiom-satisfying function carries a
`MetricSpace` structure (`IsMetricOn.toMetricSpace`), and `IsCompleteMetricOn`
holds exactly when that structure is a `CompleteSpace`.  Metric spaces are
first countable, so the sequential form loses nothing. -/
theorem isCompleteMetricOn_iff_completeSpace {d : Z → Z → ℝ} (h : IsMetricOn d) :
    IsCompleteMetricOn d ↔ @CompleteSpace Z h.toMetricSpace.toUniformSpace := by
  letI : MetricSpace Z := h.toMetricSpace
  constructor
  · intro H
    refine Metric.complete_of_cauchySeq_tendsto ?_
    intro u hu
    obtain ⟨x, hx⟩ := H u fun ε hε => Metric.cauchySeq_iff.mp hu ε hε
    exact ⟨x, Metric.tendsto_atTop.mpr fun ε hε => hx ε hε⟩
  · intro H u hu
    have hu' : CauchySeq u := Metric.cauchySeq_iff.mpr fun ε hε => hu ε hε
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hu'
    exact ⟨x, fun ε hε => Metric.tendsto_atTop.mp hx ε hε⟩

/-- A sequence that is eventually constant converges, so a metric all of whose
Cauchy sequences are eventually constant is complete.  This is how the coding
metrics and the normalised base metric of audit §2.11 are handled: in both
cases a Cauchy sequence is eventually trapped at a single point. -/
theorem isCompleteMetricOn_of_eventually_const {d : Z → Z → ℝ} (hd : IsMetricOn d)
    (H : ∀ u : ℕ → Z, IsCauchySeqOn d u → ∃ N : ℕ, ∀ n ≥ N, u n = u N) :
    IsCompleteMetricOn d := by
  intro u hu
  obtain ⟨N, hN⟩ := H u hu
  refine ⟨u N, fun ε hε => ⟨N, fun n hn => ?_⟩⟩
  rw [hN n hn, hd.dist_self]
  exact hε

/-- A uniformly separated metric is complete: at radius `c` a Cauchy sequence
is eventually constant. -/
theorem isCompleteMetricOn_of_uniformly_separated {d : Z → Z → ℝ} (hd : IsMetricOn d)
    {c : ℝ} (hc : 0 < c) (hsep : ∀ x y : Z, x ≠ y → c ≤ d x y) :
    IsCompleteMetricOn d := by
  refine isCompleteMetricOn_of_eventually_const hd fun u hu => ?_
  obtain ⟨N, hN⟩ := hu c hc
  refine ⟨N, fun n hn => ?_⟩
  by_contra hne
  exact absurd (hN n hn N le_rfl) (not_lt.mpr (hsep _ _ hne))

/-! ## Completeness is a relabelling invariant -/

/-- Relabelling along a bijection preserves completeness, in both directions:
the relabelled metric has the same Cauchy sequences and the same limits, read
through `σ`. -/
theorem isCompleteMetricOn_comap_iff {D E : Type*} (σ : D ≃ E) (d : E → E → ℝ) :
    IsCompleteMetricOn (fun x y => d (σ x) (σ y)) ↔ IsCompleteMetricOn d := by
  constructor
  · intro H u hu
    have hcauchy : IsCauchySeqOn (fun x y => d (σ x) (σ y)) fun n => σ.symm (u n) := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      simpa using hN m hm n hn
    obtain ⟨y, hy⟩ := H _ hcauchy
    refine ⟨σ y, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hy ε hε
    refine ⟨N, fun n hn => ?_⟩
    simpa using hN n hn
  · intro H u hu
    have hcauchy : IsCauchySeqOn d fun n => σ (u n) := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      exact ⟨N, fun m hm n hn => hN m hm n hn⟩
    obtain ⟨x, hx⟩ := H _ hcauchy
    refine ⟨σ.symm x, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun n hn => ?_⟩
    simpa using hN n hn

/-! ## The radius criterion for an open set

`IsMetricOn.topology_eq_bot_iff` reads off isolating radii from discreteness;
the closed-subspace argument below needs the same reading for an arbitrary
open set. -/

/-- A point of an open set has a radius contained in it, for the topology the
metric induces. -/
theorem IsMetricOn.exists_radius_of_isOpen {Y : Type*} {m : Y → Y → ℝ} (hm : IsMetricOn m)
    {U : Set Y} (hU : @IsOpen Y hm.topology U) {x : Y} (hx : x ∈ U) :
    ∃ ε > 0, ∀ y : Y, m x y < ε → y ∈ U := by
  letI : MetricSpace Y := hm.toMetricSpace
  have hU' : IsOpen U := hU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU' x hx
  refine ⟨ε, hε, fun y hy => hball ?_⟩
  have hdist : dist y x = m x y := by
    rw [hm.dist_toMetricSpace, hm.dist_comm]
  rw [Metric.mem_ball, hdist]
  exact hy

/-! ## Restriction to a closed subspace

Audit §3 lists "restriction of a complete metric to a closed subspace is
complete" among the standard facts the preprint uses silently; Corollary 3.9
needs it for the reverse inclusion of `E(Comp(Z)) = E(Met(Z)) ∩ Comp(X)`. -/

/-- **Restriction to a closed subspace preserves completeness.**  If `m` is a
complete metric inducing the topology of `X` and `ι : A → X` is a closed
embedding along which `d` is the restriction of `m`, then `d` is complete: a
`d`-Cauchy sequence maps to an `m`-Cauchy sequence, whose limit cannot leave
the closed range of `ι`. -/
theorem isCompleteMetricOn_restrict {A X : Type*} {tA : TopologicalSpace A}
    [TopologicalSpace X] {ι : A → X}
    (hι : @Topology.IsClosedEmbedding A X tA inferInstance ι)
    {d : A → A → ℝ} {m : X → X → ℝ} (hm : IsMetricOn m)
    (htop : hm.topology = (inferInstance : TopologicalSpace X))
    (hmc : IsCompleteMetricOn m) (hrestrict : ∀ a b : A, m (ι a) (ι b) = d a b) :
    IsCompleteMetricOn d := by
  intro u hu
  have hcauchy : IsCauchySeqOn m fun n => ι (u n) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun k hk n hn => ?_⟩
    rw [hrestrict]
    exact hN k hk n hn
  obtain ⟨x, hx⟩ := hmc _ hcauchy
  have hxrange : x ∈ Set.range ι := by
    by_contra hxn
    have hopen : @IsOpen X hm.topology (Set.range ι)ᶜ := by
      rw [htop]
      exact hι.isClosed_range.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := IsMetricOn.exists_radius_of_isOpen hm hopen hxn
    obtain ⟨N, hN⟩ := hx ε hε
    refine hball (ι (u N)) ?_ ⟨u N, rfl⟩
    rw [hm.dist_comm]
    exact hN N le_rfl
  obtain ⟨a, rfl⟩ := hxrange
  refine ⟨a, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [← hrestrict]
  exact hN n hn

/-! ## The base normalisation `d' := d + 1` off the diagonal (audit §2.11)

The printed proof of Theorem 3.8 amalgamates the coding with an *arbitrary*
representative `d` of the component, and asserts that the result is complete.
Audit §2.11 records that this is false as written — `d` need not be complete —
and prescribes the repair: replace `d` by `d' := d + 1` off the diagonal,
which is a complete compatible metric at supremum distance `1` from `d`, hence
in the same component.  The elementary properties of `addOneOffDiag` live in
`Ext/Component.lean` (see below); completeness is proved here. -/

-- `addOneOffDiag` and its elementary lemmas (`addOneOffDiag_self`,
-- `addOneOffDiag_of_ne`, `one_le_addOneOffDiag`, `addOneOffDiag_nonneg`,
-- `isMetricOn_addOneOffDiag`, `topology_addOneOffDiag_eq_bot`,
-- `abs_addOneOffDiag_sub_le`) now live in `Ext/Component.lean`, which this
-- file imports: Theorem 3.4 (v2) needs `one_le_addOneOffDiag` for its
-- `ℵ₁`-selection step, and `Ext/Component.lean` does not import this file, so
-- the block had to move up rather than be duplicated.

/-- The normalised metric is complete: it is uniformly discrete. -/
theorem isCompleteMetricOn_addOneOffDiag {d : Z → Z → ℝ} (hd : IsMetricOn d) :
    IsCompleteMetricOn (addOneOffDiag d) :=
  isCompleteMetricOn_of_uniformly_separated (isMetricOn_addOneOffDiag hd) one_pos
    fun _ _ h => one_le_addOneOffDiag hd h

/-! ## Completeness of the coding metrics (audit §2.11)

The part of the printed proof of Theorem 3.8 that is correct: for `t ∉ S` the
star metric `d_t` is complete.  Cross-block distances are `4`, so a Cauchy
sequence is eventually confined to a single block; inside the star at `a` every
off-diagonal distance is at least `|t − a| > 0`, so it is eventually
constant. -/

/-- Points in different blocks are at distance exactly `4`, so a distance
below `4` forces the same block. -/
theorem extBlock_eq_of_dExt_lt_four {S : Set ℝ} {t : ℝ} {u v : ExtIndex S}
    (h : dExt S t u v < 4) : extBlock S u = extBlock S v := by
  by_contra hne
  rw [dExt_of_block_ne hne] at h
  exact absurd h (lt_irrefl 4)

/-- Two distinct points of the star at `a` are at distance at least `|t − a|`:
at least one of them is a spoke, and a spoke is at radius `l_n(a,t) ≥ |t − a|`
from the centre. -/
theorem abs_sub_le_extRadius_add (a t : ℝ) {i j : Option ℕ} (h : i ≠ j) :
    |t - a| ≤ extRadius a t i + extRadius a t j := by
  match i, j with
  | none, none => exact absurd rfl h
  | none, some n =>
      simpa [extRadius] using abs_sub_le_spokeLen n a t
  | some n, none =>
      simpa [extRadius] using abs_sub_le_spokeLen n a t
  | some n, some k =>
      show |t - a| ≤ spokeLen n a t + spokeLen k a t
      linarith [abs_sub_le_spokeLen n a t, (spokeLen_pos k a t).le]

/-- **The coding metrics are complete for `t ∉ S`** (audit §2.11).  This is
the half of the printed proof of Theorem 3.8 that survives the audit; the
failure is on the base-metric side, repaired by `addOneOffDiag`. -/
theorem isCompleteMetricOn_dExt {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htS : t ∉ S) : IsCompleteMetricOn (dExt S t) := by
  refine isCompleteMetricOn_of_eventually_const (dExt_isMetricOn hS ht) ?_
  intro u hu
  obtain ⟨N, hN⟩ := hu 1 one_pos
  have hblock : ∀ n ≥ N, extBlock S (u n) = extBlock S (u N) := fun n hn =>
    extBlock_eq_of_dExt_lt_four (lt_trans (hN n hn N le_rfl) (by norm_num))
  rcases hUN : u N with b | ⟨a, i⟩
  · -- the anchor block: the two anchors are at distance `1 + t ≥ 1`
    refine ⟨N, fun n hn => ?_⟩
    have hnone : extBlock S (u n) = none := by
      rw [hblock n hn, hUN]
      rfl
    obtain ⟨c, hc⟩ := eq_inl_of_extBlock_eq_none hnone
    by_cases hcb : c = b
    · rw [hc, hUN, hcb]
    · exfalso
      have hlt := hN n hn N le_rfl
      rw [hc, hUN, dExt, ite_eq_right hcb] at hlt
      linarith [ht.1]
  · -- a star block: off-diagonal distances are at least `|t − a| > 0`
    have hta : t ≠ (a : ℝ) := fun h => htS (h ▸ a.2)
    have hδ : 0 < |t - (a : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hta)
    obtain ⟨N₂, hN₂⟩ := hu _ hδ
    have hstar : ∀ n ≥ N, ∃ j, u n = Sum.inr (a, j) := by
      intro n hn
      have hsome : extBlock S (u n) = some a := by
        rw [hblock n hn, hUN]
        rfl
      exact eq_inr_of_extBlock_eq_some hsome
    refine ⟨max N N₂, fun n hn => ?_⟩
    obtain ⟨j, hj⟩ := hstar n (le_trans (le_max_left N N₂) hn)
    obtain ⟨k, hk⟩ := hstar (max N N₂) (le_max_left N N₂)
    by_cases hjk : j = k
    · rw [hj, hk, hjk]
    · exfalso
      have hlt := hN₂ n (le_trans (le_max_right N N₂) hn) (max N N₂) (le_max_right N N₂)
      rw [hj, hk, dExt, ite_eq_left rfl, ite_eq_right hjk] at hlt
      linarith [abs_sub_le_extRadius_add (a : ℝ) t hjk]

/-! ## Completeness of the one-point amalgam (audit §2.11)

With the normalised base of `addOneOffDiag` this is the second ingredient of
the repair.  The hypotheses are exactly what the argument uses: the base is
complete and compatible, the `E`-side metric is complete, and the two sides are
uniformly separated at the glue point.  The separation is what excludes the
mixed case — a Cauchy sequence cannot straddle the two sides — and compatibility
of the base is what keeps the outside limit outside `E`. -/

/-- **The one-point amalgam of complete metrics is complete.**  Given the
uniform gap `c` at the glue point, a Cauchy sequence for the amalgam is
eventually confined to one side: inside `E` it is Cauchy for `e` and converges
there, outside `E` it is Cauchy for the base, and its base limit is isolated,
so the sequence is eventually constant and its limit stays outside `E`. -/
theorem isCompleteMetricOn_amalgam {E : Set Z} {z : Z} {d : Z → Z → ℝ} {e : ↥E → ↥E → ℝ}
    (hz : z ∈ E) (hd : IsMetricOn d) (he : IsMetricOn e) (hdbot : hd.topology = ⊥)
    (hdc : IsCompleteMetricOn d) (hec : IsCompleteMetricOn e)
    {c : ℝ} (hc : 0 < c) (hdsep : ∀ y : Z, y ∉ E → c ≤ d z y) :
    IsCompleteMetricOn (amalgam E z hz d e) := by
  classical
  intro u hu
  obtain ⟨N₀, hN₀⟩ := hu c hc
  -- Past `N₀` the sequence cannot straddle the two sides: a mixed pair is at
  -- distance at least `c`.
  have hmix : ∀ m ≥ N₀, ∀ n ≥ N₀, u m ∈ E → u n ∉ E → False := by
    intro m hm n hn hmE hnE
    have hlt := hN₀ m hm n hn
    rw [amalgam_mem_notMem hz hmE hnE] at hlt
    linarith [IsMetricOn.nonneg he ⟨u m, hmE⟩ ⟨z, hz⟩, hdsep (u n) hnE]
  by_cases hE₀ : u N₀ ∈ E
  · -- The tail stays inside `E`, where the amalgam is `e`.
    have htail : ∀ n ≥ N₀, u n ∈ E := by
      intro n hn
      by_contra hnE
      exact hmix N₀ le_rfl n hn hE₀ hnE
    set w : ℕ → ↥E := fun n => if h : u n ∈ E then ⟨u n, h⟩ else ⟨z, hz⟩ with hw
    have hwval : ∀ (n : ℕ) (h : u n ∈ E), w n = ⟨u n, h⟩ := by
      intro n h
      simp only [hw, dite_eq_left h]
    have hwCauchy : IsCauchySeqOn e w := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨max N N₀, fun m hm n hn => ?_⟩
      have hmE := htail m (le_trans (le_max_right N N₀) hm)
      have hnE := htail n (le_trans (le_max_right N N₀) hn)
      have heq : e (w m) (w n) = amalgam E z hz d e (u m) (u n) := by
        rw [hwval m hmE, hwval n hnE, amalgam_mem_mem hz hmE hnE]
      rw [heq]
      exact hN m (le_trans (le_max_left N N₀) hm) n (le_trans (le_max_left N N₀) hn)
    obtain ⟨a, ha⟩ := hec w hwCauchy
    refine ⟨(a : Z), fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := ha ε hε
    refine ⟨max M N₀, fun n hn => ?_⟩
    have hnE := htail n (le_trans (le_max_right M N₀) hn)
    rw [amalgam_mem_mem hz hnE a.2, ← hwval n hnE]
    exact hM n (le_trans (le_max_left M N₀) hn)
  · -- The tail stays outside `E`, where the amalgam is the base metric.
    have htail : ∀ n ≥ N₀, u n ∉ E := by
      intro n hn hnE
      exact hmix n hn N₀ le_rfl hnE hE₀
    set v : ℕ → Z := fun n => if u n ∈ E then z else u n with hv
    have hvval : ∀ n ≥ N₀, v n = u n := by
      intro n hn
      simp only [hv, ite_eq_right (htail n hn)]
    have hvCauchy : IsCauchySeqOn d v := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨max N N₀, fun m hm n hn => ?_⟩
      have hm₀ := le_trans (le_max_right N N₀) hm
      have hn₀ := le_trans (le_max_right N N₀) hn
      have heq : d (v m) (v n) = amalgam E z hz d e (u m) (u n) := by
        rw [hvval m hm₀, hvval n hn₀, amalgam_notMem_notMem hz (htail m hm₀) (htail n hn₀)]
      rw [heq]
      exact hN m (le_trans (le_max_left N N₀) hm) n (le_trans (le_max_left N N₀) hn)
    obtain ⟨x, hx⟩ := hdc v hvCauchy
    obtain ⟨ε₀, hε₀, hiso⟩ := hd.topology_eq_bot_iff.mp hdbot x
    obtain ⟨N₁, hN₁⟩ := hx ε₀ hε₀
    have hux : ∀ n ≥ max N₁ N₀, u n = x := by
      intro n hn
      rw [← hvval n (le_trans (le_max_right N₁ N₀) hn)]
      exact hiso (v n) (hN₁ n (le_trans (le_max_left N₁ N₀) hn))
    have hxE : x ∉ E := by
      rw [← hux (max N₁ N₀) le_rfl]
      exact htail _ (le_max_right N₁ N₀)
    refine ⟨x, fun ε hε => ⟨max N₁ N₀, fun n hn => ?_⟩⟩
    rw [amalgam_notMem_notMem hz (htail n (le_trans (le_max_right N₁ N₀) hn)) hxE,
      hux n hn, hd.dist_self]
    exact hε

/-! ## The complete-compatible-metric locus

Audit §1: `Comp(X)` is the set of complete members of `Met(X)`.  Two ambients,
matching the two metric loci already in the development: `CPM.Comp Z` sits in
the bare pseudometric ambient `CPM Z` of a discrete carrier, and
`CPM.CompOn X` sits in the preprint's continuous-pseudometric ambient
`CPMOn X` of a topological space. -/

/-- `Comp(Z)` for a discrete carrier: the complete members of `Met(Z)`. -/
def CPM.Comp (Z : Type*) : Set (CPM Z) :=
  {d | d ∈ CPM.Met Z ∧ IsCompleteMetricOn d.1}

@[simp] theorem CPM.mem_Comp {d : CPM Z} :
    d ∈ CPM.Comp Z ↔ d ∈ CPM.Met Z ∧ IsCompleteMetricOn d.1 := Iff.rfl

theorem CPM.Comp_subset_Met (Z : Type*) : CPM.Comp Z ⊆ CPM.Met Z := fun _ h => h.1

/-- `Comp(X)` in the preprint's ambient: the complete members of `Met(X)`. -/
def CPM.CompOn (X : Type*) [TopologicalSpace X] : Set (CPMOn X) :=
  {d | d ∈ CPM.MetOn X ∧ IsCompleteMetricOn d.1.1}

@[simp] theorem mem_CPM_CompOn {X : Type*} [TopologicalSpace X] {d : CPMOn X} :
    d ∈ CPM.CompOn X ↔ d ∈ CPM.MetOn X ∧ IsCompleteMetricOn d.1.1 := Iff.rfl

theorem CPM.CompOn_subset_MetOn (X : Type*) [TopologicalSpace X] :
    CPM.CompOn X ⊆ CPM.MetOn X := fun _ h => h.1

/-- The `0/1` metric is complete, so neither `Comp(Z)` nor its intersection
with a component is empty for trivial reasons. -/
theorem isCompleteMetricOn_discreteFn (Z : Type*) : IsCompleteMetricOn (discreteFn Z) :=
  isCompleteMetricOn_of_uniformly_separated (isMetricOn_discreteFn Z) one_pos
    fun _ _ h => le_of_eq (discreteFn_of_ne h).symm

theorem CPM.discrete_mem_Comp (Z : Type*) : CPM.discrete Z ∈ CPM.Comp Z :=
  ⟨CPM.discrete_mem_Met Z, isCompleteMetricOn_discreteFn Z⟩

theorem CPM.nonempty_Comp (Z : Type*) : (CPM.Comp Z).Nonempty :=
  ⟨CPM.discrete Z, CPM.discrete_mem_Comp Z⟩

/-! ### The two ambients agree on a discrete carrier

The `Comp` analogues of `CPMOn.preimage_equivCPM_met` and
`CPMOn.preimage_MetOn_comap`, which is what carries the locus across the two
moves of the E1 bridge (`IsIsometricExtensorOn.toIsIsometricExtensor`). -/

theorem CPMOn.preimage_equivCPM_comp (D : Type*) [TopologicalSpace D] [DiscreteTopology D] :
    CPMOn.equivCPM D ⁻¹' CPM.Comp D = CPM.CompOn D := by
  have hmet : ∀ d : CPMOn D, CPMOn.equivCPM D d ∈ CPM.Met D ↔ d ∈ CPM.MetOn D :=
    fun d => Set.ext_iff.mp (CPMOn.preimage_equivCPM_met D) d
  ext d
  rw [Set.mem_preimage, CPM.mem_Comp, mem_CPM_CompOn]
  exact and_congr (hmet d) Iff.rfl

theorem CPMOn.preimage_CompOn_comap {D E : Type*} [TopologicalSpace D] [TopologicalSpace E]
    (σ : D ≃ₜ E) : CPMOn.comap σ ⁻¹' CPM.CompOn D = CPM.CompOn E := by
  have hmet : ∀ d : CPMOn E, CPMOn.comap σ d ∈ CPM.MetOn D ↔ d ∈ CPM.MetOn E :=
    fun d => Set.ext_iff.mp (CPMOn.preimage_MetOn_comap σ) d
  ext d
  rw [Set.mem_preimage, mem_CPM_CompOn, mem_CPM_CompOn]
  exact and_congr (hmet d) (isCompleteMetricOn_comap_iff σ.toEquiv d.1.1)

end
end IshikiExt
