-- Ext.UltraPMet
--
-- Issue #81, scope item 1: the non-Archimedean ambient of arXiv:2608.19618.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §1 (ambient
-- conventions) and §§2.13–2.14 (the statements this ambient carries).
-- `report/report-ja.md` is *not* the source of truth here: it stays frozen as
-- the Conjecture 5.1 archival report by the Issue #46 decision.
--
-- The preprint fixes a *range set* `R ⊆ [0,∞)` with `0 ∈ R`, calls it
-- **characteristic** when `0` is an accumulation point of `R ∖ {0}`, and
-- works in
--
--   `UCPM(X;R)` — the continuous `R`-valued pseudo-ultrametrics on `X`,
--   `UMet(Y;R)` — the members compatible with the topology of `Y`,
--
-- with the non-Archimedean uniform distance
--
--   `𝒰𝒟^R(d,e) = inf {ε ∈ R ∪ {∞} : d ≤ e ∨ ε and e ≤ d ∨ ε pointwise}`,
--
-- again extended-valued.  All four objects are new here: Mathlib has no
-- `R`-valued (pseudo-)ultrametric predicate, and no space-of-metrics
-- construction, so `IsUltraPMetOn`, `UCPM`, `UCPM.edist` and `UMet` are
-- defined from scratch.  The Archimedean ambient of `Ext/BddPMet.lean` /
-- `Ext/CPM.lean` is deliberately *not* reused for the carrier: `𝒰𝒟^R` is not
-- the supremum of `|d − e|` and is not even determined by it, so forcing the
-- ultrametric development through `CPM` would change the ambient.  What *is*
-- reused is the compatibility condition: membership in `UMet` is the same
-- `IsMetricOn` + `.topology = ⊥` predicate that `Conj51/MetD.lean` fixes for
-- the whole repository, and the relabelling transport of that predicate from
-- `Ext/Relabel.lean`.
--
-- Carrier discreteness is not an instance hypothesis anywhere below, exactly
-- as in `Ext/Relabel.lean`: "compatible" means "induces the discrete
-- topology", which is a condition on the function, not on an ambient topology.
--
-- Layering (this file is the base of the non-Archimedean track):
--   `RangeSet`, `IsCharacteristic`, `IsScale`  — the hypotheses on `R`;
--   `IsUltraPMetOn`, `UCPM`, `UCPM.edist`      — the ambient;
--   `UCPM.comap`, `UCPM.sup`                   — the two reusable operations,
--                                                 out of which the coding
--                                                 (`Ext/UltraCoding.lean`) and
--                                                 the one-point max-amalgam
--                                                 (`Ext/UltraComponent.lean`)
--                                                 are built.
--
-- Status: sorry-free; no custom axioms.

import Mathlib.Topology.MetricSpace.Ultra.Basic
import IshikiConj51.Ext.Relabel

open Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

variable {Z W : Type*}

/-! ## Range sets and the characteristic hypothesis -/

/-- A *range set* in the sense of the preprint: a set of nonnegative reals
containing `0`.  It is bundled because the ambient type `UCPM Z R` depends on
it, and both standing conditions are needed to see that ambient as a metric
space (`0 ∈ R` for `𝒰𝒟^R(d,d) = 0`, nonnegativity for the separation
argument). -/
structure RangeSet where
  /-- The underlying set of admissible distance values. -/
  carrier : Set ℝ
  zero_mem : (0 : ℝ) ∈ carrier
  nonneg : ∀ ⦃r : ℝ⦄, r ∈ carrier → 0 ≤ r

namespace RangeSet

/-- `R` is closed under binary maxima, because a maximum of two reals *is* one
of them.  This is what makes `𝒰𝒟^R` satisfy the strong triangle inequality and
what makes the max-amalgam of `Ext/UltraComponent.lean` `R`-valued. -/
theorem max_mem (R : RangeSet) {r s : ℝ} (hr : r ∈ R.carrier) (hs : s ∈ R.carrier) :
    max r s ∈ R.carrier := by
  rcases max_choice r s with h | h <;> rw [h] <;> assumption

/-- `R` is *characteristic*: `0` is an accumulation point of `R ∖ {0}`.  This
is the exact hypothesis of the preprint; it is not strengthened anywhere in
this track. -/
def IsCharacteristic (R : RangeSet) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r ∈ R.carrier, 0 < r ∧ r < ε

/-- A *scale* for `R`: a strictly decreasing sequence in `R ∖ {0}` tending to
`0`.  The preprint's `r : ℕ → R ∖ {0}`. -/
structure IsScale (R : RangeSet) (r : ℕ → ℝ) : Prop where
  mem : ∀ n, r n ∈ R.carrier
  pos : ∀ n, 0 < r n
  strictAnti : StrictAnti r
  tendsto_zero : Filter.Tendsto r Filter.atTop (nhds 0)

namespace IsScale

variable {R : RangeSet} {r : ℕ → ℝ}

theorem antitone (h : IsScale R r) : Antitone r := h.strictAnti.antitone

/-- Comparison of scale terms is the reverse comparison of indices.  Stated
here because `StrictAnti` is a definition rather than a structure, so the field
`IsScale.strictAnti` does not itself support dot notation. -/
theorem lt_iff_lt (h : IsScale R r) {m n : ℕ} : r m < r n ↔ n < m := by
  refine ⟨fun hlt => ?_, fun hnm => h.strictAnti hnm⟩
  by_contra hle
  push Not at hle
  exact absurd hlt (not_lt.mpr (h.antitone hle))

theorem le_head (h : IsScale R r) (n : ℕ) : r n ≤ r 0 := h.antitone (Nat.zero_le n)

theorem nonneg (h : IsScale R r) (n : ℕ) : 0 ≤ r n := (h.pos n).le

/-- Every positive bound is undercut by some member of the scale. -/
theorem exists_lt (h : IsScale R r) {ε : ℝ} (hε : 0 < ε) : ∃ n, r n < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h.tendsto_zero ε hε
  have := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact ⟨N, lt_of_abs_lt this⟩

end IsScale

/-! ### Existence of a scale

The preprint records that a scale exists *exactly* when `R` is characteristic.
Both directions are proved, so that the hypothesis carried by the theorems of
this track is neither stronger nor weaker than the preprint's. -/

/-- A choice of positive member of `R` below a positive bound. -/
def smallElt (R : RangeSet) (hR : R.IsCharacteristic) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then Classical.choose (hR ε hε) else 0

theorem smallElt_mem (R : RangeSet) (hR : R.IsCharacteristic) {ε : ℝ} (hε : 0 < ε) :
    smallElt R hR ε ∈ R.carrier := by
  rw [smallElt, dif_pos hε]
  exact (Classical.choose_spec (hR ε hε)).1

theorem smallElt_pos (R : RangeSet) (hR : R.IsCharacteristic) {ε : ℝ} (hε : 0 < ε) :
    0 < smallElt R hR ε := by
  rw [smallElt, dif_pos hε]
  exact (Classical.choose_spec (hR ε hε)).2.1

theorem smallElt_lt (R : RangeSet) (hR : R.IsCharacteristic) {ε : ℝ} (hε : 0 < ε) :
    smallElt R hR ε < ε := by
  rw [smallElt, dif_pos hε]
  exact (Classical.choose_spec (hR ε hε)).2.2

/-- The scale built from a characteristic `R`: each term is a member of
`R ∖ {0}` below both its predecessor and `1/(n+1)`. -/
def scale (R : RangeSet) (hR : R.IsCharacteristic) : ℕ → ℝ
  | 0 => smallElt R hR 1
  | n + 1 => smallElt R hR (min (scale R hR n) (1 / ((n : ℝ) + 2)))

theorem scale_pos (R : RangeSet) (hR : R.IsCharacteristic) : ∀ n, 0 < scale R hR n
  | 0 => smallElt_pos R hR one_pos
  | n + 1 => smallElt_pos R hR (lt_min (scale_pos R hR n) (by positivity))

theorem scale_mem (R : RangeSet) (hR : R.IsCharacteristic) : ∀ n, scale R hR n ∈ R.carrier
  | 0 => smallElt_mem R hR one_pos
  | n + 1 => smallElt_mem R hR (lt_min (scale_pos R hR n) (by positivity))

theorem scale_lt_succ (R : RangeSet) (hR : R.IsCharacteristic) (n : ℕ) :
    scale R hR (n + 1) < scale R hR n := by
  have hpos : (0 : ℝ) < min (scale R hR n) (1 / ((n : ℝ) + 2)) :=
    lt_min (scale_pos R hR n) (by positivity)
  exact lt_of_lt_of_le (smallElt_lt R hR hpos) (min_le_left _ _)

theorem scale_lt_one_div (R : RangeSet) (hR : R.IsCharacteristic) :
    ∀ n : ℕ, scale R hR n < 1 / ((n : ℝ) + 1)
  | 0 => by
      have hone : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
      rw [hone]
      exact smallElt_lt R hR one_pos
  | n + 1 => by
      have hpos : (0 : ℝ) < min (scale R hR n) (1 / ((n : ℝ) + 2)) :=
        lt_min (scale_pos R hR n) (by positivity)
      have h := lt_of_lt_of_le (smallElt_lt R hR hpos) (min_le_right _ _)
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      exact h

theorem tendsto_scale (R : RangeSet) (hR : R.IsCharacteristic) :
    Filter.Tendsto (scale R hR) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (scale_pos R hR n)]
  refine lt_of_lt_of_le (scale_lt_one_div R hR n) (le_trans ?_ hN.le)
  apply one_div_le_one_div_of_le (by positivity)
  have hcast : ((N : ℝ)) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  linarith

/-- A characteristic range set carries a scale. -/
theorem exists_isScale {R : RangeSet} (hR : R.IsCharacteristic) : ∃ r : ℕ → ℝ, IsScale R r :=
  ⟨scale R hR,
    { mem := scale_mem R hR
      pos := scale_pos R hR
      strictAnti := strictAnti_nat_of_succ_lt (scale_lt_succ R hR)
      tendsto_zero := tendsto_scale R hR }⟩

/-- Conversely, a range set carrying a scale is characteristic; the hypothesis
of this track is therefore exactly the preprint's. -/
theorem isCharacteristic_of_isScale {R : RangeSet} {r : ℕ → ℝ} (h : IsScale R r) :
    R.IsCharacteristic := by
  intro ε hε
  obtain ⟨n, hn⟩ := h.exists_lt hε
  exact ⟨r n, h.mem n, h.pos n, hn⟩

end RangeSet

/-! ## `R`-valued pseudo-ultrametrics -/

/-- `d` satisfies the axioms of an `R`-valued pseudo-ultrametric on `Z`: it
vanishes on the diagonal, is symmetric, obeys the *strong* triangle inequality
`d x z ≤ d x y ∨ d y z`, and takes all its values in `R`.  Points are not
required to be separated — that is what distinguishes `UCPM(Z;R)` from
`UMet(Z;R)`.  Nonnegativity is not a field: it follows from `R ⊆ [0,∞)`. -/
structure IsUltraPMetOn (R : RangeSet) (d : Z → Z → ℝ) : Prop where
  dist_self : ∀ x, d x x = 0
  dist_comm : ∀ x y, d x y = d y x
  dist_triangle_max : ∀ x y z, d x z ≤ max (d x y) (d y z)
  mem_range : ∀ x y, d x y ∈ R.carrier

namespace IsUltraPMetOn

variable {R : RangeSet} {d : Z → Z → ℝ}

/-- The strong triangle inequality of an `R`-valued pseudo-ultrametric,
packaged in Mathlib's `IsUltrametricDist` class for the distance function
`d`. -/
theorem toIsUltrametricDist (h : IsUltraPMetOn R d) :
    @IsUltrametricDist Z ⟨d⟩ :=
  by
    letI : Dist Z := ⟨d⟩
    exact (⟨h.dist_triangle_max⟩ : IsUltrametricDist Z)

theorem nonneg (h : IsUltraPMetOn R d) (x y : Z) : 0 ≤ d x y := R.nonneg (h.mem_range x y)

theorem dist_triangle (h : IsUltraPMetOn R d) (x y z : Z) : d x z ≤ d x y + d y z :=
  (h.dist_triangle_max x y z).trans (max_le_add_of_nonneg (h.nonneg x y) (h.nonneg y z))

/-- **Isosceles principle.**  In an ultrametric, a triangle with two unequal
sides has its third side equal to the longer of the two.  This is what makes
the one-point amalgam of Theorem 3.13 computable off the ball. -/
theorem eq_of_lt (h : IsUltraPMetOn R d) {x y z : Z} (hlt : d y z < d x y) :
    d x z = d x y := by
  refine le_antisymm ((h.dist_triangle_max x y z).trans (max_le le_rfl hlt.le)) ?_
  have hxy : d x y ≤ max (d x z) (d z y) := h.dist_triangle_max x z y
  rw [h.dist_comm z y] at hxy
  rcases max_cases (d x z) (d y z) with ⟨he, -⟩ | ⟨he, -⟩
  · rwa [he] at hxy
  · rw [he] at hxy; exact absurd (lt_of_le_of_lt hxy hlt) (lt_irrefl _)

/-- A separated `R`-valued pseudo-ultrametric is a metric in the sense of
`Conj51/MetD.lean`, so the repository-wide compatibility condition applies to
it unchanged. -/
theorem toIsMetricOn (h : IsUltraPMetOn R d) (hsep : ∀ x y, d x y = 0 → x = y) :
    IsMetricOn d :=
  ⟨h.dist_self, fun {_ _} hxy => hsep _ _ hxy, h.dist_comm, h.dist_triangle⟩

end IsUltraPMetOn

/-- `UCPM Z R`: the preprint's `UCPM(Z;R)` for a discrete carrier `Z` — the
`R`-valued pseudo-ultrametrics on `Z`.  As in `Ext/BddPMet.lean`, continuity is
vacuous on a discrete carrier, and the Lean name records what is assumed. -/
def UCPM (Z : Type*) (R : RangeSet) : Type _ := {d : Z → Z → ℝ // IsUltraPMetOn R d}

namespace UCPM

variable {R : RangeSet}

theorem nonneg (d : UCPM Z R) (x y : Z) : 0 ≤ d.1 x y := d.2.nonneg x y

/-! ### The non-Archimedean uniform distance `𝒰𝒟^R` -/

/-- The set of tolerances admissible for the pair `(d,e)`: the members `ε` of
`R` with `d ≤ e ∨ ε` and `e ≤ d ∨ ε` pointwise. -/
def tolerances (d e : UCPM Z R) : Set ℝ :=
  {r | r ∈ R.carrier ∧ ∀ x y, d.1 x y ≤ max (e.1 x y) r ∧ e.1 x y ≤ max (d.1 x y) r}

/-- The preprint's `𝒰𝒟^R(d,e) = inf {ε ∈ R ∪ {∞} : d ≤ e ∨ ε, e ≤ d ∨ ε}`.
The `∞` of the preprint's index set is Lean's empty infimum: when no member of
`R` is admissible the value is `⊤`.  Mathlib has no such construction; this is
the library gap recorded in the file header. -/
def edist (d e : UCPM Z R) : ℝ≥0∞ := ⨅ r ∈ tolerances d e, ENNReal.ofReal r

theorem tolerances_comm (d e : UCPM Z R) : tolerances d e = tolerances e d := by
  ext r
  simp only [tolerances, mem_setOf_eq, and_congr_right_iff]
  exact fun _ => ⟨fun h x y => (h x y).symm, fun h x y => (h x y).symm⟩

/-- Every admissible tolerance bounds `𝒰𝒟^R`. -/
theorem edist_le_ofReal {d e : UCPM Z R} {r : ℝ} (hr : r ∈ tolerances d e) :
    edist d e ≤ ENNReal.ofReal r :=
  iInf₂_le r hr

/-- The dual bound: a real that is below every admissible tolerance is below
`𝒰𝒟^R`. -/
theorem ofReal_le_edist {d e : UCPM Z R} {v : ℝ}
    (h : ∀ r ∈ tolerances d e, v ≤ r) : ENNReal.ofReal v ≤ edist d e :=
  le_iInf₂ fun r hr => ENNReal.ofReal_le_ofReal (h r hr)

/-- **Readout.**  A bound on `𝒰𝒟^R` is a pointwise bound, with no membership
hypothesis on the bounding real.  This is the non-Archimedean analogue of
"`ρ(d,e) ≤ c` implies `|d − e| ≤ c` pointwise" and is what every use of the
ambient distance below goes through. -/
theorem le_max_of_edist_le {d e : UCPM Z R} {c : ℝ} (hc : 0 ≤ c)
    (h : edist d e ≤ ENNReal.ofReal c) (x y : Z) : d.1 x y ≤ max (e.1 x y) c := by
  by_contra hlt
  push Not at hlt
  have hec : e.1 x y < d.1 x y := lt_of_le_of_lt (le_max_left _ _) hlt
  have hcd : c < d.1 x y := lt_of_le_of_lt (le_max_right _ _) hlt
  have hall : ∀ r ∈ tolerances d e, d.1 x y ≤ r := by
    intro r hr
    have hle := (hr.2 x y).1
    rcases max_cases (e.1 x y) r with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hle; exact absurd (lt_of_le_of_lt hle hec) (lt_irrefl _)
    · rwa [he] at hle
  have hge : ENNReal.ofReal (d.1 x y) ≤ edist d e := ofReal_le_edist hall
  have hlt' : ENNReal.ofReal c < ENNReal.ofReal (d.1 x y) :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hc hcd)).mpr hcd
  exact absurd (hge.trans h) (not_le_of_gt hlt')

/-- **The elementary lower-bound step.**  A pair at which `e` takes the value
`ρ` while `d` stays strictly below it forces every admissible tolerance to be at
least `ρ`.  Both isometry lower bounds of this track (Lemma 3.11 and Theorem
3.13) reduce to this. -/
theorem le_of_mem_tolerances {d e : UCPM Z R} {c ρ : ℝ} (hc : c ∈ tolerances d e)
    (x y : Z) (hlt : d.1 x y < ρ) (heq : e.1 x y = ρ) : ρ ≤ c := by
  have hle := (hc.2 x y).2
  rw [heq] at hle
  rcases max_cases (d.1 x y) c with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he] at hle
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  · rwa [he] at hle

theorem edist_self (d : UCPM Z R) : edist d d = 0 := by
  have h0 : (0 : ℝ) ∈ tolerances d d := by
    refine ⟨R.zero_mem, fun x y => ?_⟩
    rw [max_eq_left (d.nonneg x y)]
    exact ⟨le_rfl, le_rfl⟩
  simpa using edist_le_ofReal h0

theorem edist_comm (d e : UCPM Z R) : edist d e = edist e d := by
  rw [edist, edist, tolerances_comm]

/-- A maximum of admissible tolerances for `(d,e)` and `(e,f)` is admissible
for `(d,f)`; `R` is closed under maxima, so this stays inside `R`. -/
theorem max_mem_tolerances {d e f : UCPM Z R} {r s : ℝ}
    (hr : r ∈ tolerances d e) (hs : s ∈ tolerances e f) :
    max r s ∈ tolerances d f := by
  refine ⟨R.max_mem hr.1 hs.1, fun x y => ⟨?_, ?_⟩⟩
  · calc d.1 x y ≤ max (e.1 x y) r := (hr.2 x y).1
      _ ≤ max (max (f.1 x y) s) r := max_le_max (hs.2 x y).1 le_rfl
      _ ≤ max (f.1 x y) (max r s) :=
          max_le (max_le (le_max_left _ _) (le_max_of_le_right (le_max_right r s)))
            (le_max_of_le_right (le_max_left r s))
  · calc f.1 x y ≤ max (e.1 x y) s := (hs.2 x y).2
      _ ≤ max (max (d.1 x y) r) s := max_le_max (hr.2 x y).2 le_rfl
      _ ≤ max (d.1 x y) (max r s) :=
          max_le (max_le (le_max_left _ _) (le_max_of_le_right (le_max_left r s)))
            (le_max_of_le_right (le_max_right r s))

theorem ofReal_max (a b : ℝ) :
    ENNReal.ofReal (max a b) = max (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (ENNReal.ofReal_le_ofReal h)]
  · rw [max_eq_left h, max_eq_left (ENNReal.ofReal_le_ofReal h)]

/-- A maximum of two infima over sets of reals is the infimum of the maxima.
The nontrivial inequality is proved directly: if the double infimum exceeded the
maximum, each single infimum would fall strictly below it, and a witness from
each side would contradict that.  No distributivity lemma is invoked, so the
argument does not depend on how `max` and `⊔` are identified in `ℝ≥0∞`. -/
theorem iInf_ofReal_max_le (A B : Set ℝ) :
    (⨅ r ∈ A, ⨅ s ∈ B, max (ENNReal.ofReal r) (ENNReal.ofReal s))
      ≤ max (⨅ r ∈ A, ENNReal.ofReal r) (⨅ s ∈ B, ENNReal.ofReal s) := by
  by_contra hcon
  push Not at hcon
  have ha : (⨅ r ∈ A, ENNReal.ofReal r)
      < ⨅ r ∈ A, ⨅ s ∈ B, max (ENNReal.ofReal r) (ENNReal.ofReal s) :=
    lt_of_le_of_lt (le_max_left _ _) hcon
  have hb : (⨅ s ∈ B, ENNReal.ofReal s)
      < ⨅ r ∈ A, ⨅ s ∈ B, max (ENNReal.ofReal r) (ENNReal.ofReal s) :=
    lt_of_le_of_lt (le_max_right _ _) hcon
  obtain ⟨r, hr⟩ := iInf_lt_iff.mp ha
  obtain ⟨hrA, hrc⟩ := iInf_lt_iff.mp hr
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp hb
  obtain ⟨hsB, hsc⟩ := iInf_lt_iff.mp hs
  have hle : (⨅ r ∈ A, ⨅ s ∈ B, max (ENNReal.ofReal r) (ENNReal.ofReal s))
      ≤ max (ENNReal.ofReal r) (ENNReal.ofReal s) :=
    iInf₂_le_of_le r hrA (iInf₂_le s hsB)
  exact absurd (lt_of_le_of_lt hle (max_lt hrc hsc)) (lt_irrefl _)

/-- **The strong triangle inequality for `𝒰𝒟^R`.**  The ambient distance is
itself an (extended) ultrametric — the non-Archimedean feature the preprint's
`UCPM(Z;R)` is built for. -/
theorem edist_triangle_max (d e f : UCPM Z R) :
    edist d f ≤ max (edist d e) (edist e f) := by
  have hstep : edist d f ≤ ⨅ r ∈ tolerances d e, ⨅ s ∈ tolerances e f,
      max (ENNReal.ofReal r) (ENNReal.ofReal s) := by
    refine le_iInf₂ fun r hr => le_iInf₂ fun s hs => ?_
    rw [← ofReal_max]
    exact edist_le_ofReal (max_mem_tolerances hr hs)
  refine hstep.trans ?_
  exact iInf_ofReal_max_le (tolerances d e) (tolerances e f)

theorem edist_triangle (d e f : UCPM Z R) : edist d f ≤ edist d e + edist e f :=
  (edist_triangle_max d e f).trans (max_le le_self_add le_add_self)

theorem eq_of_edist_eq_zero {d e : UCPM Z R} (h : edist d e = 0) : d = e := by
  have h0 : edist d e ≤ ENNReal.ofReal 0 := by simp [h]
  have h1 := le_max_of_edist_le (le_refl (0 : ℝ)) h0
  rw [edist_comm] at h0
  have h2 := le_max_of_edist_le (le_refl (0 : ℝ)) h0
  refine Subtype.ext (funext fun x => funext fun y => le_antisymm ?_ ?_)
  · simpa [max_eq_left (e.nonneg x y)] using h1 x y
  · simpa [max_eq_left (d.nonneg x y)] using h2 x y

instance instEDist : EDist (UCPM Z R) := ⟨edist⟩

instance instPseudoEMetricSpace : PseudoEMetricSpace (UCPM Z R) where
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle

instance instEMetricSpace : EMetricSpace (UCPM Z R) where
  eq_of_edist_eq_zero := eq_of_edist_eq_zero

theorem edist_eq (d e : UCPM Z R) : EDist.edist d e = edist d e := rfl

/-! ### The two reusable operations -/

/-- Pullback of an `R`-valued pseudo-ultrametric along an arbitrary map.  All
four axioms are preserved verbatim, because none of them mentions separation.
Both the relabelling isometry (`comap` along a bijection) and the two legs of
the one-point amalgam of Theorem 3.13 are instances of this. -/
def comap (f : Z → W) (d : UCPM W R) : UCPM Z R :=
  ⟨fun x y => d.1 (f x) (f y),
    { dist_self := fun _ => d.2.dist_self _
      dist_comm := fun _ _ => d.2.dist_comm _ _
      dist_triangle_max := fun _ _ _ => d.2.dist_triangle_max _ _ _
      mem_range := fun _ _ => d.2.mem_range _ _ }⟩

@[simp] theorem comap_val (f : Z → W) (d : UCPM W R) :
    (comap f d).1 = fun x y => d.1 (f x) (f y) := rfl

/-- The pointwise maximum of two `R`-valued pseudo-ultrametrics is one, and
`R`-valued because a maximum of two members of `R` is one of them.  Together
with `comap` this is what Theorem 3.13's one-point amalgam is assembled from:
that amalgam takes the *maximum* of the base distance and the coding distance,
where the Archimedean construction of audit §2.7 has to take a sum. -/
def sup (d e : UCPM Z R) : UCPM Z R :=
  ⟨fun x y => max (d.1 x y) (e.1 x y),
    { dist_self := fun x => by simp [d.2.dist_self x, e.2.dist_self x]
      dist_comm := fun x y => by rw [d.2.dist_comm x y, e.2.dist_comm x y]
      dist_triangle_max := fun x y z => by
        refine max_le ?_ ?_
        · exact (d.2.dist_triangle_max x y z).trans
            (max_le_max (le_max_left _ _) (le_max_left _ _))
        · exact (e.2.dist_triangle_max x y z).trans
            (max_le_max (le_max_right _ _) (le_max_right _ _))
      mem_range := fun x y => R.max_mem (d.2.mem_range x y) (e.2.mem_range x y) }⟩

@[simp] theorem sup_val (d e : UCPM Z R) :
    (sup d e).1 = fun x y => max (d.1 x y) (e.1 x y) := rfl

/-! ### Relabelling -/

theorem tolerances_comap (σ : Z ≃ W) (d e : UCPM W R) :
    tolerances (comap σ d) (comap σ e) = tolerances d e := by
  ext r
  simp only [tolerances, mem_setOf_eq, comap_val, and_congr_right_iff]
  refine fun _ => ⟨fun h x y => ?_, fun h x y => ?_⟩
  · simpa using h (σ.symm x) (σ.symm y)
  · exact h (σ x) (σ y)

theorem edist_comap (σ : Z ≃ W) (d e : UCPM W R) :
    edist (comap σ d) (comap σ e) = edist d e := by
  rw [edist, edist, tolerances_comap]

theorem isometry_comap (σ : Z ≃ W) : Isometry (comap σ : UCPM W R → UCPM Z R) :=
  fun d e => edist_comap σ d e

/-! ## The compatible members -/

/-- An `R`-valued pseudo-ultrametric is *compatible* when it is a metric
inducing the discrete topology.  This is verbatim the condition used by the
Archimedean ambients (`Ext/BddPMet.lean`), so "compatible" has one meaning
across the repository. -/
def IsCompatible (d : UCPM Z R) : Prop := ∃ h : IsMetricOn d.1, h.topology = ⊥

/-- Relabelling preserves compatibility, in both directions; the transport of
the predicate is the one already proved in `Ext/Relabel.lean`. -/
theorem isCompatible_comap_iff (σ : Z ≃ W) (d : UCPM W R) :
    IsCompatible (comap σ d) ↔ IsCompatible d :=
  exists_isMetricOn_comap_iff σ d.1

end UCPM

/-! ## `UMet(Z;R)` and the `R`-components -/

/-- The preprint's `UMet(Z;R) ⊆ UCPM(Z;R)`. -/
def UMet (Z : Type*) (R : RangeSet) : Set (UCPM Z R) := {d | UCPM.IsCompatible d}

@[simp] theorem mem_UMet {R : RangeSet} {d : UCPM Z R} :
    d ∈ UMet Z R ↔ UCPM.IsCompatible d := Iff.rfl

/-- The `R`-component of `d`: the compatible members at finite `𝒰𝒟^R`-distance
from `d`.  The preprint's `𝔠^R ∈ 𝐔𝐌_{<∞}(Z;R)`. -/
def UComponent {R : RangeSet} (d : UCPM Z R) : Set (UCPM Z R) :=
  {e | e ∈ UMet Z R ∧ UCPM.edist d e < ⊤}

@[simp] theorem mem_UComponent {R : RangeSet} {d e : UCPM Z R} :
    e ∈ UComponent d ↔ e ∈ UMet Z R ∧ UCPM.edist d e < ⊤ := Iff.rfl

theorem preimage_UMet_comap {R : RangeSet} (σ : Z ≃ W) :
    (UCPM.comap σ : UCPM W R → UCPM Z R) ⁻¹' UMet Z R = UMet W R := by
  ext d
  exact UCPM.isCompatible_comap_iff σ d

theorem preimage_UComponent_comap {R : RangeSet} (σ : Z ≃ W) (d : UCPM W R) :
    (UCPM.comap σ : UCPM W R → UCPM Z R) ⁻¹' UComponent (UCPM.comap σ d) = UComponent d := by
  ext e
  simp only [mem_preimage, mem_UComponent, mem_UMet, UCPM.edist_comap σ d e]
  exact and_congr_left fun _ => UCPM.isCompatible_comap_iff σ e

/-! ## A completeness criterion

Every compatible member of the coding families of this track is complete for
the same reason: its Cauchy sequences are eventually constant.  Stated once
here, for an arbitrary metric space, so that Lemma 3.10 and the amalgam of
Theorem 3.13 can both use it. -/

theorem completeSpace_of_cauchySeq_eventually_const {X : Type*} [MetricSpace X]
    (H : ∀ u : ℕ → X, CauchySeq u → ∃ N : ℕ, ∀ n ≥ N, u n = u N) : CompleteSpace X :=
  Metric.complete_of_cauchySeq_tendsto fun u hu => by
    obtain ⟨N, hN⟩ := H u hu
    exact ⟨u N, tendsto_atTop_of_eventually_const hN⟩

end

end IshikiExt
