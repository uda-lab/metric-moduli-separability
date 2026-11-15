-- Ext.UltraCoding
--
-- Issue #81, scope items 4–6: Lemma 3.10, Lemma 3.11 and Theorem 3.12 of
-- arXiv:2608.19618.
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` §2.13 (the
-- setup, Lemma 3.10 and Lemma 3.11) and the Theorem 3.12 paragraph of §2.14.
--
-- Setup (audit §2.13).  A characteristic range set `R`, a scale `r`
-- (`Ext/UltraPMet.lean`), the `R`-valued Cantor ultrametric `h`
-- (`Ext/CantorUltra.lean`) and a dense non-Borel `S ⊆ 2^ω` with `|S| = ℵ₁`
-- (Proposition 2.2).  The carrier is
--
--     Z = ⨆_{w ∈ S} C_w,     C_w = {y_w} ⊔ {x_{w,n} : n ∈ ℕ},
--
-- with cluster radii `l_n(w,t) = h(t,w) ∨ r n`, star values
--
--     d_t(y_w, x_{w,n}) = l_n(w,t),   d_t(x_{w,n}, x_{w,m}) = l_n ∨ l_m,
--
-- and the constant value `r 0` between different clusters.  As in
-- `Ext/BoundedCoding.lean` the clusters are indexed by `S` itself rather than
-- by an enumeration `α ↦ w_α`; that enumeration is a bijection onto `S`, and
-- the relabelling reduction is stated once (here: `UCPM.comap` along a
-- bijection, `Ext/UltraPMet.lean`).
--
-- Index conventions relative to the preprint:
--   * `y_w`       ↦ `(w, none)`
--   * `x_{w,n}`   ↦ `(w, some n)`
--   * `l_n(w,t)`  ↦ `uRadius r w t (some n) = h(t,w) ∨ r n`
--
-- Note the two structural differences from the Archimedean coding of
-- `Ext/BoundedCoding.lean`, both of them forced by the preprint: there is no
-- anchor pair `{p,q}` carrying the parameter, and the star values are maxima
-- rather than sums.  The parameter is recovered instead from *density* of `S`
-- (audit §2.13, Lemma 3.11 lower bound) — this is exactly the place where the
-- non-Archimedean track needs density and the Archimedean one does not.
--
-- What is proved here:
--   `dU_isUltraPMetOn`     — each `d_t` is an `R`-valued ultrametric (3.10).
--   `dU_le_head`           — values lie in `[0, r 0]` (3.10).
--   `isCompatible_phiU_iff`— `d_t` induces the discrete topology **iff**
--                            `t ∉ S` (3.10, both directions).
--   `dU_completeSpace`     — `d_t` is complete for `t ∉ S` (3.10).
--   `edist_phiU`           — `𝒰𝒟^R(d_s,d_t) = h(s,t)` exactly (3.11).
--   `isClosed_image_phiU`  — `Φ(2^ω ∖ S)` is closed in `UMet(Z;R)` (3.11).
--   `preimage_UMet_phiU`   — the exact pullback identity `Φ⁻¹(UMet) = 2^ω ∖ S`.
--   `umet_not_borel`,
--   `umet_not_borel_of_card` — Theorem 3.12, on the coded carrier and on an
--                            arbitrary discrete carrier of cardinality `ℵ₁`.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.CantorUltra

open Cardinal Set

namespace IshikiExt

noncomputable section

variable {R : RangeSet} {r : ℕ → ℝ}

/-! ## The carrier -/

/-- The carrier of the ultrametric coding: for every `w ∈ S` a cluster
consisting of a centre (`(w, none)`) and countably many spokes
(`(w, some n)`). -/
abbrev UltraIndex (S : Set (ℕ → Bool)) : Type := ↥S × Option ℕ

/-- `|Z| = ℵ₁ · ℵ₀ = ℵ₁`. -/
theorem card_ultraIndex {S : Set (ℕ → Bool)} (hS : #(↥S) = aleph 1) :
    #(UltraIndex S) = aleph 1 := by
  have hopt : #(Option ℕ) = (ℵ₀ : Cardinal) := by
    rw [mk_option, mk_nat]
    exact add_eq_left le_rfl one_le_aleph0
  have hℵ : (ℵ₀ : Cardinal) ≤ aleph 1 := aleph0_le_aleph 1
  show #(↥S × Option ℕ) = aleph 1
  rw [mk_prod, lift_id, lift_id, hS, hopt, mul_eq_max hℵ le_rfl, max_eq_left hℵ]

/-! ## Cluster radii and the star values -/

/-- The distance from the centre of the cluster at `w`: `0` at the centre
itself, and the preprint's `l_n(w,t) = h(t,w) ∨ r n` at the `n`-th spoke. -/
def uRadius (r : ℕ → ℝ) (w t : ℕ → Bool) : Option ℕ → ℝ
  | none => 0
  | some n => max (cantorDist r t w) (r n)

theorem uRadius_none (r : ℕ → ℝ) (w t : ℕ → Bool) : uRadius r w t none = 0 := rfl

theorem uRadius_some (r : ℕ → ℝ) (w t : ℕ → Bool) (n : ℕ) :
    uRadius r w t (some n) = max (cantorDist r t w) (r n) := rfl

theorem uRadius_nonneg (hr : RangeSet.IsScale R r) (w t : ℕ → Bool) :
    ∀ i, 0 ≤ uRadius r w t i
  | none => le_rfl
  | some n => le_max_of_le_right (hr.nonneg n)

theorem uRadius_le_head (hr : RangeSet.IsScale R r) (w t : ℕ → Bool) :
    ∀ i, uRadius r w t i ≤ r 0
  | none => hr.nonneg 0
  | some n => max_le (cantorDist_le_head hr t w) (hr.le_head n)

theorem uRadius_mem (hr : RangeSet.IsScale R r) (w t : ℕ → Bool) :
    ∀ i, uRadius r w t i ∈ R.carrier
  | none => R.zero_mem
  | some n => R.max_mem (cantorDist_mem hr t w) (hr.mem n)

/-- Every spoke is at least as far from the centre as the defect `h(t,w)`. -/
theorem cantorDist_le_uRadius (r : ℕ → ℝ) (w t : ℕ → Bool) (n : ℕ) :
    cantorDist r t w ≤ uRadius r w t (some n) := le_max_left _ _

theorem head_le_uRadius (r : ℕ → ℝ) (w t : ℕ → Bool) (n : ℕ) :
    r n ≤ uRadius r w t (some n) := le_max_right _ _

/-- The value of the coding inside one cluster: `0` on the diagonal and the
maximum of the two radii off it.  This is the non-Archimedean analogue of the
`σ i + σ j` star of `Ext/BoundedCoding.lean`. -/
def clusterDist (σ : Option ℕ → ℝ) (i j : Option ℕ) : ℝ :=
  if i = j then 0 else max (σ i) (σ j)

@[simp] theorem clusterDist_self (σ : Option ℕ → ℝ) (i : Option ℕ) : clusterDist σ i i = 0 := by
  simp [clusterDist]

theorem clusterDist_comm (σ : Option ℕ → ℝ) (i j : Option ℕ) :
    clusterDist σ i j = clusterDist σ j i := by
  by_cases h : i = j
  · rw [h]
  · rw [clusterDist, clusterDist, ite_eq_right h, ite_eq_right (Ne.symm h), max_comm]

theorem clusterDist_nonneg {σ : Option ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i) (i j : Option ℕ) :
    0 ≤ clusterDist σ i j := by
  rw [clusterDist]
  split_ifs
  · exact le_rfl
  · exact le_max_of_le_left (hσ i)

theorem clusterDist_le {σ : Option ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hσ : ∀ i, σ i ≤ c)
    (i j : Option ℕ) : clusterDist σ i j ≤ c := by
  rw [clusterDist]
  split_ifs
  · exact hc
  · exact max_le (hσ i) (hσ j)

theorem le_clusterDist_of_ne {σ : Option ℕ → ℝ} {i j : Option ℕ} (h : i ≠ j) :
    σ i ≤ clusterDist σ i j := by
  rw [clusterDist, ite_eq_right h]
  exact le_max_left _ _

/-- Off the diagonal of a cluster at least one of the two indices is a spoke. -/
theorem exists_spoke {i j : Option ℕ} (h : i ≠ j) : ∃ n : ℕ, i = some n ∨ j = some n := by
  cases i with
  | none =>
      cases j with
      | none => exact absurd rfl h
      | some m => exact ⟨m, Or.inr rfl⟩
  | some n => exact ⟨n, Or.inl rfl⟩

/-- **The max-star strong triangle inequality.**  Points carrying nonnegative
radii `σ` and joined through a common centre by `d i j = σ i ∨ σ j` satisfy the
*strong* triangle inequality.  This is the within-a-cluster case of Lemma
3.10, and the exact analogue of `starLike_triangle` in
`Ext/BoundedCoding.lean`. -/
theorem clusterDist_triangle_max {σ : Option ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i) (i j k : Option ℕ) :
    clusterDist σ i k ≤ max (clusterDist σ i j) (clusterDist σ j k) := by
  simp only [clusterDist]
  by_cases hik : i = k
  · rw [ite_eq_left hik]
    refine le_trans ?_ (le_max_left _ _)
    split_ifs
    · exact le_rfl
    · exact le_max_of_le_left (hσ i)
  · rw [ite_eq_right hik]
    by_cases hij : i = j
    · have hjk : j ≠ k := fun h => hik (hij.trans h)
      rw [ite_eq_left hij, ite_eq_right hjk, ← hij]
      exact le_max_right _ _
    · rw [ite_eq_right hij]
      by_cases hjk : j = k
      · rw [ite_eq_left hjk, ← hjk]
        exact le_max_left _ _
      · rw [ite_eq_right hjk]
        exact max_le (le_max_of_le_left (le_max_left _ _))
          (le_max_of_le_right (le_max_right _ _))

/-- Off the diagonal of a cluster the value dominates the scale term of one of
the two spokes involved.  This is what separates points of a cluster. -/
theorem exists_head_le_clusterDist (r : ℕ → ℝ) (w t : ℕ → Bool) {i j : Option ℕ}
    (h : i ≠ j) : ∃ n : ℕ, r n ≤ clusterDist (uRadius r w t) i j := by
  obtain ⟨n, hn⟩ := exists_spoke h
  refine ⟨n, ?_⟩
  rw [clusterDist, ite_eq_right h]
  rcases hn with hn | hn
  · rw [hn]; exact le_max_of_le_left (head_le_uRadius r w t n)
  · rw [hn]; exact le_max_of_le_right (head_le_uRadius r w t n)

/-- Off the diagonal of the cluster at `w` the value is at least the defect
`h(t,w)`.  This is the uniform lower bound that makes `d_t` complete for
`t ∉ S`. -/
theorem cantorDist_le_clusterDist (r : ℕ → ℝ) (w t : ℕ → Bool) {i j : Option ℕ}
    (h : i ≠ j) : cantorDist r t w ≤ clusterDist (uRadius r w t) i j := by
  obtain ⟨n, hn⟩ := exists_spoke h
  rw [clusterDist, ite_eq_right h]
  rcases hn with hn | hn
  · rw [hn]; exact le_max_of_le_left (cantorDist_le_uRadius r w t n)
  · rw [hn]; exact le_max_of_le_right (cantorDist_le_uRadius r w t n)

/-- A uniform isolating radius inside the cluster at `w`, for a parameter `t`
off `S`: `h(t,w) > 0` at the centre and `r n` at the `n`-th spoke.  Both are at
most `r 0`, so the same radius also separates the point from every other
cluster. -/
theorem exists_isolating_radius (hr : RangeSet.IsScale R r) {w t : ℕ → Bool}
    (hne : t ≠ w) (i : Option ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r 0 ∧ ∀ j, j ≠ i → ε ≤ clusterDist (uRadius r w t) j i := by
  cases i with
  | none =>
      refine ⟨cantorDist r t w, cantorDist_pos_of_ne hr hne, cantorDist_le_head hr t w,
        fun j hj => cantorDist_le_clusterDist r w t hj⟩
  | some n =>
      refine ⟨r n, hr.pos n, hr.le_head n, fun j hj => ?_⟩
      rw [clusterDist_comm]
      exact le_trans (head_le_uRadius r w t n) (le_clusterDist_of_ne (Ne.symm hj))

/-! ## The coding family `d_t` (Lemma 3.10) -/

open Classical in
/-- The preprint's `d_t` (audit §2.13): the max-star value inside a cluster,
and the constant `r 0` between different clusters. -/
def dU (r : ℕ → ℝ) (S : Set (ℕ → Bool)) (t : ℕ → Bool) (u v : UltraIndex S) : ℝ :=
  if u.1 = v.1 then clusterDist (uRadius r (u.1 : ℕ → Bool) t) u.2 v.2 else r 0

theorem dU_of_fst_eq {S : Set (ℕ → Bool)} {t : ℕ → Bool} {u v : UltraIndex S}
    (h : u.1 = v.1) :
    dU r S t u v = clusterDist (uRadius r (u.1 : ℕ → Bool) t) u.2 v.2 := by
  rw [dU, ite_eq_left h]

theorem dU_of_fst_ne {S : Set (ℕ → Bool)} {t : ℕ → Bool} {u v : UltraIndex S}
    (h : u.1 ≠ v.1) : dU r S t u v = r 0 := by
  rw [dU, ite_eq_right h]

/-- The value inside one cluster, with both endpoints displayed as pairs; this
is the form the isolating-radius and separating-pair arguments rewrite with. -/
theorem dU_same (r : ℕ → ℝ) (S : Set (ℕ → Bool)) (t : ℕ → Bool) (a : ↥S) (i j : Option ℕ) :
    dU r S t (a, i) (a, j) = clusterDist (uRadius r (a : ℕ → Bool) t) i j :=
  dU_of_fst_eq rfl

/-- The value between two clusters, in the same displayed form. -/
theorem dU_diff (r : ℕ → ℝ) (S : Set (ℕ → Bool)) (t : ℕ → Bool) {a b : ↥S} (h : a ≠ b)
    (i j : Option ℕ) : dU r S t (a, i) (b, j) = r 0 :=
  dU_of_fst_ne h

@[simp] theorem dU_self (r : ℕ → ℝ) (S : Set (ℕ → Bool)) (t : ℕ → Bool) (u : UltraIndex S) :
    dU r S t u u = 0 := by
  have h : dU r S t u u = clusterDist (uRadius r (u.1 : ℕ → Bool) t) u.2 u.2 :=
    dU_of_fst_eq rfl
  rw [h, clusterDist_self]

theorem dU_comm (r : ℕ → ℝ) (S : Set (ℕ → Bool)) (t : ℕ → Bool) (u v : UltraIndex S) :
    dU r S t u v = dU r S t v u := by
  by_cases h : u.1 = v.1
  · rw [dU_of_fst_eq h, dU_of_fst_eq h.symm, ← h, clusterDist_comm]
  · rw [dU_of_fst_ne h, dU_of_fst_ne (Ne.symm h)]

theorem dU_nonneg (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool)
    (u v : UltraIndex S) : 0 ≤ dU r S t u v := by
  by_cases h : u.1 = v.1
  · rw [dU_of_fst_eq h]
    exact clusterDist_nonneg (uRadius_nonneg hr _ t) _ _
  · rw [dU_of_fst_ne h]; exact hr.nonneg 0

/-- **Boundedness** (audit §2.13): all values of `d_t` lie in `[0, r 0]`, which
is what lets the constant cross-cluster value `r 0` dominate every triangle. -/
theorem dU_le_head (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool)
    (u v : UltraIndex S) : dU r S t u v ≤ r 0 := by
  by_cases h : u.1 = v.1
  · rw [dU_of_fst_eq h]
    exact clusterDist_le (hr.nonneg 0) (uRadius_le_head hr _ t) _ _
  · exact le_of_eq (dU_of_fst_ne h)

theorem dU_mem (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool)
    (u v : UltraIndex S) : dU r S t u v ∈ R.carrier := by
  by_cases h : u.1 = v.1
  · rw [dU_of_fst_eq h, clusterDist]
    split_ifs
    · exact R.zero_mem
    · exact R.max_mem (uRadius_mem hr _ t _) (uRadius_mem hr _ t _)
  · rw [dU_of_fst_ne h]; exact hr.mem 0

theorem dU_triangle_max (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool)
    (u v w : UltraIndex S) : dU r S t u w ≤ max (dU r S t u v) (dU r S t v w) := by
  by_cases huw : u.1 = w.1
  · by_cases huv : u.1 = v.1
    · -- all three in one cluster: the max-star inequality
      rw [dU_of_fst_eq huw, dU_of_fst_eq huv,
        dU_of_fst_eq (huv.symm.trans huw : v.1 = w.1), ← huv]
      exact clusterDist_triangle_max (uRadius_nonneg hr _ t) _ _ _
    · -- middle point in another cluster: both legs have length `r 0`
      have hvw : v.1 ≠ w.1 := fun h => huv (huw.trans h.symm)
      rw [dU_of_fst_ne huv, dU_of_fst_ne hvw]
      exact (dU_le_head hr S t u w).trans (le_max_left _ _)
  · -- endpoints in different clusters: `d_t u w = r 0` and one leg is `r 0`
    rw [dU_of_fst_ne huw]
    by_cases huv : u.1 = v.1
    · have hvw : v.1 ≠ w.1 := fun h => huw (huv.trans h)
      rw [dU_of_fst_ne hvw]
      exact le_max_right _ _
    · rw [dU_of_fst_ne huv]
      exact le_max_left _ _

/-- **Lemma 3.10, ultrametricity and `R`-valuedness.**  For *every* parameter
`t ∈ 2^ω` — including `t ∈ S`, where compatibility fails — `d_t` is an
`R`-valued ultrametric on the carrier. -/
theorem dU_isUltraPMetOn (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool) :
    IsUltraPMetOn R (dU r S t) where
  dist_self := dU_self r S t
  dist_comm := dU_comm r S t
  dist_triangle_max := dU_triangle_max hr S t
  mem_range := dU_mem hr S t

theorem dU_pos_of_ne (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} {t : ℕ → Bool}
    {u v : UltraIndex S} (h : u ≠ v) : 0 < dU r S t u v := by
  by_cases hfst : u.1 = v.1
  · rw [dU_of_fst_eq hfst]
    have hsnd : u.2 ≠ v.2 := fun h2 => h (Prod.ext hfst h2)
    obtain ⟨n, hn⟩ := exists_head_le_clusterDist r ((u.1 : ℕ → Bool)) t hsnd
    exact lt_of_lt_of_le (hr.pos n) hn
  · rw [dU_of_fst_ne hfst]; exact hr.pos 0

theorem dU_isMetricOn (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool) :
    IsMetricOn (dU r S t) :=
  (dU_isUltraPMetOn hr S t).toIsMetricOn fun u v huv => by
    by_contra hne
    exact absurd huv (ne_of_gt (dU_pos_of_ne hr hne))

/-! ### Compatibility with the discrete topology (Lemma 3.10) -/

/-- **Compatibility, `t ∉ S`** (audit §2.13).  The isolating radii are `r n` at
the `n`-th spoke and `h(t,w) > 0` at the centre of the cluster at `w`; the
latter is positive exactly because `t ∉ S ∋ w`. -/
theorem dU_topology_eq_bot (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} {t : ℕ → Bool}
    (htS : t ∉ S) : (dU_isMetricOn hr S t).topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  rintro ⟨a, i⟩
  have hta : t ≠ (a : ℕ → Bool) := fun h => htS (h ▸ a.2)
  obtain ⟨ε, hεpos, hεhead, hεcl⟩ := exists_isolating_radius hr hta i
  refine ⟨ε, hεpos, ?_⟩
  rintro ⟨b, j⟩ hlt
  by_cases hab : b = a
  · subst hab
    by_cases hij : j = i
    · rw [hij]
    · rw [dU_same] at hlt
      exact absurd hlt (not_lt.mpr (hεcl j hij))
  · rw [dU_diff r S t hab] at hlt
    exact absurd hlt (not_lt.mpr hεhead)

/-- **Compatibility fails at `t ∈ S`** (audit §2.13): the centre of the cluster
at `t` is not isolated, because `d_t(y_t, x_{t,n}) = r n → 0`. -/
theorem dU_topology_ne_bot (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} {t : ℕ → Bool}
    (htS : t ∈ S) : (dU_isMetricOn hr S t).topology ≠ ⊥ := by
  intro hbot
  rw [IsMetricOn.topology_eq_bot_iff] at hbot
  obtain ⟨ε, hε, hall⟩ := hbot ((⟨t, htS⟩ : ↥S), none)
  obtain ⟨n, hn⟩ := hr.exists_lt hε
  have hne : ((⟨t, htS⟩ : ↥S), some n) ≠ ((⟨t, htS⟩ : ↥S), none) := by simp
  refine hne (hall _ ?_)
  rw [dU_same, clusterDist, ite_eq_right (by simp : (some n : Option ℕ) ≠ none)]
  show max (uRadius r t t (some n)) (uRadius r t t none) < ε
  rw [uRadius_some, uRadius_none, cantorDist_self, max_eq_right (hr.nonneg n),
    max_eq_left (hr.nonneg n)]
  exact hn

/-! ### Completeness for `t ∉ S` (Lemma 3.10) -/

/-- **Completeness** (audit §2.13).  For `t ∉ S` the metric `d_t` is complete:
a Cauchy sequence is confined to a single cluster by the constant
cross-cluster value `r 0`, and inside the cluster at `w` all nonzero distances
are `≥ h(t,w) > 0`, so the sequence is eventually constant. -/
theorem dU_completeSpace (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} {t : ℕ → Bool}
    (htS : t ∉ S) :
    @CompleteSpace (UltraIndex S)
      (dU_isMetricOn hr S t).toMetricSpace.toPseudoMetricSpace.toUniformSpace := by
  letI : MetricSpace (UltraIndex S) := (dU_isMetricOn hr S t).toMetricSpace
  have hdist : ∀ u v : UltraIndex S, dist u v = dU r S t u v := fun _ _ => rfl
  refine completeSpace_of_cauchySeq_eventually_const fun u hu => ?_
  rw [Metric.cauchySeq_iff] at hu
  -- the tail lies in a single cluster
  obtain ⟨N, hN⟩ := hu (r 0) (hr.pos 0)
  have hcl : ∀ n ≥ N, (u n).1 = (u N).1 := by
    intro n hn
    by_contra hne
    have hlt := hN n hn N le_rfl
    rw [hdist, dU_of_fst_ne hne] at hlt
    exact absurd hlt (lt_irrefl _)
  -- inside that cluster, distinct points are `≥ h(t,w) > 0` apart
  have hta : t ≠ ((u N).1 : ℕ → Bool) := fun h => htS (h ▸ (u N).1.2)
  obtain ⟨M, hM⟩ := hu (cantorDist r t ((u N).1 : ℕ → Bool)) (cantorDist_pos_of_ne hr hta)
  refine ⟨max M N, fun n hn => ?_⟩
  have hnN : n ≥ N := le_trans (le_max_right M N) hn
  have hcln : (u n).1 = (u N).1 := hcl n hnN
  have hfst : (u n).1 = (u (max M N)).1 := hcln.trans (hcl _ (le_max_right M N)).symm
  refine Prod.ext hfst ?_
  by_contra hsnd
  have hlt := hM n (le_trans (le_max_left M N) hn) (max M N) (le_max_left M N)
  rw [hdist, dU_of_fst_eq hfst, hcln] at hlt
  exact absurd hlt (not_lt.mpr (cantorDist_le_clusterDist r _ t hsnd))

/-! ## The parameter map `Φ` (Lemma 3.11) -/

/-- The preprint's `Φ : 2^ω → UCPM(Z;R)`, `Φ(t) = d_t`.  It is defined on all
of `2^ω`, not only on `2^ω ∖ S`; that is what makes the pullback identity
below available. -/
def phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool) :
    UCPM (UltraIndex S) R :=
  ⟨dU r S t, dU_isUltraPMetOn hr S t⟩

@[simp] theorem phiU_val (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (t : ℕ → Bool) :
    (phiU hr S t).1 = dU r S t := rfl

/-- Each cluster radius is `h(s,t)`-close to its counterpart, in the
non-Archimedean sense: `l_n(w,s) ≤ l_n(w,t) ∨ h(s,t)`.  This is the strong
triangle inequality of `h` in the form Lemma 3.11's upper bound needs. -/
theorem uRadius_le_max (hr : RangeSet.IsScale R r) (w s t : ℕ → Bool) :
    ∀ i, uRadius r w s i ≤ max (uRadius r w t i) (cantorDist r s t)
  | none => by
      rw [uRadius_none, uRadius_none]
      exact le_max_of_le_left le_rfl
  | some n => by
      rw [uRadius_some, uRadius_some]
      refine max_le ?_ (le_max_of_le_left (le_max_right _ _))
      refine (cantorDist_triangle_max hr s t w).trans ?_
      exact max_le (le_max_right _ _) (le_max_of_le_left (le_max_left _ _))

theorem dU_le_max (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (s t : ℕ → Bool)
    (u v : UltraIndex S) :
    dU r S s u v ≤ max (dU r S t u v) (cantorDist r s t) := by
  by_cases h : u.1 = v.1
  · rw [dU_of_fst_eq h, dU_of_fst_eq h, clusterDist, clusterDist]
    split_ifs
    · exact le_max_of_le_left le_rfl
    · refine max_le ?_ ?_
      · exact (uRadius_le_max hr _ s t u.2).trans
          (max_le_max (le_max_left _ _) le_rfl)
      · exact (uRadius_le_max hr _ s t v.2).trans
          (max_le_max (le_max_right _ _) le_rfl)
  · rw [dU_of_fst_ne h, dU_of_fst_ne h]
    exact le_max_left _ _

/-- **Lemma 3.11, upper bound.**  `𝒰𝒟^R(d_s,d_t) ≤ h(s,t)`; density of `S` is
not used here. -/
theorem edist_phiU_le (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) (s t : ℕ → Bool) :
    UCPM.edist (phiU hr S s) (phiU hr S t) ≤ ENNReal.ofReal (cantorDist r s t) := by
  refine UCPM.edist_le_ofReal ⟨cantorDist_mem hr s t, fun u v => ⟨?_, ?_⟩⟩
  · exact dU_le_max hr S s t u v
  · have h := dU_le_max hr S t s u v
    rwa [cantorDist_comm r t s] at h

/-- **The separating pair — this is where density of `S` is used.**  Choose
`w ∈ S` with `h(s,w) < ρ := h(s,t)`; the isosceles property forces
`h(t,w) = ρ`, and any spoke index `n` with `r n < ρ` makes the pair
`(y_w, x_{w,n})` carry the value `ρ` for `d_t` and a strictly smaller value for
`d_s`.  The audit records (§2.1) that the Archimedean track can dispense with
density; the non-Archimedean one cannot, and no such shortcut is imported here.

The pair is produced separately from the isometry statement because Theorem
3.13 needs the same pair transported into a ball. -/
theorem exists_separating_pair (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)}
    (hS : Dense S) {s t : ℕ → Bool} (hst : s ≠ t) :
    ∃ u v : UltraIndex S,
      dU r S s u v < cantorDist r s t ∧ dU r S t u v = cantorDist r s t := by
  have hρpos : 0 < cantorDist r s t := cantorDist_pos_of_ne hr hst
  obtain ⟨n, hn⟩ := hr.exists_lt hρpos
  obtain ⟨w, hwS, hw⟩ := exists_mem_cantorDist_lt hS hr s n
  have hswρ : cantorDist r s w < cantorDist r s t := hw.trans hn
  have htw : cantorDist r t w = cantorDist r s t := cantorDist_isosceles hr hswρ
  refine ⟨((⟨w, hwS⟩ : ↥S), none), ((⟨w, hwS⟩ : ↥S), some n), ?_, ?_⟩
  · rw [dU_same, clusterDist, ite_eq_right (by simp : (none : Option ℕ) ≠ some n)]
    show max (uRadius r w s none) (uRadius r w s (some n)) < cantorDist r s t
    rw [uRadius_none, uRadius_some,
      max_eq_right (le_max_of_le_right (hr.nonneg n) :
        (0 : ℝ) ≤ max (cantorDist r s w) (r n))]
    exact max_lt hswρ hn
  · rw [dU_same, clusterDist, ite_eq_right (by simp : (none : Option ℕ) ≠ some n)]
    show max (uRadius r w t none) (uRadius r w t (some n)) = cantorDist r s t
    rw [uRadius_none, uRadius_some, htw, max_eq_left (le_of_lt hn),
      max_eq_right hρpos.le]

/-- **Lemma 3.11, lower bound**: the separating pair above bounds every
admissible tolerance from below by `h(s,t)`. -/
theorem le_edist_phiU (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} (hS : Dense S)
    (s t : ℕ → Bool) :
    ENNReal.ofReal (cantorDist r s t) ≤ UCPM.edist (phiU hr S s) (phiU hr S t) := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  obtain ⟨u, v, hus, hut⟩ := exists_separating_pair hr hS hst
  exact UCPM.ofReal_le_edist fun c hc => UCPM.le_of_mem_tolerances hc u v hus hut

/-- **Lemma 3.11, the isometry.**  `Φ` is an exact `𝒰𝒟^R`-isometry from the
Cantor ultrametric: `𝒰𝒟^R(d_s,d_t) = h(s,t)`. -/
theorem edist_phiU (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} (hS : Dense S)
    (s t : ℕ → Bool) :
    UCPM.edist (phiU hr S s) (phiU hr S t) = ENNReal.ofReal (cantorDist r s t) :=
  le_antisymm (edist_phiU_le hr S s t) (le_edist_phiU hr hS s t)

theorem continuous_phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    Continuous (phiU hr S) :=
  continuous_of_edist_le_cantorDist hr fun s t => edist_phiU_le hr S s t

theorem injective_phiU (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)} (hS : Dense S) :
    Function.Injective (phiU hr S) := by
  intro s t hstEq
  by_contra hne
  have h0 : UCPM.edist (phiU hr S s) (phiU hr S t) = 0 := by
    rw [hstEq]; exact UCPM.edist_self _
  rw [edist_phiU hr hS] at h0
  rw [ENNReal.ofReal_eq_zero] at h0
  exact absurd (le_antisymm h0 (cantorDist_nonneg hr s t))
    (ne_of_gt (cantorDist_pos_of_ne hr hne))

/-! ### The pullback and trace identities -/

theorem isCompatible_phiU_iff (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool))
    (t : ℕ → Bool) : UCPM.IsCompatible (phiU hr S t) ↔ t ∉ S := by
  constructor
  · rintro ⟨h, hbot⟩ htS
    exact dU_topology_ne_bot hr htS hbot
  · intro htS
    exact ⟨dU_isMetricOn hr S t, dU_topology_eq_bot hr htS⟩

/-- **The exact pullback identity**: `Φ⁻¹(UMet(Z;R)) = 2^ω ∖ S`.  This is the
identity that carries Theorem 3.12; it is strictly stronger than the
existential non-Borel conclusion. -/
theorem preimage_UMet_phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    phiU hr S ⁻¹' UMet (UltraIndex S) R = Sᶜ := by
  ext t
  simp only [Set.mem_preimage, Set.mem_compl_iff, mem_UMet]
  exact isCompatible_phiU_iff hr S t

/-- The compact witness `L = Φ(2^ω)` of the trace argument. -/
theorem isCompact_range_phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    IsCompact (Set.range (phiU hr S)) :=
  isCompact_range (continuous_phiU hr S)

theorem isClosed_range_phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    IsClosed (Set.range (phiU hr S)) :=
  (isCompact_range_phiU hr S).isClosed

/-- **The trace identity** `L ∩ UMet(Z;R) = Φ(2^ω ∖ S)` (audit §2.14, Theorem
3.12). -/
theorem image_compl_eq_range_inter_UMet (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    phiU hr S '' Sᶜ = Set.range (phiU hr S) ∩ UMet (UltraIndex S) R := by
  ext d
  constructor
  · rintro ⟨t, htS, rfl⟩
    exact ⟨⟨t, rfl⟩, (isCompatible_phiU_iff hr S t).mpr htS⟩
  · rintro ⟨⟨t, rfl⟩, hd⟩
    exact ⟨t, (isCompatible_phiU_iff hr S t).mp hd, rfl⟩

/-- **Lemma 3.11, closed image**: `Φ(2^ω ∖ S)` is closed in `UMet(Z;R)` with
its subspace topology. -/
theorem isClosed_image_phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    IsClosed (Subtype.val ⁻¹' (phiU hr S '' Sᶜ) : Set ↥(UMet (UltraIndex S) R)) := by
  rw [image_compl_eq_range_inter_UMet]
  have hpre : (Subtype.val ⁻¹' (Set.range (phiU hr S) ∩ UMet (UltraIndex S) R) :
      Set ↥(UMet (UltraIndex S) R)) = Subtype.val ⁻¹' Set.range (phiU hr S) := by
    ext d
    simp
  rw [hpre]
  exact (isClosed_range_phiU hr S).preimage continuous_subtype_val

/-! ## Theorem 3.12 -/

local instance ucpmMeasurableSpace (Z : Type*) (R : RangeSet) :
    MeasurableSpace (UCPM Z R) := borel (UCPM Z R)

local instance ucpmBorelSpace (Z : Type*) (R : RangeSet) : BorelSpace (UCPM Z R) := ⟨rfl⟩

/-- **Theorem 3.12 on the coded carrier.**  `UMet(Z;R)` is not Borel in
`UCPM(Z;R)`.  The proof is the pullback route: `Φ` is continuous, hence
Borel-measurable, and `Φ⁻¹(UMet) = 2^ω ∖ S`, so a Borel `UMet` would make `S`
Borel. -/
theorem umet_not_borel (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)}
    (hSnonmeas : ¬ MeasurableSet S) : ¬ MeasurableSet (UMet (UltraIndex S) R) := by
  intro hU
  have hpre : MeasurableSet (phiU hr S ⁻¹' UMet (UltraIndex S) R) :=
    hU.preimage (continuous_phiU hr S).measurable
  rw [preimage_UMet_phiU hr S] at hpre
  exact hSnonmeas (by simpa using hpre.compl)

/-- Every carrier of cardinality `ℵ₁` is a relabelling of the coded carrier
supplied by Proposition 2.2, and the parameter set is dense and non-Borel.
Universes are compared after `Cardinal.lift`, exactly as in
`Ext/Relabel.lean`. -/
theorem exists_equiv_ultraIndex_of_card {Z : Type*} (hZ : #Z = aleph 1) :
    ∃ S : Set (ℕ → Bool), Dense S ∧ ¬ MeasurableSet S ∧ Nonempty (Z ≃ UltraIndex S) := by
  obtain ⟨S, hSdense, hScard, hSnonmeas⟩ := exists_dense_aleph1_nonBorel_cantor
  refine ⟨S, hSdense, hSnonmeas, Cardinal.lift_mk_eq'.mp ?_⟩
  rw [hZ, card_ultraIndex hScard]
  simp

/-- **Theorem 3.12, in its literal arbitrary-carrier form** (audit §2.14).  For
every discrete `Z` with `|Z| = ℵ₁` and every characteristic range set `R`, the
compatible `R`-valued ultrametrics on `Z` form a non-Borel subset of
`UCPM(Z;R)`.  No hypothesis on a parameter set is left in the statement. -/
theorem umet_not_borel_of_card (hR : R.IsCharacteristic) (Z : Type*)
    (hZ : #Z = aleph 1) : ¬ MeasurableSet (UMet Z R) := by
  intro hU
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  obtain ⟨S, -, hSnonmeas, ⟨σ⟩⟩ := exists_equiv_ultraIndex_of_card hZ
  have hpre : MeasurableSet ((UCPM.comap σ : UCPM (UltraIndex S) R → UCPM Z R) ⁻¹' UMet Z R) :=
    hU.preimage (UCPM.isometry_comap σ).continuous.measurable
  rw [preimage_UMet_comap σ] at hpre
  exact umet_not_borel hr hSnonmeas hpre

/-- Neither Theorem 3.12 nor Theorem 3.13 is vacuous: a characteristic `R` and
a carrier of cardinality `ℵ₁` do carry compatible `R`-valued ultrametrics.  The
witness is the Lemma 3.10 coding at any parameter off the parameter set, which
is nonempty because a non-Borel `S` is not all of `2^ω`. -/
theorem exists_mem_UMet_of_card (hR : R.IsCharacteristic) (Z : Type*)
    (hZ : #Z = aleph 1) : (UMet Z R).Nonempty := by
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  obtain ⟨S, -, hSnonmeas, ⟨σ⟩⟩ := exists_equiv_ultraIndex_of_card hZ
  obtain ⟨t, htS⟩ : (Sᶜ : Set (ℕ → Bool)).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hSnonmeas (by rw [h]; exact MeasurableSet.univ)
  refine ⟨UCPM.comap σ (phiU hr S t), ?_⟩
  rw [mem_UMet]
  exact (UCPM.isCompatible_comap_iff σ _).mpr ((isCompatible_phiU_iff hr S t).mpr htS)

end

end IshikiExt
