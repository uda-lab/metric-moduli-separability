-- Conj51.MetricConstruction
--
-- LEM-STAR-METRIC (report 補題 3.3): the family of metrics on `D`
-- parametrised by `t ∈ [0,1]`, lying in `Met(D)` exactly for
-- `t ∈ A^∁ = [0,1] \ A`.
--
-- Mathematical source of truth: `report/report-ja.md` §3.3.  The report
-- fixes an injective enumeration `A = {a_α : α < ω₁}` and indexes the sets
-- `C_α` by `α < ω₁`; here they are indexed by `A` itself.  Since `|A| = ℵ₁`,
-- that enumeration is a *bijection* `ω₁ ≃ A`, so the two index sets give the
-- same construction up to relabelling — the relabelling principle is report
-- §3.2.  Nothing else is changed: the distance table, the function
-- `s_n(α,t)`, and the statements (C1)–(C3) are transcribed literally.
--
-- Index conventions relative to the report:
--   * report `p, q`               ↦ `Sum.inl true`, `Sum.inl false`
--   * report `y_α`                ↦ `Sum.inr (a, none)`
--   * report `x_{α,n}`, `n ∈ ℕ`   ↦ `Sum.inr (a, some n)`
--   * report `s_n(α,t) = min(1, |t − a_α| + 1/(n+1))`, `n ∈ ℕ`
--                                 ↦ `starSpoke n a t = min 1 (|t − a| + 1/(n+1))`
--     — the report's index convention matches this file literally.
--     (The internal `star`/`spoke`/`centre`/`block` vocabulary below is
--     Lean-side proof-engineering naming only; the report uses the symbols
--     `C_α`, `y_α`, `x_{α,n}`, `{p,q}` directly.)
--
-- What is proved here (report §3.3):
--   (C1) `dStar_isMetricOn`      — `d_t` is a metric for every `t ∈ [0,1]`.
--   (C2) `dStar_topology_eq_bot` — for `t ∉ A` it induces the discrete topology.
--   (C3) `dStar_topology_ne_bot` — for `t ∈ A` it does not.
--   `dStar_mem_MetD_iff`         — the equivalence in report 補題 3.3:
--                                  `d_t ∈ Met(D) ↔ t ∈ A^∁`.
--   `card_starIndex`             — `|D| = ℵ₁` (report §3.3).
--   `lem_star_metric`            — LEM-STAR-METRIC itself: the conjunction of
--     `|D| = ℵ₁`, (C1), the equivalence, and the existence of the parameter
--     map `φ : A^∁ → MetD (StarIndex A)` of report §3.4.
-- Together with the pointwise Lipschitz estimates `dStar_sub_le` /
-- `dStar_anchor_sub` (report §3.4, the pair-by-pair half of (C4)) that the
-- bi-Lipschitz embedding is built from.  The supremum-level estimate
-- `|t−s| ≤ ρ(d_t,d_s) ≤ 2|t−s|` and the closedness of the image are
-- LEM-CLOSED-IMAGE (Issue #9, `ClosedEmbedding.lean`).

import Mathlib
import IshikiConj51.Conj51.MetD

open Cardinal

/-! ## The index type `D` (report §3.3) -/

/-- The carrier `D` of the report's §3.3 construction: two anchor points
(`Sum.inl`), and, for every `a ∈ A`, a star consisting of a centre
(`Sum.inr (a, none)`) and countably many spokes (`Sum.inr (a, some n)`). -/
abbrev StarIndex (A : Set ℝ) : Type := Bool ⊕ (↥A × Option ℕ)

/-- The part of the report's partition `D = {p,q} ⊔ ⨆_α C_α` (report §3.3)
containing a point: `none` for the anchor pair `{p,q}`, `some a` for `C_a`.
(`block` is Lean-internal vocabulary; the report says 分割の要素.) -/
def starBlock (A : Set ℝ) : StarIndex A → Option ↥A
  | Sum.inl _ => none
  | Sum.inr (a, _) => some a

theorem eq_inl_of_starBlock_eq_none {A : Set ℝ} {x : StarIndex A}
    (h : starBlock A x = none) : ∃ b, x = Sum.inl b := by
  rcases x with b | ⟨a, i⟩
  · exact ⟨b, rfl⟩
  · simp [starBlock] at h

theorem eq_inr_of_starBlock_eq_some {A : Set ℝ} {x : StarIndex A} {a : ↥A}
    (h : starBlock A x = some a) : ∃ i, x = Sum.inr (a, i) := by
  rcases x with b | ⟨a', i⟩
  · simp [starBlock] at h
  · simp only [starBlock, Option.some_inj] at h
    exact ⟨i, by rw [h]⟩

/-! ## The spoke lengths `s_n(α,t)` (report §3.3) -/

/-- The report's `s_n(α,t) = min(1, |t − a_α| + 1/(n+1))`, `n ∈ ℕ`
(report §3.3) — the indexing matches the report literally. -/
noncomputable def starSpoke (n : ℕ) (a t : ℝ) : ℝ := min 1 (|t - a| + 1 / ((n : ℝ) + 1))

theorem starSpoke_pos (n : ℕ) (a t : ℝ) : 0 < starSpoke n a t :=
  lt_min one_pos (by positivity)

theorem starSpoke_le_one (n : ℕ) (a t : ℝ) : starSpoke n a t ≤ 1 := min_le_left _ _

/-- Distance from the star centre: `0` for the centre itself, `s_n` for the
`n`-th spoke.  With this notation the whole star carries the star metric
`d(i,j) = σ i + σ j` for `i ≠ j` (report §3.3, rows 2–3 of the table). -/
noncomputable def starRadius (a t : ℝ) : Option ℕ → ℝ
  | none => 0
  | some n => starSpoke n a t

theorem starRadius_nonneg (a t : ℝ) : ∀ i, 0 ≤ starRadius a t i
  | none => le_rfl
  | some n => (starSpoke_pos n a t).le

theorem starRadius_le_one (a t : ℝ) : ∀ i, starRadius a t i ≤ 1
  | none => zero_le_one
  | some n => starSpoke_le_one n a t

theorem starRadius_pos_of_ne (a t : ℝ) {i j : Option ℕ} (h : i ≠ j) :
    0 < starRadius a t i + starRadius a t j := by
  match i, j with
  | none, none => exact absurd rfl h
  | none, some n => simpa [starRadius] using starSpoke_pos n a t
  | some n, none => simpa [starRadius] using starSpoke_pos n a t
  | some n, some m =>
      have h1 := starSpoke_pos n a t
      have h2 := starSpoke_pos m a t
      simp only [starRadius]
      linarith

/-! ## The star-type distance `d_t` (report §3.3, the distance table) -/

open Classical in
/-- The report's `d_t : D × D → [0,2]`.  Read off the §3.3 table:
`d_t(p,q) = 1 + t`; within the star at `a`, `d_t(i,j) = σ i + σ j` for
`i ≠ j` (which gives `s_n` between centre and spoke and `s_n + s_m` between
two distinct spokes); every pair from two different blocks has distance `1`.
Symmetry is immediate branch by branch (see `dStar_comm`). -/
noncomputable def dStar (A : Set ℝ) (t : ℝ) : StarIndex A → StarIndex A → ℝ
  | Sum.inl b, Sum.inl c => if b = c then 0 else 1 + t
  | Sum.inl _, Sum.inr _ => 1
  | Sum.inr _, Sum.inl _ => 1
  | Sum.inr (a, i), Sum.inr (b, j) =>
      if a = b then (if i = j then 0 else starRadius (a : ℝ) t i + starRadius (a : ℝ) t j)
      else 1

/-- The anchor pair carries the parameter: `d_t(p,q) = 1 + t` (report §3.3). -/
theorem dStar_anchor (A : Set ℝ) (t : ℝ) :
    dStar A t (Sum.inl true) (Sum.inl false) = 1 + t := by
  simp [dStar]

theorem dStar_of_block_ne {A : Set ℝ} {t : ℝ} {u v : StarIndex A}
    (h : starBlock A u ≠ starBlock A v) : dStar A t u v = 1 := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · exact absurd rfl h
  · simp [dStar]
  · simp [dStar]
  · have hne : a ≠ a' := by simpa [starBlock] using h
    simp [dStar, hne]

theorem dStar_self (A : Set ℝ) (t : ℝ) (u : StarIndex A) : dStar A t u u = 0 := by
  rcases u with b | ⟨a, i⟩ <;> simp [dStar]

theorem dStar_comm (A : Set ℝ) (t : ℝ) (u v : StarIndex A) :
    dStar A t u v = dStar A t v u := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · cases b <;> cases c <;> simp [dStar]
  · simp [dStar]
  · simp [dStar]
  · by_cases hab : a = a'
    · subst hab
      by_cases hij : i = j
      · subst hij; simp [dStar]
      · simp [dStar, hij, Ne.symm hij, add_comm]
    · simp [dStar, hab, Ne.symm hab]

theorem dStar_nonneg {A : Set ℝ} {t : ℝ} (ht : 0 ≤ t) (u v : StarIndex A) :
    0 ≤ dStar A t u v := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · simp only [dStar]; split_ifs <;> linarith
  · simp [dStar]
  · simp [dStar]
  · simp only [dStar]
    split_ifs
    · exact le_rfl
    · linarith [starRadius_nonneg (a : ℝ) t i, starRadius_nonneg (a : ℝ) t j]
    · norm_num

theorem dStar_le_two {A : Set ℝ} {t : ℝ} (ht : t ≤ 1) (u v : StarIndex A) :
    dStar A t u v ≤ 2 := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · simp only [dStar]; split_ifs <;> linarith
  · norm_num [dStar]
  · norm_num [dStar]
  · simp only [dStar]
    split_ifs
    · norm_num
    · linarith [starRadius_le_one (a : ℝ) t i, starRadius_le_one (a : ℝ) t j]
    · norm_num

/-- The star-metric triangle inequality in the abstract: if the points of a
set carry nonnegative "radii" `σ` and distinct points are joined through a
common centre (`d i j = σ i + σ j`), the triangle inequality holds.  This is
the content of report §3.3 case (a). -/
theorem star_dist_triangle {ι : Type*} [DecidableEq ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (i j k : ι) :
    (if i = k then 0 else σ i + σ k)
      ≤ (if i = j then 0 else σ i + σ j) + (if j = k then 0 else σ j + σ k) := by
  by_cases hik : i = k
  · rw [if_pos hik]
    have h1 := hσ i; have h2 := hσ j; have h3 := hσ k
    split_ifs <;> linarith
  · rw [if_neg hik]
    by_cases hij : i = j
    · have hjk : j ≠ k := by rw [← hij]; exact hik
      rw [if_pos hij, if_neg hjk, hij]
      linarith
    · rw [if_neg hij]
      by_cases hjk : j = k
      · rw [if_pos hjk, ← hjk]
        linarith
      · rw [if_neg hjk]
        linarith [hσ j]

/-- **(C1)** (report §3.3).  `d_t` is a metric on `D` for *every* `t ∈ [0,1]`
— including `t ∈ A`, where it merely fails to be compatible with the discrete
topology (that is (C3)). -/
theorem dStar_isMetricOn (A : Set ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsMetricOn (dStar A t) := by
  obtain ⟨ht0, ht1⟩ := ht
  refine ⟨dStar_self A t, ?_, dStar_comm A t, ?_⟩
  · -- `d_t u v = 0 → u = v`: every table entry is strictly positive off the
    -- diagonal (report §3.3, first paragraph).
    intro u v huv
    rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
    · by_cases h : b = c
      · rw [h]
      · rw [dStar, if_neg h] at huv; linarith
    · rw [dStar] at huv; linarith
    · rw [dStar] at huv; linarith
    · by_cases hab : a = a'
      · subst hab
        by_cases hij : i = j
        · rw [hij]
        · rw [dStar, if_pos rfl, if_neg hij] at huv
          linarith [starRadius_pos_of_ne (a : ℝ) t hij]
      · rw [dStar, if_neg hab] at huv; linarith
  · -- Triangle inequality: report §3.3 (C1) cases (a)–(c), organised by how
    -- the three points meet the partition.
    intro u v w
    by_cases huw : starBlock A u = starBlock A w
    · by_cases huv : starBlock A u = starBlock A v
      · -- (a): all three points lie in the same block.
        rcases u with b | ⟨a, i⟩
        · obtain ⟨c, rfl⟩ := eq_inl_of_starBlock_eq_none huv.symm
          obtain ⟨e, rfl⟩ := eq_inl_of_starBlock_eq_none huw.symm
          cases b <;> cases c <;> cases e <;> simp [dStar] <;> linarith
        · obtain ⟨j, rfl⟩ := eq_inr_of_starBlock_eq_some huv.symm
          obtain ⟨k, rfl⟩ := eq_inr_of_starBlock_eq_some huw.symm
          simpa [dStar] using
            star_dist_triangle (starRadius (a : ℝ) t) (starRadius_nonneg (a : ℝ) t) i j k
      · -- middle point outside the shared block: both legs have length 1.
        have hvw : starBlock A v ≠ starBlock A w := fun hh => huv (huw.trans hh.symm)
        rw [dStar_of_block_ne huv, dStar_of_block_ne hvw]
        linarith [dStar_le_two ht1 u w]
    · -- endpoints in different blocks: `d_t u w = 1` and at least one leg
      -- also has length 1.
      rw [dStar_of_block_ne huw]
      by_cases hv : starBlock A u = starBlock A v
      · have hvw : starBlock A v ≠ starBlock A w := fun hh => huw (hv.trans hh)
        rw [dStar_of_block_ne hvw]
        linarith [dStar_nonneg ht0 u v]
      · rw [dStar_of_block_ne hv]
        linarith [dStar_nonneg ht0 v w]

/-! ## Compatibility with the discrete topology (report §3.3, (C2)–(C3)) -/

/-- **(C2)** (report §3.3).  For `t ∈ A^∁ = [0,1] \ A` every point of `D` is
isolated, so `d_t` induces the discrete topology.  The isolating radii are the
report's `δ(u)`: `1` at the anchors, `s_n(a,t)` at a spoke, and
`min(1, |t − a|)` at a centre — the last positive exactly because `t ∉ A`. -/
theorem dStar_topology_eq_bot (A : Set ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htA : t ∉ A) : (dStar_isMetricOn A ht).topology = ⊥ := by
  obtain ⟨ht0, ht1⟩ := ht
  rw [IsMetricOn.topology_eq_bot_iff]
  rintro (b | ⟨a, i⟩)
  · -- anchors: δ(p) = δ(q) = 1
    refine ⟨1, one_pos, ?_⟩
    rintro (c | ⟨a', j⟩) hlt
    · by_cases h : c = b
      · rw [h]
      · rw [dStar, if_neg h] at hlt; linarith
    · rw [dStar] at hlt; linarith
  · match i with
    | some n =>
        -- spoke: δ(x_{a,n}) = s_n(a,t) > 0, independently of `t`
        refine ⟨starSpoke n (a : ℝ) t, starSpoke_pos n (a : ℝ) t, ?_⟩
        rintro (c | ⟨a', j⟩) hlt
        · rw [dStar] at hlt
          linarith [starSpoke_le_one n (a : ℝ) t]
        · by_cases hab : a' = a
          · subst hab
            by_cases hij : j = some n
            · rw [hij]
            · rw [dStar, if_pos rfl, if_neg hij] at hlt
              rw [show starRadius (a' : ℝ) t (some n) = starSpoke n (a' : ℝ) t from rfl] at hlt
              linarith [starRadius_nonneg (a' : ℝ) t j]
          · rw [dStar, if_neg hab] at hlt
            linarith [starSpoke_le_one n (a : ℝ) t]
    | none =>
        -- centre: δ(y_a) = min(1, |t − a|), positive since t ∉ A ∋ a
        have hta : t ≠ (a : ℝ) := fun h => htA (h ▸ a.2)
        have habs : 0 < |t - (a : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hta)
        refine ⟨min 1 |t - (a : ℝ)|, lt_min one_pos habs, ?_⟩
        rintro (c | ⟨a', j⟩) hlt
        · rw [dStar] at hlt
          linarith [min_le_left (1 : ℝ) |t - (a : ℝ)|]
        · by_cases hab : a' = a
          · subst hab
            match j with
            | none => rfl
            | some m =>
                rw [dStar, if_pos rfl, if_neg (by simp : (some m : Option ℕ) ≠ none)] at hlt
                simp only [starRadius, add_zero, starSpoke] at hlt
                have hmono : min 1 |t - (a' : ℝ)|
                    ≤ min 1 (|t - (a' : ℝ)| + 1 / ((m : ℝ) + 1)) :=
                  min_le_min le_rfl (le_add_of_nonneg_right (by positivity))
                linarith
          · rw [dStar, if_neg hab] at hlt
            linarith [min_le_left (1 : ℝ) |t - (a : ℝ)|]

/-- **(C3)** (report §3.3).  At a parameter `t ∈ A` the function `d_t` is
still a metric (that is (C1), proved for all `t ∈ [0,1]`), but the star centre
`y_t` is no longer isolated: `d_t(y_t, x_{t,n}) = min(1, 1/(n+1)) → 0`.  Hence
`d_t ∉ Met(D)`.  This boundary behaviour is what makes the image of the
parameter map closed (Issue #9). -/
theorem dStar_topology_ne_bot (A : Set ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htA : t ∈ A) : (dStar_isMetricOn A ht).topology ≠ ⊥ := by
  rw [Ne, IsMetricOn.topology_eq_bot_iff]
  push Not
  refine ⟨Sum.inr (⟨t, htA⟩, none), ?_⟩
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨Sum.inr (⟨t, htA⟩, some n), ?_, by simp⟩
  rw [dStar, if_pos rfl, if_neg (by simp : (some n : Option ℕ) ≠ none)]
  simp only [starRadius, add_zero, starSpoke, sub_self, abs_zero, zero_add]
  exact lt_of_le_of_lt (min_le_right _ _) hn

/-- The equivalence stated by report 補題 3.3: for the family `d_t` on
`D = StarIndex A`, membership in `Met(D)` characterises the parameter set
exactly, `d_t ∈ Met(D) ⟺ t ∈ A^∁ = [0,1] \ A`.

The left-hand side is literally `MetD (StarIndex A)`'s defining predicate, so
this says: each `d_t` with `t ∈ A^∁` is a metric on `D` *compatible with the
discrete topology* (no boundedness, no uniform discreteness), and no
parameter outside `A^∁` contributes to it.

This is the pointwise half of LEM-STAR-METRIC; the claim ID is carried by the
aggregate `lem_star_metric` below, which also pins `|D| = ℵ₁` and exposes the
whole family inside `MetD`. -/
theorem dStar_mem_MetD_iff (A : Set ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∃ h : IsMetricOn (dStar A t), h.topology = ⊥) ↔ t ∉ A := by
  constructor
  · rintro ⟨h, hbot⟩ htA
    exact dStar_topology_ne_bot A ht htA hbot
  · intro htA
    exact ⟨dStar_isMetricOn A ht, dStar_topology_eq_bot A ht htA⟩

/-- The parameter map `φ : A^∁ → Met(D)`, `t ↦ d_t`, of report §3.4, as a map
into the Lean type `MetD`.  Issue #9 turns this into the bi-Lipschitz
embedding with closed image. -/
noncomputable def starMet (A : Set ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (htA : t ∉ A) :
    MetD (StarIndex A) :=
  ⟨dStar A t, dStar_isMetricOn A ht, dStar_topology_eq_bot A ht htA⟩

@[simp] theorem starMet_coe (A : Set ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (htA : t ∉ A) :
    (starMet A ht htA).1 = dStar A t := rfl

/-! ## Cardinality of `D` (report §3.3) -/

/-- `|D| = 2 + ℵ₁ · ℵ₀ = ℵ₁` (report §3.3). -/
theorem card_starIndex {A : Set ℝ} (hA : #(↥A) = aleph 1) : #(StarIndex A) = aleph 1 := by
  have hℵ : (ℵ₀ : Cardinal) ≤ aleph 1 := aleph0_le_aleph 1
  have hopt : #(Option ℕ) = (ℵ₀ : Cardinal) := by
    rw [mk_option, mk_nat]
    exact add_eq_left le_rfl one_le_aleph0
  have hprod : #(↥A × Option ℕ) = aleph 1 := by
    rw [mk_prod, lift_id, lift_id, hA, hopt, mul_eq_max hℵ le_rfl, max_eq_left hℵ]
  have h2 : (2 : Cardinal) ≤ aleph 1 := le_trans ofNat_lt_aleph0.le hℵ
  show #(Bool ⊕ (↥A × Option ℕ)) = aleph 1
  rw [mk_sum, lift_id, lift_id, mk_bool, hprod]
  exact add_eq_right hℵ h2

/-! ## LEM-STAR-METRIC -/

/-- **LEM-STAR-METRIC** (report 補題 3.3, §3.2–§3.4).

Given `A ⊆ ℝ` with `|A| = ℵ₁`, the star construction produces a discrete
index set `D = StarIndex A` of cardinality `ℵ₁` together with the family
`(d_t)_{t ∈ [0,1]}` such that

1. `|D| = ℵ₁` — the source's hypothesis on the underlying discrete space
   (report §3.2, §3.3);
2. every `d_t`, `t ∈ [0,1]`, is a metric on `D` — (C1), report §3.3;
3. `d_t` induces the discrete topology **iff** `t ∉ A` — (C2) together with
   (C3), report §3.3.  Note this is an iff: the failure at `t ∈ A` is
   part of the claim, since it is what makes the image closed in Issue #9;
4. consequently the parameter map `φ : A^∁ = [0,1] \ A → Met(D)`, `t ↦ d_t`,
   exists as a genuine map into `MetD (StarIndex A)`, with `φ t` carried by
   `d_t` — report §3.4.

Clauses 1–4 together are the content of report 補題 3.3 (the family exists,
with `d_t ∈ Met(D) ⟺ t ∈ A^∁`), with clause 4 exposing the parameter map.
`MetD` is the unweakened `Met(D)` of `Conj51/MetD.lean` — no boundedness and
no uniform discreteness is assumed anywhere.

The component lemmas (`card_starIndex`, `dStar_isMetricOn`,
`dStar_mem_MetD_iff`, `dStar_topology_eq_bot`, `dStar_topology_ne_bot`,
`starMet`) remain available individually; Issue #9 consumes those directly. -/
theorem lem_star_metric {A : Set ℝ} (hA : #(↥A) = aleph 1) :
    #(StarIndex A) = aleph 1 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, IsMetricOn (dStar A t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
        ((∃ h : IsMetricOn (dStar A t), h.topology = ⊥) ↔ t ∉ A)) ∧
    ∃ φ : ↥(Set.Icc (0 : ℝ) 1 \ A) → MetD (StarIndex A),
      ∀ t : ↥(Set.Icc (0 : ℝ) 1 \ A), (φ t).1 = dStar A (t : ℝ) :=
  ⟨card_starIndex hA,
    fun _ ht => dStar_isMetricOn A ht,
    fun _ ht => dStar_mem_MetD_iff A ht,
    ⟨fun t => starMet A t.2.1 t.2.2, fun _ => rfl⟩⟩

/-! ## Pointwise Lipschitz estimates (report §3.4, pair-by-pair half of (C4))

These are the quantitative estimates the bi-Lipschitz embedding is assembled
from.  Taking the supremum over pairs turns `dStar_sub_le` into the upper
bound `ρ(d_t, d_s) ≤ 2|t−s|` and `dStar_anchor_sub` into the lower bound
`|t−s| ≤ ρ(d_t, d_s)`; that supremum-level statement is LEM-CLOSED-IMAGE
(Issue #9). -/

theorem starSpoke_sub_le (n : ℕ) (a t s : ℝ) :
    |starSpoke n a t - starSpoke n a s| ≤ |t - s| := by
  have hinner : |(|t - a| + 1 / ((n : ℝ) + 1)) - (|s - a| + 1 / ((n : ℝ) + 1))| ≤ |t - s| := by
    rw [show (|t - a| + 1 / ((n : ℝ) + 1)) - (|s - a| + 1 / ((n : ℝ) + 1))
          = |t - a| - |s - a| by ring]
    have h := abs_abs_sub_abs_le_abs_sub (t - a) (s - a)
    rwa [show (t - a) - (s - a) = t - s by ring] at h
  refine (abs_min_sub_min_le_max (1 : ℝ) (|t - a| + 1 / ((n : ℝ) + 1)) (1 : ℝ)
    (|s - a| + 1 / ((n : ℝ) + 1))).trans (max_le ?_ hinner)
  simp

theorem starRadius_sub_le (a t s : ℝ) : ∀ i, |starRadius a t i - starRadius a s i| ≤ |t - s|
  | none => by simp [starRadius]
  | some n => starSpoke_sub_le n a t s

/-- Every pair-value of the family is `2`-Lipschitz in the parameter
(report §3.4, upper bound). -/
theorem dStar_sub_le (A : Set ℝ) (t s : ℝ) (u v : StarIndex A) :
    |dStar A t u v - dStar A s u v| ≤ 2 * |t - s| := by
  have habs := abs_nonneg (t - s)
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · simp only [dStar]
    split_ifs
    · simp
    · rw [show (1 + t) - (1 + s) = t - s by ring]; linarith
  · simp only [dStar, sub_self, abs_zero]; linarith
  · simp only [dStar, sub_self, abs_zero]; linarith
  · simp only [dStar]
    split_ifs
    · simp
    · -- split the two-term difference through the intermediate point
      -- `σ_s i + σ_t j` and apply the pointwise estimate to each summand
      have h1 := starRadius_sub_le (a : ℝ) t s i
      have h2 := starRadius_sub_le (a : ℝ) t s j
      have hchain := abs_sub_le
        (starRadius (a : ℝ) t i + starRadius (a : ℝ) t j)
        (starRadius (a : ℝ) s i + starRadius (a : ℝ) t j)
        (starRadius (a : ℝ) s i + starRadius (a : ℝ) s j)
      rw [show (starRadius (a : ℝ) t i + starRadius (a : ℝ) t j)
              - (starRadius (a : ℝ) s i + starRadius (a : ℝ) t j)
            = starRadius (a : ℝ) t i - starRadius (a : ℝ) s i by ring,
        show (starRadius (a : ℝ) s i + starRadius (a : ℝ) t j)
              - (starRadius (a : ℝ) s i + starRadius (a : ℝ) s j)
            = starRadius (a : ℝ) t j - starRadius (a : ℝ) s j by ring] at hchain
      linarith
    · simp only [sub_self, abs_zero]; linarith

/-- The anchor pair recovers the parameter exactly (report §3.4, lower
bound). -/
theorem dStar_anchor_sub (A : Set ℝ) (t s : ℝ) :
    |dStar A t (Sum.inl true) (Sum.inl false) - dStar A s (Sum.inl true) (Sum.inl false)|
      = |t - s| := by
  rw [dStar_anchor, dStar_anchor, show (1 + t) - (1 + s) = t - s by ring]
