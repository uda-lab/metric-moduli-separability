-- Ext.BoundedCoding
--
-- Layer 1 of the Ishiki-extension package (Issue #47, sub-issue #51): the
-- bounded star-metric coding on a discrete carrier, and the exact pullback
-- identity that carries the descriptive-set obstruction.
--
-- Mathematical source of truth: the audited draft as recorded in
-- `notes/ishiki-extension-audit.md` §4 (Lemma 3.1, verdict PASS) and §5
-- (Lemma 3.2, verdict PASS), together with the corresponding Issue #46
-- comment.  Nothing here uses an analytic/coanalytic pointclass: the pullback
-- statement below is a plain equality of sets, which is exactly why it is
-- provable while the ambient pointclass convention of audit §1 is still open.
--
-- Setting.  A bad parameter set `S ⊆ [0,1]`, carrier
--
--     D = {p,q} ⊔ ⨆_{a ∈ S} ( {b_a} ⊔ {c_{a,n} : n ∈ ℕ} ),
--
-- spoke lengths `l_n(a,t) = |t − a| + 2^{-n}`, and for `t ∈ [0,1]`
--
--     d_t(p,q) = 1 + t,
--     d_t(b_a, c_{a,n}) = l_n(a,t),   d_t(c_{a,n}, c_{a,m}) = l_n + l_m (n ≠ m),
--     d_t(u,v) = 4                    whenever u, v lie in different blocks.
--
-- The draft indexes the stars by ordinals `α < ω₁` through an injective
-- enumeration `α ↦ w_α` of `S`; since that enumeration is a bijection onto
-- `S`, indexing the stars by `S` itself is the same construction up to
-- relabelling (the relabelling reduction is already stated once in
-- `Conj51/Relabel.lean`).  So `w_a = a` here.
--
-- Index conventions relative to the draft:
--   * draft `p, q`        ↦ `Sum.inl true`, `Sum.inl false`
--   * draft `b_α`         ↦ `Sum.inr (a, none)`
--   * draft `c_{α,n}`     ↦ `Sum.inr (a, some n)`
--   * draft `l_n(α,t)`    ↦ `spokeLen n a t = |t − a| + (1/2)^n`
--
-- What is proved here:
--   `dExt_isMetricOn`        — each `d_t`, `t ∈ [0,1]`, is a metric (audit §4).
--   `dExt_le_four`           — each `d_t` is bounded by `4` (audit §4).
--   `dExt_isCompatible_iff`  — `d_t` induces the discrete topology **iff**
--                              `t ∉ S` (audit §4; both directions).
--   `dist_phiFull_le`        — `ρ(d_s,d_t) ≤ 2|s−t|` (audit §5, upper bound).
--   `abs_sub_le_dist_phiFull`— `|s−t| ≤ ρ(d_s,d_t)` (audit §5, anchor readout).
--   `lipschitzWith_phiFull`  — `Φ_full : [0,1] → BCPM(D)` is 2-Lipschitz.
--   `preimage_BMet_phiFull`  — the pullback identity `Φ_full⁻¹(BMet(D))`
--                              `= [0,1] \ S` (audit §5, recommended
--                              strengthening).
--   `isClosed_image_phiFull` — the image `Φ_full([0,1] \ S)` is closed in
--                              `BMet(D)` (audit §5, closed image).
--   `card_extIndex`          — `|D| = ℵ₁` when `|S| = ℵ₁`.
--   `bounded_star_coding`    — the four Layer 1 clauses in one statement.
--
-- The Conjecture 5.1 development in `Conj51/` is left untouched; only the
-- generic base module `Conj51/MetD.lean` (`IsMetricOn` and its discreteness
-- criterion) is imported, so that "compatible with the discrete topology"
-- has a single definition across the repository.  The star-shaped triangle
-- inequality is restated here rather than imported from
-- `Conj51/MetricConstruction.lean`, to keep this development independent of
-- the Conjecture 5.1 claim modules.
--
-- Status: sorry-free.

import Mathlib
import IshikiConj51.Conj51.MetD
import IshikiConj51.Ext.BddPMet

open Cardinal

namespace IshikiExt

/-! ## The carrier `D` -/

/-- The carrier of the coding: two anchor points (`Sum.inl`), and for every
`a ∈ S` a star consisting of a centre (`Sum.inr (a, none)`) and countably many
spokes (`Sum.inr (a, some n)`). -/
abbrev ExtIndex (S : Set ℝ) : Type := Bool ⊕ (↥S × Option ℕ)

/-- The block of the partition `D = {p,q} ⊔ ⨆_a C_a` containing a point:
`none` for the anchor pair, `some a` for the star at `a`. -/
def extBlock (S : Set ℝ) : ExtIndex S → Option ↥S
  | Sum.inl _ => none
  | Sum.inr (a, _) => some a

theorem eq_inl_of_extBlock_eq_none {S : Set ℝ} {x : ExtIndex S}
    (h : extBlock S x = none) : ∃ b, x = Sum.inl b := by
  rcases x with b | ⟨a, i⟩
  · exact ⟨b, rfl⟩
  · simp [extBlock] at h

theorem eq_inr_of_extBlock_eq_some {S : Set ℝ} {x : ExtIndex S} {a : ↥S}
    (h : extBlock S x = some a) : ∃ i, x = Sum.inr (a, i) := by
  rcases x with b | ⟨a', i⟩
  · simp [extBlock] at h
  · simp only [extBlock, Option.some_inj] at h
    exact ⟨i, by rw [h]⟩

/-! ## The spoke lengths `l_n(a,t) = |t − a| + 2^{-n}` -/

/-- The draft's `l_n(α,t) = |t − w_α| + 2^{-n}`. -/
noncomputable def spokeLen (n : ℕ) (a t : ℝ) : ℝ := |t - a| + (1 / 2 : ℝ) ^ n

theorem half_pow_pos (n : ℕ) : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity

theorem half_pow_le_one (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      linarith [half_pow_pos k]

theorem spokeLen_pos (n : ℕ) (a t : ℝ) : 0 < spokeLen n a t := by
  have := half_pow_pos n
  have := abs_nonneg (t - a)
  simp only [spokeLen]
  linarith

/-- `2^{-n} ≤ l_n(a,t)`: the spoke lengths of a fixed star are bounded below
by the corresponding power of two, uniformly in the parameter. -/
theorem half_pow_le_spokeLen (n : ℕ) (a t : ℝ) : (1 / 2 : ℝ) ^ n ≤ spokeLen n a t := by
  simp only [spokeLen]
  linarith [abs_nonneg (t - a)]

/-- `|t − a| ≤ l_n(a,t)`: the distance from a star centre to any of its spokes
is at least the defect `|t − a|`. -/
theorem abs_sub_le_spokeLen (n : ℕ) (a t : ℝ) : |t - a| ≤ spokeLen n a t := by
  simp only [spokeLen]
  linarith [half_pow_pos n]

theorem abs_sub_le_one_of_mem_Icc {t a : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : |t - a| ≤ 1 := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨ha0, ha1⟩ := ha
  rw [abs_le]
  constructor <;> linarith

/-- `0 < l_n ≤ 2` on the relevant parameter range (audit §4). -/
theorem spokeLen_le_two {t a : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) : spokeLen n a t ≤ 2 := by
  simp only [spokeLen]
  linarith [abs_sub_le_one_of_mem_Icc ht ha, half_pow_le_one n]

/-- Distance from the star centre: `0` for the centre itself, `l_n` for the
`n`-th spoke.  With this notation the whole star carries the star metric
`d(i,j) = σ i + σ j` for `i ≠ j`. -/
noncomputable def extRadius (a t : ℝ) : Option ℕ → ℝ
  | none => 0
  | some n => spokeLen n a t

theorem extRadius_nonneg (a t : ℝ) : ∀ i, 0 ≤ extRadius a t i
  | none => le_rfl
  | some n => (spokeLen_pos n a t).le

theorem extRadius_le_two {t a : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i, extRadius a t i ≤ 2
  | none => by norm_num [extRadius]
  | some n => spokeLen_le_two ht ha n

theorem extRadius_pos_of_ne (a t : ℝ) {i j : Option ℕ} (h : i ≠ j) :
    0 < extRadius a t i + extRadius a t j := by
  match i, j with
  | none, none => exact absurd rfl h
  | none, some n => simpa [extRadius] using spokeLen_pos n a t
  | some n, none => simpa [extRadius] using spokeLen_pos n a t
  | some n, some m =>
      have h1 := spokeLen_pos n a t
      have h2 := spokeLen_pos m a t
      simp only [extRadius]
      linarith

/-! ## The bounded star metric `d_t` -/

open Classical in
/-- The draft's `d_t : D × D → [0,4]`, read off the distance table of audit
§4: `d_t(p,q) = 1 + t`; within the star at `a`, `d_t(i,j) = σ i + σ j` for
`i ≠ j`; every pair from two different blocks has distance `4`. -/
noncomputable def dExt (S : Set ℝ) (t : ℝ) : ExtIndex S → ExtIndex S → ℝ
  | Sum.inl b, Sum.inl c => if b = c then 0 else 1 + t
  | Sum.inl _, Sum.inr _ => 4
  | Sum.inr _, Sum.inl _ => 4
  | Sum.inr (a, i), Sum.inr (b, j) =>
      if a = b then (if i = j then 0 else extRadius (a : ℝ) t i + extRadius (a : ℝ) t j)
      else 4

/-- The anchor pair carries the parameter: `d_t(p,q) = 1 + t`. -/
theorem dExt_anchor (S : Set ℝ) (t : ℝ) :
    dExt S t (Sum.inl true) (Sum.inl false) = 1 + t := by
  simp [dExt]

theorem dExt_of_block_ne {S : Set ℝ} {t : ℝ} {u v : ExtIndex S}
    (h : extBlock S u ≠ extBlock S v) : dExt S t u v = 4 := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · exact absurd rfl h
  · simp [dExt]
  · simp [dExt]
  · have hne : a ≠ a' := by simpa [extBlock] using h
    simp [dExt, hne]

theorem dExt_self (S : Set ℝ) (t : ℝ) (u : ExtIndex S) : dExt S t u u = 0 := by
  rcases u with b | ⟨a, i⟩ <;> simp [dExt]

theorem dExt_comm (S : Set ℝ) (t : ℝ) (u v : ExtIndex S) :
    dExt S t u v = dExt S t v u := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · cases b <;> cases c <;> simp [dExt]
  · simp [dExt]
  · simp [dExt]
  · by_cases hab : a = a'
    · subst hab
      by_cases hij : i = j
      · subst hij; simp [dExt]
      · simp [dExt, hij, Ne.symm hij, add_comm]
    · simp [dExt, hab, Ne.symm hab]

theorem dExt_nonneg {S : Set ℝ} {t : ℝ} (ht0 : 0 ≤ t) (u v : ExtIndex S) :
    0 ≤ dExt S t u v := by
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · simp only [dExt]; split_ifs <;> linarith
  · simp [dExt]
  · simp [dExt]
  · simp only [dExt]
    split_ifs
    · exact le_rfl
    · linarith [extRadius_nonneg (a : ℝ) t i, extRadius_nonneg (a : ℝ) t j]
    · norm_num

/-- **Boundedness** (audit §4): `d_t` takes values in `[0,4]`. -/
theorem dExt_le_four {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u v : ExtIndex S) : dExt S t u v ≤ 4 := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · simp only [dExt]; split_ifs <;> linarith
  · norm_num [dExt]
  · norm_num [dExt]
  · simp only [dExt]
    split_ifs with hab hij
    · norm_num
    · subst hab
      have hmem := hS a.2
      linarith [extRadius_le_two ⟨ht0, ht1⟩ hmem i, extRadius_le_two ⟨ht0, ht1⟩ hmem j]
    · norm_num

/-- The star-shaped triangle inequality in the abstract: if the points of a
set carry nonnegative radii `σ` and distinct points are joined through a common
centre (`d i j = σ i + σ j`), then the triangle inequality holds.  This is the
within-a-star case of audit §4.

(Restated here rather than imported from `Conj51/MetricConstruction.lean`, so
that the extension development does not depend on the Conjecture 5.1 claim
modules.) -/
theorem starLike_triangle {ι : Type*} [DecidableEq ι] (σ : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i)
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

/-- **Metricity** (audit §4).  `d_t` is a metric on `D` for *every* `t ∈ [0,1]`
— including `t ∈ S`, where it merely fails to be compatible with the discrete
topology. -/
theorem dExt_isMetricOn {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsMetricOn (dExt S t) := by
  obtain ⟨ht0, ht1⟩ := ht
  refine ⟨dExt_self S t, ?_, dExt_comm S t, ?_⟩
  · -- every table entry is strictly positive off the diagonal
    intro u v huv
    rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
    · by_cases h : b = c
      · rw [h]
      · rw [dExt, if_neg h] at huv; linarith
    · rw [dExt] at huv; linarith
    · rw [dExt] at huv; linarith
    · by_cases hab : a = a'
      · subst hab
        by_cases hij : i = j
        · rw [hij]
        · rw [dExt, if_pos rfl, if_neg hij] at huv
          linarith [extRadius_pos_of_ne (a : ℝ) t hij]
      · rw [dExt, if_neg hab] at huv; linarith
  · -- triangle inequality, organised by how the three points meet the partition
    intro u v w
    by_cases huw : extBlock S u = extBlock S w
    · by_cases huv : extBlock S u = extBlock S v
      · -- all three points in the same block
        rcases u with b | ⟨a, i⟩
        · obtain ⟨c, rfl⟩ := eq_inl_of_extBlock_eq_none huv.symm
          obtain ⟨e, rfl⟩ := eq_inl_of_extBlock_eq_none huw.symm
          cases b <;> cases c <;> cases e <;> simp [dExt] <;> linarith
        · obtain ⟨j, rfl⟩ := eq_inr_of_extBlock_eq_some huv.symm
          obtain ⟨k, rfl⟩ := eq_inr_of_extBlock_eq_some huw.symm
          simpa [dExt] using
            starLike_triangle (extRadius (a : ℝ) t) (extRadius_nonneg (a : ℝ) t) i j k
      · -- middle point outside the shared block: both legs have length 4
        have hvw : extBlock S v ≠ extBlock S w := fun hh => huv (huw.trans hh.symm)
        rw [dExt_of_block_ne huv, dExt_of_block_ne hvw]
        linarith [dExt_le_four hS ⟨ht0, ht1⟩ u w]
    · -- endpoints in different blocks: `d_t u w = 4` and at least one leg is 4
      rw [dExt_of_block_ne huw]
      by_cases hv : extBlock S u = extBlock S v
      · have hvw : extBlock S v ≠ extBlock S w := fun hh => huw (hv.trans hh)
        rw [dExt_of_block_ne hvw]
        linarith [dExt_nonneg ht0 u v]
      · rw [dExt_of_block_ne hv]
        linarith [dExt_nonneg ht0 v w]

theorem dExt_isBddPMetOn {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsBddPMetOn (dExt S t) :=
  IsMetricOn.toIsBddPMetOn (dExt_isMetricOn hS ht) (dExt_le_four hS ht)

/-! ## Compatibility with the discrete topology -/

/-- **Compatibility, positive half** (audit §4).  For `t ∈ [0,1] \ S` every
point of `D` is isolated, so `d_t` induces the discrete topology.  The
isolating radii are `1` at the anchors, `l_n(a,t)` at the `n`-th spoke of the
star at `a`, and `|t − a|` at the centre of that star — the last positive
exactly because `t ∉ S ∋ a`. -/
theorem dExt_topology_eq_bot {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htS : t ∉ S) :
    (dExt_isMetricOn hS ht).topology = ⊥ := by
  obtain ⟨ht0, ht1⟩ := ht
  rw [IsMetricOn.topology_eq_bot_iff]
  rintro (b | ⟨a, i⟩)
  · -- anchors: isolating radius 1
    refine ⟨1, one_pos, ?_⟩
    rintro (c | ⟨a', j⟩) hlt
    · by_cases h : c = b
      · rw [h]
      · rw [dExt, if_neg h] at hlt; linarith
    · rw [dExt] at hlt; linarith
  · have hmem := hS a.2
    match i with
    | some n =>
        -- spoke: isolating radius l_n(a,t) > 0, independently of `t`
        refine ⟨spokeLen n (a : ℝ) t, spokeLen_pos n (a : ℝ) t, ?_⟩
        rintro (c | ⟨a', j⟩) hlt
        · rw [dExt] at hlt
          linarith [spokeLen_le_two ⟨ht0, ht1⟩ hmem n]
        · by_cases hab : a' = a
          · subst hab
            by_cases hij : j = some n
            · rw [hij]
            · rw [dExt, if_pos rfl, if_neg hij] at hlt
              rw [show extRadius (a' : ℝ) t (some n) = spokeLen n (a' : ℝ) t from rfl] at hlt
              linarith [extRadius_nonneg (a' : ℝ) t j]
          · rw [dExt, if_neg hab] at hlt
            linarith [spokeLen_le_two ⟨ht0, ht1⟩ hmem n]
    | none =>
        -- centre: isolating radius |t − a|, positive since t ∉ S ∋ a
        have hta : t ≠ (a : ℝ) := fun h => htS (h ▸ a.2)
        have habs : 0 < |t - (a : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hta)
        refine ⟨|t - (a : ℝ)|, habs, ?_⟩
        rintro (c | ⟨a', j⟩) hlt
        · rw [dExt] at hlt
          linarith [abs_sub_le_one_of_mem_Icc ⟨ht0, ht1⟩ hmem]
        · by_cases hab : a' = a
          · subst hab
            match j with
            | none => rfl
            | some m =>
                rw [dExt, if_pos rfl, if_neg (by simp : (some m : Option ℕ) ≠ none)] at hlt
                simp only [extRadius, add_zero] at hlt
                linarith [abs_sub_le_spokeLen m (a' : ℝ) t]
          · rw [dExt, if_neg hab] at hlt
            linarith [abs_sub_le_one_of_mem_Icc ⟨ht0, ht1⟩ hmem]

/-- **Compatibility, negative half** (audit §4).  At a parameter `t ∈ S` the
function `d_t` is still a metric, but the centre of the star at `t` is no
longer isolated: `d_t(b_t, c_{t,n}) = 2^{-n} → 0`. -/
theorem dExt_topology_ne_bot {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htS : t ∈ S) :
    (dExt_isMetricOn hS ht).topology ≠ ⊥ := by
  intro hbot
  rw [IsMetricOn.topology_eq_bot_iff] at hbot
  obtain ⟨ε, hε, hall⟩ := hbot (Sum.inr (⟨t, htS⟩, none))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hne : (Sum.inr (⟨t, htS⟩, some n) : ExtIndex S) ≠ Sum.inr (⟨t, htS⟩, none) := by simp
  refine hne (hall _ ?_)
  rw [dExt, if_pos rfl, if_neg (by simp : (some n : Option ℕ) ≠ none)]
  simp only [extRadius, add_zero, spokeLen, sub_self, abs_zero, zero_add]
  exact hn

/-! ## The full parameter map `Φ_full : [0,1] → BCPM(D)` -/

/-- The parameter interval `[0,1]`, as a subtype of `ℝ` carrying the subspace
metric. -/
abbrev UnitParam : Type := ↥(Set.Icc (0 : ℝ) 1)

/-- The draft's `Φ_full : [0,1] → BCPM(D)`, `t ↦ d_t` (audit §5).  It is
defined on *all* of `[0,1]`, not only on `[0,1] \ S`; that is what makes the
pullback identity below available. -/
noncomputable def phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) (t : UnitParam) :
    BddPMet (ExtIndex S) :=
  ⟨dExt S (t : ℝ), dExt_isBddPMetOn hS t.2⟩

@[simp] theorem phiFull_coe (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) (t : UnitParam) :
    (phiFull S hS t).1 = dExt S (t : ℝ) := rfl

/-! ## The Lipschitz estimates (audit §5) -/

theorem spokeLen_sub_le (n : ℕ) (a t s : ℝ) :
    |spokeLen n a t - spokeLen n a s| ≤ |t - s| := by
  simp only [spokeLen]
  rw [show (|t - a| + (1 / 2 : ℝ) ^ n) - (|s - a| + (1 / 2 : ℝ) ^ n)
        = |t - a| - |s - a| by ring]
  have h := abs_abs_sub_abs_le_abs_sub (t - a) (s - a)
  rwa [show (t - a) - (s - a) = t - s by ring] at h

theorem extRadius_sub_le (a t s : ℝ) : ∀ i, |extRadius a t i - extRadius a s i| ≤ |t - s|
  | none => by simp [extRadius]
  | some n => spokeLen_sub_le n a t s

/-- Every pair-value of the family is `2`-Lipschitz in the parameter
(audit §5, upper bound). -/
theorem dExt_sub_le (S : Set ℝ) (t s : ℝ) (u v : ExtIndex S) :
    |dExt S t u v - dExt S s u v| ≤ 2 * |t - s| := by
  have habs := abs_nonneg (t - s)
  rcases u with b | ⟨a, i⟩ <;> rcases v with c | ⟨a', j⟩
  · simp only [dExt]
    split_ifs
    · simp
    · rw [show (1 + t) - (1 + s) = t - s by ring]; linarith
  · simp only [dExt, sub_self, abs_zero]; linarith
  · simp only [dExt, sub_self, abs_zero]; linarith
  · simp only [dExt]
    split_ifs
    · simp
    · -- split the two-term difference through the intermediate value
      have h1 := extRadius_sub_le (a : ℝ) t s i
      have h2 := extRadius_sub_le (a : ℝ) t s j
      have hchain := abs_sub_le
        (extRadius (a : ℝ) t i + extRadius (a : ℝ) t j)
        (extRadius (a : ℝ) s i + extRadius (a : ℝ) t j)
        (extRadius (a : ℝ) s i + extRadius (a : ℝ) s j)
      rw [show (extRadius (a : ℝ) t i + extRadius (a : ℝ) t j)
              - (extRadius (a : ℝ) s i + extRadius (a : ℝ) t j)
            = extRadius (a : ℝ) t i - extRadius (a : ℝ) s i by ring,
        show (extRadius (a : ℝ) s i + extRadius (a : ℝ) t j)
              - (extRadius (a : ℝ) s i + extRadius (a : ℝ) s j)
            = extRadius (a : ℝ) t j - extRadius (a : ℝ) s j by ring] at hchain
      linarith
    · simp only [sub_self, abs_zero]; linarith

/-- The anchor pair recovers the parameter exactly (audit §5, lower bound). -/
theorem dExt_anchor_sub (S : Set ℝ) (t s : ℝ) :
    |dExt S t (Sum.inl true) (Sum.inl false) - dExt S s (Sum.inl true) (Sum.inl false)|
      = |t - s| := by
  rw [dExt_anchor, dExt_anchor, show (1 + t) - (1 + s) = t - s by ring]

/-- **Upper Lipschitz bound** (audit §5): `ρ(d_t, d_s) ≤ 2|t − s|`. -/
theorem dist_phiFull_le (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) (t s : UnitParam) :
    dist (phiFull S hS t) (phiFull S hS s) ≤ 2 * |(t : ℝ) - (s : ℝ)| :=
  BddPMet.dist_le (by positivity) fun u v => dExt_sub_le S (t : ℝ) (s : ℝ) u v

/-- **Lower bound** (audit §5): evaluation at the anchor pair gives
`|t − s| ≤ ρ(d_t, d_s)`.  Together with `dist_phiFull_le` this makes the
restriction of `Φ_full` to `[0,1] \ S` bi-Lipschitz. -/
theorem abs_sub_le_dist_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) (t s : UnitParam) :
    |(t : ℝ) - (s : ℝ)| ≤ dist (phiFull S hS t) (phiFull S hS s) := by
  calc |(t : ℝ) - (s : ℝ)|
      = |dExt S (t : ℝ) (Sum.inl true) (Sum.inl false)
          - dExt S (s : ℝ) (Sum.inl true) (Sum.inl false)| :=
        (dExt_anchor_sub S (t : ℝ) (s : ℝ)).symm
    _ ≤ dist (phiFull S hS t) (phiFull S hS s) :=
        BddPMet.le_dist (phiFull S hS t) (phiFull S hS s) (Sum.inl true) (Sum.inl false)

/-- **`Φ_full` is 2-Lipschitz on all of `[0,1]`** (audit §5). -/
theorem lipschitzWith_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    LipschitzWith 2 (phiFull S hS) :=
  LipschitzWith.of_dist_le_mul fun t s => by
    rw [Subtype.dist_eq, Real.dist_eq]
    simpa using dist_phiFull_le S hS t s

theorem injective_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    Function.Injective (phiFull S hS) := by
  intro t s h
  have hle := abs_sub_le_dist_phiFull S hS t s
  rw [h, dist_self] at hle
  have : (t : ℝ) - (s : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  exact Subtype.ext (by linarith)

/-! ## The pullback identity (audit §5, recommended strengthening) -/

/-- `d_t` is compatible with the discrete topology **iff** `t ∉ S`
(audit §4).  This is the pointwise form of the pullback identity. -/
theorem dExt_isCompatible_iff (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) (t : UnitParam) :
    IsCompatible (phiFull S hS t) ↔ (t : ℝ) ∉ S := by
  constructor
  · rintro ⟨h, hbot⟩ htS
    exact dExt_topology_ne_bot hS t.2 htS hbot
  · intro htS
    exact ⟨dExt_isMetricOn hS t.2, dExt_topology_eq_bot hS t.2 htS⟩

/-- **The pullback identity** (audit §5):
`Φ_full⁻¹(BMet(D)) = {t ∈ [0,1] : t ∉ S}`, as an equality of subsets of the
parameter interval.  No descriptive-set-theoretic notion appears; this is the
set equality that the Theorem 3.3 obstruction is applied to once the ambient
pointclass convention is fixed. -/
theorem preimage_BMet_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    phiFull S hS ⁻¹' BMet (ExtIndex S) = {t : UnitParam | (t : ℝ) ∉ S} := by
  ext t
  simpa [BMet] using dExt_isCompatible_iff S hS t

/-- The pullback identity in the draft's literal form
`Φ_full⁻¹(BMet(D)) = [0,1] \ S`, obtained by pushing the subtype forward into
`ℝ`. -/
theorem image_preimage_BMet_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    Subtype.val '' (phiFull S hS ⁻¹' BMet (ExtIndex S)) = Set.Icc (0 : ℝ) 1 \ S := by
  rw [preimage_BMet_phiFull]
  ext x
  constructor
  · rintro ⟨t, htS, rfl⟩
    exact ⟨t.2, htS⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨⟨x, hx1⟩, hx2, rfl⟩

/-! ## Closed image (audit §5) -/

/-- `Φ_full` has compact, hence closed, range in the ambient `BCPM(D)`:
`[0,1]` is compact and `Φ_full` is continuous. -/
theorem isClosed_range_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    IsClosed (Set.range (phiFull S hS)) :=
  (isCompact_range (lipschitzWith_phiFull S hS).continuous).isClosed

/-- The image of the good parameters is exactly the part of the range that is
compatible — a restatement of the pullback identity at the level of images. -/
theorem image_compl_eq_range_inter (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    phiFull S hS '' {t : UnitParam | (t : ℝ) ∉ S}
      = Set.range (phiFull S hS) ∩ BMet (ExtIndex S) := by
  ext d
  constructor
  · rintro ⟨t, htS, rfl⟩
    exact ⟨⟨t, rfl⟩, (dExt_isCompatible_iff S hS t).mpr htS⟩
  · rintro ⟨⟨t, rfl⟩, hd⟩
    exact ⟨t, (dExt_isCompatible_iff S hS t).mp hd, rfl⟩

/-- **Closed image** (audit §5): `Φ_full([0,1] \ S)` is closed in `BMet(D)`
with its subspace topology. -/
theorem isClosed_image_phiFull (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    IsClosed (Subtype.val ⁻¹' (phiFull S hS '' {t : UnitParam | (t : ℝ) ∉ S}) :
      Set ↥(BMet (ExtIndex S))) := by
  rw [image_compl_eq_range_inter]
  have hpre : (Subtype.val ⁻¹' (Set.range (phiFull S hS) ∩ BMet (ExtIndex S)) :
      Set ↥(BMet (ExtIndex S))) = Subtype.val ⁻¹' Set.range (phiFull S hS) := by
    ext d
    simp
  rw [hpre]
  exact (isClosed_range_phiFull S hS).preimage continuous_subtype_val

/-! ## Cardinality of the carrier -/

/-- `|D| = 2 + ℵ₁ · ℵ₀ = ℵ₁`. -/
theorem card_extIndex {S : Set ℝ} (hS : #(↥S) = aleph 1) : #(ExtIndex S) = aleph 1 := by
  have hℵ : (ℵ₀ : Cardinal) ≤ aleph 1 := aleph0_le_aleph 1
  have hopt : #(Option ℕ) = (ℵ₀ : Cardinal) := by
    rw [mk_option, mk_nat]
    exact add_eq_left le_rfl one_le_aleph0
  have hprod : #(↥S × Option ℕ) = aleph 1 := by
    rw [mk_prod, lift_id, lift_id, hS, hopt, mul_eq_max hℵ le_rfl, max_eq_left hℵ]
  have h2 : (2 : Cardinal) ≤ aleph 1 := le_trans ofNat_lt_aleph0.le hℵ
  show #(Bool ⊕ (↥S × Option ℕ)) = aleph 1
  rw [mk_sum, lift_id, lift_id, mk_bool, hprod]
  exact add_eq_right hℵ h2

/-! ## Layer 1 in one statement -/

/-- **The Layer 1 package** (audit §4–§5).

Given a bad parameter set `S ⊆ [0,1]` with `|S| = ℵ₁`, the bounded star coding
produces a carrier `D = ExtIndex S` of cardinality `ℵ₁` and a family
`(d_t)_{t ∈ [0,1]}` such that

1. `|D| = ℵ₁`;
2. every `d_t`, `t ∈ [0,1]`, is a metric on `D` with values in `[0,4]`;
3. `d_t` is compatible with the discrete topology on `D` **iff** `t ∉ S`
   (both directions: the failure at `t ∈ S` is part of the claim);
4. the full parameter map `Φ_full : [0,1] → BCPM(D)`, `t ↦ d_t`, satisfies
   `|s − t| ≤ ρ(Φ_full s, Φ_full t) ≤ 2|s − t|`, hence is 2-Lipschitz and
   bi-Lipschitz onto its image;
5. the pullback identity `Φ_full⁻¹(BMet(D)) = [0,1] \ S` holds exactly.

The components remain available individually; `isClosed_image_phiFull` adds
the closed-image statement of audit §5. -/
theorem bounded_star_coding {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) (hcard : #(↥S) = aleph 1) :
    #(ExtIndex S) = aleph 1 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, IsMetricOn (dExt S t) ∧
      ∀ u v, 0 ≤ dExt S t u v ∧ dExt S t u v ≤ 4) ∧
    (∀ t : UnitParam, IsCompatible (phiFull S hS t) ↔ (t : ℝ) ∉ S) ∧
    (∀ t s : UnitParam, |(t : ℝ) - (s : ℝ)| ≤ dist (phiFull S hS t) (phiFull S hS s) ∧
      dist (phiFull S hS t) (phiFull S hS s) ≤ 2 * |(t : ℝ) - (s : ℝ)|) ∧
    Subtype.val '' (phiFull S hS ⁻¹' BMet (ExtIndex S)) = Set.Icc (0 : ℝ) 1 \ S :=
  ⟨card_extIndex hcard,
    fun _ ht => ⟨dExt_isMetricOn hS ht,
      fun u v => ⟨dExt_nonneg ht.1 u v, dExt_le_four hS ht u v⟩⟩,
    dExt_isCompatible_iff S hS,
    fun t s => ⟨abs_sub_le_dist_phiFull S hS t s, dist_phiFull_le S hS t s⟩,
    image_preimage_BMet_phiFull S hS⟩

end IshikiExt
