-- Conj51.Cardinality
-- Formalises the descriptive-set-theoretic and cardinality prerequisites
-- for the proof of Ishiki Conjecture 5.1 (THM-CONJ51).
--
-- Key claim: LEM-A-EXISTS
--   In ZFC, there exists A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
--
-- Lean note: "A is not Fσ" means A cannot be expressed as a countable union
-- of closed sets.  The correct Mathlib predicate is the complement of
-- `Set.IsGdelta` (an Fσ set is a Gδ in the complement sense), or directly:
-- ¬ ∃ (F : ℕ → Set ℝ), (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n.
-- `IsSigmaCompact` is a DIFFERENT property (countable union of compact sets)
-- and must NOT be used as a proxy for Fσ in the final formalisation.
-- Mathlib library gap: as of v4.32.2, there is no single predicate `IsFSigma`
-- in Mathlib; the definition must be unfolded explicitly.
-- See notes/proof-audit.md (sorry tracker) for status.
--
-- Proof matches the audited two-case argument in report/report-ja.md §3
-- (Issue #3): CH branch via irrationals + the Baire category theorem,
-- non-CH branch via the perfect set theorem. See notes/proof-audit.md
-- (Issue #8) for the Mathlib declaration names used at each step.
--
-- Status: sorry-free.

import Mathlib

open Cardinal Set

/-- Predicate: A is an Fσ set (countable union of closed sets). -/
def IsFSigma (A : Set ℝ) : Prop :=
  ∃ (F : ℕ → Set ℝ), (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n

/-- A closed set disjoint from the (dense) rationals is nowhere dense. -/
theorem IsClosed.isNowhereDense_of_disjoint_rat {F : Set ℝ} (hF : IsClosed F)
    (hFQ : Disjoint F (range ((↑) : ℚ → ℝ))) : IsNowhereDense F := by
  have hdense : Dense (Fᶜ : Set ℝ) :=
    Rat.denseRange_cast.mono (subset_compl_iff_disjoint_right.mpr hFQ.symm)
  exact (isClosed_isNowhereDense_iff_compl.mpr ⟨hF.isOpen_compl, hdense⟩).2

/-- Every singleton in `ℝ` is nowhere dense (`ℝ` has no isolated points). -/
theorem isNowhereDense_singleton_real (x : ℝ) : IsNowhereDense ({x} : Set ℝ) := by
  haveI := PerfectSpace.not_isolated x
  exact (isClosed_isNowhereDense_iff_compl.mpr
    ⟨isOpen_compl_singleton, dense_compl_singleton x⟩).2

/-- The rationals (as a subset of `ℝ`) are meagre. -/
theorem isMeagre_range_rat : IsMeagre (range ((↑) : ℚ → ℝ)) := by
  have : range ((↑) : ℚ → ℝ) = ⋃ q : ℚ, ({(q : ℝ)} : Set ℝ) := by
    ext x; simp [eq_comm]
  rw [this]
  exact isMeagre_iUnion fun q => (isNowhereDense_singleton_real (q : ℝ)).isMeagre

/-- LEM-A-EXISTS, CH branch: the irrationals in `[0,1]` witness the claim
    when `ℵ₁ = 𝔠`. This branch does not use the CH hypothesis except to
    convert the cardinality `𝔠` to `ℵ₁`. -/
theorem lem_A_exists_of_CH (hCH : Cardinal.aleph 1 = (𝔠 : Cardinal.{0})) :
    ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧ (#A = Cardinal.aleph 1) ∧ ¬ IsFSigma A := by
  set T : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ) with hT
  set A : Set ℝ := Set.Icc (0 : ℝ) 1 \ range ((↑) : ℚ → ℝ) with hA
  have hTsub : T ⊆ Set.Icc (0 : ℝ) 1 := inter_subset_left
  have hAeq : A = Set.Icc (0 : ℝ) 1 \ T := by
    rw [hA, hT]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  refine ⟨A, sdiff_subset, ?_, ?_⟩
  · -- Cardinality: #A = 𝔠 = ℵ₁.
    have hIcc : #(Set.Icc (0 : ℝ) 1) = 𝔠 := mk_Icc_real (by norm_num)
    have hTcount : T.Countable := (countable_range ((↑) : ℚ → ℝ)).mono inter_subset_right
    have hTlt : #T < 𝔠 := by
      calc #T ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hTcount
        _ < 𝔠 := aleph0_lt_continuum
    have hsum : #A + #T = #(Set.Icc (0 : ℝ) 1) := by
      rw [hAeq]; exact mk_sdiff_add_mk hTsub
    have hAle : #A ≤ 𝔠 := hIcc ▸ mk_le_mk_of_subset sdiff_subset
    rcases hAle.lt_or_eq with hlt | heq
    · exfalso
      have hcontra : #A + #T < 𝔠 := add_lt_of_lt aleph0_lt_continuum.le hlt hTlt
      rw [hsum, hIcc] at hcontra
      exact lt_irrefl _ hcontra
    · rw [heq, hCH]
  · -- Not Fσ: via the Baire category theorem.
    rintro ⟨F, hFclosed, hFA⟩
    have hFnwd : ∀ n, IsNowhereDense (F n) := by
      intro n
      apply (hFclosed n).isNowhereDense_of_disjoint_rat
      rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
      rintro x ⟨hxF, hxQ⟩
      have hxA : x ∈ A := hFA ▸ mem_iUnion_of_mem n hxF
      exact hxA.2 hxQ
    have hAmeagre : IsMeagre A := hFA ▸ isMeagre_iUnion (fun n => (hFnwd n).isMeagre)
    have hIccmeagre : IsMeagre (Set.Icc (0 : ℝ) 1) := by
      apply (hAmeagre.union isMeagre_range_rat).mono
      intro x hx
      by_cases hq : x ∈ range ((↑) : ℚ → ℝ)
      · exact Or.inr hq
      · exact Or.inl ⟨hx, hq⟩
    have hIoosub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := Ioo_subset_Icc_self
    exact not_isMeagre_of_isOpen isOpen_Ioo ⟨(1 / 2 : ℝ), by norm_num⟩
      (hIccmeagre.mono hIoosub)

/-- LEM-A-EXISTS, non-CH branch: any subset of `[0,1]` of cardinality `ℵ₁`
    witnesses the claim when `ℵ₁ < 𝔠`, via the perfect set theorem. -/
theorem lem_A_exists_of_not_CH (hnCH : Cardinal.aleph 1 < (𝔠 : Cardinal.{0})) :
    ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧ (#A = Cardinal.aleph 1) ∧ ¬ IsFSigma A := by
  have hIcc : #(Set.Icc (0 : ℝ) 1) = 𝔠 := mk_Icc_real (by norm_num)
  have hle : Cardinal.aleph 1 ≤ #(Set.Icc (0 : ℝ) 1) := hIcc ▸ aleph_one_le_continuum
  obtain ⟨A, hAsub, hAcard⟩ := le_mk_iff_exists_subset.mp hle
  refine ⟨A, hAsub, hAcard, ?_⟩
  rintro ⟨F, hFclosed, hFA⟩
  have hFcount : ∀ n, (F n).Countable := by
    intro n
    by_contra hFnc
    obtain ⟨f, hfrange, -, hfinj⟩ :=
      (hFclosed n).exists_nat_bool_injection_of_not_countable hFnc
    have hFnsub : F n ⊆ A := hFA ▸ subset_iUnion F n
    let f' : (ℕ → Bool) → A := fun x => ⟨f x, hFnsub (hfrange (mem_range_self x))⟩
    have hf'inj : Function.Injective f' := by
      intro x y hxy
      exact hfinj (congrArg Subtype.val hxy)
    have hCB : (𝔠 : Cardinal) = #(ℕ → Bool) := by
      rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
      exact two_power_aleph0.symm
    have : (𝔠 : Cardinal) ≤ #A := by
      calc (𝔠 : Cardinal) = #(ℕ → Bool) := hCB
        _ ≤ #A := Cardinal.mk_le_of_injective hf'inj
    exact absurd (this.trans hAcard.le) (not_le.mpr hnCH)
  have hAcount : A.Countable := hFA ▸ countable_iUnion hFcount
  have : #A ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hAcount
  exact absurd (hAcard ▸ this) (not_le.mpr aleph0_lt_aleph_one)

/-- LEM-A-EXISTS: There exists a subset of [0,1] of cardinality ℵ₁ that is
    not an Fσ set.
    Proof: case split on CH; see `lem_A_exists_of_CH` /
    `lem_A_exists_of_not_CH` (report §3, audited in Issue #3). -/
theorem lem_A_exists :
    ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧
    (#A = Cardinal.aleph 1) ∧
    ¬ IsFSigma A := by
  have h01 : Cardinal.aleph 1 ≤ (𝔠 : Cardinal.{0}) := aleph_one_le_continuum
  rcases h01.lt_or_eq with hnCH | hCH
  · exact lem_A_exists_of_not_CH hnCH
  · exact lem_A_exists_of_CH hCH
