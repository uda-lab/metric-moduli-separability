-- Conj51.GDeltaComplete
--
-- The Lavrentiev–Alexandrov direction: a completely metrizable subspace of a
-- metric space is Gδ in the ambient space. No separability assumption; the
-- ambient space is any `MetricSpace` (our application is `X = ℝ`, but the
-- lemma is proved in full generality per Issue #23's acceptance criteria).
--
-- Confirmed absent from Mathlib v4.32.2 (Issue #19 / PR #20 inventory): no
-- theorem in Mathlib concludes `IsGδ` from a `CompleteSpace` /
-- `IsCompletelyMetrizableSpace` / `PolishSpace` hypothesis. This file proves
-- it from scratch via the X-diameter-restricted oscillation argument
-- (leader session dossier §E).
--
-- Mathematical usage: report/report-ja.md §1 background theorem 1 and §4
-- step 3 (Y ⊆ [0,1] not Gδ ⟹ Y not completely metrizable is the
-- contrapositive of this lemma, specialised to X = ℝ, Y = [0,1]).
--
-- Status: sorry-free.

import Mathlib

open TopologicalSpace Metric Set Filter Topology Bornology

variable {X : Type*} [MetricSpace X]

/-- **Lavrentiev–Alexandrov direction.** If `Y : Set X` is completely
metrizable in its subspace topology, then `Y` is a `Gδ` subset of `X`.
No separability of `X` or `Y` is assumed. -/
theorem isGδ_of_isCompletelyMetrizableSpace {Y : Set X}
    (h : IsCompletelyMetrizableSpace Y) : IsGδ Y := by
  haveI := h
  letI upg := upgradeIsCompletelyMetrizable Y
  letI : MetricSpace Y := upg.toMetricSpace
  letI : PseudoMetricSpace Y := upg.toMetricSpace.toPseudoMetricSpace
  letI : UniformSpace Y := upg.toUniformSpace
  letI : Bornology Y := PseudoMetricSpace.toBornology
  haveI : CompleteSpace Y := upg.toCompleteSpace
  -- `Y` now carries a complete metric `ρ` (the ambient `dist` on `↥Y`)
  -- inducing the same topology as the subspace topology from `X`.
  have hn1pos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hkey : ∀ n : ℕ, 2 * (1 / (3 * ((n : ℝ) + 1))) < 1 / ((n : ℝ) + 1) := by
    intro n
    have h3 : (0 : ℝ) < (n : ℝ) + 1 := hn1pos n
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) h3]
    nlinarith
  set U : ℕ → Set X := fun n : ℕ =>
      ⋃₀ {V : Set X | IsOpen V ∧ IsBounded V ∧ Metric.diam V < 1 / ((n : ℝ) + 1) ∧
        IsBounded (((↑) : Y → X) ⁻¹' V) ∧
        Metric.diam (((↑) : Y → X) ⁻¹' V) < 1 / ((n : ℝ) + 1)} with hUdef
  have hUopen : ∀ n : ℕ, IsOpen (U n) := fun n => isOpen_sUnion fun _ hV => hV.1
  -- Forward inclusion: `Y ⊆ U n` for every `n`, and `Y ⊆ closure Y`.
  have hYsubU : ∀ n : ℕ, Y ⊆ U n := by
    intro n y hy
    set yY : Y := ⟨y, hy⟩ with hyY
    set δ : ℝ := 1 / (3 * ((n : ℝ) + 1)) with hδdef
    have hδpos : 0 < δ := by positivity
    obtain ⟨V₀, hV₀open, hV₀eq⟩ := isOpen_induced_iff.mp (Metric.isOpen_ball (x := yY) (ε := δ))
    have hymemV₀ : y ∈ V₀ := by
      have : yY ∈ ((↑) : Y → X) ⁻¹' V₀ := by
        rw [hV₀eq]; exact Metric.mem_ball_self hδpos
      exact this
    refine ⟨V₀ ∩ Metric.ball y δ, ⟨hV₀open.inter Metric.isOpen_ball, ?_, ?_, ?_, ?_⟩,
      ⟨hymemV₀, Metric.mem_ball_self hδpos⟩⟩
    · exact Metric.isBounded_ball.subset inter_subset_right
    · calc Metric.diam (V₀ ∩ Metric.ball y δ)
          ≤ Metric.diam (Metric.ball y δ) :=
            Metric.diam_mono inter_subset_right Metric.isBounded_ball
        _ ≤ 2 * δ := Metric.diam_ball hδpos.le
        _ < 1 / ((n : ℝ) + 1) := by rw [hδdef]; exact hkey n
    · have hsub : ((↑) : Y → X) ⁻¹' (V₀ ∩ Metric.ball y δ) ⊆ Metric.ball yY δ := by
        rw [preimage_inter, hV₀eq]
        exact inter_subset_left
      exact Metric.isBounded_ball.subset hsub
    · have hsub : ((↑) : Y → X) ⁻¹' (V₀ ∩ Metric.ball y δ) ⊆ Metric.ball yY δ := by
        rw [preimage_inter, hV₀eq]
        exact inter_subset_left
      calc Metric.diam (((↑) : Y → X) ⁻¹' (V₀ ∩ Metric.ball y δ))
          ≤ Metric.diam (Metric.ball yY δ) := Metric.diam_mono hsub Metric.isBounded_ball
        _ ≤ 2 * δ := Metric.diam_ball hδpos.le
        _ < 1 / ((n : ℝ) + 1) := by rw [hδdef]; exact hkey n
  -- Backward inclusion: `(⋂ n, U n) ∩ closure Y ⊆ Y`.
  have hInterSub : (⋂ n, U n) ∩ closure Y ⊆ Y := by
    rintro x ⟨hxU, hxcl⟩
    have hxU' : ∀ n : ℕ, ∃ V : Set X,
        (IsOpen V ∧ IsBounded V ∧ Metric.diam V < 1 / ((n : ℝ) + 1) ∧
          IsBounded (((↑) : Y → X) ⁻¹' V) ∧
          Metric.diam (((↑) : Y → X) ⁻¹' V) < 1 / ((n : ℝ) + 1)) ∧ x ∈ V := by
      intro n
      have h1 : x ∈ U n := mem_iInter.mp hxU n
      rw [hUdef] at h1
      exact mem_sUnion.mp h1
    choose V hVprop hVmemX using hxU'
    have hVopen : ∀ n : ℕ, IsOpen (V n) := fun n => (hVprop n).1
    have hVbdd : ∀ n : ℕ, IsBounded (V n) := fun n => (hVprop n).2.1
    have hVdiam : ∀ n : ℕ, Metric.diam (V n) < 1 / ((n : ℝ) + 1) := fun n => (hVprop n).2.2.1
    have hVbddY : ∀ n : ℕ, IsBounded (((↑) : Y → X) ⁻¹' (V n)) := fun n => (hVprop n).2.2.2.1
    have hVdiamY : ∀ n : ℕ, Metric.diam (((↑) : Y → X) ⁻¹' (V n)) < 1 / ((n : ℝ) + 1) :=
      fun n => (hVprop n).2.2.2.2
    set W : ℕ → Set X := fun n : ℕ => ⋂ k ∈ Finset.range (n + 1), V k with hWdef
    have hWopen : ∀ n : ℕ, IsOpen (W n) := fun n =>
      isOpen_biInter_finset fun k _ => hVopen k
    have hWmemX : ∀ n : ℕ, x ∈ W n := by
      intro n
      simp only [hWdef, mem_iInter]
      exact fun k _ => hVmemX k
    have hWanti : ∀ {n m : ℕ}, n ≤ m → W m ⊆ W n := by
      intro n m hnm z hz
      simp only [hWdef, mem_iInter] at hz ⊢
      exact fun k hk => hz k
        (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hnm)))
    have hWsubV : ∀ n : ℕ, W n ⊆ V n :=
      fun n => biInter_subset_of_mem (Finset.self_mem_range_succ n)
    have hWbdd : ∀ n : ℕ, IsBounded (W n) := fun n => (hVbdd n).subset (hWsubV n)
    have hWdiam : ∀ n : ℕ, Metric.diam (W n) < 1 / ((n : ℝ) + 1) :=
      fun n => lt_of_le_of_lt (Metric.diam_mono (hWsubV n) (hVbdd n)) (hVdiam n)
    have hWbddY : ∀ n : ℕ, IsBounded (((↑) : Y → X) ⁻¹' (W n)) :=
      fun n => (hVbddY n).subset (preimage_mono (hWsubV n))
    have hWdiamY : ∀ n : ℕ, Metric.diam (((↑) : Y → X) ⁻¹' (W n)) < 1 / ((n : ℝ) + 1) :=
      fun n => lt_of_le_of_lt
        (Metric.diam_mono (preimage_mono (hWsubV n)) (hVbddY n)) (hVdiamY n)
    have hWmeetsY : ∀ n : ℕ, (W n ∩ Y).Nonempty :=
      fun n => mem_closure_iff.mp hxcl (W n) (hWopen n) (hWmemX n)
    choose y hyW hyY using hWmeetsY
    set yY : ℕ → Y := fun n => ⟨y n, hyY n⟩ with hyYdef
    have hyYinW : ∀ n : ℕ, ((yY n : X)) ∈ W n := hyW
    have hyYpreim : ∀ n : ℕ, yY n ∈ ((↑) : Y → X) ⁻¹' (W n) := hyW
    have hcauchy : CauchySeq yY := by
      apply cauchySeq_of_le_tendsto_0 (fun n : ℕ => 1 / ((n : ℝ) + 1))
      · intro n m N hNn hNm
        have hn : yY n ∈ ((↑) : Y → X) ⁻¹' (W N) :=
          (preimage_mono (hWanti hNn)) (hyYpreim n)
        have hm : yY m ∈ ((↑) : Y → X) ⁻¹' (W N) :=
          (preimage_mono (hWanti hNm)) (hyYpreim m)
        exact (dist_le_diam_of_mem (hWbddY N) hn hm).trans (hWdiamY N).le
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨yLim, hyLim⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hvalTendsto : Tendsto (fun n : ℕ => ((yY n : X))) atTop (𝓝 ((yLim : X))) :=
      (continuous_subtype_val.continuousAt).tendsto.comp hyLim
    have hxTendsto : Tendsto (fun n : ℕ => ((yY n : X))) atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      calc dist ((yY n : X)) x ≤ Metric.diam (W n) :=
            dist_le_diam_of_mem (hWbdd n) (hyYinW n) (hWmemX n)
        _ ≤ 1 / ((n : ℝ) + 1) := (hWdiam n).le
    have hxeq : x = ((yLim : X)) := tendsto_nhds_unique hxTendsto hvalTendsto
    rw [hxeq]
    exact yLim.2
  have hYeq : Y = (⋂ n, U n) ∩ closure Y :=
    Subset.antisymm
      (fun y hy => ⟨mem_iInter.mpr (fun n => hYsubU n hy), subset_closure hy⟩) hInterSub
  rw [hYeq]
  exact (IsGδ.iInter_of_isOpen hUopen).inter
    (PerfectlyNormalSpace.closed_gdelta isClosed_closure)
