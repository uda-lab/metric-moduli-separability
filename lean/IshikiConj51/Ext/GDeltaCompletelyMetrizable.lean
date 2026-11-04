-- Ext.GDeltaCompletelyMetrizable
--
-- Issue #108: the reverse Alexandrov theorem needed for the five-way
-- complete-metrizability/component/σ-compactness equivalence.
--
-- Statement gate (frozen audit record): `notes/borel-manuscript-20260827-audit.md`
-- §2.16 and §4 row E4d; Kechris, *Classical Descriptive Set Theory*,
-- Theorem 3.11, reverse direction.
--
-- Confirmed absent from Mathlib v4.32.2 at the 2026-09-02 inventory: no
-- theorem derives complete metrizability of a `Gδ` subspace of a completely
-- metrizable ambient space.  The forward direction is proved separately in
-- `IshikiConj51/Conj51/GDeltaComplete.lean`.
--
-- Status: sorry-free; no custom axioms.

import Mathlib

open TopologicalSpace Metric Set Filter Topology

namespace IshikiExt

noncomputable section

/-- Complete metrizability is invariant under homeomorphism.  Stated for
wholly abstract `α`/`β` (only a bare `TopologicalSpace` instance each) and
proved once at this generality, rather than inlined at each call site: when
`β` is later instantiated with a concrete type that already carries its own
`PseudoEMetricSpace`/`UniformSpace` instance (e.g. a subset of a metrizable
space), inlining this argument directly against that concrete type lets
ordinary instance search see — and become confused by — the competing
instance. Elaborating the argument once, generically, avoids that: the
`MetricSpace β` instance built inside this proof is the only one visible while
the proof itself is type-checked, so no diamond can arise here regardless of
what instance the caller's concrete `β` happens to carry.  (The identical
argument appears independently in `Ext/FiveWay.lean`, restated here rather
than imported to avoid a cyclic dependency between that file and this one.) -/
theorem isCompletelyMetrizableSpace_of_homeomorph
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β)
    (hα : TopologicalSpace.IsCompletelyMetrizableSpace α) :
    TopologicalSpace.IsCompletelyMetrizableSpace β := by
  letI : TopologicalSpace.IsCompletelyMetrizableSpace α := hα
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
  let mα : MetricSpace α := inferInstance
  let mβ : MetricSpace β := MetricSpace.induced e.symm e.symm.injective mα
  have htopα : mα.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace α) := by
    with_reducible_and_instances rfl
  have htop : mβ.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace β) := by
    change TopologicalSpace.induced e.symm mα.toUniformSpace.toTopologicalSpace = _
    rw [htopα]
    exact e.symm.isInducing.eq_induced.symm
  letI : MetricSpace β := mβ
  have hcomplete : CompleteSpace β := by
    have hisometry : Isometry (e.symm : β → α) :=
      MetricSpace.isometry_induced (e.symm : β → α) e.symm.injective
    exact (hisometry.isUniformInducing.completeSpace_congr e.symm.surjective).mpr
      (inferInstance : CompleteSpace α)
  exact ⟨⟨mβ, htop, hcomplete⟩⟩

/-- **Alexandrov's theorem, reverse direction.**  A `Gδ` subset of a
completely metrizable space is itself completely metrizable, in its subspace
topology.  No separability assumption on either space.  This is
`thm:complete-metrizability-g-delta`'s reverse direction (Kechris, Theorem
3.11), confirmed absent from Mathlib; `IshikiConj51/Conj51/GDeltaComplete.lean`
has the forward direction already. Consumed by Issue #108's `sigma-compact ⇒
each-component` branch (`notes/borel-manuscript-20260827-audit.md` §2.16),
where it is used for the first time in this repository (the audit records
that every earlier use of Alexandrov–Lavrentiev was the forward direction). -/
theorem isCompletelyMetrizableSpace_of_isGδ {X : Type*} [TopologicalSpace X]
    (hX : TopologicalSpace.IsCompletelyMetrizableSpace X) {Y : Set X}
    (hY : IsGδ Y) : TopologicalSpace.IsCompletelyMetrizableSpace ↥Y := by
  letI : TopologicalSpace.IsCompletelyMetrizableSpace X := hX
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨U, hUopen, hYU⟩ := hY.eq_iInter_nat
  have hYsubU : ∀ n : ℕ, Y ⊆ U n := by
    intro n x hx
    rw [hYU] at hx
    exact mem_iInter.mp hx n
  let g : ℕ → X → ℝ := fun n x => 1 / Metric.infDist x (U n)ᶜ
  have hg_continuous : ∀ n : ℕ, Continuous (fun y : ↥Y => g n (y : X)) := by
    intro n
    rw [continuous_iff_continuousAt]
    intro y
    have hy_not_mem : (y : X) ∉ closure (U n)ᶜ := by
      rw [(hUopen n).isClosed_compl.closure_eq]
      simpa using hYsubU n y.2
    have hcomp_eq :
        ((fun x => (Metric.infDist x (U n)ᶜ)⁻¹) ∘ ((↑) : ↥Y → X))
          = (fun z : ↥Y => (Metric.infDist (z : X) (U n)ᶜ)⁻¹) := rfl
    have hterm : ContinuousAt (fun z : ↥Y => (Metric.infDist (z : X) (U n)ᶜ)⁻¹) y :=
      hcomp_eq ▸ (Metric.continuousAt_inv_infDist_pt hy_not_mem).comp
        continuous_subtype_val.continuousAt
    simpa only [g, one_div] using hterm
  have hgraph_continuous : Continuous (fun y : ↥Y => fun n => g n (y : X)) :=
    continuous_pi hg_continuous
  let Φ : ↥Y → X × (ℕ → ℝ) :=
    fun y => ((y : X), fun n => g n (y : X))
  have hΦ_continuous : Continuous Φ := by
    exact continuous_subtype_val.prodMk hgraph_continuous
  have hΦ_embedding : IsEmbedding Φ := by
    refine Topology.IsEmbedding.of_comp hΦ_continuous continuous_fst ?_
    have hcomp_eq : (Prod.fst ∘ Φ) = ((↑) : ↥Y → X) := rfl
    rw [hcomp_eq]
    exact Topology.IsEmbedding.subtypeVal
  have hΦ_range_closed : IsClosed (Set.range Φ) := by
    rw [← closure_subset_iff_isClosed]
    rintro ⟨x, a⟩ hxa
    obtain ⟨z, hz_range, hz_tendsto⟩ := mem_closure_iff_seq_limit.mp hxa
    choose y hy using hz_range
    have hz_eq : z = fun k => Φ (y k) := funext fun k => (hy k).symm
    rw [hz_eq] at hz_tendsto
    have hy_tendsto_x : Tendsto (fun k => (y k : X)) atTop (𝓝 x) := by
      simpa only [Φ] using hz_tendsto.fst_nhds
    have hg_tendsto_a : ∀ n : ℕ,
        Tendsto (fun k => g n (y k : X)) atTop (𝓝 (a n)) := by
      intro n
      have hsnd := hz_tendsto.snd_nhds
      exact tendsto_pi_nhds.mp hsnd n
    have hxU : ∀ n : ℕ, x ∈ U n := by
      intro n
      by_contra hx
      have hx_compl : x ∈ (U n)ᶜ := hx
      have hcompl_nonempty : ((U n)ᶜ : Set X).Nonempty := ⟨x, hx_compl⟩
      have hinf_tendsto :
          Tendsto (fun k => Metric.infDist (y k : X) (U n)ᶜ) atTop (𝓝 0) := by
        have hcomp_eq :
            ((fun x' => Metric.infDist x' (U n)ᶜ) ∘ (fun k => (y k : X)))
              = (fun k => Metric.infDist (y k : X) (U n)ᶜ) := rfl
        have h : Tendsto (fun k => Metric.infDist (y k : X) (U n)ᶜ) atTop
            (𝓝 (Metric.infDist x (U n)ᶜ)) :=
          hcomp_eq ▸ ((Metric.continuous_infDist_pt (U n)ᶜ).tendsto x).comp hy_tendsto_x
        simpa only [Metric.infDist_zero_of_mem hx_compl] using h
      have hinf_pos : ∀ k : ℕ, 0 < Metric.infDist (y k : X) (U n)ᶜ := by
        intro k
        apply ((hUopen n).isClosed_compl.notMem_iff_infDist_pos hcompl_nonempty).mp
        simpa using hYsubU n (y k).2
      have hinf_tendsto_right :
          Tendsto (fun k => Metric.infDist (y k : X) (U n)ᶜ) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinf_tendsto
          (Eventually.of_forall hinf_pos)
      have hg_tendsto_top : Tendsto (fun k => g n (y k : X)) atTop atTop := by
        have htop := hinf_tendsto_right.inv_tendsto_nhdsGT_zero
        have h_inv :
            (fun k : ℕ => Metric.infDist (y k : X) (U n)ᶜ)⁻¹ =
              (fun k : ℕ => (Metric.infDist (y k : X) (U n)ᶜ)⁻¹) := by
          funext k
          simp only [Pi.inv_apply]
        rw [h_inv] at htop
        simpa only [g, one_div, Function.comp] using htop
      exact (not_tendsto_atTop_of_tendsto_nhds (hg_tendsto_a n) hg_tendsto_top).elim
    have hxY : x ∈ Y := by
      rw [hYU]
      exact mem_iInter.mpr hxU
    have ha : a = fun n => g n x := by
      funext n
      have hx_not_mem : x ∉ closure (U n)ᶜ := by
        rw [(hUopen n).isClosed_compl.closure_eq]
        simpa using hxU n
      have hg_tendsto_x : Tendsto (fun k => g n (y k : X)) atTop (𝓝 (g n x)) := by
        have hcomp_eq :
            ((fun x' => (Metric.infDist x' (U n)ᶜ)⁻¹) ∘ (fun k => (y k : X)))
              = (fun k => (Metric.infDist (y k : X) (U n)ᶜ)⁻¹) := rfl
        have hterm : Tendsto (fun k => (Metric.infDist (y k : X) (U n)ᶜ)⁻¹) atTop
            (𝓝 ((Metric.infDist x (U n)ᶜ)⁻¹)) :=
          hcomp_eq ▸ (Metric.continuousAt_inv_infDist_pt hx_not_mem).tendsto.comp hy_tendsto_x
        simpa only [g, one_div] using hterm
      exact tendsto_nhds_unique (hg_tendsto_a n) hg_tendsto_x
    refine ⟨⟨x, hxY⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact ha.symm
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → ℝ) := inferInstance
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (X × (ℕ → ℝ)) := inferInstance
  have hRange : TopologicalSpace.IsCompletelyMetrizableSpace (Set.range Φ) :=
    hΦ_range_closed.isCompletelyMetrizableSpace
  let e : Set.range Φ ≃ₜ ↥Y := hΦ_embedding.toHomeomorph.symm
  exact isCompletelyMetrizableSpace_of_homeomorph e hRange

end

end IshikiExt
