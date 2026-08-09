-- Conj51.MainTheorem
--
-- States and proves `THM-CONJ51`.
--
-- `MetD D` — the Lean representation of the source's `Met(D)` (Ishiki,
-- arXiv:2407.03030, §1.1; verified in Issue #2) — was introduced here by
-- Issue #6 and now lives, unchanged, in `Conj51/MetD.lean`.  It had to move
-- to a module the claim files can import: this file imports
-- `MetricConstruction.lean` and `ClosedEmbedding.lean`, and those are exactly
-- the modules that construct elements of `Met(D)`.  See `MetD.lean` for the
-- source-faithfulness notes on `IsMetricOn`, the `.topology = ⊥` condition,
-- and the extended-valued supremum distance.
--
-- Source-faithfulness note specific to this file:
--   * "Completely metrizable" is the ordinary (finite-metric)
--     notion applied to the *topology* `MetD D` carries — Mathlib's
--     `TopologicalSpace.IsCompletelyMetrizableSpace` asks only whether some
--     compatible finite-valued `MetricSpace` structure realises that
--     topology completely; it does not require the topology to have been
--     built from a finite-valued distance in the first place.
--
-- This file assembles report/report-ja.md §4, whose six steps map onto the
-- proof of `thm_conj51_of_lavrentiev` below as follows:
--   step 1  `lem_A_exists`                     (Cardinality.lean, Issue #8)
--   step 2  `isFSigma_of_isGdelta_sdiff`       (below; De Morgan)
--   step 3  the `lavrentiev` hypothesis        (GDeltaComplete.lean, Issue #23)
--   step 4  `isClosedEmbedding_starParam`      (ClosedEmbedding.lean, Issue #9)
--           together with `MetD.relabelIsometry` (Relabel.lean), which moves
--           the construction from the concrete `StarIndex A` to an arbitrary
--           `D` of the same cardinality — report §3.2/§3.8
--   step 5  `Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`
--           (Mathlib; background theorem 2, no separability assumed)
--   step 6  the contradiction closing `thm_conj51_of_lavrentiev`
--
-- Steps 2–6 are stated and proved here in full.  Step 3 — the
-- Lavrentiev–Alexandrov direction "completely metrizable subspace of a metric
-- space is Gδ" (report §1 background theorem 1) — is absent from Mathlib
-- v4.32.2 and is Issue #23's deliverable; until it lands it is carried as the
-- explicit hypothesis `lavrentiev` of `thm_conj51_of_lavrentiev`, and
-- `thm_conj51` itself keeps a tracked `sorry`.  See notes/proof-audit.md.

import Mathlib
import IshikiConj51.Conj51.MetD
import IshikiConj51.Conj51.Relabel
import IshikiConj51.Conj51.Cardinality
import IshikiConj51.Conj51.MetricConstruction
import IshikiConj51.Conj51.ClosedEmbedding

open Cardinal
open scoped ENNReal

/-- Report §4 step 2 (De Morgan).  If `A ⊆ [0,1]` and the complement
`Y = [0,1] \ A` is `Gδ` in `ℝ`, then `A` is `Fσ`: writing `Y = ⋂ₙ Uₙ` with
`Uₙ` open, `A = ⋃ₙ ([0,1] ∩ Uₙᶜ)` and each term is closed.

The intersection with `[0,1]` is what lets a statement about `Y` inside the
*ambient* line yield `Fσ`-ness of `A` inside the line as well; it works
because `[0,1]` is itself closed. -/
theorem isFSigma_of_isGdelta_sdiff {A : Set ℝ} (hAsub : A ⊆ Set.Icc 0 1)
    (h : IsGδ (Set.Icc (0 : ℝ) 1 \ A)) : IsFSigma A := by
  obtain ⟨U, hUopen, hUeq⟩ := h.eq_iInter_nat
  refine ⟨fun n => Set.Icc (0 : ℝ) 1 ∩ (U n)ᶜ,
    fun n => isClosed_Icc.inter (hUopen n).isClosed_compl, ?_⟩
  have hmem : ∀ x : ℝ, (x ∈ Set.Icc (0 : ℝ) 1 ∧ x ∉ A) ↔ ∀ n, x ∈ U n := by
    intro x
    simpa [Set.mem_iInter] using Set.ext_iff.mp hUeq x
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro hxA
    have hne : ¬ ∀ n, x ∈ U n := fun hall => ((hmem x).mpr hall).2 hxA
    obtain ⟨n, hn⟩ := not_forall.mp hne
    exact ⟨n, hAsub hxA, hn⟩
  · rintro ⟨n, hxI, hn⟩
    by_contra hxA
    exact hn ((hmem x).mp ⟨hxI, hxA⟩ n)

/-- **THM-CONJ51, modulo the Lavrentiev–Alexandrov direction.**

This is the complete assembly of report §4 with its one Mathlib-absent
ingredient isolated as the hypothesis `lavrentiev`, which is exactly report §1
background theorem 1 specialised to the ambient space `ℝ`:

> a subset of `ℝ` that is completely metrizable in its subspace topology is
> `Gδ` in `ℝ`.

The hypothesis does *not* smuggle in the conclusion: it is a statement about
subsets of the line, with no reference to `Met(D)`, to `A`, or to
cardinality, and it is a genuine classical theorem (Alexandrov/Lavrentiev)
being formalised independently in Issue #23. -/
theorem thm_conj51_of_lavrentiev
    (lavrentiev : ∀ Y : Set ℝ,
      TopologicalSpace.IsCompletelyMetrizableSpace Y → IsGδ Y)
    (D : Type*) (hD : #D = Cardinal.aleph 1) :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D) := by
  intro hcm
  haveI := hcm
  -- step 1: LEM-A-EXISTS
  obtain ⟨A, hAsub, hAcard, hAnotFsigma⟩ := lem_A_exists
  -- step 4a: `D` and the star index set have the same cardinality, so `Met(D)`
  -- and `Met(StarIndex A)` are isometric (Relabel.lean).  `StarIndex A` lives in
  -- `Type 0` whereas `D : Type u` is arbitrary, so the two cardinals are
  -- compared after `Cardinal.lift`; `ℵ₁` is lift-invariant (`Cardinal.lift_aleph`,
  -- `Ordinal.lift_one`), so this is the same statement as `#(StarIndex A) = #D`.
  obtain ⟨σ⟩ : Nonempty (StarIndex A ≃ D) :=
    Cardinal.lift_mk_eq'.mp <| by
      rw [card_starIndex hAcard, hD]
      simp
  haveI hStar : TopologicalSpace.IsCompletelyMetrizableSpace (MetD (StarIndex A)) :=
    (MetD.relabelIsometry σ.symm).toHomeomorph.isClosedEmbedding.IsCompletelyMetrizableSpace
  -- steps 4b and 5: LEM-CLOSED-IMAGE plus closed-subspace inheritance
  haveI hY : TopologicalSpace.IsCompletelyMetrizableSpace (StarParamSpace A) :=
    (isClosedEmbedding_starParam A).IsCompletelyMetrizableSpace
  -- step 3: Lavrentiev, applied to `Y = [0,1] \ A`
  have hGdelta : IsGδ (Set.Icc (0 : ℝ) 1 \ A) := lavrentiev _ hY
  -- steps 2 and 6: `A` would be Fσ, contradicting LEM-A-EXISTS
  exact hAnotFsigma (isFSigma_of_isGdelta_sdiff hAsub hGdelta)

/-- **THM-CONJ51.** For a discrete space `D` of cardinality `ℵ₁`,
`Met(D)` — equipped with the supremum-metric topology — is not completely
metrizable.

This matches the report's (`report/report-ja.md` §2) and the source's
(Ishiki, arXiv:2407.03030, Conjecture 5.1) statement exactly: no bounded,
uniformly-discrete, or otherwise weakened proxy is substituted.

Status: the whole of report §4 is proved in `thm_conj51_of_lavrentiev`; the
only step still missing is the Lavrentiev–Alexandrov direction (Issue #23,
`GDeltaComplete.lean`), which discharges the `lavrentiev` hypothesis. Tracked
as a `sorry` in notes/proof-audit.md; not claimed as proved. -/
theorem thm_conj51 (D : Type*) (hD : #D = Cardinal.aleph 1) :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D) := by
  sorry
