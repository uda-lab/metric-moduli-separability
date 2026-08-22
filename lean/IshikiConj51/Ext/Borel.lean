-- Ext.Borel
--
-- Issue #56, items 1–2: the Borel obstruction for the bounded discrete
-- Ishiki-extension coding.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §7 items 1–2
-- (the statement gate for the Borel-preprint track).  The parameter-set
-- theorem uses the CH/¬CH dichotomy recorded there; the obstruction pulls it
-- back through the already verified `phiFull` coding.
--
-- Status: sorry-free; no custom axioms.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Card
import IshikiConj51.Ext.BoundedCoding

open Cardinal Set

namespace IshikiExt

noncomputable section

/-! ## Cardinality of Borel sets -/

/-- The Borel σ-algebra of `ℝ` has cardinality at most the continuum. -/
theorem cardinal_borel_subset_le_continuum :
    #{s : Set ℝ | MeasurableSet s} ≤ (𝔠 : Cardinal.{0}) := by
  obtain ⟨b, hb, -, hbasis⟩ := TopologicalSpace.exists_countable_basis ℝ
  have hborel : borel ℝ = MeasurableSpace.generateFrom b :=
    hbasis.borel_eq_generateFrom
  have hbcard : #b ≤ (𝔠 : Cardinal) := by
    exact (Cardinal.le_aleph0_iff_set_countable.mpr hb).trans
      Cardinal.aleph0_le_continuum
  change #{s : Set ℝ | @MeasurableSet ℝ (borel ℝ) s} ≤ (𝔠 : Cardinal)
  rw [hborel]
  exact MeasurableSpace.cardinal_measurableSet_le_continuum hbcard

/-- An uncountable Borel subset of the real line has cardinality continuum. -/
theorem cardinal_borel_uncountable {S : Set ℝ} (hS : MeasurableSet S)
    (hSunc : ¬Countable (↥S)) : #(↥S) = (𝔠 : Cardinal.{0}) := by
  letI : StandardBorelSpace S := MeasurableSet.standardBorel hS
  let e : S ≃ᵐ (ℕ → Bool) :=
    PolishSpace.measurableEquivNatBoolOfNotCountable hSunc
  have hfun : #(ℕ → Bool) = (𝔠 : Cardinal) := by
    rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat,
      Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.two_power_aleph0
  exact e.toEquiv.cardinal_eq.trans hfun

/-! ## The non-Borel parameter set -/

theorem exists_aleph1_nonBorel_of_not_CH
    (hnCH : Cardinal.aleph 1 < (𝔠 : Cardinal.{0})) :
    ∃ S ⊆ Set.Icc (0 : ℝ) 1, #(↥S) = Cardinal.aleph 1 ∧ ¬ MeasurableSet S := by
  have hIcc : #(Set.Icc (0 : ℝ) 1) = (𝔠 : Cardinal.{0}) :=
    Cardinal.mk_Icc_real (by norm_num)
  have hle : Cardinal.aleph 1 ≤ #(Set.Icc (0 : ℝ) 1) :=
    hIcc ▸ Cardinal.aleph_one_le_continuum
  obtain ⟨S, hSsub, hScard⟩ := Cardinal.le_mk_iff_exists_subset.mp hle
  refine ⟨S, hSsub, hScard, ?_⟩
  intro hSmeas
  have hSunc : ¬Countable (↥S) := by
    intro hScount
    have hle0 : #(↥S) ≤ Cardinal.aleph0 :=
      Cardinal.le_aleph0_iff_set_countable.mpr hScount
    exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) (hScard ▸ hle0)
  have hSc : #(↥S) = (𝔠 : Cardinal) :=
    cardinal_borel_uncountable hSmeas hSunc
  exact (ne_of_lt hnCH) (hScard.symm.trans hSc)

theorem exists_aleph1_nonBorel_of_CH
    (hCH : Cardinal.aleph 1 = (𝔠 : Cardinal.{0})) :
    ∃ S ⊆ Set.Icc (0 : ℝ) 1, #(↥S) = Cardinal.aleph 1 ∧ ¬ MeasurableSet S := by
  have hIcc : #(Set.Icc (0 : ℝ) 1) = (𝔠 : Cardinal.{0}) :=
    Cardinal.mk_Icc_real (by norm_num)
  have hpow : (𝔠 : Cardinal.{0}) < #(𝒫 (Set.Icc (0 : ℝ) 1)) := by
    rw [Cardinal.mk_powerset, hIcc]
    exact Cardinal.cantor (𝔠 : Cardinal)
  have hmeas : #{S : Set ℝ | MeasurableSet S} ≤ (𝔠 : Cardinal.{0}) :=
    cardinal_borel_subset_le_continuum
  have hnot : ¬ (∀ S : Set ℝ, S ⊆ Set.Icc (0 : ℝ) 1 → MeasurableSet S) := by
    intro hall
    have hsub : (𝒫 (Set.Icc (0 : ℝ) 1)) ⊆ {S : Set ℝ | MeasurableSet S} := by
      intro S hS
      exact hall S hS
    have hle : #(𝒫 (Set.Icc (0 : ℝ) 1)) ≤ #{S : Set ℝ | MeasurableSet S} :=
      Cardinal.mk_le_mk_of_subset hsub
    exact (not_le_of_gt hpow) (hle.trans hmeas)
  push Not at hnot
  obtain ⟨S, hSsub, hSnonmeas⟩ := hnot
  have hSunc : ¬Countable (↥S) := by
    intro hScount
    exact hSnonmeas (Set.Countable.measurableSet hScount)
  have hSle : #(↥S) ≤ Cardinal.aleph 1 := by
    have hSleC : #(↥S) ≤ (𝔠 : Cardinal.{0}) :=
      hIcc ▸ Cardinal.mk_le_mk_of_subset hSsub
    exact hSleC.trans_eq hCH.symm
  have hSge : Cardinal.aleph 1 ≤ #(↥S) :=
    Cardinal.aleph_one_le_iff.mpr
      (Cardinal.aleph0_lt_mk_iff.mpr (not_countable_iff.mp hSunc))
  exact ⟨S, hSsub, le_antisymm hSle hSge, hSnonmeas⟩

/-- There is an `ℵ₁`-sized non-Borel subset of `[0,1]`. -/
theorem exists_aleph1_nonBorel :
    ∃ S ⊆ Set.Icc (0 : ℝ) 1, #(↥S) = Cardinal.aleph 1 ∧ ¬ MeasurableSet S := by
  have hCHor : Cardinal.aleph 1 ≤ (𝔠 : Cardinal.{0}) :=
    Cardinal.aleph_one_le_continuum
  rcases hCHor.lt_or_eq with hnCH | hCH
  · exact exists_aleph1_nonBorel_of_not_CH hnCH
  · exact exists_aleph1_nonBorel_of_CH hCH

/-! ## Pullback obstruction in the bounded ambient -/

local instance bddPMetMeasurableSpace (D : Type*) : MeasurableSpace (BddPMet D) :=
  borel (BddPMet D)

local instance bddPMetBorelSpace (D : Type*) : BorelSpace (BddPMet D) :=
  ⟨rfl⟩

/-- The bounded compatible-metric locus is not Borel in the bounded
pseudometric ambient, for the parameter set supplied by
`exists_aleph1_nonBorel`. -/
theorem bmet_not_borel {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (_hScard : #(↥S) = Cardinal.aleph 1) (hSnonmeas : ¬ MeasurableSet S) :
    ¬ MeasurableSet (BMet (ExtIndex S)) := by
  intro hBMet
  have hphi : Measurable (phiFull S hS) :=
    (lipschitzWith_phiFull S hS).continuous.measurable
  have hpre : MeasurableSet (phiFull S hS ⁻¹' BMet (ExtIndex S)) :=
    hBMet.preimage hphi
  have himage : MeasurableSet
      (Subtype.val '' (phiFull S hS ⁻¹' BMet (ExtIndex S))) :=
    measurableSet_Icc.subtype_image hpre
  rw [image_preimage_BMet_phiFull S hS] at himage
  have hSmeas : MeasurableSet S := by
    have heq : S = Set.Icc (0 : ℝ) 1 \ (Set.Icc (0 : ℝ) 1 \ S) := by
      ext x
      constructor
      · intro hx
        exact ⟨hS hx, fun hx' => hx'.2 hx⟩
      · intro hx
        by_contra hxn
        exact hx.2 ⟨hx.1, hxn⟩
    rw [heq]
    exact measurableSet_Icc.diff himage
  exact hSnonmeas hSmeas

end
end IshikiExt
