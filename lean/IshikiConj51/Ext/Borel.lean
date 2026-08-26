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

/-! ## Proposition 2.1, with the density clause

The preprint's Proposition 2.1 asserts, beyond the `ℵ₁`-sized non-Borel set of
`exists_aleph1_nonBorel`, that the set is *dense in `[0,1]`* and *non-Borel in
`[0,1]`* — both statements about the space `[0,1]`, not about `ℝ`.  They are
rendered on the subtype `↥(Icc 0 1)`:

* "dense in `[0,1]`" is `Dense (Subtype.val ⁻¹' S)` for the subspace topology
  of `↥(Icc 0 1)` — note that `Dense S` over `ℝ` would be *false* for any
  `S ⊆ Icc 0 1`, so it is not a rendering of the printed clause;
  `dense_val_preimage_Icc_iff` identifies the subtype statement with the
  ambient closure statement `Icc 0 1 ⊆ closure S`;
* "non-Borel in `[0,1]`" is `¬ MeasurableSet (Subtype.val ⁻¹' S)` for the
  Borel σ-algebra of `↥(Icc 0 1)` (Mathlib's `Subtype.instMeasurableSpace`,
  which `Subtype.borelSpace` identifies with the Borel σ-algebra of the
  subspace topology); `measurableSet_val_preimage_Icc_iff` is the trace
  equivalence with Borelness in `ℝ`, available because `Icc 0 1` itself is
  Borel in `ℝ`.

Density is *not* consumed by the Archimedean chain 3.1–3.9 (audit §2.1); the
theorem exists to cover the printed proposition literally.  The construction
is the densification already used for Proposition 2.2
(`exists_dense_aleph1_nonBorel_cantor`, `Ext/CantorUltra.lean`): adjoin a
countable dense set to the `exists_aleph1_nonBorel` witness and recover
non-Borelness from `T = (T ∪ Q) ∖ (Q ∖ T)`.  No CH, definability or
pointclass hypothesis appears. -/

/-- **The trace equivalence for subsets of `[0,1]`.**  A subset of `Icc 0 1`
is Borel in the space `[0,1]` iff it is Borel in `ℝ`: the Borel σ-algebra of
the subtype is the trace σ-algebra, and `Icc 0 1` is Borel in `ℝ`. -/
theorem measurableSet_val_preimage_Icc_iff {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    MeasurableSet (Subtype.val ⁻¹' S : Set ↥(Set.Icc (0 : ℝ) 1)) ↔ MeasurableSet S := by
  constructor
  · intro h
    have himage : MeasurableSet
        (Subtype.val '' (Subtype.val ⁻¹' S : Set ↥(Set.Icc (0 : ℝ) 1))) :=
      measurableSet_Icc.subtype_image h
    rwa [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hS] at himage
  · intro h
    exact h.preimage measurable_subtype_coe

/-- Density in the space `[0,1]` is the ambient closure statement
`Icc 0 1 ⊆ closure S`. -/
theorem dense_val_preimage_Icc_iff {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    Dense (Subtype.val ⁻¹' S : Set ↥(Set.Icc (0 : ℝ) 1)) ↔
      Set.Icc (0 : ℝ) 1 ⊆ closure S := by
  have himage : Subtype.val '' (Subtype.val ⁻¹' S : Set ↥(Set.Icc (0 : ℝ) 1)) = S := by
    rw [Subtype.image_preimage_coe]
    exact Set.inter_eq_right.mpr hS
  constructor
  · intro hdense x hx
    have hmem := closure_subtype.mp (hdense ⟨x, hx⟩)
    rwa [himage] at hmem
  · intro hsub x
    refine closure_subtype.mpr ?_
    rw [himage]
    exact hsub x.2

/-- **Proposition 2.1** (`prop:dense-aleph1-nonborel-interval`, audit §2.1),
with all four printed clauses: there is an `S ⊆ [0,1]`, dense in `[0,1]`, of
cardinality `ℵ₁`, that is not Borel in `[0,1]`.  Density and non-Borelness
are stated in the space `[0,1]` (see the section comment); the ambient-`ℝ`
reading of both clauses is `exists_dense_aleph1_nonBorel_Icc_ambient`. -/
theorem exists_dense_aleph1_nonBorel_Icc :
    ∃ S ⊆ Set.Icc (0 : ℝ) 1,
      Dense (Subtype.val ⁻¹' S : Set ↥(Set.Icc (0 : ℝ) 1)) ∧
      #(↥S) = Cardinal.aleph 1 ∧
      ¬ MeasurableSet (Subtype.val ⁻¹' S : Set ↥(Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨T, hTsub, hTcard, hTnonmeas⟩ := exists_aleph1_nonBorel
  obtain ⟨Q', hQ'count, hQ'dense⟩ :=
    TopologicalSpace.exists_countable_dense ↥(Set.Icc (0 : ℝ) 1)
  set Q : Set ℝ := Subtype.val '' Q' with hQdef
  have hQcount : Q.Countable := hQ'count.image _
  have hQsub : Q ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hsub : T ∪ Q ⊆ Set.Icc (0 : ℝ) 1 := Set.union_subset hTsub hQsub
  refine ⟨T ∪ Q, hsub, ?_, ?_, ?_⟩
  · -- density: the preimage contains the countable dense set `Q'`.
    refine Dense.mono ?_ hQ'dense
    intro t ht
    exact Or.inr ⟨t, ht, rfl⟩
  · -- cardinality: `ℵ₁ ≤ #(T ∪ Q) ≤ ℵ₁ + ℵ₀ = ℵ₁`.
    refine le_antisymm ?_ ?_
    · calc #(↥(T ∪ Q)) ≤ #(↥T) + #(↥Q) := Cardinal.mk_union_le T Q
        _ ≤ aleph 1 + (ℵ₀ : Cardinal.{0}) :=
            add_le_add hTcard.le (Cardinal.le_aleph0_iff_set_countable.mpr hQcount)
        _ = aleph 1 := Cardinal.add_eq_left (Cardinal.aleph0_le_aleph 1)
            (Cardinal.aleph0_le_aleph 1)
    · calc (aleph 1 : Cardinal.{0}) = #(↥T) := hTcard.symm
        _ ≤ #(↥(T ∪ Q)) := Cardinal.mk_le_mk_of_subset Set.subset_union_left
  · -- non-Borelness in `[0,1]`, via the trace equivalence and
    -- `T = (T ∪ Q) ∖ (Q ∖ T)`.
    rw [measurableSet_val_preimage_Icc_iff hsub]
    intro hmeas
    refine hTnonmeas ?_
    have hQT : ((Q \ T : Set ℝ)).Countable := hQcount.mono Set.sdiff_subset
    have hTeq : T = (T ∪ Q) \ (Q \ T) := by
      ext x
      constructor
      · intro hx
        exact ⟨Or.inl hx, fun hx' => hx'.2 hx⟩
      · rintro ⟨hx, hx'⟩
        rcases hx with hx | hx
        · exact hx
        · by_contra hxT
          exact hx' ⟨hx, hxT⟩
    rw [hTeq]
    exact hmeas.diff hQT.measurableSet

/-- Proposition 2.1 in the ambient-`ℝ` reading: density as
`Icc 0 1 ⊆ closure S` and non-Borelness in `ℝ`, equivalent to the subtype
statements by `dense_val_preimage_Icc_iff` and
`measurableSet_val_preimage_Icc_iff`. -/
theorem exists_dense_aleph1_nonBorel_Icc_ambient :
    ∃ S ⊆ Set.Icc (0 : ℝ) 1,
      Set.Icc (0 : ℝ) 1 ⊆ closure S ∧
      #(↥S) = Cardinal.aleph 1 ∧
      ¬ MeasurableSet S := by
  obtain ⟨S, hSsub, hSdense, hScard, hSnonmeas⟩ := exists_dense_aleph1_nonBorel_Icc
  exact ⟨S, hSsub, (dense_val_preimage_Icc_iff hSsub).mp hSdense, hScard,
    fun h => hSnonmeas ((measurableSet_val_preimage_Icc_iff hSsub).mpr h)⟩

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
