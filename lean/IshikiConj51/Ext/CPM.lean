-- Ext.CPM
--
-- Issue #56, item 3: the ambient-faithfulness layer for the Ishiki
-- extension. `CPM D` is the unbounded pseudometric ambient corresponding to
-- the preprint's continuous-pseudometric space on a discrete carrier.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §7 item 3.
-- Since the carrier is discrete, continuity is vacuous; `CPM` records the
-- pseudometric content without adding a misleading continuity field.  For a
-- general topological space the preprint's ambient is strictly smaller, and
-- `CPM X` must not be substituted for it: see `CPMOn` in
-- `Ext/GeneralSeparability.lean`.
--
-- This file also carries the completeness of the ambient (audit §2.8, the
-- "uniform limits of pseudometrics" step), which the general-space transfer
-- needs in order to conclude that an isometric image of `CPM D` is closed.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Borel

open Cardinal Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

/-! ## The unbounded pseudometric ambient -/

/-- A finite-valued pseudometric on `D`, stated for a bare function. -/
structure IsPMetricOn {D : Type*} (d : D → D → ℝ) : Prop where
  dist_self : ∀ x, d x x = 0
  dist_comm : ∀ x y, d x y = d y x
  dist_triangle : ∀ x y z, d x z ≤ d x y + d y z

theorem IsPMetricOn.nonneg {D : Type*} {d : D → D → ℝ}
    (h : IsPMetricOn d) (x y : D) : 0 ≤ d x y := by
  have htri := h.dist_triangle x y x
  rw [h.dist_self x, h.dist_comm y x] at htri
  linarith

/-- `CPM D`: arbitrary finite-valued pseudometrics on `D`. -/
def CPM (D : Type*) : Type _ := {d : D → D → ℝ // IsPMetricOn d}

namespace CPM

variable {D : Type*}

/-- The extended supremum distance on the unbounded pseudometric ambient. -/
noncomputable def edist (d e : CPM D) : ℝ≥0∞ :=
  ⨆ p : D × D, ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2|

theorem edist_self (d : CPM D) : edist d d = 0 := by
  simp [edist]

theorem edist_comm (d e : CPM D) : edist d e = edist e d := by
  simp only [edist, abs_sub_comm]

theorem edist_triangle (d e f : CPM D) : edist d f ≤ edist d e + edist e f := by
  apply iSup_le
  intro p
  calc ENNReal.ofReal |d.1 p.1 p.2 - f.1 p.1 p.2|
      ≤ ENNReal.ofReal (|d.1 p.1 p.2 - e.1 p.1 p.2| +
          |e.1 p.1 p.2 - f.1 p.1 p.2|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2| +
          ENNReal.ofReal |e.1 p.1 p.2 - f.1 p.1 p.2| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ edist d e + edist e f :=
        add_le_add
          (le_iSup (fun q : D × D => ENNReal.ofReal
            |d.1 q.1 q.2 - e.1 q.1 q.2|) p)
          (le_iSup (fun q : D × D => ENNReal.ofReal
            |e.1 q.1 q.2 - f.1 q.1 q.2|) p)

theorem eq_of_edist_eq_zero {d e : CPM D} (h : edist d e = 0) : d = e := by
  have hpt : ∀ p : D × D, ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2| = 0 :=
    ENNReal.iSup_eq_zero.mp h
  apply Subtype.ext
  funext x y
  have hxy := hpt (x, y)
  rw [ENNReal.ofReal_eq_zero] at hxy
  have hnn : 0 ≤ |d.1 x y - e.1 x y| := abs_nonneg _
  have habs0 : |d.1 x y - e.1 x y| = 0 := le_antisymm hxy hnn
  have hsub0 : d.1 x y - e.1 x y = 0 := abs_eq_zero.mp habs0
  linarith

noncomputable instance : EDist (CPM D) := ⟨edist⟩

noncomputable instance : PseudoEMetricSpace (CPM D) where
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle

noncomputable instance : EMetricSpace (CPM D) where
  eq_of_edist_eq_zero := eq_of_edist_eq_zero

/-! ### Pointwise control by the extended supremum distance -/

/-- Evaluation at a single pair is dominated by the supremum distance. -/
theorem ofReal_abs_sub_le_edist (d e : CPM D) (x y : D) :
    ENNReal.ofReal |d.1 x y - e.1 x y| ≤ edist d e :=
  le_iSup (fun p : D × D => ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2|) (x, y)

theorem abs_sub_lt_of_edist_lt {d e : CPM D} {c : ℝ} (hc : 0 < c)
    (h : edist d e < ENNReal.ofReal c) (x y : D) : |d.1 x y - e.1 x y| < c :=
  (ENNReal.ofReal_lt_ofReal_iff hc).mp
    (lt_of_le_of_lt (ofReal_abs_sub_le_edist d e x y) h)

theorem edist_le_ofReal {d e : CPM D} {c : ℝ}
    (h : ∀ x y : D, |d.1 x y - e.1 x y| ≤ c) : edist d e ≤ ENNReal.ofReal c :=
  iSup_le fun p => ENNReal.ofReal_le_ofReal (h p.1 p.2)

/-! ### Completeness

The supremum distance is a uniform distance, so a Cauchy sequence of
pseudometrics converges pointwise and its pointwise limit is again a
pseudometric.  This is the "uniform limits of pseudometrics" step of
`notes/borel-preprint-audit.md` §2.8, which the general-space transfer needs in
order to conclude that an isometric image of `CPM D` is closed. -/

noncomputable instance instCompleteSpace : CompleteSpace (CPM D) := by
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  -- Each pair of points gives a Cauchy sequence of reals.
  have hptCauchy : ∀ x y : D, CauchySeq fun n => (u n).1 x y := by
    intro x y
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      EMetric.cauchySeq_iff.mp hu (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa [Real.dist_eq] using abs_sub_lt_of_edist_lt hε (hN m hm n hn) x y
  choose dinf hdinf using fun x y : D =>
    cauchySeq_tendsto_of_complete (hptCauchy x y)
  -- The pointwise limit is again a pseudometric.
  have hpm : IsPMetricOn dinf := by
    refine ⟨fun x => ?_, fun x y => ?_, fun x y z => ?_⟩
    · refine tendsto_nhds_unique (hdinf x x) ?_
      have hconst : (fun n => (u n).1 x x) = fun _ : ℕ => (0 : ℝ) :=
        funext fun n => (u n).2.dist_self x
      rw [hconst]
      exact tendsto_const_nhds
    · refine tendsto_nhds_unique (hdinf x y) ?_
      have hswap : (fun n => (u n).1 x y) = fun n => (u n).1 y x :=
        funext fun n => (u n).2.dist_comm x y
      rw [hswap]
      exact hdinf y x
    · exact le_of_tendsto_of_tendsto' (hdinf x z) ((hdinf x y).add (hdinf y z))
        fun n => (u n).2.dist_triangle x y z
  refine ⟨⟨dinf, hpm⟩, ?_⟩
  -- Uniform convergence: let the second index of the Cauchy modulus tend to `∞`.
  rw [EMetric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have hr : (0 : NNReal) < r := ENNReal.coe_pos.mp hr0
    exact_mod_cast hr
  have hhalf : (0 : ℝ) < (r : ℝ) / 2 := by linarith
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu (ENNReal.ofReal ((r : ℝ) / 2))
    (ENNReal.ofReal_pos.mpr hhalf)
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ∀ x y : D, |(u n).1 x y - dinf x y| ≤ (r : ℝ) / 2 := by
    intro x y
    refine le_of_tendsto
      ((tendsto_const_nhds.sub (hdinf x y)).abs) (Filter.eventually_atTop.mpr ⟨N, ?_⟩)
    intro m hm
    exact le_of_lt (abs_sub_lt_of_edist_lt hhalf (hN n hn m hm) x y)
  refine lt_of_le_of_lt (edist_le_ofReal hbound) (lt_of_lt_of_le ?_ (le_of_lt hrε))
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr (by linarith)

end CPM

/-! ## The bounded ambient inside `CPM` -/

/-- The canonical inclusion of bounded pseudometrics into `CPM`. -/
def BddPMet.toCPM (d : BddPMet D) : CPM D :=
  ⟨d.1, ⟨d.2.dist_self, d.2.dist_comm, d.2.dist_triangle⟩⟩

@[simp] theorem BddPMet.toCPM_coe (d : BddPMet D) : (d.toCPM).1 = d.1 := rfl

local instance cpmBddPMetMeasurableSpace (D : Type*) : MeasurableSpace (BddPMet D) :=
  borel (BddPMet D)

local instance cpmBddPMetBorelSpace (D : Type*) : BorelSpace (BddPMet D) :=
  ⟨rfl⟩

local instance cpmMeasurableSpace (D : Type*) : MeasurableSpace (CPM D) :=
  borel (CPM D)

local instance cpmBorelSpace (D : Type*) : BorelSpace (CPM D) :=
  ⟨rfl⟩

/-- The extended sup distance agrees with the real supremum distance on the
bounded ambient. -/
theorem edist_toCPM_eq_ofReal_supDist {D : Type*} (d e : BddPMet D) :
    CPM.edist d.toCPM e.toCPM = ENNReal.ofReal (BddPMet.supDist d e) := by
  obtain ⟨C, hC0, hC⟩ := d.2.exists_bound
  obtain ⟨E, hE0, hE⟩ := e.2.exists_bound
  change (⨆ p : D × D, ENNReal.ofReal
      |d.1 p.1 p.2 - e.1 p.1 p.2|) = ENNReal.ofReal
      (⨆ p : D × D, |d.1 p.1 p.2 - e.1 p.1 p.2|)
  have hbound : ∀ p : D × D, |d.1 p.1 p.2 - e.1 p.1 p.2| ≤ C + E := by
    intro p
    rw [abs_sub_le_iff]
    constructor <;> linarith [hC p.1 p.2, hE p.1 p.2,
      d.2.nonneg p.1 p.2, e.2.nonneg p.1 p.2]
  have hupper : (⨆ p : D × D, ENNReal.ofReal
      |d.1 p.1 p.2 - e.1 p.1 p.2|) ≤ ENNReal.ofReal (C + E) := by
    apply iSup_le
    intro p
    exact ENNReal.ofReal_le_ofReal (hbound p)
  have hfinite : (⨆ p : D × D, ENNReal.ofReal
      |d.1 p.1 p.2 - e.1 p.1 p.2|) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hupper ENNReal.ofReal_lt_top)
  have hto : ((⨆ p : D × D, ENNReal.ofReal
      |d.1 p.1 p.2 - e.1 p.1 p.2|).toReal) =
      ⨆ p : D × D, |d.1 p.1 p.2 - e.1 p.1 p.2| := by
    rw [ENNReal.toReal_iSup]
    · congr 1
      funext p
      rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    · intro p
      exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfinite, hto]

/-- The inclusion of bounded pseudometrics is an isometry for the extended
sup distances. -/
theorem isometry_toCPM {D : Type*} : Isometry (BddPMet.toCPM : BddPMet D → CPM D) := by
  intro d e
  change CPM.edist d.toCPM e.toCPM = edist d e
  rw [edist_toCPM_eq_ofReal_supDist, edist_dist, BddPMet.dist_eq_supDist]

/-- A Borel set in `CPM D` pulls back to a Borel set in `BddPMet D`. -/
theorem measurableSet_preimage_toCPM {D : Type*} {A : Set (CPM D)}
    (hA : MeasurableSet A) :
    MeasurableSet (BddPMet.toCPM ⁻¹' A) := by
  exact hA.preimage (isometry_toCPM (D := D)).continuous.measurable

/-! ## The two ambient non-Borelness corollaries -/

/-- The bounded compatible-metric locus, viewed inside the unbounded ambient. -/
def CPM.BMet (D : Type*) : Set (CPM D) := BddPMet.toCPM '' IshikiExt.BMet D

theorem preimage_CPM_BMet_toCPM {D : Type*} :
    BddPMet.toCPM ⁻¹' CPM.BMet D = BMet D := by
  ext d
  constructor
  · rintro ⟨e, he, hde⟩
    have hed : e = d := (isometry_toCPM (D := D)).injective hde
    simpa [hed] using he
  · intro hd
    exact ⟨d, hd, rfl⟩

/-- The bounded compatible-metric locus is non-Borel even in the larger
unbounded pseudometric ambient. -/
theorem bmet_not_borel_cpm {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hScard : #(↥S) = Cardinal.aleph 1) (hSnonmeas : ¬ MeasurableSet S) :
    ¬ MeasurableSet (CPM.BMet (ExtIndex S)) := by
  intro hBMet
  have hpull : MeasurableSet
      (BddPMet.toCPM ⁻¹' CPM.BMet (ExtIndex S)) :=
    measurableSet_preimage_toCPM hBMet
  rw [preimage_CPM_BMet_toCPM] at hpull
  exact bmet_not_borel hS hScard hSnonmeas hpull

/-! ## The unbounded compatible-metric locus -/

/-- The preprint's unbounded `Met(D)` locus inside `CPM D`. -/
def CPM.Met (D : Type*) : Set (CPM D) :=
  {d | ∃ h : IsMetricOn d.1, h.topology = ⊥}

def phiFullCPM (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    UnitParam → CPM (ExtIndex S) :=
  BddPMet.toCPM ∘ phiFull S hS

theorem continuous_phiFullCPM {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    Continuous (phiFullCPM S hS) :=
  (isometry_toCPM (D := ExtIndex S)).continuous.comp
    (lipschitzWith_phiFull S hS).continuous

/-- The unbounded compatible-metric locus has the same parameter pullback as
the bounded locus. -/
theorem preimage_CPM_Met_phiFull {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    phiFullCPM S hS ⁻¹' CPM.Met (ExtIndex S) =
      {t : UnitParam | (t : ℝ) ∉ S} := by
  ext t
  change (∃ h : IsMetricOn (phiFull S hS t).1, h.topology = ⊥) ↔
    (t : ℝ) ∉ S
  simpa [IsCompatible] using dExt_isCompatible_iff S hS t

/-- The literal unbounded `Met(ExtIndex S)` locus is non-Borel in
`CPM(ExtIndex S)`, for the coded carrier of the parameter set `S`. The
arbitrary-carrier form is `met_not_borel_of_card` (`Ext/Relabel.lean`). -/
theorem met_not_borel {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hSnonmeas : ¬ MeasurableSet S) :
    ¬ MeasurableSet (CPM.Met (ExtIndex S)) := by
  intro hMet
  have hpre : MeasurableSet
      (phiFullCPM S hS ⁻¹' CPM.Met (ExtIndex S)) :=
    hMet.preimage (continuous_phiFullCPM hS).measurable
  have himage : MeasurableSet
      (Subtype.val '' (phiFullCPM S hS ⁻¹' CPM.Met (ExtIndex S))) :=
    measurableSet_Icc.subtype_image hpre
  rw [preimage_CPM_Met_phiFull hS] at himage
  have himage_eq :
      Subtype.val '' {t : UnitParam | (t : ℝ) ∉ S} = Set.Icc (0 : ℝ) 1 \ S := by
    ext x
    constructor
    · rintro ⟨t, htS, rfl⟩
      exact ⟨t.2, htS⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, hx2, rfl⟩
  rw [himage_eq] at himage
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
