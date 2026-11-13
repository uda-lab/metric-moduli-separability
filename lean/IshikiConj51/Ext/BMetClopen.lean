-- Ext.BMetClopen
--
-- Issue #96, scope item 2: Lemma 3.2's closedness clause relative to `Met(Z)`.
--
-- Statement gate (frozen audit record): `notes/borel-preprint-audit.md` §2.5 (Lemma
-- 3.2, whose printed closedness clause is "`Φ([0,1] ∖ S)` is closed in
-- `Met(Z)`") and §1 (the component conventions; "each class is clopen in
-- `Met(Z)`" is recalled there).
--
-- `Ext/BoundedCoding.lean` delivers the closedness clause relative to the
-- bounded locus (`isClosed_image_phiFull`, in the `BddPMet` ambient).  The
-- bridge to the printed `Met(Z)`-relative clause is the elementary
-- finite-sup-distance fact suggested by the issue: a member of `Met(Z)` is
-- bounded exactly when it is at finite `𝒟`-distance from a bounded member
-- (`CPM.isBdd_iff_edist_lt_top`), so `BMet(Z)` is precisely the
-- finite-sup-distance component of the `0/1` metric
-- (`CPM.BMet_eq_component_discrete`) and hence clopen in `Met(Z)`
-- (`CPM.isClopen_val_preimage_BMet`): relative closedness in `BMet(Z)`
-- transfers to relative closedness in `Met(Z)`
-- (`isClosed_val_preimage_Met_of_isClosed_val_preimage_BMet`).
--
-- The `BMet`-relative input is re-derived at `CPM` level from compactness of
-- the range of `Φ_full` (`isClosed_range_phiFullCPM`), the same argument that
-- proves `isClosed_range_phiFull` in the bounded ambient; nothing of the
-- Theorem 3.4 component development (`Ext/Component.lean`) is duplicated —
-- only its `CPM.component` vocabulary is reused.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.Component
import IshikiConj51.Ext.CompleteMetrizability

open Set
open scoped ENNReal

namespace IshikiExt

noncomputable section

variable {Z : Type*}

/-! ## Boundedness is finite sup-distance from a bounded base metric -/

/-- The `0/1` metric is bounded. -/
theorem CPM.isBdd_discrete (Z : Type*) : (CPM.discrete Z).IsBdd := by
  refine ⟨1, fun x y => ?_⟩
  by_cases h : x = y
  · rw [h]
    show discreteFn Z y y ≤ 1
    rw [discreteFn_self]
    norm_num
  · show discreteFn Z x y ≤ 1
    rw [discreteFn_of_ne h]

/-- **Boundedness is exactly finite sup-distance from a bounded base metric.**
For a bounded `d`, a pseudometric `e` is bounded iff `𝒟_Z(d,e) < ∞`. -/
theorem CPM.isBdd_iff_edist_lt_top {d e : CPM Z} (hd : d.IsBdd) :
    e.IsBdd ↔ CPM.edist d e < ⊤ := by
  obtain ⟨C, hC⟩ := hd
  constructor
  · rintro ⟨E, hE⟩
    refine lt_of_le_of_lt (CPM.edist_le_ofReal (c := C + E) fun x y => ?_)
      ENNReal.ofReal_lt_top
    rw [abs_sub_le_iff]
    constructor <;> linarith [hC x y, hE x y, d.2.nonneg x y, e.2.nonneg x y]
  · intro h
    refine ⟨C + (CPM.edist d e).toReal, fun x y => ?_⟩
    have hpt : ENNReal.ofReal |d.1 x y - e.1 x y| ≤ CPM.edist d e :=
      CPM.ofReal_abs_sub_le_edist d e x y
    have habs : |d.1 x y - e.1 x y| ≤ (CPM.edist d e).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal h.ne).mp hpt
    have hpair := abs_le.mp habs
    linarith [hC x y, hpair.1]

/-- **`BMet(Z)` is the finite-sup-distance component of the `0/1` metric.**
This identifies the bounded compatible locus with a `∼`-class in the sense of
audit §1, through the `CPM.component` vocabulary of `Ext/Component.lean`. -/
theorem CPM.BMet_eq_component_discrete (Z : Type*) :
    CPM.BMet Z = CPM.component (CPM.discrete Z) := by
  ext d
  rw [CPM.mem_BMet_iff]
  show d ∈ CPM.Met Z ∧ d.IsBdd ↔ d ∈ CPM.Met Z ∧ CPM.edist (CPM.discrete Z) d < ⊤
  exact and_congr_right fun _ => CPM.isBdd_iff_edist_lt_top (CPM.isBdd_discrete Z)

/-- The issue's phrasing: the bounded compatible metrics form the component
containing any bounded compatible metric. -/
theorem CPM.component_eq_BMet_of_mem {d : CPM Z} (hd : d ∈ CPM.BMet Z) :
    CPM.component d = CPM.BMet Z := by
  rw [CPM.BMet_eq_component_discrete] at hd ⊢
  exact CPM.component_eq_of_mem hd

/-! ## `BMet(Z)` is clopen in `Met(Z)` -/

/-- In any extended pseudometric space, the points at finite distance from a
fixed point form a clopen set: both the set and its complement absorb the
`edist`-ball of radius `1` around each of their points. -/
theorem isClopen_setOf_edist_lt_top {X : Type*} [PseudoEMetricSpace X] (x : X) :
    IsClopen {y : X | edist x y < ⊤} := by
  constructor
  · rw [← isOpen_compl_iff, EMetric.isOpen_iff]
    intro y hy
    refine ⟨1, one_pos, fun z hz hzmem => hy ?_⟩
    have hzy : edist z y < ⊤ := lt_of_lt_of_le (Metric.mem_eball.mp hz) le_top
    calc edist x y ≤ edist x z + edist z y := edist_triangle x z y
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hzmem, hzy⟩
  · rw [EMetric.isOpen_iff]
    intro y hy
    refine ⟨1, one_pos, fun z hz => ?_⟩
    have hyz : edist y z < ⊤ := by
      rw [edist_comm]
      exact lt_of_lt_of_le (Metric.mem_eball.mp hz) le_top
    calc edist x z ≤ edist x y + edist y z := edist_triangle x y z
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hy, hyz⟩

/-- The finite-distance locus of a fixed pseudometric is clopen in the ambient
`CPM(Z)`. -/
theorem CPM.isClopen_setOf_edist_lt_top (d : CPM Z) :
    IsClopen {e : CPM Z | CPM.edist d e < ⊤} :=
  IshikiExt.isClopen_setOf_edist_lt_top d

/-- **`BMet(Z)` is clopen in `Met(Z)`** (audit §1's "each class is clopen",
for the class that `BMet(Z)` is): the trace of the bounded locus on the
subspace `Met(Z)` is the trace of the clopen finite-distance locus of the
`0/1` metric. -/
theorem CPM.isClopen_val_preimage_BMet (Z : Type*) :
    IsClopen (Subtype.val ⁻¹' CPM.BMet Z : Set ↥(CPM.Met Z)) := by
  have heq : (Subtype.val ⁻¹' CPM.BMet Z : Set ↥(CPM.Met Z))
      = Subtype.val ⁻¹' {e : CPM Z | CPM.edist (CPM.discrete Z) e < ⊤} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [CPM.BMet_eq_component_discrete]
    exact ⟨fun h => h.2, fun h => ⟨d.2, h⟩⟩
  rw [heq]
  exact (CPM.isClopen_setOf_edist_lt_top (CPM.discrete Z)).preimage
    continuous_subtype_val

/-- **The transfer.**  A subset of `BMet(Z)` that is closed relative to
`BMet(Z)` is closed relative to `Met(Z)`: intersect a closed ambient witness
with the closed finite-distance locus, whose trace on `Met(Z)` is exactly
`BMet(Z)`. -/
theorem isClosed_val_preimage_Met_of_isClosed_val_preimage_BMet
    {W : Set (CPM Z)} (hWsub : W ⊆ CPM.BMet Z)
    (hW : IsClosed (Subtype.val ⁻¹' W : Set ↥(CPM.BMet Z))) :
    IsClosed (Subtype.val ⁻¹' W : Set ↥(CPM.Met Z)) := by
  obtain ⟨C, hCclosed, hCpre⟩ := isClosed_induced_iff.mp hW
  have hCB : CPM.BMet Z ∩ C = W := by
    have h1 : Subtype.val '' (Subtype.val ⁻¹' C : Set ↥(CPM.BMet Z))
        = Subtype.val '' (Subtype.val ⁻¹' W : Set ↥(CPM.BMet Z)) := by rw [hCpre]
    rwa [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      Set.inter_eq_right.mpr hWsub] at h1
  refine isClosed_induced_iff.mpr
    ⟨C ∩ {e : CPM Z | CPM.edist (CPM.discrete Z) e < ⊤},
      hCclosed.inter (CPM.isClopen_setOf_edist_lt_top (CPM.discrete Z)).isClosed, ?_⟩
  ext d
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hdC, hdF⟩
    have hdB : (d : CPM Z) ∈ CPM.BMet Z := by
      rw [CPM.BMet_eq_component_discrete]
      exact ⟨d.2, hdF⟩
    rw [← hCB]
    exact ⟨hdB, hdC⟩
  · intro hdW
    have hdB : (d : CPM Z) ∈ CPM.BMet Z := hWsub hdW
    have hdC : (d : CPM Z) ∈ C := by
      rw [← hCB] at hdW
      exact hdW.2
    refine ⟨hdC, ?_⟩
    rw [CPM.BMet_eq_component_discrete] at hdB
    exact hdB.2

/-! ## Lemma 3.2 in `Met(Z)` -/

/-- The bounded-locus pullback identity of `Ext/BoundedCoding.lean`, read at
`CPM` level: `Φ_full⁻¹(BMet(Z)) = {t ∈ [0,1] : t ∉ S}`. -/
theorem preimage_CPM_BMet_phiFull {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    phiFullCPM S hS ⁻¹' CPM.BMet (ExtIndex S) = {t : UnitParam | (t : ℝ) ∉ S} := by
  have hcomp : phiFullCPM S hS ⁻¹' CPM.BMet (ExtIndex S)
      = phiFull S hS ⁻¹' (BddPMet.toCPM ⁻¹' CPM.BMet (ExtIndex S)) := rfl
  rw [hcomp, preimage_CPM_BMet_toCPM, preimage_BMet_phiFull]

/-- `Φ_full` has compact, hence closed, range in the ambient `CPM(Z)`:
`[0,1]` is compact and `Φ_full` is continuous, as in
`isClosed_range_phiFull`. -/
theorem isClosed_range_phiFullCPM {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    IsClosed (Set.range (phiFullCPM S hS)) :=
  (isCompact_range (continuous_phiFullCPM hS)).isClosed

/-- The image of `[0,1] ∖ S` is the part of the range in the bounded locus. -/
theorem image_compl_eq_range_inter_CPM_BMet {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    phiFullCPM S hS '' {t : UnitParam | (t : ℝ) ∉ S}
      = Set.range (phiFullCPM S hS) ∩ CPM.BMet (ExtIndex S) := by
  rw [← preimage_CPM_BMet_phiFull hS, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The trace identity of audit §2.5 at `CPM` level: on the range of `Φ_full`
the metric and the bounded loci cut out the same set, `Φ_full([0,1] ∖ S)`. -/
theorem image_compl_eq_range_inter_CPM_Met {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    phiFullCPM S hS '' {t : UnitParam | (t : ℝ) ∉ S}
      = Set.range (phiFullCPM S hS) ∩ CPM.Met (ExtIndex S) := by
  rw [← preimage_CPM_Met_phiFull hS, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- `Φ_full([0,1] ∖ S)` is closed in `BMet(Z)`, at `CPM` level — the
`CPM`-ambient form of `isClosed_image_phiFull`. -/
theorem isClosed_image_phiFullCPM_bmet {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    IsClosed (Subtype.val ⁻¹' (phiFullCPM S hS '' {t : UnitParam | (t : ℝ) ∉ S}) :
      Set ↥(CPM.BMet (ExtIndex S))) := by
  rw [image_compl_eq_range_inter_CPM_BMet hS]
  have hpre : (Subtype.val ⁻¹' (Set.range (phiFullCPM S hS) ∩ CPM.BMet (ExtIndex S)) :
      Set ↥(CPM.BMet (ExtIndex S))) = Subtype.val ⁻¹' Set.range (phiFullCPM S hS) := by
    ext d
    simp
  rw [hpre]
  exact (isClosed_range_phiFullCPM hS).preimage continuous_subtype_val

/-- **Lemma 3.2, closedness clause, literally** (audit §2.5):
`Φ_full([0,1] ∖ S)` is closed in `Met(Z)` with its subspace topology, in the
preprint's unbounded ambient `CPM(Z)`.  The proof is the issue's route: the
`BMet(Z)`-relative closedness (`isClosed_image_phiFullCPM_bmet`) transfers to
`Met(Z)` because `BMet(Z)` is clopen in `Met(Z)`
(`CPM.isClopen_val_preimage_BMet`, via
`isClosed_val_preimage_Met_of_isClosed_val_preimage_BMet`). -/
theorem isClosed_image_phiFullCPM_met {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    IsClosed (Subtype.val ⁻¹' (phiFullCPM S hS '' {t : UnitParam | (t : ℝ) ∉ S}) :
      Set ↥(CPM.Met (ExtIndex S))) := by
  refine isClosed_val_preimage_Met_of_isClosed_val_preimage_BMet ?_
    (isClosed_image_phiFullCPM_bmet hS)
  rw [image_compl_eq_range_inter_CPM_BMet hS]
  exact Set.inter_subset_right

end

end IshikiExt
