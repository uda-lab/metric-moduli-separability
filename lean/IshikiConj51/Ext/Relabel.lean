-- Ext.Relabel
--
-- Transport of the Ishiki-extension ambients along a bijection of the
-- underlying discrete carrier, and the arbitrary-carrier form of the
-- Borel obstruction.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §7 item 4
-- (Issue #63).  The theorems of Issue #56 (`bmet_not_borel`,
-- `bmet_not_borel_cpm`, `met_not_borel`) are stated for the *concrete*
-- carrier `ExtIndex S` produced by the bounded star coding, whereas the
-- preprint's Theorem 3.3 and its abstract quantify over *every* discrete set
-- of cardinality `ℵ₁`.  Both ambients depend on the carrier only through its
-- cardinality: a bijection `σ : D ≃ E` relabels (pseudo)metrics, preserves
-- the pseudometric axioms, the boundedness, the metric axioms and the
-- discreteness of the induced topology, and preserves the supremum distance
-- *exactly* — the supremum is taken over `D × D`, which `σ × σ` reindexes
-- bijectively.  Hence `BddPMet E ≃ᵢ BddPMet D` and `CPM E ≃ᵢ CPM D`, carrying
-- `BMet` to `BMet` and `Met` to `Met`.
--
-- This mirrors `Conj51/Relabel.lean`, which performs the same transport for
-- `MetD` (the unbounded metric ambient of the Conjecture 5.1 track) and is
-- consumed by `thm_conj51` for exactly this purpose.  The `MetD` supremum
-- distance is `ℝ≥0∞`-valued, so its reindexing step is `Equiv.iSup_comp` in a
-- complete lattice; `BddPMet.supDist` is real-valued and only
-- *conditionally* complete, so the corresponding step here is done by
-- antisymmetry from the repository's own `le_supDist` / `supDist_le` pair.
--
-- Discreteness of the carrier is not an instance hypothesis anywhere below,
-- exactly as in `Conj51/MainTheorem.lean`: membership in `BMet D` and in
-- `CPM.Met D` is the condition `IsMetricOn.topology = ⊥`, i.e. "this metric
-- induces the discrete topology", which is what "compatible with the
-- discrete topology on `D`" means.  No separate topology on `D` is involved.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.CPM

open Cardinal Set

namespace IshikiExt

noncomputable section

variable {D E : Type*}

/-! ## Transport of the compatibility condition

`BMet D` and `CPM.Met D` are both cut out by the same predicate on the
underlying function: it satisfies the metric axioms and the topology it
induces is discrete.  The two lemmas below transport that predicate, and
`exists_isMetricOn_comap_iff` packages them as an iff, which is what the
membership statements for both ambients need. -/

/-- Relabelling a metric along a bijection again satisfies the metric axioms.
Separation is the only clause needing anything beyond composition: `σ` is
injective. -/
theorem isMetricOn_comap (σ : D ≃ E) {d : E → E → ℝ} (h : IsMetricOn d) :
    IsMetricOn fun x y => d (σ x) (σ y) where
  dist_self _ := h.dist_self _
  eq_of_dist_eq_zero hxy := σ.injective (h.eq_of_dist_eq_zero hxy)
  dist_comm _ _ := h.dist_comm _ _
  dist_triangle _ _ _ := h.dist_triangle _ _ _

/-- Relabelling preserves discreteness of the induced topology: the isolating
radius of `σ u` serves as the isolating radius of `u`. -/
theorem topology_comap_eq_bot (σ : D ≃ E) {d : E → E → ℝ} (h : IsMetricOn d)
    (hbot : h.topology = ⊥) : (isMetricOn_comap σ h).topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  intro u
  obtain ⟨ε, hε, hall⟩ := h.topology_eq_bot_iff.mp hbot (σ u)
  exact ⟨ε, hε, fun v hv => σ.injective (hall (σ v) hv)⟩

/-- The converse of `isMetricOn_comap`.  It is proved directly, by evaluating
at `σ.symm`, rather than by relabelling twice along `σ` and `σ.symm`: the
double relabelling is only *propositionally* the original function, and
rewriting under `IsMetricOn.topology` — which is `implicit_reducible` and
unfolds to a whole `UniformSpace` — is expensive enough to exhaust the
elaborator's heartbeat budget. -/
theorem isMetricOn_of_comap (σ : D ≃ E) {d : E → E → ℝ}
    (h : IsMetricOn fun x y => d (σ x) (σ y)) : IsMetricOn d where
  dist_self x := by simpa using h.dist_self (σ.symm x)
  eq_of_dist_eq_zero {x y} hxy := by
    refine σ.symm.injective (h.eq_of_dist_eq_zero (x := σ.symm x) (y := σ.symm y) ?_)
    simpa using hxy
  dist_comm x y := by simpa using h.dist_comm (σ.symm x) (σ.symm y)
  dist_triangle x y z := by
    simpa using h.dist_triangle (σ.symm x) (σ.symm y) (σ.symm z)

theorem topology_eq_bot_of_comap (σ : D ≃ E) {d : E → E → ℝ}
    (h : IsMetricOn fun x y => d (σ x) (σ y)) (hbot : h.topology = ⊥) :
    (isMetricOn_of_comap σ h).topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  intro u
  obtain ⟨ε, hε, hall⟩ := h.topology_eq_bot_iff.mp hbot (σ.symm u)
  refine ⟨ε, hε, fun v hv => σ.symm.injective (hall (σ.symm v) ?_)⟩
  simpa using hv

/-- Compatibility with the discrete topology is invariant under relabelling. -/
theorem exists_isMetricOn_comap_iff (σ : D ≃ E) (d : E → E → ℝ) :
    (∃ h : IsMetricOn fun x y => d (σ x) (σ y), h.topology = ⊥) ↔
      ∃ h : IsMetricOn d, h.topology = ⊥ :=
  ⟨fun ⟨h, hbot⟩ => ⟨isMetricOn_of_comap σ h, topology_eq_bot_of_comap σ h hbot⟩,
    fun ⟨h, hbot⟩ => ⟨isMetricOn_comap σ h, topology_comap_eq_bot σ h hbot⟩⟩

/-! ## Relabelling the bounded ambient `BCPM(D)` -/

namespace BddPMet

/-- Relabelling along `σ : D ≃ E` pulls a bounded pseudometric on `E` back to
one on `D`; the same constant bounds it. -/
def comap (σ : D ≃ E) (d : BddPMet E) : BddPMet D :=
  ⟨fun x y => d.1 (σ x) (σ y),
    { dist_self := fun _ => d.2.dist_self _
      dist_comm := fun _ _ => d.2.dist_comm _ _
      dist_triangle := fun _ _ _ => d.2.dist_triangle _ _ _
      bounded := by
        obtain ⟨C, hC⟩ := d.2.bounded
        exact ⟨C, fun _ _ => hC _ _⟩ }⟩

@[simp] theorem comap_val (σ : D ≃ E) (d : BddPMet E) :
    (comap σ d).1 = fun x y => d.1 (σ x) (σ y) := rfl

/-- Relabelling preserves the supremum distance exactly.  Both inequalities
are the same reindexing argument, run through `σ` in one direction and
`σ.symm` in the other; the supremum here is a conditional supremum of a real
bounded family, so it is obtained from `le_supDist`/`supDist_le` rather than
from a complete-lattice reindexing lemma. -/
theorem supDist_comap (σ : D ≃ E) (d e : BddPMet E) :
    supDist (comap σ d) (comap σ e) = supDist d e := by
  refine le_antisymm (supDist_le (supDist_nonneg d e) fun u v => ?_)
    (supDist_le (supDist_nonneg _ _) fun u v => ?_)
  · exact le_supDist d e (σ u) (σ v)
  · simpa using le_supDist (comap σ d) (comap σ e) (σ.symm u) (σ.symm v)

theorem isometry_comap (σ : D ≃ E) : Isometry (comap σ : BddPMet E → BddPMet D) :=
  Isometry.of_dist_eq fun d e => supDist_comap σ d e

/-- `BCPM(E) ≃ BCPM(D)` for any bijection `σ : D ≃ E`. -/
def relabelEquiv (σ : D ≃ E) : BddPMet E ≃ BddPMet D where
  toFun := comap σ
  invFun := comap σ.symm
  left_inv _ := Subtype.ext (by funext x y; simp)
  right_inv _ := Subtype.ext (by funext x y; simp)

@[simp] theorem relabelEquiv_apply (σ : D ≃ E) (d : BddPMet E) :
    relabelEquiv σ d = comap σ d := rfl

/-- The relabelling bijection is an isometry of the supremum distance, hence a
homeomorphism `BCPM(E) ≃ₜ BCPM(D)`. -/
def relabelIsometry (σ : D ≃ E) : BddPMet E ≃ᵢ BddPMet D where
  toEquiv := relabelEquiv σ
  isometry_toFun := isometry_comap σ

end BddPMet

/-- Relabelling preserves membership in `BMet`, in both directions. -/
theorem isCompatible_comap_iff (σ : D ≃ E) (d : BddPMet E) :
    IsCompatible (BddPMet.comap σ d) ↔ IsCompatible d :=
  exists_isMetricOn_comap_iff σ d.1

theorem preimage_BMet_comap (σ : D ≃ E) :
    BddPMet.comap σ ⁻¹' BMet D = BMet E := by
  ext d
  exact isCompatible_comap_iff σ d

/-! ## Relabelling the unbounded ambient `CPM(D)` -/

namespace CPM

/-- Relabelling along `σ : D ≃ E` pulls a pseudometric on `E` back to one on
`D`. -/
def comap (σ : D ≃ E) (d : CPM E) : CPM D :=
  ⟨fun x y => d.1 (σ x) (σ y),
    { dist_self := fun _ => d.2.dist_self _
      dist_comm := fun _ _ => d.2.dist_comm _ _
      dist_triangle := fun _ _ _ => d.2.dist_triangle _ _ _ }⟩

@[simp] theorem comap_val (σ : D ≃ E) (d : CPM E) :
    (comap σ d).1 = fun x y => d.1 (σ x) (σ y) := rfl

/-- Relabelling preserves the extended supremum distance exactly: `σ × σ`
reindexes the supremum bijectively. -/
theorem edist_comap (σ : D ≃ E) (d e : CPM E) :
    edist (comap σ d) (comap σ e) = edist d e :=
  Equiv.iSup_comp (g := fun q : E × E => ENNReal.ofReal |d.1 q.1 q.2 - e.1 q.1 q.2|)
    (σ.prodCongr σ)

theorem isometry_comap (σ : D ≃ E) : Isometry (comap σ : CPM E → CPM D) :=
  fun d e => edist_comap σ d e

/-- `CPM(E) ≃ CPM(D)` for any bijection `σ : D ≃ E`. -/
def relabelEquiv (σ : D ≃ E) : CPM E ≃ CPM D where
  toFun := comap σ
  invFun := comap σ.symm
  left_inv _ := Subtype.ext (by funext x y; simp)
  right_inv _ := Subtype.ext (by funext x y; simp)

@[simp] theorem relabelEquiv_apply (σ : D ≃ E) (d : CPM E) :
    relabelEquiv σ d = comap σ d := rfl

/-- The relabelling bijection is an isometry, hence a homeomorphism
`CPM(E) ≃ₜ CPM(D)`. -/
def relabelIsometry (σ : D ≃ E) : CPM E ≃ᵢ CPM D where
  toEquiv := relabelEquiv σ
  isometry_toFun := isometry_comap σ

/-- Relabelling commutes with the inclusion of the bounded ambient. -/
@[simp] theorem comap_toCPM (σ : D ≃ E) (d : BddPMet E) :
    (BddPMet.comap σ d).toCPM = comap σ d.toCPM := rfl

/-- Relabelling preserves membership in the unbounded compatible-metric locus
`Met`, in both directions. -/
theorem mem_Met_comap_iff (σ : D ≃ E) (d : CPM E) :
    comap σ d ∈ CPM.Met D ↔ d ∈ CPM.Met E :=
  exists_isMetricOn_comap_iff σ d.1

theorem preimage_Met_comap (σ : D ≃ E) :
    comap σ ⁻¹' CPM.Met D = CPM.Met E := by
  ext d
  exact mem_Met_comap_iff σ d

/-- Relabelling preserves the bounded compatible-metric locus viewed inside
the unbounded ambient.  Unlike `Met`, this locus is defined as an *image*, so
the forward direction has to rebuild the bounded witness on `E`; the
relabelling of the witness along `σ.symm` does that. -/
theorem preimage_BMet_comap (σ : D ≃ E) :
    comap σ ⁻¹' CPM.BMet D = CPM.BMet E := by
  ext x
  constructor
  · rintro ⟨b, hb, hbx⟩
    refine ⟨BddPMet.comap σ.symm b, (isCompatible_comap_iff σ.symm b).mpr hb, ?_⟩
    apply Subtype.ext
    funext u v
    simpa using congrArg (fun c : CPM D => c.1 (σ.symm u) (σ.symm v)) hbx
  · rintro ⟨b, hb, rfl⟩
    exact ⟨BddPMet.comap σ b, (isCompatible_comap_iff σ b).mpr hb, rfl⟩

end CPM

/-! ## The arbitrary-carrier Borel obstruction

The Borel σ-algebras of both ambients are the ones generated by their own
(extended-)metric topologies, so the relabelling isometry is in particular
continuous and hence Borel-measurable; a Borel locus on an arbitrary carrier
`D` therefore pulls back to a Borel locus on the concrete coded carrier
`ExtIndex S`, where Issue #56 shows it is not Borel.

The `MeasurableSpace`/`BorelSpace` instances of `Ext/Borel.lean` and
`Ext/CPM.lean` are `local` to those files, so they are redeclared here.  Both
copies unfold to `borel (BddPMet _)` / `borel (CPM _)`, so the statements
below are the same statements as the Issue #56 ones at `D := ExtIndex S`. -/

local instance relabelBddPMetMeasurableSpace (D : Type*) : MeasurableSpace (BddPMet D) :=
  borel (BddPMet D)

local instance relabelBddPMetBorelSpace (D : Type*) : BorelSpace (BddPMet D) :=
  ⟨rfl⟩

local instance relabelCpmMeasurableSpace (D : Type*) : MeasurableSpace (CPM D) :=
  borel (CPM D)

local instance relabelCpmBorelSpace (D : Type*) : BorelSpace (CPM D) :=
  ⟨rfl⟩

/-- The hypothesis `#D = ℵ₁` of the three theorems below is satisfiable, so
none of them is vacuous: the coded carrier of the bounded star coding is one
such `D`. -/
theorem exists_carrier_aleph_one : ∃ D : Type, #D = aleph 1 := by
  obtain ⟨S, -, hScard, -⟩ := exists_aleph1_nonBorel
  exact ⟨ExtIndex S, card_extIndex hScard⟩

/-- Every carrier of cardinality `ℵ₁` is a relabelling of the coded carrier
`ExtIndex S` supplied by `exists_aleph1_nonBorel`.  `ExtIndex S` lives in
`Type 0` while `D : Type u` is arbitrary, so the cardinals are compared after
`Cardinal.lift`; `ℵ₁` is lift-invariant. -/
theorem exists_equiv_extIndex_of_card {D : Type*} (hD : #D = aleph 1) :
    ∃ S : Set ℝ, S ⊆ Set.Icc (0 : ℝ) 1 ∧ #(↥S) = aleph 1 ∧ ¬ MeasurableSet S ∧
      Nonempty (D ≃ ExtIndex S) := by
  obtain ⟨S, hSsub, hScard, hSnonmeas⟩ := exists_aleph1_nonBorel
  refine ⟨S, hSsub, hScard, hSnonmeas, Cardinal.lift_mk_eq'.mp ?_⟩
  rw [hD, card_extIndex hScard]
  simp

/-- **Arbitrary-carrier form of the bounded-ambient obstruction** (audit §7
item 2).  For *every* discrete `D` with `|D| = ℵ₁`, the compatible bounded
metrics `BMet(D)` are not Borel in the bounded pseudometric ambient
`BCPM(D)`.  This is not Theorem 3.3 itself — the preprint states the
obstruction in the unbounded ambient `CPM(D)`; that is
`bmet_not_borel_cpm_of_card` below. -/
theorem bmet_not_borel_of_card (D : Type*) (hD : #D = aleph 1) :
    ¬ MeasurableSet (BMet D) := by
  intro hBMet
  obtain ⟨S, hSsub, hScard, hSnonmeas, ⟨σ⟩⟩ := exists_equiv_extIndex_of_card hD
  have hpre : MeasurableSet (BddPMet.comap σ ⁻¹' BMet D) :=
    hBMet.preimage (BddPMet.isometry_comap σ).continuous.measurable
  rw [preimage_BMet_comap σ] at hpre
  exact bmet_not_borel hSsub hScard hSnonmeas hpre

/-- **Theorem 3.3, in its literal arbitrary-carrier form.**  The preprint's
Theorem 3.3 states exactly this (audit §2.6): for a discrete `Z` with
`|Z| = ℵ₁`, `BMet(Z)` is not Borel in `CPM(Z)`.  Here for *every* discrete
`D` with `|D| = ℵ₁`. -/
theorem bmet_not_borel_cpm_of_card (D : Type*) (hD : #D = aleph 1) :
    ¬ MeasurableSet (CPM.BMet D) := by
  intro hBMet
  obtain ⟨S, hSsub, hScard, hSnonmeas, ⟨σ⟩⟩ := exists_equiv_extIndex_of_card hD
  have hpre : MeasurableSet (CPM.comap σ ⁻¹' CPM.BMet D) :=
    hBMet.preimage (CPM.isometry_comap σ).continuous.measurable
  rw [CPM.preimage_BMet_comap σ] at hpre
  exact bmet_not_borel_cpm hSsub hScard hSnonmeas hpre

/-- **The abstract's and introduction's `Met(Z)` claim, in its literal
arbitrary-carrier form.**  The preprint announces "`Met(Z)` is not Borel" in
its abstract and introduction, while the body's Theorem 3.3 states the
`BMet(Z)` version; audit §2.6 records that gap and §7 item 3 asks for both to
be formalised from the single pullback identity.  This is the `Met` one: for
*every* discrete `D` with `|D| = ℵ₁`, the metrics on `D` compatible with the
discrete topology form a non-Borel subset of the space of continuous
pseudometrics on `D` with the supremum distance.

No hypothesis on a parameter set is left in the statement: the non-Borel
`S ⊆ [0,1]` of cardinality `ℵ₁` is produced internally by
`exists_aleph1_nonBorel`, and the coded carrier `ExtIndex S` it determines is
relabelled onto `D` by `CPM.relabelIsometry`. -/
theorem met_not_borel_of_card (D : Type*) (hD : #D = aleph 1) :
    ¬ MeasurableSet (CPM.Met D) := by
  intro hMet
  obtain ⟨S, hSsub, -, hSnonmeas, ⟨σ⟩⟩ := exists_equiv_extIndex_of_card hD
  have hpre : MeasurableSet (CPM.comap σ ⁻¹' CPM.Met D) :=
    hMet.preimage (CPM.isometry_comap σ).continuous.measurable
  rw [CPM.preimage_Met_comap σ] at hpre
  exact met_not_borel hSsub hSnonmeas hpre

end
end IshikiExt
