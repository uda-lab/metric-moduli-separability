-- Conj51.ClosedEmbedding
--
-- LEM-CLOSED-IMAGE (report 補題 3.4): the parameter map `φ : A^∁ → Met(D)`,
-- `t ↦ d_t`, of report/report-ja.md §3.4 is a bi-Lipschitz embedding of
-- `A^∁ = [0,1] \ A` into `Met(D)` whose image is closed.
--
-- Mathematical source of truth: `report/report-ja.md` §3.4, (C4) and (C5).
--
-- What is proved here:
--   `edist_le_edist_starParam`   — (C4) lower bound `|t−s| ≤ ρ(d_t, d_s)`.
--   `edist_starParam_le`         — (C4) upper bound `ρ(d_t, d_s) ≤ 2|t−s|`.
--   `range_starParam`            — (C5) the image is cut out by the three
--     conditions of report §3.4 (C5) (手順1–手順3).
--   `isClosed_starRange`         — (C5) that description is a closed set.
--   `isClosedEmbedding_starParam`— φ is a closed embedding.
--   `lem_closed_image`           — LEM-CLOSED-IMAGE itself.
--
-- Two deliberate departures from the report's *presentation* (not from its
-- mathematics), both recorded in notes/proof-audit.md:
--
--   * The report speaks of "a bi-Lipschitz homeomorphism onto its image",
--     i.e. of the subspace `φ(A^∁) ⊆ Met(D)`.  Here the same content is
--     packaged as `Topology.IsClosedEmbedding (starParam A)`, which is
--     definitionally "φ is a homeomorphism onto its image *and* that image
--     is closed".  This is the form Mathlib's closed-subspace inheritance
--     theorem (`Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`)
--     consumes, so no separate transfer along `A^∁ ≃ₜ φ(A^∁)` is needed.
--
--   * Report §3.4 (C5) argues with a sequence `d_{t_k} → e` and extracts a limit
--     parameter.  The formalisation replaces the sequence by the equivalent
--     *closed-set description* of the image:
--         range φ = {e | anchorParam e ∈ [0,1]}
--                     ∩ ⋂_{u,v} {e | e u v = d_{anchorParam e} u v},
--     where `anchorParam e := e p q − 1` is report 手順1's readout of the
--     parameter from the anchor pair.  Each factor is closed because
--     `e ↦ e u v` is 1-Lipschitz (it is one term of the supremum defining ρ)
--     and `t ↦ d_t u v` is 2-Lipschitz — the latter being exactly the
--     estimate `ρ(d_{t_k}, d_t) ≤ 2|t_k − t|` that drives report 手順2.
--     手順3 (`t ∉ A`) is not part of the closed description: it is *derived*
--     from `e ∈ Met(D)` via (C3), which is what makes the description exact.
--
-- No boundedness or uniform-discreteness restriction is used anywhere; `MetD`
-- is the unweakened `Met(D)` of `Conj51/MetD.lean`.
--
-- Status: sorry-free.

import Mathlib
import IshikiConj51.Conj51.MetricConstruction

open Topology
open scoped ENNReal

/-! ## The parameter map `φ : A^∁ → Met(D)` (report §3.4) -/

/-- The parameter space `A^∁ = [0,1] \ A` of the report, as a subtype of `ℝ`
carrying the subspace topology. -/
abbrev StarParamSpace (A : Set ℝ) : Type := ↥(Set.Icc (0 : ℝ) 1 \ A)

/-- The report's `φ : A^∁ → Met(D)`, `t ↦ d_t` (§3.4), as a map of types.  This
is clause 4 of `lem_star_metric` made into a named function. -/
noncomputable def starParam (A : Set ℝ) (t : StarParamSpace A) : MetD (StarIndex A) :=
  starMet A t.2.1 t.2.2

@[simp] theorem starParam_coe (A : Set ℝ) (t : StarParamSpace A) :
    (starParam A t).1 = dStar A (t : ℝ) := rfl

/-- On a subtype of `ℝ` the extended distance is the absolute difference. -/
theorem edist_subtype_real {S : Set ℝ} (t s : ↥S) :
    edist t s = ENNReal.ofReal |(t : ℝ) - (s : ℝ)| := by
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq]

/-- Each pair-value of the star family is `2`-Lipschitz in the parameter
(report §3.4); this is `dStar_sub_le` repackaged. -/
theorem lipschitzWith_dStar (A : Set ℝ) (u v : StarIndex A) :
    LipschitzWith 2 (fun t : ℝ => dStar A t u v) :=
  LipschitzWith.of_dist_le_mul fun t s => by
    rw [Real.dist_eq, Real.dist_eq]
    simpa using dStar_sub_le A t s u v

/-! ## (C4): the bi-Lipschitz estimate `|t−s| ≤ ρ(d_t, d_s) ≤ 2|t−s|` -/

/-- **(C4) lower bound** (report §3.4).  The anchor pair alone already
separates the parameters: `|t − s| = |d_t(p,q) − d_s(p,q)| ≤ ρ(d_t, d_s)`. -/
theorem edist_le_edist_starParam (A : Set ℝ) (t s : StarParamSpace A) :
    edist t s ≤ edist (starParam A t) (starParam A s) := by
  rw [edist_subtype_real]
  have h := MetD.ofReal_abs_sub_le_edist (starParam A t) (starParam A s)
    (Sum.inl true) (Sum.inl false)
  rwa [starParam_coe, starParam_coe, dStar_anchor_sub] at h

/-- **(C4) upper bound** (report §3.4).  Every entry of the distance table
moves by at most `2|t − s|`, hence so does the supremum. -/
theorem edist_starParam_le (A : Set ℝ) (t s : StarParamSpace A) :
    edist (starParam A t) (starParam A s) ≤ 2 * edist t s := by
  rw [edist_subtype_real]
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal |(t : ℝ) - (s : ℝ)|
      = ENNReal.ofReal (2 * |(t : ℝ) - (s : ℝ)|) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  rw [h2]
  refine MetD.edist_le_of_forall fun u v => ?_
  rw [starParam_coe, starParam_coe]
  exact ENNReal.ofReal_le_ofReal (dStar_sub_le A (t : ℝ) (s : ℝ) u v)

theorem lipschitzWith_starParam (A : Set ℝ) : LipschitzWith 2 (starParam A) := fun t s => by
  simpa using edist_starParam_le A t s

theorem antilipschitzWith_starParam (A : Set ℝ) : AntilipschitzWith 1 (starParam A) := fun t s => by
  simpa using edist_le_edist_starParam A t s

/-- φ is injective — the lower bound of (C4), report §3.4 系. -/
theorem starParam_injective (A : Set ℝ) : Function.Injective (starParam A) := by
  intro t s h
  have hle := edist_le_edist_starParam A t s
  rw [h, edist_self, le_zero_iff] at hle
  exact edist_eq_zero.mp hle

/-! ## (C5): the image is closed (report §3.4) -/

/-- Report §3.4 (C5) 手順1: the anchor pair reads the parameter back off an
arbitrary element of `Met(D)`, since `d_t(p,q) = 1 + t`. -/
noncomputable def anchorParam (A : Set ℝ) (e : MetD (StarIndex A)) : ℝ :=
  e.1 (Sum.inl true) (Sum.inl false) - 1

theorem continuous_anchorParam (A : Set ℝ) : Continuous (anchorParam A) :=
  (MetD.lipschitzWith_apply (D := StarIndex A) (Sum.inl true) (Sum.inl false)).continuous.sub
    continuous_const

@[simp] theorem anchorParam_starParam (A : Set ℝ) (t : StarParamSpace A) :
    anchorParam A (starParam A t) = (t : ℝ) := by
  simp [anchorParam, dStar_anchor]

/-- The closed description of `φ(A^∁)` used in place of report §3.4 (C5)'s sequential
argument: an element of `Met(D)` lies in the image exactly when its anchor
parameter lies in `[0,1]` and it coincides with the star metric of that
parameter.  The remaining condition of (C5), `t ∉ A` (手順3), is *not* imposed
here — it is a consequence of membership in `Met(D)` by (C3), which is what
makes this description exact (`range_starParam`). -/
def StarRange (A : Set ℝ) : Set (MetD (StarIndex A)) :=
  {e | anchorParam A e ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ u v, e.1 u v = dStar A (anchorParam A e) u v}

/-- **(C5), exactness** (report §3.4).  Note the direction that uses (C3): if
`e ∈ Met(D)` agrees with `d_t` then `t ∉ A`, because `d_t` for `t ∈ A` is not
compatible with the discrete topology.  This is 手順3. -/
theorem range_starParam (A : Set ℝ) : Set.range (starParam A) = StarRange A := by
  ext e
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨by rw [anchorParam_starParam]; exact t.2.1, fun u v => ?_⟩
    rw [anchorParam_starParam, starParam_coe]
  · rintro ⟨hIcc, heq⟩
    have hval : e.1 = dStar A (anchorParam A e) := funext fun u => funext fun v => heq u v
    have hA : anchorParam A e ∉ A :=
      (dStar_mem_MetD_iff A hIcc).mp (MetD.exists_isMetricOn_of_val_eq e hval)
    exact ⟨⟨anchorParam A e, hIcc, hA⟩, Subtype.ext hval.symm⟩

/-- **(C5), closedness** (report §3.4).  Both factors of the description are
closed: `anchorParam` is continuous (手順1), and for fixed `u, v` the two
sides of the defining equation are continuous in `e` — `e ↦ e u v` because it
is one term of the supremum, and `e ↦ d_{anchorParam e} u v` because
`t ↦ d_t u v` is `2`-Lipschitz.  That Lipschitz estimate is precisely
`ρ(d_{t_k}, d_t) ≤ 2|t_k − t|`, the engine of 手順2. -/
theorem isClosed_starRange (A : Set ℝ) : IsClosed (StarRange A) := by
  have hcont := continuous_anchorParam A
  have hset : StarRange A =
      (anchorParam A ⁻¹' Set.Icc (0 : ℝ) 1) ∩
        ⋂ (u : StarIndex A) (v : StarIndex A),
          {e : MetD (StarIndex A) | e.1 u v = dStar A (anchorParam A e) u v} := by
    ext e
    simp only [StarRange, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter]
  rw [hset]
  refine (isClosed_Icc.preimage hcont).inter
    (isClosed_iInter fun u => isClosed_iInter fun v => ?_)
  exact isClosed_eq (MetD.lipschitzWith_apply u v).continuous
    ((lipschitzWith_dStar A u v).continuous.comp hcont)

theorem isClosed_range_starParam (A : Set ℝ) : IsClosed (Set.range (starParam A)) := by
  rw [range_starParam]
  exact isClosed_starRange A

/-- φ is a closed embedding: a homeomorphism onto its image, and that image is
closed in `Met(D)`.  This is report §3.4, the 系 of (C4) together with (C5). -/
theorem isClosedEmbedding_starParam (A : Set ℝ) :
    IsClosedEmbedding (starParam A) :=
  ⟨⟨(antilipschitzWith_starParam A).isInducing (lipschitzWith_starParam A).continuous,
      starParam_injective A⟩,
    isClosed_range_starParam A⟩

/-! ## LEM-CLOSED-IMAGE -/

/-- **LEM-CLOSED-IMAGE** (report 補題 3.4, §3.4).

For `A ⊆ ℝ` the parameter map `φ : A^∁ = [0,1] \ A → Met(D)`, `t ↦ d_t`, of
the star construction satisfies

1. the bi-Lipschitz estimate `|t − s| ≤ ρ(d_t, d_s) ≤ 2|t − s|` — (C4),
   report §3.4 (here in the extended-distance form carried by `MetD`, where
   `edist t s = ENNReal.ofReal |t − s|` on the subtype `A^∁ ⊆ ℝ`);
2. φ is a closed embedding — i.e. a homeomorphism onto its image (the 系 of
   (C4), report §3.4, which follows from clause 1) and that image is closed
   in `Met(D)` (C5, report §3.4).

Clause 1 implies injectivity and both continuity and openness onto the image,
so clause 2's embedding half is *not* an extra assumption; it is recorded
explicitly because it is the form the closed-subspace inheritance theorem
consumes in `MainTheorem.lean`.

No hypothesis on `|A|` is needed: cardinality enters only through
LEM-STAR-METRIC's clause 1 (`|D| = ℵ₁`), never in (C4)/(C5) — see the Remark
closing report §4. -/
theorem lem_closed_image (A : Set ℝ) :
    (∀ t s : StarParamSpace A,
        edist t s ≤ edist (starParam A t) (starParam A s) ∧
          edist (starParam A t) (starParam A s) ≤ 2 * edist t s) ∧
      IsClosedEmbedding (starParam A) :=
  ⟨fun t s => ⟨edist_le_edist_starParam A t s, edist_starParam_le A t s⟩,
    isClosedEmbedding_starParam A⟩
