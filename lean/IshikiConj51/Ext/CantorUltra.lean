-- Ext.CantorUltra
--
-- Issue #81, scope items 2–3: the Cantor-space inputs of the non-Archimedean
-- track of arXiv:2608.19618.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.2
-- (Proposition 2.2, with the audited repair) and the setup paragraph of §2.13
-- (the standard `R`-valued Cantor ultrametric).
--
-- Two independent pieces:
--
-- 1. **Proposition 2.2** — a dense non-Borel `S ⊆ 2^ω` with `|S| = ℵ₁`.  The
--    preprint derives this from Proposition 2.1 "because `2^ω` is Borel
--    isomorphic to `[0,1]`", which transfers non-Borelness and cardinality but
--    **not density** (audit §2.2, verdict FIX).  The repair carried out here is
--    the audit's: obtain a non-Borel `T ⊆ 2^ω` with `|T| = ℵ₁` and then
--    *densify*, `S = T ∪ Q₀` with `Q₀` countable dense — the second half of the
--    audit's repair route 1, which needs of `T` only "non-Borel of size `ℵ₁`".
--    `T` is produced by running the CH/¬CH dichotomy of §2.1 directly in `2^ω`
--    (the audit's repair route 2 minus its Bernstein branch), for the same
--    reason as in `Ext/Borel.lean`: the dichotomy is available from Mathlib
--    while the Borel isomorphism `2^ω ≅ [0,1]` and Bernstein sets are not.
--    The dichotomy is stated once, for an arbitrary standard Borel space of
--    cardinality `𝔠` whose Borel σ-algebra has at most `𝔠` members, so that the
--    real-line instance of `Ext/Borel.lean` and this Cantor instance are two
--    readings of one argument.
--
-- 2. **The standard `R`-valued Cantor ultrametric** `h(s,t) = r(min {n : s n ≠
--    t n})` attached to a scale `r` (`Ext/UltraPMet.lean`), together with the
--    exact ball description `h(s,t) < r n ↔ s and t agree below n+1`.  That
--    single equivalence is what ties `h` to the product topology of `2^ω`: it
--    turns cylinders into `h`-balls, so `Dense S` (a product-topology
--    statement, which is what Proposition 2.2 delivers) supplies the
--    approximation used by Lemma 3.11, and any family of maps that is
--    `h`-Lipschitz is continuous for the product topology.
--
-- Mathlib has `PiNat.firstDiff` and the `(1/2)^n` distance built from it, but
-- not the `R`-valued version, so `cantorDist` is defined here; the `PiNat`
-- distance is a local instance in Mathlib and is not used.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.UltraPMet

open Cardinal Set

namespace IshikiExt

noncomputable section

/-! ## Cardinality input for the dichotomy -/

/-- The Borel σ-algebra of a second-countable Borel space has at most `𝔠`
members.  This is `Ext/Borel.lean`'s `cardinal_borel_subset_le_continuum` with
the real line replaced by an arbitrary such space. -/
theorem cardinal_measurableSet_le_continuum (α : Type) [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] :
    #{s : Set α | MeasurableSet s} ≤ (𝔠 : Cardinal.{0}) := by
  obtain ⟨b, hb, -, hbasis⟩ := TopologicalSpace.exists_countable_basis α
  have hbcard : #b ≤ (𝔠 : Cardinal) :=
    (Cardinal.le_aleph0_iff_set_countable.mpr hb).trans Cardinal.aleph0_le_continuum
  have hgen := MeasurableSpace.cardinal_measurableSet_le_continuum (α := α) hbcard
  have hborel : (inferInstance : MeasurableSpace α) = borel α := BorelSpace.measurable_eq
  have heq : (inferInstance : MeasurableSpace α) = MeasurableSpace.generateFrom b :=
    hborel.trans hbasis.borel_eq_generateFrom
  rwa [← heq] at hgen

/-- An uncountable Borel subset of a standard Borel space has cardinality
continuum. -/
theorem cardinal_eq_continuum_of_measurableSet {α : Type} [MeasurableSpace α]
    [StandardBorelSpace α] {T : Set α} (hT : MeasurableSet T) (hunc : ¬ Countable (↥T)) :
    #(↥T) = (𝔠 : Cardinal.{0}) := by
  letI : StandardBorelSpace T := MeasurableSet.standardBorel hT
  let e : T ≃ᵐ (ℕ → Bool) := PolishSpace.measurableEquivNatBoolOfNotCountable hunc
  have hfun : #(ℕ → Bool) = (𝔠 : Cardinal) := by
    rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
      Cardinal.lift_id]
    exact Cardinal.two_power_aleph0
  exact e.toEquiv.cardinal_eq.trans hfun

/-- **The CH/¬CH dichotomy**, stated once.  In a standard Borel space of
cardinality `𝔠` whose Borel σ-algebra has at most `𝔠` members there is a
non-Borel subset of cardinality `ℵ₁`.  This is the statement content of audit
§2.1 with density dropped; `Ext/Borel.lean` runs it on `[0,1] ⊆ ℝ` and
Proposition 2.2 below runs it on `2^ω`. -/
theorem exists_aleph1_nonMeasurable (α : Type) [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSingletonClass α] (hcard : #α = (𝔠 : Cardinal.{0}))
    (hborel : #{s : Set α | MeasurableSet s} ≤ (𝔠 : Cardinal.{0})) :
    ∃ T : Set α, #(↥T) = aleph 1 ∧ ¬ MeasurableSet T := by
  rcases (Cardinal.aleph_one_le_continuum).lt_or_eq with hnCH | hCH
  · -- ¬CH: any subset of size `ℵ₁` is non-Borel, since a Borel one would have
    -- size `𝔠 > ℵ₁`.
    have hle : aleph 1 ≤ #(Set.univ : Set α) := by
      rw [Cardinal.mk_univ, hcard]; exact hnCH.le
    obtain ⟨T, -, hTcard⟩ := Cardinal.le_mk_iff_exists_subset.mp hle
    refine ⟨T, hTcard, fun hTmeas => ?_⟩
    have hunc : ¬ Countable (↥T) := by
      intro hcount
      have := Cardinal.le_aleph0_iff_set_countable.mpr hcount
      exact absurd (hTcard ▸ this) (not_le_of_gt Cardinal.aleph0_lt_aleph_one)
    exact (ne_of_lt hnCH) (hTcard.symm.trans (cardinal_eq_continuum_of_measurableSet hTmeas hunc))
  · -- CH: there are more subsets than Borel sets, and any non-Borel one is
    -- uncountable, hence of size `ℵ₁` under CH.
    have hpow : (𝔠 : Cardinal.{0}) < #(Set α) := by
      rw [Cardinal.mk_set, ← hcard]; exact Cardinal.cantor _
    have hnot : ¬ ∀ T : Set α, MeasurableSet T := by
      intro hall
      have hsub : (Set.univ : Set (Set α)) ⊆ {s : Set α | MeasurableSet s} :=
        fun s _ => hall s
      have hle : #(Set α) ≤ #{s : Set α | MeasurableSet s} := by
        rw [← Cardinal.mk_univ (α := Set α)]
        exact Cardinal.mk_le_mk_of_subset hsub
      exact absurd (hle.trans hborel) (not_le_of_gt hpow)
    push Not at hnot
    obtain ⟨T, hTnonmeas⟩ := hnot
    have hunc : ¬ Countable (↥T) := fun hcount =>
      hTnonmeas (Set.Countable.measurableSet hcount)
    refine ⟨T, le_antisymm ?_ ?_, hTnonmeas⟩
    · exact (Cardinal.mk_set_le T).trans (hcard.trans hCH.symm).le
    · exact Cardinal.aleph_one_le_iff.mpr
        (Cardinal.aleph0_lt_mk_iff.mpr (not_countable_iff.mp hunc))

/-! ## Proposition 2.2 -/

theorem mk_cantor : #(ℕ → Bool) = (𝔠 : Cardinal.{0}) := by
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.two_power_aleph0

/-- **Proposition 2.2** (audit §2.2, as repaired).  There is a *dense* subset
`S ⊆ 2^ω` of cardinality `ℵ₁` that is not Borel.  Density is what the
preprint's Borel-isomorphism argument fails to deliver and is what Lemma 3.11
genuinely uses. -/
theorem exists_dense_aleph1_nonBorel_cantor :
    ∃ S : Set (ℕ → Bool), Dense S ∧ #(↥S) = aleph 1 ∧ ¬ MeasurableSet S := by
  obtain ⟨T, hTcard, hTnonmeas⟩ :=
    exists_aleph1_nonMeasurable (ℕ → Bool) mk_cantor
      (cardinal_measurableSet_le_continuum (ℕ → Bool))
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense (ℕ → Bool)
  refine ⟨T ∪ Q, Dense.mono Set.subset_union_right hQdense, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · calc #(↥(T ∪ Q)) ≤ #(↥T) + #(↥Q) := Cardinal.mk_union_le T Q
        _ ≤ aleph 1 + (ℵ₀ : Cardinal.{0}) :=
            add_le_add hTcard.le (Cardinal.le_aleph0_iff_set_countable.mpr hQcount)
        _ = aleph 1 := Cardinal.add_eq_left (Cardinal.aleph0_le_aleph 1)
            (Cardinal.aleph0_le_aleph 1)
    · calc (aleph 1 : Cardinal.{0}) = #(↥T) := hTcard.symm
        _ ≤ #(↥(T ∪ Q)) := Cardinal.mk_le_mk_of_subset Set.subset_union_left
  · -- If `T ∪ Q` were Borel, then `T = (T ∪ Q) ∖ (Q ∖ T)` would be Borel too,
    -- because `Q ∖ T` is countable.
    intro hmeas
    refine hTnonmeas ?_
    have hQT : ((Q \ T : Set (ℕ → Bool))).Countable := hQcount.mono Set.sdiff_subset
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

/-! ## The standard `R`-valued Cantor ultrametric -/

variable {R : RangeSet} {r : ℕ → ℝ}

open Classical in
/-- `h(s,t) = r(min {n : s n ≠ t n})`, the standard `R`-valued ultrametric on
`2^ω` attached to a scale `r` (audit §2.13, setup).  Mathlib's `PiNat.dist` is
the special case `r n = 2^{-n}`, is a local instance there, and is not
`R`-valued; only the index function `PiNat.firstDiff` is reused. -/
def cantorDist (r : ℕ → ℝ) (s t : ℕ → Bool) : ℝ :=
  if s = t then 0 else r (PiNat.firstDiff s t)

@[simp] theorem cantorDist_self (r : ℕ → ℝ) (t : ℕ → Bool) : cantorDist r t t = 0 := by
  simp [cantorDist]

theorem cantorDist_of_ne {s t : ℕ → Bool} (h : s ≠ t) :
    cantorDist r s t = r (PiNat.firstDiff s t) := by
  simp [cantorDist, h]

theorem cantorDist_comm (r : ℕ → ℝ) (s t : ℕ → Bool) :
    cantorDist r s t = cantorDist r t s := by
  rcases eq_or_ne s t with rfl | h
  · rfl
  · rw [cantorDist_of_ne h, cantorDist_of_ne h.symm, PiNat.firstDiff_comm]

theorem cantorDist_nonneg (hr : RangeSet.IsScale R r) (s t : ℕ → Bool) :
    0 ≤ cantorDist r s t := by
  rcases eq_or_ne s t with rfl | h
  · simp
  · rw [cantorDist_of_ne h]; exact hr.nonneg _

theorem cantorDist_pos_of_ne (hr : RangeSet.IsScale R r) {s t : ℕ → Bool} (h : s ≠ t) :
    0 < cantorDist r s t := by
  rw [cantorDist_of_ne h]; exact hr.pos _

theorem cantorDist_eq_zero_iff (hr : RangeSet.IsScale R r) {s t : ℕ → Bool} :
    cantorDist r s t = 0 ↔ s = t := by
  refine ⟨fun h => ?_, fun h => by rw [h, cantorDist_self]⟩
  by_contra hne
  exact absurd h (ne_of_gt (cantorDist_pos_of_ne hr hne))

theorem cantorDist_mem (hr : RangeSet.IsScale R r) (s t : ℕ → Bool) :
    cantorDist r s t ∈ R.carrier := by
  rcases eq_or_ne s t with rfl | h
  · simpa using R.zero_mem
  · rw [cantorDist_of_ne h]; exact hr.mem _

/-- Every value of `h` is at most the first term of the scale; this is the
bound that makes the constant cross-cluster distance `r 0` of the Lemma 3.10
coding dominate everything inside a cluster. -/
theorem cantorDist_le_head (hr : RangeSet.IsScale R r) (s t : ℕ → Bool) :
    cantorDist r s t ≤ r 0 := by
  rcases eq_or_ne s t with rfl | h
  · simpa using hr.nonneg 0
  · rw [cantorDist_of_ne h]; exact hr.le_head _

theorem cantorDist_triangle_max (hr : RangeSet.IsScale R r) (s t u : ℕ → Bool) :
    cantorDist r s u ≤ max (cantorDist r s t) (cantorDist r t u) := by
  rcases eq_or_ne s u with rfl | hsu
  · rw [cantorDist_self]
    exact (cantorDist_nonneg hr s t).trans (le_max_left _ _)
  rcases eq_or_ne s t with rfl | hst
  · exact le_max_right _ _
  rcases eq_or_ne t u with rfl | htu
  · exact le_max_left _ _
  rw [cantorDist_of_ne hsu, cantorDist_of_ne hst, cantorDist_of_ne htu]
  refine (hr.antitone (PiNat.min_firstDiff_le s t u hsu)).trans ?_
  rcases min_cases (PiNat.firstDiff s t) (PiNat.firstDiff t u) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he]
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **Isosceles principle for `h`.**  If `h(s,w) < h(s,t)` then
`h(t,w) = h(s,t)`: an ultrametric triangle with two unequal sides is isosceles
with the third side equal to the longer one.  This is what turns density of `S`
into the exact lower bound of Lemma 3.11. -/
theorem cantorDist_isosceles (hr : RangeSet.IsScale R r) {s t w : ℕ → Bool}
    (h : cantorDist r s w < cantorDist r s t) :
    cantorDist r t w = cantorDist r s t := by
  refine le_antisymm ?_ ?_
  · refine (cantorDist_triangle_max hr t s w).trans ?_
    rw [cantorDist_comm r t s]
    exact max_le le_rfl h.le
  · have htri := cantorDist_triangle_max hr s w t
    rcases max_cases (cantorDist r s w) (cantorDist r w t) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at htri
      exact absurd (lt_of_le_of_lt htri h) (lt_irrefl _)
    · rw [he, cantorDist_comm r w t] at htri
      exact htri

/-- **The ball description.**  `h(s,t) < r n` exactly when `s` and `t` agree on
the first `n+1` coordinates — that is, exactly when `s` lies in the cylinder of
`t` of length `n+1`.  Every interaction below between `h` and the product
topology of `2^ω` goes through this one equivalence. -/
theorem cantorDist_lt_iff (hr : RangeSet.IsScale R r) (s t : ℕ → Bool) (n : ℕ) :
    cantorDist r s t < r n ↔ ∀ m ≤ n, s m = t m := by
  constructor
  · intro hlt m hm
    rcases eq_or_ne s t with rfl | hst
    · rfl
    · rw [cantorDist_of_ne hst] at hlt
      exact PiNat.apply_eq_of_lt_firstDiff (lt_of_le_of_lt hm (hr.lt_iff_lt.mp hlt))
  · intro hall
    rcases eq_or_ne s t with rfl | hst
    · simpa using hr.pos n
    · rw [cantorDist_of_ne hst]
      refine hr.lt_iff_lt.mpr ?_
      by_contra hle
      push Not at hle
      exact PiNat.apply_firstDiff_ne hst (hall _ hle)

theorem cantorDist_lt_of_mem_cylinder (hr : RangeSet.IsScale R r) {s t : ℕ → Bool} {n : ℕ}
    (hs : s ∈ PiNat.cylinder t (n + 1)) : cantorDist r s t < r n :=
  (cantorDist_lt_iff hr s t n).mpr fun m hm =>
    PiNat.mem_cylinder_iff.mp hs m (Nat.lt_succ_of_le hm)

/-- **Density, in the form Lemma 3.11 uses.**  A dense set meets every
`h`-ball, because the balls of radius `r n` are cylinders. -/
theorem exists_mem_cantorDist_lt {S : Set (ℕ → Bool)} (hS : Dense S)
    (hr : RangeSet.IsScale R r) (t : ℕ → Bool) (n : ℕ) :
    ∃ w ∈ S, cantorDist r t w < r n := by
  obtain ⟨w, hwS, hw⟩ := hS.exists_mem_open (PiNat.isOpen_cylinder (fun _ => Bool) t (n + 1))
    ⟨t, PiNat.self_mem_cylinder t (n + 1)⟩
  exact ⟨w, hwS, by rw [cantorDist_comm]; exact cantorDist_lt_of_mem_cylinder hr hw⟩

/-- **Continuity criterion.**  A map out of `2^ω` that is `1`-Lipschitz from
`h` into an extended pseudometric space is continuous for the product topology.
Both parameter maps of this track (Lemma 3.11 and Theorem 3.13) are of this
shape, and this is the only place where the identification of the `h`-topology
with the product topology is used. -/
theorem continuous_of_edist_le_cantorDist {X : Type*} [PseudoEMetricSpace X]
    (hr : RangeSet.IsScale R r) {f : (ℕ → Bool) → X}
    (hf : ∀ s t, edist (f s) (f t) ≤ ENNReal.ofReal (cantorDist r s t)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  obtain ⟨c, hc0, hcε⟩ : ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal c < ε := by
    obtain ⟨q, hq0, hqε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    refine ⟨(q : ℝ), by exact_mod_cast ENNReal.coe_pos.mp hq0, ?_⟩
    rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn⟩ := hr.exists_lt hc0
  filter_upwards [(PiNat.isOpen_cylinder (fun _ => Bool) t (n + 1)).mem_nhds
    (PiNat.self_mem_cylinder t (n + 1))] with s hs
  calc edist (f s) (f t) ≤ ENNReal.ofReal (cantorDist r s t) := hf s t
    _ < ENNReal.ofReal c :=
        (ENNReal.ofReal_lt_ofReal_iff hc0).mpr ((cantorDist_lt_of_mem_cylinder hr hs).trans hn)
    _ < ε := hcε

end

end IshikiExt
