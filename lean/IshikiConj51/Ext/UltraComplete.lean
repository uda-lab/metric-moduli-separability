-- Ext.UltraComplete
--
-- Issue #83, scope items 1 and 2: the complete `R`-valued compatible-ultrametric
-- locus `UComp(Z;R)` on a discrete carrier, and Theorem 3.16 of
-- arXiv:2608.19618.
--
-- Mathematical source of truth: `notes/borel-preprint-audit.md` §2.15 (the
-- Theorem 3.16 paragraph), together with §2.13–§2.14 for the coding and
-- amalgamation machinery it reuses.  `report/report-ja.md` is *not* the source
-- of truth here: it stays frozen as the Conjecture 5.1 archival report by the
-- Issue #46 decision.
--
-- The audit records Theorem 3.16 as PASS, and records *why*: unlike the
-- Archimedean Theorem 3.8 (audit §2.11, whose printed proof amalgamates an
-- arbitrary — possibly incomplete — representative of the component), the
-- printed proof of 3.16 normalises the base first.  That normalisation is the
-- backbone of this file and is formalised exactly as the audit states it:
--
--   * `supConstOffDiag c d = d ∨ c` off the diagonal, for `c ∈ R ∖ {0}`, is a
--     complete compatible `R`-valued ultrametric (`isUltraPMetOn_supConstOffDiag`,
--     `topology_supConstOffDiag_eq_bot`, `isCompleteMetricOn_supConstOffDiag`);
--   * it stays in the `R`-component of `d`, by the audited bound
--     `𝒰𝒟^R(d ∨ c, d) ≤ c` (`edist_uSupConstOffDiag_le`,
--     `UComponent_uSupConstOffDiag`);
--   * the coding metrics `e_t` are complete for `t ∉ S` — this is Lemma 3.10's
--     completeness clause, already proved as `dU_completeSpace`
--     (`Ext/UltraCoding.lean`) and only restated here in the bare-metric form
--     of `Ext/Completeness.lean`;
--   * the one-point max-amalgam of two complete pieces is complete
--     (`isCompleteMetricOn_uAmalgam`): past the point where the Cauchy
--     condition drops below the uniform gap at the glue point, the sequence
--     cannot straddle the two sides, so it settles in one of them.
--
-- Everything else is the Theorem 3.13 development of `Ext/UltraComponent.lean`,
-- reused unchanged: the same ball selection, the same amalgam family `psiU`,
-- the same compatibility criterion and the same pullback identity.  Only the
-- base metric is normalised before the construction runs, and only completeness
-- of the amalgam is new.
--
-- As in audit §2.11 for the Archimedean side, the "consequently `UComp(Z;R)` is
-- non-Borel" clause is *not* obtained by intersecting with a component (which
-- is itself non-Borel): it runs on the pullback identity
-- `Ψ⁻¹(UComp(Z;R)) = 2^ω ∖ S`, in which the component plays no role.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.UltraComponent
import IshikiConj51.Ext.Completeness

open Cardinal Set

namespace IshikiExt

noncomputable section

variable {Z W : Type*} {R : RangeSet} {r : ℕ → ℝ}

/-! ## The complete compatible locus

Audit §1: `UComp(Z;R)` is the set of complete members of `UMet(Z;R)`.
Completeness is `IsCompleteMetricOn` (`Ext/Completeness.lean`), which
`isCompleteMetricOn_iff_completeSpace` pins to Mathlib's `CompleteSpace` for
the `MetricSpace` structure the function carries — so the locus is the ordinary
one and not a convenient proxy.  This is the exact non-Archimedean twin of
`CPM.Comp`. -/

/-- `UComp(Z;R)` for a discrete carrier: the complete members of `UMet(Z;R)`. -/
def UComp (Z : Type*) (R : RangeSet) : Set (UCPM Z R) :=
  {d | d ∈ UMet Z R ∧ IsCompleteMetricOn d.1}

@[simp] theorem mem_UComp {d : UCPM Z R} :
    d ∈ UComp Z R ↔ d ∈ UMet Z R ∧ IsCompleteMetricOn d.1 := Iff.rfl

theorem UComp_subset_UMet (Z : Type*) (R : RangeSet) : UComp Z R ⊆ UMet Z R := fun _ h => h.1

/-! ## The complete-base normalisation `d ∨ c` off the diagonal (audit §2.15)

The preprint replaces the representative `d` of the component by `d ∨ c` off
the diagonal, for a fixed `c ∈ R ∖ {0}`.  The four properties the proof uses —
`R`-valued ultrametric, compatible, complete, and `𝒰𝒟^R`-close to `d` — are
proved here.  The non-Archimedean shape of the argument is what makes the
maximum the right operation: `R` is closed under maxima, so `d ∨ c` is still
`R`-valued, where the Archimedean normalisation of audit §2.11 has to add a
constant instead. -/

open Classical in
/-- Audit §2.15's normalisation of the base metric: raise every off-diagonal
value to at least `c`. -/
def supConstOffDiag (c : ℝ) (d : Z → Z → ℝ) : Z → Z → ℝ :=
  fun x y => if x = y then 0 else max (d x y) c

@[simp] theorem supConstOffDiag_self (c : ℝ) (d : Z → Z → ℝ) (x : Z) :
    supConstOffDiag c d x x = 0 := by
  simp [supConstOffDiag]

theorem supConstOffDiag_of_ne {c : ℝ} {d : Z → Z → ℝ} {x y : Z} (h : x ≠ y) :
    supConstOffDiag c d x y = max (d x y) c := by
  simp [supConstOffDiag, h]

/-- Off the diagonal the normalised metric is at least `c`: it is uniformly
discrete, which is what makes it complete and what supplies the gap at the glue
point of the amalgam. -/
theorem le_supConstOffDiag {c : ℝ} {d : Z → Z → ℝ} {x y : Z} (h : x ≠ y) :
    c ≤ supConstOffDiag c d x y := by
  rw [supConstOffDiag_of_ne h]
  exact le_max_right _ _

theorem supConstOffDiag_nonneg {c : ℝ} (hc : 0 ≤ c) (d : Z → Z → ℝ) (x y : Z) :
    0 ≤ supConstOffDiag c d x y := by
  by_cases h : x = y
  · rw [h, supConstOffDiag_self]
  · exact le_trans hc (le_supConstOffDiag h)

/-- The normalised metric is an `R`-valued ultrametric.  The strong triangle
inequality survives because raising every off-diagonal value to `c` raises both
legs of a nondegenerate triangle as well, and because a degenerate triangle has
its remaining leg on both sides. -/
theorem isUltraPMetOn_supConstOffDiag {c : ℝ} (hcR : c ∈ R.carrier) {d : Z → Z → ℝ}
    (hd : IsUltraPMetOn R d) : IsUltraPMetOn R (supConstOffDiag c d) where
  dist_self x := supConstOffDiag_self c d x
  dist_comm x y := by
    by_cases h : x = y
    · rw [h]
    · rw [supConstOffDiag_of_ne h, supConstOffDiag_of_ne (Ne.symm h), hd.dist_comm]
  dist_triangle_max x y z := by
    by_cases hxz : x = z
    · rw [hxz, supConstOffDiag_self]
      exact le_max_of_le_left (supConstOffDiag_nonneg (R.nonneg hcR) d z y)
    · by_cases hxy : x = y
      · rw [hxy]
        exact le_max_right _ _
      · by_cases hyz : y = z
        · rw [hyz]
          exact le_max_left _ _
        · rw [supConstOffDiag_of_ne hxz, supConstOffDiag_of_ne hxy, supConstOffDiag_of_ne hyz]
          refine max_le ?_ (le_max_of_le_left (le_max_right _ _))
          exact (hd.dist_triangle_max x y z).trans
            (max_le_max (le_max_left _ _) (le_max_left _ _))
  mem_range x y := by
    by_cases h : x = y
    · rw [h, supConstOffDiag_self]
      exact R.zero_mem
    · rw [supConstOffDiag_of_ne h]
      exact R.max_mem (hd.mem_range x y) hcR

theorem isMetricOn_supConstOffDiag {c : ℝ} (hc : 0 < c) (hcR : c ∈ R.carrier)
    {d : Z → Z → ℝ} (hd : IsUltraPMetOn R d) : IsMetricOn (supConstOffDiag c d) :=
  (isUltraPMetOn_supConstOffDiag hcR hd).toIsMetricOn fun x y hxy => by
    by_contra hne
    have hle : c ≤ supConstOffDiag c d x y := le_supConstOffDiag hne
    rw [hxy] at hle
    exact absurd hle (not_le.mpr hc)

/-- The normalised metric is compatible with the discrete topology, whatever the
original one was: every point is isolated at radius `c`. -/
theorem topology_supConstOffDiag_eq_bot {c : ℝ} (hc : 0 < c) (hcR : c ∈ R.carrier)
    {d : Z → Z → ℝ} (hd : IsUltraPMetOn R d) :
    (isMetricOn_supConstOffDiag hc hcR hd).topology = ⊥ := by
  rw [IsMetricOn.topology_eq_bot_iff]
  intro u
  refine ⟨c, hc, fun v hv => ?_⟩
  by_contra hne
  exact absurd hv (not_lt.mpr (le_supConstOffDiag hne))

/-- The normalised metric is complete: it is uniformly discrete. -/
theorem isCompleteMetricOn_supConstOffDiag {c : ℝ} (hc : 0 < c) (hcR : c ∈ R.carrier)
    {d : Z → Z → ℝ} (hd : IsUltraPMetOn R d) : IsCompleteMetricOn (supConstOffDiag c d) :=
  isCompleteMetricOn_of_uniformly_separated (isMetricOn_supConstOffDiag hc hcR hd) hc
    fun _ _ h => le_supConstOffDiag h

/-- The normalisation as a member of the ambient. -/
def uSupConstOffDiag {c : ℝ} (hcR : c ∈ R.carrier) (d : UCPM Z R) : UCPM Z R :=
  ⟨supConstOffDiag c d.1, isUltraPMetOn_supConstOffDiag hcR d.2⟩

@[simp] theorem uSupConstOffDiag_val {c : ℝ} (hcR : c ∈ R.carrier) (d : UCPM Z R) :
    (uSupConstOffDiag hcR d).1 = supConstOffDiag c d.1 := rfl

theorem isCompatible_uSupConstOffDiag {c : ℝ} (hc : 0 < c) (hcR : c ∈ R.carrier)
    (d : UCPM Z R) : UCPM.IsCompatible (uSupConstOffDiag hcR d) :=
  ⟨isMetricOn_supConstOffDiag hc hcR d.2, topology_supConstOffDiag_eq_bot hc hcR d.2⟩

/-- **The audited component bound `𝒰𝒟^R(d ∨ c, d) ≤ c`.**  `c` itself is an
admissible tolerance for the pair, in both directions. -/
theorem edist_uSupConstOffDiag_le {c : ℝ} (hc : 0 ≤ c) (hcR : c ∈ R.carrier) (d : UCPM Z R) :
    UCPM.edist d (uSupConstOffDiag hcR d) ≤ ENNReal.ofReal c := by
  refine UCPM.edist_le_ofReal ⟨hcR, fun x y => ⟨?_, ?_⟩⟩
  · show d.1 x y ≤ max (supConstOffDiag c d.1 x y) c
    by_cases h : x = y
    · rw [h, d.2.dist_self]
      exact le_max_of_le_right hc
    · rw [supConstOffDiag_of_ne h]
      exact le_max_of_le_left (le_max_left _ _)
  · show supConstOffDiag c d.1 x y ≤ max (d.1 x y) c
    by_cases h : x = y
    · rw [h, supConstOffDiag_self]
      exact le_max_of_le_right hc
    · exact (supConstOffDiag_of_ne h).le

/-- **The normalised base represents the same `R`-component.**  This is what
lets Theorem 3.16 be stated for an arbitrary representative while the
construction runs over the normalised one. -/
theorem UComponent_uSupConstOffDiag {c : ℝ} (hc : 0 ≤ c) (hcR : c ∈ R.carrier)
    (d : UCPM Z R) : UComponent (uSupConstOffDiag hcR d) = UComponent d := by
  have hfin : UCPM.edist d (uSupConstOffDiag hcR d) < ⊤ :=
    lt_of_le_of_lt (edist_uSupConstOffDiag_le hc hcR d) ENNReal.ofReal_lt_top
  have hfin' : UCPM.edist (uSupConstOffDiag hcR d) d < ⊤ := by
    rwa [UCPM.edist_comm] at hfin
  ext e
  simp only [mem_UComponent, and_congr_right_iff]
  refine fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · exact lt_of_le_of_lt (UCPM.edist_triangle d (uSupConstOffDiag hcR d) e)
      (ENNReal.add_lt_top.mpr ⟨hfin, h⟩)
  · exact lt_of_le_of_lt (UCPM.edist_triangle (uSupConstOffDiag hcR d) d e)
      (ENNReal.add_lt_top.mpr ⟨hfin', h⟩)

/-! ## Completeness of the one-point max-amalgam (audit §2.15)

The audit's third ingredient: a Cauchy sequence for the amalgam "settles in one
side or converges to the glue point".  In the form used below the glue point is
the centre of the ball, and the uniform gap `c` at it — supplied by the
normalised base — is what forbids a Cauchy tail from straddling the two sides.
Once the tail is confined, the amalgam *is* one of the two pieces there
(`uAmalgam_in_in`, `uAmalgam_out_out`), and completeness of that piece finishes
the argument. -/

/-- **The one-point max-amalgam of complete pieces is complete.**  The base is
complete and compatible, the coded side is complete, and every point outside the
ball is at base distance at least `c > 0` from the centre.

Inside the ball the amalgam is the transported coding, so a confined Cauchy
sequence converges there and its limit is a point of the ball; outside the ball
the amalgam is the base metric, whose limit is isolated by compatibility, so the
sequence is eventually constant. -/
theorem isCompleteMetricOn_uAmalgam {d : UCPM Z R} {z : Z} {q : ℝ} (hq : 0 ≤ q)
    (hdm : IsMetricOn d.1) (hdbot : hdm.topology = ⊥) (hdc : IsCompleteMetricOn d.1)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ y : Z, y ∉ uBall d z q → c ≤ d.1 z y)
    (κ : ↥(uBall d z q) ≃ W) {e : UCPM W R} (hec : IsCompleteMetricOn e.1) :
    IsCompleteMetricOn (uAmalgam d z q hq κ e).1 := by
  classical
  intro u hu
  obtain ⟨N₀, hN₀⟩ := hu c hc
  -- Past `N₀` the sequence cannot straddle the two sides: a mixed pair is at
  -- amalgam distance at least `c`.
  have hmix : ∀ i ≥ N₀, ∀ j ≥ N₀, u i ∈ uBall d z q → u j ∉ uBall d z q → False := by
    intro i hi j hj hiB hjB
    have hge : d.1 z (u j) ≤ (uAmalgam d z q hq κ e).1 (u i) (u j) := by
      rw [uAmalgam_val hq, uRetract_of_mem hiB, uRetract_of_notMem hjB]
      exact le_max_left _ _
    exact absurd (lt_of_le_of_lt (le_trans (hgap _ hjB) hge) (hN₀ i hi j hj)) (lt_irrefl c)
  by_cases hB₀ : u N₀ ∈ uBall d z q
  · -- The tail stays inside the ball, where the amalgam is the transported coding.
    have htail : ∀ n ≥ N₀, u n ∈ uBall d z q := by
      intro n hn
      by_contra hnB
      exact hmix N₀ le_rfl n hn hB₀ hnB
    set w : ℕ → W := fun n => κ (uInto d z q hq (u n)) with hw
    have hwval : ∀ (n : ℕ) (h : u n ∈ uBall d z q), w n = κ ⟨u n, h⟩ := by
      intro n h
      simp only [hw, uInto_of_mem h]
    have hwCauchy : IsCauchySeqOn e.1 w := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨max N N₀, fun i hi j hj => ?_⟩
      have hiB := htail i (le_trans (le_max_right N N₀) hi)
      have hjB := htail j (le_trans (le_max_right N N₀) hj)
      have heq : e.1 (w i) (w j) = (uAmalgam d z q hq κ e).1 (u i) (u j) := by
        rw [hwval i hiB, hwval j hjB, uAmalgam_in_in (e := e) hq hiB hjB]
      rw [heq]
      exact hN i (le_trans (le_max_left N N₀) hi) j (le_trans (le_max_left N N₀) hj)
    obtain ⟨a, ha⟩ := hec w hwCauchy
    refine ⟨(κ.symm a : Z), fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := ha ε hε
    refine ⟨max M N₀, fun n hn => ?_⟩
    have hnB := htail n (le_trans (le_max_right M N₀) hn)
    have hxB : (κ.symm a : Z) ∈ uBall d z q := (κ.symm a).2
    have hval : (uAmalgam d z q hq κ e).1 (u n) (κ.symm a : Z) = e.1 (w n) a := by
      rw [uAmalgam_in_in (e := e) hq hnB hxB, ← hwval n hnB,
        Subtype.coe_eta, Equiv.apply_symm_apply]
    rw [hval]
    exact hM n (le_trans (le_max_left M N₀) hn)
  · -- The tail stays outside the ball, where the amalgam is the base metric.
    have htail : ∀ n ≥ N₀, u n ∉ uBall d z q := by
      intro n hn hnB
      exact hmix n hn N₀ le_rfl hnB hB₀
    set v : ℕ → Z := fun n => if u n ∈ uBall d z q then z else u n with hv
    have hvval : ∀ n ≥ N₀, v n = u n := by
      intro n hn
      simp only [hv, if_neg (htail n hn)]
    have hvCauchy : IsCauchySeqOn d.1 v := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨max N N₀, fun i hi j hj => ?_⟩
      have hi₀ := le_trans (le_max_right N N₀) hi
      have hj₀ := le_trans (le_max_right N N₀) hj
      have heq : d.1 (v i) (v j) = (uAmalgam d z q hq κ e).1 (u i) (u j) := by
        rw [hvval i hi₀, hvval j hj₀, uAmalgam_out_out (e := e) hq (htail i hi₀) (htail j hj₀)]
      rw [heq]
      exact hN i (le_trans (le_max_left N N₀) hi) j (le_trans (le_max_left N N₀) hj)
    obtain ⟨x, hx⟩ := hdc v hvCauchy
    obtain ⟨ε₀, hε₀, hiso⟩ := hdm.topology_eq_bot_iff.mp hdbot x
    obtain ⟨N₁, hN₁⟩ := hx ε₀ hε₀
    have hux : ∀ n ≥ max N₁ N₀, u n = x := by
      intro n hn
      rw [← hvval n (le_trans (le_max_right N₁ N₀) hn)]
      exact hiso (v n) (hN₁ n (le_trans (le_max_left N₁ N₀) hn))
    refine ⟨x, fun ε hε => ⟨max N₁ N₀, fun n hn => ?_⟩⟩
    rw [hux n hn, (uAmalgam d z q hq κ e).2.dist_self x]
    exact hε

/-! ## The coding metrics are complete (Lemma 3.10)

`dU_completeSpace` (`Ext/UltraCoding.lean`) is Lemma 3.10's completeness clause,
stated with Mathlib's `CompleteSpace`.  `isCompleteMetricOn_iff_completeSpace`
carries it to the bare-metric form the amalgam lemma consumes; the two are the
same statement. -/

theorem isCompleteMetricOn_phiU (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)}
    {t : ℕ → Bool} (htS : t ∉ S) : IsCompleteMetricOn (phiU hr S t).1 :=
  (isCompleteMetricOn_iff_completeSpace (dU_isMetricOn hr S t)).mpr (dU_completeSpace hr htS)

/-- **The pullback identity on the coded carrier**: `Φ⁻¹(UComp(Z;R)) = 2^ω ∖ S`.
The coding family needs no normalisation — the compatibility criterion of Lemma
3.10 and its completeness clause have the same parameter range — so this is
already the complete-locus form of Theorem 3.12, and it is what the general-space
transfer of Corollary 3.17 consumes. -/
theorem preimage_UComp_phiU (hr : RangeSet.IsScale R r) (S : Set (ℕ → Bool)) :
    phiU hr S ⁻¹' UComp (UltraIndex S) R = Sᶜ := by
  ext t
  simp only [Set.mem_preimage, mem_UComp, mem_UMet, Set.mem_compl_iff]
  constructor
  · rintro ⟨hcomp, -⟩
    exact (isCompatible_phiU_iff hr S t).mp hcomp
  · intro htS
    exact ⟨(isCompatible_phiU_iff hr S t).mpr htS, isCompleteMetricOn_phiU hr htS⟩

/-! ## The normalised amalgam family (audit §2.15)

The Theorem 3.13 family `psiU` of `Ext/UltraComponent.lean`, run over a
normalised base.  Only one new fact is needed about it: it is complete exactly
where it is compatible. -/

section Family

variable {d : UCPM Z R} {z : Z} {q : ℝ} {S : Set (ℕ → Bool)}

/-- **The amalgam family is complete for `t ∉ S`.**  The base is complete and
compatible by normalisation, the coded side is complete by Lemma 3.10, and the
uniform gap at the glue point is the normalisation constant. -/
theorem isCompleteMetricOn_psiU (hr : RangeSet.IsScale R r) (hq : 0 ≤ q)
    (hdm : IsMetricOn d.1) (hdbot : hdm.topology = ⊥) (hdc : IsCompleteMetricOn d.1)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ y : Z, y ∉ uBall d z q → c ≤ d.1 z y)
    (θ : ↥(uBall d z q) ≃ UltraIndex S) {t : ℕ → Bool} (htS : t ∉ S) :
    IsCompleteMetricOn (psiU hr d z q hq θ t).1 :=
  isCompleteMetricOn_uAmalgam hq hdm hdbot hdc hc hgap θ (isCompleteMetricOn_phiU hr htS)

/-- **The pullback identity for the complete locus**: `Ψ⁻¹(UComp(Z;R)) = 2^ω ∖ S`.
Compatibility and completeness of the amalgam have the same parameter range, so
the complete locus traces exactly like `UMet(Z;R)` did in Theorem 3.13. -/
theorem preimage_UComp_psiU (hr : RangeSet.IsScale R r) (hq : 0 ≤ q)
    (hdm : IsMetricOn d.1) (hdbot : hdm.topology = ⊥) (hdc : IsCompleteMetricOn d.1)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ y : Z, y ∉ uBall d z q → c ≤ d.1 z y)
    (θ : ↥(uBall d z q) ≃ UltraIndex S) :
    psiU hr d z q hq θ ⁻¹' UComp Z R = Sᶜ := by
  have hd : UCPM.IsCompatible d := ⟨hdm, hdbot⟩
  ext t
  simp only [Set.mem_preimage, mem_UComp, mem_UMet, Set.mem_compl_iff]
  constructor
  · rintro ⟨hcomp, -⟩
    exact (isCompatible_psiU_iff hr hq hd θ t).mp hcomp
  · intro htS
    exact ⟨(isCompatible_psiU_iff hr hq hd θ t).mpr htS,
      isCompleteMetricOn_psiU hr hq hdm hdbot hdc hc hgap θ htS⟩

/-- The same pullback, for the component's complete part.  The finite-distance
clause of the component holds for *every* parameter (the audited bound
`𝒰𝒟^R(m_t,d) ≤ q ∨ r 0`), so intersecting with the component imposes no further
condition — which is why the componentwise and the component-free statements of
Theorem 3.16 reach the same contradiction. -/
theorem preimage_UComponent_inter_UComp_psiU (hr : RangeSet.IsScale R r) (hq : 0 ≤ q)
    (hqR : q ∈ R.carrier) (hdm : IsMetricOn d.1) (hdbot : hdm.topology = ⊥)
    (hdc : IsCompleteMetricOn d.1) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ y : Z, y ∉ uBall d z q → c ≤ d.1 z y)
    (θ : ↥(uBall d z q) ≃ UltraIndex S) :
    psiU hr d z q hq θ ⁻¹' (UComponent d ∩ UComp Z R) = Sᶜ := by
  rw [Set.preimage_inter, preimage_UComponent_psiU hr hq hqR ⟨hdm, hdbot⟩ θ,
    preimage_UComp_psiU hr hq hdm hdbot hdc hc hgap θ, Set.inter_self]

end Family

/-! ## Theorem 3.16 -/

-- `ucpmMeasurableSpace`/`ucpmBorelSpace` (`Ext.UltraCoding`) are declared
-- `local instance` there, so they are re-registered here.  They are the same
-- constants, so `MeasurableSet` below means what it means in `umet_not_borel`
-- and in `ucomponent_not_borel_of_card`.
attribute [local instance] ucpmMeasurableSpace ucpmBorelSpace

/-- **The normalised Theorem 3.13 setup.**  For every discrete carrier of
cardinality `ℵ₁`, every characteristic `R` and every compatible `R`-valued
ultrametric `d`, there is a continuous family `Ψ : 2^ω → UCPM(Z;R)` whose
pullbacks of `UComp(Z;R)` and of `𝔠^R ∩ UComp(Z;R)` are both the complement of a
non-Borel parameter set.

This is where the audit's normalisation happens: the family is the Theorem 3.13
amalgam over `d ∨ c` rather than over `d`, and `UComponent_uSupConstOffDiag`
identifies the component of the normalised base with the component of `d`.
Compatibility of `d` itself is therefore never used — the normalisation supplies
it — so the hypothesis is carried unreferenced, to keep the component indexed as
the audit indexes it. -/
theorem exists_ucomp_witness (hR : R.IsCharacteristic) (Z : Type*) (hZ : #Z = aleph 1)
    (d : UCPM Z R) (_hd : d ∈ UMet Z R) :
    ∃ (S : Set (ℕ → Bool)) (Ψ : (ℕ → Bool) → UCPM Z R), ¬ MeasurableSet S ∧ Continuous Ψ ∧
      Ψ ⁻¹' UComp Z R = Sᶜ ∧ Ψ ⁻¹' (UComponent d ∩ UComp Z R) = Sᶜ := by
  obtain ⟨rr, hr⟩ := RangeSet.exists_isScale hR
  obtain ⟨S, -, hScard, hSnonmeas⟩ := exists_dense_aleph1_nonBorel_cantor
  -- a nonzero member of `R`, the normalisation constant of audit §2.15
  obtain ⟨c, hcR, hc, -⟩ := hR 1 one_pos
  have hd'm : IsMetricOn (uSupConstOffDiag hcR d).1 := isMetricOn_supConstOffDiag hc hcR d.2
  have hd'bot : hd'm.topology = ⊥ := topology_supConstOffDiag_eq_bot hc hcR d.2
  have hd'c : IsCompleteMetricOn (uSupConstOffDiag hcR d).1 :=
    isCompleteMetricOn_supConstOffDiag hc hcR d.2
  -- `Z` is uncountable, hence in particular nonempty
  have hZcount : ¬ Countable Z := by
    intro hcnt
    haveI := hcnt
    have hle : #Z ≤ (ℵ₀ : Cardinal) := Cardinal.mk_le_aleph0
    rw [hZ] at hle
    exact absurd hle (not_le_of_gt Cardinal.aleph0_lt_aleph_one)
  obtain ⟨z⟩ : Nonempty Z := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hZcount inferInstance
  -- an uncountable closed ball of radius in `R`, around the *normalised* base
  obtain ⟨q, hqR, hqunc⟩ := exists_radius_not_countable (uSupConstOffDiag hcR d) z hZcount
  have hq : 0 ≤ q := R.nonneg hqR
  have hballcard : #(↥(uBall (uSupConstOffDiag hcR d) z q)) = aleph 1 := by
    refine le_antisymm ((Cardinal.mk_set_le _).trans hZ.le) ?_
    exact Cardinal.aleph_one_le_iff.mpr
      (Cardinal.aleph0_lt_mk_iff.mpr (not_countable_iff.mp hqunc))
  obtain ⟨θ⟩ : Nonempty (↥(uBall (uSupConstOffDiag hcR d) z q) ≃ UltraIndex S) := by
    refine Cardinal.lift_mk_eq'.mp ?_
    rw [hballcard, card_ultraIndex hScard]
    simp
  -- the uniform gap at the glue point is the normalisation constant
  have hgap : ∀ y : Z, y ∉ uBall (uSupConstOffDiag hcR d) z q →
      c ≤ (uSupConstOffDiag hcR d).1 z y := by
    intro y hy
    have hzy : z ≠ y := by
      intro hzy
      refine hy ?_
      show (uSupConstOffDiag hcR d).1 z y ≤ q
      rw [← hzy, (uSupConstOffDiag hcR d).2.dist_self]
      exact hq
    exact le_supConstOffDiag hzy
  refine ⟨S, psiU hr (uSupConstOffDiag hcR d) z q hq θ, hSnonmeas, continuous_psiU hr hq θ,
    preimage_UComp_psiU hr hq hd'm hd'bot hd'c hc hgap θ, ?_⟩
  rw [← UComponent_uSupConstOffDiag (R.nonneg hcR) hcR d]
  exact preimage_UComponent_inter_UComp_psiU hr hq hqR hd'm hd'bot hd'c hc hgap θ

/-- **Theorem 3.16, componentwise** (audit §2.15).  For every discrete `Z` with
`|Z| = ℵ₁`, every characteristic range set `R` and every compatible `R`-valued
ultrametric `d` on `Z`, the complete part `𝔠^R ∩ UComp(Z;R)` of the `R`-component
of `d` is not Borel in `UCPM(Z;R)`.

The base of the construction is not `d` but its normalisation `d ∨ c` off the
diagonal (audit §2.15), which is complete, compatible and represents the same
`R`-component. -/
theorem ucomponent_inter_ucomp_not_borel (hR : R.IsCharacteristic) (Z : Type*)
    (hZ : #Z = aleph 1) (d : UCPM Z R) (hd : d ∈ UMet Z R) :
    ¬ MeasurableSet (UComponent d ∩ UComp Z R) := by
  intro hmeas
  obtain ⟨S, Ψ, hSnonmeas, hcont, -, hpre⟩ := exists_ucomp_witness hR Z hZ d hd
  have h : MeasurableSet (Ψ ⁻¹' (UComponent d ∩ UComp Z R)) :=
    hmeas.preimage hcont.measurable
  rw [hpre] at h
  exact hSnonmeas (by simpa using h.compl)

/-- **Theorem 3.16, the "consequently" part** (audit §2.15).  For every discrete
`Z` with `|Z| = ℵ₁` and every characteristic range set `R`, the complete
compatible `R`-valued ultrametrics `UComp(Z;R)` are not Borel in `UCPM(Z;R)`.

As on the Archimedean side (audit §2.11) this does *not* follow by intersecting
with a component, which is itself non-Borel; it follows from the pullback
identity `Ψ⁻¹(UComp(Z;R)) = 2^ω ∖ S`, in which the component plays no role.  The
representative used to build the setup is supplied by `exists_mem_UMet_of_card`
and carries no information into the statement. -/
theorem ucomp_not_borel_of_card (hR : R.IsCharacteristic) (Z : Type*)
    (hZ : #Z = aleph 1) : ¬ MeasurableSet (UComp Z R) := by
  intro hmeas
  obtain ⟨d, hd⟩ := exists_mem_UMet_of_card hR Z hZ
  obtain ⟨S, Ψ, hSnonmeas, hcont, hpre, -⟩ := exists_ucomp_witness hR Z hZ d hd
  have h : MeasurableSet (Ψ ⁻¹' UComp Z R) := hmeas.preimage hcont.measurable
  rw [hpre] at h
  exact hSnonmeas (by simpa using h.compl)

/-- Neither form of Theorem 3.16 is vacuous: a non-Borel set is nonempty, so
every `R`-component does meet `UComp(Z;R)`.  This is the clause Corollary 3.17
needs, in the form "`UComp` of the coded carrier is nonempty". -/
theorem nonempty_ucomponent_inter_ucomp (hR : R.IsCharacteristic) (Z : Type*)
    (hZ : #Z = aleph 1) (d : UCPM Z R) (hd : d ∈ UMet Z R) :
    (UComponent d ∩ UComp Z R).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  exact ucomponent_inter_ucomp_not_borel hR Z hZ d hd (hempty ▸ MeasurableSet.empty)

end

end IshikiExt
