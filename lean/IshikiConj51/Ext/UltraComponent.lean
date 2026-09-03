-- Ext.UltraComponent
--
-- Issue #81, scope item 6: Theorem 3.13 of arXiv:2608.19618 — every
-- `R`-component of `UMet(Z;R)` is non-Borel in `UCPM(Z;R)`.
--
-- Mathematical source of truth: the Theorem 3.13 paragraph of
-- `notes/borel-preprint-audit.md` §2.14.
--
-- The argument, following the audit exactly:
--
-- 1. `R` has a countable cofinal subset and `d` is `R`-valued, so the closed
--    balls `E_q = {x : d(z,x) ≤ q}` with `q ∈ R` cover `Z`; since `|Z| = ℵ₁`
--    is uncountable and the cover is countable, one of them is uncountable,
--    hence of cardinality `ℵ₁`.
-- 2. Transfer the Lemma 3.10 coding to `E := E_q` along a bijection `θ`.
-- 3. Amalgamate with `d` at the single point `z` by the *max* form
--    `m_t(x,a) = d(x,z) ∨ e_t(z,a)`.  In Lean the amalgam is realised as the
--    pointwise maximum of two pullbacks,
--
--       `m_t = (d ∘ retract) ∨ (e_t ∘ into)`,
--
--    where `retract` collapses `E` to `z` and `into` collapses the complement
--    of `E` to `z`.  Both operations are the reusable ones of
--    `Ext/UltraPMet.lean` (`UCPM.comap`, `UCPM.sup`), so the ultrametric and
--    `R`-valuedness axioms of `m_t` are discharged by construction; only
--    separation, compatibility and the distance estimates need proof.
-- 4. `𝒰𝒟^R(m_t, d) ≤ q ∨ r 0` — the audit's bound, verified case by case,
--    the mixed case using the ultrametric isosceles identity `d(x,a) = d(x,z)`
--    for `d(x,z) > q ≥ d(z,a)`.  In particular `m_t` lies in the component of
--    `d` for *every* `t`, so membership in `𝔠^R` reduces to compatibility.
-- 5. `m_t` is compatible **iff** `t ∉ S`, and `t ↦ m_t` is a `𝒰𝒟^R`-isometry
--    from the Cantor ultrametric; the trace, closed image and pullback
--    identities follow as in Theorem 3.12.
--
-- One deviation from the preprint's phrasing, recorded because it *weakens*
-- what is assumed: the audit transfers the coding "with the centre `y_0 ↦ z`".
-- The amalgam below glues at `θ(z)` whatever that point is, and no property of
-- it beyond `z ∈ E` is used — every cluster value is `≤ r 0`, which is all the
-- estimates need.  The normalisation is therefore a labelling convention, and
-- the arbitrary bijection `θ` is used unchanged.
--
-- Status: sorry-free; no custom axioms.

import IshikiConj51.Ext.UltraCoding

open Cardinal Set

namespace IshikiExt

noncomputable section

variable {Z W : Type*} {R : RangeSet} {r : ℕ → ℝ}

/-! ## A countable cofinal subset of a set of reals -/

/-- Every set of reals has a countable cofinal subset: a sequence approaching
its supremum from below, the supremum itself when it is attained, or a sequence
escaping to `+∞`.  This is the "`R ⊆ [0,∞)` has a countable cofinal subset"
step of audit §2.14. -/
theorem exists_countable_cofinal (A : Set ℝ) :
    ∃ Q ⊆ A, Q.Countable ∧ ∀ x ∈ A, ∃ y ∈ Q, x ≤ y := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨∅, Set.Subset.rfl, Set.countable_empty, by simp⟩
  by_cases hbdd : BddAbove A
  · by_cases hmem : sSup A ∈ A
    · exact ⟨{sSup A}, by simpa using hmem, Set.countable_singleton _,
        fun x hx => ⟨sSup A, rfl, le_csSup hbdd hx⟩⟩
    · have hchoice : ∀ n : ℕ, ∃ a ∈ A, sSup A - 1 / ((n : ℝ) + 1) < a := by
        intro n
        refine exists_lt_of_lt_csSup hA ?_
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      choose a ha hlt using hchoice
      refine ⟨Set.range a, ?_, Set.countable_range a, ?_⟩
      · rintro _ ⟨n, rfl⟩
        exact ha n
      · intro x hx
        have hxlt : x < sSup A :=
          lt_of_le_of_ne (le_csSup hbdd hx) fun h => hmem (h ▸ hx)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxlt)
        exact ⟨a n, ⟨n, rfl⟩, le_of_lt (by linarith [hlt n])⟩
  · have hchoice : ∀ n : ℕ, ∃ a ∈ A, (n : ℝ) < a := by
      intro n
      by_contra hcon
      push Not at hcon
      exact hbdd ⟨(n : ℝ), fun x hx => hcon x hx⟩
    choose a ha hlt using hchoice
    refine ⟨Set.range a, ?_, Set.countable_range a, ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact ha n
    · intro x hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨a n, ⟨n, rfl⟩, le_of_lt (hn.trans (hlt n))⟩

/-! ## Closed balls of an `R`-valued ultrametric -/

/-- The closed `d`-ball of radius `q` around `z`. -/
def uBall (d : UCPM Z R) (z : Z) (q : ℝ) : Set Z := {x | d.1 z x ≤ q}

@[simp] theorem mem_uBall {d : UCPM Z R} {z : Z} {q : ℝ} {x : Z} :
    x ∈ uBall d z q ↔ d.1 z x ≤ q := Iff.rfl

theorem mem_uBall_self (d : UCPM Z R) (z : Z) {q : ℝ} (hq : 0 ≤ q) : z ∈ uBall d z q := by
  simpa [uBall, d.2.dist_self z] using hq

/-- The ball has diameter at most its radius: the strong triangle inequality
turns "both endpoints near `z`" into "the endpoints are near each other". -/
theorem uBall_dist_le {d : UCPM Z R} {z : Z} {q : ℝ} {x y : Z}
    (hx : x ∈ uBall d z q) (hy : y ∈ uBall d z q) : d.1 x y ≤ q := by
  refine (d.2.dist_triangle_max x z y).trans (max_le ?_ hy)
  rw [d.2.dist_comm x z]
  exact hx

/-- **Isosceles identity off the ball.**  A point outside the ball is exactly
as far from every point of the ball as it is from the centre. -/
theorem uBall_isosceles {d : UCPM Z R} {z : Z} {q : ℝ} {x y : Z}
    (hx : x ∉ uBall d z q) (hy : y ∈ uBall d z q) : d.1 x y = d.1 x z := by
  have hlt : d.1 z y < d.1 x z := by
    rw [d.2.dist_comm x z]
    exact lt_of_le_of_lt hy (not_le.mp hx)
  exact d.2.eq_of_lt hlt

/-- **The ball selection** (audit §2.14).  Some closed ball of radius in `R` is
uncountable.  A countable cofinal `Q ⊆ R` makes `{E_q : q ∈ Q}` a countable
cover of `Z`, so a countable union would exhaust an uncountable `Z`. -/
theorem exists_radius_not_countable (d : UCPM Z R) (z : Z) (hZ : ¬ Countable Z) :
    ∃ q ∈ R.carrier, ¬ Countable ↥(uBall d z q) := by
  obtain ⟨Q, hQA, hQc, hQcof⟩ := exists_countable_cofinal R.carrier
  by_contra hcon
  push Not at hcon
  have hcover : (Set.univ : Set Z) = ⋃ q ∈ Q, uBall d z q := by
    ext x
    simp only [Set.mem_univ, true_iff, Set.mem_iUnion]
    obtain ⟨y, hyQ, hy⟩ := hQcof (d.1 z x) (d.2.mem_range z x)
    exact ⟨y, hyQ, hy⟩
  have huniv : (Set.univ : Set Z).Countable := by
    rw [hcover]
    exact Set.Countable.biUnion hQc fun q hq => Set.countable_coe_iff.mp (hcon q (hQA hq))
  exact hZ (Set.countable_univ_iff.mp huniv)

/-! ## The one-point max-amalgam -/

open Classical in
/-- Collapse the ball to its centre. -/
def uRetract (d : UCPM Z R) (z : Z) (q : ℝ) (x : Z) : Z :=
  if x ∈ uBall d z q then z else x

open Classical in
/-- Collapse the complement of the ball to the centre. -/
def uInto (d : UCPM Z R) (z : Z) (q : ℝ) (hq : 0 ≤ q) (x : Z) : ↥(uBall d z q) :=
  if h : x ∈ uBall d z q then ⟨x, h⟩ else ⟨z, mem_uBall_self d z hq⟩

theorem uRetract_of_mem {d : UCPM Z R} {z : Z} {q : ℝ} {x : Z} (hx : x ∈ uBall d z q) :
    uRetract d z q x = z := by
  rw [uRetract, if_pos hx]

theorem uRetract_of_notMem {d : UCPM Z R} {z : Z} {q : ℝ} {x : Z} (hx : x ∉ uBall d z q) :
    uRetract d z q x = x := by
  rw [uRetract, if_neg hx]

theorem uInto_of_mem {d : UCPM Z R} {z : Z} {q : ℝ} {hq : 0 ≤ q} {x : Z}
    (hx : x ∈ uBall d z q) : uInto d z q hq x = ⟨x, hx⟩ := by
  rw [uInto, dif_pos hx]

theorem uInto_of_notMem {d : UCPM Z R} {z : Z} {q : ℝ} {hq : 0 ≤ q} {x : Z}
    (hx : x ∉ uBall d z q) : uInto d z q hq x = ⟨z, mem_uBall_self d z hq⟩ := by
  rw [uInto, dif_neg hx]

/-- **The one-point max-amalgam** of the base `d` with a coding `e` transported
into the ball along `κ`.  It is the pointwise maximum of two pullbacks, so it
is an `R`-valued ultrametric by construction. -/
def uAmalgam (d : UCPM Z R) (z : Z) (q : ℝ) (hq : 0 ≤ q)
    (κ : ↥(uBall d z q) → W) (e : UCPM W R) : UCPM Z R :=
  UCPM.sup (UCPM.comap (uRetract d z q) d) (UCPM.comap (κ ∘ uInto d z q hq) e)

section Amalgam

variable {d : UCPM Z R} {z : Z} {q : ℝ} {κ : ↥(uBall d z q) → W} {e : UCPM W R}

theorem uAmalgam_val (hq : 0 ≤ q) (x y : Z) :
    (uAmalgam d z q hq κ e).1 x y
      = max (d.1 (uRetract d z q x) (uRetract d z q y))
        (e.1 (κ (uInto d z q hq x)) (κ (uInto d z q hq y))) := rfl

theorem base_le_uAmalgam (hq : 0 ≤ q) (x y : Z) :
    d.1 (uRetract d z q x) (uRetract d z q y) ≤ (uAmalgam d z q hq κ e).1 x y :=
  le_max_left _ _

theorem coding_le_uAmalgam (hq : 0 ≤ q) (x y : Z) :
    e.1 (κ (uInto d z q hq x)) (κ (uInto d z q hq y)) ≤ (uAmalgam d z q hq κ e).1 x y :=
  le_max_right _ _

theorem uAmalgam_in_in (hq : 0 ≤ q) {x y : Z} (hx : x ∈ uBall d z q) (hy : y ∈ uBall d z q) :
    (uAmalgam d z q hq κ e).1 x y = e.1 (κ ⟨x, hx⟩) (κ ⟨y, hy⟩) := by
  rw [uAmalgam_val hq, uRetract_of_mem hx, uRetract_of_mem hy, uInto_of_mem hx,
    uInto_of_mem hy, d.2.dist_self z]
  exact max_eq_right (e.2.nonneg _ _)

theorem uAmalgam_out_out (hq : 0 ≤ q) {x y : Z} (hx : x ∉ uBall d z q)
    (hy : y ∉ uBall d z q) : (uAmalgam d z q hq κ e).1 x y = d.1 x y := by
  rw [uAmalgam_val hq, uRetract_of_notMem hx, uRetract_of_notMem hy, uInto_of_notMem hx,
    uInto_of_notMem hy, e.2.dist_self _]
  exact max_eq_left (d.2.nonneg x y)

/-! ### The membership bound `𝒰𝒟^R(m_t, d) ≤ q ∨ r 0` -/

/-- **The audited component bound.**  If every value of the transported coding
is at most `c`, then `𝒰𝒟^R(d, m) ≤ q ∨ c`.  In particular the amalgam always
lies in the `R`-component of `d`, whatever the parameter is; membership in the
component therefore reduces to compatibility. -/
theorem edist_uAmalgam_le (hq : 0 ≤ q) (hqR : q ∈ R.carrier) {c : ℝ} (hcR : c ∈ R.carrier)
    (hc : ∀ a b, e.1 a b ≤ c) :
    UCPM.edist d (uAmalgam d z q hq κ e) ≤ ENNReal.ofReal (max q c) := by
  refine UCPM.edist_le_ofReal ⟨R.max_mem hqR hcR, fun x y => ?_⟩
  by_cases hx : x ∈ uBall d z q
  · by_cases hy : y ∈ uBall d z q
    · -- both endpoints in the ball: both values are `≤ q ∨ c`
      rw [uAmalgam_in_in hq hx hy]
      exact ⟨le_max_of_le_right (le_max_of_le_left (uBall_dist_le hx hy)),
        le_max_of_le_right (le_max_of_le_right (hc _ _))⟩
    · -- mixed: the isosceles identity makes the cross value equal to `d x y`
      have hzy : d.1 z y = d.1 x y := by
        rw [d.2.dist_comm z y, ← uBall_isosceles hy hx]
        exact d.2.dist_comm y x
      rw [uAmalgam_val hq, uRetract_of_mem hx, uRetract_of_notMem hy, uInto_of_mem hx,
        uInto_of_notMem hy, hzy]
      exact ⟨le_max_of_le_left (le_max_left _ _),
        max_le (le_max_left _ _) (le_max_of_le_right (le_max_of_le_right (hc _ _)))⟩
  · by_cases hy : y ∈ uBall d z q
    · have hxz : d.1 x z = d.1 x y := (uBall_isosceles hx hy).symm
      rw [uAmalgam_val hq, uRetract_of_notMem hx, uRetract_of_mem hy, uInto_of_notMem hx,
        uInto_of_mem hy, hxz]
      exact ⟨le_max_of_le_left (le_max_left _ _),
        max_le (le_max_left _ _) (le_max_of_le_right (le_max_of_le_right (hc _ _)))⟩
    · rw [uAmalgam_out_out hq hx hy]
      exact ⟨le_max_left _ _, le_max_left _ _⟩

/-! ## Theorem 3.13 -/

section Component

variable (hr : RangeSet.IsScale R r) {S : Set (ℕ → Bool)}

/-- The transported coding family: the Lemma 3.10 coding on the ball, glued to
the base metric at the centre.  This is the preprint's `m_t`. -/
def psiU (hr : RangeSet.IsScale R r) (d : UCPM Z R) (z : Z) (q : ℝ) (hq : 0 ≤ q)
    {S : Set (ℕ → Bool)} (θ : ↥(uBall d z q) → UltraIndex S) (t : ℕ → Bool) : UCPM Z R :=
  uAmalgam d z q hq θ (phiU hr S t)

theorem psiU_val (hq : 0 ≤ q) (θ : ↥(uBall d z q) → UltraIndex S) (t : ℕ → Bool) (x y : Z) :
    (psiU hr d z q hq θ t).1 x y
      = max (d.1 (uRetract d z q x) (uRetract d z q y))
        (dU r S t (θ (uInto d z q hq x)) (θ (uInto d z q hq y))) := rfl

theorem psiU_in_in (hq : 0 ≤ q) {θ : ↥(uBall d z q) → UltraIndex S} {t : ℕ → Bool} {x y : Z}
    (hx : x ∈ uBall d z q) (hy : y ∈ uBall d z q) :
    (psiU hr d z q hq θ t).1 x y = dU r S t (θ ⟨x, hx⟩) (θ ⟨y, hy⟩) :=
  uAmalgam_in_in (κ := θ) (e := phiU hr S t) hq hx hy

theorem psiU_out_out (hq : 0 ≤ q) {θ : ↥(uBall d z q) → UltraIndex S} {t : ℕ → Bool} {x y : Z}
    (hx : x ∉ uBall d z q) (hy : y ∉ uBall d z q) :
    (psiU hr d z q hq θ t).1 x y = d.1 x y :=
  uAmalgam_out_out (κ := θ) (e := phiU hr S t) hq hx hy

/-- Reading the amalgam at a pair pulled back from the coded carrier: there it
*is* the coding, which is what lets Lemma 3.11's separating pair be reused. -/
theorem psiU_val_symm (hq : 0 ≤ q) (θ : ↥(uBall d z q) ≃ UltraIndex S) (t : ℕ → Bool)
    (u v : UltraIndex S) :
    (psiU hr d z q hq θ t).1 (θ.symm u : Z) (θ.symm v : Z) = dU r S t u v := by
  rw [psiU_in_in hr hq (θ.symm u).2 (θ.symm v).2, Subtype.coe_eta, Subtype.coe_eta,
    θ.apply_symm_apply, θ.apply_symm_apply]

/-- The amalgam lies in the `R`-component of `d`, for every parameter. -/
theorem edist_psiU_lt_top (hq : 0 ≤ q) (hqR : q ∈ R.carrier)
    {θ : ↥(uBall d z q) → UltraIndex S} (t : ℕ → Bool) :
    UCPM.edist d (psiU hr d z q hq θ t) < ⊤ :=
  lt_of_le_of_lt
    (edist_uAmalgam_le (κ := θ) (e := phiU hr S t) hq hqR (hr.mem 0)
      (fun a b => dU_le_head hr S t a b))
    ENNReal.ofReal_lt_top

/-- **Compatibility of the amalgam, `t ∉ S`.**  Inside the ball the isolating
radii are those of Lemma 3.10; outside they are those of the base metric `d`;
across the boundary the distance is at least `d(z,·)`, which the compatibility
of `d` bounds away from `0`. -/
theorem psiU_topology_eq_bot (hq : 0 ≤ q) (hd : UCPM.IsCompatible d)
    (θ : ↥(uBall d z q) ≃ UltraIndex S) {t : ℕ → Bool} (htS : t ∉ S) :
    UCPM.IsCompatible (psiU hr d z q hq θ t) := by
  obtain ⟨hdm, hdbot⟩ := hd
  have hdiso := hdm.topology_eq_bot_iff.mp hdbot
  have hbase : ∀ x y : Z, d.1 (uRetract d z q x) (uRetract d z q y)
      ≤ (psiU hr d z q hq θ t).1 x y := base_le_uAmalgam hq
  have hcm : IsMetricOn (psiU hr d z q hq θ t).1 := by
    refine (psiU hr d z q hq θ t).2.toIsMetricOn fun x y hxy => ?_
    by_cases hx : x ∈ uBall d z q
    · by_cases hy : y ∈ uBall d z q
      · rw [psiU_in_in hr hq hx hy] at hxy
        have hθ := (dU_isMetricOn hr S t).eq_of_dist_eq_zero hxy
        exact congrArg Subtype.val (θ.injective hθ)
      · exfalso
        have hle := hbase x y
        rw [uRetract_of_mem hx, uRetract_of_notMem hy, hxy] at hle
        have h0 : d.1 z y = 0 := le_antisymm hle (d.2.nonneg z y)
        exact hy (mem_uBall.mpr (by rw [h0]; exact hq))
    · by_cases hy : y ∈ uBall d z q
      · exfalso
        have hle := hbase x y
        rw [uRetract_of_notMem hx, uRetract_of_mem hy, hxy] at hle
        have h0 : d.1 z x = 0 := by
          rw [d.2.dist_comm z x]
          exact le_antisymm hle (d.2.nonneg x z)
        exact hx (mem_uBall.mpr (by rw [h0]; exact hq))
      · rw [psiU_out_out hr hq hx hy] at hxy
        exact hdm.eq_of_dist_eq_zero hxy
  refine ⟨hcm, hcm.topology_eq_bot_iff.mpr fun u => ?_⟩
  by_cases hu : u ∈ uBall d z q
  · -- inside the ball
    obtain ⟨ε₁, hε₁, hall₁⟩ :=
      (dU_isMetricOn hr S t).topology_eq_bot_iff.mp (dU_topology_eq_bot hr htS) (θ ⟨u, hu⟩)
    obtain ⟨ε₂, hε₂, hall₂⟩ := hdiso z
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun v hv => ?_⟩
    by_cases hvB : v ∈ uBall d z q
    · rw [psiU_in_in hr hq hvB hu] at hv
      have hθ := hall₁ _ (lt_of_lt_of_le hv (min_le_left _ _))
      exact congrArg Subtype.val (θ.injective hθ)
    · exfalso
      have hle := hbase v u
      rw [uRetract_of_notMem hvB, uRetract_of_mem hu] at hle
      have hvz : v = z := hall₂ v (lt_of_le_of_lt hle (lt_of_lt_of_le hv (min_le_right _ _)))
      exact hvB (by rw [hvz]; exact mem_uBall_self d z hq)
  · -- outside the ball
    obtain ⟨ε₃, hε₃, hall₃⟩ := hdiso u
    have hzu : 0 < d.1 z u := lt_of_le_of_lt hq (not_le.mp hu)
    refine ⟨min ε₃ (d.1 z u), lt_min hε₃ hzu, fun v hv => ?_⟩
    by_cases hvB : v ∈ uBall d z q
    · exfalso
      have hle := hbase v u
      rw [uRetract_of_mem hvB, uRetract_of_notMem hu] at hle
      exact absurd (lt_of_le_of_lt hle (lt_of_lt_of_le hv (min_le_right _ _))) (lt_irrefl _)
    · rw [psiU_out_out hr hq hvB hu] at hv
      exact hall₃ v (lt_of_lt_of_le hv (min_le_left _ _))

/-- **Compatibility fails at `t ∈ S`.**  The failing pair of Lemma 3.10 lives
inside the ball, where the amalgam *is* the transported coding. -/
theorem psiU_topology_ne_bot (hq : 0 ≤ q) (θ : ↥(uBall d z q) ≃ UltraIndex S)
    {t : ℕ → Bool} (htS : t ∈ S) : ¬ UCPM.IsCompatible (psiU hr d z q hq θ t) := by
  rintro ⟨hcm, hbot⟩
  obtain ⟨ε, hε, hall⟩ :=
    hcm.topology_eq_bot_iff.mp hbot (θ.symm ((⟨t, htS⟩ : ↥S), none) : Z)
  obtain ⟨n, hn⟩ := hr.exists_lt hε
  have hval : dU r S t ((⟨t, htS⟩ : ↥S), some n) ((⟨t, htS⟩ : ↥S), none) = r n := by
    rw [dU_same, clusterDist, if_neg (by simp : (some n : Option ℕ) ≠ none)]
    show max (uRadius r t t (some n)) (uRadius r t t none) = r n
    rw [uRadius_some, uRadius_none, cantorDist_self, max_eq_right (hr.nonneg n),
      max_eq_left (hr.nonneg n)]
  have hlt : (psiU hr d z q hq θ t).1 (θ.symm ((⟨t, htS⟩ : ↥S), some n) : Z)
      (θ.symm ((⟨t, htS⟩ : ↥S), none) : Z) < ε := by
    rw [psiU_val_symm hr hq θ t, hval]
    exact hn
  have heq := hall _ hlt
  have hinj := θ.symm.injective (Subtype.ext heq)
  simp at hinj

/-- **Compatibility of the amalgam, both directions.** -/
theorem isCompatible_psiU_iff (hq : 0 ≤ q) (hd : UCPM.IsCompatible d)
    (θ : ↥(uBall d z q) ≃ UltraIndex S) (t : ℕ → Bool) :
    UCPM.IsCompatible (psiU hr d z q hq θ t) ↔ t ∉ S :=
  ⟨fun h htS => psiU_topology_ne_bot hr hq θ htS h,
    fun htS => psiU_topology_eq_bot hr hq hd θ htS⟩

/-! ### The isometry -/

theorem edist_psiU_le (hq : 0 ≤ q) {θ : ↥(uBall d z q) → UltraIndex S} (s t : ℕ → Bool) :
    UCPM.edist (psiU hr d z q hq θ s) (psiU hr d z q hq θ t)
      ≤ ENNReal.ofReal (cantorDist r s t) := by
  refine UCPM.edist_le_ofReal ⟨cantorDist_mem hr s t, fun x y => ⟨?_, ?_⟩⟩
  · rw [psiU_val hr hq, psiU_val hr hq]
    refine max_le (le_max_of_le_left (le_max_left _ _)) ?_
    refine (dU_le_max hr S s t _ _).trans ?_
    exact max_le (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _)
  · rw [psiU_val hr hq, psiU_val hr hq]
    refine max_le (le_max_of_le_left (le_max_left _ _)) ?_
    have h := dU_le_max hr S t s (θ (uInto d z q hq x)) (θ (uInto d z q hq y))
    rw [cantorDist_comm r t s] at h
    exact h.trans (max_le (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _))

/-- **The amalgam family is an exact `𝒰𝒟^R`-isometry** (audit §2.14): the
separating pair of Lemma 3.11 lies inside the ball, where the amalgam is the
transported coding, so the lower bound transports verbatim — density of `S` is
used here exactly as in Lemma 3.11. -/
theorem edist_psiU (hq : 0 ≤ q) (hS : Dense S) (θ : ↥(uBall d z q) ≃ UltraIndex S)
    (s t : ℕ → Bool) :
    UCPM.edist (psiU hr d z q hq θ s) (psiU hr d z q hq θ t)
      = ENNReal.ofReal (cantorDist r s t) := by
  refine le_antisymm (edist_psiU_le hr hq s t) ?_
  rcases eq_or_ne s t with rfl | hst
  · simp
  obtain ⟨u, v, hus, hut⟩ := exists_separating_pair hr hS hst
  refine UCPM.ofReal_le_edist fun c hc => ?_
  refine UCPM.le_of_mem_tolerances hc (θ.symm u : Z) (θ.symm v : Z) ?_ ?_
  · rw [psiU_val_symm hr hq θ s]
    exact hus
  · rw [psiU_val_symm hr hq θ t]
    exact hut

theorem continuous_psiU (hq : 0 ≤ q) (θ : ↥(uBall d z q) → UltraIndex S) :
    Continuous (psiU hr d z q hq θ) :=
  continuous_of_edist_le_cantorDist hr fun s t => edist_psiU_le hr hq s t

/-! ### The pullback, trace and closed-image identities -/

/-- **The exact pullback identity for the component**: `Ψ⁻¹(𝔠^R) = 2^ω ∖ S`.
The finite-distance clause is automatic — that is the content of the audited
bound `𝒰𝒟^R(m_t,d) ≤ q ∨ r 0` — so the component traces exactly like
`UMet(Z;R)` did in Theorem 3.12. -/
theorem preimage_UComponent_psiU (hq : 0 ≤ q) (hqR : q ∈ R.carrier)
    (hd : UCPM.IsCompatible d) (θ : ↥(uBall d z q) ≃ UltraIndex S) :
    psiU hr d z q hq θ ⁻¹' UComponent d = Sᶜ := by
  ext t
  simp only [Set.mem_preimage, mem_UComponent, mem_UMet, Set.mem_compl_iff]
  constructor
  · rintro ⟨hcomp, -⟩
    exact (isCompatible_psiU_iff hr hq hd θ t).mp hcomp
  · intro htS
    exact ⟨(isCompatible_psiU_iff hr hq hd θ t).mpr htS, edist_psiU_lt_top hr hq hqR t⟩

theorem isCompact_range_psiU (hq : 0 ≤ q) (θ : ↥(uBall d z q) → UltraIndex S) :
    IsCompact (Set.range (psiU hr d z q hq θ)) :=
  isCompact_range (continuous_psiU hr hq θ)

/-- **The trace identity** `L' ∩ 𝔠^R = Ψ(2^ω ∖ S)` (audit §2.14). -/
theorem image_compl_eq_range_inter_UComponent (hq : 0 ≤ q) (hqR : q ∈ R.carrier)
    (hd : UCPM.IsCompatible d) (θ : ↥(uBall d z q) ≃ UltraIndex S) :
    psiU hr d z q hq θ '' Sᶜ = Set.range (psiU hr d z q hq θ) ∩ UComponent d := by
  rw [← preimage_UComponent_psiU hr hq hqR hd θ]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, rfl⟩, ht⟩
  · rintro ⟨⟨t, rfl⟩, hx⟩
    exact ⟨t, hx, rfl⟩

/-- **Closed image**: `Ψ(2^ω ∖ S)` is closed in the component `𝔠^R` with its
subspace topology. -/
theorem isClosed_image_psiU (hq : 0 ≤ q) (hqR : q ∈ R.carrier) (hd : UCPM.IsCompatible d)
    (θ : ↥(uBall d z q) ≃ UltraIndex S) :
    IsClosed (Subtype.val ⁻¹' (psiU hr d z q hq θ '' Sᶜ) : Set ↥(UComponent d)) := by
  rw [image_compl_eq_range_inter_UComponent hr hq hqR hd θ]
  have hpre : (Subtype.val ⁻¹' (Set.range (psiU hr d z q hq θ) ∩ UComponent d) :
      Set ↥(UComponent d)) = Subtype.val ⁻¹' Set.range (psiU hr d z q hq θ) := by
    ext x
    simp
  rw [hpre]
  exact ((isCompact_range_psiU hr hq θ).isClosed).preimage continuous_subtype_val

end Component

end Amalgam

/-! ## The theorem -/

local instance ucomponentMeasurableSpace (Z : Type*) (R : RangeSet) :
    MeasurableSpace (UCPM Z R) := borel (UCPM Z R)

local instance ucomponentBorelSpace (Z : Type*) (R : RangeSet) :
    BorelSpace (UCPM Z R) := ⟨rfl⟩

/-- **Theorem 3.13** (audit §2.14).  For every discrete `Z` with `|Z| = ℵ₁`,
every characteristic range set `R`, and every compatible `R`-valued ultrametric
`d` on `Z`, the `R`-component of `d` is not Borel in `UCPM(Z;R)`.

The witness is the amalgam family of the audit: the Lemma 3.10 coding
transported into an uncountable closed ball around a base point and glued to
`d` at its centre.  Its parameter pullback is exactly `2^ω ∖ S` for the dense
non-Borel `S` of Proposition 2.2. -/
theorem ucomponent_not_borel_of_card (hR : R.IsCharacteristic)
    (Z : Type*) (hZ : #Z = aleph 1) (d : UCPM Z R) (hd : d ∈ UMet Z R) :
    ¬ MeasurableSet (UComponent d) := by
  intro hcomp
  obtain ⟨r, hr⟩ := RangeSet.exists_isScale hR
  obtain ⟨S, hSdense, hScard, hSnonmeas⟩ := exists_dense_aleph1_nonBorel_cantor
  -- `Z` is uncountable, hence in particular nonempty
  have hZcount : ¬ Countable Z := by
    intro hc
    haveI := hc
    have hle : #Z ≤ (ℵ₀ : Cardinal) := Cardinal.mk_le_aleph0
    rw [hZ] at hle
    exact absurd hle (not_le_of_gt Cardinal.aleph0_lt_aleph_one)
  obtain ⟨z⟩ : Nonempty Z := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hZcount inferInstance
  -- an uncountable closed ball of radius in `R`
  obtain ⟨q, hqR, hqunc⟩ := exists_radius_not_countable d z hZcount
  have hq : 0 ≤ q := R.nonneg hqR
  -- it has cardinality `ℵ₁`, hence carries the coded carrier
  have hballcard : #(↥(uBall d z q)) = aleph 1 := by
    refine le_antisymm ?_ ?_
    · exact (Cardinal.mk_set_le _).trans hZ.le
    · exact Cardinal.aleph_one_le_iff.mpr
        (Cardinal.aleph0_lt_mk_iff.mpr (not_countable_iff.mp hqunc))
  obtain ⟨θ⟩ : Nonempty (↥(uBall d z q) ≃ UltraIndex S) := by
    refine Cardinal.lift_mk_eq'.mp ?_
    rw [hballcard, card_ultraIndex hScard]
    simp
  -- pull the component back along the amalgam family
  have hpre : MeasurableSet (psiU hr d z q hq θ ⁻¹' UComponent d) :=
    hcomp.preimage (continuous_psiU hr hq θ).measurable
  rw [preimage_UComponent_psiU hr hq hqR hd θ] at hpre
  exact hSnonmeas (by simpa using hpre.compl)

end

end IshikiExt

namespace IshikiExt

noncomputable section

variable {Z W : Type*} {R : RangeSet}

/-! ## The arbitrary-subset one-point max-amalgam

This is the subset-indexed form of `uRetract`, `uInto`, and `uAmalgam`.
Unlike the closed-ball construction above, its definitions use only a subset
`H` and a chosen point `z ∈ H`; no numerical ball property is built in. -/

open Classical in
/-- Collapse an arbitrary subset `H` to its chosen point `z`. -/
def hRetract (H : Set Z) (z : Z) (x : Z) : Z :=
  if x ∈ H then z else x

open Classical in
/-- Map `H` identically into its subtype and collapse its complement to `z`. -/
def hInto (H : Set Z) (z : Z) (hz : z ∈ H) (x : Z) : ↥H :=
  if h : x ∈ H then ⟨x, h⟩ else ⟨z, hz⟩

theorem hRetract_of_mem {H : Set Z} {z x : Z} (hx : x ∈ H) :
    hRetract H z x = z := by
  rw [hRetract, if_pos hx]

theorem hRetract_of_notMem {H : Set Z} {z x : Z} (hx : x ∉ H) :
    hRetract H z x = x := by
  rw [hRetract, if_neg hx]

theorem hInto_of_mem {H : Set Z} {z x : Z} {hz : z ∈ H} (hx : x ∈ H) :
    hInto H z hz x = ⟨x, hx⟩ := by
  rw [hInto, dif_pos hx]

theorem hInto_of_notMem {H : Set Z} {z x : Z} {hz : z ∈ H} (hx : x ∉ H) :
    hInto H z hz x = ⟨z, hz⟩ := by
  rw [hInto, dif_neg hx]

/-- The one-point max-amalgam over an arbitrary subset `H`. -/
def hAmalgam (d : UCPM Z R) (H : Set Z) (z : Z) (hz : z ∈ H)
    (κ : ↥H → W) (e : UCPM W R) : UCPM Z R :=
  UCPM.sup (UCPM.comap (hRetract H z) d) (UCPM.comap (κ ∘ hInto H z hz) e)

section HAmalgam

variable {d : UCPM Z R} {H : Set Z} {z : Z} {hz : z ∈ H}
  {κ : ↥H → W} {e : UCPM W R}

theorem hAmalgam_val (x y : Z) :
    (hAmalgam d H z hz κ e).1 x y
      = max (d.1 (hRetract H z x) (hRetract H z y))
        (e.1 (κ (hInto H z hz x)) (κ (hInto H z hz y))) := rfl

theorem base_le_hAmalgam (x y : Z) :
    d.1 (hRetract H z x) (hRetract H z y) ≤ (hAmalgam d H z hz κ e).1 x y :=
  le_max_left _ _

theorem coding_le_hAmalgam (x y : Z) :
    e.1 (κ (hInto H z hz x)) (κ (hInto H z hz y))
      ≤ (hAmalgam d H z hz κ e).1 x y :=
  le_max_right _ _

theorem hAmalgam_in_in {x y : Z} (hx : x ∈ H) (hy : y ∈ H) :
    (hAmalgam d H z hz κ e).1 x y = e.1 (κ ⟨x, hx⟩) (κ ⟨y, hy⟩) := by
  rw [hAmalgam_val, hRetract_of_mem hx, hRetract_of_mem hy, hInto_of_mem hx,
    hInto_of_mem hy, d.2.dist_self z]
  exact max_eq_right (e.2.nonneg _ _)

theorem hAmalgam_out_out {x y : Z} (hx : x ∉ H) (hy : y ∉ H) :
    (hAmalgam d H z hz κ e).1 x y = d.1 x y := by
  rw [hAmalgam_val, hRetract_of_notMem hx, hRetract_of_notMem hy,
    hInto_of_notMem hx, hInto_of_notMem hy, e.2.dist_self _]
  exact max_eq_left (d.2.nonneg x y)

end HAmalgam

end

end IshikiExt
