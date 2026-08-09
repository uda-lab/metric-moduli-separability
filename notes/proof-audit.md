# Proof Audit

This file records:
- Open proof obligations
- Failed or abandoned proof attempts
- Independent audit findings

Do not record research history in the main report or paper.

---

## Open obligations

| ID | Claim | Status | Notes |
|----|-------|--------|-------|
| LEM-A-EXISTS | ∃ A ⊆ [0,1], \|A\| = ℵ₁, A not Fσ | ✅ 独立監査通過 / Gate B passed (Issue #10, 2026-08-09) | See report §3; CH case via irrationals + Baire category, non-CH case via the perfect-set-theorem counting argument. Lean proof complete and sorry-free (Issue #8, 2026-08-09): `lem_A_exists`, `IshikiConj51/Conj51/Cardinality.lean`, see the sorry tracker below. |
| — | Y = [0,1] \ A not Gδ → not completely metrizable | ✅ 独立監査通過 / Gate B passed (Issue #10, 2026-08-09) | See report §1 (background theorems 1–2) and §4 steps 2–3, 5. Fσ/Gδ complement duality made explicit (De Morgan); Alexandrov–Lavrentiev used only for the separable ambient [0,1]; closed-subspace inheritance for the non-separable Met(D) now uses an elementary, separability-free argument instead. |
| LEM-STAR-METRIC | Star-type family of compatible metrics on D parametrised by Y | ✅ 独立監査通過 / Gate B passed (Issue #10, 2026-08-09) | Report §3.1–§3.5: explicit construction (reference pair + ω₁ stars, s_n(α,t) = min(1, \|t−a_α\| + 1/n)) with full proofs of (C1) metric axioms, (C2) compatibility for t ∈ Y, (C3) loss of compatibility at t ∈ A. Lean formalisation complete and sorry-free (Issue #7, 2026-08-09): `IshikiConj51/Conj51/MetricConstruction.lean`, see below. |
| LEM-CLOSED-IMAGE | Bi-Lipschitz embedding with closed image | ✅ 独立監査通過 / Gate B passed (Issue #10, 2026-08-09) | Report §3.6–§3.7: (C4) \|t−s\| ≤ ρ(d_t,d_s) ≤ 2\|t−s\| and (C5) closedness of φ(Y), including the boundary case where the limit parameter lands in A and (C3) supplies the contradiction. Lean formalisation complete and sorry-free (Issue #9, 2026-08-09): `lem_closed_image`, `IshikiConj51/Conj51/ClosedEmbedding.lean`, see below. |
| THM-CONJ51 | Full assembly | ✅ 独立監査通過 / Gate B passed (Issue #10, 2026-08-09) | Report §4 steps 1–6; no mathematically unwritten step remains. Plan-Gates A–C (independent review, Lean formalisation, report/Lean statement agreement) are all now decided in the affirmative, and the **proof candidate** label was lifted by owner decision (PR #29 comment, 2026-08-09; Issue #31). Lean assembly of §4 complete (Issue #9, 2026-08-09) as `thm_conj51_of_lavrentiev`. **`thm_conj51` is now proved sorry-free**: Issue #23's Alexandrov–Lavrentiev direction (`isGδ_of_isCompletelyMetrizableSpace`, `GDeltaComplete.lean`, merged in PR #25) discharges the `lavrentiev` hypothesis at `X := ℝ`, and `#print axioms thm_conj51` gives `[propext, Classical.choice, Quot.sound]`. Gate B (Issue #10) was carried out on 2026-08-09 by an agent uninvolved in #2–#9 and found **no mathematical gap**; see the Issue #10 audit-findings entry below for the reconstruction, the failed counterexample attempts, and the reviewer's own `#print axioms` run. |

---

## Failed / abandoned attempts

### [2026-08-08] Attempt: non-CH branch of LEM-A-EXISTS via direct Fσ-structure contradiction

- Approach: the original report §3 non-CH sketch tried to argue directly
  from "the structure of an Fσ representation" that a size-ℵ₁ subset of
  [0,1] cannot be Fσ when ℵ₁ < 𝔠, by noting that a closed superset F ⊇ A
  with |F| ≥ ℵ₁ would need |F| = 𝔠 > ℵ₁, but stopped there.
- Why it failed: no actual contradiction was derived. The sketch never
  established that any single Fσ-piece F_n must itself be uncountable (or
  otherwise be forced into contradiction) — it only noted an inequality
  between cardinalities without connecting it back to a bound on |F_n| or
  on |A| = ⋃F_n. The report explicitly flagged this as "より微妙で，要検証"
  (more subtle, needs verification) rather than asserting it was complete.
- What was learned: the correct move is to bound *each* Fσ-piece
  individually (|F_n| ≤ |A| = ℵ₁ < 𝔠) and apply the perfect set theorem
  (Cantor–Bendixson corollary) piecewise, forcing every F_n countable, then
  use closure of countability under countable unions — see report §3 for
  the completed argument.

Template:
```
### [Date] Attempt: <short description>
- Approach: ...
- Why it failed: ...
- What was learned: ...
```

---

## Audit findings

### [2026-08-09] LEM-A-EXISTS — non-CH branch was incomplete, now fixed

- **Finding.** The report's previous non-CH branch sketch (§3, pre-audit) tried
  to derive a contradiction "directly from the Fσ structure" without
  specifying the mechanism, and explicitly flagged this step as "要検証"
  (needs verification). As written, no contradiction was actually
  demonstrated — it observed that a candidate closed superset could have
  cardinality up to 𝔠 without immediately explaining why that is
  impossible for a set of the required cardinality ℵ₁.
- **Fix.** Replaced with a complete counting argument: if ℵ₁ < 𝔠, then
  *any* A ⊆ [0,1] with |A| = ℵ₁ is automatically not Fσ, because every
  Fσ-piece F_n ⊆ A satisfies |F_n| ≤ ℵ₁ < 𝔠, so by the perfect set theorem
  (an uncountable closed subset of [0,1] has cardinality 𝔠, a consequence
  of the Cantor–Bendixson theorem) each F_n must be countable, making
  A = ⋃F_n countable — contradicting |A| = ℵ₁. This requires no
  case-specific set (e.g. no Bernstein-set construction), only the
  cardinality bound ℵ₁ < 𝔠 and the existence of *some* ℵ₁-sized subset of
  [0,1] (always true since ℵ₁ ≤ 𝔠 in ZFC).
- **Note on the CH branch.** The CH branch's argument (irrationals ∩ [0,1],
  not Fσ by the Baire category theorem) was already correct as stated and
  is independent of CH — CH is only used to get |irrationals ∩ [0,1]| = 𝔠
  = ℵ₁. No change was needed there beyond adding precise references.
- **Not used: uniform Bernstein-set argument.** A single construction
  working uniformly across both CH and ¬CH (e.g., enumerating all perfect
  subsets of [0,1] via transfinite recursion and diagonalizing against
  them) was considered as an alternative that avoids the case split, but
  was not pursued: it requires more machinery (transfinite recursion over
  up to 𝔠-many perfect sets) for no proof-strength gain over the
  elementary two-case argument above, which is already fully rigorous.
  Left as a remark in case a future audit prefers a case-split-free proof.

### [2026-08-09] Closed-subspace inheritance for Met(D) — non-separability misapplication, now fixed

- **Finding.** The report's §1 background theorem stated "完全距離化可能な空間
  （Polish 空間）の部分空間が完全距離化可能であることと，それが Gδ 集合である
  ことは同値である" — i.e. it parenthetically identified "完全距離化可能な空間"
  (completely metrizable space) with "Polish 空間" (Polish space). These are
  **not** the same: Polish = completely metrizable **and separable**. The
  report then derived "閉部分空間の遺伝性" (closed-subspace inheritance) as a
  corollary of this (Polish-flavoured) theorem, and applied it in the main
  proof (old step 5) to $\operatorname{Met}(D)$. But $\operatorname{Met}(D)$
  is **not separable** for $|D|=\aleph_1$ (perturbing the base metric near
  each point of $D$ independently produces an uncountable, uniformly
  separated subset of $\operatorname{Met}(D)$, which a separable metric space
  cannot contain). Citing a Polish-specific source (e.g. Kechris Thm 3.11,
  which is explicitly about Polish spaces) to justify a claim about a
  non-separable space is a citation-scope error, independent of whether the
  underlying fact happens to still be true.
- **Fix.** Split the report's single background theorem into two: background
  theorem 1 (Alexandrov–Lavrentiev $G_\delta$ characterisation) is now stated
  and used **only** for the separable ambient space $[0,1]$ (main proof step
  3); background theorem 2 (closed-subspace inheritance) is now proved
  directly and elementarily — a complete metric on $Z$ restricted to a closed
  $C \subseteq Z$ is a complete metric on $C$ — with **no separability
  hypothesis at all**, and is the only one used for $\operatorname{Met}(D)$
  (main proof step 5).
- **Note (not a further error, but worth recording).** The general (not
  necessarily separable) form of the Gδ-characterisation theorem does exist
  in the literature (Engelking, *General Topology*, Thm. 4.3.23–4.3.24;
  Willard, *General Topology*, Thm. 24.12, p. 179 — both independently
  verified), so it is not strictly true that *no* Gδ-style theorem can ever
  apply to a non-separable space. The report avoids relying on that general
  (and citation-wise less commonly pinned down) form regardless, since the
  elementary closed-subspace argument is simpler, fully self-contained, and
  sufficient for exactly what step 5 needs.
- Made the Fσ/Gδ complement duality (main proof step 2) explicit via De
  Morgan's law, and confirmed the ambient space is consistently $[0,1]$ for
  both $A$ and $Y$ (as opposed to $\mathbb{R}$), which coincide here since
  $[0,1]$ is closed in $\mathbb{R}$.
- Added a one-sentence note (report §1) on why $\operatorname{Met}(D)$'s
  sup-distance possibly being extended-valued (per the Issue #2 literature
  finding) does not affect any of the above: complete metrizability is a
  purely topological property, independent of which compatible metric
  witnesses it.
- **Follow-up flagged, not fixed here (out of scope for Issue #4):**
  `paper/main.tex` §"Background results" (lines 81–89) contains the exact
  same pre-fix bug — an "Alexandrov's theorem" stated for Polish spaces,
  with a "closed subspace inheritance" corollary drawn from it without
  qualification. `paper/main.tex` is a not-yet-audited draft (Issue #11,
  blocked on the mathematical audit passing) and wasn't in this issue's
  acceptance criteria, so it was left untouched — but whoever drafts the
  English paper (Issue #11) should mirror the report-ja.md §1 fix (split
  into a separable-only Gδ characterisation and a separability-free
  closed-subspace lemma) rather than translate the current buggy English
  text as-is.
- **Second follow-up, added 2026-08-09 (Issue #5), also not fixed here:**
  `paper/main.tex` line 101 states LEM-A-EXISTS with `A \subset [0,1]`, while
  `report/report-ja.md` uses `A \subseteq [0,1]`. The report was unified to
  `⊆` throughout under Issue #5; `paper/main.tex` was left alone for the same
  out-of-scope reason as above. Issue #11 should unify it, since the four
  stable claim IDs must read identically across report, paper, and Lean.

### [2026-08-09] LEM-STAR-METRIC / LEM-CLOSED-IMAGE — construction written out; verification notes

Recorded while writing report §3.1–§3.8 (Issue #5). No error was found in the
construction being written up, but the following points were checked
explicitly and are the places a reviewer should look first.

- **Triangle-inequality case split is exhaustive by construction.** The proof
  partitions `D = {p,q} ⊔ ⨆_α C_α` and then splits three distinct points by
  how they distribute over that partition: all in one block (only a star is
  possible, since `{p,q}` has two elements), two in one block plus one
  outside (sub-split by whether the shared block is a star or `{p,q}`), and
  all three in distinct blocks. That is the complete list of distributions,
  which is why no residual case can hide. In the last case `p` and `q` cannot
  both occur, so every pair is a cross-block pair at distance 1 — this is the
  step that would break if `d_t(p,q)` were allowed to exceed 2.
- **Where `t ≤ 1` is load-bearing.** Only in case (c): `d_t(p,q) = 1+t ≤ 2 =
  d_t(p,z) + d_t(z,q)`. A reference-pair distance `1+t` with `t > 1` would
  violate the triangle inequality through any third point. The parameter
  interval `[0,1]` therefore cannot be widened without rescaling the
  reference pair.
- **Isolation of the endpoints does not depend on `t`.** `δ(x_{α,n}) =
  s_n(α,t) ≥ 1/n > 0` holds for every `t ∈ [0,1]`, including `t ∈ A`. Only
  the *centre* `y_α` loses isolation, and only for `t = a_α`. This is why
  (C3) is a statement about one specific centre rather than about the whole
  star, and why `d_t` remains a metric there.
- **Where `|A| = ℵ₁` is used (corrected 2026-08-09 after the PR #17 codex
  review).** The first draft of report §3.8 claimed that (C1)–(C5) work for any
  non-empty `A`, with the cardinality consumed only by the count
  `|D| = 2 + ℵ₁ + ℵ₁·ℵ₀ = ℵ₁`. That was wrong: §3.2 indexes the stars by
  `α < ω₁` via an injective enumeration `A = {a_α : α < ω₁}`, and such an
  enumeration exists precisely when `|A| = ℵ₁` (a smaller `A` cannot supply it;
  a larger one would leave elements of `A` uncovered, breaking the (C3)
  boundary argument). The accurate split, now in §3.8, is: `|A| = ℵ₁` is used
  twice at construction time (existence of the `ω₁`-indexed enumeration; the
  `|D|` count), while the *verification* of (C1)–(C5) uses no cardinality — each
  proof is local (≤ 3 points, one point vs. its complement, one centre `y_β`,
  or a per-pair estimate). Weakening the cardinality would require reindexing
  the stars by `A` itself plus filler points to keep `|D| = ℵ₁`; not done here.
  Non-Fσ-ness remains consumed only by main proof steps 2–3. The split is
  recorded so a later change to LEM-A-EXISTS traces to exactly the affected
  steps.
- **Finiteness of ρ on the image.** `notes/literature.md` (Issue #2) records
  that the sup-distance on `Met(Z)` is genuinely extended-valued in general.
  Every `d_t` here has range in `[0,2]`, so `ρ(d_t, d_s) ≤ 2 < ∞` and the
  whole image lies in a single finite-distance (clopen) component of
  `Met(D)`. The (C4)/(C5) arguments therefore never manipulate `∞`.
- **Not used: a uniformly discrete construction.** Making the satellite
  distances bounded below by a single constant would simplify (C2) but would
  narrow the family to uniformly discrete metrics, which per
  `notes/literature.md` is strictly stronger than the source's compatibility
  condition. The construction deliberately lets `inf_n s_n(α,t) → 0` as
  `t → a_α`, since that degeneration is exactly what makes the image closed
  rather than merely embedded.

### [2026-08-09] Issue #10 — independent end-to-end mathematical review (Gate A / Gate B)

**Reviewer and independence.** Carried out by an agent that took no part in
Issues #2–#9 / PRs #14–#25 (neither writing the report nor the Lean sources).
The argument was reconstructed from primary material only — the arXiv:2407.03030
v4 PDF, `report/report-ja.md`, `notes/literature.md`, and the Lean sources at
`4009275` — without asking the other agents any mathematical question and
without reading their working notes. Where this review reaches the same
conclusion as an earlier entry above, it did so independently; those
coincidences are noted, not inherited.

**Verdicts.**

| Gate | Question | Verdict |
|------|----------|---------|
| **Gate A** | Is `report/report-ja.md` a self-contained natural-language proof — every step written out, no appeal to an unwritten lemma? | **PASS.** §3 gives the explicit construction with complete proofs of (C1)–(C5), and §4's six steps each name the result they invoke, every one of which is proved earlier in the same document — with exactly one external input, background theorem 1 (Alexandrov–Lavrentiev), which §1 states precisely and cites to Engelking 4.3.23–4.3.24 / Willard 24.12 / Kechris 3.11 rather than proving. That is the appropriate treatment for a classical textbook theorem, and it is the *only* uncited-by-proof step: background theorem 2 (closed-subspace inheritance), which is the one applied to the non-separable `Met(D)`, **is** proved in full in §1. No step is left to the reader and no "it is easy to see" carries weight. |
| **Gate B** | Independent mathematical review: does the argument prove Conjecture 5.1 for \|D\| = ℵ₁? | **PASS — no mathematical gap found.** Every implication of LEM-A-EXISTS, LEM-STAR-METRIC, LEM-CLOSED-IMAGE and the §4 assembly was re-derived from scratch and holds. The counterexample searches in §3 below all failed to produce one. Findings F1–F3 are documentation defects outside the four claim IDs and do not affect the mathematics. |

*Gate naming.* This entry uses the naming in the Issue #10 brief: **Gate A** =
"is the report a self-contained natural-language proof", **Gate B** =
"independent end-to-end mathematical review". `report/report-ja.md` §4 uses the
project-plan naming, where Gate A is the independent review, Gate B the Lean
formalisation and Gate C the report ↔ Lean statement agreement. In plan terms
this entry decides plan-Gate A and, via §5 below, plan-Gate C; plan-Gate B was
completed by Issues #6–#9/#23.

Consequently the four claim IDs are marked **独立監査通過 (Gate B passed)** in
the obligations table. Whether the report and `STATUS.md` may now drop the
**証明候補 / proof candidate** label is a project decision for the owner, not
the reviewer's to make; this review deliberately leaves that label in place and
records only that no mathematical gap was found.

#### 1. Source statement re-verified against the v4 PDF (acceptance criterion 3)

Text extracted locally with `pdftotext -layout` from the v4 PDF, not from any
secondary summary.

> **Conjecture 5.1.** Recall that ℵ1 stands for the first uncountable
> cardinality, and let Dℵ1 denote the the discrete space of cardinality of ℵ1.
> Under this notations, the space Met(Dℵ1) is not completely metrizable.

and, from §1.1,

> the set of all metrics on Z that generate the same topology of Z … D_Z(d,e) =
> sup_{x,y∈Z} |d(x,y) − e(x,y)|

with `BMet(Z)` introduced *separately* as the bounded subset, and §2.2 treating
`D_Z` as genuinely extended-valued (finite-distance classes form clopen
components). Three consequences, all confirmed:

* `Met(D)` is *all* compatible metrics — no boundedness restriction. The Lean
  `MetD D` carries no bound, and its `edist` is `ℝ≥0∞`-valued (`MetD.lean`), so
  the extended-valued sup is modelled rather than truncated.
* "compatible with the discrete topology" is `IsMetricOn.topology = ⊥`, which
  `IsMetricOn.topology_eq_bot_iff` unfolds to `∀ u, ∃ ε > 0, ∀ v, d v u < ε →
  v = u` — i.e. every point is isolated, **not** uniform discreteness (`∃ ε`
  before `∀ u`). The quantifier order was checked explicitly because swapping
  it is the single most tempting way to make (C2) easier, and it would
  falsify the theorem's scope.
* The cardinality hypothesis is `#D = ℵ₁` exactly, matching `thm_conj51`.

No proxy weakening was found anywhere in the chain.

#### 2. Independent reconstruction (acceptance criterion 1)

Each step below was re-derived without consulting the report's proof text
first, then compared against it.

* **LEM-A-EXISTS, CH branch.** `A = [0,1] \ ℚ`. If `A = ⋃ₙ Fₙ` with `Fₙ` closed
  in `[0,1]`, each `Fₙ ⊆ A` has empty interior (every interval meets ℚ), hence
  is nowhere dense, so `[0,1] = ⋃ₙ Fₙ ∪ ⋃_{q∈ℚ∩[0,1]} {q}` is meagre in
  itself — contradicting Baire. Under CH `|A| = 𝔠 = ℵ₁`. ✔
* **LEM-A-EXISTS, non-CH branch.** With `ℵ₁ < 𝔠`, take *any* `A ⊆ [0,1]` with
  `|A| = ℵ₁` (possible since `ℵ₁ ≤ 𝔠`). If `A = ⋃ₙ Fₙ` were Fσ, some `Fₙ` is
  uncountable; an uncountable closed subset of ℝ has size 𝔠 (perfect set
  theorem), so `|A| ≥ 𝔠 > ℵ₁`. ✔ Note the two branches are genuinely
  different: in the CH branch a specific `A` is needed, in the non-CH branch
  *every* size-ℵ₁ set works. The case split is on `ℵ₁ = 𝔠` vs `ℵ₁ < 𝔠`, which
  is exhaustive in ZFC given `ℵ₁ ≤ 𝔠`; no extra axiom is used. ✔
* **(C1).** The case analysis was redone from the distance table alone. It is
  exhaustive, and the two inequalities that are actually tight are
  `1 + t ≤ 2` (reference pair versus a detour through any third point, needing
  `t ≤ 1`) and `s_n + s_m ≤ 2` (within-star pair versus a detour outside the
  star, needing `s ≤ 1`, which `min(1, ·)` supplies unconditionally). Both hold.
  This independently reproduces the "where `t ≤ 1` is load-bearing" note above.
  ✔
* **(C2).** Compatibility ⟺ `δ(u) := inf_{v≠u} d(u,v) > 0` for all `u`. The
  computation `δ(p) = δ(q) = 1`, `δ(x_{α,n}) = s_n(α,t)`, `δ(y_α) = min(1,
  |t−a_α|)` is correct, the last one being an infimum that is **not attained**
  (`inf_n min(1, |t−a_α| + 1/n)`). The proof does not need attainment — only
  positivity — and the report does not claim it. ✔
* **(C3).** At `t = a_β`, `δ(y_β) = 0` while `d_{a_β}` is still a metric
  (`s_n(β,a_β) = 1/n > 0`, so positivity survives). So exactly compatibility
  fails, which is what 手順3 needs. ✔
* **(C4).** Lower bound from the reference pair alone; upper bound from
  1-Lipschitzness of `r ↦ min(1, |r − a| + 1/n)` applied at most twice per
  table entry. Both re-derived. ✔
* **(C5).** The three steps are valid: `Met(D)` is metrizable (by `min(ρ,1)`),
  so closure = sequential closure and the sequential argument is legitimate;
  the parameter is recovered continuously from the reference pair; the limit is
  identified by a 3ε argument; and `t ∉ A` is *derived* from `e ∈ Met(D)` via
  (C3) rather than assumed. The last point is the crux — the image is closed
  precisely because the "missing" limits fail to be compatible metrics at all,
  so they are not points of `Met(D)` to begin with. ✔
* **§4 assembly.** Steps 1–6 chain correctly; step 3 applies the Gδ
  characterisation only to `Y ⊆ [0,1]` (separable), step 5 uses only the
  separability-free closed-subspace inheritance. The two are kept apart, which
  is the correct treatment given that `Met(D)` is not separable (§3 below). ✔

#### 3. Adversarial checks — attempted counterexamples and hidden assumptions (acceptance criterion 2)

Each item is an attempt to break the argument. All failed; the resolution is
recorded so the attempt need not be repeated.

| # | Attack | Outcome |
|---|--------|---------|
| A1 | **Ambient ambiguity**: report §3/§4 work inside `[0,1]`, the Lean `IsFSigma`/`IsGδ` are relative to `ℝ`. Does "A is not Fσ" mean the same thing in both? | **No gap.** `[0,1]` is closed in `ℝ`, so a subset of `[0,1]` closed in `[0,1]` is closed in `ℝ` and conversely; hence Fσ-in-`[0,1]` ⟺ Fσ-in-`ℝ` for `A ⊆ [0,1]`. Report §4 step 2 states this explicitly; the Lean side does the same job constructively in `isFSigma_of_isGdelta_sdiff`, which intersects each `Uₙᶜ` with `Icc 0 1` — I re-verified that `A = ⋃ₙ (Icc 0 1 ∩ Uₙᶜ)` for `A ⊆ Icc 0 1` and `Icc 0 1 \ A = ⋂ₙ Uₙ`. The Gδ side is equally ambient-independent, for a slightly different reason: `Y ⊆ [0,1]` Gδ in `[0,1]` means `Y = [0,1] ∩ ⋂ₙ Uₙ`, and `[0,1]` is itself Gδ in `ℝ` (closed sets in a metric space are Gδ), so `Y` is Gδ in `ℝ` too. Both relative notions therefore agree with the absolute ones here, and the Lean statement's use of `IsGδ`/`IsFSigma` relative to `ℝ` is the same claim as the report's relative to `[0,1]`. |
| A2 | **Separability smuggled in**: does any step apply a Polish-space theorem to `Met(D)`? | **No.** `Met(D)` is genuinely non-separable: fix pairwise-disjoint pairs `{u_α, v_α}`, `α < ω₁`, and for `T ⊆ ω₁` let `d_T ≡ 1` off the diagonal except `d_T(u_α,v_α) = ½` for `α ∈ T`. Each `d_T` is compatible (all `δ ≥ ½`) and `ρ(d_T, d_{T'}) = ½` for `T ≠ T'`, giving `2^{ℵ₁}` points pairwise ½-apart. So the Alexandrov/Lavrentiev *characterisation* must not be applied to `Met(D)` — and the report applies it only to `Y ⊆ [0,1]`, using the elementary separability-free closed-subspace inheritance for `Met(D)`. Lean matches: `Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace` (Mathlib) has no separability hypothesis, and `isGδ_of_isCompletelyMetrizableSpace` is applied at `X := ℝ`. |
| A3 | **Extended-valued sup**: does `ρ = ∞` break (C4)/(C5) or the metrizability claim? | **No.** All `d_t` take values in `[0,2]`, so the whole image sits in one finite-distance component; and an extended metric still metrizes via `min(ρ,1)`, so the closure-equals-sequential-closure step in (C5) is valid. The Lean side keeps `ℝ≥0∞` throughout and never needs finiteness. |
| A4 | **Uniform discreteness**: is the family secretly confined to uniformly discrete metrics (which would make the result weaker than the source's)? | **No.** `inf_u δ(u) = min(1, dist(t, A))`, so `d_t` is uniformly discrete exactly when `t ∉ Ā`. In the CH branch `A` is the irrationals, hence dense, so `dist(t,A) = 0` and **every** `d_t` in the family is compatible but *not* uniformly discrete. The family therefore genuinely inhabits `Met(D)` and not a uniformly-discrete subfamily. (In the non-CH branch some individual `d_t` may happen to be uniformly discrete; that is harmless, since nothing in (C1)–(C5) refers to the notion.) The decisive point is the one behind (C5): the degeneration `δ(y_β) → 0` as `t → a_β` is what makes the image closed, so a construction engineered to be uniformly discrete could not work. |
| A5 | **Boundary case not excluded**: could some `e ∈ Met(D)` be a limit of `d_{t_k}` with `t_k → t ∈ A`? | **No.** Then `e = d_t` by (C4)+3ε, and `d_t ∉ Met(D)` by (C3) — contradiction with `e ∈ Met(D)`. Checked that (C3) really applies to the *limit* parameter, not merely to the `t_k`: `t = e(p,q) − 1 ∈ [0,1]` because `[0,1]` is closed, so `d_t` is defined and (C3) is available. |
| A6 | **Cardinal arithmetic**: is `\|D\| = 2 + ℵ₁ + ℵ₁·ℵ₀ = ℵ₁` right, and does anything depend on CH? | **Yes / no.** `ℵ₁·ℵ₀ = ℵ₁` and finite + ℵ₁ = ℵ₁ in ZFC. CH is used only to *choose* `A`, and both branches of the choice are available in ZFC, so the theorem is a ZFC theorem, not a CH theorem. Cross-checked in Lean: `card_starIndex` derives `#(StarIndex A) = ℵ₁` from `#A = ℵ₁` alone, and `lem_A_exists` case-splits on `aleph_one_le_continuum.lt_or_eq` with no extra hypothesis. |
| A7 | **Does the argument prove too much?** If it worked for countable `D` it would contradict Koshino's theorem (for separable `X`, `Met(X)` completely metrizable ⟺ `X` σ-compact; a countable discrete space *is* σ-compact, so `Met(D)` *is* completely metrizable there). | **It does not.** The construction needs `A` non-Fσ, and every countable `A` is Fσ; so no countable `D` can be produced this way. The argument therefore stops exactly at the boundary the known theorem predicts, which is a non-trivial consistency check rather than a coincidence. |
| A8 | **Is the closed-set description in Lean weaker than the report's sequential argument?** `StarRange` imposes only `anchorParam e ∈ [0,1]` and `e = d_{anchorParam e}`. | **Equivalent, and exactness is proved** (`range_starParam`). The `t ∉ A` clause is deliberately *not* imposed; it is recovered from `e : MetD _` through `dStar_mem_MetD_iff`, i.e. through (C3). This is the same mathematical content as 手順3, packaged as a range computation instead of a limit argument. I checked the two closedness ingredients — `e ↦ e.1 u v` is 1-Lipschitz because it is a single term of the defining supremum, and `t ↦ dStar A t u v` is 2-Lipschitz by (C4)'s per-entry estimate — and both are genuinely available at that point in the file. |
| A9 | **Anchor readout**: `anchorParam e := e p q − 1` presumes the reference-pair value determines the parameter. Could two parameters share it? | **No** — `1 + t` is injective in `t`, which is also what gives (C4)'s lower bound. This is the only place the reference pair is used, and removing it would cost injectivity, not just the constant. |

#### 4. Numerical falsification attempt

`notes/scripts/star-metric-spotcheck.py` (added by this issue) evaluates a
finite model of the construction — 4 anchors, spokes `n = 1..6` — and checks
(C1) over all ordered triples on a 201-point grid of `t`, (C2)/(C3) using the
*exact* infimum `min(1,|t−a|)` rather than the truncated one, and (C4) on 4000
random parameter pairs. Report §3.8's observation that every (C1)–(C5)
verification is local (≤ 3 points, or one point against its complement) is what
makes a finite model exercise the same inequalities. Output:

```
(C1) triangle violations: 0, positivity violations: 0
(C2) t=0.5   not in A: min_u delta(u) = 0.120000 > 0 -> discrete
(C3) t=0.1   in A:     delta(y_a) = 0.000000, min_u delta(u) = 0.000000
(C4) rho(d_t,d_s)/|t-s| over 4000 random pairs: [1.453372, 2.000000]
all spot-checks passed
```

The observed ratio range sits inside the claimed `[1,2]` and attains the upper
bound, so the constant 2 in (C4) is sharp for this family (the lower constant 1
is attained only in the limit of the finite model, where the reference pair
dominates). This is evidence, not proof; it failed to falsify.

#### 5. Report ↔ Lean statement cross-check (acceptance criterion 3)

Checked at `4009275`. "Faithful" below means: the Lean statement is not weaker
than the report's, introduces no extra hypothesis, and substitutes no proxy.

| Claim ID | Report | Lean declaration | Verdict |
|----------|--------|------------------|---------|
| LEM-A-EXISTS | §3 | `lem_A_exists : ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧ #A = Cardinal.aleph 1 ∧ ¬ IsFSigma A` | Faithful. `IsFSigma` is the local definition (`∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n`) — the correct notion, not `IsSigmaCompact`. |
| LEM-STAR-METRIC | §3.2–§3.5 | `lem_star_metric` in `MetricConstruction.lean`, with `dStar_isMetricOn` (C1), `dStar_topology_eq_bot` (C2), `dStar_topology_ne_bot` (C3) | Faithful. `starSpoke n a t = min 1 (|t−a| + 1/(n+1))` is the report's `s_n` with `n` reindexed from 0; the distance table matches row by row. |
| LEM-CLOSED-IMAGE | §3.6–§3.7 | `lem_closed_image`, `isClosedEmbedding_starParam` | Faithful; presentation differs (closed-set description vs. sequences), content identical — see A8. |
| THM-CONJ51 | §2, §4 | `thm_conj51 (D : Type*) (hD : #D = Cardinal.aleph 1) : ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)` | Faithful to the source's Conjecture 5.1 as quoted in §1 above. |

Two further points checked because they are the places a formalisation can
silently drift:

* **`Cardinal.aleph 1` really is ℵ₁, in the right universe.** `D : Type u`
  makes `#D : Cardinal.{u}`, and `Cardinal.aleph 1` elaborates in the same
  universe; `MainTheorem.lean` reconciles `StarIndex A : Type 0` with
  `D : Type u` through `Cardinal.lift_mk_eq'` and lift-invariance of `ℵ₁`.
  So the hypothesis is "`D` has cardinality ℵ₁", not "`D` has cardinality
  `lift ℵ₁` for some unintended index".
* **The `lavrentiev` hypothesis of `thm_conj51_of_lavrentiev` does not smuggle
  in the conclusion.** It quantifies over arbitrary `Y : Set ℝ`, mentions
  neither `Met(D)` nor `A` nor any cardinal, and is discharged in `thm_conj51`
  by `isGδ_of_isCompletelyMetrizableSpace` — a standalone general theorem
  (`{Y : Set X}`, `[MetricSpace X]`, no separability) proved in
  `GDeltaComplete.lean` under Issue #23. I read that statement directly rather
  than trusting the docstring.

#### 6. `#print axioms` re-run by the reviewer

Re-run independently on `main` at `4009275` after a from-scratch rebuild of all
`IshikiConj51` modules (the checked-out `.lake/build` artefacts were stale
hard-links copied from a since-deleted worktree, and `lake` reported them
up-to-date; they were deleted and rebuilt module by module before the check).

The script also `#check`s each statement, so the axiom lines below are anchored
to the statements they were read off, and type-checks two `example`s pinning
`Cardinal.aleph 1` to "the successor of ℵ₀" and to `≤ 𝔠` (both elaborate with
no error, which is why they produce no output).

```
$ cd lean && LEAN_NUM_THREADS=1 flock /tmp/lean-build.lock lake env lean /tmp/audit-axioms.lean
thm_conj51 : ∀ (D : Type u_1), #D = ℵ_ 1 → ¬TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)
thm_conj51_of_lavrentiev : (∀ (Y : Set ℝ), TopologicalSpace.IsCompletelyMetrizableSpace ↑Y → IsGδ Y) →
  ∀ (D : Type u_1), #D = ℵ_ 1 → ¬TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)
lem_A_exists : ∃ A ⊆ Set.Icc 0 1, #↑A = ℵ_ 1 ∧ ¬IsFSigma A
@lem_star_metric : ∀ {A : Set ℝ},
  #↑A = ℵ_ 1 →
    #(StarIndex A) = ℵ_ 1 ∧
      (∀ t ∈ Set.Icc 0 1, IsMetricOn (dStar A t)) ∧
        (∀ t ∈ Set.Icc 0 1, (∃ (h : IsMetricOn (dStar A t)), h.topology = ⊥) ↔ t ∉ A) ∧
          ∃ φ, ∀ (t : ↑(Set.Icc 0 1 \ A)), ↑(φ t) = dStar A ↑t
lem_closed_image : ∀ (A : Set ℝ),
  (∀ (t s : StarParamSpace A),
      edist t s ≤ edist (starParam A t) (starParam A s) ∧ edist (starParam A t) (starParam A s) ≤ 2 * edist t s) ∧
    Topology.IsClosedEmbedding (starParam A)
@isGδ_of_isCompletelyMetrizableSpace : ∀ {X : Type u_1} [inst : MetricSpace X] {Y : Set X},
  TopologicalSpace.IsCompletelyMetrizableSpace ↑Y → IsGδ Y
IsFSigma : Set ℝ → Prop
'thm_conj51' depends on axioms: [propext, Classical.choice, Quot.sound]
'thm_conj51_of_lavrentiev' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_A_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_star_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
'lem_closed_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'isGδ_of_isCompletelyMetrizableSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'isFSigma_of_isGdelta_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'isClosedEmbedding_starParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'range_starParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'dStar_isMetricOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'dStar_topology_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'dStar_topology_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Result: the three standard Lean axioms only — `propext`, `Classical.choice`,
`Quot.sound` — for every declaration checked. No `sorryAx`, and no custom
axiom. `Classical.choice` is expected and legitimate: the argument is a ZFC
argument that uses AC (well-ordering / choice of the ℵ₁-many anchors, and the
perfect-set branch of LEM-A-EXISTS).**

The script used is reproduced here so the check can be repeated verbatim:

```lean
import IshikiConj51
open Cardinal
#check @thm_conj51
#check @thm_conj51_of_lavrentiev
#check @lem_A_exists
#check @lem_star_metric
#check @lem_closed_image
#check @isGδ_of_isCompletelyMetrizableSpace
#check @IsFSigma
example : Order.succ Cardinal.aleph0 = Cardinal.aleph 1 := Cardinal.succ_aleph0
example : Cardinal.aleph 1 ≤ Cardinal.continuum := Cardinal.aleph_one_le_continuum
#print axioms thm_conj51
#print axioms thm_conj51_of_lavrentiev
#print axioms lem_A_exists
#print axioms lem_star_metric
#print axioms lem_closed_image
#print axioms isGδ_of_isCompletelyMetrizableSpace
#print axioms isFSigma_of_isGdelta_sdiff
#print axioms isClosedEmbedding_starParam
#print axioms range_starParam
#print axioms dStar_isMetricOn
#print axioms dStar_topology_eq_bot
#print axioms dStar_topology_ne_bot
```

#### 7. Findings (all non-blocking; none touches the four claim IDs)

* **F1 — `paper/main.tex` is inconsistent with the report, including one
  mathematical error.** Three distinct problems, all in scope for Issue #11:
  1. §2.2 states Alexandrov's theorem for *Polish* spaces and then derives
     "a closed subspace of a completely metrizable space is completely
     metrizable" from it with the parenthetical "(Closed sets are Gδ.)"
     (`paper/main.tex:81–89`). That derivation is invalid outside the
     separable setting, and `Met(D)` is not separable (A2 above) — it is
     exactly the misapplication the report already corrected. The paper must
     adopt the report §1 split: separable-only Gδ characterisation, plus a
     separability-free elementary proof of closed-subspace inheritance.
  2. `LEM-STAR-METRIC` is stated in the paper as "a family … with suitable
     bi-Lipschitz properties" (`paper/main.tex:114–119`), which is not the
     report's claim. Per `CLAUDE.md`, a stable claim ID must denote the same
     statement in report, Lean and paper; this one currently does not.
  3. `A \subset [0,1]` (`paper/main.tex:101`) should be `\subseteq`; and the
     appendix's "all theorems are stubs (`sorry`)" (`paper/main.tex:162–164`)
     plus the abstract's "has not yet passed independent mathematical audit"
     are both false as of #24 and this issue.
* **F2 — Kechris theorem/page numbers remain unverified.** `notes/literature.md`
  already flags this; this review could not close it (web search is unavailable
  in this environment). Non-blocking because everything load-bearing is cited
  to Engelking 4.3.23–4.3.24 / Willard 24.12, which *are* verified, and because
  the perfect-set and Baire steps were re-proved from scratch in §2 above rather
  than taken on citation.
* **F3 — `report/report-ja.md` §5 is stale.** It lists Issues #6–#9 as
  outstanding Lean work and this review (Issue #10) as pending; #6–#9 landed in
  #18/#21/#22/#24 and Gate B is now decided. Fixed by this PR.

#### 8. What this audit does *not* certify

* **Novelty/priority.** Whether this argument (or the closed copy of ℚ it
  produces under CH) already appears in the literature was not investigated;
  this is a correctness review only.
* **The other Ishiki conjectures.** Only Conjecture 5.1 for `|D| = ℵ₁` was
  reviewed.
* **Kechris citation numbering** — see F2.

#### 9. Two remarks that may be worth keeping

* **Under CH the construction has a very concrete shape:** `A` is the set of
  irrationals in `[0,1]`, so `Y = ℚ ∩ [0,1]` and the theorem says `Met(D_{ℵ₁})`
  contains a closed copy of `ℚ`. That is a sharper statement than "not
  completely metrizable" and is immediately checkable against intuition.
* **The method is not confined to ℵ₁.** Nothing in (C1)–(C5) uses `|A| = ℵ₁`
  beyond the indexing (report §3.8), so the same construction gives "`Met(D_κ)`
  is not completely metrizable" for every `κ` with `ℵ₁ ≤ κ ≤ 𝔠`, by taking
  `|A| = κ` non-Fσ (any uncountable `A` of size `< 𝔠` is non-Fσ; for `κ = 𝔠`
  take the irrationals). Not claimed in the report, and not formalised — noted
  only because it costs nothing and would be the obvious next question.

---

### [2026-08-09] Issue #26 — E9 cross-artifact claim consistency check (paper ↔ report ↔ Lean)

Performed by an agent uninvolved in the paper (#11), report (#5), or Lean
(#6–#9, #23) work. Scope: the four stable claim IDs across `paper/main.tex`
(post-PR #29 full rewrite), `report/report-ja.md`, and
`lean/IshikiConj51/Conj51/*.lean`; plus terminology per `notes/terminology.md`.
This complements the Issue #10 review §5 (report ↔ Lean, checked at `4009275`)
by adding the third leg: the paper's final wording, which did not exist in its
present form at the time of #10.

"一致" below means: hypotheses and conclusion agree across all three artifacts —
no silent weakening, no silent strengthening, no proxy formalisation. Line
numbers refer to the files as of this entry's commit.

#### Cross-check matrix (claim ID × 3 artifacts)

| Claim ID | paper/main.tex | report/report-ja.md | Lean | Verdict |
|----------|----------------|---------------------|------|---------|
| LEM-A-EXISTS | Lemma 3.1, lines 209–213: "In ZFC, there exists A ⊆ [0,1] with \|A\| = ℵ₁ such that A is not an Fσ set." Proof: CH case split, lines 215–272. | §3 lines 46–49: 同一主張（ZFC，A ⊆ [0,1]，\|A\| = ℵ₁，A は Fσ でない）; CH 場合分け lines 53–76; Bernstein 別証 line 79 = paper Remark 3.2 (lines 274–283). | `lem_A_exists` (`Cardinality.lean:136–143`): `∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧ #A = aleph 1 ∧ ¬ IsFSigma A`; `IsFSigma` local (lines 30–31), not `IsSigmaCompact`. | **一致.** Lean's `IsFSigma` uses ℝ-closed sets; for A ⊆ [0,1] this is equivalent to Fσ-in-[0,1] (any closed F ⊆ A lies in [0,1], and [0,1] is closed in ℝ) — re-derived for this check, consistent with report §4 step 2's remark (line 276). |
| LEM-STAR-METRIC | Lemma 3.3, lines 293–299: ∃ discrete D, \|D\| = ℵ₁, family (d_t)_{t∈[0,1]} of metrics with d_t ∈ Met(D) ⟺ t ∈ Y. Construction lines 308–350; (C1)–(C3) lines 352–422. | 主張 lines 87–88 states the constructive direction (family (d_t)_{t∈Y} ⊆ Met(D)); the same section proves (C1) for all t ∈ [0,1] (§3.3), (C2) (§3.4), (C3) (§3.5), and the 系 "d_t ∈ Met(D) ⟺ t ∈ Y" (line 194). | `lem_star_metric` (`MetricConstruction.lean:397–407`): conjunction of `#(StarIndex A) = ℵ₁`, (C1) for all t ∈ [0,1], the iff, and existence of φ : ↥([0,1] \ A) → MetD. | **一致.** Paper and Lean state the aggregate (family + iff); the report's headline 主張 is the Y-direction only, but the iff is proved and displayed as the 系 of the same claim-ID section (line 194), so no artifact asserts anything the others lack. Lean hypothesis is `#A = ℵ₁` for arbitrary `A : Set ℝ` (non-Fσ not assumed) — strictly more general, matching report §3.8: the Fσ condition enters only in THM-CONJ51. Spoke reindexing n ↦ n+1 (ℕ≥1 → ℕ) is bijective (file header lines 14–22), not a weakening. |
| LEM-CLOSED-IMAGE | Lemma 4.1, lines 431–436: φ : Y → Met(D), t ↦ d_t is a bi-Lipschitz embedding with closed image. (C4) two-sided estimate \|t−s\| ≤ ρ ≤ 2\|t−s\| lines 438–457; (C5) lines 464–495. | 主張 lines 204–205: 同一主張（双リプシッツ埋め込み，像は閉）; (C4) §3.6 lines 211–212; (C5) §3.7 lines 234–250. | `lem_closed_image` (`ClosedEmbedding.lean:211–217`): `(∀ t s, edist t s ≤ edist (φ t) (φ s) ∧ edist (φ t) (φ s) ≤ 2 * edist t s) ∧ IsClosedEmbedding (starParam A)`. | **一致.** `IsClosedEmbedding` is definitionally "homeomorphism onto image + image closed"; the (C4) constants 1 and 2 are kept explicitly, so "bi-Lipschitz" is not degraded to a mere topological embedding. Lean replaces the report/paper sequential (C5) argument with the closed-set description `range φ = StarRange A` — presentation difference only, audited in the Issue #9/#10 entries above; re-verified here: 手順3 (t ∉ A) is derived from e ∈ Met(D) via (C3) in `range_starParam` (lines 145–155), exactly the report's line 248 step. |
| THM-CONJ51 | Theorem 4.2, lines 497–501: "If \|D\| = ℵ₁, then Met(D), with the supremum-metric topology, is not completely metrizable." Labelled candidate. Proof lines 503–530 = report §4 steps 1–6. | §2 lines 37–38: 同一主張（\|D\| = ℵ₁ のとき Met(D) は上限距離位相に関して完全距離化可能でない）; 証明候補 line 40; proof §4 lines 273–280. | `thm_conj51` (`MainTheorem.lean:142–144`): `(D : Type*) (hD : #D = aleph 1) : ¬ IsCompletelyMetrizableSpace (MetD D)`. | **一致.** `MetD D` (`MetD.lean:102–103`) is the unweakened Met(D): finite-valued metric, induced topology = ⊥ (discrete), no boundedness/uniform-discreteness proxy; the topology on `MetD D` comes from the `EMetricSpace` instance whose `edist` is the sup distance (`MetD.lean:113–114`) = sup-metric topology. Discreteness of D is carried by the `⊥` comparison inside `MetD`, equivalent to "D discrete" since Met(D) depends only on the underlying set. Universe/lift handling audited in Issue #10 §5. |

#### Ambient design decision (Gδ in [0,1] vs. IsGδ in ℝ) — equivalence re-checked

Report §4 steps 2–3 (and paper Theorem 4.2 steps 2–3) work with Gδ/Fσ **in
[0,1]**; Lean works with `IsGδ`/`IsFSigma` **in ℝ** throughout, and
`isFSigma_of_isGdelta_sdiff` (`MainTheorem.lean:65–82`) converts
`IsGδ ([0,1] \ A)` (ℝ-ambient) to `IsFSigma A` (ℝ-ambient) by intersecting
with the closed set [0,1]. The two forms differ but are equivalent —
re-derived independently for this check rather than taken from the earlier
audits:

* For S ⊆ [0,1]: S Fσ-in-[0,1] ⟺ S Fσ-in-ℝ, because a set closed in [0,1] is
  closed in ℝ ([0,1] being closed in ℝ), and conversely any closed-in-ℝ F ⊆ S
  is contained in [0,1], hence closed in [0,1].
* For Y = [0,1] \ A: Y Gδ-in-[0,1] ⟺ Y Gδ-in-ℝ, because [0,1] is closed in a
  metric space, hence itself Gδ in ℝ, so Y = [0,1] ∩ G (G Gδ-in-ℝ) is Gδ-in-ℝ;
  the converse is intersection with [0,1].
* The set identity inside `isFSigma_of_isGdelta_sdiff` — from
  [0,1] \ A = ⋂ₙ Uₙ (Uₙ open in ℝ) and A ⊆ [0,1], conclude
  A = ⋃ₙ ([0,1] ∩ Uₙᶜ) with each term closed in ℝ — checked by hand in both
  directions.

Verdict: **形式が異なるが等価、監査済み** (consistent with the Issue #9/#23
entries above); the paper's appendix (lines 596–602) states this design
decision explicitly and accurately.

#### Terminology check (notes/terminology.md, JA/EN)

* **Met(D) meaning preserved verbatim in all three.** terminology.md line 8
  ("metrics compatible with the discrete topology … supremum-metric topology")
  = report lines 12–13 (「離散位相に**適合する**距離の全体，上限距離位相を装備」
  plus the 注意 that this is *not* all metrics on the set) = paper lines 58–67
  (compatible with the discrete topology, "a genuine restriction", sup-distance
  topology) = Lean `MetD` docstring and definition (`MetD.lean:97–103`).
* **Extended-valued ρ** acknowledged in all three: report §1 注意 (line 31),
  paper Remark 2.3 (lines 167–177), Lean `MetD.edist : ℝ≥0∞`
  (`MetD.lean:109–114`) — with the same resolution (min(ρ,1) / topology-only
  dependence) in report and paper.
* **完全距離化可能 = completely metrizable** used consistently; both report
  (line 20–29) and paper (§2.1 lines 115–120, §2.2) keep the
  Polish-vs-completely-metrizable distinction and the separable/non-separable
  split of the two background theorems, per terminology.md lines 25–27.
* Minor, non-blocking: Lean source uses "anchor (pair/Param)" for what the
  report calls 基準対 and the paper "reference pair". Identifier naming only;
  terminology.md's Lean-naming table does not bind it and no statement depends
  on the name.

#### Findings

* **E9-F1 (staleness, non-mathematical): report §5 third bullet (line 292) is
  outdated.** It still asserts that `paper/main.tex` retains the invalid
  Polish-based derivation of closed-subspace inheritance and a mismatched
  LEM-STAR-METRIC statement (the Issue #10 F1 items). PR #29 (merged
  2026-08-09) rewrote the paper and fixed all F1 items — verified directly in
  this check (paper §2.2 lines 122–165 has the corrected split; Lemma 3.3 is
  the family+iff statement; appendix reports sorry-free with the three standard
  axioms). Per the cross-artifact discipline, this entry does **not** edit the
  report; proposal recorded on the Issue #26 PR: reopen Issue #5 (owner of the
  report) — or fold into E10 (#27) — to refresh report §5's Issue #11 bullet.
* No mathematical mismatch found in any of the four claim IDs. The
  "proof candidate" framing (paper abstract line 45, Theorem 4.2 label; report
  lines 4, 40, 282) is intentionally preserved pending owner decision and was
  left untouched.

> **Post-decision note (2026-08-09, Issue #31).** The entry above is a
> historical snapshot: its line references and its description of the
> "proof candidate" framing describe the artifacts **as of PR #30's commit,
> before the owner's decision**. Later the same day the owner lifted the
> proof-candidate label (PR #29 comment; implemented in Issue #31 / PR #32),
> which rewrote exactly the framing passages cited above (paper abstract,
> Theorem 4.2 label, report lines 4/40/282) into declarative form and
> refreshed report §5's Issue #11 bullet — resolving this entry's reopen
> proposal without reopening Issue #5. The claim-ID consistency verdicts in
> the matrix are unaffected: hypotheses and conclusions were not touched by
> the relabelling.

---

## Lean sorry tracker

| File | Declaration | Claim ID | Priority | Notes |
|------|-------------|----------|----------|-------|
| ~~`IshikiConj51/Conj51/Cardinality.lean`~~ | ~~`lem_A_exists`~~ | LEM-A-EXISTS | — | **Resolved (Issue #8, 2026-08-09): sorry-free.** CH branch (irrationals, Baire category via `IsMeagre`/`not_isMeagre_of_isOpen`) and non-CH branch (perfect set theorem via `IsClosed.exists_nat_bool_injection_of_not_countable`) both formalised, matching report §3 (Issue #3) exactly, no weakening. `#print axioms lem_A_exists` confirms `[propext, Classical.choice, Quot.sound]` only. |
| ~~`IshikiConj51/Conj51/MainTheorem.lean`~~ | ~~`thm_conj51`~~ | THM-CONJ51 | — | **Resolved (Issue #9, 2026-08-09): sorry-free.** This was the repository's last `sorry`. Statement unchanged since Issue #6 — hypothesis `#D = Cardinal.aleph 1` and conclusion `¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)` faithfully match report §2 / source Conjecture 5.1, with no weakening (not bounded, not uniformly discrete). The entire report §4 assembly is proved in the sibling `thm_conj51_of_lavrentiev`, which differs only by carrying the Alexandrov–Lavrentiev direction as the explicit hypothesis `lavrentiev : ∀ Y : Set ℝ, IsCompletelyMetrizableSpace ↥Y → IsGδ Y`; that hypothesis is now discharged by Issue #23's `isGδ_of_isCompletelyMetrizableSpace` (`GDeltaComplete.lean`, merged in PR #25) at `X := ℝ`, so the proof is the single application `thm_conj51_of_lavrentiev (fun _ h => isGδ_of_isCompletelyMetrizableSpace h) D hD`. `#print axioms thm_conj51` now reports `[propext, Classical.choice, Quot.sound]` — `sorryAx` gone. |

**Sorry count: 0.** No `sorry` remains anywhere in `lean/`, and no declaration in the
repository introduces a custom `axiom`. Verified by `grep -rn '\bsorry\b' lean/`
(prose mentions only) together with the `#print axioms` table below.

## Lean TODO tracker (no theorem statement yet)

Empty as of Issue #9 (2026-08-09): every claim ID now has a Lean theorem
statement — `lem_A_exists`, `lem_star_metric`, `lem_closed_image`,
`thm_conj51` — and, as of the Issue #23 merge and the discharge performed in
Issue #9, every one of them is proved. No Lean proof work remains for the
claim IDs. Mathematical review (Issue #10, Gate B) has since been completed —
see the Issue #10 audit-findings entry above — so the outstanding project work
is the English paper (Issue #11).

## Module map note: `GDeltaComplete.lean` (Issue #23, 2026-08-09)

`IshikiConj51/Conj51/GDeltaComplete.lean` is a new module, **not** one of the
four claim-ID files (it carries no `LEM-`/`THM-` stable ID of its own). It
holds `isGδ_of_isCompletelyMetrizableSpace`, a general-purpose supporting
lemma (the Lavrentiev–Alexandrov direction — see the Mathlib library gaps
entry above). Issue #9's THM-CONJ51 assembly cites it for the `Y ⊆ [0,1]`
step (report §1 background theorem 1 / §4 step 3), specialising `X := ℝ`.
The citation happens in `MainTheorem.lean`, not `ClosedEmbedding.lean` as
originally anticipated: `ClosedEmbedding.lean` proves LEM-CLOSED-IMAGE only,
and the §4 assembly that consumes both it and this lemma lives in
`MainTheorem.lean`. It is imported
from the library root `IshikiConj51.lean` alongside the four claim-ID
modules.

## Met(D) construction (Issue #6, 2026-08-09)

`MetD D` and its `EMetricSpace` instance are sorry-free. They were introduced
in `IshikiConj51/Conj51/MainTheorem.lean` by Issue #6 and **relocated
verbatim** to `IshikiConj51/Conj51/MetD.lean` by Issue #7 — `MainTheorem.lean`
imports the claim modules, so those modules could not import `Met(D)` back
from it. `MetD.lean` is therefore a shared base module, not a fifth claim
file: the architecture's 1:1 mapping is still four files ↔ four claim IDs
(`Cardinality`, `MetricConstruction`, `ClosedEmbedding`, `MainTheorem`), with
`MetD.lean` sitting underneath all of them. No definition or statement
changed in the move.

- `IsMetricOn {D} (d : D → D → ℝ) : Prop` — raw-function metric axioms
  (`dist_self`, `eq_of_dist_eq_zero`, `dist_comm`, `dist_triangle`), so the
  induced topology can be compared to the discrete topology `⊥` separately
  from bundling a full `MetricSpace` structure.
- `MetD D := {d : D → D → ℝ // ∃ h : IsMetricOn d, h.topology = ⊥}` — exactly
  the source's `Met(D)`: ordinary finite-valued metrics on `D` inducing the
  discrete topology, no boundedness or uniform-discreteness restriction.
- `MetD.edist d e := ⨆ p : D × D, ENNReal.ofReal |d.1 p.1 p.2 - e.1 p.1 p.2|`
  — the source's sup-distance, genuinely extended-valued (`ℝ≥0∞`), matching
  the Issue #2/#4 finding that the *ambient* distance on the space `Met(D)`
  can be infinite even though each individual metric on `D` is finite-valued.
  `edist_self`, `edist_comm`, `edist_triangle`, `eq_of_edist_eq_zero` are all
  proved (not `sorry`); `#print axioms` on each shows only
  `[propext, Classical.choice, Quot.sound]`.
- `EDist` / `PseudoEMetricSpace` / `EMetricSpace` instances registered for
  `MetD D` from the above, giving `MetD D` a genuine `TopologicalSpace`
  instance via Mathlib's standard uniformity-from-edist construction — this
  *is* the supremum-metric topology.
- `thm_conj51` uses Mathlib's `TopologicalSpace.IsCompletelyMetrizableSpace`
  (`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean`), which already
  exists in Mathlib v4.32.2. This resolves the leader dossier's flagged
  "biggest risk item" (§D: "Lavrentiev 方向...最大のリスク項目") for the
  *statement* — the predicate needed no local definition. The *proof* that
  `MetD D` does or does not satisfy it (via the Lavrentiev/closed-subspace
  route from Issue #4) is not attempted here.

## LEM-STAR-METRIC formalisation (Issue #7, 2026-08-09)

`IshikiConj51/Conj51/MetricConstruction.lean` is complete and **sorry-free**.

- Index type `StarIndex A := Bool ⊕ (↥A × Option ℕ)`, transcribing report
  §3.2: `Sum.inl true/false` are the anchors `p, q`; `Sum.inr (a, none)` is
  the star centre `y_α`; `Sum.inr (a, some n)` is the satellite `x_{α,n}`.
  Stars are indexed by `A` itself rather than by `α < ω₁`. Since `|A| = ℵ₁`
  the report's enumeration is a *bijection* `ω₁ ≃ A`, so this is a
  relabelling, not a change of construction — report §3.8 records the route.
- `starSpoke n a t := min 1 (|t − a| + 1/(n+1))` is the report's
  `s_n(α,t) = min(1, |t − a_α| + 1/n)` reindexed by `k = n+1`, a bijective
  reindexing of the spoke family (report indexes from `n ≥ 1`, Lean from
  `n ≥ 0`).
- Proved: `dStar_isMetricOn` (C1, all `t ∈ [0,1]`), `dStar_topology_eq_bot`
  (C2, `t ∉ A`), `dStar_topology_ne_bot` (C3, `t ∈ A`), and the report's 系
  as `dStar_mem_MetD_iff : (∃ h : IsMetricOn (dStar A t), h.topology = ⊥) ↔ t ∉ A`.
  The left-hand side is literally `MetD (StarIndex A)`'s defining predicate,
  so no boundedness or uniform-discreteness proxy is substituted.
- `card_starIndex : #(↥A) = ℵ₁ → #(StarIndex A) = ℵ₁` (report §3.2,
  `2 + ℵ₁·ℵ₀ = ℵ₁`).
- The claim ID **LEM-STAR-METRIC** is carried by the aggregate theorem
  `lem_star_metric (hA : #(↥A) = ℵ₁)`, which conjoins all four obligations the
  report's §3.1 statement makes: `#(StarIndex A) = ℵ₁`; (C1) for every
  `t ∈ [0,1]`; the 系 iff; and the existence of the parameter map
  `φ : ↥([0,1] \ A) → MetD (StarIndex A)` with `(φ t).1 = dStar A t`
  (report §3.6). The pointwise iff alone would have been *weaker* than the
  report — it fixes no cardinality and never exposes the family inside
  `MetD` — so the claim ID was moved off it onto the aggregate
  (codex review of PR #21). The component lemmas stay individually available
  for Issue #9.
- Pointwise Lipschitz estimates `starSpoke_sub_le`, `starRadius_sub_le`,
  `dStar_sub_le` (`|d_t(u,v) − d_s(u,v)| ≤ 2|t−s|`) and `dStar_anchor_sub`
  (`= |t−s|` on the anchor pair) — the pair-by-pair half of (C4). Taking
  suprema to get `|t−s| ≤ ρ(d_t,d_s) ≤ 2|t−s|`, and closedness of the image,
  remain LEM-CLOSED-IMAGE (Issue #9).
- General-purpose lemma `IsMetricOn.topology_eq_bot_iff` (in `MetD.lean`,
  stated for an arbitrary `IsMetricOn`, not for the star family) converts
  `.topology = ⊥` into the report's §3.4 isolating-radius criterion; Issue #9
  reuses it.

`#print axioms` on every declaration above yields exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`:
`IsMetricOn.topology_eq_bot_iff`, `dStar_isMetricOn`, `dStar_topology_eq_bot`,
`dStar_topology_ne_bot`, `dStar_mem_MetD_iff`, `lem_star_metric`,
`card_starIndex`, `starMet`, `dStar_sub_le`, `dStar_anchor_sub`.
(At the time of Issue #7 `thm_conj51` still reported `sorryAx`; that last
`sorry` was discharged in Issue #9 after Issue #23 merged — see the sorry
tracker above.)

**Verification method and its limit.** This container's cgroup ceiling
(~3.4 GiB) makes a repository-wide `lake build` an OOM risk: `lake` fans out
one `lean` worker per module and each `import Mathlib` module peaks around
0.8–1 GiB, and `LEAN_NUM_THREADS` caps only the thread count *inside* one
process, not the worker count (this lake, 5.0.0-src / Lean 4.32.2, has no
`-j` flag to cap it either). Issue #7 was therefore verified by
single-process `lake env lean` passes over the concatenated module sources
under `flock /tmp/lean-build.lock` — sufficient for elaboration errors and
for `#print axioms`, but it does **not** exercise the olean/import graph.
A whole-repository consistency build (every module built explicitly, one at
a time, in dependency order) is deferred to the Issue #9 PR and must be run
there once. **Discharged: that build was run in the Issue #9 PR — see the
next section.**

## LEM-CLOSED-IMAGE and the §4 assembly (Issue #9, 2026-08-09)

Files: `IshikiConj51/Conj51/ClosedEmbedding.lean` (new content, was a
placeholder), `IshikiConj51/Conj51/Relabel.lean` (new module),
`IshikiConj51/Conj51/MainTheorem.lean` (proof added),
`IshikiConj51/Conj51/MetD.lean` (five generic `ρ` lemmas appended).

**Two deliberate departures from the report's presentation.** Neither changes
what is proved; both are recorded here rather than in the report, which stays
the mathematical source of truth.

1. *"Bi-Lipschitz homeomorphism onto its image" is packaged as
   `Topology.IsClosedEmbedding`.* The report speaks of the subspace
   `φ(Y) ⊆ Met(D)`; `IsClosedEmbedding φ` is definitionally "φ is a
   homeomorphism onto its image, and that image is closed". This is the exact
   shape Mathlib's inheritance theorem consumes, so no separate transfer along
   `Y ≃ₜ φ(Y)` is needed. The report's quantitative estimate (C4) is *also*
   kept, as the first conjunct of `lem_closed_image`, so nothing is lost:
   the embedding is recorded as bi-Lipschitz with the report's constants
   (`1` and `2`), not merely as a topological embedding.
2. *Report §3.7's sequential argument is replaced by a closed-set
   description.* Instead of extracting a limit parameter from a sequence
   `d_{t_k} → e`, the formalisation proves
   `range φ = {e | anchorParam e ∈ [0,1]} ∩ ⋂_{u,v} {e | e u v = d_{anchorParam e} u v}`
   where `anchorParam e := e p q − 1` is 手順1's readout of the parameter from
   the anchor pair. Both factors are closed: `anchorParam` is continuous
   (1-Lipschitz minus a constant), and each equation is between two continuous
   functions of `e`, the second being `2`-Lipschitz composed with
   `anchorParam` — that 2-Lipschitz estimate *is* `ρ(d_{t_k}, d_t) ≤ 2|t_k−t|`,
   the engine of 手順2.

   The subtle point worth flagging for review: 手順3 (`t ∉ A`) is deliberately
   **not** imposed as a condition in the closed description. It is *derived*
   from `e ∈ Met(D)` via (C3) (`dStar_mem_MetD_iff`), which is what makes the
   description an exact equality rather than a containment. The `t ∈ [0,1]`
   factor, by contrast, genuinely must be imposed: the metric axioms alone
   only force `t ∈ [−1,1]`.

**Why `Relabel.lean` exists.** THM-CONJ51 is stated for an arbitrary `D` with
`#D = ℵ₁`, while the construction produces one particular such set,
`StarIndex A`. `MetD.relabelIsometry (σ : D ≃ E) : MetD E ≃ᵢ MetD D` transports
`Met(–)` along any bijection: relabelling preserves the metric axioms, preserves
discreteness (the isolating radius of `σ u` serves for `u`), and preserves `ρ`
exactly, since `σ × σ` reindexes the defining supremum bijectively. The report
makes the same remark informally in §3.2/§3.8.

**No-smuggle audit of the `lavrentiev` hypothesis.** `thm_conj51_of_lavrentiev`
assumes `∀ Y : Set ℝ, IsCompletelyMetrizableSpace Y → IsGδ Y`. This is report §1
background theorem 1 specialised to the ambient space `ℝ`. It mentions no
`Met(D)`, no `A`, and no cardinality; it is a statement purely about subsets of
the line, and it is a genuine classical theorem being formalised independently
in Issue #23. It therefore does not contain the conclusion. It is nonetheless
outstanding **debt, not progress** — the chain is not sorry-free until Issue #23
lands and `thm_conj51` becomes
`thm_conj51_of_lavrentiev (fun _ h => isGδ_of_isCompletelyMetrizableSpace h) D hD`.

**Statement-gate check on `lem_closed_image`.** No hypothesis on `#A` is
assumed — matching report §3.8, where cardinality enters only via
LEM-STAR-METRIC clause 1 — and `MetD` is the unweakened `Met(D)`: no
boundedness and no uniform-discreteness restriction anywhere in the module.

**Verification method (Issue #9).** Unlike Issue #7, this work was verified by
a real olean build: the deferred whole-repository consistency build was run
here, with every module built explicitly, one at a time, in dependency order
(`MetD` → `Relabel` → `Cardinality` → `MetricConstruction` → `ClosedEmbedding`
→ `MainTheorem`), each as a single-target `lake build <module>` under
`flock /tmp/lean-build.lock` with `LEAN_NUM_THREADS=1`. This does exercise the
olean/import graph, closing the gap Issue #7 left open. `Relabel.lean` was added
to the library root `IshikiConj51.lean` when created, so it is inside the
default build target rather than only compiling in isolation, and the root
module `IshikiConj51` was itself built afterwards, so the guard actually runs
over the new file.

**`#print axioms` audit (Issue #9, 2026-08-09; re-run after the Issue #23
merge discharged the last `sorry`).** Run against the built library root. No
custom axiom is introduced anywhere, and no declaration depends on `sorryAx`:

| Declaration | Axioms |
|---|---|
| `lem_A_exists` | `[propext, Classical.choice, Quot.sound]` |
| `lem_star_metric` | `[propext, Classical.choice, Quot.sound]` |
| `lem_closed_image` | `[propext, Classical.choice, Quot.sound]` |
| `isClosedEmbedding_starParam` | `[propext, Classical.choice, Quot.sound]` |
| `isClosed_range_starParam` | `[propext, Classical.choice, Quot.sound]` |
| `range_starParam` | `[propext, Classical.choice, Quot.sound]` |
| `MetD.relabelIsometry` | `[propext, Classical.choice, Quot.sound]` |
| `MetD.edist_comap` | `[propext, Classical.choice, Quot.sound]` |
| `isFSigma_of_isGdelta_sdiff` | `[propext, Classical.choice, Quot.sound]` |
| `thm_conj51_of_lavrentiev` | `[propext, Classical.choice, Quot.sound]` |
| `thm_conj51` | `[propext, Classical.choice, Quot.sound]` |
| `isGδ_of_isCompletelyMetrizableSpace` (Issue #23) | `[propext, Classical.choice, Quot.sound]` |

The three standard entries are Lean's ordinary logical dependencies
(propositional extensionality, the axiom of choice, and soundness of
quotients) — i.e. classical ZFC-style reasoning, which is what the report's
argument uses (LEM-A-EXISTS is a ZFC existence proof). The capstone
`thm_conj51` is pinned to exactly that list: `sorryAx` is absent, so the
formal chain from LEM-A-EXISTS through LEM-STAR-METRIC, LEM-CLOSED-IMAGE and
the Lavrentiev direction to THM-CONJ51 is complete inside this repository,
with nothing deferred to a future Mathlib release.

This is a statement about the *formal* chain only. By itself it does not
discharge Gate B (Issue #10): whether `MetD`, `dStar`, `IsFSigma` and the
`IsGδ` ambient convention faithfully render the source's notions is a question
about the statements, which `#print axioms` cannot answer. See the
statement-gate notes in the Issue #9 section above. That remaining question was
settled separately by the Issue #10 review (2026-08-09), whose §5 cross-checks
each claim ID's Lean statement against the report and the arXiv source and
finds no proxy weakening; the audit entry is above.

## Mathlib library gaps (v4.32.2)

| Gap | Description | File | Status |
|-----|-------------|------|--------|
| `IsFSigma` predicate | No canonical Mathlib built-in; defined locally as `∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n`. | `IshikiConj51/Conj51/Cardinality.lean` | open |
| `Met(D)` as a type | ~~No Mathlib type for the space of compatible metrics on D with the sup-metric topology.~~ Resolved (Issue #6, 2026-08-09): constructed explicitly as `MetD`, see above. | `IshikiConj51/Conj51/MetD.lean` (relocated from `MainTheorem.lean` by Issue #7) | resolved |
| `TopologicalSpace.IsCompletelyMetrizableSpace` | Exists natively in Mathlib v4.32.2 (`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean`) — no local definition needed. Confirmed by direct source inspection (Issue #6). | `IshikiConj51/Conj51/MainTheorem.lean` | not a gap (dossier flagged as biggest risk item; resolved by inspection) |
| Alexandrov–Lavrentiev direction (completely metrizable subspace ⟹ Gδ in ambient space) | **Resolved locally (Issue #23, 2026-08-09).** Confirmed absent from Mathlib v4.32.2 (Issue #19); proved from scratch as `isGδ_of_isCompletelyMetrizableSpace {X} [MetricSpace X] {Y : Set X} (h : IsCompletelyMetrizableSpace Y) : IsGδ Y` in a new module, general form (no separability assumption). Proof: X-diameter-restricted oscillation argument (leader dossier §E) — `Uₙ := ⋃₀ {V open, X-bounded, X-diam V < 1/(n+1), and diam of V's Y-trace < 1/(n+1)}` (using `Bornology.IsBounded` + `Metric.diam` rather than `EMetric`/`Metric.ediam`, to sidestep the "unbounded set has junk diam 0" trap while staying in the finite-real API); `Y = (⋂ₙ Uₙ) ∩ closure Y`, forward inclusion via shrinking balls, backward inclusion via a Cauchy sequence (`cauchySeq_of_le_tendsto_0` / `cauchySeq_tendsto_of_complete`) converging both to the test point (in `X`) and into `Y` (via `Y`'s upgraded complete metric), forcing equality by uniqueness of limits (`tendsto_nhds_unique`). `Y`'s closure is Gδ via `PerfectlyNormalSpace.closed_gdelta` (automatic for metric spaces); `Uₙ` is Gδ via `IsGδ.iInter_of_isOpen`; combined via `IsGδ.inter`. `#print axioms` confirms `[propext, Classical.choice, Quot.sound]` only. **Real Lean instance-diamond found and fixed along the way**: `letI := upgradeIsCompletelyMetrizable Y` alone was not sufficient — `Y : Set X` already carries a competing global `Subtype.pseudoMetricSpace`/`instBornologySubtype` instance chain (the *ambient*, possibly non-complete restricted metric), and several Mathlib lemmas (`cauchySeq_of_le_tendsto_0`, `IsBounded.subset`) silently resolved to that ambient instance instead of the upgraded complete one, causing type mismatches only surfaced once `CompleteSpace` was actually needed. Fixed by explicitly re-`letI`-ing `MetricSpace`/`PseudoMetricSpace`/`UniformSpace`/`Bornology` Y-instances from the upgrade before using any of them, forcing consistent resolution throughout. **Consumed by Issue #9 (2026-08-09):** `thm_conj51_of_lavrentiev`'s explicit `lavrentiev` hypothesis is exactly this lemma instantiated at `X := ℝ`, so `thm_conj51` discharges to `thm_conj51_of_lavrentiev (fun _ h => isGδ_of_isCompletelyMetrizableSpace h) D hD`. No ℝ-ambient ↔ `[0,1]`-ambient conversion lemma is needed: the report's "Gδ in [0,1]" step is carried out in the ambient line and the intersection with the closed set `[0,1]` happens inside `isFSigma_of_isGdelta_sdiff`. | `IshikiConj51/Conj51/GDeltaComplete.lean` | **resolved** |
| Cantor–Bendixson / perfect set theorem | **Used (Issue #8, 2026-08-09).** Ended up not needing `exists_countable_union_perfect_of_isClosed` directly — `IsClosed.exists_nat_bool_injection_of_not_countable` (below) was sufficient on its own for the non-CH branch. | `IshikiConj51/Conj51/Cardinality.lean` | used |
| Perfect set has cardinality continuum | **Used (Issue #8, 2026-08-09).** `IsClosed.exists_nat_bool_injection_of_not_countable` (`Mathlib/Topology/MetricSpace/Perfect.lean:135`, requires `[PolishSpace α]`, satisfied by `ℝ`): closed + uncountable ⟹ injection from `ℕ → Bool` (cardinality `𝔠`) into the set. Composed with `Cardinal.mk_le_of_injective` and `Cardinal.mk_arrow`/`mk_bool`/`mk_nat` to get `𝔠 ≤ #(F n)`. | `IshikiConj51/Conj51/Cardinality.lean` | used |
| `ℵ₁ ≤ 𝔠` | **Used (Issue #8, 2026-08-09).** `aleph_one_le_continuum : ℵ₁ ≤ 𝔠` (`Mathlib/SetTheory/Cardinal/Continuum.lean:85`) — exact match, no derivation needed. Also used `aleph0_lt_aleph_one`, `aleph0_lt_continuum`, `le_mk_iff_exists_subset`, `mk_sdiff_add_mk`, `add_lt_of_lt`, `mk_Icc_real`, `Cardinal.le_aleph0_iff_set_countable`. | `IshikiConj51/Conj51/Cardinality.lean` | used |
| Closed subspace of complete space is complete | `instance IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} [hs : IsClosed s] : CompleteSpace s` (`Mathlib/Topology/UniformSpace/UniformEmbedding.lean:320`) — exact match for the Issue #4 elementary closed-subspace-inheritance argument; no manual Cauchy-sequence proof needed in Lean. **Superseded in practice (Issue #9, 2026-08-09):** the assembly does not need to descend to `CompleteSpace`, because Mathlib states the inheritance directly at the level of the predicate the theorem is about — `Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace` (`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean:249`), with the companion `IsClosed.isCompletelyMetrizableSpace` (:295). Neither assumes separability, which is exactly what the non-separable `Met(D)` requires (Issue #4). | `IshikiConj51/Conj51/MainTheorem.lean` (Issue #9) | used (via `IsClosedEmbedding.IsCompletelyMetrizableSpace`) |
| "ℚ is not Gδ" as a standalone lemma | Not found under that name. Not actually needed: report §3 (LEM-A-EXISTS, CH branch) argues directly via the Baire category theorem on meager sets, never via a "ℚ is not Gδ" fact. (Mathlib does have `IsGδ.setOf_irrational : IsGδ {x | Irrational x}` — the complementary *positive* fact — in `Mathlib/Topology/Instances/Irrational.lean:41`, available if ever wanted as a cross-check, but not load-bearing.) | — | not a gap (not needed) |
| Baire category / meagre-set API (CH branch) | **Used (Issue #8, 2026-08-09).** `IsMeagre`, `IsNowhereDense`, `isClosed_isNowhereDense_iff_compl`, `isMeagre_iUnion`, `IsMeagre.union`/`.mono`, `not_isMeagre_of_isOpen` (`Mathlib/Topology/GDelta/Basic.lean`, `Mathlib/Topology/Baire/Lemmas.lean`; `BaireSpace ℝ` is automatic from `IsCompletelyPseudoMetrizableSpace`). Singleton nowhere-density used `PerfectSpace.not_isolated`/`dense_compl_singleton` (`Mathlib/Topology/Perfect.lean`, `Mathlib/Topology/ClusterPt.lean`; `PerfectSpace ℝ` is automatic from `[T1Space] [ConnectedSpace] [Nontrivial]`), and `Rat.denseRange_cast` for density of ℚ. | `IshikiConj51/Conj51/Cardinality.lean` | used |
