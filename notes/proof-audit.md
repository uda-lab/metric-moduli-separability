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
| LEM-A-EXISTS | ∃ A ⊆ [0,1], \|A\| = ℵ₁, A not Fσ | ✅ audited (2026-08-09) | See report §3; CH case via irrationals + Baire category, non-CH case via the perfect-set-theorem counting argument. Lean proof still pending (`sorry`), tracked below. |
| — | Y = [0,1] \ A not Gδ → not completely metrizable | ✅ audited (2026-08-09) | See report §1 (background theorems 1–2) and §4 steps 2–3, 5. Fσ/Gδ complement duality made explicit (De Morgan); Alexandrov–Lavrentiev used only for the separable ambient [0,1]; closed-subspace inheritance for the non-separable Met(D) now uses an elementary, separability-free argument instead. |
| LEM-STAR-METRIC | Star-type family of compatible metrics on D parametrised by Y | ✅ written, awaiting independent review (2026-08-09) | Report §3.1–§3.5: explicit construction (reference pair + ω₁ stars, s_n(α,t) = min(1, \|t−a_α\| + 1/n)) with full proofs of (C1) metric axioms, (C2) compatibility for t ∈ Y, (C3) loss of compatibility at t ∈ A. Lean statement still absent (Issue #7). |
| LEM-CLOSED-IMAGE | Bi-Lipschitz embedding with closed image | ✅ written, awaiting independent review (2026-08-09) | Report §3.6–§3.7: (C4) \|t−s\| ≤ ρ(d_t,d_s) ≤ 2\|t−s\| and (C5) closedness of φ(Y), including the boundary case where the limit parameter lands in A and (C3) supplies the contradiction. Lean statement still absent (Issue #9). |
| THM-CONJ51 | Full assembly | ✅ written, awaiting independent review (2026-08-09) | Report §4 steps 1–6; no mathematically unwritten step remains. Retains **proof candidate** status until Gates A–C (independent review, Lean formalisation, report/Lean statement agreement) pass. Lean statement still absent (Issue #9). |

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
- **(C5) does not use `|A| = ℵ₁`.** The closedness argument works for any
  non-empty `A ⊆ [0,1]`; the cardinality hypothesis is consumed only by the
  count `|D| = 2 + ℵ₁ + ℵ₁·ℵ₀ = ℵ₁`, and non-Fσ-ness is consumed only by main
  proof steps 2–3. This dependency split is stated in report §3.8 so that a
  later change to LEM-A-EXISTS can be traced to exactly the steps it affects.
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

---

## Lean sorry tracker

| File | Declaration | Claim ID | Priority | Notes |
|------|-------------|----------|----------|-------|
| `IshikiConj51/Conj51/Cardinality.lean` | `lem_A_exists` | LEM-A-EXISTS | high | Mathematical audit complete (report §3, 2026-08-09); Lean formalisation of the two-case argument is still open (Issue #8). |

No `sorry` must remain in the final formalisation.

## Lean TODO tracker (no theorem statement yet)

The following claim IDs do **not** yet have Lean theorem statements because
the required mathematical objects (notably the `Met(D)` type) are not yet
formalised.  The stable IDs will be attached to theorems only once the
statements faithfully represent the mathematical claims.

| File | Claim ID | Blocked on |
|------|----------|------------|
| `IshikiConj51/Conj51/MetricConstruction.lean` | LEM-STAR-METRIC | star-type construction + audit |
| `IshikiConj51/Conj51/ClosedEmbedding.lean` | LEM-CLOSED-IMAGE | LEM-STAR-METRIC + Met(D) type |
| `IshikiConj51/Conj51/MainTheorem.lean` | THM-CONJ51 | all above + Met(D) type |

## Mathlib library gaps (v4.32.2)

| Gap | Description | File | Status |
|-----|-------------|------|--------|
| `IsFSigma` predicate | No canonical Mathlib built-in; defined locally as `∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n`. | `IshikiConj51/Conj51/Cardinality.lean` | open |
| `Met(D)` as a type | No Mathlib type for the space of compatible metrics on D with the sup-metric topology.  Must be constructed explicitly. | `IshikiConj51/Conj51/MainTheorem.lean` | open |
