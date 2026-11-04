# Borel manuscript audit — 2026-11-03 received source

> **Subject:** Y. Ishiki and T. Uda, *Borelness of Moduli Spaces of Metrics
> Implies Separability*, the manuscript source received from the owner on
> 2026-11-03 (`\date{November 3, 2026}`). This note calls it **the 2026-11-03
> received source**. It is **not** an arXiv version: arXiv carries v1 only.
> **Role:** this note is the active mathematical source of truth for the Borel
> track and the statement gate for its Lean formalisation.
> `notes/borel-manuscript-20260827-audit.md` is the frozen record of the
> 2026-08-27 received source and `notes/borel-preprint-audit.md` the frozen
> record of arXiv:2608.19618 v1; their verdicts are carried into the
> **2026-08-27 verdict** column of §2 here.
> **Verdicts:** **PASS** (statement and proof check out), **FIX** (statement
> believed true; the written proof has a concrete, repairable gap),
> **EXTERNAL** (correct modulo an external theorem, recorded in §4). A
> statement can be PASS/FIX *and* EXTERNAL.
> **Policy:** a statement is not accepted because it appears in the manuscript.
> Every printed proof of the 2026-11-03 received source was re-read and
> re-checked against the source itself for this note.

---

## 0. Provenance and access rules

* **What was received.** An archive supplied by the owner on 2026-11-03,
  containing `main.tex` (93,250 bytes) and `main.bbl` (13,664 bytes). Title,
  authors and keywords are unchanged from the earlier sources. It is a later
  working draft of the same paper.
* **Where it lives.** Outside version control. It is **never** copied into the
  repository, a worktree, a commit, a pull request, or an issue comment.
* **Reference-only, by owner directive.** The ceiling for this note is: LaTeX
  `\label` references, statement-level paraphrase, and short one-line
  quotations. No proof is reproduced.
* **Naming.** The public e-print arXiv:2608.19618 carries **v1 only**. Neither
  received source may be called "arXiv v2".
* **Comparison basis.** The 2026-08-27 archive is not available to this audit.
  Every "changed since 2026-08-27" statement below is a comparison against the
  record in `notes/borel-manuscript-20260827-audit.md`, not a textual diff.
* **Macros and ambient conventions.** Unchanged from the 2026-08-27 note §0.
  The definitions of `CPM(X)`, `UCPM(X;R)`, `𝒰𝒟^R`, the characteristic range
  set and the (R-)components now sit in numbered definitions (§1), with the
  same content.

---

## 1. Label and numbering map, 2026-08-27 ↔ 2026-11-03

Labels are the stable identifiers; numbers are derived from the `[section]`
theorem counter shared by every environment (definitions included) and are
recorded only to navigate a compiled PDF. **Cite labels, not numbers.** The
Lean docstrings still carry v1 numbers; they are not renumbered — the label is
the identifier that survives every revision.

**Why the numbers moved.** Four definitions are now numbered environments,
the ultrametric clause of the separated-set lemma became its own lemma, and
the ultrametric results moved from §3 into a new §4 with one new lemma.

### 1.1 Preliminaries (§2)

| label | 11-03 | 08-27 | note |
|---|---|---|---|
| `def:continuous-pseudometric-space` | 2.1 | — | `CPM(X)`, `Met(X)`, `BMet(X)`, `BCPM(X)` |
| `thm:koshino-characterization` | 2.2 | 2.1 | external **E3** |
| `thm:metric-isometric-extensor` | 2.3 | 2.2 | external **E1** |
| `lem:one-point-amalgamation` | 2.4 | 2.3 | completeness half no longer proved in text (§2.2) |
| `def:separated-net` | 2.5 | — | `ε`-net, `ε`-separated |
| `lem:maximal-separated-set` | 2.6 | 2.4 (metric clause) | |
| `lem:maximal-separated-set-ultrametric` | 2.7 | 2.4 (ultrametric clause) | **new label**, now with a proof |
| `lem:cpm-complete` | 2.8 | 2.5 | |
| `def:ultrametric-pseudometric-space` | 2.9 | — | `UCPM`, `Adm`, `𝒰𝒟^R`, `UMet`, `UComp` |
| `lem:ucpm-complete` | 2.10 | 2.6 | |
| `thm:ultrametric-isometric-extensor` | 2.11 | 2.7 | external **E2** |
| `def:finite-distance-components` | 2.12 | — | components; asserts they are clopen |
| `lem:metric-extensor-pullbacks` | 2.13 | 2.8 | |
| `lem:continuous-pullback-obstruction` | 2.14 | 2.9 | |
| `lem:relative-borel-inheritance` | 2.15 | 2.10 | |
| `thm:complete-metrizability-g-delta` | 2.16 | 2.11 | external **E4**d |
| `prop:dense-aleph1-nonborel-interval` | 2.17 | 2.12 | |
| `prop:dense-aleph1-nonborel-cantor` | 2.18 | 2.13 | proof compressed (§2.2) |

### 1.2 Archimedean results (§3)

| label | 11-03 | 08-27 | note |
|---|---|---|---|
| `lem:metric-coding` | 3.1 | 3.1 | |
| `lem:closed-parameter-embedding` | 3.2 | 3.2 | |
| `thm:bounded-discrete-nonborel` | 3.3 | 3.3 | |
| `thm:metric-component-nonborel` | 3.4 | 3.4 | `\|Z\| ≥ ℵ₁` |
| `cor:discrete-metric-nonborel` | 3.5 | 3.5 | **now only the `Met(Z)` clause**; still `\|Z\| = ℵ₁` |
| `thm:borel-separability` | 3.6 | 3.6 | `BMet(X)` hypothesis, unchanged |
| `cor:nonseparable-metric-nonborel` | 3.7 | 3.7 | **now a `theorem` environment**; label keeps `cor:`; clauses `(M1)`, `(M2)` |
| `cor:metric-space-complete-separability` | 3.8 | 3.8 | **proof repaired** (#113, §3) |
| `cor:bounded-metric-complete-sigma-compact` | 3.9 | 3.9 | five-way, `(C1)`–`(C5)` |
| `thm:complete-metric-nonborel` | 3.10 | 3.10 | |
| `cor:complete-metric-borel-separability` | 3.11 | 3.11 | |

### 1.3 Non-Archimedean results (§4)

| label | 11-03 | 08-27 | note |
|---|---|---|---|
| `lem:ultrametric-coding` | 4.1 | 3.12 | clauses `(R1)` compatibility, `(R2)` completeness |
| `lem:closed-ultrametric-parameter-embedding` | 4.2 | 3.13 | |
| `thm:discrete-ultrametric-nonborel` | 4.3 | 3.14 | |
| `thm:ultrametric-component-nonborel` | 4.4 | 3.15 | still `\|Z\| = ℵ₁` |
| `lem:ultrametric-extensor-preserving-component` | 4.5 | — | **new lemma**, extracted from the 08-27 proof of 3.16 |
| `cor:nonseparable-ultrametric-nonborel` | 4.6 | 3.16 | **now a `theorem` environment**; clauses `(U1)`, `(U2)` |
| `thm:ultrametric-borel-separability` | 4.7 | 3.17 | |
| `cor:ultrametric-space-complete-separability` | 4.8 | 3.18 | |
| `thm:complete-ultrametric-nonborel` | 4.9 | 3.19 | |
| `cor:complete-ultrametric-borel-separability` | 4.10 | 3.20 | |

### 1.4 Equation and clause labels

The equation labels recorded in the 2026-08-27 note §1.3 that this note uses
are all still present. New labels used here: the extensor clauses are now
tagged `(E1)`–`(E4)` (`item:metric-extensor-*`) and `(I1)`–`(I3)`
(`item:ultrametric-extensor-*`), the pullback clauses `(P1)`–`(P4)`;
`eq:clopen-net-retraction-map`, `eq:net-metric-quotient`,
`eq:net-nearest-point`, `eq:component-controlled-base-comparison`
(lemma 4.5); `eq:uncountable-net-ball`, `eq:net-transferred-coding`,
`eq:net-coding-amalgamation`, `eq:net-coding-thresholds`,
`eq:component-controlled-parameter-map` (theorem 4.6);
`eq:complete-ultrametric-extensor`, `eq:complete-ultrametric-parameter-map`,
`eq:complete-ultrametric-coding-restriction` (corollary 4.10).

---

## 2. Theorem-by-theorem audit

### 2.0 Summary verdict table

| label | track | 2026-08-27 verdict | 2026-11-03 verdict |
|---|---|---|---|
| `thm:koshino-characterization` | A | EXTERNAL (E3) | **EXTERNAL** (E3) |
| `thm:metric-isometric-extensor` | A | EXTERNAL (E1) | **EXTERNAL** (E1) |
| `lem:one-point-amalgamation` | shared | PASS + EXTERNAL | **PASS + EXTERNAL** (§4, standard) |
| `lem:maximal-separated-set` | shared | PASS | **PASS** |
| `lem:maximal-separated-set-ultrametric` | NA | (inside 2.4) PASS | **PASS** |
| `lem:cpm-complete`, `lem:ucpm-complete` | A / NA | EXTERNAL | **EXTERNAL** (§4, standard) |
| `thm:ultrametric-isometric-extensor` | NA | EXTERNAL (E2) | **EXTERNAL** (E2) |
| `def:finite-distance-components` (clopen claim) | shared | — (silent) | **PASS** |
| `lem:metric-extensor-pullbacks` | A | PASS + EXTERNAL (E1) | **PASS + EXTERNAL** (E1) |
| `lem:continuous-pullback-obstruction` | shared | PASS | **PASS** |
| `lem:relative-borel-inheritance` | shared | PASS | **PASS** |
| `thm:complete-metrizability-g-delta` | shared | EXTERNAL (E4d) | **EXTERNAL** (E4d) |
| `prop:dense-aleph1-nonborel-interval` | shared | PASS + EXTERNAL (E4a, E4b) | **PASS + EXTERNAL** (E4a, E4b) |
| `prop:dense-aleph1-nonborel-cantor` | NA | PASS + EXTERNAL (E4c) | **PASS + EXTERNAL** (E4c) |
| `lem:metric-coding` | A | PASS | **PASS** |
| `lem:closed-parameter-embedding` | A | PASS | **PASS** |
| `thm:bounded-discrete-nonborel` | A | PASS | **PASS** |
| `thm:metric-component-nonborel` | A | PASS | **PASS** |
| `cor:discrete-metric-nonborel` | A | PASS | **PASS** |
| `thm:borel-separability` | A | PASS + EXTERNAL (E1) | **PASS + EXTERNAL** (E1) |
| `cor:nonseparable-metric-nonborel` | A | PASS + EXTERNAL (E1, E1c) | **PASS + EXTERNAL** (E1, E1c) |
| `cor:metric-space-complete-separability` | A | **FIX** (#113) | **PASS + EXTERNAL** (E4d) |
| `cor:bounded-metric-complete-sigma-compact` | A | PASS + EXTERNAL (E3, E5, E6) | **PASS + EXTERNAL** (E3, E4d, E5, E6) |
| `thm:complete-metric-nonborel` | A | PASS | **PASS** |
| `cor:complete-metric-borel-separability` | A | PASS + EXTERNAL (E1(4)) | **PASS + EXTERNAL** (E1(4)) |
| `lem:ultrametric-coding` | NA | PASS | **PASS** |
| `lem:closed-ultrametric-parameter-embedding` | NA | PASS | **PASS** |
| `thm:discrete-ultrametric-nonborel` | NA | PASS | **PASS** |
| `thm:ultrametric-component-nonborel` | NA | PASS | **PASS** |
| `lem:ultrametric-extensor-preserving-component` | NA | — (inside 3.16, E2c) | **PASS + EXTERNAL** (E2c′) |
| `cor:nonseparable-ultrametric-nonborel` | NA | PASS + EXTERNAL (E2, E2c) | **PASS + EXTERNAL** (E2c′, Prop 2.3) |
| `thm:ultrametric-borel-separability` | NA | PASS + EXTERNAL (E2, E2c) | **PASS + EXTERNAL** (via 4.6) |
| `cor:ultrametric-space-complete-separability` | NA | PASS + EXTERNAL (E4d) | **PASS + EXTERNAL** (E4d) |
| `thm:complete-ultrametric-nonborel` | NA | PASS | **PASS** |
| `cor:complete-ultrametric-borel-separability` | NA | PASS + EXTERNAL (E2(N1)) | **PASS + EXTERNAL** (E2(N1), E4d) |

A = Archimedean, NA = non-Archimedean. E2c′ is the re-scoped construction
dependency of §4; it replaces the 2026-08-27 E2c.

**Net movement.** The one 2026-08-27 FIX (#113) is discharged by the preferred
repair. Every editorial finding of the 2026-08-27 note §2.21 and the two
exposition requests of its §2.19 item 7 and §2.20 scope note are resolved,
except the `ℵ₁`-versus-`≥ ℵ₁` hypothesis of `cor:discrete-metric-nonborel`
(§3). **The 2026-11-03 received source has no FIX- or BLOCKED-level defect,
and no statement in it was found to be false.** Three new editorial findings
are recorded in §2.3; none bears on a verdict.

**Verdict semantics.** As before: verdicts are local, and a downstream PASS
means "no new gap introduced here", not "unconditional".

### 2.1 Unchanged statements and proofs

For every row of §2.0 not discussed in §2.2, the 2026-11-03 statement and
printed proof agree, as far as the 2026-08-27 note records them, with the
2026-08-27 text, and the check recorded in the corresponding section of that
note was re-run against the new text and holds. In particular:

* `lem:metric-coding`, `lem:closed-parameter-embedding`,
  `thm:bounded-discrete-nonborel`: the coding `d_t` (cluster distances
  `l_n(α,t) = |t − w_α| + 2^{-n}`, `p`–`q` distance `1 + t`, cross-cluster
  distance `4`), the bi-Lipschitz estimate `|s − t| ≤ 𝒟(d_s,d_t) ≤ 2|s − t|`
  and the pullback `Φ⁻¹(Met(Z)) = [0,1] ∖ S`. ✓
* `thm:metric-component-nonborel`: ball selection from `Z = ⋃_k B̄(z,2^k)`
  with `z ∈ H` now explicit, the compatibility of `m_t` now argued in text
  (cross distances `≥ d(x,z)` and `inf_{x ≠ z} d(x,z) > 0` because `d` is
  compatible on the discrete `Z`), the component bound `2^k + 4` on cross
  pairs, and the bi-Lipschitz estimate through the `z`–`q_H` pair. ✓
* `thm:borel-separability`, `cor:nonseparable-metric-nonborel`,
  `thm:complete-metric-nonborel`, `cor:complete-metric-borel-separability`:
  as in the 2026-08-27 note §2.14 and §2.17. The pointwise estimate
  `eq:metric-extensor-point-estimate` (`r(x,a) ≤ 4d(x,a) + 1`, E1c) and the
  resulting bound `|r(x,y) − d(x,y)| < 10ε + 2` are unchanged. ✓
* `cor:bounded-metric-complete-sigma-compact`: the six implications, the
  `G_δ` characterisation `eq:component-restriction-characterization` and the
  open-surjection argument `eq:restriction-map-ball-image` are as in the
  2026-08-27 note §2.16. ✓
* `lem:ultrametric-coding` … `thm:ultrametric-component-nonborel`,
  `thm:complete-ultrametric-nonborel`: as in the 2026-08-27 note §2.18 and
  §2.20. In `thm:ultrametric-component-nonborel` the ball `H = B̄(z,q)` is the
  whole ball, so `d(x,z) > q` outside `H` and `q > 0` (otherwise
  `H = {z}`). ✓

### 2.2 Changed items

#### `cor:metric-space-complete-separability` — PASS + EXTERNAL (E4d)

The proof now runs: `Met(X)` completely metrizable ⇒ `G_δ` in `CPM(X)` by
`thm:complete-metrizability-g-delta` ⇒ Borel ⇒ separable by the contrapositive
of `cor:nonseparable-metric-nonborel`. This is the preferred repair of the
2026-08-27 note §8. ✓ (Editorial: the proof opens with "Now assume", a
leftover of the earlier text.)

#### `cor:discrete-metric-nonborel` — PASS

Now states only that `Met(Z)` is non-Borel in `CPM(Z)` for `|Z| = ℵ₁`; the
"every component" clause is left to `thm:metric-component-nonborel`. The proof
is `thm:metric-component-nonborel` + openness of components in `Met(Z)` +
`lem:relative-borel-inheritance`, which needs `Met(Z) ≠ ∅` (true: the discrete
`{0,1}`-metric). ✓

#### `lem:maximal-separated-set-ultrametric` — PASS

New label for the 2026-08-27 ultrametric clause, now a separate lemma with its own proof: maximality
gives the cover by open `r`-balls at `A`, `d(a,b) ≥ r` and the strong
triangle inequality give disjointness, and balls are clopen, so the centre map
`π` is a continuous retraction with `d(x,π(x)) < r`. ✓

#### `def:finite-distance-components` — PASS

The definition now asserts that components of `CPM(Z)` and `Met(Z)`, and
`R`-components of `UCPM(Z;R)` and `UMet(Z;R)`, are clopen. Each is a union of
`min{·,1}`-balls of radius `1`, and so is its complement; for `𝒰𝒟^R` this uses
`𝒰𝒟^R(d,f) ≤ 𝒰𝒟^R(d,e) ∨ 𝒰𝒟^R(e,f)`, which follows from the definition of
`Adm` because the maximum of two admissible thresholds is admissible. ✓

#### `lem:one-point-amalgamation` — PASS + EXTERNAL (§4, standard)

The proof is now only the two citations (interpolation paper Proposition 3.2
for the metric case, *Fractal dimensions* Lemma 2.15 for the ultrametric case,
applied to disjoint copies). The completeness half, which the 2026-08-27
source proved in text, is no longer proved there; whether the cited results
include completeness is not verified here. The audit's own argument (2026-08-27
note §2.3: a Cauchy sequence is either eventually in one piece or converges to
the glue point) proves it, so the verdict stands. Editorial finding 2 (§2.3).

#### `prop:dense-aleph1-nonborel-cantor` — PASS + EXTERNAL (E4c)

The construction is `S = Q ∪ (f(S₀) ∖ P)` for disjoint countable dense `P`, `Q`,
a Borel isomorphism `f : [0,1] → 2^ω` (Srivastava, Theorem 3.3.13) and `S₀`
from `prop:dense-aleph1-nonborel-interval`; the proof now ends with "`S` is a
required set". Checked: `|S| = ℵ₁`; `Q ⊆ S` and `P ⊆ 2^ω ∖ S` give
bi-density; `f⁻¹(S)` differs from `S₀` by a subset of the countable
`f⁻¹(P ∪ Q)`, so `S` Borel would make `S₀` Borel. ✓ Editorial finding 3
(§2.3).

#### `lem:ultrametric-extensor-preserving-component` — PASS + EXTERNAL (E2c′)

**Statement.** For a nonempty `R`-valued ultrametric space `(Y,d)`,
`r ∈ R ∖ {0}` and a maximal `r`-separated `A ⊆ Y`, there are an isometric
extensor `E : UMet(A;R) → UMet(Y;R)` and `τ ∈ R` with
`𝒰𝒟^R_Y(E(d|_{A²}), d) ≤ τ`.

**Printed proof, checked step by step.**

1. `A` is closed and discrete (separation); `π` and
   `eq:clopen-net-retraction` come from `lem:maximal-separated-set-ultrametric`. ✓
2. The metric quotient `Y_{/A}` collapses `A` to a point `ϖ_A`, with
   `δ(p x, p y) = min{d(x,y), ρ(x) + ρ(y)}` and `ρ = dist(·, A)`
   (`eq:net-metric-quotient`), cited to the factorization paper's
   Proposition 2.6. The formula is well defined on classes, and `p` is
   1-Lipschitz. ✓ (E2c′)
3. `Y_{/A}` is zero-dimensional: trivially if `A = Y`, otherwise by
   Proposition 2.8 since `Y ∖ A` is ultrametrizable; Proposition 2.3 then
   gives a compatible `R`-valued ultrametric `v₀`, truncated to
   `v = min{v₀, b}`, `b ∈ R ∖ {0}`. ✓ (E2c′)
4. `eq:net-nearest-point`, `d(x,π(x)) = ρ(x)`: for `a ≠ π(x)` the isosceles
   property gives `d(x,a) = d(π(x),a) ≥ r > d(x,π(x))`. ✓
5. `Θ = (π, p) : Y → A × Y_{/A}` is a topological embedding. Injectivity is
   immediate. Off `A`, inverse continuity comes from `p|_{Y ∖ A}` being a
   homeomorphism onto `Y_{/A} ∖ {ϖ_A}` (Proposition 2.6) and `Y ∖ A` being
   open. At `a ∈ A`, `Θ⁻¹({a} × B(ϖ_A, s; δ)) ⊆ B(a, s; d)` by step 4. ✓
   This replaces the 2026-08-27 route through the conditions (D), (SR) of the
   factorization paper's Theorem 2.11 and the proof of its Theorem 3.1; neither
   is used any more.
6. `E(w)(x,y) = w(π x, π y) ∨ v(p x, p y)`
   (`eq:component-controlled-ultrametric-extension`). The text says "the cited
   proof shows that `E` is an isometric extensor". Checked directly:
   `E(w)` is the pullback along the embedding `Θ` of the max-product of two
   compatible `R`-valued ultrametrics, hence in `UMet(Y;R)`; on `A²`, `p` is
   constant, so `E(w)|_{A²} = w`; and an `ε` is admissible for `(w₁,w₂)` iff it
   is admissible for `(E(w₁),E(w₂))` (one direction by restriction, the other
   because the `v`-term is common), so
   `eq:component-controlled-extension-isometry` holds. ✓ This step needs
   nothing from the cited proof beyond the formula.
7. `d̂ = E(d|_{A²})` satisfies `d̂(x, π x) = v(p x, ϖ_A) ≤ b`, and the strong
   triangle inequality through `π x`, `π y` gives
   `eq:component-controlled-base-comparison` with `τ = r ∨ b ∈ R`. ✓

**Audit observation — an elementary proof without E2c′.** The quotient,
Propositions 2.3/2.6/2.8 and the embedding `Θ` can all be avoided. Put

`v′(x,y) = d(x,y)` if `π x = π y`, and `v′(x,y) = ρ(x) ∨ ρ(y)` otherwise

(equivalently `v′ = min{d, ρ(x) ∨ ρ(y)}`, the ultrametric form of
`eq:net-metric-quotient`), and `E′(w)(x,y) = w(π x, π y) ∨ v′(x,y)`.
Then, checked case by case:

* `v′` is an `R`-valued pseudo-ultrametric vanishing on `A²` (`ρ = d(·,π·)`
  takes values in `R`);
* `E′(w)` is an `R`-valued ultrametric, equal to `d` on each ball `B(a,r)` and
  `≥ w(a,b) ≥ inf_{b′ ≠ a} w(a,b′) > 0` between `B(a,r)` and `B(b,r)`, so it
  induces the topology of `Y` whenever `w` is compatible with the discrete
  topology of `A`;
* `E′(w)|_{A²} = w`, and `Adm(E′(w₁),E′(w₂)) = Adm(w₁,w₂)`, so `E′` is an
  isometric extensor;
* across two balls, `d(x,y) = d(π x, π y) > ρ(x) ∨ ρ(y)` by the isosceles
  property, hence **`E′(d|_{A²}) = d` exactly** and the lemma holds with
  `τ = 0`.

So the lemma is elementary. Recorded for the Lean lane (#132), which can
discharge the E2c hypothesis with no external input, and as an optional
simplification for the authors; the printed proof is correct as it stands.

#### `cor:nonseparable-ultrametric-nonborel` — PASS + EXTERNAL (E2c′ via 4.5, Proposition 2.3)

The proof is the 2026-08-27 proof with the extensor construction moved into
`lem:ultrametric-extensor-preserving-component`. Re-checked as in the
2026-08-27 note §2.19 items 1, 5, 6, 8–12, with two changes:

* The compatibility step for `m_t` now gives its reason: cross distances are
  `≥ e(x,z) ≥ r` by the `r`-separation of `A`. This is the reason the
  2026-08-27 note §2.19 item 7 asked for; resolved. ✓
* `UMet(Y;R) ≠ ∅` for clause `(U2)` is now stated, via the factorization
  paper's Proposition 2.3. ✓ (The Lean layer derives it without Proposition
  2.3; §7.)

#### `cor:complete-ultrametric-borel-separability` — PASS + EXTERNAL (E2(N1), E4d)

The proof now says explicitly that the construction of 4.6 is repeated only
"through the definition of `m_t`" and that the completeness-preserving extensor
of `thm:ultrametric-isometric-extensor` replaces the component-controlled one.
This is the scope clarification the 2026-08-27 note §2.20 asked for;
resolved. Completeness of `e|_{((A ∖ H) ∪ {z})²}` comes from `r`-separation. The
corollary still depends on E2(N1) and not on E2c′. ✓

### 2.3 Editorial findings (no verdict change)

1. **`cor:discrete-metric-nonborel` hypothesis.** Still stated for
   `|Z| = ℵ₁` although its proof works verbatim for `|Z| ≥ ℵ₁`, the hypothesis
   of `thm:metric-component-nonborel` immediately before it. Carried over from
   the 2026-08-27 note §2.21 item 3.
2. **`lem:one-point-amalgamation` completeness.** The completeness assertions
   are now supported only by citations; a reader cannot tell from the text
   whether the cited Proposition 3.2 and Lemma 2.15 contain them. Either restore
   the short argument or state where the cited sources prove completeness.
3. **`prop:dense-aleph1-nonborel-cantor` proof.** "`S` is a required set"
   leaves all three properties unverified in text. The verification (§2.2) is
   three lines and should be printed.

Minor, not further tracked: `cor:nonseparable-metric-nonborel` and
`cor:nonseparable-ultrametric-nonborel` are now `theorem` environments with
`cor:` labels; the proof of `lem:metric-coding` announces assertion `(A1)`
first but proves `(A2)` first.

---

## 3. Resolution of the 2026-08-27 findings

| 2026-08-27 item | status in the 2026-11-03 source |
|---|---|
| §8 / #113, `cor:metric-space-complete-separability` FIX | **resolved** — preferred repair (§2.2) |
| §2.21 item 1, introduction cites the component theorem for `Met(Z)` | **resolved** — now cites `cor:discrete-metric-nonborel` |
| §2.21 item 2, introduction cites the `BMet` theorem for "`Met(X)` Borel ⇒ separable" | **resolved** — now cites `cor:nonseparable-metric-nonborel` |
| §2.21 item 3, `cor:discrete-metric-nonborel` stated for `= ℵ₁` | **outstanding** (§2.3 item 1) |
| §2.19 item 7, unstated reason for `eq:amalgamated-coding-compatibility` | **resolved** (§2.2) |
| §2.20 scope note, "repeat the construction" in 4.10 | **resolved** (§2.2) |
| §3.2, v1 §2.7 exposition request (compatibility of `m_t`, `z ∈ H`) | **resolved** (§2.1) |
| §2.1 / §4 E3, Koshino "Corollary 1.2" number | **outstanding** — still cited as Corollary 1.2 |
| §4 E6, cite Hausdorff directly rather than Michael–Stone §3.4 | **outstanding** (recommendation) |

The Lean side needs no change:
`separable_of_isCompletelyMetrizableSpace_CPM_MetOn_of_isometricExtensorOn`
already follows the repaired route.

---

## 4. External dependencies

E1, E1c, E2, E3, E4a–d, E5 and E6 are consumed exactly as recorded in the
2026-08-27 note §4, which holds their exact statements and verification
provenance; the 2026-11-03 renderings of `thm:metric-isometric-extensor`
(`(E1)`–`(E4)`, clause `(E4)` conditioned on `X` completely metrizable) and
`thm:ultrametric-isometric-extensor` (`(I1)`–`(I3)`) agree with those records.
In summary:

* **E1** — Ishiki, *An isometric extensor of metrics*, Theorem 1.1:
  `E : Met(A) → Met(X)` and `Ẽ : CPM(A) → CPM(X)` for closed `A`, with
  extension, isometry, `BMet` preservation, `Ẽ(Met(A)) = Ẽ(CPM(A)) ∩ Met(X)`,
  and completeness preservation when `X` is completely metrizable.
* **E1c** — the same paper, Lemma 4.4: `r(x,a) ≤ 4 d(x,a) + 1` for the
  construction with chosen base metrics. Construction data; never a clause of
  E1.
* **E2** — Ishiki, *A factorization of metric spaces*, Theorem 4.7 and (N1):
  isometric `E : UMet(A;R) → UMet(X;R)` for nonempty closed `A` and
  characteristic `R`, with extension, isometry, and completeness preservation
  when `X` is completely metrizable.
* **E3** — Koshino: separable metrizable `X` is σ-compact iff `BMet(X)` is
  completely metrizable.
* **E4** — (a) perfect set theorem for Borel sets (Kechris 13.6); (b) Bernstein
  sets (Kechris 8.24); (c) `[0,1] ≅_B 2^ω` (Srivastava 3.3.13); (d)
  Alexandrov–Lavrentiev, both directions (Kechris 3.11).
* **E5** — Ishiki, interpolation theorem (singleton family, exact distance).
* **E6** — Hausdorff's open-image theorem, via Michael–Stone §3.4.

**E2c′ — re-scoped construction dependency of
`lem:ultrametric-extensor-preserving-component`.** It **replaces E2c**. The
2026-11-03 source consumes, from *A factorization of metric spaces*:

* *Proposition 2.6* (metric quotient): the formula `eq:net-metric-quotient`
  defines a metric on `Y_{/A}`, `p` is continuous, and `p|_{Y ∖ A}` is a
  homeomorphism onto `Y_{/A} ∖ {ϖ_A}`. **Newly cited**; its exact wording has
  not yet been checked against the paper — this note records only the use.
* *Proposition 2.8*: metrizable `X`, nonempty closed `F`, `dim(X ∖ F) = 0`
  ⇒ `X/F` zero-dimensional (as in the 2026-08-27 note §4).
* *Proposition 2.3*: for characteristic `S`, metrizable `X` has
  `UMet(X;S) ≠ ∅` iff `dim X = 0` (as in the 2026-08-27 note §4). Also used
  by `cor:nonseparable-ultrametric-nonborel` for `UMet(Y;R) ≠ ∅`.
* *Formula from the proof of Theorem 4.7*: the max-form extensor. Its
  extensor and isometry properties are verified directly (§2.2 step 6), so no
  further content of that proof is consumed.

No longer consumed: the conditions (D), (SR) of Theorem 2.11 and the proof of
Theorem 3.1. By the audit observation in §2.2, E2c′ is **eliminable**: the
lemma has a proof with no external input. E2c′ is still construction-level
data and must never become a clause of E2.

**Standard facts.** As in the 2026-08-27 note §4: `lem:cpm-complete` and
`lem:ucpm-complete` (Ishiki, *Spaces of metrics are Baire*, Lemma 2.4; both
proved in Lean); `lem:one-point-amalgamation` (cited, completeness half see
§2.2). Still silent and elementary: separated sets are closed and discrete;
the restriction of a complete metric to a closed subspace is complete; a
countable union of countable sets is countable; a topological sum of
completely metrizable spaces is completely metrizable.

---

## 5. Removed claims — must not be reinstated

The 2026-08-27 note §5 remains binding without change. In short: the
superseded analytic/coanalytic draft's "neither analytic nor coanalytic"
claims must not be reintroduced — the `|S| = ℵ₁` "not coanalytic" half is not
a ZFC theorem, and the classical pointclasses are the wrong notion in the
nonseparable ambient. The 2026-11-03 source contains no analytic or
coanalytic statement. `note_by_ishiki_1.pdf`, `note_by_ishiki_2.pdf` and the
standalone older `main.tex` are artifacts of that draft and are not the latest
source.

---

## 6. Dependency graph (printed proofs)

Changes from the 2026-08-27 note §6 only; every other edge is unchanged.

```
borel-separability, E4d → metric-space-complete-separability          [removed]
nonseparable-metric-nonborel, E4d
                        → metric-space-complete-separability          [new]
maximal-separated-set-ultrametric, E2c′
                        → ultrametric-extensor-preserving-component   [new]
ultrametric-coding, one-point-amalgamation, ucpm-complete,
dense-aleph1-nonborel-cantor(co-density),
ultrametric-extensor-preserving-component, Prop 2.3
                        → nonseparable-ultrametric-nonborel           [replaces the E2, E2c edge]
```

`thm:metric-component-nonborel` stays on the critical path; the three
ultrametric discrete theorems stay leaves; co-density of
`prop:dense-aleph1-nonborel-cantor` stays load-bearing for 4.6 and 4.10.
`cor:nonseparable-ultrametric-nonborel` no longer consumes E2 itself — only
the self-contained extensor of 4.5.

---

## 7. Lean correspondence

**Standing constraints, unchanged.** External theorems enter only as explicit
hypotheses, never as axioms; accepted declarations are sorry-free with an
axiom footprint within `propext`/`Classical.choice`/`Quot.sound`; that
evidence lives in the PR and issue trail. The per-declaration record of the
v1-gated statements stays in `notes/borel-preprint-audit.md` §7, and the
received-source additions in the 2026-08-27 note §7.

**Lean file headers.** Each `Ext/` file names its *statement gate*: the
frozen audit note, and section, against which its statements were accepted.
Bare "audit §" references inside a file are to that note. The label-level
correspondence with the current source is §7.1 here.

### 7.1 Statement-level correspondence

Every labelled result of the 2026-11-03 source has a Lean counterpart at
statement level, or enters as an explicit hypothesis, except as noted in §7.2.

| label | 11-03 | Lean (`lean/IshikiConj51/Ext/`) |
|---|---|---|
| `prop:dense-aleph1-nonborel-interval`, `-cantor` | 2.17, 2.18 | `Borel.lean`; `exists_bidense_aleph1_nonBorel_cantor` (avoids E4c) |
| `lem:metric-coding`, `lem:closed-parameter-embedding` | 3.1, 3.2 | `BoundedCoding.lean` (`dExt`, `dExt_isCompatible_iff`, `isClosed_image_phiFull`), `BMetClopen.lean`, `Completeness.lean` |
| `thm:bounded-discrete-nonborel` | 3.3 | `Borel.lean`, `CPM.lean`, `Relabel.lean` |
| `thm:metric-component-nonborel` | 3.4 | `component_not_measurableSet` (`aleph 1 ≤ #Z`) |
| `cor:discrete-metric-nonborel` | 3.5 | `met_not_borel_of_card` (by the pullback route, not via 3.4) |
| `thm:borel-separability` | 3.6 | `separable_of_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn`; the `Met` form is `separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn` |
| `cor:nonseparable-metric-nonborel` | 3.7 | `not_measurableSet_CPMOn_component_of_isComponentControlledExtensorOn`, `not_measurableSet_CPM_MetOn_of_isComponentControlledExtensorOn` (E1, E1c) |
| `cor:metric-space-complete-separability` | 3.8 | `separable_of_isCompletelyMetrizableSpace_CPM_MetOn_of_isometricExtensorOn` |
| `cor:bounded-metric-complete-sigma-compact` | 3.9 | `tfae_isCompletelyMetrizableSpace_iff_sigmaCompactSpace` (E1, E3, E5, E6) |
| `thm:complete-metric-nonborel`, `cor:complete-metric-borel-separability` | 3.10, 3.11 | `CompleteMetric.lean` (under `aleph 1 ≤ #Z`, stronger than printed) |
| `lem:ultrametric-coding` … `thm:ultrametric-component-nonborel` | 4.1–4.4 | `UltraCoding.lean`, `UltraComponent.lean` (`#Z = aleph 1`) |
| `lem:ultrametric-extensor-preserving-component` | 4.5 | **not formalised**; enters as the hypothesis `hEx : … IsUltraComponentControlledExtensorOn …` |
| `cor:nonseparable-ultrametric-nonborel` | 4.6 | `not_measurableSet_UCPMOn_component_of_isUltraComponentControlledExtensorOn`, `not_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn` |
| `thm:ultrametric-borel-separability`, `cor:ultrametric-space-complete-separability` | 4.7, 4.8 | `separable_of_measurableSet_UMetOn_of_isUltraComponentControlledExtensorOn`, `separable_of_isCompletelyMetrizableSpace_UMetOn_of_isUltraComponentControlledExtensorOn`; v1 route in `UltraTransfer.lean` |
| `thm:complete-ultrametric-nonborel`, `cor:complete-ultrametric-borel-separability` | 4.9, 4.10 | `UltraComplete.lean`; `separable_of_{measurableSet,isCompletelyMetrizableSpace}_UCompOn_of_isUltrametrizableSpace` (both claims, with `UComp ≠ ∅`) |
| E1 / E2 / E3 / E4d / E5 / E6 | 2.3, 2.11, 2.2, 2.16 | explicit hypothesis bundles; 2.16's reverse direction is proved (`GDeltaCompletelyMetrizable.lean`) |
| standard lemmas 2.4, 2.8, 2.10, 2.12 (clopen), 2.15 | — | `Amalgam.lean`, `Completeness.lean`, `completeSpace_UCPMOn`, `isClopen_setOf_edist_lt_top` |

### 7.2 Gaps

* **`lem:ultrametric-extensor-preserving-component` (4.5).** The E2c structure
  `IsUltraComponentControlledExtensorOn` and its provider `hEx` quantify over
  exactly 4.5's data (an `R`-valued compatible ultrametric `d`, `a ∈ R ∖ {0}`,
  a nonempty closed discrete `a`-separated `a`-net `A`). Lean's
  `component_control` asks only for `edist … < ⊤`, weaker than `≤ τ`, which
  is all its consumers need. The E2c docstring attributes the hypothesis to
  4.5 and maps each field to the lemma. Discharging it outright is #132: by
  §2.2's audit observation the construction `E′` needs no external input and
  gives `E′(d|_{A²}) = d`.
* **`lem:continuous-pullback-obstruction` (2.14), second assertion** (compact
  `P`, Hausdorff `Z`, injective `f` ⇒ `f(A)` is a closed subspace of `B`
  homeomorphic to `A`). No general Lean declaration; its instances are
  `isClosed_image_phiFull`, `isClosed_image_phiU` and `isClosed_image_psiU`.
  No main theorem consumes it. No action unless a consumer appears.
* **`cor:discrete-metric-nonborel`** — the printed derivation from 3.4 through
  `lem:relative-borel-inheritance` is not formalised; the statement is.
  Nothing depends on the derivation.
