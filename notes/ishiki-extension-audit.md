# Ishiki extension audit

> **Status:** in progress.  
> **Scope:** theorem-by-theorem mathematical audit for Issue #46.  
> **Policy:** a manuscript statement is not accepted merely because it appears in the draft.  Definitions, ambient conventions, and load-bearing external results are checked before Lean work begins.  
> **Re-audit:** §§1–6 were re-derived from scratch in an independent context on 2026-08-12; the verdicts below are that pass's, and superseded verdicts are noted in place.

## 0. Verdict legend

- **PASS** — statement and proof architecture checked at the current level; only routine citation polishing may remain.
- **FIX** — statement is recoverable, but the current proof or formulation needs a concrete correction.
- **BLOCKED** — theorem-level acceptance depends on an unresolved definition or external result.

The Japanese terminology companion is tracked in #48 / draft PR #49.

---

## 1. Descriptive-set-theoretic ambient convention

### Verdict: **BLOCKED — definition must be fixed before Theorem 3.3ff**

The draft §2.3 introduces analytic/coanalytic subsets in the classical setting of a Polish ambient space.  Later statements use phrases such as

```text
BMet(D) is analytic or coanalytic in CPM(D)
Met(X) is analytic or coanalytic in CPM(X)
```

for general metrizable `D,X`, where the pseudometric ambient need not be separable or Polish.

This is not a harmless omission.  Outside Polish spaces, several generalisations of `analytic` occur in the literature.

The obstruction is *not* a failure of closure under continuous inverse images: the classical definition has that closure.  For continuous `f : [0,1] → Y` and `A = g(P)` with `P` Polish and `g` continuous, `f⁻¹(A)` is the projection to `[0,1]` of `{(x,p) ∈ [0,1]×P : f(x)=g(p)}`, which is closed because `Y` is metrizable; hence `f⁻¹(A)` is `Σ¹₁`.

The obstruction is that the classical definition admits only separable analytic sets, and `BMet(D)` is nonseparable, so Theorem 3.3 would hold for trivial reasons.  Explicitly, fix three distinct points `u,v,y₀ ∈ D` and let `A` range over the subsets of `D\{u,v,y₀}`.  Set `d_A(x,y)=2` when `x≠y` and `|{x,y}∩A|=1`, and `d_A(x,y)=1` for the other pairs `x≠y`.  Any symmetric off-diagonal function with values in `[1,2]` satisfies the triangle inequality, so each `d_A` is a bounded metric compatible with the discrete topology.  For `A≠A'` pick `z ∈ A△A'`, say `z ∈ A\A'`: then `|{z,y₀}∩A| = 1` while `|{z,y₀}∩A'| = 0`, so `D_sup(d_A,d_{A'})=1`.  (The reserved point `y₀` is needed: without it `A` and `D\A` give the same metric.)  Hence `BMet(D)` has density `2^{|D|}`.  Composing with the two-point identification `π : D → D\{v}`, `π(v)=u`, the pullbacks `π^*d_A` are bounded pseudometrics that are *not* compatible — they do not separate `u,v` — and they stay `1`-separated, because `π` fixes both `z` and `y₀`.  So the complement is nonseparable too.  Under the classical reading neither `BMet(D)` nor its complement could ever be analytic, and both halves of the theorem would be vacuous.

### Candidate repair

For an arbitrary metrizable ambient space `Y`, explicitly define a subset `A ⊆ Y` to be **Souslin-F / relative analytic** when it is obtained by the Souslin `A`-operation from closed subsets of `Y`; define coanalytic by complement in `Y`.

Advantages for the present proof:

1. in a Polish ambient this agrees with the classical analytic (`Σ¹₁`) notion — every `Σ¹₁` set is the `A`-operation applied to a regular Souslin scheme of closed sets (Kechris, *Classical Descriptive Set Theory*, 25.7, §25.C);
2. continuous inverse images are immediate, because inverse images preserve closed sets and commute with the Souslin operation; they also commute with complementation, so the coanalytic half transfers at the same time;
3. the whole-parameter metric coding then gives a direct pullback contradiction from `[0,1]` or `2^ℕ`, where the classical perfect-set theorems apply;
4. no descriptive-set-theoretic regularity theorem is required for the nonseparable ambient itself.

Terminology varies between sources (`analytic`, `Souslin`, `absolute analytic`, relative analytic), so the manuscript should define the class rather than rely on the name alone.

### Sources consulted

- R. W. Hansell, *On the nonseparable theory of Borel and Souslin sets*, Bull. Amer. Math. Soc. **78** (1972), and the companion Trans. AMS paper (1974): the standard development of Souslin-`F` and `κ`-Souslin sets in nonseparable metric spaces.
- C. A. Rogers and J. E. Jayne, *Analytic Sets* (1980): survey treatment of analytic sets beyond the Polish setting.
- Kechris, *Classical Descriptive Set Theory*, 25.7 / §25.C for the Polish-ambient agreement.
- *Encyclopedia of Mathematics*, “Analytic set” and “Descriptive set theory”: the classical notion is explicitly distinguished from general metric/topological extensions.

The manuscript should also record that Theorem 3.3 needs **only** the two closure properties above.  It needs no separation theorem and no regularity theory for the nonseparable class — which matters, because the nonseparable Souslin-`F` separation results carry completeness and weight hypotheses.

---

## 2. Proposition 2.1 — dense bad parameter set in `[0,1]`

### Verdict: **FIX under CH — BLOCKED for `ℵ₁<𝔠`** (the first pass recorded PASS)

Claim: there is a dense `S ⊆ [0,1]` with `|S|=ℵ₁` that is neither analytic nor coanalytic.

Both branches of the first-pass proof used the perfect-set property for **coanalytic** sets.  That is not a theorem of ZFC: under `V=L` there are uncountable thin (perfect-subset-free) `Π¹₁` sets.  Only the analytic perfect-set theorem (Souslin; Kechris 29.1) is available.

### CH case — corrected proof

Take a Bernstein set `S ⊆ [0,1]`, so `|S| = 𝔠 = ℵ₁`.

- `S` is dense because every nonempty relatively open interval contains a nonempty perfect subset, which must meet `S`.
- `S` is not analytic: it is uncountable, so Kechris 29.1 would give a nonempty perfect subset `K ⊆ S`, whereas the Bernstein condition forces `K\S ≠ ∅`.
- `S` is not coanalytic: otherwise `[0,1]\S` is analytic, and it is uncountable because it too meets every perfect set; Kechris 29.1 then puts a nonempty perfect subset inside `[0,1]\S`, again contradicting the Bernstein condition.

Only the analytic perfect-set theorem is used, so this branch is ZFC-safe.

### non-CH case — refuted; cardinality alone does not repair it

Here `ℵ₁<𝔠`, and the first-pass recipe was: choose a countable dense `Q ⊆ [0,1]` and extend it arbitrarily to `S` with `|S|=ℵ₁`.

**Half of the argument survives.**  `|S|=ℵ₁<𝔠` makes `S` thin, so by Kechris 29.1 an analytic `S` would be countable.  *`S` is not analytic — in ZFC, for every such `S`.*

**The coanalytic half is false as stated.**  There is a largest thin `Π¹₁` set `C₁` (Kechris 1975; independently Guaspari 1973 and Sacks 1976), and in ZFC `|C₁| = |ω₁^L|`.  Every hyperarithmetic real lies in `C₁`, so `C₁` is dense in `[0,1]`.  Hence in any model of `¬CH` with `ω₁^L = ω₁` — `L` extended by `ℵ₂` Cohen reals, or any ccc extension of `L` forcing `MA_{ℵ₁} + 𝔠 = ℵ₂` — the set `S := C₁` is a legitimate output of the recipe (dense, `|C₁| = ℵ₁`, and `Q` may be taken inside it) and **is** coanalytic.  The recipe has counterexamples.

**What a repair must supply.**  Analytic and coanalytic are meant boldface here, so excluding the lightface `C₁` is not enough: `S` must escape `C₁(a)` for every real parameter `a`.  The economical route is the Mansfield–Solovay theorem — a `Σ¹₂(a)` set either is contained in `L[a]` or contains a nonempty perfect subset — which disposes of `Σ¹₁` and `Π¹₁` simultaneously, both being `Σ¹₂`.  Since `|S| = ℵ₁ < 𝔠` already makes `S` thin, the requirement collapses to

```text
(★)  S ⊄ L[a]  for every real a.
```

`(★)` is not free:

- **`cf(𝔠) = ℵ₁` suffices (ZFC).**  Suppose `(★)` fails, so every `S ∈ [ℝ]^{ℵ₁}` lies in some `ℝ ∩ L[a]`.  That family is `⊆`-directed (`L[a],L[b] ⊆ L[a⊕b]`), hence `ω₁`-directed: `ω₁` many members have union of size `ℵ₁`, so a member contains it.  Let `λ` be its cofinality.  A cofinal subfamily covers `ℝ` with sets of size `≤ ℵ₁`, so `λ = 𝔠`.  And `cf(λ) ≥ ℵ₂`: splitting a minimal cofinal `D` into an increasing `ω₁`-chain of non-cofinal pieces `D_i`, pick `z_i` bounded by no member of `D_i`, take an upper bound `w` of `{z_i}`, and any `d ∈ D` above `w` lies in some `D_i`, contradicting the choice of `z_i`.  Hence `cf(𝔠) ≥ ℵ₂`.
- **`non(𝒩) = ℵ₁` or `non(ℳ) = ℵ₁` suffices, without mentioning `C₁`.**  `Σ¹₁` and `Π¹₁` sets are Lebesgue measurable and have the Baire property, and a measurable set of size `ℵ₁ < 𝔠` must be null, since positive measure yields a perfect subset.  So a non-null (resp. non-meagre) set of size `ℵ₁` is neither analytic nor coanalytic.  `MA_{ℵ₁}` pushes both invariants above `ℵ₁`, which already closes this route.
- In the standard models (Cohen, random, `MA`) `(★)` holds by mutual genericity, but those arguments are model-specific.

Each bullet produces a set of size `ℵ₁`, not yet a dense one; adjoining a countable dense `Q ⊆ [0,1]` fixes that without cost.  The size stays `ℵ₁`, and `(★)`, non-nullity and non-meagreness are all inherited by supersets, so the exclusion argument applies verbatim to `S ∪ Q`.

**No ZFC proof of `(★)` in general was obtained; treat it as open until settled.**  Until it is, the proposition should either carry an explicit hypothesis in the `ℵ₁<𝔠` branch, or Theorem 3.3 should be stated in the asymmetric ZFC-safe form recorded in §6.

### Citations settled by this pass

- perfect-set theorem for analytic sets: Kechris, *Classical Descriptive Set Theory*, **29.1**;
- largest thin `Π¹₁` set, and `|C₁| = |ω₁^L|` in ZFC: Kechris, *The theory of countable analytical sets*, Trans. Amer. Math. Soc. **202** (1975); Guaspari (1973); Sacks (1976);
- Mansfield–Solovay: a `Σ¹₂(a)` set is contained in `L[a]` or contains a perfect subset.

Still to be checked against primary sources: textbook numbers for the Bernstein construction, for measurability and the Baire property of `Σ¹₁`/`Π¹₁`, for Mansfield–Solovay, and for `C₁`.  There is no perfect-set theorem for coanalytic sets to cite.

---

## 3. Proposition 2.2 — Cantor-space parameter set

### Verdict: **FIX**

The current proof says the result follows from Proposition 2.1 because `[0,1]` and `2^ℕ` are Borel isomorphic.  This does not preserve the required **density**: a Borel isomorphism preserves the Borel structure, not the topology.

### Corrected proof — transfer along the binary expansion

Repeating the Bernstein construction inside `2^ℕ` would work under CH but would duplicate the `ℵ₁<𝔠` defect of §2 in a second place.  Transfer instead.

Let `φ : 2^ℕ → [0,1]`, `φ(x) = Σ_n x_n 2^{-(n+1)}`.  It is continuous, surjective and at most `2`-to-`1`, and the image of a nonempty basic clopen set `[s]` is a nondegenerate dyadic interval.  For `S` as in Proposition 2.1 put `T := φ⁻¹(S)`.

- `T` is dense: `φ([s])` has nonempty interior, which meets the dense set `S`.
- `|T| = ℵ₁`, because `φ` is surjective and at most `2`-to-`1`.
- `T` is not analytic: otherwise `φ(T) = S` would be analytic.
- `T` is not coanalytic: otherwise `2^ℕ\T = φ⁻¹([0,1]\S)` is analytic, hence so is its image `[0,1]\S`, making `S` coanalytic.

### Outcome

The proposition statement survives unchanged; only the proof is replaced.  The transfer keeps Proposition 2.2 a genuine corollary of Proposition 2.1, so the pair has a single point of repair — which matters while the `ℵ₁<𝔠` branch of §2 is unresolved.  Under CH the corollary is ZFC-safe; for `ℵ₁<𝔠` it inherits exactly the status of Proposition 2.1.

---

## 4. Lemma 3.1 — Archimedean bounded metric coding

### Verdict: **PASS**

For

```text
l_n(α,t) = |t-w_α| + 2^{-n},
```

define `d_t` by the draft's table: anchor distance `1+t`, star distances `l_n` / `l_n+l_m`, and cross-block distance `4`.

### Metricity and boundedness

For `t,w_α∈[0,1]`,

```text
0 < l_n(α,t) ≤ 2.
```

Hence every star has diameter at most `4`.  The restriction to a star is the tree metric with centre `b_α` and edge lengths `l_n`.  The anchor block has diameter at most `2`.

Distinct blocks are placed at distance `4`.  For a mixed triple the only nontrivial instance is `x,y` in one block and `z` in another, where `d_t(x,y) ≤ d_t(x,z)+d_t(z,y) = 8` is what has to hold: the condition is `diam(block) ≤ 2·4`, and the bound `diam ≤ 4` gives it with room to spare.

Thus every `d_t` is a metric and `d_t(X²)⊆[0,4]`.

### Compatibility iff `t∉S`

If `t∉S`, then

```text
inf_{v≠c_{α,n}} d_t(c_{α,n},v) ≥ l_n(α,t) ≥ 2^{-n} > 0,
inf_{v≠b_α} d_t(b_α,v) = |t-w_α| > 0.
```

Anchors and cross-block isolation are immediate.  Hence the induced topology is discrete.

If `t=w_β∈S`, then

```text
d_t(b_β,c_{β,n}) = 2^{-n} → 0,
```

so `b_β` is not isolated.

Therefore

```text
d_t ∈ BMet(X)  ⇔  t ∈ [0,1]\S.
```

Note that for `t = w_β ∈ S` the function `d_t` is still a genuine metric — all its off-diagonal values are positive — and only compatibility fails.  This is what makes the whole-parameter map of §5 well defined on all of `[0,1]`.

---

## 5. Lemma 3.2 — parameter embedding

### Verdict: **PASS**

For `s,t∈[0,1]`, anchor evaluation gives

```text
|s-t| ≤ D_X(d_s,d_t).
```

The map `t↦|t-w_α|+2^{-n}` is 1-Lipschitz.  Therefore star centre/spoke distances vary by at most `|s-t|`, spoke/spoke distances by at most `2|s-t|`, and cross-block distances are constant.  Hence

```text
D_X(d_s,d_t) ≤ 2|s-t|.
```

The restricted map

```text
Φ : [0,1]\S → BMet(X),  t↦d_t
```

is bi-Lipschitz.

### Closed image

If `d_{t_k}→d∈BMet(X)`, evaluation at the anchor yields

```text
t_k → t := d(p,q)-1 ∈ [0,1].
```

The limit parameter lies in `[0,1]` because `[0,1]` is closed.  The upper Lipschitz estimate gives `d_{t_k}→d_t`, so uniqueness of limits yields `d=d_t`.  Since `d` is compatible with the discrete topology, Lemma 3.1 forces `t∉S`.  Thus the image is closed in `BMet(X)` — closedness relative to `BMet(X)`, which is what the argument establishes and all that Theorem 3.3 uses.

### Recommended stronger formulation

Keep the full parameter map

```text
Φ_full : [0,1] → BCPM(X),  t↦d_t.
```

It is 2-Lipschitz and satisfies the exact identity

```text
Φ_full⁻¹(BMet(X)) = [0,1]\S.
```

This pullback identity should be the load-bearing descriptive-set-theoretic statement for Theorem 3.3.

---

## 6. Theorem 3.3 — discrete descriptive obstruction

### Verdict: **BLOCKED — by the ambient convention (§1), and for `ℵ₁<𝔠` also by Proposition 2.1 (§2)** (the first pass recorded "blocked only by the ambient convention")

Once §1 is repaired with a pointclass on arbitrary metrizable ambients that is preserved by continuous inverse images and agrees with classical `Σ¹₁/Π¹₁` on `[0,1]`, the theorem follows immediately from

```text
Φ_full⁻¹(BMet(X)) = [0,1]\S.
```

Indeed `[0,1]\S` is neither analytic nor coanalytic because `S` has neither property and the two classes are dual in the Polish ambient `[0,1]`.

This pullback proof is preferable to the draft's relatively-closed-copy argument because it exposes exactly which pointclass closure property is used and avoids ambient-dependent interpretation of a homeomorphic copy.

### What survives in ZFC

The pullback splits the conclusion into two halves that need different inputs:

```text
BMet(X) analytic    ⇒  [0,1]\S analytic    ⇒  S coanalytic
BMet(X) coanalytic  ⇒  [0,1]\S coanalytic  ⇒  S analytic
```

Under CH both halves hold in ZFC, via the corrected Bernstein argument of §2.

Under `ℵ₁<𝔠` the two halves separate.  `S` is not analytic for cardinality reasons alone, so **`BMet(X)` is not coanalytic** in ZFC, for any dense `S` of size `ℵ₁`.  The other half — `BMet(X)` is not analytic — is exactly what `(★)` of §2 would buy.  If `(★)` stays unresolved, this asymmetric statement is the strongest unconditional form of the theorem.

No independent defect has been found in the discrete metric construction: §§4–5 were re-derived from scratch and confirmed.

---

## 7. Next audit targets

1. Fix/reference the nonseparable ambient pointclass convention.
2. Settle `(★)` of §2, or decide which weaker form of Proposition 2.1 / Theorem 3.3 the manuscript should carry for `ℵ₁<𝔠`.  This is a question to put to the authors, not a citation gap.
3. Theorem 3.4 — finite-sup-distance component construction.
4. Theorem 3.5 / Corollary 3.6 — passage to a general nonseparable metrizable space via Ishiki's extensor.
5. Complete-metric branch.
6. Non-Archimedean branch.
7. Koshino consequence.

Theorem-level Lean work (#47) remains blocked until the convention in §1 is fixed and the `ℵ₁<𝔠` branch of §2 is decided.  The Archimedean coding of §§4–5 is confirmed and is a safe formalisation target in the meantime.

---

## 8. Mathlib inventory (Lean 4.32.2, mathlib4 tag `v4.32.2`)

Deliverable of #46/#47.  Every declaration below was confirmed to exist by grep in `lean/.lake/packages/mathlib`; every gap is the absence of any such declaration, not a naming guess.

### 8.1 Available

| need | declaration | ambient hypotheses |
| --- | --- | --- |
| analytic set | `MeasureTheory.AnalyticSet` (`MeasureTheory/Constructions/Polish/Basic.lean`) | `[TopologicalSpace α]`; defined as `s = ∅ ∨ s` is a continuous image of `ℕ → ℕ` |
| usual characterisation | `MeasureTheory.analyticSet_iff_exists_polishSpace_range` | — |
| closed ⇒ analytic | `IsClosed.analyticSet` | `[PolishSpace α]` |
| Borel ⇒ analytic | `MeasurableSet.analyticSet`, `MeasurableSet.analyticSet_image` | `[PolishSpace α] [BorelSpace α]` |
| countable unions / intersections | `MeasureTheory.AnalyticSet.iUnion`, `.iInter` | `[Countable ι]`; `iInter` also `[Nonempty ι] [T2Space α]` |
| continuous images | `MeasureTheory.AnalyticSet.image_of_continuous`, `.image_of_continuousOn` | — |
| **continuous preimages** | `MeasureTheory.AnalyticSet.preimage` | `[PolishSpace X] [T2Space Y]` |
| Suslin's theorem | `MeasureTheory.AnalyticSet.measurableSet_of_compl` | `[T2Space α] [OpensMeasurableSpace α]` |
| Lusin–Souslin | `MeasureTheory.measurableSet_range_of_continuous_injective`, `MeasurableSet.image_of_continuousOn_injOn`, `MeasurableSet.image_of_measurable_injOn` | Polish / standard Borel |
| perfect sets | `Perfect`, `Preperfect`, `PerfectSpace` (`Topology/Perfect.lean`) | — |
| PSP for **closed** sets | `exists_perfect_nonempty_of_isClosed_of_not_countable` | `[SecondCountableTopology α]` |
| Cantor–Bendixson | `exists_countable_union_perfect_of_isClosed` | `[SecondCountableTopology α]` |
| perfect ⇒ cardinality `𝔠` | `Perfect.exists_nat_bool_injection`, `IsClosed.exists_nat_bool_injection_of_not_countable` | `[CompleteSpace α]` / `[PolishSpace α]` |
| Cantor space and schemes | `CantorScheme.inducedMap`, `.VanishingDiam`, `.ClosureAntitone`, `CantorScheme.Disjoint.map_injective`, `ClosureAntitone.map_of_vanishingDiam`; `PiNat.cylinder`, `PiNat.res`, `PiNat.firstDiff` | — |
| cardinal arithmetic | `Cardinal.mk_real : #ℝ = 𝔠`, `Cardinal.aleph_one_le_continuum` | — |
| completeness, closed subspaces | `IsClosed.isComplete`, `IsClosed.completeSpace_coe`, `IsComplete.isClosed`, `IsClosed.isCompletelyMetrizableSpace` | `[CompleteSpace α]` where applicable |
| ultrametric | `IsUltrametricDist` (`Topology/MetricSpace/Ultra/Basic.lean`) | class on `[Dist X]` |
| bounded pseudometrics, sup distance | repo-side `IshikiExt.BddPMet` (#51 / PR #52) — no Mathlib equivalent | `IsMetricOn`, `IsCompatible`, `BMet` reused from `Conj51/MetD.lean` |

Two observations worth carrying into Layer 2.

`AnalyticSet` is precisely the classical convention that §1 rejects: a continuous image of a Polish space, hence always separable.  Formalising Theorem 3.3 against it would reproduce the vacuity of §1 inside Lean.

`AnalyticSet.preimage` is nevertheless the exact closure property §1 asks for, and its Mathlib proof — the equaliser `{x : f x.1 = g x.2}` is closed, then project — is the same argument §1 uses to show the classical convention *does* have that closure.  So the closure principle is not what is missing; a non-vacuous pointclass is.

### 8.2 Gaps, with impact

| gap | status | impact |
| --- | --- | --- |
| PSP for analytic sets (Kechris 29.1) | absent; only the closed-set version exists | §2 depends on it in both branches.  A from-scratch proof (Souslin scheme representation, then the closed-set machinery) is an independent and substantial sub-issue — it should not be bundled into a Theorem 3.3 issue |
| coanalytic pointclass | absent as a named class | defining it as a complement is trivial, but no `Π¹₁`-specific lemma exists to build on |
| Souslin `𝒜`-operation | absent as an operation | `CantorScheme` already supplies the indexing infrastructure — schemes `List β → Set α`, `PiNat.res`, and intersection along a branch in `CantorScheme.inducedMap` — so the §1 Souslin-`F` convention is a definition plus its closure lemmas, not a theory from scratch |
| Bernstein set | absent (`Bernstein` in Mathlib is the approximation polynomial) | the CH branch of §2 needs a transfinite-recursion construction written from scratch |
| thin `Π¹₁` sets, `C₁`, Mansfield–Solovay, `L[a]` | absent; the constructible hierarchy is not in Mathlib at all | `(★)` and the whole `ℵ₁<𝔠` analysis of §2 are out of formalisation reach for now; Layer 2 must treat the existence of a bad set as a hypothesis, not a lemma |
| cardinal invariants (`non(𝒩)`, `non(ℳ)`) | absent | the elementary `(★)` route of §2 is likewise not formalisable today |
| descriptive set theory in nonseparable spaces | absent | there is no ambient theory to instantiate §1 against; the pointclass must be axiomatised as a hypothesis |

The practical consequence for #47 Layer 2 is the shape the Layer 1 handoff already anticipated: assume the pointclass closure principle as an explicit named hypothesis rather than a custom axiom, feed it `preimage_BMet_phiFull`, and keep the existence of the bad parameter set as a further hypothesis until §2 is resolved.
