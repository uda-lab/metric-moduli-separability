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

---

## 9. Theorem 3.4 — every finite-distance component of `Met(D)`

### Verdict: **PASS-INDEPENDENT**, at the same conditional strength as Theorem 3.3

The construction and the pullback identity are unconditional.  The descriptive-set-theoretic conclusion inherits both global conditions of §6: it needs the §1 ambient convention, and only its "not coanalytic" half is ZFC-safe (the "not analytic" half needs CH or `(★)`).

**Method note for §§9–12.** The joint manuscript was not available to this pass.  Each statement below was identified from the item specification of Issue #46 and then proved from scratch; the constructions are this audit's own and need not match the manuscript's.  A PASS-INDEPENDENT verdict therefore certifies *the theorem*, not the manuscript's proof text.  What remains once the draft is in hand is statement-level reconciliation: confirming that each verdict is about the manuscript's actual claim, under its definitions and conventions, and recording any gap where the manuscript's argument and the derivation below disagree.  Revising the manuscript's text is not this project's role (#46: mathematical cross-checking and Lean verification).

Throughout, `D` is discrete with `|D| = ℵ₁`.  Every function on `D²` is continuous, so `CPM(D)` is the set of all pseudometrics on `D`, and `BCPM(D)` the bounded ones.  Following Ishiki §2.2, `d ∼ e` iff `D_D(d,e) < ∞`, `M_{<∞}(D) = Met(D)/∼`, and each class `C(ρ)` is a clopen path-connected component of `Met(D)`.

**Claim.** For every `ρ ∈ Met(D)`, the component `C(ρ)` is neither analytic nor coanalytic in `CPM(D)`.

### 9.1 The uncountable bounded ball

Fix `x₀ ∈ D`.  Then `D = ⋃_{n∈ℕ} B_ρ(x₀,n)`, and a countable union of countable sets is countable, so some ball `B := B_ρ(x₀,N)` is uncountable, hence `|B| = ℵ₁`, with `diam_ρ B ≤ 2N`.

This is the only place where the component is used: it supplies an `ℵ₁`-sized piece on which `ρ` is bounded, so that a bounded coding perturbation stays at finite sup-distance from `ρ`.

### 9.2 One-point amalgamation

Deleting one point from `B` if necessary, assume `B ≠ D`; this costs nothing, `|B|` still being `ℵ₁`.  Choose `o ∈ B` and put

```text
D₁ := B,   D₀ := (D \ B) ∪ {o},   D₀ ∩ D₁ = {o},   D₀ ∪ D₁ = D,   D₀\{o} ≠ ∅.
```

Since `|D₁| = ℵ₁ = ℵ₁·ℵ₀`, partition `D₁ = {o,q} ⊔ ⨆_{α<ω₁} T_α` with `T_α = {b_α} ∪ {c_{α,n} : n∈ℕ}`, and let `d_t` be the coding metric of §4 on `D₁` with anchor pair `(o,q)`, `d_t(o,q) = 1+t`.

Define `m_t` on `D` by

```text
m_t|_{D₀²} = ρ,   m_t|_{D₁²} = d_t,
m_t(x,y) = ρ(x,o) + d_t(o,y)   for x ∈ D₀\{o}, y ∈ D₁\{o}.
```

This is the one-point amalgamation (wedge) of `(D₀,ρ)` and `(D₁,d_t)` at `o`.  It is a metric: positivity of the cross values is `ρ(x,o) > 0`, and each triangle inequality reduces to one inside a piece after inserting `o`, e.g. for `x,x' ∈ D₀` and `y ∈ D₁\{o}`,

```text
m_t(x,x') = ρ(x,x') ≤ ρ(x,o) + ρ(o,x') ≤ m_t(x,y) + m_t(y,x'),
m_t(x,y)  = ρ(x,o) + d_t(o,y) ≤ ρ(x,x') + ρ(x',o) + d_t(o,y) = m_t(x,x') + m_t(x',y),
```

and symmetrically with the roles of the pieces exchanged.  No boundedness is needed for this step; `ρ` may be unbounded on `D₀`.

### 9.3 Compatibility iff `t ∉ S`

Cross-distances are bounded below by `ε := inf_{x∈D₀\{o}} ρ(x,o) > 0` (`o` is `ρ`-isolated) and by `inf_{y∈D₁\{o}} d_t(o,y) = min(1+t,4) ≥ 1`.  Hence a point of `D₀\{o}` is `m_t`-isolated iff it is `ρ`-isolated in `D₀`, a point of `D₁\{o}` is `m_t`-isolated iff it is `d_t`-isolated in `D₁`, and `o` is always isolated.  With §4,

```text
m_t ∈ Met(D)  ⇔  t ∈ [0,1]\S,
```

and `m_t` is a genuine metric for every `t ∈ [0,1]`, so `Ψ : t ↦ m_t` is defined on all of `[0,1]`.

### 9.4 `m_t` stays at finite sup-distance from `ρ`, for every `t`

On `D₀²` the two functions agree.  On `D₁²`, `d_t ≤ 4` and `ρ ≤ 2N`, so `|m_t-ρ| ≤ max(4,2N)`.  Across, for `x ∈ D₀\{o}`, `y ∈ D₁\{o}`,

```text
|m_t(x,y) - ρ(x,y)| ≤ |ρ(x,o) - ρ(x,y)| + d_t(o,y) ≤ ρ(o,y) + 4 ≤ 2N + 4.
```

Hence `D_D(m_t,ρ) ≤ 2N+4 < ∞` **uniformly in `t`**, including `t ∈ S` (for such `t`, `m_t` is not in the component, being incompatible — it is merely at finite sup-distance from `ρ`).  So the finite-distance condition is never the obstruction; compatibility is.

### 9.5 Exact whole-parameter pullback

Anchor evaluation gives `|m_t(o,q) - m_s(o,q)| = |t-s|`; every entry of `m_t` is `2`-Lipschitz in `t` (§5, and the cross values through `d_t(o,·)`).  So

```text
|s-t| ≤ D_D(m_s,m_t) ≤ 2|s-t|,
```

`Ψ : [0,1] → CPM(D)` is a bi-Lipschitz embedding, and by 9.3–9.4

```text
Ψ⁻¹(C(ρ)) = Ψ⁻¹(Met(D)) = [0,1] \ S.
```

Under the §1 convention, a pointclass closed under continuous preimages therefore transports any classification of `C(ρ)` to `[0,1]\S`, and §2 forbids it.  The split of §6 applies verbatim: **in ZFC, `C(ρ)` is not coanalytic**, for every `ρ`; "not analytic" needs CH or `(★)`.

### 9.6 Consequences and observations

- `BMet(D)` is *one* component: two bounded metrics are automatically at finite sup-distance.  So Theorem 3.3 is the case `ρ` bounded of Theorem 3.4, and no separate argument is needed for it.
- The same map gives `Ψ⁻¹(Met(D)) = [0,1]\S`, so the unbounded space `Met(D)` is covered by the identical pullback — Theorem 3.4 subsumes both the bounded and the global discrete statement.
- **Density of `S` is not used** anywhere in §§4–5 or §9.  The coding needs only an injective `ℵ₁`-enumeration `{w_α}` of `S`.  Density is a property of the parameter set that the descriptive-set-theoretic argument never consumes; if the manuscript carries it into Theorems 3.3/3.4 it is decorative there.  §13.2 reaches the same conclusion for the non-Archimedean coding, so density is unused on both tracks — which makes it a question about the statement of Proposition 2.1/2.2 rather than about these proofs (§14 item 8).

---

## 10. Theorem 3.5 / Corollary 3.6 — transfer to a general metrizable space

### Verdict: **PASS-INDEPENDENT**, with the closed-image argument replaced by an exact pullback

Conditional in the same two ways as §§6 and 9: the §1 convention is required, and the ZFC-safe half is "not coanalytic".

### 10.1 Closed discrete subsets of a non-separable metrizable space

**Lemma.** Every non-separable metrizable `X` contains a closed discrete `D ⊆ X` with `|D| = ℵ₁`.

Fix a compatible metric `w` and, for each `n ≥ 1`, a maximal `1/n`-separated `A_n ⊆ X` (Zorn).  If every `A_n` were countable, `⋃_n A_n` would be a countable dense set: maximality puts every `x` within `1/n` of `A_n`.  So some `A_N` is uncountable; take `D ⊆ A_N` with `|D| = ℵ₁`.

Any `E ⊆ A_N` is closed and discrete: the ball `B_w(x,1/(3N))` meets `A_N` in at most one point, so if `x ∈ cl(E)` then all sufficiently small balls at `x` meet `E` in that same single point, forcing `x ∈ E`; the same ball witnesses discreteness.

### 10.2 The external input, at the level of its exact wording

Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030v4, **Theorem 1.1** (verbatim structure): let `X` be metrizable and `A` a closed subset.  Then there is `E : Met(A) → Met(X)` with

1. `E(d)|_{A²} = d` for every `d ∈ Met(A)`;
2. `D_A(d,e) = D_X(E(d),E(e))` for all `d,e ∈ Met(A)` (isometric embedding, extended-valued sup metrics);
3. `E(BMet(A)) ⊆ BMet(X)`;
4. `E(Comp(A)) ⊆ Comp(X)` — **see §11.3: this clause needs the hypothesis that `X` is completely metrizable**;

and furthermore an isometric extensor `Ẽ : CPM(A) → CPM(X)` of pseudometrics with `Ẽ|_{Met(A)} = E` and

```text
E(Met(A)) = Ẽ(CPM(A)) ∩ Met(X),
```

so that `E(Met(A))` is closed in `Met(X)`.

Two facts from the paper's proof of the "furthermore" part are used below and are worth recording, because the theorem statement does not display them: `Ẽ` is obtained by extending `E` along the density of `Met(A)` in `CPM(A)` (Ishiki, *Spaces of metrics are Baire*, arXiv:2402.04565, Theorem 1.3: `Met(Z)` is comeager, hence dense, in `CPM(Z)`) into the complete space `CPM(X)`; and `Ẽ` is again an extensor, `Ẽ(ψ)|_{A²} = ψ` for all `ψ ∈ CPM(A)`.  Both are used explicitly in the paper's own derivation of the displayed equality.

### 10.3 Restriction is the wrong map

`R̃ : CPM(X) → CPM(A)`, `d ↦ d|_{A²}`, is well defined and `1`-Lipschitz, hence continuous, and `R := R̃|_{Met(X)}` maps into `Met(A)` because `A` carries the subspace topology.  By Theorem 1.1(1), `R̃ ∘ Ẽ = id_{CPM(A)}` and `R ∘ E = id_{Met(A)}`, so `Ẽ` is a section and `Ẽ∘R̃` is an idempotent retraction of `CPM(X)` onto the closed set `Ẽ(CPM(A))`.

But `R̃⁻¹(Met(A)) ⊇ Met(X)` with the inclusion proper as soon as `A ⊊ X`: collapsing a point of `X\A` onto `A` gives a continuous pseudometric on `X` that restricts to a compatible metric on `A` and is not a metric on `X`.  So the obvious continuous map does **not** pull the classification back, and the transfer has to run along `Ẽ`, in the direction opposite to restriction.  This is the structural reason the extensor theorem is load-bearing rather than convenient.

### 10.4 The exact pullback identities

**(a) `Ẽ⁻¹(Met(X)) = Met(A)`.**  `⊇` is `Ẽ|_{Met(A)} = E`.  For `⊆`, let `ψ ∈ CPM(A)` with `Ẽ(ψ) ∈ Met(X)`.  Then `Ẽ(ψ) ∈ Ẽ(CPM(A)) ∩ Met(X) = E(Met(A))`, so `Ẽ(ψ) = E(φ) = Ẽ(φ)` for some `φ ∈ Met(A)`; `Ẽ` is isometric, hence injective, so `ψ = φ ∈ Met(A)`.  (Equivalently and more directly: `ψ = Ẽ(ψ)|_{A²}` is the restriction of a compatible metric on `X` to the closed subspace `A`.)

**(b) `Ẽ⁻¹(BCPM(X)) = BCPM(A)` and `Ẽ⁻¹(BMet(X)) = BMet(A)`.**  Let `0` be the zero pseudometric on `A`.  Boundedness of `ψ` is `D_A(ψ,0) < ∞`, so by isometry `ψ` is bounded iff `D_X(Ẽψ, Ẽ0) < ∞`.  Pick any `d₀ ∈ BMet(A)`; by Theorem 1.1(3) `Ẽ(d₀) = E(d₀)` is bounded, and `D_X(Ẽ0, Ẽd₀) = D_A(0,d₀) < ∞`, so `Ẽ(0)` is bounded.  Hence `ψ` bounded ⇔ `Ẽψ` bounded, and (b) follows from (a).

Clause (3) is the one clause of Theorem 1.1 that (b) — hence the Koshino corollary of §12 — genuinely consumes, so its support was checked: Ishiki's Lemma 4.4 gives `E(d)(x,y) ≤ 4w(x,y) + 1` for `x ∈ X`, `y ∈ A`, hence `E(d)` bounded whenever the auxiliary `w ∈ Met(X)` extending the component representative is bounded, and for a bounded component one may take `w` bounded by replacing it with `min(w, sup m)`, which is still compatible and still restricts to `m`.

Both identities are exact, hold on the whole of `CPM(A)`, and use no property of `A` beyond closedness.

### 10.5 The theorem

**Theorem.** Let `X` be metrizable and non-separable.  Then `Met(X)` is neither analytic nor coanalytic in `CPM(X)`, and `BMet(X)` is neither analytic nor coanalytic in `BCPM(X)`.  Equivalently (Theorem 3.5): if `Met(X)` is analytic or coanalytic in `CPM(X)`, then `X` is separable; likewise for `BMet(X)` in `BCPM(X)`.

*Proof.*  Take `D ⊆ X` closed discrete with `|D| = ℵ₁` (10.1) and `Ẽ` for `A = D` (10.2).  The composite

```text
Λ := Ẽ ∘ Ψ : [0,1] → CPM(X)
```

is continuous (`Ψ` is `2`-Lipschitz, `Ẽ` isometric), and by 9.5 and 10.4(a)

```text
Λ⁻¹(Met(X)) = Ψ⁻¹(Ẽ⁻¹(Met(X))) = Ψ⁻¹(Met(D)) = [0,1]\S.
```

Under the §1 convention the classes are closed under continuous preimages and under complementation-in-the-ambient, so a classification of `Met(X)` would classify `[0,1]\S` in `[0,1]`, contradicting §2.  For the bounded statement use `Φ_full` of §5 (whose values are bounded) and 10.4(b) in place of (a). ∎

As in §6 and §9.5, the ZFC-safe half is **"not coanalytic"**; the analytic half inherits `(★)`.

### 10.6 What the transfer does and does not give

- The component refinement transfers, but which component it reaches depends on the family used.  Running `Ẽ ∘ Ψ` for `Ψ` built from `ρ ∈ Met(D)` (§9): `E(m_t)` is at sup-distance `≤ 2N+4` from `E(ρ)` by isometry, so the family lands in `C(E(ρ))` and `(Ẽ∘Ψ)⁻¹(C(E(ρ))) = [0,1]\S`.  Hence **`C(E(ρ))` is neither analytic nor coanalytic, for every `ρ ∈ Met(D)`**.  Running `Ẽ ∘ Φ_full` instead: `Φ_full` is bounded, and `{d ∈ CPM(X) : D_X(d, Ẽ(0)) < ∞}` — the finite-distance class taken in the *ambient*, since `Ẽ(0)` is a pseudometric and not a member of `Met(X)` — equals `BCPM(X)` because `Ẽ(0)` is bounded (10.4(b)), so the component reached is `BMet(X)`.  The two agree exactly when `ρ` is bounded.  There is no argument here for *every* component of `Met(X)`: only those of the form `C(E(ρ))` are covered, and components disjoint from `Ẽ(CPM(D))` are untouched.
- No converse is available and none should be claimed.  Separability of `X` does not make `CPM(X)` separable (already `C_b(ℝ)` is not), so the classical machinery does not return, and Koshino's theorem ties the complexity of `AM(X)` to the absolute Borel class of `X`, which is unbounded among separable metrizable `X`.  Corollary 3.6 must be read as a one-way implication.

### 10.7 The closed-image argument, made concrete on the `X` side (not load-bearing)

If the manuscript keeps its Appendix A route, the anchor read-back template of §5 does reproduce on `X`, as follows.  The whole family must be carried by `Ẽ`, not by `E`, since `E(d_t)` is undefined for `t ∈ S`.  The anchor pair `p,q` lies in `D`, so by the extensor property `Ẽ(d_t)(p,q) = d_t(p,q) = 1+t`: the parameter is still readable off the extended pseudometric.  If `Ẽ(d_{t_k}) → m ∈ Met(X)` with `t_k ∉ S`, then `t_k → t := m(p,q)-1 ∈ [0,1]`; `Ẽ` is continuous and `d_{t_k} → d_t` by §5, so `m = Ẽ(d_t)`; then 10.4(a) gives `d_t ∈ Met(D)`, i.e. `t ∉ S`, and `m = E(d_t)` is in the family.  So `{E(d_t) : t ∉ S}` is closed in `Met(X)` and bi-Lipschitz to `[0,1]\S`.

This is genuinely a *closed-image* statement and is what one needs for complete-metrizability consequences by the classical route (§12.3).  What it does **not** do by itself is transfer an ambient pointclass: a relatively closed homeomorphic copy of `Met(D)` inside `Met(X)` carries no classification back to `CPM(D)`, because the homeomorphism of the copies is not induced by any map of the ambients.  The pullback of 10.4 supplies exactly the missing ambient-level map, which is why §§9–10 are stated through it.

---

## 11. Theorems 3.7 / 3.8 — the complete-metric branch

### Verdict: **FIX** — the general-space statement needs `X` completely metrizable; the discrete statement is **PASS-INDEPENDENT**

As in §§9–10, the pointclass conclusions are conditional on §1 and, in their "not analytic" half, on §2.

### 11.1 The coding metrics are complete

Let `t ∉ S`.  In `d_t` (§4) distinct blocks are `4` apart, and inside the block `T_α` every two distinct points are at distance at least `|t-w_α| > 0` (`d_t(b_α,c_{α,n}) = |t-w_α| + 2^{-n}`, `d_t(c_{α,n},c_{α,m}) ≥ 2|t-w_α|`).  A `d_t`-Cauchy sequence therefore lies eventually in a single block and, that block being uniformly discrete, is eventually constant.  So `d_t` is complete.  Note the gaps `|t-w_α|` are not uniform over `α` — `S` accumulates at `t` whenever `S` is dense — and completeness does not need them to be: the block decomposition localises every Cauchy sequence first.

`d_t` is in fact complete for **every** `t ∈ [0,1]`, not only off `S`.  For `t = w_β ∈ S` the block `T_β` is no longer uniformly discrete, but the sequence `(c_{β,n})` that witnesses this converges — `d_t(b_β,c_{β,n}) = 2^{-n} → 0` — so nothing escapes: a Cauchy sequence in `T_β` is eventually constant or converges to `b_β`, and the other blocks are unchanged.  Completeness therefore does not detect `S` at all; compatibility does.  This matches the non-Archimedean track, where the coding is likewise complete at every parameter and no separate complete construction is needed.

Since `d_t ∉ Met(D)` for `t ∈ S`,

```text
Φ_full⁻¹(Comp(D)) = [0,1]\S,
```

so **Theorem 3.7 for `Comp(D)` follows from the same coding, with no new construction**.

### 11.2 One-point amalgamation preserves completeness

In §9.2 take `ρ ∈ Comp(D)`.  The Archimedean amalgamation is additive through the basepoint, `m_t(x,y) = ρ(x,o) + d_t(o,y)`; it restricts to `ρ` and to `d_t` isometrically, which is what the argument needs (the non-Archimedean track's `max` amalgamation plays the same role there).  Cross-distances in `m_t` are `≥ ε > 0` (9.3), so an `m_t`-Cauchy sequence is eventually inside `D₀` or inside `D₁`.  There it is `ρ`-Cauchy or `d_t`-Cauchy; `D₀` is closed in the discrete space `D` so `ρ|_{D₀}` is complete, and `d_t` is complete by 11.1.  Hence `m_t` is complete for every `t ∈ [0,1]`, so `m_t ∈ Comp(D)` exactly when it is compatible, i.e. for `t ∉ S`, and

```text
Ψ⁻¹({d ∈ Comp(D) : D_D(d,ρ) < ∞}) = [0,1]\S     for every ρ ∈ Comp(D).
```

### 11.3 Erratum in the external input: Theorem 1.1(4)

**Theorem 1.1(4) of arXiv:2407.03030v4 is stated without hypothesis and is false as printed.**  Take `A = {a}` a one-point closed subspace of `X = ℚ`.  Then `Comp(A) = Met(A) ≠ ∅` while `Comp(ℚ) = ∅`, so `E(Comp(A)) ⊆ Comp(X)` fails for every map `E`.

The paper's own proof supplies the missing hypothesis: clause (4) is proved by Proposition 4.9, which begins "If `X` is a completely metrizable space, …", and the construction in §4 correspondingly says "If `X` is completely metrizable, we choose `m` as a complete metric … and we also choose `w` as a complete metric on `X`", citing Bacon, *Extending a complete metric*, Amer. Math. Monthly **75** (1968) for the complete extension.  So the correct clause is

```text
(4′)  if X is completely metrizable, then E(Comp(A)) ⊆ Comp(X).
```

`(4′)` is not vacuous in our application: `A = D` closed in a completely metrizable `X` is completely metrizable, and `Comp(D) ≠ ∅`.  This is an erratum against the published preprint, not against the joint draft, but any draft statement that cites Theorem 1.1(4) inherits it and must carry the hypothesis.

### 11.4 Pullback for complete metrics

Assume `X` is completely metrizable, `A ⊆ X` closed.  Then

```text
Ẽ⁻¹(Comp(X)) = Comp(A).
```

`⊇` is `(4′)`.  For `⊆`: if `Ẽ(ψ) ∈ Comp(X) ⊆ Met(X)` then `ψ ∈ Met(A)` by 10.4(a), and `ψ = Ẽ(ψ)|_{A²}` is the restriction of a complete metric to a closed subspace, hence complete.

### 11.5 The corrected general-space theorem

**Theorem 3.8 (corrected).** Let `X` be **completely metrizable** and non-separable.  Then `Comp(X)` is neither analytic nor coanalytic in `CPM(X)`.  Contrapositively: if `X` is completely metrizable and `Comp(X)` is analytic or coanalytic in `CPM(X)`, then `X` is separable.

*Proof.* `Λ = Ẽ∘Φ_full` and `Λ⁻¹(Comp(X)) = Φ_full⁻¹(Comp(D)) = [0,1]\S` by 11.1 and 11.4. ∎

**The added hypothesis is necessary, not cosmetic.** If `X` is not completely metrizable then `Comp(X) = ∅`, which is closed, hence both analytic and coanalytic under any of the conventions in play, while `X` may be non-separable (e.g. `ℚ × D` for discrete `D` of size `ℵ₁`).  Without the hypothesis the statement is refuted by a triviality, and the same triviality is what `(4′)` is protecting.  Equivalently one may phrase the hypothesis as `Comp(X) ≠ ∅`.

### 11.6 On the path/component assertions

`Comp(D)` is **not** a union of finite-distance components of `Met(D)`, so component-level statements about it must be phrased as intersections `C ∩ Comp(D)` (as in 11.2), not as "components of `Comp(D)`".  Witness inside the single component `BMet(D)`: fix a countably infinite `{x_n} ⊆ D`, let `e` be the metric with `e(x_n,x_m) = |2^{-n} - 2^{-m}|` and `e = 1` on the remaining off-diagonal pairs.  All values lie in `(0,1]` and the only nontrivial triangle inequalities are `≤ 1/2 ≤ 2` and `1 ≤ 1 + |2^{-n}-2^{-m}|`, so `e` is a bounded metric; `x_n` is isolated because its nearest neighbour is at distance `2^{-(n+1)}`, and every other point is `1`-separated, so `e ∈ BMet(D)`.  But `(x_n)` is `e`-Cauchy without a limit, so `e ∉ Comp(D)`, while the `0/1` metric lies in `BMet(D) ∩ Comp(D)`.  Ishiki's clopen/path-connectedness statement (§2.2) is about `M_{<∞}`, and does not descend to `Comp`.

---

## 12. Item 8 — the Koshino consequence

### Verdict: **PASS-INDEPENDENT, and ZFC-safe — the `(★)` gap of §2 does not propagate here**

### 12.1 Koshino's statements, verbatim

Koshino, *On the Borel complexity and the complete metrizability of spaces of metrics*, arXiv:2403.07421v2 = Anal. Geom. Metr. Spaces **12** (2024), art. 20240014.  Both results are **unnumbered** in the source.

Notation: `C(X²)` = bounded continuous real functions on `X²` with the sup metric `D`; `PM(X) ⊆ C(X²)` the bounded continuous pseudometrics, closed in `C(X²)`; `AM(X) ⊆ PM(X)` the **bounded** admissible (= compatible) metrics.  `A_n`, `M_n` are the absolute Borel classes, with `M₀` = compact metrizable, `M₁` = completely metrizable, `A₁` = σ-locally compact metrizable (σ-compact in the separable case).

> **Theorem.** Suppose that `X` is a metrizable space and `n ≥ 1` is a natural number.  If `AM(X)` is in `A_n` (respectively, `M_n`), then `X` is in `M_n` (respectively, `A_n`).

> **Corollary.** Let `X` be a separable metrizable space.  Then `X` is σ-compact if and only if `AM(X)` is completely metrizable.

In Ishiki's notation `AM(X) = BMet(X)` and `PM(X) = BCPM(X)`.  Ishiki §5 recalls the Corollary in the `Met(X)` form; that identification is his, not Koshino's, and the two spaces should not be silently exchanged (this repeats the caveat already in `notes/literature.md`).

### 12.2 Where the separability hypothesis actually enters

Koshino's proof of the Corollary is two lines: "only if" (`X` σ-compact ⇒ `AM(X)` completely metrizable) is his earlier [7, Proposition 3] and carries no separability, σ-compact metrizable spaces being separable anyway; "if" is the Theorem at `n = 1`, giving `X ∈ A₁`.

So separability is used at exactly one point: to upgrade **`A₁` = σ-locally compact metrizable** to **σ-compact**.  Nothing else in the Corollary needs it.  Removing the hypothesis is therefore precisely the task of proving that `AM(X)` completely metrizable forces `X` separable — which is Ishiki's stated motivation for Conjecture 5.1 and is what the present track delivers.

### 12.3 The consequence, by an elementary route that needs no pointclass convention

**Theorem.** Let `X` be metrizable.  If `AM(X)` is completely metrizable, then `X` is separable.

*Proof.*  Suppose `X` is non-separable and take `D ⊆ X` closed discrete with `|D| = ℵ₁` (10.1).  By 10.4(b), `Ẽ` restricts to a continuous (indeed isometric) map `Ẽ_b : PM(D) → PM(X)` with `Ẽ_b⁻¹(AM(X)) = AM(D)`.

If `AM(X)` is completely metrizable, it is a `G_δ` in the metrizable ambient `PM(X)` (Kechris, *Classical Descriptive Set Theory*, Theorem 3.11 — no separability hypothesis).  Continuous preimages of `G_δ` sets are `G_δ`, so `AM(D)` is a `G_δ` in `PM(D)`, which is a complete metric space; hence `AM(D)` is completely metrizable.

But `AM(D) = BMet(D)` is not completely metrizable: by §5 the set `{d_t : t ∉ S}` is closed in `BMet(D)` and bi-Lipschitz to `[0,1]\S`, and a closed subspace of a completely metrizable space is completely metrizable, so `[0,1]\S` would be `G_δ` in `[0,1]` and `S` would be `F_σ`.  An uncountable `F_σ` subset of `[0,1]` contains a nonempty perfect set (Cantor–Bendixson, Kechris 6.4, applied to an uncountable closed piece), so it suffices that `S` contain none.  The coding of §§4–5 runs with *any* injectively enumerated `S ⊆ [0,1]` of size `ℵ₁`, so take `S` to be an `ℵ₁`-sized subset of a Bernstein set — a ZFC construction with no CH case split, and weaker than what Proposition 2.1 is asked to deliver. ∎

**Corollary (separability hypothesis removed).** For **every** metrizable `X`: `X` is σ-compact if and only if `AM(X)` is completely metrizable.

*Proof.* "⇒" is Koshino [7, Proposition 3].  "⇐": the Theorem gives separability, and then Koshino's Corollary applies (equivalently: Koshino's Theorem at `n=1` gives `X ∈ A₁`, and separability turns σ-locally compact into σ-compact). ∎

### 12.4 The `(★)` gap of §2 does not reach this corollary

Two independent reasons, and either alone is decisive.

1. **The parameter set needed here is weaker.**  The proof of 12.3 needs only that `S` is not `F_σ`, for which it is enough that `S` be uncountable and contain no nonempty perfect subset (the converse fails: a non-`F_σ` set may well contain a perfect subset).  A subset of a Bernstein set of size `ℵ₁` has this property in ZFC, with no case split on CH and with no reference to analytic or coanalytic sets at all.  `(★)` concerns whether such an `S` can also be kept off `L[a]` for every real `a`, which the `F_σ` argument never asks.
2. **Even in the pointclass formulation, only the ZFC-safe half is used.**  Complete metrizability of `AM(X)` makes it `G_δ`, hence *both* analytic and coanalytic under the §1 Souslin-`F` convention (a `G_δ` is Borel; in a metric space open sets are `F_σ`, so Borel sets and their complements are all Souslin-`F`).  One may therefore invoke the coanalytic half of §10.5, which §6 identifies as the half available in ZFC — for `ℵ₁ < 𝔠` for any `S` of size `ℵ₁`, and under CH for the Bernstein `S` of §2.  ("For every `S` of size `ℵ₁`" would be an overclaim: under CH, `S = [0,1]` has size `ℵ₁` and is closed.)

Consequently the Koshino corollary is unconditional in ZFC.  What it does depend on: Ishiki's Theorem 1.1, clauses (1)(2)(3) and the "furthermore" part (not (4), so §11.3 is irrelevant here); the coding of §§4–5; Kechris 3.11 and 6.4.  Route 1 additionally avoids §1 entirely, so this corollary is not blocked by the ambient-convention question either.

### 12.5 Byproducts

- The same argument with 10.4(a) in place of 10.4(b) reproves Ishiki's §5 motivation directly: for non-separable metrizable `X`, `Met(X)` is not completely metrizable.  This is the extensor-based route to the statement that the project's Conjecture 5.1 work established for `D_{ℵ₁}`; here it comes out of the pullback with the closed-image argument used only in the mild form of §10.7.
- With 11.4 in place of 10.4, and `X` completely metrizable, `Comp(X)` completely metrizable ⇒ `X` separable, by the identical `G_δ`-preimage argument.

Two verifications these byproducts need and 12.3 does not.  First, the ambient must be metrizable and complete even though `D_X` is extended-valued: `min(D_X,1)` is a genuine metric inducing the same topology, and a `min(D_X,1)`-Cauchy sequence is eventually `D_X`-Cauchy, so `CPM(X)` is completely metrizable and Kechris 3.11 applies to it.  Second, the coding copy must be closed in the right space.  It is: §5 gives closedness in `BMet(D)`, and if `d_{t_k} → d` with `d ∈ Met(D)` then `d` is at finite sup-distance from a bounded metric, hence bounded, so `d ∈ BMet(D)` and §5 applies — the copy is closed in `Met(D)`, and being contained in `Comp(D)` (11.1) it is closed there too.

### 12.6 Residual checks

- `[7, Proposition 3]` (Koshino 2022, Bull. Pol. Acad. Sci. Math. **70**) — the "σ-compact ⇒ `AM(X)` is `G_δ` in `C(X²)`" direction — was not re-derived in this pass; it is quoted from Koshino's own summary of it.  It is the only ingredient of the final corollary that this audit takes on trust.
- The identifications `A₁` = σ-locally compact metrizable and `M₁` = completely metrizable are quoted from Koshino's introduction, not re-derived here.  They are load-bearing for the corollary: `A₁` is where the removed separability hypothesis was doing its work.

---

## 13. Non-Archimedean track (draft Lemmas 3.9–3.10, Theorems 3.11–3.16)

> Derived independently of the joint draft, from the checkpoint list of Issue #46 item 7.  The mapping onto the draft's numbering is provisional: the results below are labelled `NA-1`…`NA-9` and matched to the checkpoints, not to draft statements.  Sources for the ambient conventions are Ishiki, *An embedding, an extension, and an interpolation of ultrametrics* (arXiv:2008.10209 = [20] of arXiv:2407.03030) and *A factorization of metric spaces* (arXiv:2212.13409 = [22]).

### 13.0 Verdict summary

| # | statement | verdict |
| --- | --- | --- |
| NA-1 | conventions: `UD^R_X`, range set, countable coinitiality | **PASS** — fixed against [20, §1] and [22, §2]; the draft must name which of `UD^R_X` / `D_X` it uses |
| NA-2 | dense bad `S ⊆ 2^ℕ` by direct Bernstein construction | **PASS under CH**; **BLOCKED for `ℵ₁<𝔠`** — inherits `(★)` of §2, but removes the §3 Borel-isomorphism defect |
| NA-3 | `R`-valued ultrametric coding on discrete `D`, `\|D\|=ℵ₁` | **PASS** — construction below; simpler than §4 (no diameter budget) |
| NA-4 | exact `UD` estimate `UD^R_X(d_σ,d_τ) = ρ_R(σ,τ)` | **PASS** — an exact isometry, strictly stronger than the bi-Lipschitz §5 estimate |
| NA-5 | countable coinitiality of `R` | **PASS, and necessary** — without it the ambient is uniformly discrete and every theorem in the track is false |
| NA-6 | ultrametric one-point amalgamation, component branch | **PASS** — amalgamation is correct and `UD`-isometric; it coincides with ball refinement.  **FIX**: the `UD`-component decomposition is trivial when `R` has a maximum |
| NA-7 | complete-ultrametric branch | **PASS** — the coding ultrametrics are complete for *every* parameter, so no separate construction is needed |
| NA-8 | transfer to general spaces via the ultrametric extensor | **FIX (load-bearing)** — [22, Thm 4.7] has neither a pseudo-ultrametric clause nor a closed-image clause; both are derivable from [22, Thm 3.1] but must be stated and proved, not cited |
| NA-9 | ambient pointclass | **BLOCKED** — §1 propagates verbatim; the non-Archimedean ambient is nonseparable with nonseparable complement |

---

### 13.1 Conventions (NA-1)

Fixed against the primary sources, since the draft's `UD` notation is inherited from them.

A **range set** `R` is a subset of `[0,∞)` with `0 ∈ R`; `R₊ = R\{0}` ([20, §1]).  `R` is **characteristic** ([22, §2]) — equivalently has **countable coinitiality** ([20, §1]) — if `inf R₊ = 0`, i.e. there is a strictly decreasing sequence in `R₊` tending to `0`.  `UMet(X;R)` is the set of `R`-valued ultrametrics on `X` compatible with the topology of `X`.  The **non-Archimedean supremum metric** is ([20, §1])

```text
UD^R_X(d,e) = inf{ ε ∈ R ⊔ {∞} : ∀x,y   d(x,y) ≤ e(x,y) ∨ ε   and   e(x,y) ≤ d(x,y) ∨ ε }.
```

Two reformulations are used constantly below and should be recorded in the draft:

```text
(U1)  the defining condition on ε is equivalent to:  ∀x,y  ( d(x,y) ≠ e(x,y)  ⟹  d(x,y) ∨ e(x,y) ≤ ε )
(U2)  writing  raw(d,e) = sup{ d(x,y) ∨ e(x,y) : d(x,y) ≠ e(x,y) }  (sup ∅ = 0),
      one has  raw(d,e) ≤ UD^R_X(d,e) = inf{ ε ∈ R ⊔ {∞} : ε ≥ raw(d,e) },
      so UD^R_X is the R-rounding of raw, and { UD ≤ r } = { raw ≤ r } for every r ∈ R.
```

`(U1)` is [20, Remark 1.8] stated for all `ε` rather than for `r ∈ R₊`; `(U2)` is immediate from `(U1)`.  The infimum in `(U2)` need not be attained — this is why [20, §1] records the value range as `CL(R) ⊔ {∞}` rather than `R ⊔ {∞}` — but it is attained, and the rounding is the identity, whenever `raw(d,e) ∈ R`, which is the case at every use below.  Notation: `UMet(X;R)` and `UD^R_X` are the symbols of arXiv:2407.03030 §1.1; [20] writes `UM(X,S)` and `UD^S_X` for the same objects, and defines `UD^S_X` only on `UM(X,S)`.  Extending it to pseudo-ultrametrics, as the ambient below requires, is this audit's step, not the source's.  `UD^R_X` is an ultrametric with values in `CL(R) ⊔ {∞}`, and `D_X ≤ UD^R_X` ([20, Lemma 6.2]) — so the `UD`-topology is finer than the sup-metric topology, in general strictly.

**Ambient.**  Take `UCPM(X;R)` = continuous `R`-valued pseudo-ultrametrics on `X`, with `UD^R_X`.  This is the non-Archimedean counterpart of `CPM(X)` and is the right target for a pullback formulation.  It is complete: `(C(X²,R), U^R_{X²})` is a complete ultrametric space ([20, Lemma 7.5]), the evaluations `f ↦ f(a,b)` are continuous into `(R,d_E)` ([20, Lemmas 7.2, 7.4]), so symmetry, vanishing on the diagonal and the strong triangle inequality all cut out a closed subset; and by `(U2)` the uniformities of `UD^R_X` and `U^R_{X²}` agree on `UCPM(X;R)` (they have the same entourages `{raw ≤ r}`, `r ∈ R₊`).

### 13.2 Cantor parameter set, directly (NA-2)

The non-Archimedean coding needs a bad set in `2^ℕ`, not in `[0,1]`, so §3's transfer is not on the critical path here — the construction can be done in `2^ℕ` from the start, and should be.

`2^ℕ` is a perfect Polish space, so the Bernstein recursion of §2 runs verbatim: enumerate the `𝔠` many nonempty perfect subsets of `2^ℕ` and pick two distinct points from each.  The resulting `S ⊆ 2^ℕ` meets every nonempty perfect set and omits a point of each, so under CH it has `|S| = 𝔠 = ℵ₁`, is dense (every nonempty cylinder `[s]` contains a perfect set), and is neither analytic nor coanalytic by the analytic perfect-set theorem alone (Kechris 29.1), exactly as in §2.  For `ℵ₁ < 𝔠` the Bernstein set itself is the wrong object — the recursion delivers `|S| = 𝔠 > ℵ₁`, not the `ℵ₁`-enumeration `{σ_α : α < ω₁}` that the coding of `NA-3` consumes.  There, as in §2, one takes an `ℵ₁`-sized subset of it instead: `|S| = ℵ₁` makes `S` thin, hence not analytic in ZFC, while "not coanalytic" needs `(★)`.

Two consequences for the manuscript:

- Proposition 2.2 should be proved *directly* in `2^ℕ` and, if a `[0,1]` version is still wanted, obtained by transfer in the other direction.  This removes §3's defect (a Borel isomorphism does not preserve density) at its source rather than repairing it downstream.
- **Density is not used by the coding below.**  The construction `NA-3` uses only `|S| = ℵ₁` and the failure of both pointclass memberships.  What density buys is that `UMet(D;R)` is not closed in the ambient — and for that it is the density of `2^ℕ\S`, not of `S`, that is used, since `d_σ` for `σ ∈ S` is a limit of compatible `d_τ` exactly when `σ ∈ cl(2^ℕ\S)`; both constructions above supply both densities.  This is a separate, weaker statement, and it is what the older relatively-closed-copy argument needed.  Under the pullback formulation demanded by Issue #46 point C it is dead weight, and in particular the `ℵ₁<𝔠` branch of §2 need not adjoin a countable dense `Q`.  §9.6 reaches the same conclusion independently on the Archimedean side: §§4–5 and §9 consume only the injective `ℵ₁`-enumeration.  Note what this does and does not license: it is a change to the *statement* of Proposition 2.1/2.2, which still asserts density, not merely a simplification of their proofs, so it is a question for the authors (§13.10 item 5) rather than a repair this audit can make unilaterally.

### 13.3 The `R`-valued coding (NA-3; draft Lemma 3.9 analogue)

Let `R` be a characteristic range set and fix a strictly decreasing `(r_n)_{n≥0}` in `R₊` with `r_n → 0`.  Put `T = {0} ∪ {r_n : n ∈ ℕ} ⊆ R`.  Give `2^ℕ` the `T`-valued ultrametric

```text
ρ_R(σ,τ) = r_{2Δ(σ,τ)}   (σ ≠ τ),      ρ_R(σ,σ) = 0,
Δ(σ,τ) = min{ n : σ(n) ≠ τ(n) }.
```

`ρ_R` is an ultrametric because `Δ(σ,υ) ≥ min(Δ(σ,τ),Δ(τ,υ))` and `n ↦ r_{2n}` is decreasing; its balls are the cylinders, so it induces the product topology and `(2^ℕ,ρ_R)` is compact.

Let `S = {σ_α : α < ω₁} ⊆ 2^ℕ` be the parameter set of `NA-2`.  Carrier:

```text
X = A ⊔ ⨆_{α<ω₁} B_α ,      A = { u_n, v_n : n ∈ ℕ } ,      B_α = { b_α } ∪ { c_{α,n} : n ∈ ℕ },
```

a discrete space with `|X| = ℵ₁`.  For `σ ∈ 2^ℕ` define `d_σ : X² → T` by

```text
anchor      d_σ(u_n,v_n) = r_{2n}   if σ(n)=0,        r_{2n+1}  if σ(n)=1;
            d_σ(x,y)     = r_0      for all other distinct x,y ∈ A;
star        ℓ_n(α,σ) = ρ_R(σ,σ_α) ∨ r_n,
            d_σ(b_α,c_{α,n}) = ℓ_n(α,σ),   d_σ(c_{α,n},c_{α,m}) = ℓ_n(α,σ) ∨ ℓ_m(α,σ)  (n≠m);
cross       d_σ(x,y) = r_0   whenever x,y lie in distinct members of { A } ∪ { B_α }.
```

**`d_σ` is a `T`-valued ultrametric, for every `σ ∈ 2^ℕ`.**  All off-diagonal values lie in `T₊` (each is `≥ r_n` for some `n`), so positivity holds even at bad parameters — as in §4, this is what makes the whole-parameter map of `NA-4` total.  Strong triangle inequality, by block:

- *Anchor.*  The designated pairs `{u_n,v_n}` are pairwise disjoint, so any three distinct points contain at most one designated pair; with all remaining distances equal to `r_0 ≥ r_{2n}, r_{2n+1}`, every triple is isosceles with the two larger sides equal to `r_0`.
- *Star.*  For any `ℓ : ℕ → (0,∞)`, setting `d(b,c_n) = ℓ_n` and `d(c_n,c_m) = ℓ_n ∨ ℓ_m` gives an ultrametric: `ℓ_n ∨ ℓ_m ≤ (ℓ_n ∨ ℓ_k) ∨ (ℓ_k ∨ ℓ_m)` and `ℓ_n ≤ ℓ_m ∨ (ℓ_n ∨ ℓ_m)`.
- *Cross.*  All intra-block values are `≤ r_0`, and every cross pair has value exactly `r_0`.  For a triple meeting two blocks, at least two of the three sides are cross pairs, both of value `r_0`, and the third is `≤ r_0`.

Note the contrast with §4: no diameter budget is needed.  Taking the cross distance equal to the largest intra-block value `r_0` already works, because `∨` replaces `+`.  In particular every `d_σ` is bounded by `r_0`, so if `R` is bounded the bounded/unbounded distinction collapses and `UMet = UBMet`.

**Compatibility iff `σ ∉ S`.**

```text
inf_{v ≠ c_{α,n}} d_σ(c_{α,n},v)  ≥ ℓ_n(α,σ) ≥ r_n > 0        (spokes always isolated)
inf_{n}          d_σ(b_α,c_{α,n}) = inf_n ( ρ_R(σ,σ_α) ∨ r_n ) = ρ_R(σ,σ_α)
```

using `r_n → 0`.  Anchor points and cross-block pairs are `r_{2n+1}`- resp. `r_0`-isolated.  Hence `b_α` is isolated iff `σ ≠ σ_α`, and

```text
d_σ ∈ UMet(X;R)   ⇔   σ ∈ 2^ℕ \ S.
```

This is sharper than §4's version: `ρ_R(σ,σ_α)` *is* the isolation radius of `b_α`, not merely a lower bound for it.

**Completeness (used in `NA-7`).**  Every `d_σ` is a complete ultrametric on `X`, for every `σ`.  A sequence of distinct points that is Cauchy must eventually stay in one block; in `A` the values are bounded below by `r_{2n+1}` along any fixed pair, so no such sequence exists; in `B_α`, `d_σ(c_{α,n},c_{α,m}) = ρ_R(σ,σ_α) ∨ r_{min(n,m)}`, which is `> 0` and constant `= ρ_R(σ,σ_α)` for large `n,m` unless `σ = σ_α`, in which case `c_{α,n} → b_α`.

### 13.4 Exact `UD` estimate and the pullback identity (NA-4; draft Lemma 3.10 analogue)

**Claim.**  For all `σ,τ ∈ 2^ℕ`,

```text
UD^R_X(d_σ, d_τ) = ρ_R(σ,τ).
```

*Lower bound.*  Let `Δ = Δ(σ,τ)`.  At the anchor pair `(u_Δ,v_Δ)` the two values are the distinct elements `r_{2Δ}, r_{2Δ+1}`, whose maximum is `r_{2Δ}`; by `(U1)` any admissible `ε` satisfies `ε ≥ r_{2Δ}`.

*Upper bound.*  Check `(U1)` with `ε = r_{2Δ}` pair by pair.  Cross-block pairs and non-designated anchor pairs carry the value `r_0` under both, so they never disagree.  A designated anchor pair `(u_n,v_n)` disagrees only if `σ(n) ≠ τ(n)`, forcing `n ≥ Δ`, and then the maximum is `r_{2n} ≤ r_{2Δ}`.  For a star pair, write `ρ_σ = ρ_R(σ,σ_α)`, `ρ_τ = ρ_R(τ,σ_α)`.  If `ℓ_n(α,σ) ≠ ℓ_n(α,τ)`, i.e. `ρ_σ ∨ r_n ≠ ρ_τ ∨ r_n`, then `ρ_σ ≠ ρ_τ` and `ρ_σ ∨ ρ_τ > r_n`, so

```text
ℓ_n(α,σ) ∨ ℓ_n(α,τ) = ρ_σ ∨ ρ_τ = ρ_R(σ,τ) = r_{2Δ},
```

the middle equality being the isosceles property of the ultrametric `ρ_R` (if `ρ(σ,a) ≠ ρ(τ,a)` then `ρ(σ,τ)` equals their maximum).  Spoke–spoke pairs reduce to the same computation via `ℓ_n ∨ ℓ_m = ρ ∨ r_{min(n,m)}`.  Since `r_{2Δ} ∈ R`, `(U2)` gives `UD^R_X(d_σ,d_τ) = r_{2Δ}` exactly. ∎

So the whole-parameter map

```text
Φ_full : (2^ℕ, ρ_R) → (UCPM(X;R), UD^R_X),   σ ↦ d_σ
```

is an **isometric embedding**, with

```text
Φ_full⁻¹( UMet(X;R) ) = 2^ℕ \ S.
```

Three points where this is better-behaved than §5, and which the manuscript should exploit rather than merely mirror:

1. The estimate is an equality; there is no analogue of §5's `|s-t| ≤ D ≤ 2|s-t|` slack.  The `∨` operation does not accumulate the way `+` does, and the isosceles property replaces the two-sided Lipschitz bound.
2. `Φ_full` is continuous into `(UCPM(X;R), D_X)` as well, since `D_X ≤ UD^R_X`, and the same pullback identity holds there.  The obstruction therefore holds for **both** candidate topologies on the ambient, which insulates the theorem from the ambiguity raised in 13.10(1).
3. `Φ_full(2^ℕ)` is **compact**, hence closed in any Hausdorff ambient.  §5's closed-image argument (evaluate at the anchor, take limits, invoke closedness of `[0,1]`) has no counterpart to prove here — closedness is free.  Consequently `Φ_full(2^ℕ\S) = Φ_full(2^ℕ) ∩ UMet(X;R)` is relatively closed in `UMet(X;R)` without further work.

Combining with a pointclass on nonseparable metrizable ambients that is closed under continuous preimages and agrees with `Σ¹₁/Π¹₁` on the Polish space `2^ℕ` (§1), the discrete obstruction follows exactly as in §6, with the same ZFC bookkeeping:

```text
UMet(D;R) analytic    ⇒  2^ℕ\S analytic    ⇒  S coanalytic
UMet(D;R) coanalytic  ⇒  2^ℕ\S coanalytic  ⇒  S analytic
```

Under CH both halves hold in ZFC; under `ℵ₁<𝔠` only "**`UMet(D;R)` is not coanalytic**" is unconditional, the other half being exactly `(★)`.

### 13.5 Countable coinitiality: where it is used, and that it is necessary (NA-5)

Three distinct uses, which the draft should separate:

1. **Isolation.**  `inf_n (ρ ∨ r_n) = ρ` in `NA-3` needs `r_n → 0`; this is the entire compatibility mechanism.
2. **Reduction to a model value set.**  Everything above is built inside `T = {0} ∪ {r_n}`.  For an arbitrary characteristic `R` one may either work with `(r_n)` directly (as done here) or transport from `A = {0} ∪ {2^{-n}}` along an increasing amenable `ψ` with `ψ(A) = T` ([20, Lemma 2.2, Lemma 2.12, Prop. 2.14]); `d ↦ ψ∘d` is a bijection `UMet(X;A) → UMet(X;T)` and preserves the `(U1)` relation "agree above scale", so it is a homeomorphism for `UD`.  Either route is fine; the direct one avoids a lemma.
3. **Existence of `v`.**  The extensor of `NA-8` needs `v ∈ UMet(X/F;R) ≠ ∅`, which by [22, Prop. 2.3] requires `R` characteristic.

**Necessity.**  If `R` is not characteristic, there is `r > 0` with `R ∩ (0,r) = ∅`.  For distinct `f,g ∈ UCPM(D;R)` some pair carries distinct values, at least one of which is `≥ r`, so `raw(f,g) ≥ r` and by `(U2)` `UD^R_D(f,g) ≥ r`.  The ambient is uniformly `r`-discrete, every subset is clopen, and `UMet(D;R)` is closed — hence analytic *and* coanalytic under any convention.  Every statement in the track that is formulated with `UD^R_X` as the ambient metric is therefore false without countable coinitiality, and the hypothesis must appear in each of them, not only where it is convenient.  The argument is specific to `UD`: it uses `(U2)`, so it says nothing about a `D_sup`-formulated ambient, where non-characteristic `R` need not force uniform discreteness.  Which formulation the draft intends is 13.10(1), and the necessity claim should be attached to whichever it is.  (Compare [20, Lemma 2.13]: without countable coinitiality every `R`-valued ultrametric space is *discrete and complete*; its proof exhibits a single radius `r` with `[0,r) ∩ R = {0}`, so the discreteness it gives is in fact uniform, which is what the argument above uses.  By [20, Proposition 2.14] the same `r` forces `UMet(Y;R) = ∅` for every non-discrete `Y`, so the failure is not confined to the discrete carrier.)

### 13.6 One-point amalgamation and the component branch (NA-6; draft Theorem 3.12 analogue)

**Amalgamation lemma.**  Let `(Y,d)`, `(Z,e)` be `R`-valued (pseudo-)ultrametric spaces with `Y ∩ Z = {*}`.  Define on `Y ∪ Z`

```text
m(x,y) = d(x,y)  (x,y ∈ Y);   m(x,y) = e(x,y)  (x,y ∈ Z);
m(x,z) = d(x,*) ∨ e(*,z)      (x ∈ Y\Z, z ∈ Z\Y).
```

Then `m` is an `R`-valued (pseudo-)ultrametric.  No closure hypothesis on `R` is needed, since `∨` of two members of `R` is a member of `R`.  This is the counterpart of §9.2, where the Archimedean amalgamation is additive through the basepoint, `m(x,z) = d(x,*) + e(*,z)`; `∨` in place of `+` is exactly what removes the diameter bookkeeping there.  The nontrivial triples:

```text
x,y ∈ Y, z ∈ Z\Y :  m(x,y) = d(x,y) ≤ d(x,*) ∨ d(*,y) ≤ m(x,z) ∨ m(z,y)
                    m(x,z) = d(x,*) ∨ e(*,z) ≤ (d(x,y) ∨ d(y,*)) ∨ e(*,z) = m(x,y) ∨ m(y,z)
x ∈ Y\Z, y,z ∈ Z\Y: m(x,y) = d(x,*) ∨ e(*,y) ≤ d(x,*) ∨ e(*,z) ∨ e(z,y) = m(x,z) ∨ m(z,y)
```

`m` induces the wedge topology (for `x ∈ Y\{*}` and `s < d(x,*)` the `m`-ball `B(x,s)` lies in `Y`; `B(*,s) = B_d(*,s) ∪ B_e(*,s)`), so `m ∈ UMet(Y∨Z;R)` iff `d ∈ UMet(Y;R)` and `e ∈ UMet(Z;R)`.

**Completeness is preserved** — for genuine ultrametrics; in the pseudo-ultrametric case `Y` and `Z` need not be closed in the wedge (a point of `Z\{*}` may lie at distance `0` from `*`), and the argument below does not apply without passing to the metric quotient.  (§11.2 is the Archimedean counterpart; there the pieces are `ε`-separated, so the case below in which the sequence meets both sides infinitely often cannot arise.)  Let `(x_i)` be `m`-Cauchy.  If it has infinitely many terms in each of `Y\{*}`, `Z\{*}`, then cross distances `d(x_i,*) ∨ e(*,x_j) < ε` eventually, so both subsequences converge to `*` and so does the sequence.  Otherwise it is eventually inside the closed subspace `Y` or `Z` and converges there.  The converse holds since `Y`, `Z` are closed.

**`UD`-isometry in the varying factor.**  With `(Z,e)` fixed, `d ↦ m_d` satisfies `UD^R_{Y∨Z}(m_d,m_{d'}) = UD^R_Y(d,d')`.  `≥` is restriction to `Y²`; for `≤`, if `m_d(x,z) ≠ m_{d'}(x,z)` on a cross pair then `d(x,*) ≠ d'(x,*)` and their maximum exceeds `e(*,z)`, so `m_d(x,z) ∨ m_{d'}(x,z) = d(x,*) ∨ d'(x,*)`, and `(U1)` transfers.

**Component branch.**  Fix `ν ∈ UMet(D;R)`, `|D| = ℵ₁`, and `x₀ ∈ D`.  Every subset of `ℝ` has countable cofinality (a strictly increasing `ω₁`-sequence of reals is impossible), so choosing `s_k ∈ R₊` increasing with `s_k → sup R` gives `D = ⋃_k B_ν(x₀,s_k)`; hence some closed ball `W := B_ν(x₀,ε)`, `ε ∈ R₊`, has `|W| = ℵ₁`.  This is the ultrametric form of the "uncountable bounded ball" step, and it needs no hypothesis beyond `R ⊆ [0,∞)`.

Now identify `W` with the carrier `X` of `NA-3`, choosing the coding sequence inside `(0,ε]` so that `r_0 = ε`, and set

```text
Ψ(σ)(x,y) = d_σ(x,y)   for x,y ∈ W,        Ψ(σ)(x,y) = ν(x,y)   otherwise.
```

`Ψ(σ)` is an ultrametric: for `x,y ∈ W` and `z ∉ W` the isosceles property of `ν` gives `ν(x,z) = ν(y,z) > ε ≥ Ψ(σ)(x,y)`, so all mixed triples are isosceles with the two large sides equal.  Taking `* = x₀` and `Z = (D\W) ∪ {x₀}`, this "ball refinement" *is* the one-point amalgamation of the lemma above — the two formulations coincide because `W` is a ball, which is why the amalgamation route works here without the `+`-bookkeeping the Archimedean version needs.  One reads off

```text
UD^R_D(Ψ(σ), ν) ≤ ε,      D_sup(Ψ(σ),ν) ≤ ε,
UD^R_D(Ψ(σ), Ψ(τ)) = ρ_R(σ,τ),
Ψ⁻¹( UMet(D;R) ) = 2^ℕ \ S,
```

the last because points of `D\W` retain their `ν`-isolation and points of `W` are isolated exactly when they are isolated in the coding.  So every `UD`-component, and equally every `D_sup`-component, of `UMet(D;R)` carries the obstruction.

**FIX — the component statement is trivial for bounded `R`.**  Under `UD^R_X`, `d ~ e` iff `d` and `e` agree above some scale `ε ∈ R₊`.  If `sup R` is attained — equivalently `R` has a maximum, which covers every finite `R` — then `UD^R_X ≤ max R < ∞` always and there is exactly **one** component, so the componentwise theorem says nothing beyond the global one.  Attainment, not unboundedness, is the right dividing line: if `R` is bounded with `sup R ∉ R`, two pseudo-ultrametrics with `raw = sup R` admit no `ε ∈ R` above it, so `UD^R_X = ∞` and the decomposition is again non-trivial.  Note also that `UD`-equivalence is far more rigid than finite sup distance: members of one `UD`-component share all their values above `ε` and all their `ε'`-ball partitions for `ε' > ε`, so range coherence, not just finiteness, is part of the equivalence.  The refinement construction respects this automatically (it alters only values `≤ ε`), which is the reason it, rather than a general perturbation, is the right tool.  The draft should state which decomposition it means — `UD`-components of `UMet(X;R)` or `D_sup`-components — since only the latter is a faithful analogue of Theorem 3.4.

### 13.7 Complete-ultrametric branch (NA-7; draft Theorems 3.15–3.16 analogue)

No new construction is required.  By `NA-3`, `d_σ` is a complete ultrametric for **every** `σ ∈ 2^ℕ`, and completeness is preserved by the refinement/amalgamation of `NA-6` (a Cauchy sequence is eventually inside or outside the clopen ball `W`) — provided the ambient `ν` being refined is itself complete, which the component form of the complete branch must therefore assume, exactly as §11.2 assumes `ρ ∈ Comp(D)`.  Writing `UComp(X;R) = Comp(X) ∩ UMet(X;R)`, we get directly

```text
Φ_full⁻¹( UComp(X;R) ) = Φ_full⁻¹( UMet(X;R) ) = 2^ℕ \ S,
```

since for `σ ∈ S` the ultrametric `d_σ` is complete but not compatible, hence outside `UComp`.  The complete branch therefore costs one sentence, not a second coding.  There is no asymmetry with the Archimedean side after all: §11.1 records that `d_t` is likewise complete at every parameter, the sequence witnessing incompatibility at `t = w_β` being convergent rather than divergent.  On both tracks completeness fails to detect the parameter set and compatibility is what does the work, so neither branch needs a second coding — worth checking whether the draft duplicates work on either side.

### 13.8 Transfer to general ultrametrizable spaces — the extensor (NA-8)

This is the one place in the non-Archimedean track where the draft's citation base is insufficient as published.

**Where the ultrametric extensor lives.**  It is *not* in arXiv:2407.03030.  That paper states its non-Archimedean counterpart only in the introduction, as a pointer: "for an ultrametrizable space `X` and a closed subset `A`, the author constructed an isometric extensor from `(UMet(A;R), UD^R_X)` into `(UMet(X;R), UD^R_X)` (see [22, Theorem 4.7])", and calls its own Theorem 1.1 "an Archimedean analogue of [22, Theorem 4.7]".  The reference is Ishiki, *A factorization of metric spaces*, Colloq. Math. **174** (2023), 101–119 (arXiv:2212.13409).  It must be treated as an **external theorem with an explicit hypothesis**, exactly as the Layer-2 plan of §8 prescribes.

**What [22, Theorem 4.7] actually says.**  `X` ultrametrizable, `F ⊆ X` nonempty closed, `S` a characteristic subset of `[0,∞)`, `v ∈ UMet(X/F;S)`, and `Φ : X → F × X/F` the embedding of [22, Theorem 3.1]; then `Σ : Met(F) → Met(X)`, `Σ(d) = Φ*(d ×_∞ v)`, satisfies `Σ(d)|_{F²} = d`, `UD^S_X(Σd,Σe) = UD^S_F(d,e)`, monotonicity, `Σ(d ∨ e) = Σ(d) ∨ Σ(e)`, and `Σ(UMet(F;S)) ⊆ UMet(X;S)`; with (N1) `Σ(UCM(F;S)) ⊆ UCM(X;S)` when `X` is completely metrizable.

**Two clauses the draft needs and Theorem 4.7 does not have.**

- *No pseudo-ultrametric extension.*  `Σ` is defined on `Met(F)` — metrics **compatible with the topology of `F`**.  The coding ultrametrics `d_σ` for `σ ∈ S` are not compatible, so they are outside the domain.  The Archimedean paper solved precisely this by adding the clause `Ẽ : CPM(A) → CPM(X)` with `E(Met(A)) = Ẽ(CPM(A)) ∩ Met(X)`; Theorem 4.7 has no such clause.  §10.3–10.4 record why this is not a technicality: restriction runs the wrong way, so the pseudometric extensor is the only available ambient-level map.
- *No closed-image statement.*  Again the Archimedean Theorem 1.1 states it; Theorem 4.7 does not.

**The repair, from the construction rather than the statement.**  Both clauses follow from [22, Theorem 3.1], where `Φ = (r,π)` with `r : X → F` the Engelking-type retraction of [22, Theorem 2.11] and `π : X → X/F` the (1-Lipschitz) quotient map, and `Φ(a) = (a,ω_F)` for `a ∈ F`.  Since `Σ(d)(x,y) = d(r(x),r(y)) ∨ v(π(x),π(y))`, define by the *same formula*

```text
Σ̃ : UCPM(F;R) → UCPM(X;R),     Σ̃(d)(x,y) = d(r(x),r(y)) ∨ v(π(x),π(y)).
```

Then, with `F` closed in `X` and `dim_T(X\F) = 0` (automatic for ultrametrizable `X`):

1. `Σ̃(d)` is a continuous `R`-valued pseudo-ultrametric — a pointwise maximum of the pullbacks `d∘(r×r)` and `v∘(π×π)`, both continuous pseudo-ultrametrics.  If `d` is a genuine ultrametric on the set `F` then so is `Σ̃(d)`, because `Φ` is injective.
2. `Σ̃(d)|_{F²} = d`, from `Φ(a) = (a,ω_F)`.
3. `Σ̃|_{UMet(F;R)} = Σ`, and `UD^R_X(Σ̃d, Σ̃e) = UD^R_F(d,e)`.  For `≥`, restrict to `F²`.  For `≤`: if `Σ̃(d)(x,y) ≠ Σ̃(e)(x,y)` then `d(rx,ry) ≠ e(rx,ry)` and the common `v`-term is dominated, so `Σ̃(d)(x,y) ∨ Σ̃(e)(x,y) = d(rx,ry) ∨ e(rx,ry)`, and `(U1)` transfers.
4. **`Σ̃⁻¹( UMet(X;R) ) = UMet(F;R)`.**  `⊇` is Theorem 4.7(5).  `⊆`: if `Σ̃(d)` is compatible on `X`, its restriction to the subspace `F` is `d`, hence `d` is compatible on `F`.
5. `Σ̃` is an isometric embedding of the **complete** space `UCPM(F;R)` (13.1), so `Σ̃(UCPM(F;R))` is complete, hence closed in `UCPM(X;R)`; therefore `Σ(UMet(F;R)) = Σ̃(UCPM(F;R)) ∩ UMet(X;R)` is relatively closed in `UMet(X;R)`.  This is the missing closed-image clause, and it comes out of the ambient's completeness rather than a limit argument.
6. Under (N1), `Σ̃⁻¹(UComp(X;R)) = UComp(F;R)`: `⊇` is (N1); `⊆` because `F` is closed in `(X, Σ̃(d))` when `Σ̃(d)` is compatible.  This is §11.4 verbatim with `∨` for `+`, and (N1)'s hypothesis that `X` be completely metrizable is the same hypothesis that §11.3 shows the Archimedean Theorem 1.1(4) to be missing — so on this point [22, Theorem 4.7] is the more careful of the two statements.

**Consequent transfer theorem.**  Let `X` be a non-separable ultrametrizable space and `R` a characteristic range set.  A non-separable metrizable space contains an uncountable `ε`-separated set, which is closed and discrete; take `D ⊆ X` closed discrete with `|D| = ℵ₁`.  Then `Σ̃ ∘ Φ_full : 2^ℕ → UCPM(X;R)` is continuous with

```text
(Σ̃ ∘ Φ_full)⁻¹( UMet(X;R) ) = 2^ℕ \ S,
```

and likewise for `UComp(X;R)` when `X` is completely metrizable.  So `UMet(X;R)` — and its complete part — is neither analytic nor coanalytic, on the same pointclass hypothesis as §6.

**FIX — hypothesis on `X`.**  The conclusion "`UMet(X;R)` analytic or coanalytic ⟹ `X` separable" is **false for general metrizable `X`**: if `dim_T(X) ≠ 0` then `UMet(X;R) = ∅` ([22, Prop. 2.3]), which is closed, while `X` may be non-separable.  Every statement in the non-Archimedean track must read "ultrametrizable `X`" (equivalently metrizable with `dim_T(X) = 0`), and the corresponding corollary is strictly narrower in scope than its Archimedean counterpart.  Check whether the draft says "metrizable" anywhere in Theorems 3.13–3.16.

### 13.9 Propagation of §1 and of `(★)` (NA-9)

**§1 propagates verbatim.**  The non-Archimedean ambient is nonseparable with nonseparable complement, so the classical (separable) reading of "analytic" makes the theorems vacuous here too; the witness below is the ultrametric form of the one in §1.  Explicitly: fix `r_1 < r_0` in `R₊` and, for `A ⊆ D\{u,v,y₀}`, let `d_A` be the ultrametric whose two `r_1`-balls are `A` and `D\A`, with cross distance `r_0`.  For `A ≠ A'` and `z ∈ A\A'` one has `d_A(z,y₀) = r_0 ≠ r_1 = d_{A'}(z,y₀)`, so `UD^R_D(d_A,d_{A'}) = r_0`: a `r_0`-separated family of size `2^{ℵ₁}` in `UMet(D;R)`.  Identifying `u` with `v` by pullback along `π` gives an equally separated family of non-compatible pseudo-ultrametrics.  The §1 repair (Souslin-`F` / relative analytic, closed under continuous preimages and complementation, agreeing with `Σ¹₁` on `2^ℕ`) is exactly what `NA-4` and `NA-8` consume, and nothing more.

**`(★)` propagates with the same asymmetry.**  Under CH the track carries no set-theoretic hypothesis beyond ZFC, via the direct Bernstein set of `NA-2` — set-theoretically safe, that is; the §1 ambient convention still gates every pointclass statement here, and CH does nothing about it.  Under `ℵ₁ < 𝔠`, `|S| = ℵ₁` makes `S` thin, so `S` is not analytic in ZFC and therefore

```text
UMet(D;R), UComp(D;R), each of their components, and UMet(X;R) for
non-separable ultrametrizable X  are not coanalytic — unconditionally.
```

The dual half is exactly `(★)` of §2 and no more; the non-Archimedean track adds no new set-theoretic obligation.  If `(★)` stays open, the asymmetric ZFC-safe form of §6 is the right shape for Theorems 3.11–3.16 as well — as it is for §§9.5, 10.5 and 11.5 on the Archimedean side.  The scope matters: "not coanalytic in ZFC for any `S` of size `ℵ₁`" is available under `ℵ₁ < 𝔠`, where thinness does the work; under CH it holds for the Bernstein `S` of §2 and `NA-2`, not for an arbitrary `S` of that size.

**Lean note (for #47).**  The non-Archimedean coding is a better Layer-1 target than the Archimedean one: the estimate of `NA-4` is an exact equality, the carrier arithmetic is `max` rather than `+` (so no diameter budget and no `2`-Lipschitz constants), `IsUltrametricDist` exists in Mathlib v4.32.2, and completeness (`NA-7`) is free.  The descriptive layer is unchanged and remains blocked by §1 and §8.2 in the same way.

### 13.10 Points to put to the authors

1. **Which metric does `UMet(X;R)` carry?**  `UD^R_X` or the Archimedean `D_X`?  They need not induce the same topology: `D_X ≤ UD^R_X` gives continuity of the identity `(UMet,UD) → (UMet,D)` and nothing in the reverse direction ([20, Lemma 6.2]), though for particular `R` the two may still coincide.  The obstruction above holds for both, but the theorem statement means different things.
2. **Which ambient?**  `UCPM(X;R)` (continuous `R`-valued pseudo-ultrametrics), `C(X²,R)` with `U^R_{X²}` ([20, Remark 7.1]), or the full `CPM(X)` of the Archimedean sections?  "Analytic in `CPM(X)`" and "analytic in `UCPM(X;R)`" are different assertions; §1's pointclass convention must be fixed for whichever is chosen.
3. **Is `R` assumed characteristic** (countable coinitiality)?  It is necessary, not merely convenient — see `NA-5`.  Is it stated in every theorem, or only where used?
4. **Is `R` assumed bounded?**  If `sup R` is attained, `UD^R_X` is bounded and the `UD`-component decomposition is trivial (`NA-6`), so a componentwise theorem stated for `UD` is vacuous.  Confirm whether the intended components are `D_sup`-components.
5. **Is density of the parameter set used anywhere in the non-Archimedean track?**  It is not needed for the pullback route (`NA-2`).  If it is retained, please say which statement consumes it — otherwise Proposition 2.1/2.2 can drop it, which also simplifies the `ℵ₁<𝔠` branch.
6. **Provenance of the ultrametric extensor clauses.**  [22, Theorem 4.7] as published has no pseudo-ultrametric extension `Σ̃` and no closed-image statement.  Does the draft's Appendix A prove them?  If so, they should be stated as a lemma derived from [22, Theorem 3.1] and the explicit formula `Σ(d) = d∘(r×r) ∨ v∘(π×π)` (see `NA-8`), not cited from Theorem 4.7.
7. **Hypothesis on `X` in the general-space non-Archimedean theorems.**  Must be *ultrametrizable*, not metrizable, or the statement is false for `dim_T(X) ≠ 0` (`NA-8`, FIX).
8. **Is the complete branch given a separate coding?**  It need not be: the coding ultrametrics of `NA-3` are complete for every parameter (`NA-7`).
9. **`UBMet` vs `UMet`.**  If `R` is bounded these coincide; if the draft states both, confirm `R` is intended unbounded there.
10. **Draft numbering.**  Please confirm the correspondence Lemma 3.9 ↔ `NA-3`, Lemma 3.10 ↔ `NA-4`, Theorem 3.11 ↔ discrete obstruction, 3.12 ↔ components, 3.13/3.14 ↔ general space, 3.15/3.16 ↔ complete branch, so the audit verdicts can be attached to the manuscript's own labels.

---

### 13.11 Provenance and residual checks

- The joint draft was not available; every statement above was derived from the Issue #46 checkpoint list and verified against the primary literature ([20], [22], arXiv:2407.03030).  A different construction in the manuscript does not invalidate these verdicts, but the *statements* should be compared clause by clause, in particular the exact `UD` estimate (`NA-4`) and the extensor clauses (`NA-8`).
- `NA-8` item 5 (closed image via completeness of the ambient) and `NA-5` (necessity of countable coinitiality) are new relative to what the sources state; both have short proofs given above and should be independently re-checked before they are relied on.
- Citation numbers for [20] and [22] are those of arXiv:2407.03030's bibliography; the arXiv identifiers are 2008.10209 and 2212.13409 respectively, and the `UD^S_X` definition used here is [20, §1] with [20, Remark 1.8].
- Provenance at integration.  The [20] citations above — `§1`, Remark 1.8, Lemmas 2.2/2.12/2.13, Proposition 2.14, Lemmas 6.2, 7.2, 7.4, 7.5, Remark 7.1 — were re-checked against the arXiv:2008.10209 full text when this section was merged, and two wordings were corrected then: `(U2)` is an infimum rather than a minimum, and Lemma 2.13 states "discrete and complete", its uniform radius coming from the proof.  [22] (arXiv:2212.13409) was **not** available at integration time, so the content attributed to its Theorems 3.1 and 4.7 — including the clause list of `NA-8` and the (N1) numbering — is carried over from the item-7 pass unverified here, and is the one external dependency of this section that a second reader should re-check against the paper.

---

## 14. Standing gaps after §§9–13

1. §1 (ambient convention) still gates the pointclass statements of §§9–11 and of §13 alike.  It does **not** gate §12.3 route 1.
2. `(★)` of §2 still gates the "not analytic" half of Theorems 3.3/3.4/3.5/3.8 and of the non-Archimedean Theorems 3.11–3.16.  It gates nothing in §12.  Neither track adds a set-theoretic obligation beyond `(★)`.
3. Ishiki Theorem 1.1(4) must be quoted as `(4′)` with the completely-metrizable hypothesis (§11.3); the authors should be told, since the defect is in the published preprint.  Its non-Archimedean counterpart, [22, Theorem 4.7](N1), already carries that hypothesis (§13.8 item 6).
4. **[22, Theorem 4.7] cannot be cited for what the non-Archimedean transfer needs** (§13.8, `NA-8`, FIX): as published it has neither a pseudo-ultrametric extension clause nor a closed-image clause, and `Σ` is defined only on compatible metrics, so the coding ultrametrics at bad parameters lie outside its domain.  Both clauses are derivable from [22, Theorem 3.1] and the explicit formula `Σ(d) = d∘(r×r) ∨ v∘(π×π)`, but they must be stated and proved rather than attributed.  This is load-bearing: without them the non-Archimedean general-space theorems have no ambient-level map.
5. Two hypotheses that the non-Archimedean statements must carry everywhere, not only where convenient: `R` characteristic (countable coinitiality), without which the `UD` ambient is uniformly discrete and every `UD`-formulated theorem in the track is false (§13.5; the argument is specific to `UD` and leaves a `D_sup` formulation undecided); and `X` **ultrametrizable**, not merely metrizable, without which `UMet(X;R) = ∅` and the general-space statement is refuted by a triviality (§13.8) — the exact analogue of the `Comp(X) = ∅` failure in §11.5.
6. [22] (arXiv:2212.13409) was not available when §13 was integrated, so its Theorem 3.1 / 4.7 content there is unverified at this repository (§13's provenance note).  It is the one external dependency of §13 that should be re-checked against the paper.
7. Items 4–8 above were derived without the manuscript.  Once the draft is available, what remains is statement-level reconciliation — does each verdict above answer the manuscript's actual statement, under its definitions and conventions, and where do the two arguments disagree?  The specific points to reconcile: what ambient and pointclass its Theorem 3.4 quantifies over and whether its component statement is the one proved in §9; whether its Theorem 3.8 carries the completely-metrizable hypothesis that §11.5 shows to be necessary; which clauses of Ishiki Theorem 1.1 it invokes, given §11.3; whether its Appendix A argument establishes the ambient-level transfer that §10.7 identifies as the missing step; and the ten non-Archimedean questions of §13.10, of which the extensor provenance (item 6), the hypothesis on `X` (item 7) and which metric `UMet(X;R)` carries (item 1) are the ones that change what the theorems assert.
8. Whether the density of the parameter set survives in Proposition 2.1/2.2 is now a question for the authors rather than a proof detail: neither track consumes it (§9.6, §13.2), and dropping it would also remove the need to adjoin a countable dense `Q` in the `ℵ₁<𝔠` branch of §2.  It is a change to those statements, not to their proofs.
9. §7's audit targets are now all answered: items 3, 4, 5 in §§9–11, item 7 in §12, item 6 in §13.  Items 1 and 2 of that list — the ambient convention and `(★)` — remain the two open questions, and they are the same two that gate everything else.
