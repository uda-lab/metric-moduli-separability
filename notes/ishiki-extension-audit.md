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
- **Density of `S` is not used** anywhere in §§4–5 or §9.  The coding needs only an injective `ℵ₁`-enumeration `{w_α}` of `S`.  Density is a property of the parameter set that the descriptive-set-theoretic argument never consumes; if the manuscript carries it into Theorems 3.3/3.4 it is decorative there (it may still be needed elsewhere, e.g. in the non-Archimedean track, which this pass did not examine).

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

## 13. Standing gaps after §§9–12

1. §1 (ambient convention) still gates the pointclass statements of §§9–11.  It does **not** gate §12.3 route 1.
2. `(★)` of §2 still gates the "not analytic" half of Theorems 3.3/3.4/3.5/3.8.  It gates nothing in §12.
3. Ishiki Theorem 1.1(4) must be quoted as `(4′)` with the completely-metrizable hypothesis (§11.3); the authors should be told, since the defect is in the published preprint.
4. Items 4–6 and 8 above were derived without the manuscript.  Once the draft is available, what remains is statement-level reconciliation — does each verdict above answer the manuscript's actual statement, under its definitions and conventions, and where do the two arguments disagree?  The specific points to reconcile: what ambient and pointclass its Theorem 3.4 quantifies over and whether its component statement is the one proved in §9; whether its Theorem 3.8 carries the completely-metrizable hypothesis that §11.5 shows to be necessary; which clauses of Ishiki Theorem 1.1 it invokes, given §11.3; and whether its Appendix A argument establishes the ambient-level transfer that §10.7 identifies as the missing step.
5. §7 items 3, 4 and 5 (Theorems 3.4, 3.5/3.6, 3.7/3.8) and item 7 (Koshino) are answered in §§9–12; item 6 (non-Archimedean) is still open and is being derived separately.
