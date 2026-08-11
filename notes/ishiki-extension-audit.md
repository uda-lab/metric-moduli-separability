# Ishiki extension audit

> **Status:** in progress.  
> **Scope:** theorem-by-theorem mathematical audit for Issue #46.  
> **Policy:** a manuscript statement is not accepted merely because it appears in the draft.  Definitions, ambient conventions, and load-bearing external results are checked before Lean work begins.

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

This is not a harmless omission.  Outside Polish spaces, several generalisations of `analytic` occur in the literature.  In particular, the classical continuous-image-of-Polish definition produces only separable analytic spaces and is therefore not suitable as an unqualified nonseparable ambient convention.

### Candidate repair

For an arbitrary metrizable ambient space `Y`, explicitly define a subset `A ⊆ Y` to be **Souslin-F / relative analytic** when it is obtained by the Souslin `A`-operation from closed subsets of `Y`; define coanalytic by complement in `Y`.

Advantages for the present proof:

1. in a Polish ambient this agrees with the classical analytic (`Σ¹₁`) notion;
2. continuous inverse images are immediate, because inverse images preserve closed sets and commute with the Souslin operation;
3. the whole-parameter metric coding then gives a direct pullback contradiction from `[0,1]` or `2^ℕ`, where the classical perfect-set theorems apply;
4. no descriptive-set-theoretic regularity theorem is required for the nonseparable ambient itself.

Terminology varies between sources (`analytic`, `Souslin`, `absolute analytic`, relative analytic), so the manuscript should define the class rather than rely on the name alone.

### Sources consulted

- *Encyclopedia of Mathematics*, “Analytic set” and “Descriptive set theory”: the classical notion is explicitly distinguished from general metric/topological extensions, and the nonseparable metric case is discussed in terms of `A`-sets / Souslin operation.
- General-topology literature on absolute/Souslin-F analyticity confirms that terminology is not uniform.

A stronger primary/reference citation should be chosen before manuscript wording is recommended to the authors.

---

## 2. Proposition 2.1 — dense bad parameter set in `[0,1]`

### Verdict: **PASS**

Claim: there is a dense `S ⊆ [0,1]` with `|S|=ℵ₁` that is neither analytic nor coanalytic.

### CH case

Take a Bernstein set `S ⊆ [0,1]` of cardinality `𝔠=ℵ₁`.

- `S` is dense because every nonempty relatively open interval contains a nonempty perfect subset, which must meet `S`.
- `S` contains no nonempty perfect subset: if `K ⊆ S` were perfect, the Bernstein condition would require `K\S ≠ ∅`.
- likewise the complement contains no nonempty perfect subset.
- since `S` is uncountable, the perfect-set theorem for analytic and coanalytic subsets of a Polish space rules out both pointclasses.

### non-CH case

Here `ℵ₁<𝔠`.  Choose a countable dense `Q ⊆ [0,1]` and extend it to a set `S` with `|S|=ℵ₁`.

If `S` were analytic or coanalytic, the perfect-set property would give a nonempty perfect subset, hence cardinality `𝔠`, contradicting `|S|=ℵ₁<𝔠`.

### Remaining citation task

Verify the exact Kechris theorem numbers for:

- perfect-set theorem for analytic sets;
- perfect-set theorem for coanalytic sets;
- the cited Bernstein construction/cardinality claim.

The proof itself passes independently of theorem-number polishing.

---

## 3. Proposition 2.2 — Cantor-space parameter set

### Verdict: **FIX**

The current proof says the result follows from Proposition 2.1 because `[0,1]` and `2^ℕ` are Borel isomorphic.  This does not preserve the required **density**: a Borel isomorphism preserves the Borel structure, not the topology.

### Corrected proof

Work directly in Cantor space `2^ℕ`.

#### CH

Take a Bernstein subset `S ⊆ 2^ℕ` of cardinality `𝔠=ℵ₁`.

Each nonempty basic open set in `2^ℕ` is homeomorphic to `2^ℕ`, hence contains a nonempty perfect subset.  Therefore a Bernstein set meets every nonempty basic open set and is dense.  As in Proposition 2.1, `S` is neither analytic nor coanalytic.

#### non-CH

Choose a countable dense subset `Q ⊆ 2^ℕ` and extend it to `S` with `Q⊆S` and `|S|=ℵ₁`.

Then `S` is dense.  Since `ℵ₁<𝔠`, the perfect-set property of analytic and coanalytic subsets of the Polish space `2^ℕ` rules out either classification.

### Outcome

The proposition statement survives unchanged.  Only the proof should be replaced.

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

Hence every star has diameter at most `4`.  The restriction to a star is the tree metric with centre `b_α` and edge lengths `l_n`.  Distinct blocks are placed at distance `4`, so all mixed triangle inequalities are immediate.  The anchor block has diameter at most `2`.

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

The upper Lipschitz estimate gives `d_{t_k}→d_t`, so uniqueness of limits yields `d=d_t`.  Since `d` is compatible with the discrete topology, Lemma 3.1 forces `t∉S`.  Thus the image is closed in `BMet(X)`.

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

### Verdict: **BLOCKED only by the ambient convention**

Once §1 is repaired with a pointclass on arbitrary metrizable ambients that is preserved by continuous inverse images and agrees with classical `Σ¹₁/Π¹₁` on `[0,1]`, the theorem follows immediately from

```text
Φ_full⁻¹(BMet(X)) = [0,1]\S.
```

Indeed `[0,1]\S` is neither analytic nor coanalytic because `S` has neither property and the two classes are dual in the Polish ambient `[0,1]`.

This pullback proof is preferable to the draft's relatively-closed-copy argument because it exposes exactly which pointclass closure property is used and avoids ambient-dependent interpretation of a homeomorphic copy.

No independent defect has been found in the discrete metric construction.

---

## 7. Next audit targets

1. Fix/reference the nonseparable ambient pointclass convention.
2. Theorem 3.4 — finite-sup-distance component construction.
3. Theorem 3.5 / Corollary 3.6 — passage to a general nonseparable metrizable space via Ishiki's extensor.
4. Complete-metric branch.
5. Non-Archimedean branch.
6. Koshino consequence.

Lean work (#47) remains blocked until the theorem-level convention in §1 is fixed.
