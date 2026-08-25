# Borel preprint audit — arXiv:2608.19618 v1

> **Status:** complete (Issue #55).
> **Subject:** Y. Ishiki and T. Uda, *Borelness of Moduli Spaces of Metrics
> Implies Separability*, arXiv:2608.19618 v1 (20 Aug 2026). All statements were
> checked against the LaTeX source of v1.
> **Role:** this note is the active mathematical source of truth for the Borel
> track and the statement gate for the downstream Lean issues (#56, #57).
> Numbers such as "Theorem 3.3" are derived from the v1 source's `[section]`
> theorem counter; the LaTeX labels are the stable identifiers.
> **Policy:** a statement is not accepted because it appears in the preprint;
> every proof was re-derived. Verdicts: **PASS** (statement and proof check
> out), **FIX** (statement believed true; the written proof has a concrete,
> repairable gap, described in place), **EXTERNAL** (correct modulo an external
> theorem — published or arXiv, per-source status in §3 — quoted exactly
> there). A statement can be PASS/FIX *and* EXTERNAL.
> **Supersedes:** the 11 Aug analytic/coanalytic audit
> (`notes/ishiki-extension-audit.md` on branch `audit/ishiki-extension`),
> kept only as a historical record; see §5 for what must not be reinstated.

---

## 0. Summary verdict table

| # | label | statement (short) | track | verdict |
|---|-------|-------------------|-------|---------|
| 2.1 | `prop:dense-aleph1-nonborel-interval` | dense non-Borel `S ⊆ [0,1]`, `\|S\| = ℵ₁` | shared | **PASS** |
| 2.2 | `prop:dense-aleph1-nonborel-cantor` | same in `2^ω` | NA | **FIX** (density transfer) |
| 3.1 | `lem:metric-coding` | bounded star coding `d_t`, compatibility iff `t ∉ S` | A | **PASS** |
| 3.2 | `lem:closed-parameter-embedding` | `Φ` bi-Lipschitz, `Φ([0,1]∖S)` closed in `Met(Z)` | A | **PASS** |
| 3.3 | `thm:bounded-discrete-nonborel` | `BMet(Z)` non-Borel in `CPM(Z)` | A | **PASS** |
| 3.4 | `thm:metric-component-nonborel` | every component of `Met(Z)` non-Borel | A | **PASS** |
| 3.5 | `thm:borel-separability` | `Met(X)` Borel ⇒ `X` separable | A | **PASS + EXTERNAL** (Thm 1.1) |
| 3.6 | `cor:metric-space-complete-separability` | `Met(X)` completely metrizable ⇒ separable | A | **PASS + EXTERNAL** (Alexandrov) |
| 3.7 | `cor:bounded-metric-complete-sigma-compact` | `BMet(X)` compl. metrizable ⟺ `X` σ-compact | A | **FIX + EXTERNAL** (Koshino; Thm 1.1(3)) |
| 3.8 | `thm:complete-metric-nonborel` | `𝔠 ∩ Comp(Z)` and `Comp(Z)` non-Borel | A | **FIX** (complete base metric) |
| 3.9 | `cor:complete-metric-borel-separability` | `Comp(X)` Borel ⇒ separable (`X` compl. metr.) | A | **PASS + EXTERNAL** (Thm 1.1(4); assumes 3.8 repair) |
| 3.10 | `lem:ultrametric-coding` | ultrametric star coding, compatibility iff `t ∉ S` | NA | **PASS** |
| 3.11 | `lem:closed-ultrametric-parameter-embedding` | `Φ` isometric, closed image | NA | **PASS** |
| 3.12 | `thm:discrete-ultrametric-nonborel` | `UMet(Z;R)` non-Borel in `UCPM(Z;R)` | NA | **PASS** |
| 3.13 | `thm:ultrametric-component-nonborel` | every `R`-component non-Borel | NA | **PASS** |
| 3.14 | `thm:ultrametric-borel-separability` | `UMet(Y;R)` Borel ⇒ `Y` separable | NA | **FIX + EXTERNAL** (Thm 4.7) |
| 3.15 | `cor:ultrametric-space-complete-separability` | `UMet(Y;R)` compl. metrizable ⇒ separable | NA | **PASS** (assumes 3.14 repair) |
| 3.16 | `thm:complete-ultrametric-nonborel` | `𝔠^R ∩ UComp(Z;R)` non-Borel | NA | **PASS** |
| 3.17 | `cor:complete-ultrametric-borel-separability` | `UComp(Y;R)` Borel ⇒ separable | NA | **FIX + EXTERNAL** (Thm 4.7(N1)) |

A = Archimedean, NA = non-Archimedean. Every FIX has a concrete repair,
*checked in this audit*, recorded in §2; none threatens the truth of the
stated result. The FIXes in 3.14/3.17 share a single cause (§2.14).

**Verdict semantics (propagation).** Verdicts are *local*: each statement's
verdict assumes the statements it cites (per the graph in §4) hold **as
repaired**. Concretely: 3.10–3.13 and 3.16 consume only the *statement* of
2.2 (whose proof is FIX but whose repair is verified in §2.2); 3.9 consumes
3.8-as-repaired; 3.15 and 3.17 consume 3.14-as-repaired. A PASS on a
downstream item therefore means "no *new* gap introduced here", not
"unconditional"; any gate (in particular the Lean issues #56/#57) that
consumes a statement whose ancestors carry FIX must treat the recorded
repairs as part of the statement being gated. With the four repairs of
§§2.2, 2.10, 2.11, 2.14 admitted, every statement of the preprint has a
complete verified proof route; no BLOCKED-level defect remains — **the Borel
reformulation removes both blocking defects of the superseded draft** (§5).

---

## 1. Ambient conventions of the preprint

Recorded exactly, because the superseded draft failed here.

* `CPM(X)` — all continuous pseudometrics `d : X × X → [0,∞)` on a topological
  space `X` (individual values are finite), with the supremum metric
  `𝒟_X(d,e) = sup_{(x,y) ∈ X²} |d(x,y) − e(x,y)|`. **`𝒟_X` is
  `[0,∞]`-valued**; the preprint notes the topology is equivalently induced by
  the ordinary metric `min{𝒟_X, 1}`. `BCPM(X)` = bounded members.
* `Met(X)` ⊆ `CPM(X)` — metrics compatible with the topology of `X` (defined in
  the introduction); `BMet(X)` — its subspace of bounded metrics. No
  boundedness or uniform-discreteness restriction on `Met(X)` itself.
* `Comp(X)` = complete members of `Met(X)`.
* Components: `d ∼ e` iff `𝒟_X(d,e) < ∞`; `𝐌_{<∞}(Z) = Met(Z)/∼`; each class
  `𝔠` is clopen and (path-)connected in `Met(Z)`. (Recalled without citation in
  §2.2 of the preprint; elementary, re-derived here: openness from the radius-1
  ball, path-connectedness via convex combinations, which stay compatible.)
* Range sets: `R ⊆ [0,∞)` with `0 ∈ R`; *characteristic* iff `0` is an
  accumulation point of `R∖{0}`. `UCPM(X;R)` (`\youcpm`) — continuous `R`-valued
  pseudo-ultrametrics, with the non-Archimedean uniform metric
  `𝒰𝒟^R_X(d,e) = inf{ε ∈ R∪{∞} : d ≤ e ∨ ε and e ≤ d ∨ ε pointwise}` (again
  extended-valued). `UMet(Y;R)` (`\youltsp`) — compatible `R`-valued
  ultrametrics; `R`-components `𝔠^R ∈ 𝐔𝐌_{<∞}(Z;R)` via `𝒰𝒟^R < ∞`;
  `UComp(Y;R)` — complete members of `UMet(Y;R)`.

**Borel-in-nonseparable-ambient convention.**
"Borel in `CPM(X)`" means: member of the σ-algebra generated by the open sets
of the (typically nonseparable) metric topology of `CPM(X)`. Every
descriptive-set-theoretic step the preprint performs in the nonseparable
ambient is one of:

1. closed (or compact) sets are Borel — valid in any topological space;
2. intersection of a Borel set with a closed/Borel set is Borel;
3. **trace**: `B` Borel in `M` and `L ⊆ M` a subspace ⇒ `B ∩ L` Borel in `L`
   — valid in full generality (generator-level argument), no separability;
4. transfer along a homeomorphism (`L ≅ [0,1]` or `≅ 2^ω`, and pullback along
   an isometry of `CPM(Z)` onto a closed subspace of `CPM(X)`) — Borel
   σ-algebras are topological invariants.

All perfect-set-theoretic input is applied only inside the Polish spaces
`[0,1]`, `2^ω` (or homeomorphic compact copies `L`), never in the nonseparable
ambient. In addition, any competing "Borel" convention on a metric space
(Baire σ-algebra, ball σ-algebra) is contained in σ(open), so non-membership
in σ(open) is the strongest form.
This is exactly what the analytic/coanalytic version lacked (§5): the
classical `Σ¹₁/Π¹₁` pointclasses force separability and made the old
Theorem 3.3 vacuous, whereas the Borel σ-algebra needs no Polishness of the
ambient. **Verdict on the convention: PASS.**

One presentational observation (no defect): the theorems assert non-Borelness
in `CPM(Z)` / `UCPM(Z;R)`; by trace-monotonicity (3), non-Borelness in the
smaller ambients `BCPM(Z)` (for 3.3) and in any subspace containing the
witness compact `L` follows from the same argument, and conversely non-Borel
in `BCPM` implies non-Borel in `CPM`. This freedom is what lets the Lean
layer work in the bounded ambient (§7).

Relabelling convention: Theorems 3.3, 3.4, 3.8, 3.12, 3.13, 3.16 are stated
for an *arbitrary* discrete space `Z` with `|Z| = ℵ₁` while the proofs use the
specific coded carrier fixed before Lemma 3.1 (resp. 3.10). A bijection of
discrete spaces induces an isometry of `CPM`/`UCPM` preserving
`Met/BMet/Comp/UMet/UComp` and components (elementary: relabel both
arguments; every defining property is invariant), so this is sound; the
preprint leaves it implicit. Lean status: `Conj51/Relabel.lean` formalises
this reduction for `MetD` (the space `Met(D)` with its extended sup
distance — `relabelIsometry : MetD E ≃ᵢ MetD D`); `Ext/Relabel.lean`
*(delivered by #63)* formalises the corresponding `BddPMet`/`CPM` relabelling
isometries and the `BMet`/`Met` preimage identities, consumed by the
arbitrary-carrier forms of §7 item 4. The `UCPM` relabelling isometry and the
`UMet`/component preimage identities are in `Ext/UltraPMet.lean`
(`UCPM.isometry_comap`, `preimage_UMet_comap`, `preimage_UComponent_comap`),
*delivered by #81*, and carry the arbitrary-carrier forms of 3.12 and 3.13.
The Archimedean component-preservation lemmas for 3.8 and the `UComp` ones
(3.16) remain **not yet formalised**; neither gates #56/#57/#66.

---

## 2. Theorem-by-theorem audit

### 2.1 Proposition 2.1 (`prop:dense-aleph1-nonborel-interval`) — PASS

**Statement.** There exists a dense subset `S ⊆ [0,1]` with `Card(S) = ℵ₁`
that is not Borel in `[0,1]`. (ZFC; shared by both tracks.)

**Proof check.** Dichotomy on CH.
*CH:* `S` = a Bernstein subset of `[0,1]` (existence: Kechris, Example 8.24).
A Bernstein set meets every nonempty perfect set, hence is dense (every
nonempty relatively open interval contains a perfect set) and has cardinality
`𝔠` (it meets `𝔠` pairwise disjoint perfect sets); under CH, `𝔠 = ℵ₁`. If `S`
were Borel it would be an uncountable Borel set, so by the perfect set theorem
for Borel sets (Kechris, Theorem 13.6) it would contain a nonempty perfect
`K ⊆ S`, contradicting `K ∖ S ≠ ∅`. ✓
*¬CH:* fix countable dense `Q ⊆ [0,1]`, choose `S ⊇ Q` with `|S| = ℵ₁ < 𝔠`.
`S` is uncountable with `|S| < 𝔠`; a Borel `S` would be uncountable Borel and
hence of cardinality `𝔠` (Theorem 13.6). ✓
Both branches are ZFC; this is exactly the dichotomy that the superseded
analytic/coanalytic version could not run (§5). The density justification in
the CH case ("by the perfect set property") compresses the
meets-every-perfect-set argument; no gap.

**Note for Lean (§7):** density of `S` is used **only** in the
non-Archimedean track (Lemma 3.11's isometry lower bound); the entire
chain 3.1–3.9 uses only `|S| = ℵ₁` + non-Borel.

### 2.2 Proposition 2.2 (`prop:dense-aleph1-nonborel-cantor`) — FIX

**Statement.** Same as 2.1 with `[0,1]` replaced by the Cantor space
`2^ω`. (Used only by the non-Archimedean track.)

**Gap.** The written proof is "follows from the fact that `2^ω` is Borel
isomorphic to `[0,1]`". A Borel isomorphism transfers non-Borelness and
cardinality, but **not density** — density is a topological, not Borel,
property. (The identical defect was found in the superseded draft's
Proposition 2.2 and is inherited verbatim.)

**Repair (either suffices).**
1. Transfer + densify: pull `S₀` of 2.1 back through a Borel isomorphism to
   get `T ⊆ 2^ω` non-Borel with `|T| = ℵ₁`, then set `S = T ∪ Q₀` with `Q₀`
   countable dense in `2^ω`; `S` is dense, `|S| = ℵ₁`, and non-Borel (if `S`
   were Borel, `T = S ∖ (Q₀ ∖ T)` would be Borel-minus-countable, hence
   Borel).
2. Run the 2.1 dichotomy verbatim in `2^ω`: `2^ω` is a nonempty perfect
   Polish space, so Bernstein subsets exist and Theorem 13.6 applies; the ¬CH
   branch is unchanged.
Statement true in ZFC; the citation for the Borel isomorphism (Kechris,
Theorem 15.6, currently uncited) should be added if route 1 is kept.

**Lean** (`Ext/CantorUltra.lean`, #81): `exists_dense_aleph1_nonBorel_cantor`.
The non-Borel `T` comes from route 2's dichotomy run directly in `2^ω` (no
Bernstein set is needed in Lean, as in §7 item 1) and density from route 1's
`S = T ∪ Q₀`; the Borel isomorphism of the printed proof is not used.

### 2.3 Setup before Lemma 3.1

`S = {w_α : α < ω₁}` an injective enumeration of the set from 2.1;
`Z = {p,q} ⊔ {b_α : α<ω₁} ⊔ {c_{α,n} : α<ω₁, n ∈ ℤ_{≥0}}` with the discrete
topology, `C_α = {b_α} ⊔ {c_{α,n} : n}`; `|Z| = ℵ₁`. ✓ (`2 + ℵ₁ + ℵ₁·ℵ₀ = ℵ₁`.)

### 2.4 Lemma 3.1 (`lem:metric-coding`) — PASS

**Statement.** For `t ∈ [0,1]`, with spoke lengths
`l_n(α,t) = |t − w_α| + 2^{−n}`, define `d_t` by: `d_t(p,q) = 1+t`;
`d_t(b_α, c_{α,n}) = l_n(α,t)`; `d_t(c_{α,n}, c_{α,m}) = l_n + l_m` (`n ≠ m`);
`d_t(u,v) = 4` for `u,v` in different blocks of
`{{p,q}} ∪ {C_α}`; `d_t(u,u) = 0`. Then `d_t` is a bounded metric on the
underlying set of `Z`, and `d_t ∈ Met(Z) ⟺ t ∈ [0,1] ∖ S`.

**Proof check.** `0 < l_n ≤ 2`, so each star (hedgehog with centre `b_α`) has
diameter ≤ 4 and the anchor block diameter ≤ 2; within-block star triangle
inequality is standard; mixed triples work because cross-block distance is
exactly 4 ≥ diameters and ≤ 4+4. Values in `[0,4]`, positivity off-diagonal
holds for *every* `t` (including `t ∈ S`, where `d_t(b_β,c_{β,n}) = 2^{−n} >
0`) — this totality is what makes the full parameter map of 3.2 well defined.
Compatibility: for `t ∉ S`, isolation radii are `1` at `p,q`, `l_n(α,t) ≥
2^{−n}` at `c_{α,n}`, `inf_n l_n(α,t) = |t − w_α| > 0` at `b_α`; for
`t = w_β ∈ S`, `d_t(b_β, c_{β,n}) = 2^{−n} → 0`, so `b_β` is not isolated. ✓
Identical (up to relabelling of the star index) to the construction already
re-derived twice in this repo (superseded audit §4, verdict PASS) and
formalised sorry-free in Lean (§6).

### 2.5 Lemma 3.2 (`lem:closed-parameter-embedding`) — PASS

**Statement.** `Φ : [0,1] → CPM(Z)`, `Φ(t) = d_t`, is a bi-Lipschitz
embedding, and `Φ([0,1] ∖ S)` is closed in `Met(Z)`.

**Proof check.** Lower bound `|s−t| ≤ 𝒟_Z(d_s,d_t)` by evaluation at `(p,q)`;
upper bound `𝒟_Z(d_s,d_t) ≤ 2|s−t|` since each table entry is 1- or
2-Lipschitz in `t` and cross-block entries are constant. Closedness: if
`d_{t_k} → d ∈ Met(Z)` with `t_k ∈ [0,1]∖S`, the anchor recovers
`t_k → t := d(p,q) − 1 ∈ [0,1]`; the upper Lipschitz bound gives `d = d_t`;
`d` compatible + Lemma 3.1 force `t ∉ S`. ✓ (Same status in the superseded
audit §5; formalised, §6.) Note the two byproducts used later: `L :=
Φ([0,1])` is compact (hence closed/Borel in `CPM(Z)`), and the exact
trace identity `L ∩ Met(Z) = L ∩ BMet(Z) = Φ([0,1]∖S)` (all `d_t` are
bounded, and `d_t` compatible ⟺ `t ∉ S`).

### 2.6 Theorem 3.3 (`thm:bounded-discrete-nonborel`) — PASS

**Statement.** `Z` discrete, `|Z| = ℵ₁` ⇒ `BMet(Z)` is non-Borel in `CPM(Z)`.

**Proof check.** Suppose `BMet(Z)` Borel in `CPM(Z)`. `F := Φ([0,1]∖S)` is
closed in `BMet(Z)` (closed in `Met(Z)` by 3.2 and contained in `BMet(Z)`),
so `F = C ∩ BMet(Z)` for some closed `C ⊆ CPM(Z)`, hence `F` is Borel in
`CPM(Z)`; since `F ⊆ L` and `F = L ∩ BMet(Z)`, `F` is Borel in the compact
`L ≅ [0,1]` (trace), transporting to `[0,1]∖S` Borel — contradiction
with 2.1. Every step is in the §1-verified list; no Polishness of the ambient
is used. ✓

**Presentation note (introduction/abstract vs body).** The abstract and
introduction announce "`Met(Z)` is not Borel", citing this theorem, but 3.3
literally states the `BMet(Z)` version. Both are true by the *same* proof —
the trace identity of §2.5 holds with `Met(Z)` in place of `BMet(Z)`, and 3.2
gives closedness in `Met(Z)` directly — but the `Met(Z)` version is stated
nowhere in the body. Recommend stating both (or a remark) in a revision; for
Lean, formalise both from the single pullback identity (§7).

### 2.7 Theorem 3.4 (`thm:metric-component-nonborel`) — PASS

**Statement.** `Z` discrete, `|Z| = ℵ₁` ⇒ every component
`𝔠 ∈ 𝐌_{<∞}(Z)` is non-Borel in `CPM(Z)`.

**Proof check.** Fix `d ∈ 𝔠`, `z ∈ Z`. Some closed `d`-ball
`E = {x : d(z,x) ≤ h}`, `h ∈ ℤ_{≥1}`, has `|E| = ℵ₁` (countable union
exhausts `Z`; `ℵ₁` is regular). Transfer the 3.1 family to `E` by a bijection
`θ` with `θ(p) = z`, getting `e_t` with `e_t ∈ Met(E) ⟺ t ∉ S`. Amalgamate
with `d` along the single common point `z`:
`m_t(x,a) = d(x,z) + e_t(z,a)` for `x ∉ E`, `a ∈ E` — a metric (one-point
amalgamation), compatible iff `t ∉ S` (isolation radii as in 3.1 on the `E`
side, `d`-isolation outside, cross-distances ≥ max(d(x,z), e_t(z,a)) with
`e_t(z,·) ≥ 1`). Bi-Lipschitz estimates via evaluation at `(z, q_E)`;
closedness of `Ψ([0,1]∖S)` in `𝔠` as in 3.2. Trace: for the compact
`L' = Ψ([0,1])`, `L' ∩ 𝔠 = Ψ([0,1]∖S)`, then argue as in 3.3. ✓

Two steps are implicit but immediate; recorded for the Lean layer:
(i) `m_t ∈ 𝔠` for `t ∉ S`, i.e. `𝒟_Z(m_t, d) < ∞`: on `E²` both metrics are
bounded (`e_t ≤ 4`, `d ≤ 2h`), cross terms differ from `d` by at most
`4 + h`, outside they agree; (ii) `m_t ∈ 𝔠 ⟺ t ∉ S` for the trace identity
(membership in `Met(Z)` is the only condition, by (i)). ✓

### 2.8 Theorem 3.5 (`thm:borel-separability`) — PASS + EXTERNAL

**Statement.** `X` metrizable; if `Met(X)` is Borel in `CPM(X)`, then `X` is
separable.

**Proof check.** Contrapositive: `X` nonseparable. Standard separated-set
argument (maximal `1/n`-separated sets; if all countable, their union is
countable dense) yields an `ε`-separated, hence **closed discrete**, subspace
`Z ⊆ X` with `|Z| = ℵ₁`. By EXTERNAL **E1** (Ishiki 2024, Theorem 1.1; exact
quote §3) there is an isometric extensor `Ẽ : CPM(Z) → CPM(X)` of
pseudometrics restricting to `E : Met(Z) → Met(X)`. `CPM(Z)` is complete
(uniform limits of continuous pseudometrics; w.r.t. `min{𝒟,1}`), so the
isometric image `Ẽ(CPM(Z))` is closed in `CPM(X)`. The identity
`E(Met(Z)) = Ẽ(CPM(Z)) ∩ Met(X)` holds (the preprint re-derives it from the
extension property `Ẽ(d)|_{Z²} = d` plus restriction-preserves-compatibility;
E1 even states it verbatim), so `E(Met(Z))` is closed in `Met(X)`, and for a
fixed component `𝔠` (clopen in `Met(Z)`), `E(𝔠)` is closed in `Met(X)` and
isometric to `𝔠`. If `Met(X)` were Borel in `CPM(X)`, then `E(𝔠)` (closed in
the Borel set `Met(X)`) would be Borel in `CPM(X)`; pulling back along the
homeomorphism `Ẽ` onto its closed image (trace + homeomorphism, §1) makes `𝔠`
Borel in `CPM(Z)`, contradicting 3.4. ✓ The pullback step is left implicit in
the preprint; it is the §1 argument.

**Scoping observation (not a defect).** The proof works verbatim with
`Met(Z)` itself in place of the component `𝔠` (using `E(Met(Z))` closed and
the `Met(Z)` version of 3.3 noted in §2.6), so the minimal verified chain for
3.5 does **not** need Theorem 3.4. Theorem 3.4 stands as a finer independent
result, and is not a prerequisite of the #57 Lean package (§7).

### 2.9 Corollary 3.6 (`cor:metric-space-complete-separability`) — PASS + EXTERNAL

**Statement.** `X` metrizable; if `Met(X)` is completely metrizable, then `X`
is separable.

**Check.** No proof is given in the preprint. The intended (and correct)
derivation: a completely metrizable subspace of a metric space is `G_δ` in it
(Alexandrov–Lavrentiev, valid for arbitrary metrizable ambient — Kechris,
Theorem 3.11; already number-verified in this repo, `notes/literature.md`),
hence `Met(X)` is Borel in `CPM(X)`; apply 3.5. Recommend adding the proof
with the citation. This corollary is what settles Conjecture 5.1 (Ishiki
2024, §5) in the strengthened Borel form.

### 2.10 Corollary 3.7 (`cor:bounded-metric-complete-sigma-compact`) — FIX + EXTERNAL

**Statement.** `X` metrizable: `BMet(X)` is completely metrizable ⟺ `X` is
σ-compact.

**Gap.** The preprint derives this by "combining" EXTERNAL **E3** (Koshino:
for *separable* metrizable `X`, `X` σ-compact ⟺ `AM(X) = BMet(X)` completely
metrizable) with Corollary 3.6. The (⇐) direction is fine: σ-compact
metrizable ⇒ separable, then Koshino. The (⇒) direction needs "`BMet(X)`
completely metrizable ⇒ `X` separable" to enter Koshino's hypothesis — but
3.6 provides this for `Met(X)`, **not** `BMet(X)`, and neither implies the
other formally (`BMet(X)` is a clopen union of components of `Met(X)`; no
complete-metrizability transfer in either direction).

**Repair (uses only tools already in the paper).** Prove the `BMet` analogue
of 3.5: if `BMet(X)` is Borel in `CPM(X)` and `X` nonseparable, take `Z` as
in 3.5; Theorem 1.1(3) (E1) gives `E(BMet(Z)) ⊆ BMet(X)`, and
`E(BMet(Z)) = Ẽ(CPM(Z)) ∩ BMet(X)` (restriction of a bounded metric is
bounded), so `BMet(X)` Borel ⇒ `BMet(Z)` Borel in `CPM(Z)` by the same
pullback — contradicting 3.3 directly (no components needed). Then:
`BMet(X)` completely metrizable ⇒ `G_δ` in `CPM(X)` (Alexandrov, as in 3.6)
⇒ Borel ⇒ `X` separable ⇒ Koshino. Statement true; the missing link is a
lemma to state explicitly in a revision.

**Citation caveat (E3).** The preprint cites "[Corollary 1.2]" of Koshino,
but this repo's verified literature record (`notes/literature.md`, checked
against the arXiv v2 = published text on 2026-08-10) found the paper's main
Theorem and Corollary **unnumbered**. Verify the citation number against the
published AGMS version before submission. Also note Koshino's object is
`AM(X)` (bounded *admissible* metrics, sup-metric) — identical to `BMet(X)`;
the identification is legitimate here, unlike the `Met(X)` recollection
warned about in `notes/literature.md`.

### 2.11 Theorem 3.8 (`thm:complete-metric-nonborel`) — FIX

**Statement.** `Z` discrete, `|Z| = ℵ₁`: for every component
`𝔠 ∈ 𝐌_{<∞}(Z)`, `𝔠 ∩ Comp(Z)` is non-Borel in `CPM(Z)`; consequently
`Comp(Z)` is non-Borel.

**Gap.** The proof asserts that the metrics `m_t` of 3.4 are complete for
`t ∉ S`. For the *coding* part this is right (`d_t` is complete for `t ∉ S`:
cross-block distance 4 confines Cauchy sequences to one block, and within
`C_α` distances are ≥ `2|t−w_α| > 0`, resp. ≥ `|t−w_α|`, so Cauchy sequences
are eventually constant). But `m_t` restricted to `(Z∖E) ∪ {z}` is the
**arbitrary** base metric `d ∈ 𝔠`, which need not be complete — e.g. `𝔠` the
component of a compatible metric embedding a countable subset of `Z` as
`{1/n} ⊆ ℝ`; then `m_t` inherits the non-convergent Cauchy sequence and is
*not* complete for any `t`. As written, the claim "m_t … complete if `t ∉ S`"
is false for such `𝔠`.

**Repair (the non-Archimedean analogue 3.16 already does exactly this).**
Before running the 3.4 construction, replace the base point by a complete
member of the same component: `d' := d + 1` off the diagonal is a
compatible complete metric with `𝒟_Z(d,d') = 1 < ∞`, so `d' ∈ 𝔠`. With base
`d'`, the amalgam `m_t` (`t ∉ S`) is complete: Cauchy sequences either stay
in `E` (complete by the coding), stay outside (eventually constant,
off-diagonal ≥ 1), or converge to `z`. The rest of the proof is unchanged,
including the "consequently" part: the trace `L' ∩ Comp(Z) = L' ∩ (𝔠 ∩
Comp(Z)) = Ψ([0,1]∖S)` (for `t ∈ S`, `m_t ∉ Met(Z) ⊇ Comp(Z)`), so a Borel
`Comp(Z)` — or a Borel `𝔠 ∩ Comp(Z)` — yields the same `[0,1]∖S`-Borel
contradiction. (The "consequently" does **not** follow by intersecting with
`𝔠`, which is itself non-Borel; the trace route above is the correct reading
of "the same argument".)

### 2.12 Corollary 3.9 (`cor:complete-metric-borel-separability`) — PASS + EXTERNAL

**Statement.** `X` **completely metrizable**; if `Comp(X)` is Borel in
`CPM(X)`, then `X` is separable.

**Proof check.** `X` nonseparable ⇒ closed discrete `Z`, `|Z| = ℵ₁`, as in
3.5. E1 with clause (4) — completeness preservation, legitimate here because
`X` is assumed completely metrizable (see the E1 caveat in §3) — gives
`E(Comp(Z)) ⊆ Comp(X)`; conversely a complete compatible metric on `X`
restricts to a complete compatible metric on the closed `Z`, so
`E(Comp(Z)) = E(Met(Z)) ∩ Comp(X)`, closed in `Comp(X)`. For a component
`𝔠`, `E(𝔠 ∩ Comp(Z)) = E(𝔠) ∩ Comp(X)` is closed in `Comp(X)` and isometric
to `𝔠 ∩ Comp(Z)`. If `Comp(X)` were Borel, the ambient pullback along `Ẽ`
(available at CPM level, E1 "furthermore") makes `𝔠 ∩ Comp(Z)` Borel in
`CPM(Z)`, contradicting 3.8 (as repaired). ✓ Nonemptiness of `𝔠 ∩ Comp(Z)`
is part of 3.8's conclusion (non-Borel sets are nonempty). The corollary
inherits the FIX of 3.8 but adds no gap of its own; the component-free
variant (via `Comp(Z)` non-Borel) again suffices, cf. §2.8.

### 2.13 Coding by ultrametrics: Lemma 3.10, Lemma 3.11 — PASS

Setup: characteristic `R`, strictly decreasing `r : ℕ → R∖{0}`, `r(n) → 0`
(exists exactly because `R` is characteristic); `h(s,t) = r(min{n : s(n) ≠
t(n)})` the standard `R`-valued ultrametric on `2^ω` inducing the product
topology; `S ⊆ 2^ω` from 2.2 (dense is **used** here); carrier
`Z = ⊔_{α<ω₁} C_α`, `C_α = {y_α} ⊔ {x_{α,n}}`.

**Lemma 3.10 (`lem:ultrametric-coding`).** With
`l_n(α,t) = h(t,w_α) ∨ r(n)`: star values within `C_α`
(`d_t(y_α,x_{α,n}) = l_n`, `d_t(x_{α,n},x_{α,m}) = l_n ∨ l_m`), `r(0)`
across clusters. Checked: values lie in `R`; max-star + constant-across is an
`R`-valued ultrametric (all intra-cluster values ≤ `r(0)`); compatibility for
`t ∉ S` via isolation radii `≥ min(l_n, r(0))` at spokes and
`inf_n l_n = h(t,w_α) > 0` at centres; failure at `t = w_β` via
`d_t(y_β,x_{β,n}) = r(n) → 0`; completeness for `t ∉ S` (Cauchy sequences
confined to one cluster, intra-cluster distances ≥ `h(t,w_α) > 0`). PASS. ✓

**Lemma 3.11 (`lem:closed-ultrametric-parameter-embedding`).**
`Φ(t) = d_t` is a `𝒰𝒟^R`-**isometry**: `≤ h(s,t)` from the strong triangle
inequality `l_n(α,s) ≤ l_n(α,t) ∨ h(s,t)`; `≥` via **density of `S`**
(choose `w_α` with `h(s,w_α) < ρ := h(s,t)`, then the isosceles property
gives `h(t,w_α) = ρ`, and `n` with `r(n) < ρ` witnesses
`d_s(y_α,x_{α,n}) < ρ = d_t(y_α,x_{α,n})`). Closedness of `Φ(2^ω ∖ S)` in
`UMet(Z;R)`: a `𝒰𝒟^R`-limit forces `(t_k)` Cauchy in compact `(2^ω,h)`,
limit `d = d_t`, compatibility forces `t ∉ S`. PASS. ✓

**Lean** (`Ext/UltraCoding.lean`, #81): 3.10 is `dU_isUltraPMetOn`,
`dU_le_head`, `isCompatible_phiU_iff` and `dU_completeSpace`; 3.11 is
`edist_phiU` (both bounds, the lower one through `exists_separating_pair`,
which consumes `Dense S`) and `isClosed_image_phiU`.

### 2.14 Theorems 3.12–3.14, Corollary 3.15

**Theorem 3.12 (`thm:discrete-ultrametric-nonborel`) — PASS.**
`UMet(Z;R)` non-Borel in `UCPM(Z;R)`: `L = Φ(2^ω)` is compact (isometric
image of compact), `L ∩ UMet(Z;R) = Φ(2^ω∖S)` is relatively closed by 3.11,
trace argument as in 3.3 with `2^ω` in place of `[0,1]`. ✓ (Relabelling
implicit as in §1; a stray comma in the statement, editorial.)

**Theorem 3.13 (`thm:ultrametric-component-nonborel`) — PASS.** Mirror of
3.4: `R ⊆ [0,∞)` has a countable cofinal subset and `d` is `R`-valued, so
some closed ball `E` (radius `q ∈ R`) has `|E| = ℵ₁` (regularity of `ℵ₁`);
transfer 3.10 with the centre `y_0 ↦ z`; ultrametric one-point amalgam
`m_t(x,a) = d(x,z) ∨ e_t(z,a)` (checked: strong triangle inequality in all
mixed cases; `R`-valued). Membership `m_t ∈ 𝔠^R` for `t ∉ S` is stated with
the correct bound `𝒰𝒟^R(m_t,d) ≤ q ∨ r(0)` (checked: on `E²` both ≤ `q ∨
r(0)`; cross terms *equal* `d(x,a)` when `d(x,z) ≥ r(0)`, both ≤ `q ∨ r(0)`
otherwise, using the ultrametric isosceles `d(x,a) = d(x,z)` for `d(x,z) > q
≥ d(z,a)`). Isometry `𝒰𝒟^R(m_s,m_t) = h(s,t)` (coding clusters all inside
`E`); compatibility ⟺ `t ∉ S` (`d(x,z) > q` outside `E` restores isolation);
closed image in `𝔠^R`; trace as before. ✓

**Lean** (#81): 3.12 is `umet_not_borel_of_card` (`Ext/UltraCoding.lean`) and
3.13 is `ucomponent_not_borel_of_card` (`Ext/UltraComponent.lean`), both on an
arbitrary discrete carrier of cardinality `ℵ₁`; the audited bound
`𝒰𝒟^R(m_t,d) ≤ q ∨ r 0` is `edist_uAmalgam_le`. 3.14 and 3.15 are #82; see
the Lean notes after each statement below.

**Theorem 3.14 (`thm:ultrametric-borel-separability`) — FIX + EXTERNAL.**
*Statement.* `Y` ultrametrizable; if `UMet(Y;R)` is Borel in `UCPM(Y;R)`,
then `Y` is separable.
*What checks out.* Nonseparable `Y` gives closed discrete `Z`, `|Z| = ℵ₁`
(separated sets, as in 3.5). EXTERNAL **E2** (Ishiki 2023, Theorem 4.7;
quote §3) gives an isometric extensor `E : UMet(Z;R) → UMet(Y;R)` (the
restriction to `UMet(Z;R)` of E2's `Σ : Met(Z) → Met(Y)`, using clauses (1),
(2), (5)). Closedness of the image in `UMet(Y;R)` is proved via
the restriction map and the extension property; `E(𝔠^R)` closed in
`UMet(Y;R)`, isometric to `𝔠^R`. ✓
*Gap.* The final step "if `UMet(Y;R)` were Borel, this would contradict
3.13" needs a pullback of Borelness from `UCPM(Y;R)` to `UCPM(Z;R)`. In the
Archimedean 3.5 this is available because E1 extends to the **pseudometric
ambient** (`Ẽ : CPM(Z) → CPM(X)`); E2 has **no `UCPM`-level extensor** — its
domain is `Met(Z)` — so the isometry `E` cannot transport the ambient Borel
σ-algebra, and "Borel in `UCPM(Y;R)`" is not an intrinsic property of the
subspace `E(𝔠^R)` (any space is closed in itself).
*Repair (uses only the paper's results; each step proved here).* Work
with the compact witness instead of the component. `F := E(Ψ(2^ω∖S))` is
closed in `UMet(Y;R)` (image of the closed set of 3.13 under the
homeomorphism-onto-closed-image `E`), and `ι := E ∘ Ψ : (2^ω∖S, h) → F` is
an isometry (3.13 isometry composed with E2(2)).

*Sub-lemma (completeness of `UCPM(Y;R)`, every characteristic `R`).*
(i) `𝒰𝒟^R(d,e) ≤ ε` implies `|d(x,y) − e(x,y)| ≤ ε` for every pair: from
`d(x,y) ≤ e(x,y) ∨ ε`, either `d ≤ e` or `d ≤ ε`; in both cases
`d − e ≤ ε`, and symmetrically. So a `𝒰𝒟^R`-Cauchy sequence `(d_k)` is
uniformly Cauchy and has a uniform limit `d_∞`, which is a continuous
pseudometric satisfying the strong triangle inequality (pointwise limit of
max-inequalities). (ii) `d_∞` is `R`-valued: fix a pair `(x,y)` and set
`v_k := d_k(x,y) ∈ R`, `v := lim v_k`. If `v = 0` then `v ∈ R`. If `v > 0`,
pick `ε ∈ R∖{0}` with `ε < v` (`R` characteristic); for large `j,k` the
defining inequalities give `v_k ≤ v_j ∨ ε` and `v_j ≤ v_k ∨ ε` while
`v_j, v_k > ε`, forcing `v_j = v_k` — the values are eventually constant, so
`v ∈ R`. (iii) `𝒰𝒟^R(d_j, d_∞) → 0`: given `ε ∈ R∖{0}`, for large `j` and
all `k ≥ j`, `d_j ≤ d_k ∨ ε` and `d_k ≤ d_j ∨ ε` pointwise; let `k → ∞` to
get `d_j ≤ d_∞ ∨ ε` and `d_∞ ≤ d_j ∨ ε`, i.e. `𝒰𝒟^R(d_j,d_∞) ≤ ε`. ∎

Now extend: `ι` is an isometry from `2^ω∖S`, dense in the compact
`P := cl_{2^ω}(2^ω∖S)`, into the complete space `UCPM(Y;R)`, hence extends
uniquely to an isometry `ῑ : (P,h) → UCPM(Y;R)` (uniform continuity +
completeness; the extension is isometric and in particular injective, by
continuity of the two distance functions). `K := ῑ(P)` is compact and
`ῑ : P → K` is a homeomorphism.

*Claim: `K ∩ UMet(Y;R) = F`.* `⊇` by construction (`ῑ = ι` on `2^ω∖S`). For
`⊆`: take `t ∈ P` with `ῑ(t) ∈ UMet(Y;R)`; choose `t_k ∈ 2^ω∖S`, `t_k → t`;
then `ι(t_k) → ῑ(t)` *inside* `UMet(Y;R)`, and `F` is closed in
`UMet(Y;R)`, so `ῑ(t) ∈ F = ι(2^ω∖S)`; injectivity of `ῑ` gives
`t ∈ 2^ω∖S`. ∎

Conclusion: if `UMet(Y;R)` were Borel in `UCPM(Y;R)`, then
`F = K ∩ UMet(Y;R)` would be Borel in the compact metric (hence Polish)
space `K ≅ P` (trace, §1), so `ῑ⁻¹(F) = P∖S` would be Borel in `P`; `P` is
closed in `2^ω`, so `P∖S = 2^ω∖S` would be Borel in `2^ω` — contradicting
2.2. (No co-density of `S` is assumed; passing to `P` handles that.)
This explicit extension argument is the *sole* verified repair; there is no
route via "separable metrizable spaces are absolutely Borel" — that is
false, and `F ≅ 2^ω∖S` is itself a counterexample (non-Borel in `2^ω`).
Statement true; the transfer argument above must be added to the paper, and
a Lean formalisation of 3.14 must formalise it (it is not extractable from
the paper's text).

**Lean** (#82, `Ext/UltraTransfer.lean`): the repair, not the printed proof.
`ultraExtend` is `ῑ` — the dense-uniform extension of `E ∘ Ψ`, available by
`completeSpace_UCPMOn`; `restrict_ultraExtend` propagates E2 clause (1) to the
closure and yields injectivity; `preimage_UMetOn_ultraExtend` is
`ῑ⁻¹(UMet(Y;R)) = P∖S`; `isCompact_range_ultraExtend` and
`range_ultraExtend_inter_UMetOn` are `K` and the trace identity. `P` appears
transported along `Φ` as `codingClosure = cl(Φ(2^ω∖S))`, with
`codingClosure_eq_image_closure` proving `= Φ(P)`; the theorem itself is
`separable_of_measurableSet_UMetOn_of_ultraExtensors`, and — as in 3.12–3.13 —
the last step is the pullback identity rather than the relative trace, for
which closedness of `P` is enough.

**Corollary 3.15 (`cor:ultrametric-space-complete-separability`) — PASS.**
From 3.14 via Alexandrov (`UMet(Y;R)` completely metrizable ⇒ `G_δ` in the
metrizable `UCPM(Y;R)` ⇒ Borel); proof omitted in the preprint, same remark
as 3.6. Inherits the 3.14 FIX, adds nothing.

**Lean** (#82): `separable_of_isCompletelyMetrizableSpace_UMetOn_of_ultraExtensors`,
through `measurableSet_of_isCompletelyMetrizableSpace` (E4d, #79).

### 2.15 Theorem 3.16, Corollary 3.17

**Theorem 3.16 (`thm:complete-ultrametric-nonborel`) — PASS.** For every
`𝔠^R`, `𝔠^R ∩ UComp(Z;R)` is non-Borel; consequently `UComp(Z;R)` is
non-Borel. The proof **does** perform the complete-base normalisation that
3.8 omits: `d ∨ c` off the diagonal (`c ∈ R∖{0}`) is a complete compatible
`R`-valued ultrametric in the same `R`-component (checked: `𝒰𝒟^R(d∨c, d) ≤
c`). The `e_t` are complete (3.10), and a one-point max-amalgam of two
complete ultrametric spaces is complete (Cauchy sequences either settle in
one side or converge to the glue point). Trace as in 3.8-repaired. ✓

**Corollary 3.17 (`cor:complete-ultrametric-borel-separability`) — FIX +
EXTERNAL.** `Y` ultrametrizable with `UComp(Y;R) ≠ ∅`; Borel (or completely
metrizable) `UComp(Y;R)` ⇒ `Y` separable. Checked: nonemptiness ⇒ `Y`
completely metrizable; E2 clause (N1) (quote §3) allows choosing the
extensor to preserve completeness, `E(UComp(Z;R)) = E(UMet(Z;R)) ∩
UComp(Y;R)` via restriction-to-closed-subspace, closedness and isometry as
before, conclude by 3.16. The completely-metrizable variant goes through
Alexandrov as in 3.15. Inherits exactly the 3.14 ambient-transfer FIX (same
repair, with `Ψ` replaced by the 3.16 witness); no further gap.

---

## 3. External dependencies (exact statements)

**E1 — Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030 (v4),
Theorem 1.1.** Verified against the arXiv source (retrieved for this audit).
Statement: *Let `X` be a metrizable space and `A` a closed subset of `X`.
Then there exists a map `E : Met(A) → Met(X)` such that (1) `E(d)|_{A²} = d`
for every `d ∈ Met(A)`; (2) `E` is an isometric embedding:
`𝒟_A(d,e) = 𝒟_X(E(d),E(e))`; (3) `E(BMet(A)) ⊆ BMet(X)`; (4)
`E(Comp(A)) ⊆ Comp(X)`. Furthermore there is an isometric extensor
`Ẽ : CPM(A) → CPM(X)` of pseudometrics with `Ẽ|_{Met(A)} = E`; in this
setting `Ẽ(Met(A)) = Ẽ(CPM(A)) ∩ Met(X)`, and the image `E(Met(A))` is
closed in `Met(X)`.*
Used by: 3.5 (clauses 1, 2, furthermore), 3.7-repair (clause 3), 3.9
(clause 4). **Caveat on clause (4):** as literally stated it is unconditioned
on `X`, but it cannot hold when `Comp(X) = ∅` while `Comp(A) ≠ ∅` (e.g.
`X = ℚ`, `A = {0}`); the source's own proof (its Proposition `prop:jxclosed`)
carries the hypothesis "`X` completely metrizable", and the choice of
auxiliary complete metrics is made under that hypothesis. The preprint uses
(4) only in 3.9, where `X` is assumed completely metrizable, so the usage is
sound — but the dependency should be recorded as "(4) under `X` completely
metrizable", and the misstatement is worth reporting.

**E2 — Ishiki, *A factorization of metric spaces*, Colloq. Math. 174 (2023),
101–120 (arXiv:2212.13409), Theorem 4.7.** Verified against the full text on
disk (`fact.txt`). Statement (specialised to what is used): *Let `X` be an
ultrametrizable space, `F` a nonempty closed subset, `S` a characteristic
subset of `[0,∞)` (the preprint's `R`), `v ∈ UMet(X/F; S)`; then
`Σ : Met(F) → Met(X)`, `Σ(d) = Φ*(d ×_∞ v)`, satisfies (1)
`Σ(d)|_{F²} = d`; (2) `𝒰𝒟^S_X(Σ(d),Σ(e)) = 𝒰𝒟^S_F(d,e)` (isometric); (3)
monotone; (4) `Σ(d ∨ e) = Σ(d) ∨ Σ(e)`; (5) `Σ(UMet(F;S)) ⊆ UMet(X;S)`.
(N1): if `X` is completely metrizable, the auxiliary data can be chosen so
that `Σ(Cm(F)) ⊆ Cm(X)` and `Σ(UCM(F;S)) ⊆ UCM(X;S)`.*
Used by: 3.14 (clauses 1, 2, 5), 3.17 (additionally N1). **Domain caveat:**
`Σ` is defined on `Met(F)` — there is **no pseudo-ultrametric-level
(`UCPM`) extensor** in E2; this is precisely why 3.14/3.17 need the transfer
repair of §2.14.

**E3 — Koshino, *On the Borel complexity and the complete metrizability of
spaces of metrics*, Anal. Geom. Metr. Spaces 12 (2024).** Used by 3.7 (⇐ and
the final step of ⇒): *for separable metrizable `X`: `X` is σ-compact iff
`AM(X)` (= `BMet(X)`) is completely metrizable.* Citation-number caveat in
§2.10 (preprint cites "Corollary 1.2"; repo record says unnumbered).

**E4 — standard descriptive set theory (Kechris, GTM 156).**
(a) Perfect set theorem for Borel sets — every uncountable Borel subset of a
Polish space contains a nonempty perfect set, hence has cardinality `𝔠`
(cited as Theorem 13.6; used in 2.1);
(b) Bernstein sets exist (cited as Example 8.24; used in 2.1, CH branch);
(c) `2^ω` Borel-isomorphic to `[0,1]` (used in 2.2; currently cited without
a number — add one, e.g. the Borel isomorphism theorem, Kechris 15.6);
(d) Alexandrov–Lavrentiev: a completely metrizable subspace of a metrizable
space is `G_δ` (Kechris, Theorem 3.11 — already number-verified in
`notes/literature.md`; used implicitly by 3.6, 3.15, and 3.17's second
sentence — the preprint never cites it; add).
Number verification status: **all four numbers verified against the printed
text of GTM 156** (2026-08-23, full-text copy).
(a) Theorem 13.6 is literally "(The Perfect Set Theorem for Borel Sets)
(Alexandrov, Hausdorff) Let `X` be Polish and `A ⊆ X` be Borel. Then either
`A` is countable or else it contains a Cantor set. In particular, every
uncountable standard Borel space has cardinality `2^{ℵ₀}`" — exactly the
form used in 2.1. ✓
(b) Example 8.24's numbered statement reads "There is a subset `A ⊆ ℝ` not
having the BP" — the Bernstein set (for `ℝ`, not `[0,1]`) is the transfinite
construction inside its proof, so the preprint's "(for the existence, see
[Example 8.24])" is defensible but slightly indirect (a `[0,1]`-Bernstein
set is obtained by intersecting, or by running the same recursion in
`[0,1]`). ✓
(c) Theorem 15.6 is "(The Isomorphism Theorem) Let `X`, `Y` be standard
Borel spaces. Then `X`, `Y` are Borel isomorphic iff `card(X) = card(Y)`" —
gives `2^ω ≅_B [0,1]` as the uncountable case; the right number to add in
2.2. ✓
(d) Theorem 3.11 is the two-sided completely-metrizable/`G_δ`
characterization, first assertion for arbitrary metrizable `X` —
re-confirming the `notes/literature.md` record. ✓

**Standard non-DST facts used silently (all re-derived here, no citation
needed for experts):** nonseparable metric space contains an `ε`-separated
set of size `ℵ₁` and separated sets are closed discrete (3.5, 3.14);
completeness of `CPM(X)` and `𝒰𝒟`-completeness of `UCPM(X;R)` (3.5; §2.14
repair); one-point amalgamation of metrics (sum-form 3.4, max-form 3.13);
components are clopen (§1); restriction of a complete metric to a closed
subspace is complete (3.9, 3.17); regularity of `ℵ₁` (3.4, 3.13).

---

## 4. Dependency graph

**Route W — the preprint's written proofs** (what §2 audited):

```
2.1 → 3.1 → 3.2 → 3.3 ─────────────────────────→ [3.7 repair, §2.10]
             └──→ 3.4 ──(+E1)──→ 3.5 ──(+E4d)──→ 3.6 ──(+E3)──→ 3.7
             └──→ [3.4 amalgam] → 3.8 ──(+E1(4))──→ 3.9
2.2 → 3.10 → 3.11 → 3.12
             └──→ 3.13 ──(+E2, §2.14 transfer)──→ 3.14 ──(+E4d)──→ 3.15
                    └──→ 3.16 ──(+E2(N1), §2.14 transfer, +E4d)──→ 3.17
```

**Route M — minimal verified chain for the main results** (§2.6, §2.8;
this is the executable contract for the Lean issues, not what the paper
prints):

```
2.1 → 3.1 → 3.2 → [Met(Z)/BMet(Z) pullback versions of 3.3, §2.6]
        ──(+E1: Ẽ on CPM, extension, isometry, Met-preservation)──→ 3.5
        ──(+E4d)──→ 3.6;   3.7 additionally needs E1(3) + E3 (§2.10)
```

Route M consumes: the `Met(Z)`-version of 3.3 (stated only in the
abstract/introduction of the preprint — §2.6), the ambient (`CPM`-level)
pullback of §1, and, for the arbitrary-carrier statement forms, the
relabelling isometries of §1. It does **not** consume 3.4/3.8/3.13/3.16,
which are finer independent results. The two routes are both sound; §2's
verdicts audit Route W, while §7 scopes #56/#57 along Route M and lists each
Route M obligation explicitly.

---

## 5. Removed claims — must not be reinstated

The 11 Aug draft (Issue #46 track; audited in
`notes/ishiki-extension-audit.md`, superseded) claimed, for a dense
`S ⊆ [0,1]` of cardinality `ℵ₁` produced by the CH/¬CH recipe, that `S` is
**neither analytic nor coanalytic**, and correspondingly that `BMet(D)` /
`Met(X)` is neither analytic nor coanalytic in the ambient pseudometric
space. Two independent findings of that audit stand and remain binding:

1. **The `|S| = ℵ₁` "not coanalytic" claim is not a ZFC theorem.** The ¬CH
   branch is refutable: there are models of ZFC + ¬CH — any ccc forcing
   extension of `L` keeping `ω₁^L = ω₁`, e.g. adding `ℵ₂` Cohen reals — in
   which the largest thin `Π¹₁` set `C₁` (Kechris 1975; Guaspari; Sacks) is a
   **coanalytic** dense set of cardinality `ℵ₁`, a legitimate output of the
   old recipe. By Mansfield–Solovay (`Σ¹₂(a)` sets are contained in `L[a]` or
   contain a perfect set), a ZFC repair would need to produce `S` with
   `S ⊄ L[a]` for every real `a`, which the audit could not obtain in ZFC and
   which fails for the recipe as stated. Only the asymmetric half ("not
   analytic", by cardinality `ℵ₁ < 𝔠` + Souslin's perfect set theorem)
   survived in ZFC under ¬CH.
2. **The classical analytic/coanalytic pointclasses are the wrong notion in
   the nonseparable ambient**: `Σ¹₁` sets are separable by definition, and
   both `BMet(D)` and its complement in `BCPM(D)` have density `2^{ℵ₁}`, so
   the old Theorem 3.3 was vacuously true under the classical reading and
   needed a bespoke Souslin-`F` convention to mean anything.

**The Borel statement replaces both.** The perfect set theorem for *Borel*
sets is a ZFC theorem (no thin-Borel pathology exists), making 2.1 a clean
unconditional dichotomy, and the Borel σ-algebra of the nonseparable ambient
is generated by its own topology with all needed closure properties (§1) —
no Polish ambient, no Souslin operation, no pointclass convention. No
analytic/coanalytic statement appears anywhere in arXiv:2608.19618, and none
may be reintroduced into the verification targets. Any future strengthening
toward projective classes must reopen the (★)-analysis above as a research
question, not as a verification target.

---

## 6. Correspondence with existing Lean (namespace `IshikiExt`, PR #52; plus `Conj51/`)

Mapping recorded **only** where hypotheses/conclusions match literally;
mismatches stated explicitly. Lean files:
`lean/IshikiConj51/Ext/BddPMet.lean`, `lean/IshikiConj51/Ext/BoundedCoding.lean`
(sorry-free, built against the 11 Aug draft's §3.1 = the preprint's §3.1
coding, which is unchanged).

| preprint | Lean declaration | match |
|---|---|---|
| carrier `Z = {p,q} ⊔ ⊔_α C_α` | `ExtIndex S = Bool ⊕ (↥S × Option ℕ)` | literal up to relabelling: stars indexed by `S` itself instead of an enumeration `α ↦ w_α`; `p,q ↦ inl true/false`, `b_α ↦ inr (a, none)`, `c_{α,n} ↦ inr (a, some n)`. (the `BddPMet`/`CPM`-level relabelling is `Ext/Relabel.lean`, *delivered by #63* — see §1) |
| `card(Z) = ℵ₁` | `card_extIndex : #S = ℵ₁ → #(ExtIndex S) = ℵ₁` | literal |
| `l_n(α,t) = \|t−w_α\| + 2^{−n}` | `spokeLen n a t = \|t − a\| + (1/2)^n` | literal |
| ambient `BCPM(Z)`, sup metric | `BddPMet D` with `supDist`, `MetricSpace` instance | literal for the *bounded* ambient; the preprint's stated ambient `CPM(Z)` (unbounded, `[0,∞]`-valued `𝒟`) is `CPM D` in `Ext/CPM.lean`, *delivered by #56 item 3* |
| 3.1: `d_t` is a metric, values in `[0,4]` (all `t ∈ [0,1]`) | `dExt_isMetricOn`, `dExt_nonneg`, `dExt_le_four` (hyp. `S ⊆ Icc 0 1`, `t ∈ Icc 0 1`) | literal |
| 3.1: `d_t ∈ Met(Z) ⟺ t ∉ S` | `dExt_isCompatible_iff` (via `dExt_topology_eq_bot` / `_ne_bot`); `IsCompatible` = `IsMetricOn` + induced topology `= ⊥` | literal, phrased as membership in `BMet(D) ⊆ BddPMet D`; for `d_t` (bounded) the `Met`/`BMet` versions coincide |
| 3.2: `\|s−t\| ≤ 𝒟(d_s,d_t) ≤ 2\|s−t\|` | `abs_sub_le_dist_phiFull`, `dist_phiFull_le`, `lipschitzWith_phiFull` (constant 2), `injective_phiFull` | literal (identical constants) |
| 3.2: `Φ([0,1]∖S)` closed in `Met(Z)` | `isClosed_image_phiFull` — closed in the **subspace `BMet D`** | matches the `BMet`-relative form; the preprint's `Met(Z)`-relative closedness additionally needs "`BMet` is a union of components, clopen in `Met`" — not yet formalised (trivial) |
| 3.3's implicit trace identity `F = L ∩ BMet(Z)` | `image_compl_eq_range_inter`; `preimage_BMet_phiFull` / `image_preimage_BMet_phiFull` (`Φ_full⁻¹(BMet) = Icc∖S`) | literal — and strictly stronger (exact pullback over all of `[0,1]`), which is the recommended Lean route for 3.3 (§7) |
| `L = Φ([0,1])` compact/closed | `isClosed_range_phiFull` | literal (in the `BddPMet` ambient) |

This table predates #56/#57/#63/#66; see §7 for the current, maintained
delivery status. Superseded by delivery: Proposition 2.1's density-free
ingredient (the non-**Borel** `[0,1]` parameter set, `#S = ℵ₁`, is now
`exists_aleph1_nonBorel`, §7 item 1 — "2.1 *without* density"; the literal
Proposition 2.1, which additionally asserts `S` dense, has no Lean
declaration; `Conj51/Cardinality.lean`'s non-**Fσ** `lem_A_exists` remains
the separate, strictly weaker archival-track result) and Theorem 3.3
(`bmet_not_borel_cpm`, `met_not_borel`, §7 item 3), plus Theorem 3.5
conditionally (`IsIsometricExtensor.not_measurableSet_CPM_MetOn`, §7 "#66").
Theorem 3.4 and the one-point amalgamation it rests on are now
`Ext/Component.lean` and `Ext/Amalgam.lean` (§7 "#84"), Corollaries 3.6 and
3.7 are `Ext/CompleteMetrizability.lean` (§7 "#79"), and Theorem 3.8 with
Corollary 3.9 are `Ext/Completeness.lean` and `Ext/CompleteMetric.lean`
(§7 "#80"); the non-Archimedean chain 2.2 and 3.10–3.17 landed with #81, #82
and #83. Proposition 2.1's density clause is now the only audited statement
with no Lean declaration, and it does not gate #56/#57/#66 (§7 item 5).

Archival mapping (unchanged by this audit): `Conj51/` +
`report/report-ja.md` formalise the companion arXiv:2608.11023
(claim IDs `LEM-A-EXISTS`, `LEM-STAR-METRIC`, `LEM-CLOSED-IMAGE`,
`THM-CONJ51`). Note the companion's coding differs from the preprint's
(spokes `min(1, |t−a| + 1/(n+1))`, cross-distance 1, values in `[0,2]`,
Fσ/Gδ instead of Borel): **`Conj51/` matches 2608.11023, `IshikiExt`
matches 2608.19618**; do not confuse them.

---

## 7. Minimal Lean theorem package

Constraints from this audit: external theorems (E1, E2) enter only as
**explicit hypotheses** of the Lean statements, never as axioms; the Borel
side uses Mathlib's `MeasurableSet` over the `borel` σ-algebra of the ambient
(extended-)metric topology (`BorelSpace` instances); the legacy local
`IsFSigma` (`Conj51/Cardinality.lean`) is irrelevant to this track. Density
of `S` is **omitted** from the Archimedean statements (unused, §2.1).

### #56 — discrete core (statement gate: this note)

1. **`exists_aleph1_nonBorel`** — `∃ S ⊆ Icc (0:ℝ) 1, #S = ℵ₁ ∧
   ¬ MeasurableSet S` (Borel σ-algebra of `ℝ` or of `Icc 0 1`; equivalent by
   trace). The *statement* is 2.1 without density; the Lean *proof route*
   need not follow the preprint's Bernstein construction — a CH-dichotomy
   runs entirely on Mathlib v4.32.2 API (declarations
   grep-verified against the pinned mathlib):
   * E4a in the needed form "`B` Borel in a Polish space, uncountable ⇒
     `#B = 𝔠`" is derivable: `MeasurableSet.standardBorel`
     (`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`) makes `B` a
     standard Borel space, and
     `PolishSpace.measurableEquivNatBoolOfNotCountable` (ibid.) gives
     `B ≃ᵐ (ℕ → Bool)`, hence `#B = 𝔠`.
   * *¬CH branch:* any `S ⊆ Icc 0 1` with `#S = ℵ₁ < 𝔠`; Borel would force
     `#S = 𝔠` by the above.
   * *CH branch:* `MeasurableSpace.cardinal_measurableSet_le_continuum`
     (`Mathlib/MeasureTheory/MeasurableSpace/Card.lean`) — the Borel
     σ-algebra is countably generated, so there are at most `𝔠 < 2^𝔠`
     Borel sets; hence some `S ⊆ Icc 0 1` is non-Borel. Countable sets are
     Borel, so `S` is uncountable, and under CH `ℵ₁ ≤ #S ≤ 𝔠 = ℵ₁`.
   Neither a Bernstein set (E4b) nor any perfect-set transfinite recursion
   is needed in Lean; E4b remains a paper-side citation only. (The audit of
   the preprint's own written proof stays as §2.1 — Route W and the Lean
   route legitimately differ here, the gated statement is identical.) The
   old `lem_A_exists` CH branch (`[0,1]∖ℚ`, Baire) still does not adapt —
   `[0,1]∖ℚ` is Borel. *Delivered by #56* (`Ext/Borel.lean`,
   `exists_aleph1_nonBorel`).
2. **`bmet_not_borel`** (Theorem 3.3, bounded-ambient form) — for `S` as in
   (1): `¬ MeasurableSet (BMet (ExtIndex S))` in `BddPMet (ExtIndex S)`.
   Layer 1 supplies both inputs: `phiFull` is continuous
   (`lipschitzWith_phiFull`), hence Borel-measurable, and
   `image_preimage_BMet_phiFull` gives `Subtype.val '' Φ_full⁻¹(BMet) =
   Icc∖S`. What remains is that measurability of `BMet` would then make
   `Icc∖S`, hence `S`, measurable, contradicting (1). This *pullback route*
   replaces the paper's relative-closure argument and needs no new topology. *Delivered by #56*
   (`Ext/Borel.lean`, `bmet_not_borel`).
3. **Transfer to the `CPM D` ambient** — a `CPM D` type (unbounded
   continuous — i.e. arbitrary, `D` discrete — pseudometrics with
   `EMetricSpace` sup distance, mirroring `Conj51/MetD.lean`), plus the
   **bridge lemma** identifying the `BddPMet D` metric topology with the
   subspace topology induced from `CPM D` (the real-valued `supDist` and the
   `ENNReal`-valued sup distance agree on bounded pairs; hence the Borel
   σ-algebra of `BddPMet D` is the trace σ-algebra), the subspace-trace
   lemma ("`MeasurableSet` in the larger ambient ⇒ `MeasurableSet` of the
   intersection in the subspace"), and the two corollaries: `BMet(D)`
   non-Borel in `CPM(D)`, and the `Met(D)` version (§2.6) via
   `phiFull⁻¹(Met D) = Icc∖S` in the `CPM` ambient. With this layer, the
   preprint's literal 3.3 statement and the abstract's `Met(Z)` claim are
   both discharged (item 2 alone is a bounded-ambient surrogate). *Delivered
   by #56* (`Ext/CPM.lean`, `bmet_not_borel_cpm` and `met_not_borel`).
4. **Arbitrary-carrier form (relabelling)** — for the statements "for every
   discrete `D` with `#D = ℵ₁`": `BddPMet`- and `CPM`-level relabelling
   isometries induced by a bijection `D ≃ E`, preserving `BMet`/`Met`
   (mirror of `relabelIsometry` in `Conj51/Relabel.lean`, which covers
   `MetD` only — §1). Without it the #56 theorems are stated for the
   concrete `ExtIndex S` carrier, which is acceptable for the gate but not
   for the literal preprint statement. *Delivered by #63*
   (`Ext/Relabel.lean`): `bmet_not_borel_cpm_of_card` is Theorem 3.3 as
   stated in the body, `met_not_borel_of_card` the abstract/introduction
   `Met(Z)` claim (§2.6), and `bmet_not_borel_of_card` item 2's
   bounded-ambient statement — each quantified over an arbitrary `D` with
   `#D = ℵ₁` and carrying no residual hypothesis on the parameter set. One
   deviation from the `MetD` mirror: `BddPMet.supDist` is a real conditional
   supremum, so the reindexing step cannot use `Equiv.iSup_comp` (no
   `ciSup` analogue exists in the pinned mathlib) and is proved by
   antisymmetry from `le_supDist`/`supDist_le`. The same item at `CPMOn` level
   — relabelling the continuous-pseudometric ambient along a *homeomorphism*,
   which is what the E1 bridge needs — is *delivered by #72*, below.
5. *Not gating #57:* Theorem 3.4 (components; one-point amalgamation plus
   the uncountable-ball argument) is *delivered by #84*, below. Theorem 3.8
   (with the §2.11 repair baked in: complete base `d + 1`) is *delivered by
   #80*, below, consuming #84's amalgamation layer unchanged.

### #57 — general-space transfer (Theorem 3.5)

Statement shape (Route M of §4, the component-free route of §2.8). Consumed
from #56: the `Met(D)`-version pullback theorem (item 3) and, if the
arbitrary-carrier phrasing is wanted, the relabelling layer (item 4) —
these are gating prerequisites and must exist before #57's final theorem is
stated:

* Hypothesis bundle `IsIsometricExtensor` for a metrizable `X` (as a
  Lean-side structure): maps `Ẽ : CPM(Z) → CPM(X)` and its restriction
  `E`, with fields = E1's clauses (1) extension, (2) isometry (at
  `EMetricSpace` level), Met-preservation `E '' Met(Z) ⊆ Met(X)`; the
  identity `Ẽ(Met(Z)) = Ẽ(CPM(Z)) ∩ Met(X)` should be **derived** from (1) +
  restriction-preserves-compatibility, not hypothesised. Clauses (3)/(4) are
  needed only for the 3.7-repair / 3.9 extensions and can be optional fields;
  (4) must carry the "`X` completely metrizable" hypothesis per the E1
  caveat (§3).
* Conditionality is by design: the #57 Lean theorem takes the E1 bundle as
  an explicit hypothesis and does **not** formalise E1's proof, so Lean
  discharges the preprint's 3.5 only modulo that hypothesis — matching the
  EXTERNAL verdict semantics, not silently strengthening them.
* Supporting lemmas: nonseparable metric space has a closed discrete
  `ε`-separated subset of cardinality `ℵ₁`; completeness of `CPM(Z)`;
  isometric image of a complete space is closed; Borel pullback along a
  continuous map + trace (from #56 item 3). *Delivered by #57*
  (`Ext/GeneralSpace.lean`'s `exists_aleph1_closed_discrete_separated` and
  `isClosed_range_of_isometry_complete`; `Ext/CPM.lean`'s
  `CPM.instCompleteSpace`, added in #66).
* Target: `Met(X)` Borel in `CPM(X)` → `SeparableSpace X`, with the E1
  bundle as hypothesis; plus the 3.6 corollary via Mathlib's
  completely-metrizable-⇒-Gδ. *The Borel-obstruction target is delivered by
  #66* (`IsIsometricExtensor.not_measurableSet_CPM_MetOn` and
  `separable_of_measurableSet_CPM_MetOn_of_extensors`, "#66" below); the 3.6
  corollary remains open, listed under "#66"'s "Not delivered here" below.

### #66 — the Route M package (delivered)

Three prerequisites raised on review of #57 and #63 were resolved first.

* **Continuity-aware ambient.** `CPM X` (`Ext/CPM.lean`) is the space of *all*
  finite-valued pseudometrics on a bare carrier — the preprint's `CPM(X)` only
  when `X` is discrete, which is the case it was written for. §1 fixes the
  preprint's ambient as the *continuous* pseudometrics, and trace monotonicity
  runs only from the larger ambient to the smaller, so "Borel in `CPM X`" is a
  strictly stronger hypothesis than Theorem 3.5's and may not be substituted
  for it. `Ext/GeneralSeparability.lean` therefore introduces
  `CPMOn X = {d : CPM X // Continuous (Function.uncurry d.1)}` carrying the
  subtype extended-metric structure — literally the restriction of `𝒟_X`,
  since `Subtype.edist_eq` is `rfl` — and re-points `CPM.MetOn X` to
  `Set (CPMOn X)` and the extensor's codomain to `CPMOn X`. The extensor's
  **domain** stays the bare `CPM A`: E1 is applied to a closed *discrete* `A`,
  where the preprint's `CPM(A)` is the set of all pseudometrics on `A`. As a
  consequence `met_not_borel` is consumed verbatim and no discrete-carrier
  transfer isometry is needed anywhere in the proof. The identification itself
  is nevertheless recorded, as the checked justification of the design:
  `CPMOn.equivCPM (D) [DiscreteTopology D] : CPMOn D ≃ᵢ CPM D` together with
  `CPMOn.preimage_equivCPM_met`, identifying the two metric loci. It is an
  isometric equivalence, not a definitional identity.
* **`CompleteSpace (CPM D)`** (`Ext/CPM.lean`, `CPM.instCompleteSpace`) — the
  §2.8 "uniform limits of pseudometrics" step, proved directly from
  `EMetric.complete_of_cauchySeq_tendsto`: a Cauchy sequence for the supremum
  distance is pointwise Cauchy, the pointwise limit is again a pseudometric,
  and the Cauchy modulus survives passage to the limit in the second index.
* **`isClosed_range_of_isometry_complete`** generalised from `MetricSpace` to
  `EMetricSpace` hypotheses (`Ext/GeneralSpace.lean`); the proof term is
  unchanged, because Mathlib's `Isometry.isClosedEmbedding` is already stated
  at the extended-metric level. `CPM`'s supremum distance is
  `[0,∞]`-valued (§1), so the `MetricSpace` form could not be applied to it.

Delivered statements (all in `Ext/GeneralSeparability.lean`):

* `IsIsometricExtensor.not_measurableSet_CPM_MetOn` — the core content of
  Theorem 3.5: an isometric extensor out of the coded `ℵ₁`-sized discrete
  carrier forbids `MeasurableSet (CPM.MetOn X)`. Conditional on the
  `IsIsometricExtensor` bundle, which is a *transported* form of E1 and not E1
  itself (see "Conditionality" below); the bundle is a hypothesis, never an
  axiom, so nothing here strengthens the EXTERNAL verdict of §2.8.
* `separable_of_measurableSet_CPM_MetOn_of_extensors` — the conclusion of
  Theorem 3.5 in its separability form, with the extensor input hypothesised as
  "*every* closed discrete copy of the coded carrier inside `X` admits an
  `IsIsometricExtensor` bundle". Quantifying rather than fixing the extensor is
  what §2.8's argument needs: the closed discrete subspace is produced by the
  separated-set argument only *after* nonseparability is assumed, so the
  extensor cannot be fixed in advance. This is the variant in which
  `exists_aleph1_closed_discrete_separated` is actually consumed, and no
  CPM-level relabelling (§7 item 4) is needed *inside the proof* — the
  bijection between the coded carrier and the separated set is absorbed into
  the embedding. Relabelling is still what stands between the hypothesis and
  E1 itself, below.
* `separable_of_measurableSet_CPM_MetOn` — the literal statement of Issue #66,
  recorded as a corollary and flagged as such: its hypotheses are jointly
  inconsistent. `IsIsometricExtensor.not_separableSpace` proves that a fixed
  extensor bundle already refutes separability with no Borel hypothesis at
  all, so the corollary's proof runs through `False.elim`. It is not the
  result; the two statements above are.

**Conditionality, stated exactly.** Both theorems are conditional on the Lean
`IsIsometricExtensor` bundle, which is *not* E1 verbatim. E1 quantifies over an
arbitrary closed subset `A ⊆ X` and supplies `Ẽ` on the *continuous*
pseudometrics of `A`; the bundle fixes an abstract carrier plus a closed
embedding `ι` and takes the extensor already transported along `ι`, with a bare
`CPM A` domain. For closed *discrete* `A` the two agree, and the
continuity half of that bridge is proved (`CPMOn.equivCPM`,
`CPMOn.preimage_equivCPM_met`); the relabelling half — moving the domain from
`↥A` to the abstract carrier along `ι` — is the CPMOn-level instance of item 4
above, and was **not** formalised in #66. E1 therefore implies the Lean
hypothesis, so the Lean theorems are at least as strong as the E1-conditional
statement, but #66 did not check that implication: for its two theorems,
"modulo the bundle" is accurate and "modulo E1" would overstate. #72 below
closes the bridge and restates both with E1 as the hypothesis.

Not delivered here: the E1 bridge just described (delivered by #72),
Corollary 3.6 (completely metrizable ⇒ Borel, via Alexandrov–Lavrentiev, E4d),
and the `BMet`/`Comp` variants of the transfer needed for §2.10 and §2.12. The
last two remain open.

### #72 — the E1 bridge (delivered)

Three pieces, all in `Ext/GeneralSeparability.lean` except where noted.

* **Item 4 at `CPMOn` level.** `CPMOn.comap`/`CPMOn.relabelIsometry` transport
  the continuous-pseudometric ambient along a homeomorphism `σ : D ≃ₜ E`; the
  pseudometric content is `CPM.comap σ` and the continuity field transports
  because `σ × σ` is continuous. The locus identity is
  `CPMOn.preimage_MetOn_comap`. Unlike the bare-carrier case, the condition
  being transported is "`d` induces the topology of the ambient" rather than
  "`d` induces `⊥`", so it needs `topology_comap` (`Ext/Relabel.lean`): a
  relabelled metric induces the relabelled topology.
  That is the general form of the existing `topology_comap_eq_bot`, which stays
  as the discrete-carrier case.
* **E1 as a Lean structure.** `IsIsometricExtensorOn (A : Set X)` for a
  metrizable `X`: `closed`, `toCPM : CPMOn ↥A → CPMOn X`, `extension`,
  `isometry_toCPM`, `met_preservation`. These are E1's clauses (1), (2) and the
  inclusion half of the "furthermore" clause, with no carrier-specific choices;
  the reverse inclusion stays derived
  (`IsIsometricExtensor.image_met_eq_range_inter`), and clauses (3)/(4) are
  omitted as before.
* **The derivation.** `IsIsometricExtensorOn.toIsIsometricExtensor` takes
  E1 for `Set.range ι`, for a closed embedding `ι` of a `⊥`-topologised carrier,
  and produces the #66 bundle: relabel along the homeomorphism `ι` induces onto
  `↥(range ι)`, then drop to the bare domain by `CPMOn.equivCPM`.
  `met_preservation` transports through `CPMOn.preimage_equivCPM_met` and
  `CPMOn.preimage_MetOn_comap`.

Delivered statements:
`not_measurableSet_CPM_MetOn_of_isometricExtensorOn` and
`separable_of_measurableSet_CPM_MetOn_of_isometricExtensorOn`, the #66 pair
with `∀ A, IsClosed A → Nonempty (IsIsometricExtensorOn A)` — E1's statement
for `X` — in place of the bundle. E1's proof stays external and is not an
axiom.

### #79 — Corollaries 3.6 and 3.7 (delivered)

All in `Ext/CompleteMetrizability.lean`, except E4d, which is reused from the
archival track.

* **E4d in the ambient this track needs.** `isGδ_of_isCompletelyMetrizableSpace`
  (`Conj51/GDeltaComplete.lean`) is Alexandrov–Lavrentiev for a `MetricSpace`
  ambient, with no separability assumption on either space; Mathlib has no
  result concluding `IsGδ` from a completeness hypothesis, so the whole step is
  local. Here the ambient is `CPMOn X`, whose supremum distance reaches `∞`
  (§1), making it an `EMetricSpace` and not a `MetricSpace`, so
  `isGδ_of_isCompletelyMetrizableSpace_of_metrizableSpace` restates it for a
  metrizable ambient by choosing a compatible metric with
  `TopologicalSpace.metrizableSpaceMetric`.
* **The bounded locus in the continuous ambient.** `CPM.BMetOn X` is the
  bounded part of `CPM.MetOn X` — Koshino's `AM(X)`. `CPM.mem_BMet_iff`
  rewrites the discrete-carrier `CPM.BMet D` of `Ext/CPM.lean`, defined there
  as an image of the bounded ambient, into the same shape, and
  `CPMOn.preimage_equivCPM_bmet` / `CPMOn.preimage_BMetOn_comap` carry the
  locus across the two moves of the #72 bridge.
* **E1 clause (3).** `IsBddIsometricExtensorOn` extends `IsIsometricExtensorOn`
  by the single field `Ẽ(BMet(A)) ⊆ BMet(X)`: the same extensor with one more
  clause of E1, quoted as §3 quotes it. Clause (4) stays omitted (§2.12, and
  the "`X` completely metrizable" caveat of §3).
  `IsBddIsometricExtensorOn.image_bmet_subset` transports the clause along
  `IsIsometricExtensorOn.toIsIsometricExtensor`.
* **The §2.10 repair.** `IsIsometricExtensor.image_bmet_eq_range_inter` is
  `E(BMet(Z)) = Ẽ(CPM(Z)) ∩ BMet(X)`, the ⊆ half from clause (3) and the ⊇ half
  derived as in the `Met` case. `IsIsometricExtensor.not_measurableSet_CPM_BMetOn`
  runs §2.8's chain on it and ends at `bmet_not_borel_cpm` — Theorem 3.3
  directly, with no components, as §2.10 prescribes.

All statements below quantify over a **metrizable** `X`, which is the
hypothesis both corollaries carry. The transfer theorems of #66/#72 are stated
for a metric space, so where they are consumed a compatible metric is chosen
inside the proof; both the hypotheses and the conclusions are properties of the
topology, so nothing depends on the choice.

Delivered statements:

* `separable_of_isCompletelyMetrizableSpace_CPM_MetOn_of_isometricExtensorOn` —
  **Corollary 3.6**, conditional on E1: `Met(X)` completely metrizable implies
  `X` separable. The parameter set is produced internally by
  `exists_aleph1_nonBorel`, so E1 is the only hypothesis besides the corollary's
  own.
* `not_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn` and
  `separable_of_measurableSet_CPM_BMetOn_of_bddIsometricExtensorOn` — the
  `BMet` analogue of Theorem 3.5 that §2.10 identifies as the missing link,
  conditional on E1 clauses (1)–(3).
* `separable_of_isCompletelyMetrizableSpace_CPM_BMetOn_of_bddIsometricExtensorOn`
  — its complete-metrizability form, the `BMet` statement that Corollary 3.6
  does not supply.
* `isCompletelyMetrizableSpace_CPM_BMetOn_iff_sigmaCompactSpace` — **Corollary
  3.7**, repaired: `BMet(X)` completely metrizable iff `X` σ-compact. E3 enters
  as the explicit hypothesis `SeparableSpace X → (SigmaCompactSpace X ↔
  BMet(X) completely metrizable)` — Koshino's theorem for this `X`, with its
  separability hypothesis intact. It is never an axiom or an instance, and the
  citation-number caveat of §2.10 stands unresolved: it is recorded on the Lean
  statement rather than settled there.

E1 and E3 both stay external and are discharged nowhere in the repository.

### #84 — Theorem 3.4 (delivered)

Two files: `Ext/Amalgam.lean`, which is carrier-agnostic machinery, and
`Ext/Component.lean`, which is the theorem.

* **One-point amalgamation.** `amalgam E z hz d e` glues a metric `e` on
  `E ⊆ Z` to a metric `d` on `Z` along a common point `z ∈ E`, routing cross
  pairs through `z`. `isMetricOn_amalgam` assumes nothing but the two metric
  axioms. `amalgam_topology_eq_bot` adds compatibility of the two pieces and
  a uniform gap `c > 0` between the sides at `z` — the hypothesis form of
  §2.7's isolating radii — and `topology_eq_bot_of_amalgam` is its converse
  on the `E` side, which is what turns a coding parameter in `S` into a
  *failure* of compatibility. `abs_amalgam_sub_le` is §2.7 (i) with the
  constant explicit: `|m − d| ≤ B + 2H` when `e ≤ B` and `E` lies in the
  closed `d`-ball of radius `H` around `z`. `abs_amalgam_sub_amalgam_le`
  records that the amalgam depends on `e` pointwise `1`-Lipschitzly, which is
  what carries the coding's parameter estimate to the amalgamated family.
  None of these mentions the star coding or any cardinality, so 3.8 consumes
  them unchanged with the §2.11 repair applied to the base metric.
* **The component locus.** `CPM.component d = {e ∈ Met(Z) : 𝒟_Z(d,e) < ∞}` is
  the `∼`-class of §1, and `CPM.metSetoid` / `CPM.Components` /
  `CPM.componentSet` carry the quotient `𝐌_{<∞}(Z)` itself, so that "every
  component" can be quantified over the quotient rather than over
  representatives.
* **The `ℵ₁`-sized ball.** `exists_aleph1_ball`: the closed balls of integer
  radius around any centre exhaust the carrier, so one of them is
  uncountable, and it has cardinality at most that of the carrier. The radius
  is returned `≥ 1`, which is the form the gap hypothesis needs. Regularity
  of `ℵ₁` is not invoked; "a countable union of countable sets is countable"
  is all the argument uses.
* **The bundle.** `ComponentSetup Z` collects §2.7's data: a base metric with
  its compatibility, a subset `E` with `E ⊆ B_d(z,H)` and `d(z,·) ≥ 1` off
  `E`, and a relabelling `θ : ↥E ≃ ExtIndex S` carrying `z` to the coding's
  anchor. `mem_Met_psi_iff` is §2.7 (ii), `edist_psi_base_le` is §2.7 (i) at
  `4 + 2H`, and `preimage_component_psi` is the exact pullback identity
  `Ψ⁻¹(𝔠) = [0,1] ∖ S`. The written proof's compact witness is recorded as
  `isCompact_range_psi` and `range_inter_component`
  (`L' ∩ 𝔠 = Ψ([0,1] ∖ S)`), while the obstruction itself runs on the
  pullback identity, exactly as in item 2.
* **The theorems.** `component_not_measurableSet` — for every `d ∈ Met(Z)`,
  its component is not Borel in `CPM(Z)` — and `componentSet_not_measurableSet`,
  the same statement quantified over `𝔠 ∈ 𝐌_{<∞}(Z)`. Both are stated for an
  arbitrary carrier with `#Z = ℵ₁` and carry no residual hypothesis on a
  parameter set. The relabelling consumed is the bijection of the ball with
  the coded carrier (`isMetricOn_comap`, `topology_comap_eq_bot` of
  `Ext/Relabel.lean`); the construction never leaves `Z`, so no `CPM`-level
  transfer isometry enters.

Vacuity: `exists_carrier_aleph_one` (#63) supplies a carrier of the required
cardinality, and `CPM.nonempty_Met` / `CPM.nonempty_Components` supply a
component to quantify over — the `0/1` metric is compatible with the discrete
topology on any carrier. Neither theorem is vacuously true.

The verdict on 3.4 is unchanged: PASS. Nothing in the written proof had to be
repaired to formalise it; the two implicit steps of §2.7 are the two lemmas
named above.

### #80 — Theorem 3.8 and Corollary 3.9 (delivered)

Two files: `Ext/Completeness.lean`, which is completeness for the bare metrics
of this track together with the two `Comp` loci, and `Ext/CompleteMetric.lean`,
which is the two theorems. The component and amalgamation machinery of #84 is
consumed unchanged.

* **What completeness means here.** Metrics on this track are bare functions
  satisfying `IsMetricOn`, so completeness is stated the same way:
  `IsCompleteMetricOn d` says every `d`-Cauchy sequence converges, and
  `isCompleteMetricOn_iff_completeSpace` identifies it with `CompleteSpace`
  for `IsMetricOn.toMetricSpace`, so nothing weaker is in play.
  `CPM.Comp Z` and `CPM.CompOn X` are the complete members of `CPM.Met Z` and
  of `CPM.MetOn X` — §1's `Comp` in the discrete and the general ambient.
  `CPMOn.preimage_equivCPM_comp` and `CPMOn.preimage_CompOn_comap` carry the
  locus across the two moves of the #72 bridge, as their `Met` and `BMet`
  counterparts do.
* **The §2.11 repair, in three lemmas.** `addOneOffDiag d` is `d' := d + 1`
  off the diagonal; `isMetricOn_addOneOffDiag`,
  `topology_addOneOffDiag_eq_bot`, `isCompleteMetricOn_addOneOffDiag` and
  `abs_addOneOffDiag_sub_le` are the four properties the repair needs, the
  last one being what puts `d'` in the component of `d`.
  `isCompleteMetricOn_dExt` is the half of the printed proof that survives
  the audit: the coding metrics are complete for `t ∉ S`, cross-block
  distances confining a Cauchy sequence to one star and `|t − a| > 0` making
  it eventually constant there. `isCompleteMetricOn_amalgam` is the
  amalgamation step, with hypotheses exactly as the argument uses them — the
  base complete *and* compatible, the `E`-side metric complete, and the
  uniform gap at the glue point. Compatibility of the base is what keeps the
  limit of an outside sequence outside `E`; without it the amalgam of two
  complete metrics need not be complete. The printed proof's step — an
  arbitrary base metric — is not formalised anywhere.
* **Theorem 3.8.** `component_inter_comp_not_measurableSet` for a
  representative, `componentSet_inter_comp_not_measurableSet` for
  `𝔠 ∈ 𝐌_{<∞}(Z)`, and `comp_not_measurableSet` for the component-free
  consequence. `exists_completeComponentSetup` is the normalisation: every
  component is the component of a complete compatible metric, over which the
  §2.7 setup is rebuilt. `nonempty_component_inter_comp` records that
  `𝔠 ∩ Comp(Z)` is nonempty, which is what §2.12 uses.
* **Trace, not intersection.** The `Comp(Z)` consequence runs on
  `preimage_Comp_psi` (`Ψ⁻¹(Comp(Z)) = [0,1] ∖ S`), with `range_inter_Comp`
  recording the compact-witness form `L' ∩ Comp(Z) = Ψ([0,1] ∖ S)`. No
  component is intersected, as §2.11 prescribes.
* **E1 clause (4).** `IsCompIsometricExtensorOn` adds the single field
  `Ẽ(Comp(A)) ⊆ Comp(X)` to `IsIsometricExtensorOn`, and carries
  `IsCompletelyMetrizableSpace X` as an instance hypothesis — the §3 caveat,
  encoded rather than only recorded, so the bundle cannot be asserted where
  the source's proof does not justify it.
  `IsCompIsometricExtensorOn.image_comp_subset` transports the clause along
  `IsIsometricExtensorOn.toIsIsometricExtensor`.
* **Corollary 3.9.** `IsIsometricExtensor.image_comp_eq_range_inter` is
  `E(Comp(Z)) = Ẽ(CPM(Z)) ∩ Comp(X)`, its reverse inclusion carrying §3's
  "restriction of a complete metric to a closed subspace is complete"
  (`isCompleteMetricOn_restrict`).
  `IsIsometricExtensor.not_measurableSet_CPM_CompOn` and
  `not_measurableSet_CPM_CompOn_of_compIsometricExtensorOn` run §2.8's chain
  on it, and
  `separable_of_measurableSet_CPM_CompOn_of_compIsometricExtensorOn` is the
  corollary. The route is the component-free one of §2.12.

E1 stays external and is discharged nowhere in the repository.

### Non-Archimedean track (3.10–3.17)

Fully audited above (§2.13–2.15) and fully delivered: the discrete core —
Proposition 2.2, Lemmas 3.10–3.11, Theorems 3.12–3.13 — by #81, the transfer
3.14–3.15 by #82, and the complete branch 3.16–3.17 by #83. The preprint
presents the chain 3.1–3.9 as the headline
(abstract and introduction lead with `Met(Z)`, Borel ⇒ separability, and the
Koshino combination; the non-Archimedean results are labelled "analogues").

**Delivered (#81).** Four files, layered as the Archimedean side is.

1. `Ext/UltraPMet.lean` — the ambient. `RangeSet` (the preprint's `R ⊆ [0,∞)`
   with `0 ∈ R`), `RangeSet.IsCharacteristic` (the *exact* accumulation-point
   hypothesis) and `RangeSet.IsScale` (the strictly decreasing `r : ℕ → R∖{0}`
   with `r n → 0`). `exists_isScale` and `isCharacteristic_of_isScale` prove
   both directions of the audit's "exists exactly because `R` is
   characteristic", so no hypothesis is silently strengthened.
   `IsUltraPMetOn`/`UCPM` are the `R`-valued pseudo-ultrametrics — nonnegativity
   is *derived* from `R ⊆ [0,∞)`, not assumed — and `UCPM.edist` is the
   preprint's `𝒰𝒟^R` verbatim, an infimum over `R ∪ {∞}` realised as an empty
   infimum in `ℝ≥0∞`. It satisfies the *strong* triangle inequality
   (`UCPM.edist_triangle_max`), which the Archimedean sup-metric does not, and
   the two operations `UCPM.comap` (pullback along any map) and `UCPM.sup`
   (pointwise maximum) are what the coding and the amalgam are built from.
   Mathlib has none of this: the library gap is recorded in the file header.
2. `Ext/CantorUltra.lean` — Proposition 2.2 with its §2.2 repair, and the
   `R`-valued Cantor ultrametric `cantorDist`. The CH/¬CH dichotomy is stated
   once for an arbitrary standard Borel space of cardinality `𝔠` whose Borel
   σ-algebra has at most `𝔠` members (`exists_aleph1_nonMeasurable`), then run
   in `2^ω`; density is then supplied by the audit's densification
   `S = T ∪ Q₀`. `cantorDist_lt_iff` identifies the `h`-balls with cylinders,
   which is the only bridge used between `h` and the product topology.
3. `Ext/UltraCoding.lean` — Lemma 3.10 (`dU_isUltraPMetOn`, `dU_le_head`,
   `isCompatible_phiU_iff`, `dU_completeSpace`), Lemma 3.11 (`edist_phiU`,
   `isClosed_image_phiU`) and Theorem 3.12 (`umet_not_borel`,
   `umet_not_borel_of_card`). The lower bound of 3.11 is
   `exists_separating_pair`, which genuinely consumes `Dense S`; the
   Archimedean observation that density is dispensable (§2.1) is *not*
   imported.
4. `Ext/UltraComponent.lean` — Theorem 3.13
   (`ucomponent_not_borel_of_card`), with the ball selection
   (`exists_countable_cofinal`, `exists_radius_not_countable`), the isosceles
   identity off the ball (`uBall_isosceles`), the one-point max-amalgam
   (`uAmalgam`) and the audited membership bound `𝒰𝒟^R(m_t,d) ≤ q ∨ r 0`
   (`edist_uAmalgam_le`).

Two deviations from the preprint's phrasing, both recorded because they
*weaken* rather than strengthen what is used. (i) Theorem 3.12 and 3.13 are
proved by the pullback route of §7 item 2 rather than the printed
relative-closure argument; the trace identities and closed images the printed
proof uses are formalised alongside (`image_compl_eq_range_inter_UMet`,
`isClosed_image_phiU`, `image_compl_eq_range_inter_UComponent`,
`isClosed_image_psiU`) but are not what the theorems consume. (ii) 3.13's
"transfer 3.10 with the centre `y_0 ↦ z`" is a labelling convention: the
amalgam glues at `θ(z)` for an arbitrary bijection `θ`, and only `z ∈ E` and
"every cluster value is `≤ r 0`" are used.

**Delivered (#82).** Two more files, carrying 3.14 and 3.15.

5. `Ext/UltraGeneral.lean` — the general-space ambient and E2. `UCPMOn Y R` is
   the preprint's `UCPM(Y;R)` over a topological space (the *continuous*
   `R`-valued pseudo-ultrametrics; Borelness in the bare ambient would be a
   strictly stronger hypothesis), `UMetOn Y R` its compatible locus.
   `completeSpace_UCPM` is §2.14's sub-lemma with its three steps, and
   `completeSpace_UCPMOn` is the form 3.14 consumes.
   `UCPM.isCompatible_comap_of_mem_UMetOn` is the restriction map along a
   discrete closed subspace — what stands in for the `UCPM`-level extensor E2
   does not have. `IsUltraIsometricExtensor` is E2 (§3 clauses (1), (2), (5))
   as a hypothesis bundle with **no** `UCPM`-level field, and
   `nonempty_isUltraIsometricExtensor_id` records that the bundle is
   satisfiable.
6. `Ext/UltraTransfer.lean` — the §2.14 repair and the two theorems, listed in
   the Lean notes of §2.14.

Deviations, both recorded there: `P` is used in its transported form
`cl(Φ(2^ω∖S))` (equal to `Φ(P)`, proved), and the final step is the pullback
identity rather than the printed relative trace (which is formalised
alongside). Ultrametrizability of `Y` is not a hypothesis of the delivered
3.14/3.15: the repair does not use it, and it is E2 — supplied here as a
hypothesis — whose own hypotheses require it. The delivered statements are
therefore stronger than the preprint's and imply them.

**Delivered (#83).** Two more files, carrying the complete branch 3.16 and
3.17.

7. `Ext/UltraComplete.lean` — the discrete locus and Theorem 3.16. `UComp Z R`
   is the complete members of `UMet Z R`, with completeness the
   `IsCompleteMetricOn` of `Ext/Completeness.lean` (#80), pinned to Mathlib's
   `CompleteSpace` there. The complete-base normalisation is
   `supConstOffDiag c d` — `d ∨ c` off the diagonal for `c ∈ R∖{0}` — with its
   four properties (`isUltraPMetOn_supConstOffDiag`,
   `topology_supConstOffDiag_eq_bot`, `isCompleteMetricOn_supConstOffDiag`,
   and `edist_uSupConstOffDiag_le`, the last being the audited bound
   `𝒰𝒟^R(d∨c,d) ≤ c` and hence `UComponent_uSupConstOffDiag`). The maximum is
   what keeps the normalisation `R`-valued, where the Archimedean §2.11
   normalisation has to add a constant. `isCompleteMetricOn_uAmalgam` is the
   one-point max-amalgam step: past the index where the Cauchy condition drops
   below the gap at the glue point a sequence cannot straddle the two sides, so
   it settles in one of them. Completeness of the coding metrics is #81's
   `dU_completeSpace`, restated as `isCompleteMetricOn_phiU`. The two theorems
   are `ucomponent_inter_ucomp_not_borel` (componentwise) and
   `ucomp_not_borel_of_card` (the "consequently" clause); as in §2.11 the
   latter runs on `Ψ⁻¹(UComp(Z;R)) = 2^ω∖S` and not by intersecting with a
   component.
8. `Ext/UltraCompleteTransfer.lean` — the general-space locus `UCompOn Y R`
   and Corollary 3.17. `isCompletelyMetrizableSpace_of_mem_UCompOn` is the
   nonemptiness step, which supplies the hypothesis of E2 clause (N1);
   `IsUltraCompIsometricExtensor` is #82's E2 bundle with (N1) as one further
   field, gated on a proof of complete metrizability of `Y` so that the clause
   cannot be asserted outside the range §3 quotes it for.
   `isCompleteMetricOn_restrict_of_mem_UCompOn` is §3's "restriction of a
   complete metric to a closed subspace is complete" in this ambient, and with
   it `IsUltraCompIsometricExtensor.image_ucomp_eq_range_inter` is the audited
   identity `E(UComp(Z;R)) = E(UMet(Z;R)) ∩ UComp(Y;R)`. The transfer reuses
   #82's `ultraExtend` unchanged — it depends only on the witness and on E2
   clauses (1), (2) — with `Ψ` read as the 3.16 witness
   (`codingWitness_subset_UComp`); the two theorems are
   `separable_of_measurableSet_UCompOn_of_ultraCompExtensors` and, via
   Alexandrov–Lavrentiev (E4d),
   `separable_of_isCompletelyMetrizableSpace_UCompOn_of_ultraCompExtensors`.

The audited nonemptiness hypothesis on `UComp(Y;R)` is carried in both 3.17
statements. Ultrametrizability of `Y` is not, for the reason recorded for
3.14/3.15 above, so the delivered statements are again stronger than the
preprint's and imply them.

---

## 8. Archival scope

* `report/report-ja.md` + `lean/IshikiConj51/Conj51/` — frozen archival
  Conjecture 5.1 core (matches arXiv:2608.11023, which the preprint's
  acknowledgements record as the superseded earlier version). Not to be
  edited for this track; its claim IDs stay bound to the companion.
* `lean/IshikiConj51/Ext/{BddPMet,BoundedCoding}.lean` (IshikiExt Layer 1) —
  **reusable as-is** for #56: the coding is literally the preprint's §3.1
  (§6). Its file-header SoT pointers were repointed to this note in #56
  (PR #64).
* `notes/ishiki-extension-audit.md` (branch `audit/ishiki-extension`, PR
  #50) — historical record only; its §1–§3 findings are carried into §5
  here; its §4–§5 PASS verdicts are re-confirmed by §2.4–§2.5.
* Old draft's analytic/coanalytic claims — removed, §5; not part of any
  verification target.
