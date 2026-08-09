# Terminology and Notation

Quick reference for notation used consistently across the report, paper, and Lean source.

| Symbol / Term | Meaning |
|---------------|---------|
| $D$ | Infinite discrete topological space of cardinality $\aleph_1$ |
| $\operatorname{Met}(D)$ | Set of metrics on $D$ **compatible with the discrete topology** (i.e. the metric topology equals the discrete topology), equipped with the supremum-metric topology.  Japanese: 離散位相と**両立する**距離 (canonical); 「離散位相を誘導する距離」 is a permitted alias.  Do not use 「適合する」 |
| $\rho(d_1, d_2)$ | $\sup_{x,y \in D} \lvert d_1(x,y) - d_2(x,y)\rvert$ (supremum distance on $\operatorname{Met}(D)$) |
| $\aleph_1$ | First uncountable cardinal |
| $\omega_1$ | First uncountable ordinal |
| $\mathfrak{c}$ | Cardinality of the continuum, $2^{\aleph_0}$ |
| $A$ | A fixed non-Fσ subset of $[0,1]$ of cardinality $\aleph_1$ (report 補題 3.2 / paper Lemma `lem:A-exists`) |
| $S^\complement$ | $[0,1] \setminus S$ for $S \subseteq [0,1]$; complements are always taken in $[0,1]$.  The parameter space of the metric family is $A^\complement$ (the former standalone name $Y$ is retired) |
| $d_t$ | Member of the metric family $(d_t)_{t \in [0,1]}$ on $D$; $d_t \in \operatorname{Met}(D) \iff t \in A^\complement$ (report 補題 3.3) |
| $\varphi$ | The embedding $A^\complement \to \operatorname{Met}(D)$, $t \mapsto d_t$ |
| $a_\alpha$ | The $\alpha$-th element of $A$ under a fixed **injective** enumeration $A = \{a_\alpha : \alpha < \omega_1\}$ (report §3.3) |
| $\{p, q\}$ | The two points of $D$ with $d_t(p,q) = 1+t$, used to recover the parameter $t$ from a metric (report §3.3) |
| $C_\alpha$ | The part $\{y_\alpha\} \cup \{x_{\alpha,n} : n \in \mathbb{N}\}$ of the partition $D = \{p,q\} \sqcup \bigsqcup_{\alpha < \omega_1} C_\alpha$ (report §3.3) |
| $y_\alpha$ | The point of $C_\alpha$ at distance $s_n(\alpha,t)$ from each $x_{\alpha,n}$; through it every within-$C_\alpha$ distance is realised |
| $x_{\alpha,n}$ | The other points of $C_\alpha$, indexed by $n \in \mathbb{N}$ |
| $s_n(\alpha, t)$ | $\min(1, \lvert t - a_\alpha \rvert + 1/(n+1))$ for $n \in \mathbb{N}$ — the distance $d_t(y_\alpha, x_{\alpha,n})$ (report §3.3; matches the Lean `spokeLen` indexing) |
| $F_\sigma$ | Countable union of closed sets |
| $G_\delta$ | Countable intersection of open sets |
| Completely metrizable | A topological space homeomorphic to a complete metric space. Not the same as **Polish** (= completely metrizable **and** separable) — do not conflate the two. Japanese: 完全距離化可能 |
| Alexandrov–Lavrentiev $G_\delta$ characterisation | Forward direction (the only one used, via its contrapositive, applied to $X=[0,1]$): $X$ metrizable, $S \subseteq X$ completely metrizable $\Rightarrow$ $S$ is $G_\delta$ in $X$ — stated in this generality (no separability on $X$) as Kechris, *Classical Descriptive Set Theory*, Thm. 3.11 (§3.C, p. 17); general form also in Engelking Thm. 4.3.23–4.3.24 and Willard Thm. 24.12. The reverse direction ($G_\delta$ $\Rightarrow$ completely metrizable) genuinely needs $X$ completely metrizable — e.g. $X=\mathbb{Q}$, $S=X$ is trivially $G_\delta$ in itself but not completely metrizable — and is not used |
| Closed-subspace inheritance | A closed subspace $Y$ of a completely metrizable space $X$ is completely metrizable — proved directly (a complete metric on $X$ restricted to $Y$ is complete, since closed subsets of metric spaces are sequentially closed). **No separability needed**; this is the fact used for $\operatorname{Met}(D)$ |

**Warning:** $\operatorname{Met}(D)$ is **not** the set of all metrics on the underlying set of $D$.
A metric on $D$ that induces a non-discrete topology (e.g. a bounded metric identifying
nearby points) is **not** in $\operatorname{Met}(D)$.  This distinction is essential for the proof.

## Japanese style decisions (Issue #34)

| Decision | Canonical form |
|----------|----------------|
| compatible (metric) | 両立する（「適合する」は廃止） |
| homeomorphism type | 位相型（「同相型」は廃止） |
| isometric isomorphism | 等長同型（「等距離同型」は廃止） |
| unordered pair | 非順序対（「無順序対」は廃止） |
| index set of spokes | $n \in \mathbb{N}$ with $1/(n+1)$（$\mathbb{N}_{\ge 1}$ と $1/n$ は廃止；Lean 実装と一致） |
| complement of $A$ | $A^\complement$（standalone $Y$ は廃止；全体集合 $[0,1]$ は一度だけ明記） |
| retired construction nicknames | 「第 $\alpha$ 星」「中心」「端点」「基準対」「ブロック」は廃止 — $C_\alpha$, $y_\alpha$, $x_{\alpha,n}$, $\{p,q\}$, 「分割の要素」を直接使う（Lean identifiers `StarIndex`, `starBlock` 等は proof engineering 上の内部名として存続） |

## Lean naming conventions

| Mathematical object | Lean identifier / note |
|---------------------|------------------------|
| `Cardinal.aleph 1` | `ℵ₁` |
| `IsPolishSpace` | Preferred predicate for "Polish space / completely metrizable second-countable" |
| `IsFSigma` | Defined locally in `Conj51/Cardinality.lean` (no Mathlib built-in as of v4.32.2) |
| `Met(D)` as a type | `MetD D`, defined in `Conj51/MetD.lean` (Issue #6; relocated there from `MainTheorem.lean` in Issue #7 so the claim modules can import it) as `{d : D → D → ℝ // ∃ h : IsMetricOn d, h.topology = ⊥}` |
| `IsMetricOn` | Raw-function metric axioms (`Conj51/MetD.lean`), used instead of bundling `MetricSpace` so the induced topology can be compared to `⊥` (discrete) separately |
| $\rho$ (sup-distance on $\operatorname{Met}(D)$) | `MetD.edist`, `ℝ≥0∞`-valued (`Conj51/MetD.lean`); realises `EDist`/`PseudoEMetricSpace`/`EMetricSpace (MetD D)` instances, sorry-free |
| Completely metrizable (as a Lean predicate) | `TopologicalSpace.IsCompletelyMetrizableSpace`, native to Mathlib v4.32.2 (`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean`) — no local definition needed |
| `LEM-STAR-METRIC` in Lean | `lem_star_metric` (`Conj51/MetricConstruction.lean`, Issue #7): for `A ⊆ ℝ` with `#↥A = ℵ₁`, the conjunction of `#(StarIndex A) = ℵ₁`, metricity of every `dStar A t` on `[0,1]`, the equivalence `d_t ∈ Met(D) ↔ t ∉ A` (separately `dStar_mem_MetD_iff`), and existence of the parameter map `φ : ↥([0,1] \ A) → MetD (StarIndex A)` — sorry-free.  Corresponds to report 補題 3.3 / paper Lemma `lem:star-metric` |
| `LEM-CLOSED-IMAGE` in Lean | `lem_closed_image` (`Conj51/ClosedEmbedding.lean`, Issue #9): for `A ⊆ ℝ`, the conjunction of the two-sided estimate `edist t s ≤ edist (φ t) (φ s) ≤ 2 * edist t s` (report (C4)) and `IsClosedEmbedding (starParam A)` (report (C5)) — sorry-free. The map `φ` itself is `starParam A : StarParamSpace A → MetD (StarIndex A)`, and `StarParamSpace A := ↥([0,1] \ A)` is the report's `A^∁`.  Corresponds to report 補題 3.4 / paper Lemma `lem:closed-image` |
| Relabelling `Met(D)` along a bijection | `MetD.relabelIsometry` (`Conj51/Relabel.lean`, Issue #9): `(σ : D ≃ E) : MetD E ≃ᵢ MetD D`. `Met(D)` depends on `D` only through `#D`, so the construction on the concrete `StarIndex A` transfers to an arbitrary `D` with `#D = ℵ₁` (report §3.2) — sorry-free |
| Alexandrov–Lavrentiev direction in Lean | `isGδ_of_isCompletelyMetrizableSpace` (`Conj51/GDeltaComplete.lean`, Issue #23): `{X} [MetricSpace X] {Y : Set X} (h : IsCompletelyMetrizableSpace ↥Y) : IsGδ Y` — proved from scratch (absent from Mathlib v4.32.2), with **no separability assumption**, sorry-free; this matches report 定理 1.1 / paper Theorem `thm:background-gdelta` exactly. Note the `IsGδ` is taken in the **ambient** `X`; the report's "Gδ in [0,1]" phrasing is recovered inside `isFSigma_of_isGdelta_sdiff`, which intersects with the closed set `[0,1]`, so no ambient-conversion lemma is needed |
| `THM-CONJ51` in Lean | `thm_conj51` (`Conj51/MainTheorem.lean`): `(D : Type*) (hD : #D = Cardinal.aleph 1) : ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)` — statement unchanged since Issue #6, proved sorry-free (Issue #9). The whole of report §4 is proved in `thm_conj51_of_lavrentiev`, which carries the one Mathlib-absent ingredient as the explicit hypothesis `lavrentiev : ∀ Y : Set ℝ, IsCompletelyMetrizableSpace ↥Y → IsGδ Y`; `thm_conj51` discharges it with `isGδ_of_isCompletelyMetrizableSpace` at `X := ℝ`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.  Corresponds to report 定理 2.1 / paper Theorem `thm:conj51` |

Stable claim IDs (`LEM-A-EXISTS`, `LEM-STAR-METRIC`, `LEM-CLOSED-IMAGE`, `THM-CONJ51`)
remain in use in `STATUS.md`, `notes/proof-audit.md`, and Lean declarations/comments as
internal management identifiers; they no longer appear as reader-facing theorem names in
the report or the paper (Issue #34).  Reader-facing numbering: report 補題 3.1（閉集合の濃度）,
補題 3.2 = LEM-A-EXISTS, 補題 3.3 = LEM-STAR-METRIC, 補題 3.4 = LEM-CLOSED-IMAGE,
定理 2.1 = THM-CONJ51; paper `lem:closed-card`, `lem:A-exists`, `lem:star-metric`,
`lem:closed-image`, `thm:conj51`.

*Update as the formalisation develops.*
