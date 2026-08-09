# Terminology and Notation

Quick reference for notation used consistently across the report, paper, and Lean source.

| Symbol / Term | Meaning |
|---------------|---------|
| $D$ | Infinite discrete topological space of cardinality $\aleph_1$ |
| $\operatorname{Met}(D)$ | Set of metrics on $D$ **compatible with the discrete topology** (i.e. the metric topology equals the discrete topology), equipped with the supremum-metric topology |
| $\rho(d_1, d_2)$ | $\sup_{x,y \in D} \lvert d_1(x,y) - d_2(x,y)\rvert$ (supremum distance on $\operatorname{Met}(D)$) |
| $\aleph_1$ | First uncountable cardinal |
| $\omega_1$ | First uncountable ordinal |
| $A$ | A fixed non-Fσ subset of $[0,1]$ of cardinality $\aleph_1$ (from LEM-A-EXISTS) |
| $Y$ | $[0,1] \setminus A$ |
| $d_t$ | Star-type metric on $D$ compatible with the discrete topology, parametrised by $t \in Y$ |
| $\varphi$ | The embedding $Y \to \operatorname{Met}(D)$, $t \mapsto d_t$ |
| $a_\alpha$ | The $\alpha$-th element of $A$ under a fixed **injective** enumeration $A = \{a_\alpha : \alpha < \omega_1\}$ (report §3.2) |
| $\{p, q\}$ | 基準対 (reference pair): the two points of $D$ with $d_t(p,q) = 1+t$, used to recover the parameter $t$ from a metric (report §3.2) |
| $C_\alpha$ | 第 $\alpha$ 星 (the $\alpha$-th star): the block $\{y_\alpha\} \cup \{x_{\alpha,n} : n \in \mathbb{N}_{\ge 1}\}$ of $D$ |
| $y_\alpha$ | 中心 (centre) of the star $C_\alpha$ |
| $x_{\alpha,n}$ | 端点 (endpoint) of the star $C_\alpha$, indexed by $n \in \mathbb{N}_{\ge 1}$ |
| $s_n(\alpha, t)$ | $\min(1, \lvert t - a_\alpha \rvert + 1/n)$ — the centre-to-endpoint distance $d_t(y_\alpha, x_{\alpha,n})$ (report §3.2) |
| ブロック (block) | An element of the partition $D = \{p,q\} \sqcup \bigsqcup_{\alpha < \omega_1} C_\alpha$ (report §3.2) |
| $F_\sigma$ | Countable union of closed sets |
| $G_\delta$ | Countable intersection of open sets |
| Completely metrizable | A topological space homeomorphic to a complete metric space. Not the same as **Polish** (= completely metrizable **and** separable) — do not conflate the two |
| Alexandrov–Lavrentiev $G_\delta$ characterisation | For $X$ **Polish** (separable **and** completely metrizable), $S \subseteq X$ is completely metrizable iff $S$ is $G_\delta$ in $X$. (The forward direction alone — $S$ completely metrizable $\Rightarrow$ $S$ is $G_\delta$ in $X$ — holds more generally for any separable metrizable $X$, without requiring $X$ itself to be complete; that is the direction the report actually uses, via its contrapositive. The reverse direction genuinely needs $X$ complete: e.g. $X=\mathbb{Q}$, $S=X$ is trivially $G_\delta$ in itself but not completely metrizable.) Used only for $X=[0,1]$ (Polish); **must not** be invoked for $\operatorname{Met}(D)$, which is not separable |
| Closed-subspace inheritance | A closed subspace $C$ of a completely metrizable space $Z$ is completely metrizable — proved directly (a complete metric on $Z$ restricted to $C$ is a complete metric on $C$, since closed subsets of metric spaces are sequentially closed). **No separability needed**; this is the version used for $\operatorname{Met}(D)$ |

**Warning:** $\operatorname{Met}(D)$ is **not** the set of all metrics on the underlying set of $D$.
A metric on $D$ that induces a non-discrete topology (e.g. a bounded metric identifying
nearby points) is **not** in $\operatorname{Met}(D)$.  This distinction is essential for the proof.

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
| `LEM-STAR-METRIC` in Lean | `lem_star_metric` (`Conj51/MetricConstruction.lean`, Issue #7): for `A ⊆ ℝ` with `#↥A = ℵ₁`, the conjunction of `#(StarIndex A) = ℵ₁`, metricity of every `dStar A t` on `[0,1]`, the 系 `d_t ∈ Met(D) ↔ t ∉ A` (separately `dStar_mem_MetD_iff`), and existence of the parameter map `φ : ↥([0,1] \ A) → MetD (StarIndex A)` — sorry-free |
| `LEM-CLOSED-IMAGE` in Lean | `lem_closed_image` (`Conj51/ClosedEmbedding.lean`, Issue #9): for `A ⊆ ℝ`, the conjunction of the two-sided estimate `edist t s ≤ edist (φ t) (φ s) ≤ 2 * edist t s` (report (C4)) and `IsClosedEmbedding (starParam A)` (report (C5)) — sorry-free. The map `φ` itself is `starParam A : StarParamSpace A → MetD (StarIndex A)`, and `StarParamSpace A := ↥([0,1] \ A)` is the report's `Y` |
| Relabelling `Met(D)` along a bijection | `MetD.relabelIsometry` (`Conj51/Relabel.lean`, Issue #9): `(σ : D ≃ E) : MetD E ≃ᵢ MetD D`. `Met(D)` depends on `D` only through `#D`, so the construction on the concrete `StarIndex A` transfers to an arbitrary `D` with `#D = ℵ₁` (report §3.2/§3.8) — sorry-free |
| Alexandrov–Lavrentiev direction in Lean | `isGδ_of_isCompletelyMetrizableSpace` (`Conj51/GDeltaComplete.lean`, Issue #23): `{X} [MetricSpace X] {Y : Set X} (h : IsCompletelyMetrizableSpace ↥Y) : IsGδ Y` — proved from scratch (absent from Mathlib v4.32.2), in full generality with **no separability assumption**, sorry-free. Note the `IsGδ` is taken in the **ambient** `X`; the report's "Gδ in [0,1]" phrasing is recovered inside `isFSigma_of_isGdelta_sdiff`, which intersects with the closed set `[0,1]`, so no ambient-conversion lemma is needed |
| `THM-CONJ51` in Lean | `thm_conj51` (`Conj51/MainTheorem.lean`): `(D : Type*) (hD : #D = Cardinal.aleph 1) : ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)` — statement unchanged since Issue #6, now **proved sorry-free** (Issue #9). The whole of report §4 is proved in `thm_conj51_of_lavrentiev`, which carries the one Mathlib-absent ingredient as the explicit hypothesis `lavrentiev : ∀ Y : Set ℝ, IsCompletelyMetrizableSpace ↥Y → IsGδ Y`; `thm_conj51` discharges it with `isGδ_of_isCompletelyMetrizableSpace` at `X := ℝ`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` |

*Update as the formalisation develops.*
