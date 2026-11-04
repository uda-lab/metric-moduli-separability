# Terminology and Notation

Terminology and notation source of truth for both tracks: the archival
Conjecture 5.1 track (`report/report-ja.md`, `paper/`, `lean/IshikiConj51/Conj51/`)
and the public-preprint Borel track (arXiv:2608.19618, `lean/IshikiConj51/Ext/`).
`notes/descriptive-set-theory-ja.md` is the expository background note for the
Borel track and defers to this file for terminology decisions.

## Public-preprint (Borel) track: ambient spaces and external theorems

| Symbol / Term | Meaning |
|---------------|---------|
| $\operatorname{CPM}(X)$ | Continuous pseudometrics $d : X \times X \to [0,\infty)$ on a topological space $X$, with the supremum metric $\mathcal{D}_X(d,e) = \sup_{(x,y)} \lvert d(x,y) - e(x,y) \rvert$ (extended-valued; the topology is equivalently induced by $\min\{\mathcal{D}_X, 1\}$) |
| $\operatorname{Met}(X)$ | Metrics in $\operatorname{CPM}(X)$ compatible with the topology of $X$ — no boundedness or uniform-discreteness restriction |
| $\operatorname{BMet}(X)$ | Bounded members of $\operatorname{Met}(X)$; Koshino's $AM(X)$ (bounded admissible metrics) is identified with $\operatorname{BMet}(X)$, **not** with $\operatorname{Met}(X)$ |
| $\operatorname{Comp}(X)$ | Complete members of $\operatorname{Met}(X)$ |
| $\mathbf{M}_{<\infty}(Z)$, $\mathfrak{c}$ | Components of $\operatorname{Met}(Z)$ under $d \sim e \iff \mathcal{D}_Z(d,e) < \infty$; each component $\mathfrak{c}$ is clopen and path-connected |
| range set $R$ | $R \subseteq [0,\infty)$ with $0 \in R$ (English term kept; no Japanese coinage is fixed) |
| characteristic (range set) | $0$ is an accumulation point of $R \setminus \{0\}$ — equivalently, a strictly decreasing $r : \mathbb{N} \to R \setminus \{0\}$ with $r(n) \to 0$ exists (English term kept; no Japanese coinage is fixed) |
| $\operatorname{UCPM}(Y;R)$ | Continuous $R$-valued pseudo-ultrametrics on $Y$, with the non-Archimedean uniform distance $\mathcal{UD}^R_Y(d,e) = \inf\{\varepsilon \in R \cup \{\infty\} : d \le e \vee \varepsilon,\ e \le d \vee \varepsilon\}$ (extended-valued) |
| $\operatorname{UMet}(Y;R)$ | Compatible $R$-valued ultrametrics; $R$-components $\mathfrak{c}^R \in \mathbf{UM}_{<\infty}(Z;R)$ via $\mathcal{UD}^R < \infty$ |
| $\operatorname{UComp}(Y;R)$ | Complete members of $\operatorname{UMet}(Y;R)$ |
| E1 | Ishiki, *An isometric extensor of metrics*, arXiv:2407.03030 v4, Theorem 1.1 — the isometric extensor $E : \operatorname{Met}(A) \to \operatorname{Met}(X)$ with its pseudometric-level $\tilde{E}$; exact quote in `notes/borel-preprint-audit.md` §3 |
| E2 | Ishiki, *A factorization of metric spaces*, Colloq. Math. 174 (2023), Theorem 4.7 — the ultrametric extensor $\Sigma$; E2 supplies no $\operatorname{UCPM}$-level extensor ($\Sigma$'s domain is $\operatorname{Met}(F)$; audit §3) |
| E3 | Koshino, *On the Borel complexity and the complete metrizability of spaces of metrics*, Anal. Geom. Metr. Spaces 12 (2024) — $X$ separable metrizable: $X$ σ-compact $\iff$ $AM(X)$ completely metrizable |
| $\operatorname{BCPM}(X)$ | Bounded members of $\operatorname{CPM}(X)$, i.e. bounded continuous pseudometrics on $X$; the pseudometric-level analogue of $\operatorname{BMet}(X)$ |
| $P_d$ | For fixed $d \in \operatorname{CPM}(X)$, $P_d := \{p \in \operatorname{CPM}(X) \mid \mathcal{D}_X(p,d) < \infty\}$; the finite-distance ambient piece around $d$ in $\operatorname{CPM}(X)$, which need not be a single component of $\operatorname{Met}(X)$ |

External-theorem labels E1/E2/E3 (and E4 for the standard descriptive-set-theory
inputs) are fixed by `notes/borel-preprint-audit.md` §3, which quotes each
statement exactly; `notes/borel-manuscript-20260827-audit.md` §4 carries them
unchanged and adds E5 (Ishiki's interpolation theorem) and E6 (Hausdorff's
open-image theorem); `notes/borel-manuscript-20261103-audit.md` §4 keeps them
and re-scopes E2c as E2c′. They enter Lean only as explicit hypotheses.
A `c` suffix marks a **construction-specific** dependency — data taken from the
*proof* of the named source theorem rather than from its statement, such as E1c
(Lemma 4.4's point estimate, from the proof of E1's Theorem 1.1) and E2c (the
clopen-net retraction, quotient model and max-form extensor, from the proof of
E2's Theorem 4.7) — and such a dependency must never be added as a clause of
the theorem-level bundle whose label it is suffixed from.

## Japanese terminology (both tracks)

| English | 日本語 | 備考 |
|---|---|---|
| compatible (metric) | **両立する**距離 | 「離散位相を誘導する距離」は許容される別名；「適合する」は廃止 |
| descriptive set theory | **記述集合論** | |
| Polish space | **ポーランド空間** | 可分かつ完備距離化可能 |
| Borel set / Borel σ-algebra | **ボレル集合** / **Borel σ-代数** | |
| Borel isomorphism | **Borel 同型** | 位相同型とは異なる（稠密性・収束を保存しない） |
| homeomorphism | **位相同型** | |
| standard Borel space | **標準 Borel 空間** | |
| analytic set | **解析集合** | `Σ¹₁`；「解析的集合」は用いない |
| coanalytic set | **余解析的集合** | `Π¹₁`；初出では `coanalytic set, Π¹₁` を併記 |
| perfect set | **完全集合** | 閉かつ孤立点を持たない集合．「完全空間」という語は完備 (complete) と紛らわしいので避け，「孤立点を持たない」と明示するか「完全集合」を使う |
| perfect set theorem / property | **完全集合定理** / **完全集合性** (PSP) | |
| Bernstein set | **ベルンシュタイン集合** | |
| Cantor space | **カントール空間** | `2^ω` |
| Baire space | **ベール空間** | `ω^ω` |
| completely metrizable | **完備距離化可能** | Polish とは異なる（可分性を含まない）；混同しない |
| ultrametric | **超距離** | |
| ultrametric space | **超距離空間** | |
| ultrametrizable | **超距離化可能** | |
| non-Archimedean | **非アルキメデス的** | track 名などのより広い形容詞として使用 |
| strong triangle inequality | **強三角不等式** | $d(x,z) \le \max\{d(x,y), d(y,z)\}$ |
| range set / characteristic | 英語のまま | 十分に確立した日本語標準訳が無いため訳語を定めず，定義（上表）とともに英語で用いる |
| epsilon-separated set | **ε-分離集合**（ε-離散集合） | $A \subseteq X$ で，任意の相異なる $x,y \in A$ に対して $d(x,y) \geq \varepsilon$ を満たす集合．大津幸男「リーマン多様体とその極限」，数学メモアール第3巻，日本数学会，2004，pp. 68–69，<https://www.mathsoc.jp/publication/SugakuMemoirs/sugaku-memoirs-03-1.pdf> は「ε-離散集合」を用い，加須栄篤「無限ネットワークの可解理想境界」，p. 2，<https://www.rs.kagu.tus.ac.jp/~koike/2016kiroku-kasue.pdf> は「ε-分離集合」を用いる．文献には $>\varepsilon$ の規約もあるため，このプロジェクトでは不等号を定義で明示する |
| epsilon-net | **ε-ネット** | 任意の $x \in X$ に対して，ある $a \in A$ が存在して $d(x,a) < \varepsilon$ となる部分集合．任意の $\varepsilon>0$ に有限な ε-ネットをもつことが全有界性（プレコンパクト性）に相当し，極大 ε-分離集合は ε-ネットになる．塩谷隆「最適輸送理論とリッチ曲率」，『最適輸送理論とリッチ曲率』，数学メモアール第8巻，日本数学会，2017，§2.3，pp. 45–47，<https://www.mathsoc.jp/assets/pdf/publications/memoirs/sugaku-memoir-08.pdf> |
| maximal epsilon-separated set | **極大 ε-分離集合**（極大 ε-離散集合） | ε-分離集合の包含関係に関する極大元．最大濃度の集合ではなく，点を付加しても ε-分離性を保てない集合を指す．上記の大津幸男の資料が「極大 ε-離散集合」を用いる．塩谷隆の資料は同じ極大性の議論を ε-ネットの言葉で行う．一般の存在は包含関係に関する Zorn の補題で得る |
| clopen partition | **開かつ閉な集合からなる分割** | 位相空間 $X$ の分割 $\mathcal{P}$ で，各 $P \in \mathcal{P}$ が $X$ で開かつ閉であるもの．「開集合」「閉集合」「分割」という既に固定した語を組み合わせた記述であり，新たな造語ではないため外部の引用は不要 |
| one-point amalgamation | 英語のまま | $X_0$ と $X_1$ が一点 $z$ だけを共有する距離空間または超距離空間に対し，$x \in X_0 \setminus \{z\}$，$y \in X_1 \setminus \{z\}$ の距離を，距離の場合は $d_0(x,z)+d_1(z,y)$，超距離の場合は $\max\{d_0(x,z),d_1(z,y)\}$ と定めて $X_0\cup X_1$ に拡張する構成．両片が完備なら結果も完備である．共通部分を等長写像で貼り合わせる一般構成の一点の場合に当たる．「貼り合わせ」「接着」に相当する記述はあるが，この一般構成の標準名について信頼できる出典を確認できなかったため，英語を保持する |
| metric interpolation / interpolation theorem | **補間定理**（metric interpolation） | `notes/borel-manuscript-20260827-audit.md` §4 の E5（Ishiki の *An interpolation of metrics and spaces of metrics*）を指す語．離散族をなす閉集合族 $\{A_i\}$，$d \in \operatorname{Met}(X)$，および $e_i \in \operatorname{Met}(A_i)$ に対し，$m \in \operatorname{Met}(X)$ を $m\!\restriction_{A_i^2}=e_i$ かつ $\mathcal{D}_X(m,d)=\sup_i \mathcal{D}_{A_i}(e_i,d\!\restriction_{A_i^2})$ となるように構成する定理である．ここでいう interpolation は，E1 の isometric extensor（等長 extensor）とは異なる構成であるだけでなく，関数解析学の作用素の補間理論（Riesz–Thorin の補間定理など）とも無関係であり，両者は「補間」という語を共有するにすぎない別概念である |
| component (project-specific finite-distance class) | **成分** | このプロジェクトでいう「component」／「成分」は，$\mathbf{M}_{<\infty}(Z)$ では $\mathcal{D}_Z(d,e)<\infty$，$\mathbf{UM}_{<\infty}(Y;R)$ では $\mathcal{UD}^R_Y(d,e)<\infty$ による有限距離同値類であり，位相的連結成分ではない．超距離空間は位相的には完全不連結で連結成分が一点集合である一方，$\operatorname{UMet}(Y;R)$ の有限距離 $R$-component は大きく非自明になり得る |

## Archival Conjecture 5.1 track: symbols

Quick reference for notation used consistently across the report, paper, and
archival Lean source.

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
| $s_n(\alpha, t)$ | $\min(1, \lvert t - a_\alpha \rvert + 1/(n+1))$ for $n \in \mathbb{N}$ — the distance $d_t(y_\alpha, x_{\alpha,n})$ (report §3.3; matches the indexing of the Lean `starSpoke` definition in `Conj51/MetricConstruction.lean`) |
| $F_\sigma$ | Countable union of closed sets |
| $G_\delta$ | Countable intersection of open sets |
| Completely metrizable | A topological space homeomorphic to a complete metric space. Not the same as **Polish** (= completely metrizable **and** separable) — do not conflate the two. Japanese: 完備距離化可能 |
| Alexandrov–Lavrentiev $G_\delta$ characterisation | Forward direction (the only one used, via its contrapositive, applied to $X=[0,1]$): $X$ metrizable, $S \subseteq X$ completely metrizable $\Rightarrow$ $S$ is $G_\delta$ in $X$ — stated in this generality (no separability on $X$) as Kechris, *Classical Descriptive Set Theory*, Thm. 3.11 (§3.C, p. 17); general form also in Engelking Thm. 4.3.23–4.3.24 and Willard Thm. 24.12. The reverse direction ($G_\delta$ $\Rightarrow$ completely metrizable) genuinely needs $X$ completely metrizable — e.g. $X=\mathbb{Q}$, $S=X$ is trivially $G_\delta$ in itself but not completely metrizable — and is not used |
| Closed-subspace inheritance | A closed subspace $Y$ of a completely metrizable space $X$ is completely metrizable — proved directly (a complete metric on $X$ restricted to $Y$ is complete, since closed subsets of metric spaces are sequentially closed). **No separability needed**; this is the fact used for $\operatorname{Met}(D)$ |

**Warning:** $\operatorname{Met}(D)$ is **not** the set of all metrics on the underlying set of $D$.
A metric on $D$ that induces a non-discrete topology (e.g. a bounded metric identifying
nearby points) is **not** in $\operatorname{Met}(D)$.  This distinction is essential for the proof.

## Japanese style decisions

| Decision | Canonical form |
|----------|----------------|
| compatible (metric) | 両立する（「適合する」は廃止） |
| homeomorphism type | 位相型（「同相型」は廃止） |
| isometric isomorphism | 等長同型（「等距離同型」は廃止） |
| unordered pair | 非順序対（「無順序対」は廃止） |
| index set of spokes | $n \in \mathbb{N}$ with $1/(n+1)$（$\mathbb{N}_{\ge 1}$ と $1/n$ は廃止；Lean 実装と一致） |
| complement of $A$ | $A^\complement$（standalone $Y$ は廃止；全体集合 $[0,1]$ は一度だけ明記） |
| font for sets/spaces ($\mathbf{N}, \mathbf{R}$ vs $\mathbb{N}, \mathbb{R}$) | $\mathbf{N}, \mathbf{R}$ と $\mathbb{N}, \mathbb{R}$ はともに許容（タイプセット環境によって劣悪な黒板太字を避けるため） |
| retired construction nicknames | 「第 $\alpha$ 星」「中心」「端点」「基準対」「ブロック」は廃止 — $C_\alpha$, $y_\alpha$, $x_{\alpha,n}$, $\{p,q\}$, 「分割の成分」を直接使う（Lean identifiers `StarIndex`, `starBlock` 等は proof engineering 上の内部名として存続） |

## Lean naming conventions (archival track)

| Mathematical object | Lean identifier / note |
|---------------------|------------------------|
| `Cardinal.aleph 1` | `ℵ₁` |
| `IsPolishSpace` | Preferred predicate for "Polish space / completely metrizable second-countable" |
| `IsFSigma` | Defined locally in `Conj51/Cardinality.lean` (no Mathlib built-in as of v4.32.2) |
| `Met(D)` as a type | `MetD D`, defined in `Conj51/MetD.lean` as `{d : D → D → ℝ // ∃ h : IsMetricOn d, h.topology = ⊥}` |
| `IsMetricOn` | Raw-function metric axioms (`Conj51/MetD.lean`), used instead of bundling `MetricSpace` so the induced topology can be compared to `⊥` (discrete) separately |
| $\rho$ (sup-distance on $\operatorname{Met}(D)$) | `MetD.edist`, `ℝ≥0∞`-valued (`Conj51/MetD.lean`); realises `EDist`/`PseudoEMetricSpace`/`EMetricSpace (MetD D)` instances, sorry-free |
| Completely metrizable (as a Lean predicate) | `TopologicalSpace.IsCompletelyMetrizableSpace`, native to Mathlib v4.32.2 (`Mathlib/Topology/Metrizable/CompletelyMetrizable.lean`) — no local definition needed |
| `LEM-STAR-METRIC` in Lean | `lem_star_metric` (`Conj51/MetricConstruction.lean`): for `A ⊆ ℝ` with `#↥A = ℵ₁`, the conjunction of `#(StarIndex A) = ℵ₁`, metricity of every `dStar A t` on `[0,1]`, the equivalence `d_t ∈ Met(D) ↔ t ∉ A` (separately `dStar_mem_MetD_iff`), and existence of the parameter map `φ : ↥([0,1] \ A) → MetD (StarIndex A)` — sorry-free.  Corresponds to report 補題 3.3 / paper Lemma `lem:star-metric` |
| `LEM-CLOSED-IMAGE` in Lean | `lem_closed_image` (`Conj51/ClosedEmbedding.lean`): for `A ⊆ ℝ`, the conjunction of the two-sided estimate `edist t s ≤ edist (φ t) (φ s) ≤ 2 * edist t s` (report (C4)) and `IsClosedEmbedding (starParam A)` (report (C5)) — sorry-free. The map `φ` itself is `starParam A : StarParamSpace A → MetD (StarIndex A)`, and `StarParamSpace A := ↥([0,1] \ A)` is the report's `A^∁`.  Corresponds to report 補題 3.4 / paper Lemma `lem:closed-image` |
| Relabelling `Met(D)` along a bijection | `MetD.relabelIsometry` (`Conj51/Relabel.lean`): `(σ : D ≃ E) : MetD E ≃ᵢ MetD D`. `Met(D)` depends on `D` only through `#D`, so the construction on the concrete `StarIndex A` transfers to an arbitrary `D` with `#D = ℵ₁` (report §3.2) — sorry-free |
| Alexandrov–Lavrentiev direction in Lean | `isGδ_of_isCompletelyMetrizableSpace` (`Conj51/GDeltaComplete.lean`): `{X} [MetricSpace X] {Y : Set X} (h : IsCompletelyMetrizableSpace ↥Y) : IsGδ Y` — proved from scratch (absent from Mathlib v4.32.2), with **no separability assumption**, sorry-free; this matches report 定理 1.1 / paper Theorem `thm:background-gdelta` exactly. Note the `IsGδ` is taken in the **ambient** `X`; the report's "Gδ in [0,1]" phrasing is recovered inside `isFSigma_of_isGdelta_sdiff`, which intersects with the closed set `[0,1]`, so no ambient-conversion lemma is needed |
| `THM-CONJ51` in Lean | `thm_conj51` (`Conj51/MainTheorem.lean`): `(D : Type*) (hD : #D = Cardinal.aleph 1) : ¬ TopologicalSpace.IsCompletelyMetrizableSpace (MetD D)` — proved sorry-free. The whole of report §4 is proved in `thm_conj51_of_lavrentiev`, which carries the one Mathlib-absent ingredient as the explicit hypothesis `lavrentiev : ∀ Y : Set ℝ, IsCompletelyMetrizableSpace ↥Y → IsGδ Y`; `thm_conj51` discharges it with `isGδ_of_isCompletelyMetrizableSpace` at `X := ℝ`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.  Corresponds to report 定理 2.1 / paper Theorem `thm:conj51` |

Stable claim IDs (`LEM-A-EXISTS`, `LEM-STAR-METRIC`, `LEM-CLOSED-IMAGE`, `THM-CONJ51`)
remain in use in `notes/proof-audit.md` and in Lean declarations/comments as
internal identifiers of the archival track; they no longer appear as reader-facing
theorem names in the report or the paper.  Reader-facing numbering: report
補題 3.1（閉集合の濃度）, 補題 3.2 = LEM-A-EXISTS, 補題 3.3 = LEM-STAR-METRIC,
補題 3.4 = LEM-CLOSED-IMAGE, 定理 2.1 = THM-CONJ51; paper `lem:closed-card`,
`lem:A-exists`, `lem:star-metric`, `lem:closed-image`, `thm:conj51`.

Lean naming for the public-preprint track is recorded per theorem in
`notes/borel-preprint-audit.md` §7.
