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
| $F_\sigma$ | Countable union of closed sets |
| $G_\delta$ | Countable intersection of open sets |
| Completely metrizable | A topological space homeomorphic to a complete metric space; equivalently (for subspaces of Polish spaces), a $G_\delta$ subspace (Alexandrov's theorem) |
| Alexandrov's theorem | A subspace of a Polish space is Polish iff it is a $G_\delta$ set |
| Closed-subspace inheritance | A closed subspace of a completely metrizable space is completely metrizable (corollary of Alexandrov: closed sets are $G_\delta$) |

**Warning:** $\operatorname{Met}(D)$ is **not** the set of all metrics on the underlying set of $D$.
A metric on $D$ that induces a non-discrete topology (e.g. a bounded metric identifying
nearby points) is **not** in $\operatorname{Met}(D)$.  This distinction is essential for the proof.

## Lean naming conventions

| Mathematical object | Lean identifier / note |
|---------------------|------------------------|
| `Cardinal.aleph 1` | `ℵ₁` |
| `IsPolishSpace` | Preferred predicate for "Polish space / completely metrizable second-countable" |
| `IsFSigma` | Defined locally in `Conj51/Cardinality.lean` (no Mathlib built-in as of v4.32.2) |
| `Met(D)` as a type | **Not yet defined in Lean** — see `Conj51/MainTheorem.lean` TODO |

*Update as the formalisation develops.*
