# Terminology and Notation

Quick reference for notation used consistently across the report, paper, and Lean source.

| Symbol / Term | Meaning |
|---------------|---------|
| $D$ | Infinite discrete topological space |
| $\operatorname{Met}(D)$ | Set of all metrics on $D$, with supremum-metric topology |
| $\rho(d, d')$ | $\sup_{x,y \in D} \lvert d(x,y) - d'(x,y)\rvert$ (supremum distance on $\operatorname{Met}(D)$) |
| $\aleph_1$ | First uncountable cardinal |
| $\omega_1$ | First uncountable ordinal |
| $A$ | A fixed non-Fσ subset of $[0,1]$ of cardinality $\aleph_1$ (from LEM-A-EXISTS) |
| $Y$ | $[0,1] \setminus A$ |
| $d_t$ | Star-type metric on $D$ parametrised by $t \in Y$ |
| $\varphi$ | The embedding $Y \to \operatorname{Met}(D)$, $t \mapsto d_t$ |
| $F_\sigma$ | Countable union of closed sets |
| $G_\delta$ | Countable intersection of open sets |
| Completely metrizable | A topological space homeomorphic to a complete metric space |

## Lean naming conventions

| Mathematical object | Lean name / namespace |
|---------------------|-----------------------|
| `Cardinal.aleph 1` | `ℵ₁` |
| `CompleteSpace` | `Mathlib.Topology.UniformSpace.Completion` |
| `IsSigmaCompact` | proxy for Fσ-compactness in metric context |

*Update as the formalisation develops.*
