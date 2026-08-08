-- Conj51.Cardinality
-- Formalises the descriptive-set-theoretic and cardinality prerequisites
-- for the proof of Ishiki Conjecture 5.1 (THM-CONJ51).
--
-- Key claim: LEM-A-EXISTS
--   In ZFC, there exists A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
--
-- Lean note: "A is not Fσ" means A cannot be expressed as a countable union
-- of closed sets.  The correct Mathlib predicate is the complement of
-- `Set.IsGdelta` (an Fσ set is a Gδ in the complement sense), or directly:
-- ¬ ∃ (F : ℕ → Set ℝ), (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n.
-- `IsSigmaCompact` is a DIFFERENT property (countable union of compact sets)
-- and must NOT be used as a proxy for Fσ in the final formalisation.
-- Mathlib library gap: as of v4.32.2, there is no single predicate `IsFSigma`
-- in Mathlib; the definition must be unfolded explicitly.
-- See notes/proof-audit.md (sorry tracker) for status.
--
-- Status: sorry-stub pending audit.

import Mathlib

/-- Predicate: A is an Fσ set (countable union of closed sets). -/
def IsFSigma (A : Set ℝ) : Prop :=
  ∃ (F : ℕ → Set ℝ), (∀ n, IsClosed (F n)) ∧ A = ⋃ n, F n

/-- LEM-A-EXISTS: There exists a subset of [0,1] of cardinality ℵ₁ that is
    not an Fσ set.
    Proof obligation: ZFC existence argument; depends only on standard set theory.
    Status: SORRY — pending independent audit. -/
theorem lem_A_exists :
    ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧
    (#A = Cardinal.aleph 1) ∧
    ¬ IsFSigma A := by
  sorry
