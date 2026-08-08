-- Conj51.Cardinality
-- Formalises the descriptive-set-theoretic and cardinality prerequisites
-- for the proof of Ishiki Conjecture 5.1 (THM-CONJ51).
--
-- Key claim: LEM-A-EXISTS
--   In ZFC, there exists A ⊆ [0,1] with |A| = ℵ₁ and A not Fσ.
--
-- Status: sorry-stub pending audit.

import Mathlib

/-- LEM-A-EXISTS: There exists a subset of [0,1] of cardinality ℵ₁ that is
    not an Fσ set.
    Proof obligation: ZFC existence argument; depends only on standard set theory.
    Status: SORRY — pending independent audit. -/
theorem lem_A_exists :
    ∃ A : Set ℝ, A ⊆ Set.Icc 0 1 ∧
    (#A = Cardinal.aleph 1) ∧
    ¬ IsSigmaCompact A := by
  sorry
