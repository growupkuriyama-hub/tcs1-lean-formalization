import LeanCfgProject.TCS1.MainTheoremSemanticPackage
import LeanCfgProject.TCS1.MaterializedProductionCost

/-!
# TCS #1 v79: materialized paper-facing main theorem package

This module closes the implementation-facing version of the main learning
theorem.  In the finite-alphabet setting used by the manuscript, reconstructed
hypotheses are represented by explicit finite production tables; the
table-backed CYK parser decides exactly the reconstructed language; the
materialized conservative learner is extensionally identical to the semantic
Gold learner; and every update is covered by one explicit prefix-polynomial
combinatorial work envelope including production-table materialization.

The cost statement counts explicit finite scans/comparisons.  It is not a
machine-code cost semantics for Lean's evaluator.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section MainTheoremMaterializedPackage

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M] [DecidableEq M]

/-- Gold-stabilization conclusion for the explicit production-table learner. -/
def MaterializedGoldConclusion
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (datum : Nat → Word α) : Prop :=
  ∃ n₀,
    (BatchLanguage H
        (materializedConservativeHypothesis H datum n₀) = L
      ∧
      ∀ j,
        materializedConservativeHypothesis H datum (n₀ + j) =
          materializedConservativeHypothesis H datum n₀)
    ∨
    (∃ n,
      n₀ ≤ n ∧
      materializedConservativeHypothesis H datum (n + 1) ≠
        materializedConservativeHypothesis H datum n ∧
      BatchLanguage H
        (materializedConservativeHypothesis H datum (n + 1)) = L
      ∧
      ∀ j,
        materializedConservativeHypothesis H datum ((n + 1) + j) =
          materializedConservativeHypothesis H datum (n + 1))

/--
Paper-facing materialized core of the fixed-h learning theorem.

It packages exact table-backed membership, the full materialized update bound,
finite positive characteristic data, and Gold identification of the actual
table-backed conservative run.
-/
theorem indexedFixedH_learning_materialized_core
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈ LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    (∀ K : Finset (Word α),
      ∀ word : Word α,
        reconstructionMaterializedCYKMember H K word = true
          ↔
        word ∈ BatchLanguage H K)
    ∧
    (∀ n : Nat,
      reconstructionProductionTableScanEnvelope
          (Fintype.card
            (ReconstructionFactorSlot
              (materializedConservativeHypothesis H datum n)))
          (Fintype.card α)
        +
      (reconstructionUnitClosureTableScanEnvelope
          (Fintype.card
            (ReconstructionFactorSlot
              (materializedConservativeHypothesis H datum n)))
        +
       (cykNaiveComparisonEnvelope
          (Fintype.card
            (ReconstructionFactorSlot
              (materializedConservativeHypothesis H datum n)))
          (datum (n + 1)).length
        +
        reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteAccumulatedSample datum (n + 1)))))
        ≤
      conservativeMaterializedUpdateWorkEnvelope
        (Fintype.card α)
        (positiveDataPrefixNorm datum (n + 1)))
    ∧
    (∃ C : Finset (Word α),
      (↑C : Set (Word α)) ⊆
        LeastClosedLanguage G.toMixedRules A
      ∧
      BatchLanguage H C =
        LeastClosedLanguage G.toMixedRules A)
    ∧
    MaterializedGoldConclusion
      H
      (LeastClosedLanguage G.toMixedRules A)
      datum := by
  obtain ⟨C, hCpos, hchar⟩ :=
    indexedFixedH_exists_characteristic_sample
      H G A hsub
  refine ⟨?_, ?_, ⟨C, hCpos, hchar⟩, ?_⟩
  · intro K word
    exact
      reconstructionMaterializedCYKMember_eq_true_iff
        H K word
  · intro n
    exact
      materializedConservative_update_work_le_prefix
        H datum n
  · unfold MaterializedGoldConclusion
    exact
      materializedConservative_gold_identification_explicit
        H
        (LeastClosedLanguage G.toMixedRules A)
        C
        hchar
        hsub
        datum
        hpositive
        hcoverage

/--
Materialized form of Corollary (poly-update): table construction, unit closure,
CYK membership, and a possible reconstruction are jointly bounded by one
explicit polynomial in the positive-data prefix (with the fixed alphabet size
as a constant parameter).
-/
theorem corollary_poly_update_materialized
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionProductionTableScanEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (materializedConservativeHypothesis H datum n)))
        (Fintype.card α)
      +
    (reconstructionUnitClosureTableScanEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (materializedConservativeHypothesis H datum n)))
      +
     (cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (materializedConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      +
      reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteAccumulatedSample datum (n + 1)))))
      ≤
    conservativeMaterializedUpdateWorkEnvelope
      (Fintype.card α)
      (positiveDataPrefixNorm datum (n + 1)) :=
  materializedConservative_update_work_le_prefix
    H datum n

end MainTheoremMaterializedPackage

end TCS1
end LeanCfgProject
