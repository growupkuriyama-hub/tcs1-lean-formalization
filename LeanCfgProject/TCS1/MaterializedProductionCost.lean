import LeanCfgProject.TCS1.ReconstructionProductionTables
import LeanCfgProject.TCS1.MaterializedConservativeLearner

/-!
# TCS #1 v79: materialized production-table cost accounting

The materialized reconstruction layer stores the unit-free terminal, binary,
and start relations as explicit finite tables.  This module adds the missing
representation-level bookkeeping promised by that layer.

The accounting is intentionally combinatorial.  For m factor-slot states and
a terminal alphabet of size a, exhaustive table materialization scans

  m * a        terminal entries,
  m * (m * m)  binary entries, and
  m            start entries.

The already verified all-source R2/R3 closure budget is kept separate and is
then composed with this table scan, CYK membership, and a possible rebuild.
This does not claim a machine-code cost model for Lean's evaluator.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MaterializedProductionCost

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [Fintype α] [DecidableEq α]
variable [DecidableEq M]

/-- Candidate-scan count for materializing terminal, binary, and start tables. -/
def reconstructionProductionTableScanEnvelope
    (stateCount alphabetCount : Nat) : Nat :=
  stateCount * alphabetCount +
    stateCount * (stateCount * stateCount) +
    stateCount

/-- The scan count is a manifest cubic polynomial in the state count. -/
theorem reconstructionProductionTableScanEnvelope_polynomial_form
    (m a : Nat) :
    reconstructionProductionTableScanEnvelope m a =
      m * a + m ^ 3 + m := by
  unfold reconstructionProductionTableScanEnvelope
  ring

/-- Materialization scan is monotone in the number of finite states. -/
theorem reconstructionProductionTableScanEnvelope_mono_left
    {m m' a : Nat}
    (h : m ≤ m') :
    reconstructionProductionTableScanEnvelope m a ≤
      reconstructionProductionTableScanEnvelope m' a := by
  unfold reconstructionProductionTableScanEnvelope
  gcongr

/-- The explicit start table is no larger than the factor-slot state space. -/
theorem reconstructionFactorSlotStartTable_card_le
    (K : Finset (Word α)) :
    (reconstructionFactorSlotStartTable K).card ≤
      Fintype.card (ReconstructionFactorSlot K) := by
  have h :=
    Finset.card_le_univ
      (reconstructionFactorSlotStartTable K)
  simpa using h

/-- Number of productions physically stored by the parser-facing tables. -/
def reconstructionMaterializedProductionCard
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Nat :=
  (reconstructionFactorSlotUnitFreeTerminalTable H K).card +
    (reconstructionFactorSlotUnitFreeBinaryTable H K).card +
    (reconstructionFactorSlotStartTable K).card

/--
The physically stored parser-facing table size is bounded by the exhaustive
candidate scan used to construct it.
-/
theorem reconstructionMaterializedProductionCard_le_scanEnvelope
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    reconstructionMaterializedProductionCard H K ≤
      reconstructionProductionTableScanEnvelope
        (Fintype.card (ReconstructionFactorSlot K))
        (Fintype.card α) := by
  have ht :=
    reconstructionFactorSlotUnitFreeTerminalTable_card_le
      H K
  have hb :=
    reconstructionFactorSlotUnitFreeBinaryTable_card_le
      H K
  have hs :=
    reconstructionFactorSlotStartTable_card_le
      (α := α) K
  unfold reconstructionMaterializedProductionCard
  unfold reconstructionProductionTableScanEnvelope
  exact Nat.add_le_add (Nat.add_le_add ht hb) hs

/--
The physically stored production table of the current concrete hypothesis is
itself bounded by the same prefix-only materialization scan polynomial.
-/
theorem concreteConservative_materializedProductionCard_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionMaterializedProductionCard
        H (concreteConservativeHypothesis H datum n)
      ≤
    reconstructionProductionTableScanEnvelope
      (5 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 5)
      (Fintype.card α) := by
  have hstored :=
    reconstructionMaterializedProductionCard_le_scanEnvelope
      H (concreteConservativeHypothesis H datum n)
  have hcard :=
    reconstructionFactorSlot_current_card_le_prefix_degreeFive
      H datum n
  have hscan :=
    reconstructionProductionTableScanEnvelope_mono_left
      (a := Fintype.card α) hcard
  exact le_trans hstored hscan

/--
The same production-storage bound for the actual materialized hypothesis
sequence used by the table-backed learner.
-/
theorem materializedConservative_productionCard_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionMaterializedProductionCard
        H (materializedConservativeHypothesis H datum n)
      ≤
    reconstructionProductionTableScanEnvelope
      (5 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 5)
      (Fintype.card α) := by
  rw [materializedConservativeHypothesis_eq_concrete]
  exact
    concreteConservative_materializedProductionCard_le_prefix
      H datum n

/--
Prefix-only budget for a materialized update: production-table scan plus the
previous executable budget (unit closure, CYK, and a possible rebuild).
-/
def conservativeMaterializedUpdateWorkEnvelope
    (alphabetCount prefixNorm : Nat) : Nat :=
  reconstructionProductionTableScanEnvelope
      (5 * (prefixNorm + 1) ^ 5)
      alphabetCount
    +
  conservativeExecutableUpdateWorkEnvelope prefixNorm

/-- The materialized-update envelope is explicitly polynomial. -/
theorem conservativeMaterializedUpdateWorkEnvelope_polynomial_form
    (a p : Nat) :
    conservativeMaterializedUpdateWorkEnvelope a p =
      (5 * (p + 1) ^ 5) * a +
        (5 * (p + 1) ^ 5) ^ 3 +
        (5 * (p + 1) ^ 5) +
        ((5 * (p + 1) ^ 5) ^ 4 +
          conservativeCYKPrefixEnvelope p +
          5 * (p + 1) ^ 5) := by
  unfold conservativeMaterializedUpdateWorkEnvelope
  rw [reconstructionProductionTableScanEnvelope_polynomial_form]
  rw [conservativeExecutableUpdateWorkEnvelope_polynomial_form]

/--
End-to-end combinatorial work bound for the concrete hypothesis at stage n:
table materialization + unit closure + CYK membership + possible rebuild.
-/
theorem concreteConservative_materialized_update_work_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionProductionTableScanEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
        (Fintype.card α)
      +
    (reconstructionUnitClosureTableScanEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
      +
     (cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      +
      reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteAccumulatedSample datum (n + 1)))))
      ≤
    conservativeMaterializedUpdateWorkEnvelope
      (Fintype.card α)
      (positiveDataPrefixNorm datum (n + 1)) := by
  have hcard :=
    reconstructionFactorSlot_current_card_le_prefix_degreeFive
      H datum n
  have htables :=
    reconstructionProductionTableScanEnvelope_mono_left
      (a := Fintype.card α) hcard
  have hrest :=
    concreteConservative_executable_update_work_le_prefix
      H datum n
  unfold conservativeMaterializedUpdateWorkEnvelope
  exact Nat.add_le_add htables hrest

/--
The same bound stated directly on the materialized-table learner's actual
hypothesis sequence.
-/
theorem materializedConservative_update_work_le_prefix
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
      (positiveDataPrefixNorm datum (n + 1)) := by
  rw [materializedConservativeHypothesis_eq_concrete]
  exact
    concreteConservative_materialized_update_work_le_prefix
      H datum n

end MaterializedProductionCost

end TCS1
end LeanCfgProject
