import LeanCfgProject.TCS1.ReconstructionProductionTables
import LeanCfgProject.TCS1.ExecutableConservativeLearner

/-!
# TCS #1 v79: conservative learner over materialized production tables

The reconstruction production-table layer lowers the reconstructed hypothesis
to explicit finite terminal/binary/start tables and proves that the resulting
CYK Boolean test decides exactly BatchLanguage.

This module uses that table-backed parser in the learner itself.  The resulting
hypothesis sequence is proved pointwise identical to the already verified
executable factor-slot learner, and hence to the semantic conservative learner.
Gold identification therefore transfers unchanged.

No new runtime claim is made here: the existing update-cost theorem accounts
for factor-slot unit closure, CYK work, and reconstruction.  A separate layer
may additionally account for physically building the explicit production
tables.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MaterializedConservativeLearner

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [Fintype α] [DecidableEq α]
variable [DecidableEq M]

/-- One keep/rebuild step whose membership branch reads explicit finite tables. -/
def materializedConservativeUpdate
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α) :
    Finset (Word α) :=
  if reconstructionMaterializedCYKMember H current word then
    current
  else
    accumulated

/-- Generated data take the keep branch of the table-backed update. -/
theorem materializedConservativeUpdate_keep
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α)
    (hgen : word ∈ BatchLanguage H current) :
    materializedConservativeUpdate
        H current accumulated word
      =
    current := by
  have htrue :
      reconstructionMaterializedCYKMember
        H current word = true :=
    (reconstructionMaterializedCYKMember_eq_true_iff
      H current word).2 hgen
  simp [materializedConservativeUpdate, htrue]

/-- Missing data take the rebuild branch of the table-backed update. -/
theorem materializedConservativeUpdate_rebuild
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α)
    (hmiss : word ∉ BatchLanguage H current) :
    materializedConservativeUpdate
        H current accumulated word
      =
    accumulated := by
  have hnot :
      reconstructionMaterializedCYKMember
        H current word ≠ true := by
    intro htrue
    exact hmiss
      ((reconstructionMaterializedCYKMember_eq_true_iff
        H current word).1 htrue)
  have hfalse :
      reconstructionMaterializedCYKMember
        H current word = false := by
    cases h :
      reconstructionMaterializedCYKMember
        H current word <;> simp_all
  simp [materializedConservativeUpdate, hfalse]

/--
The table-backed update is extensionally identical to the verified executable
factor-slot update.
-/
theorem materializedConservativeUpdate_eq_executable
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α) :
    materializedConservativeUpdate
        H current accumulated word
      =
    executableConservativeUpdate
        H current accumulated word := by
  by_cases hgen : word ∈ BatchLanguage H current
  · rw [materializedConservativeUpdate_keep
        H current accumulated word hgen]
    symm
    exact
      executableConservativeUpdate_keep
        H current accumulated word hgen
  · rw [materializedConservativeUpdate_rebuild
        H current accumulated word hgen]
    symm
    exact
      executableConservativeUpdate_rebuild
        H current accumulated word hgen

/-- Conservative positive-data hypothesis sequence using materialized tables. -/
def materializedConservativeHypothesis
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    Nat → Finset (Word α)
  | 0 => ∅
  | n + 1 =>
      materializedConservativeUpdate
        H
        (materializedConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))

@[simp] theorem materializedConservativeHypothesis_zero
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    materializedConservativeHypothesis H datum 0 = ∅ :=
  rfl

/--
The materialized-table run is pointwise identical to the executable
factor-slot run.
-/
@[simp] theorem materializedConservativeHypothesis_eq_executable
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    ∀ n,
      materializedConservativeHypothesis H datum n =
        executableConservativeHypothesis H datum n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        materializedConservativeUpdate
            H
            (materializedConservativeHypothesis H datum n)
            (concreteAccumulatedSample datum (n + 1))
            (datum (n + 1))
          =
        executableConservativeUpdate
            H
            (executableConservativeHypothesis H datum n)
            (concreteAccumulatedSample datum (n + 1))
            (datum (n + 1))
      rw [ih]
      exact
        materializedConservativeUpdate_eq_executable
          H
          (executableConservativeHypothesis H datum n)
          (concreteAccumulatedSample datum (n + 1))
          (datum (n + 1))

/-- Hence the materialized run is also pointwise identical to the semantic run. -/
theorem materializedConservativeHypothesis_eq_concrete
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    materializedConservativeHypothesis H datum n =
      concreteConservativeHypothesis H datum n := by
  rw [materializedConservativeHypothesis_eq_executable]
  exact executableConservativeHypothesis_eq_concrete H datum n

/--
Gold identification stated directly for the materialized-table hypothesis
sequence.
-/
theorem materializedConservative_gold_identification_explicit
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (C : Finset (Word α))
    (hchar : BatchLanguage H C = L)
    (hsub : FixedHSubstitutable H L)
    (datum : Nat → Word α)
    (hpositive : ∀ n, datum n ∈ L)
    (hcoverage :
      ∀ w, w ∈ L →
        ∃ n, w ∈ concreteAccumulatedSample datum n) :
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
            materializedConservativeHypothesis H datum (n + 1)) := by
  have h :=
    executableConservative_gold_identification_explicit
      H L C hchar hsub datum hpositive hcoverage
  simpa only [← materializedConservativeHypothesis_eq_executable
    (H := H) (datum := datum)] using h

end MaterializedConservativeLearner

end TCS1
end LeanCfgProject
