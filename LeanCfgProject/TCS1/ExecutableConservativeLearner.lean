import LeanCfgProject.TCS1.ReconstructionFactorSlotCYK
import LeanCfgProject.TCS1.ConcreteConservativeLearner

/-!
# TCS #1 v79: fully executable conservative positive-data learner

The semantic Gold learner in `ConcreteConservativeLearner` used a classical
membership test for `BatchLanguage`.  The factor-slot CYK development now
provides an ordinary Boolean decision procedure for exactly that language.

This module replaces the classical branch by
`reconstructionFactorSlotCYKMember`, defines a genuinely computable
hypothesis sequence, and proves it pointwise identical to the previously
verified semantic conservative run.  Consequently all existing Gold
convergence theorems transfer without changing their language-theoretic proof.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ExecutableConservativeLearner

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]

/-- One executable keep/rebuild step using the verified factor-slot CYK parser. -/
def executableConservativeUpdate
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α) :
    Finset (Word α) :=
  if reconstructionFactorSlotCYKMember H current word then
    current
  else
    accumulated

/-- Generated data take the keep branch of the executable update. -/
theorem executableConservativeUpdate_keep
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α)
    (hgen : word ∈ BatchLanguage H current) :
    executableConservativeUpdate
        H current accumulated word
      =
    current := by
  have htrue :
      reconstructionFactorSlotCYKMember
        H current word = true :=
    (reconstructionFactorSlotCYKMember_eq_true_iff
      H current word).2 hgen
  simp [executableConservativeUpdate, htrue]

/-- Missing data take the rebuild branch of the executable update. -/
theorem executableConservativeUpdate_rebuild
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α)
    (hmiss : word ∉ BatchLanguage H current) :
    executableConservativeUpdate
        H current accumulated word
      =
    accumulated := by
  have hnot :
      reconstructionFactorSlotCYKMember
        H current word ≠ true := by
    intro htrue
    exact hmiss
      ((reconstructionFactorSlotCYKMember_eq_true_iff
        H current word).1 htrue)
  have hfalse :
      reconstructionFactorSlotCYKMember
        H current word = false := by
    cases h :
      reconstructionFactorSlotCYKMember
        H current word <;> simp_all
  simp [executableConservativeUpdate, hfalse]

/--
The executable update is extensionally the same keep/rebuild operator as the
previous classical semantic definition.
-/
theorem executableConservativeUpdate_eq_concrete
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α) :
    executableConservativeUpdate
        H current accumulated word
      =
    concreteConservativeUpdate
        H current accumulated word := by
  by_cases hgen : word ∈ BatchLanguage H current
  · rw [executableConservativeUpdate_keep
        H current accumulated word hgen]
    symm
    exact
      concreteConservativeUpdate_keep
        H current accumulated word hgen
  · rw [executableConservativeUpdate_rebuild
        H current accumulated word hgen]
    symm
    exact
      concreteConservativeUpdate_rebuild
        H current accumulated word hgen

/-- Fully executable conservative hypothesis sequence. -/
def executableConservativeHypothesis
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    Nat → Finset (Word α)
  | 0 => ∅
  | n + 1 =>
      executableConservativeUpdate
        H
        (executableConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))

@[simp] theorem executableConservativeHypothesis_zero
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    executableConservativeHypothesis H datum 0 = ∅ :=
  rfl

/--
The executable run is pointwise identical to the semantic run already used in
the Gold proof.
-/
@[simp] theorem executableConservativeHypothesis_eq_concrete
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    ∀ n,
      executableConservativeHypothesis H datum n =
        concreteConservativeHypothesis H datum n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        executableConservativeUpdate
            H
            (executableConservativeHypothesis H datum n)
            (concreteAccumulatedSample datum (n + 1))
            (datum (n + 1))
          =
        concreteConservativeUpdate
            H
            (concreteConservativeHypothesis H datum n)
            (concreteAccumulatedSample datum (n + 1))
            (datum (n + 1))
      rw [ih]
      exact
        executableConservativeUpdate_eq_concrete
          H
          (concreteConservativeHypothesis H datum n)
          (concreteAccumulatedSample datum (n + 1))
          (datum (n + 1))

/-- Generated data cause a literal keep step in the executable sequence. -/
theorem executableConservativeHypothesis_keep
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat)
    (hgen :
      datum (n + 1) ∈
        BatchLanguage H
          (executableConservativeHypothesis H datum n)) :
    executableConservativeHypothesis H datum (n + 1) =
      executableConservativeHypothesis H datum n := by
  change
    executableConservativeUpdate
        H
        (executableConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))
      =
    executableConservativeHypothesis H datum n
  exact
    executableConservativeUpdate_keep
      H
      (executableConservativeHypothesis H datum n)
      (concreteAccumulatedSample datum (n + 1))
      (datum (n + 1))
      hgen

/-- Missing data cause a literal rebuild in the executable sequence. -/
theorem executableConservativeHypothesis_rebuild
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat)
    (hmiss :
      datum (n + 1) ∉
        BatchLanguage H
          (executableConservativeHypothesis H datum n)) :
    executableConservativeHypothesis H datum (n + 1) =
      concreteAccumulatedSample datum (n + 1) := by
  change
    executableConservativeUpdate
        H
        (executableConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))
      =
    concreteAccumulatedSample datum (n + 1)
  exact
    executableConservativeUpdate_rebuild
      H
      (executableConservativeHypothesis H datum n)
      (concreteAccumulatedSample datum (n + 1))
      (datum (n + 1))
      hmiss

/--
End-to-end polynomial work bound stated on the actual executable hypothesis
sequence.  It includes finite R2/R3 unit closure, CYK membership, and a
possible rebuild.
-/
theorem executableConservative_update_work_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionUnitClosureTableScanEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (executableConservativeHypothesis H datum n)))
      +
    (cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (executableConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      +
     reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteAccumulatedSample datum (n + 1))))
      ≤
    conservativeExecutableUpdateWorkEnvelope
      (positiveDataPrefixNorm datum (n + 1)) := by
  rw [executableConservativeHypothesis_eq_concrete]
  exact
    concreteConservative_executable_update_work_le_prefix
      H datum n

/--
Gold identification stated directly for the executable hypothesis sequence.
The convergence proof is inherited from the already verified semantic run via
pointwise equality.
-/
theorem executableConservative_gold_identification_explicit
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
          (executableConservativeHypothesis H datum n₀) = L
        ∧
        ∀ j,
          executableConservativeHypothesis H datum (n₀ + j) =
            executableConservativeHypothesis H datum n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        executableConservativeHypothesis H datum (n + 1) ≠
          executableConservativeHypothesis H datum n ∧
        BatchLanguage H
          (executableConservativeHypothesis H datum (n + 1)) = L
        ∧
        ∀ j,
          executableConservativeHypothesis H datum ((n + 1) + j) =
            executableConservativeHypothesis H datum (n + 1)) := by
  have h :=
    concreteConservative_gold_identification_explicit
      H L C hchar hsub datum hpositive hcoverage
  simpa only [← executableConservativeHypothesis_eq_concrete
    (H := H) (datum := datum)] using h

end ExecutableConservativeLearner

end TCS1
end LeanCfgProject
