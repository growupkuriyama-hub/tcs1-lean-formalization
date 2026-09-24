import LeanCfgProject.TCS1.MainTheoremSemanticPackage
import LeanCfgProject.TCS1.ExecutableConservativeLearner

/-!
# TCS #1 v79: executable paper-facing package for the main theorem

The semantic main-theorem package proves characteristic-data existence and
Gold convergence for the reconstruction language.  The executable learner
development proves that the verified factor-slot CYK parser implements exactly
that semantics and that the executable conservative hypothesis sequence is
pointwise identical to the semantic run.

This file composes those layers at the manuscript-facing level.  For a fixed
finite-monoid typing with decidable finite type, a finite indexed CFG target,
and any positive complete text, it packages:

* exact Boolean membership for every reconstructed finite sample;
* an explicit prefix-polynomial work bound for every executable update;
* existence of a finite positive characteristic sample; and
* Gold identification by the executable conservative learner.

The work bound is the explicit scan/comparison accounting developed in the
complexity modules; it is not a machine-code cost semantics for Lean itself.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section MainTheoremExecutablePackage

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M] [DecidableEq M]

/-- Gold-stabilization conclusion stated for the executable hypothesis run. -/
def ExecutableGoldConclusion
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (datum : Nat → Word α) : Prop :=
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
          executableConservativeHypothesis H datum (n + 1))

/--
Paper-facing executable core of the fixed-h learning theorem.

The second conjunct is a literal bound for every update of the actual
executable hypothesis sequence.  Its right-hand side is the explicit
polynomial conservativeExecutableUpdateWorkEnvelope in the encoded positive
data prefix.
-/
theorem indexedFixedH_learning_executable_core
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
      ∀ w : Word α,
        reconstructionFactorSlotCYKMember H K w = true
          ↔
        w ∈ BatchLanguage H K)
    ∧
    (∀ n : Nat,
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
        (positiveDataPrefixNorm datum (n + 1)))
    ∧
    (∃ C : Finset (Word α),
      (↑C : Set (Word α)) ⊆
        LeastClosedLanguage G.toMixedRules A
      ∧
      BatchLanguage H C =
        LeastClosedLanguage G.toMixedRules A)
    ∧
    ExecutableGoldConclusion
      H
      (LeastClosedLanguage G.toMixedRules A)
      datum := by
  obtain ⟨C, hCpos, hchar⟩ :=
    indexedFixedH_exists_characteristic_sample
      H G A hsub
  refine ⟨?_, ?_, ⟨C, hCpos, hchar⟩, ?_⟩
  · intro K w
    exact
      reconstructionFactorSlotCYKMember_eq_true_iff
        H K w
  · intro n
    exact
      executableConservative_update_work_le_prefix
        H datum n
  · unfold ExecutableGoldConclusion
    exact
      executableConservative_gold_identification_explicit
        H
        (LeastClosedLanguage G.toMixedRules A)
        C
        hchar
        hsub
        datum
        hpositive
        hcoverage

/--
Direct paper-facing Corollary (poly-update): every stage of the executable
conservative learner is bounded by one explicit polynomial of the encoded data
prefix.
-/
theorem corollary_poly_update_executable
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
      (positiveDataPrefixNorm datum (n + 1)) :=
  executableConservative_update_work_le_prefix
    H datum n

end MainTheoremExecutablePackage

end TCS1
end LeanCfgProject
