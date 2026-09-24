import LeanCfgProject.TCS1.LinearReducedWitnessBridge
import LeanCfgProject.TCS1.ConcreteConservativeLearner

/-!
# TCS #1: linear characteristic-data facade

This module packages the linear-spine semantic bounds into the actual
characteristic sample used by the fixed-h reconstruction theorem.

Starting only from qualitative reducedness, structural reachability, and the
linear-spine SSBNF shape, we choose the minimum canonical productive yields
and contexts internally.  The resulting canonical witness finset:

* reconstructs the reduced typed target language exactly; and
* has the explicit polynomial encoded-size envelope proved for the linear
  subclass.

The final theorem also feeds this same finite sample into the concrete
conservative positive-data learner.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearCharacteristicDataFacade

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w} [Fintype N] [Fintype α]

/-- The minimum-choice canonical sample of one qualitatively reduced grammar. -/
noncomputable def linearCanonicalSample_of_reducedness
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active) :
    Finset (Word α) :=
  canonicalWitnessFinset
    H terminalRule binaryRule startRule epsilonStart Active
    (minimalReducedWitnessChoices_of_reducedness R)

/--
Reduced-level form of Theorem (polynomial characteristic data for linear
targets): exact reconstruction and the explicit polynomial sample-size bound
hold simultaneously for the actual minimum canonical sample.
-/
theorem linearReduced_characteristic_package
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (hsub :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active)) :
    let K :=
      linearCanonicalSample_of_reducedness
        H terminalRule binaryRule startRule epsilonStart Active R
    BatchLanguage H K =
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
    ∧
    (∑ word ∈ K, (word.length + 1))
      ≤
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) := by
  classical
  dsimp
  let C :=
    minimalReducedWitnessChoices_of_reducedness R
  have hminimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C := by
    simpa [C] using
      (minimalReducedWitnessChoices_minimality R)
  constructor
  · simpa [linearCanonicalSample_of_reducedness, C] using
      (exact_reconstruction_of_canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart
        Active C hsub)
  · simpa [linearCanonicalSample_of_reducedness, C] using
      (canonicalWitnessFinset_linear_norm_le_of_shape
        H terminalRule binaryRule startRule epsilonStart
        Active Wrapper shape reach C hminimal)

/--
The same reduced-level theorem with the polynomial sample bound projected as a
standalone fact.
-/
theorem linearReduced_characteristic_sample_norm_le
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (hsub :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active)) :
    (∑ word ∈
      linearCanonicalSample_of_reducedness
        H terminalRule binaryRule startRule epsilonStart Active R,
      (word.length + 1))
      ≤
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) := by
  exact
    (linearReduced_characteristic_package
      H terminalRule binaryRule startRule epsilonStart
      Active Wrapper R shape reach hsub).2

/--
Concrete conservative Gold identification for the reduced linear-spine target.

The characteristic stage is obtained automatically from finite coverage, so
the only presentation assumptions are positivity and coverage.
-/
theorem linearReduced_concreteGold_identification
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (hsub :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈
          ReducedTypedLanguage
            H terminalRule binaryRule startRule epsilonStart Active)
    (hcoverage :
      ∀ word,
        word ∈
          ReducedTypedLanguage
            H terminalRule binaryRule startRule epsilonStart Active →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    ∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀)
          =
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum (n₀ + j) =
            concreteConservativeHypothesis H datum n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        concreteConservativeHypothesis H datum (n + 1) ≠
          concreteConservativeHypothesis H datum n ∧
        BatchLanguage H
          (concreteConservativeHypothesis H datum (n + 1))
          =
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1)) := by
  have hchar :=
    (linearReduced_characteristic_package
      H terminalRule binaryRule startRule epsilonStart
      Active Wrapper R shape reach hsub).1
  exact
    concreteConservative_gold_identification_explicit
      H
      (ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active)
      (linearCanonicalSample_of_reducedness
        H terminalRule binaryRule startRule epsilonStart Active R)
      hchar hsub
      datum hpositive hcoverage

end LinearCharacteristicDataFacade

end TCS1
end LeanCfgProject
