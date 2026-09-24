import LeanCfgProject.TCS1.LinearCharacteristicDataFacade
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.LinearTypedShapeBridge

/-!
# TCS #1: concrete linear characteristic data

The previous linear facade was stated for an arbitrary qualitatively reduced
typed grammar plus an external structural-reachability certificate.  The
productive/reachable trim used in the manuscript already constructs both
objects.

This module instantiates the linear theorem with that concrete trim.  The only
linear-specific semantic assumption left is therefore the linear-spine shape
of the normalized untyped SSBNF grammar.  Trimming, reducedness, reachability,
minimum witness choices, and transport back to the untyped target language are
all discharged internally.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ConcreteLinearCharacteristicData

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w} [Fintype N] [Fintype α]

/-- Minimum canonical sample of the concrete productive/reachable typed trim. -/
noncomputable def concreteLinearCanonicalSample
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    Finset (Word α) :=
  canonicalWitnessFinset
    H terminalRule binaryRule startRule epsilonStart
    (ConcreteTypedActive
      H terminalRule binaryRule startRule)
    (concreteTypedActive_minimalChoices
      H terminalRule binaryRule startRule epsilonStart)

/--
Concrete reduced linear-spine package: exact reconstruction of the original
untyped start language and polynomial characteristic-data size.

No abstract reducedness, reachability, or witness-choice hypotheses remain.
-/
theorem concreteTypedActive_linear_characteristic_package
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Wrapper :
      ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule) → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))
        (ActiveTypedBinaryRule binaryRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))
        Wrapper)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    BatchLanguage H
        (concreteLinearCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart
    ∧
    (∑ word ∈
      concreteLinearCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
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
  classical
  let Active :=
    ConcreteTypedActive
      H terminalRule binaryRule startRule
  let R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active :=
    concreteTypedActive_qualitativeReducedness
      H terminalRule binaryRule startRule epsilonStart
  let C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active :=
    concreteTypedActive_minimalChoices
      H terminalRule binaryRule startRule epsilonStart
  have hreach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active := by
    simpa [Active, C] using
      (concreteTypedActive_structuralReachability
        H terminalRule binaryRule startRule epsilonStart C)
  have hsubReduced :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active) := by
    simpa [Active] using
      (concreteTypedActive_fixedHSubstitutable
        H terminalRule binaryRule startRule epsilonStart hsub)
  have hpack :=
    linearReduced_characteristic_package
      H terminalRule binaryRule startRule epsilonStart
      Active Wrapper R shape hreach hsubReduced
  constructor
  · calc
      BatchLanguage H
          (concreteLinearCanonicalSample
            H terminalRule binaryRule startRule epsilonStart)
        =
      ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active := by
            simpa [concreteLinearCanonicalSample, Active, R, C,
              linearCanonicalSample_of_reducedness,
              concreteTypedActive_minimalChoices] using hpack.1
      _ =
      UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart := by
            simpa [Active] using
              (concreteTypedActive_language_eq_untyped
                H terminalRule binaryRule startRule epsilonStart)
  · simpa [concreteLinearCanonicalSample, Active, R, C,
      linearCanonicalSample_of_reducedness,
      concreteTypedActive_minimalChoices] using hpack.2

/--
Concrete conservative identification of a linear-spine target from positive
data, with all typed-trimming infrastructure hidden from the theorem
interface.
-/
theorem concreteTypedActive_linear_conservativeGold_identification
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Wrapper :
      ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule) → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))
        (ActiveTypedBinaryRule binaryRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))
        Wrapper)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈
          UntypedStartLanguage
            terminalRule binaryRule startRule epsilonStart)
    (hcoverage :
      ∀ word,
        word ∈
          UntypedStartLanguage
            terminalRule binaryRule startRule epsilonStart →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    ∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀)
          =
        UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart
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
        UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1)) := by
  have hchar :=
    (concreteTypedActive_linear_characteristic_package
      H terminalRule binaryRule startRule epsilonStart
      Wrapper shape hsub).1
  exact
    concreteConservative_gold_identification_explicit
      H
      (UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart)
      (concreteLinearCanonicalSample
        H terminalRule binaryRule startRule epsilonStart)
      hchar hsub
      datum hpositive hcoverage


/--
Paper-facing linear characteristic-data theorem from an untyped linear-spine
SSBNF grammar.

This is the interface produced by Proposition (linear-spine SSBNF
normalization): the wrapper predicate and linear-spine shape live entirely on
the untyped normalized grammar.  Yield typing and productive/reachable
trimming preserve that shape automatically.
-/
theorem concreteLinear_characteristic_package_of_untyped_shape
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Wrapper : N → Prop)
    (shape :
      UntypedLinearSpineShape
        terminalRule binaryRule Wrapper)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    BatchLanguage H
        (concreteLinearCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart
    ∧
    (∑ word ∈
      concreteLinearCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
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
  have typedShape :=
    concreteTypedActive_linearSpineShape_of_untyped
      H terminalRule binaryRule startRule Wrapper shape
  exact
    concreteTypedActive_linear_characteristic_package
      H terminalRule binaryRule startRule epsilonStart
      (typedWrapper (M := M) Wrapper)
      typedShape hsub

/--
Concrete conservative identification from an untyped linear-spine SSBNF
presentation.  No typed shape, trimming, reducedness, reachability, or
canonical-choice certificate appears in the statement.
-/
theorem concreteLinear_conservativeGold_identification_of_untyped_shape
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Wrapper : N → Prop)
    (shape :
      UntypedLinearSpineShape
        terminalRule binaryRule Wrapper)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈
          UntypedStartLanguage
            terminalRule binaryRule startRule epsilonStart)
    (hcoverage :
      ∀ word,
        word ∈
          UntypedStartLanguage
            terminalRule binaryRule startRule epsilonStart →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    ∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀)
          =
        UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart
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
        UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1)) := by
  have typedShape :=
    concreteTypedActive_linearSpineShape_of_untyped
      H terminalRule binaryRule startRule Wrapper shape
  exact
    concreteTypedActive_linear_conservativeGold_identification
      H terminalRule binaryRule startRule epsilonStart
      (typedWrapper (M := M) Wrapper)
      typedShape hsub
      datum hpositive hcoverage

end ConcreteLinearCharacteristicData

end TCS1
end LeanCfgProject
