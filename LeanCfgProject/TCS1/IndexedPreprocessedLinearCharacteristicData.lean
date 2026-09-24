import LeanCfgProject.TCS1.LinearConstructedStartLanguage

/-!
# TCS #1: characteristic data for preprocessed indexed linear CFGs

This module composes the specialized linear normalization with the verified
linear characteristic-data theorem.

Starting from an ordinary finite indexed mixed CFG whose productions are
linear, nonempty, and non-unit after standard preprocessing, we now have:

* a concrete finite linear-spine terminal/binary grammar;
* exact start-language preservation, with epsilon kept separately;
* an internally constructed minimum canonical characteristic sample; and
* concrete conservative Gold identification from positive data.

The only semantic class assumption left is fixed-h substitutability of the
original source target language.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section IndexedPreprocessedLinearCharacteristicData

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type z} [Monoid M] [Fintype M]

variable [Fintype N] [Fintype α] [Fintype P]

/-- Canonical sample obtained after the concrete specialized normalization. -/
noncomputable def indexedPreprocessedLinearCanonicalSample
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (S : N)
    (keepEmpty : Prop) :
    Finset (Word α) :=
  concreteLinearCanonicalSample
    H
    (LinearConstructedTerminalRule
      (G.toPreparedLinear hprep))
    (LinearConstructedBinaryRule
      (G.toPreparedLinear hprep))
    (linearConstructedStartRule
      (G.toPreparedLinear hprep) S)
    keepEmpty

/--
The start-language equality transports fixed-h substitutability from the
original indexed target to the concrete normalized grammar.
-/
theorem indexedPreprocessedLinear_fixedHSubstitutable_normalized
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (S : N)
    (keepEmpty : Prop)
    (hsub :
      FixedHSubstitutable H
        (G.linearTargetLanguage S keepEmpty)) :
    FixedHSubstitutable H
      (UntypedStartLanguage
        (LinearConstructedTerminalRule
          (G.toPreparedLinear hprep))
        (LinearConstructedBinaryRule
          (G.toPreparedLinear hprep))
        (linearConstructedStartRule
          (G.toPreparedLinear hprep) S)
        keepEmpty) := by
  rw [indexedPreprocessedLinear_startLanguage_eq_source
    G hprep S keepEmpty]
  exact hsub

/--
Characteristic sample package for an ordinary preprocessed indexed linear CFG.

The quantitative right-hand side is written in terms of the actual normalized
grammar counts.  A separate counting bridge can subsequently eliminate those
counts in favor of the source encoding scale.
-/
theorem indexedPreprocessedLinear_characteristic_package
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (S : N)
    (keepEmpty : Prop)
    (hsub :
      FixedHSubstitutable H
        (G.linearTargetLanguage S keepEmpty)) :
    BatchLanguage H
        (indexedPreprocessedLinearCanonicalSample
          H G hprep S keepEmpty)
      =
    G.linearTargetLanguage S keepEmpty
    ∧
    (∑ word ∈
      indexedPreprocessedLinearCanonicalSample
        H G hprep S keepEmpty,
      (word.length + 1))
      ≤
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card
        (LinearConstructedState
          (G.toPreparedLinear hprep)))
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (LinearConstructedTerminalRule
            (G.toPreparedLinear hprep)))
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (LinearConstructedBinaryRule
            (G.toPreparedLinear hprep)))
        (Fintype.ofFinite _)) := by
  have hshape :
      UntypedLinearSpineShape
        (LinearConstructedTerminalRule
          (G.toPreparedLinear hprep))
        (LinearConstructedBinaryRule
          (G.toPreparedLinear hprep))
        (LinearConstructedWrapper
          (G.toPreparedLinear hprep)) :=
    linearConstructed_untypedLinearSpineShape
      (G.toPreparedLinear hprep)
  have hsubNorm :=
    indexedPreprocessedLinear_fixedHSubstitutable_normalized
      H G hprep S keepEmpty hsub
  have hpack :=
    concreteLinear_characteristic_package_of_untyped_shape
      H
      (LinearConstructedTerminalRule
        (G.toPreparedLinear hprep))
      (LinearConstructedBinaryRule
        (G.toPreparedLinear hprep))
      (linearConstructedStartRule
        (G.toPreparedLinear hprep) S)
      keepEmpty
      (LinearConstructedWrapper
        (G.toPreparedLinear hprep))
      hshape hsubNorm
  constructor
  · calc
      BatchLanguage H
          (indexedPreprocessedLinearCanonicalSample
            H G hprep S keepEmpty)
        =
      UntypedStartLanguage
          (LinearConstructedTerminalRule
            (G.toPreparedLinear hprep))
          (LinearConstructedBinaryRule
            (G.toPreparedLinear hprep))
          (linearConstructedStartRule
            (G.toPreparedLinear hprep) S)
          keepEmpty := by
            simpa [indexedPreprocessedLinearCanonicalSample]
              using hpack.1
      _ =
      G.linearTargetLanguage S keepEmpty :=
        indexedPreprocessedLinear_startLanguage_eq_source
          G hprep S keepEmpty
  · simpa [indexedPreprocessedLinearCanonicalSample]
      using hpack.2

/--
Concrete conservative identification of the original preprocessed indexed
linear target from positive data.
-/
theorem indexedPreprocessedLinear_conservativeGold_identification
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (S : N)
    (keepEmpty : Prop)
    (hsub :
      FixedHSubstitutable H
        (G.linearTargetLanguage S keepEmpty))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈ G.linearTargetLanguage S keepEmpty)
    (hcoverage :
      ∀ word,
        word ∈ G.linearTargetLanguage S keepEmpty →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    ∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀)
          =
        G.linearTargetLanguage S keepEmpty
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
        G.linearTargetLanguage S keepEmpty
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1)) := by
  have hchar :=
    (indexedPreprocessedLinear_characteristic_package
      H G hprep S keepEmpty hsub).1
  exact
    concreteConservative_gold_identification_explicit
      H
      (G.linearTargetLanguage S keepEmpty)
      (indexedPreprocessedLinearCanonicalSample
        H G hprep S keepEmpty)
      hchar hsub
      datum hpositive hcoverage

end IndexedPreprocessedLinearCharacteristicData

end TCS1
end LeanCfgProject
