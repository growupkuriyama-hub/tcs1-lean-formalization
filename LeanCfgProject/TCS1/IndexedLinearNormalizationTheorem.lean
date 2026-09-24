import LeanCfgProject.TCS1.IndexedLinearNormalizationSize

/-!
# TCS #1: paper-facing arbitrary linear normalization theorem

This module packages the completed Section 8 normalization chain in the form
used by Proposition linear-normal.

For every finite indexed linear CFG and chosen start symbol, the construction
produces a separated-start terminal/binary grammar which

* generates exactly the original source language;
* has the required linear-spine one-wrapper-child shape; and
* has concrete state-plus-rule size bounded by an explicit polynomial in the
  original indexed encoding size.

Thus neither semantic preprocessing hypotheses nor intermediate grammar counts
remain in the theorem statement.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedLinearNormalizationTheorem

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]

/--
Paper-facing arbitrary finite linear-CFG normalization package.

The target grammar is the concrete construction attached to the finite
prepared grammar produced from G; epsilon is retained separately at the start
exactly when the original start symbol is nullable.
-/
theorem indexedLinear_normalization_source_package
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    UntypedStartLanguage
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
        (G.linearKeepEmpty hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S
    ∧
    UntypedLinearSpineShape
      (LinearConstructedTerminalRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedBinaryRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedWrapper
        (G.linearPreparedGrammar hlinear))
    ∧
    Fintype.card
        (LinearConstructedState
          (G.linearPreparedGrammar hlinear))
      +
      (Fintype.card
          (LinearConstructedTerminalRuleIndex
            (G.linearPreparedGrammar hlinear))
       +
       Fintype.card
          (LinearConstructedBinaryRuleIndex
            (G.linearPreparedGrammar hlinear)))
      ≤
    2 *
      linearPreparedEncodingEnvelope
        G.linearNormalizationSourceScale := by
  refine
    ⟨indexedLinear_constructedStartLanguage_eq_source
        G hlinear S,
      linearConstructed_untypedLinearSpineShape
        (G.linearPreparedGrammar hlinear),
      ?_⟩
  exact
    indexedLinear_constructedSize_le_sourceEnvelope
      G hlinear

/-- Language-preservation projection of the paper-facing package. -/
theorem indexedLinear_normalization_language_eq
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    UntypedStartLanguage
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
        (G.linearKeepEmpty hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S :=
  (indexedLinear_normalization_source_package
    G hlinear S).1

/-- Linear-spine shape projection of the paper-facing package. -/
theorem indexedLinear_normalization_shape
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    UntypedLinearSpineShape
      (LinearConstructedTerminalRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedBinaryRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedWrapper
        (G.linearPreparedGrammar hlinear)) :=
  linearConstructed_untypedLinearSpineShape
    (G.linearPreparedGrammar hlinear)

/-- Source-polynomial size projection of the paper-facing package. -/
theorem indexedLinear_normalization_size_le
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    Fintype.card
        (LinearConstructedState
          (G.linearPreparedGrammar hlinear))
      +
      (Fintype.card
          (LinearConstructedTerminalRuleIndex
            (G.linearPreparedGrammar hlinear))
       +
       Fintype.card
          (LinearConstructedBinaryRuleIndex
            (G.linearPreparedGrammar hlinear)))
      ≤
    2 *
      linearPreparedEncodingEnvelope
        G.linearNormalizationSourceScale :=
  indexedLinear_constructedSize_le_sourceEnvelope
    G hlinear

end IndexedLinearNormalizationTheorem

end TCS1
end LeanCfgProject
