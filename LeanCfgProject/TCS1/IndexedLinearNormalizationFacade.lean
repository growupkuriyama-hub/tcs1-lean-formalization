import LeanCfgProject.TCS1.LinearRawUnitFreePreparedBridge
import LeanCfgProject.TCS1.LinearRawPreprocessingFacade
import LeanCfgProject.TCS1.LinearConstructedStartLanguage
import LeanCfgProject.TCS1.PreparedLinearNormalizationFacade

/-!
# TCS #1: arbitrary indexed linear CFG to concrete linear-spine normalization

This facade closes the semantic preprocessing gap in Proposition linear-normal.

Starting with an ordinary finite indexed mixed CFG whose right-hand sides are
linear (at most one nonterminal), it composes:

* the raw epsilon/unit representation;
* explicit epsilon elimination, retaining start epsilon separately;
* unit-closure copying into a finite prepared grammar; and
* the verified concrete linear-spine factorization.

No already-preprocessed assumption remains. The resulting separated-start
terminal/binary grammar has exactly the original source language and satisfies
the one-wrapper-child linear-spine condition. Its concrete state/rule size is
bounded by twice the encoding scale of the finite prepared intermediate
grammar; a following counting module transports that bound to the original
source encoding.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedLinearNormalizationFacade

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]

/-- Finite prepared grammar obtained from an arbitrary indexed linear CFG. -/
noncomputable def IndexedMixedCFG.linearPreparedGrammar
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    PreparedLinearIndexedCFG
      N α
      (RawLinearPreparedRuleIndex
        (G.toRawLinear hlinear)) :=
  rawLinearPreparedGrammar
    (G.toRawLinear hlinear)

/-- Epsilon is retained at the separated start exactly when the source start is nullable. -/
def IndexedMixedCFG.linearKeepEmpty
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) : Prop :=
  RawLinearNullable
    (G.toRawLinear hlinear) S

/--
Every prepared derivation produced by the finite raw preprocessing stage is
nonempty.
-/
theorem indexedLinear_preparedDerives_nonempty
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    {A : N}
    {word : List α}
    (d :
      PreparedLinearDerives
        (G.linearPreparedGrammar hlinear)
        A word) :
    word ≠ [] := by
  have dunit :
      RawLinearUnitFreeDerives
        (G.toRawLinear hlinear) A word :=
    preparedDerives_to_rawLinearUnitFree
      (G.toRawLinear hlinear) d
  have deps :
      RawLinearEpsilonFreeDerives
        (G.toRawLinear hlinear) A word :=
    (rawLinear_unit_elimination_preserves_language
      (G.toRawLinear hlinear) A word).2 dunit
  exact
    rawLinearEpsilonFreeDerives_nonempty
      (G.toRawLinear hlinear) deps

/--
For every nonempty word, the finite prepared grammar already has exactly the
original source language.
-/
theorem indexedLinear_preparedDerives_iff_source_nonempty
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (A : N)
    (word : List α)
    (hne : word ≠ []) :
    PreparedLinearDerives
        (G.linearPreparedGrammar hlinear)
        A word
      ↔
    word ∈ LeastClosedLanguage
      G.toMixedRules A := by
  calc
    PreparedLinearDerives
        (G.linearPreparedGrammar hlinear)
        A word
      ↔
    RawLinearUnitFreeDerives
        (G.toRawLinear hlinear) A word :=
      (rawLinearUnitFreeDerives_iff_prepared
        (G.toRawLinear hlinear) A word).symm
    _ ↔
    word ∈ LeastClosedLanguage
      G.toMixedRules A :=
      indexedLinear_unitFree_iff_source_nonempty
        G hlinear A word hne

/--
The separated-start language of the fully concrete specialized normalization
is exactly the language of the original indexed linear CFG.
-/
theorem indexedLinear_constructedStartLanguage_eq_source
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
    LeastClosedLanguage G.toMixedRules S := by
  rw [linearConstructed_startLanguage_eq_prepared]
  apply Set.ext
  intro word
  change
    ((G.linearKeepEmpty hlinear S ∧ word = [])
      ∨
      PreparedLinearDerives
        (G.linearPreparedGrammar hlinear) S word)
      ↔
    word ∈ LeastClosedLanguage G.toMixedRules S
  constructor
  · intro hword
    rcases hword with heps | hprepared
    · rcases heps with ⟨hnull, rfl⟩
      exact
        (indexedLinear_rawNullable_iff_source_epsilon
          G hlinear S).1 hnull
    · have hne :
          word ≠ [] :=
        indexedLinear_preparedDerives_nonempty
          G hlinear hprepared
      exact
        (indexedLinear_preparedDerives_iff_source_nonempty
          G hlinear S word hne).1 hprepared
  · intro hsource
    by_cases hnil : word = []
    · left
      refine ⟨?_, hnil⟩
      subst word
      exact
        (indexedLinear_rawNullable_iff_source_epsilon
          G hlinear S).2 hsource
    · right
      exact
        (indexedLinear_preparedDerives_iff_source_nonempty
          G hlinear S word hnil).2 hsource

/--
Paper-facing semantic/structural normalization package for an arbitrary finite
indexed linear CFG.

The size bound is already attached to the actual constructed grammar; only the
last transport from the prepared encoding scale to the original source scale
is left to the counting facade.
-/
theorem indexedLinear_normalization_package
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
      (G.linearPreparedGrammar hlinear).encodingScale := by
  exact
    ⟨indexedLinear_constructedStartLanguage_eq_source
        G hlinear S,
      linearConstructed_untypedLinearSpineShape
        (G.linearPreparedGrammar hlinear),
      linearConstructed_combined_size_le_twice_scale
        (G.linearPreparedGrammar hlinear)⟩

end IndexedLinearNormalizationFacade

end TCS1
end LeanCfgProject
