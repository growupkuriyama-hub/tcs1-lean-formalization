import LeanCfgProject.TCS1.LinearIndexedPreprocessedBridge
import LeanCfgProject.TCS1.ConcreteLinearCharacteristicData

/-!
# TCS #1: start-separated language of the specialized linear normalization

The verified specialized factorization preserves every old nonterminal
language.  The learner, however, uses the manuscript's separated-start
interface: the start symbol only points to one non-start child and epsilon is
recorded separately.

This module installs that start interface on the concrete linear-spine grammar
and identifies its language exactly with the source indexed linear CFG,
optionally adjoining epsilon.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearConstructedStartLanguage

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- The separated start points to one old source nonterminal. -/
def linearConstructedStartRule
    (G : PreparedLinearIndexedCFG N α P)
    (S : N) :
    LinearConstructedState G → Prop :=
  fun X => X = linearOldState G S

/-- Source language with epsilon kept separately at the start. -/
def preparedLinearStartLanguage
    (G : PreparedLinearIndexedCFG N α P)
    (S : N)
    (keepEmpty : Prop) :
    Set (List α) :=
  {word |
    (keepEmpty ∧ word = [])
      ∨
    PreparedLinearDerives G S word}

/--
The concrete constructed start language is exactly the prepared source
language, with the optional epsilon endpoint.
-/
theorem linearConstructed_startLanguage_eq_prepared
    (G : PreparedLinearIndexedCFG N α P)
    (S : N)
    (keepEmpty : Prop) :
    UntypedStartLanguage
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearConstructedStartRule G S)
        keepEmpty
      =
    preparedLinearStartLanguage G S keepEmpty := by
  apply Set.ext
  intro word
  constructor
  · intro hword
    cases hword with
    | @nonempty A word hstart d =>
        have hA :
            A = linearOldState G S :=
          hstart
        subst A
        right
        exact
          linearConstructed_old_derives_to_prepared
            G d
    | epsilon heps =>
        left
        exact ⟨heps, rfl⟩
  · intro hword
    rcases hword with heps | hsource
    · rcases heps with ⟨heps, rfl⟩
      exact UntypedStartDerives.epsilon heps
    · exact
        UntypedStartDerives.nonempty
          (show
            linearConstructedStartRule G S
              (linearOldState G S) from rfl)
          (preparedLinearDerives_to_linearConstructed
            G hsource)

/--
Least-closed form of the same start language.
-/
theorem preparedLinearStartLanguage_eq_least
    (G : PreparedLinearIndexedCFG N α P)
    (S : N)
    (keepEmpty : Prop) :
    preparedLinearStartLanguage G S keepEmpty
      =
    {word |
      (keepEmpty ∧ word = [])
        ∨
      word ∈ PreparedLinearLeastLanguage G S} := by
  apply Set.ext
  intro word
  constructor
  · intro hword
    rcases hword with heps | hder
    · exact Or.inl heps
    · exact
        Or.inr
          ((preparedLinearDerives_iff_leastLanguage
            G S word).1 hder)
  · intro hword
    rcases hword with heps | hleast
    · exact Or.inl heps
    · exact
        Or.inr
          ((preparedLinearDerives_iff_leastLanguage
            G S word).2 hleast)

/-- Source target language for a preprocessed indexed linear grammar. -/
def IndexedMixedCFG.linearTargetLanguage
    (G : IndexedMixedCFG N α P)
    (S : N)
    (keepEmpty : Prop) :
    Set (List α) :=
  {word |
    (keepEmpty ∧ word = [])
      ∨
    word ∈ LeastClosedLanguage G.toMixedRules S}

/--
After the indexed-prepared representation bridge, the constructed start
language is literally the original indexed source target.
-/
theorem indexedPreprocessedLinear_startLanguage_eq_source
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (S : N)
    (keepEmpty : Prop) :
    UntypedStartLanguage
        (LinearConstructedTerminalRule
          (G.toPreparedLinear hprep))
        (LinearConstructedBinaryRule
          (G.toPreparedLinear hprep))
        (linearConstructedStartRule
          (G.toPreparedLinear hprep) S)
        keepEmpty
      =
    G.linearTargetLanguage S keepEmpty := by
  rw [linearConstructed_startLanguage_eq_prepared]
  rw [preparedLinearStartLanguage_eq_least]
  unfold IndexedMixedCFG.linearTargetLanguage
  apply Set.ext
  intro word
  constructor
  · intro hword
    rcases hword with heps | hleast
    · exact Or.inl heps
    · exact
        Or.inr
          (by
            rw [← indexedMixedCFG_preparedLeast_eq_source
              G hprep S]
            exact hleast)
  · intro hword
    rcases hword with heps | hsource
    · exact Or.inl heps
    · exact
        Or.inr
          (by
            rw [indexedMixedCFG_preparedLeast_eq_source
              G hprep S]
            exact hsource)

end LinearConstructedStartLanguage

end TCS1
end LeanCfgProject
