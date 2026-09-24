import LeanCfgProject.TCS1.LinearMixedRhsDecomposition
import LeanCfgProject.TCS1.FiniteCFGEncoding

/-!
# TCS #1: indexed preprocessed linear CFG to prepared normalization input

This module closes the representation gap immediately before the specialized
linear-spine binarization.

The source is the ordinary finite indexed mixed CFG representation used by the
rest of the normalization development.  Assuming each production is already
linear and the standard preprocessing has removed empty and unit non-start
rules, every indexed RHS has a prepared linear representation.

We choose those representations once, preserve the production index and left
side exactly, and prove:

* exact mixed-RHS recovery production by production;
* exact preservation of total RHS length;
* equivalence of source grammar closure and prepared closure;
* equality of the corresponding least generated languages.

Thus the verified prepared linear-normalization package applies directly to an
ordinary preprocessed finite indexed linear CFG.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearIndexedPreprocessedBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Preconditions supplied by the standard preprocessing stage. -/
structure IndexedLinearPreprocessed
    (G : IndexedMixedCFG N α P) : Prop where
  linear :
    ∀ p : P,
      MixedRhsLinear (G.rhs p)
  nonempty :
    ∀ p : P,
      G.rhs p ≠ []
  nonunit :
    ∀ p : P, ∀ B : N,
      G.rhs p ≠ [Sum.inl B]

/-- One chosen prepared RHS for every source production. -/
noncomputable def indexedPreparedLinearRhs
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (p : P) :
    PreparedLinearRhs N α :=
  Classical.choose
    (exists_preparedLinearRhs_of_linear_nonempty_nonunit
      (G.rhs p)
      (hprep.linear p)
      (hprep.nonempty p)
      (hprep.nonunit p))

/-- The chosen prepared RHS recovers the original mixed RHS exactly. -/
theorem indexedPreparedLinearRhs_toMixedRhs
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (p : P) :
    (indexedPreparedLinearRhs G hprep p).toMixedRhs =
      G.rhs p := by
  exact
    Classical.choose_spec
      (exists_preparedLinearRhs_of_linear_nonempty_nonunit
        (G.rhs p)
        (hprep.linear p)
        (hprep.nonempty p)
        (hprep.nonunit p))

/--
Prepared indexed grammar obtained without changing production identities or
left-hand sides.
-/
noncomputable def IndexedMixedCFG.toPreparedLinear
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G) :
    PreparedLinearIndexedCFG N α P where
  lhs := G.lhs
  rhs := indexedPreparedLinearRhs G hprep

@[simp] theorem indexedMixedCFG_toPreparedLinear_lhs
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (p : P) :
    (G.toPreparedLinear hprep).lhs p =
      G.lhs p := by
  rfl

@[simp] theorem indexedMixedCFG_toPreparedLinear_rhs_toMixed
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (p : P) :
    ((G.toPreparedLinear hprep).rhs p).toMixedRhs =
      G.rhs p := by
  exact indexedPreparedLinearRhs_toMixedRhs G hprep p

/-- Source RHS lengths are preserved production by production. -/
theorem indexedMixedCFG_toPreparedLinear_sourceLength
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (p : P) :
    ((G.toPreparedLinear hprep).rhs p).sourceLength =
      (G.rhs p).length := by
  rw [← PreparedLinearRhs.toMixedRhs_length]
  rw [indexedMixedCFG_toPreparedLinear_rhs_toMixed]

/-- Hence the total indexed RHS length is preserved exactly. -/
theorem indexedMixedCFG_toPreparedLinear_totalSourceLength
    [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G) :
    (G.toPreparedLinear hprep).totalSourceLength =
      G.totalRhsLength := by
  classical
  unfold PreparedLinearIndexedCFG.totalSourceLength
  unfold IndexedMixedCFG.totalRhsLength
  apply Finset.sum_congr rfl
  intro p hp
  exact indexedMixedCFG_toPreparedLinear_sourceLength G hprep p

/--
Prepared closure is exactly ordinary mixed-CFG closure for the same indexed
source grammar.
-/
theorem indexedMixedCFG_preparedClosed_iff_grammarClosed
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (L : N → Set (List α)) :
    PreparedLinearGrammarClosed
        (G.toPreparedLinear hprep) L
      ↔
    GrammarClosed G.toMixedRules L := by
  constructor
  · intro hprepared A word hstep
    rcases hstep with
      ⟨rhs, ⟨p, hlhs, hrhs⟩, hreal⟩
    subst A
    apply hprepared p word
    apply
      (preparedLinearRhs_realizes_iff_mixed
        L ((G.toPreparedLinear hprep).rhs p) word).2
    rw [indexedMixedCFG_toPreparedLinear_rhs_toMixed]
    rw [hrhs]
    exact hreal
  · intro hclosed p word hreal
    apply hclosed (G.lhs p)
    refine
      ⟨G.rhs p, ?_, ?_⟩
    · exact ⟨p, rfl, rfl⟩
    · have hmixed :=
        (preparedLinearRhs_realizes_iff_mixed
          L ((G.toPreparedLinear hprep).rhs p) word).1
          hreal
      rw [indexedMixedCFG_toPreparedLinear_rhs_toMixed] at hmixed
      exact hmixed

/--
The least generated language of every old nonterminal is unchanged by the
representation conversion.
-/
theorem indexedMixedCFG_preparedLeast_eq_source
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (A : N) :
    PreparedLinearLeastLanguage
        (G.toPreparedLinear hprep) A
      =
    LeastClosedLanguage G.toMixedRules A := by
  apply Set.ext
  intro word
  constructor
  · intro hprepared L hclosed
    exact
      hprepared L
        ((indexedMixedCFG_preparedClosed_iff_grammarClosed
          G hprep L).2 hclosed)
  · intro hsource L hclosed
    exact
      hsource L
        ((indexedMixedCFG_preparedClosed_iff_grammarClosed
          G hprep L).1 hclosed)

/-- Encoding scale naturally inherited by the specialized linear front end. -/
def IndexedMixedCFG.linearPreparedScale
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P) : Nat :=
  Fintype.card α + G.encodingScale

/-- The prepared encoding scale is exactly the source scale plus the alphabet. -/
theorem indexedMixedCFG_toPreparedLinear_encodingScale
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G) :
    (G.toPreparedLinear hprep).encodingScale =
      G.linearPreparedScale := by
  unfold PreparedLinearIndexedCFG.encodingScale
  unfold IndexedMixedCFG.linearPreparedScale
  unfold IndexedMixedCFG.encodingScale
  rw [indexedMixedCFG_toPreparedLinear_totalSourceLength]
  omega

/--
Paper-facing local normalization package for an ordinary preprocessed indexed
linear CFG.
-/
theorem indexedPreprocessedLinear_normalization_package
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G) :
    (∀ A : N,
      {word |
        UntypedDerives
          (LinearConstructedTerminalRule
            (G.toPreparedLinear hprep))
          (LinearConstructedBinaryRule
            (G.toPreparedLinear hprep))
          (linearOldState
            (G.toPreparedLinear hprep) A)
          word}
        =
      LeastClosedLanguage G.toMixedRules A)
    ∧
    UntypedLinearSpineShape
      (LinearConstructedTerminalRule
        (G.toPreparedLinear hprep))
      (LinearConstructedBinaryRule
        (G.toPreparedLinear hprep))
      (LinearConstructedWrapper
        (G.toPreparedLinear hprep))
    ∧
    Fintype.card
        (LinearConstructedState
          (G.toPreparedLinear hprep))
      +
      (Fintype.card
          (LinearConstructedTerminalRuleIndex
            (G.toPreparedLinear hprep))
       +
       Fintype.card
          (LinearConstructedBinaryRuleIndex
            (G.toPreparedLinear hprep)))
      ≤
    2 * G.linearPreparedScale := by
  have hpackage :=
    preparedLinear_normalization_package
      (G.toPreparedLinear hprep)
  refine ⟨?_, hpackage.2.1, ?_⟩
  · intro A
    calc
      {word |
        UntypedDerives
          (LinearConstructedTerminalRule
            (G.toPreparedLinear hprep))
          (LinearConstructedBinaryRule
            (G.toPreparedLinear hprep))
          (linearOldState
            (G.toPreparedLinear hprep) A)
          word}
        =
      PreparedLinearLeastLanguage
        (G.toPreparedLinear hprep) A :=
          hpackage.1 A
      _ =
      LeastClosedLanguage G.toMixedRules A :=
        indexedMixedCFG_preparedLeast_eq_source
          G hprep A
  · rw [← indexedMixedCFG_toPreparedLinear_encodingScale
      G hprep]
    exact hpackage.2.2

end LinearIndexedPreprocessedBridge

end TCS1
end LeanCfgProject
