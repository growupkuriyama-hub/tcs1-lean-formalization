import LeanCfgProject.TCS1.LinearNormalizationCompleteness

/-!
# TCS #1: paper-facing prepared linear normalization package

The preceding construction modules now provide all three ingredients of the
binarization stage in Appendix "Proof of the linear-spine SSBNF
normalization":

* an actual finite terminal/binary grammar;
* exact preservation of every old nonterminal language; and
* the linear-spine syntactic condition with an explicit linear size bound.

This facade packages those conclusions at the level immediately after the
standard epsilon/unit/useless-symbol preprocessing.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section PreparedLinearNormalizationFacade

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/--
The concrete factorization preserves the least language of every prepared old
nonterminal exactly.
-/
theorem linearConstructed_old_language_eq_preparedLeast
    (G : PreparedLinearIndexedCFG N α P)
    (A : N) :
    {word |
      UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearOldState G A) word}
      =
    PreparedLinearLeastLanguage G A := by
  apply Set.ext
  intro word
  change
    UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearOldState G A) word
      ↔
    word ∈ PreparedLinearLeastLanguage G A
  rw [linearConstructed_old_language_iff_prepared]
  exact preparedLinearDerives_iff_leastLanguage G A word

/--
Complete local form of Proposition linear-normal after standard preprocessing.

The first conjunct is exact language preservation on every old nonterminal;
the second is the required one-wrapper-child linear-spine shape; and the third
is an explicit linear bound for the concrete state and rule index spaces.
-/
theorem preparedLinear_normalization_package
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    (∀ A : N,
      {word |
        UntypedDerives
          (LinearConstructedTerminalRule G)
          (LinearConstructedBinaryRule G)
          (linearOldState G A) word}
        =
      PreparedLinearLeastLanguage G A)
    ∧
    UntypedLinearSpineShape
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (LinearConstructedWrapper G)
    ∧
    Fintype.card (LinearConstructedState G) +
      (Fintype.card (LinearConstructedTerminalRuleIndex G) +
       Fintype.card (LinearConstructedBinaryRuleIndex G))
      ≤
    2 * G.encodingScale := by
  refine ⟨?_, linearConstructed_untypedLinearSpineShape G, ?_⟩
  · intro A
    exact linearConstructed_old_language_eq_preparedLeast G A
  · exact linearConstructed_combined_size_le_twice_scale G

end PreparedLinearNormalizationFacade

end TCS1
end LeanCfgProject
