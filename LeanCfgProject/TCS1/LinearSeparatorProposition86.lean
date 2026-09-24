import LeanCfgProject.TCS1.LinearSeparatorPreparedGrammar
import LeanCfgProject.TCS1.LinearSeparatorNonregular
import LeanCfgProject.TCS1.LinearSeparatorFixedH

/-!
# TCS #1 v78: Proposition 8.6 separation package

This facade bundles the Lean verification of Proposition 8.6.  It includes
the concrete prepared linear-CFG witness, exact generated-language equality,
Mathlib regular-language nonregularity, the four-element fixed-h positive
result, failure of Clark--Eyraud substitutability, and failure of every fixed
(k,l) window.

The smaller theorem below keeps the substitutability claims available as a
standalone core; the final theorem packages all semantic components together.
-/

namespace LeanCfgProject
namespace TCS1

/-- Lean-verified substitutability/separation core of Proposition 8.6. -/
theorem lpm_proposition86_substitutability_core :
    FixedHSubstitutable lpmTyping LpmLanguage ∧
      ¬ ClarkEyraudSubstitutable LpmLanguage ∧
      ∀ k l : Nat,
        ¬ FixedWindowSubstitutable k l LpmLanguage := by
  refine ⟨lpm_fixedHSubstitutable, lpm_not_clarkEyraud, ?_⟩
  intro k l
  exact lpm_not_fixedWindowSubstitutable k l

/--
Full semantic package for Proposition 8.6.

The first conjunct supplies an explicit prepared linear-CFG witness whose
initial-set language is exactly L_{±,e}; the second is Mathlib regular-language
nonregularity; the remaining conjuncts are the three substitutability claims.
-/
theorem lpm_proposition86_full_semantic :
    LpmPreparedStartLanguage = LpmLanguage ∧
      ¬ LpmFormalLanguage.IsRegular ∧
      FixedHSubstitutable lpmTyping LpmLanguage ∧
      ¬ ClarkEyraudSubstitutable LpmLanguage ∧
      ∀ k l : Nat,
        ¬ FixedWindowSubstitutable k l LpmLanguage := by
  refine
    ⟨lpm_prepared_linear_language_eq,
      lpm_not_regular,
      lpm_fixedHSubstitutable,
      lpm_not_clarkEyraud,
      ?_⟩
  intro k l
  exact lpm_not_fixedWindowSubstitutable k l


end TCS1
end LeanCfgProject
