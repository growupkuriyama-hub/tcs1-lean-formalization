import LeanCfgProject.TCS1.LinearSeparatorProposition86

/-!
# TCS #1 v144–v148: `prop:linear-separator-example` in its existential form

From v142/v144 on, the manuscript states that `L_{±,e}` is linear, nonregular
and belongs to `C^lin_h` *for some* homomorphism `h` into a finite monoid
(the explicit four-element typing is now displayed after the proof).  The
existing theorem `lpm_proposition86_full_semantic` proves the statement for the
explicit typing `lpmTyping`; this file packages it as the existential claim.
The linear-CFG part is `LpmPreparedStartLanguage = LpmLanguage`
(`lpmPreparedLinearGrammar` is a linear grammar).
-/

namespace LeanCfgProject
namespace TCS1

theorem prop_linearSeparatorExample_existsH :
    LpmPreparedStartLanguage = LpmLanguage ∧
    ¬ LpmFormalLanguage.IsRegular ∧
    (∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (H : FixedFiniteMonoidHom LpmSymbol M),
      FixedHSubstitutable H LpmLanguage) ∧
    ¬ ClarkEyraudSubstitutable LpmLanguage ∧
    ∀ k l : Nat, ¬ FixedWindowSubstitutable k l LpmLanguage := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lpm_proposition86_full_semantic
  exact ⟨h1, h2, ⟨LpmType, inferInstance, inferInstance, lpmTyping, h3⟩, h4, h5⟩

end TCS1
end LeanCfgProject
