import LeanCfgProject.TCS1.GeneralCFGDerivation

/-!
# TCS #1 v65: bridge between parse trees and RHS semantics

The terminal-isolation kernel was stated using the semantic evaluator
`RhsRealizes`, while the full grammar semantics is represented by explicit
mutual parse trees in `GeneralCFGDerivation`. This file proves that the two
views coincide when each nonterminal is interpreted by its generated
language.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section GeneralCFGDerivationBridge

variable {N : Type u}
variable {α : Type v}

/-- Aligned symbol derivations realize the concatenated terminal word. -/
theorem mixedSymbolsDerive_to_rhsRealizes
    {R : MixedRules N α}
    {rhs : List (MixedSymbol N α)}
    {pieces : List (List α)}
    (d : MixedSymbolsDerive R rhs pieces) :
    RhsRealizes (MixedNonterminalLanguage R) rhs pieces.flatten := by
  cases d with
  | nil =>
      rfl
  | @terminal a rhs pieces tail =>
      have ih :=
        mixedSymbolsDerive_to_rhsRealizes tail
      change ∃ t, ([a] :: pieces).flatten = a :: t ∧
        RhsRealizes (MixedNonterminalLanguage R) rhs t
      refine ⟨pieces.flatten, ?_, ih⟩
      simp
  | @nonterminal A rhs w pieces head tail =>
      have ih :=
        mixedSymbolsDerive_to_rhsRealizes tail
      change ∃ u v, (w :: pieces).flatten = u ++ v ∧
        u ∈ MixedNonterminalLanguage R A ∧
        RhsRealizes (MixedNonterminalLanguage R) rhs v
      refine ⟨w, pieces.flatten, ?_, ?_, ih⟩
      · simp
      · exact head
termination_by rhs.length
decreasing_by omega

/--
Conversely, every semantic RHS realization can be represented by aligned
parse-tree pieces whose join is the realized word.
-/
theorem rhsRealizes_to_mixedSymbolsDerive
    {R : MixedRules N α}
    (rhs : List (MixedSymbol N α))
    (w : List α)
    (h : RhsRealizes (MixedNonterminalLanguage R) rhs w) :
    ∃ pieces,
      MixedSymbolsDerive R rhs pieces ∧
      pieces.flatten = w := by
  induction rhs generalizing w with
  | nil =>
      change w = [] at h
      subst w
      exact ⟨[], MixedSymbolsDerive.nil, rfl⟩
  | cons s rhs ih =>
      cases s with
      | inr a =>
          change ∃ tail, w = a :: tail ∧
            RhsRealizes (MixedNonterminalLanguage R) rhs tail at h
          rcases h with ⟨tail, hw, htail⟩
          obtain ⟨pieces, hd, hjoin⟩ := ih tail htail
          refine ⟨[a] :: pieces, MixedSymbolsDerive.terminal hd, ?_⟩
          simp [hjoin, hw]
      | inl A =>
          change ∃ u v, w = u ++ v ∧
            u ∈ MixedNonterminalLanguage R A ∧
            RhsRealizes (MixedNonterminalLanguage R) rhs v at h
          rcases h with ⟨u, v, hw, hu, hv⟩
          obtain ⟨pieces, hd, hjoin⟩ := ih v hv
          refine ⟨u :: pieces, MixedSymbolsDerive.nonterminal hu hd, ?_⟩
          simp [hjoin, hw]

/--
An explicit parse-tree derivation is equivalent to membership in the
one-step grammar operator evaluated at the grammar's own generated
nonterminal languages.
-/
theorem mixedDerives_iff_ruleStep
    {R : MixedRules N α}
    {A : N}
    {w : List α} :
    MixedDerives R A w ↔
      w ∈ RuleStepLanguage R (MixedNonterminalLanguage R) A := by
  constructor
  · intro d
    cases d with
    | @rule _ rhs pieces hR hpieces =>
        exact ⟨rhs, hR, mixedSymbolsDerive_to_rhsRealizes hpieces⟩
  · intro h
    rcases h with ⟨rhs, hR, hreal⟩
    obtain ⟨pieces, hp, hjoin⟩ :=
      rhsRealizes_to_mixedSymbolsDerive rhs w hreal
    rw [← hjoin]
    exact MixedDerives.rule hR hp

end GeneralCFGDerivationBridge

end TCS1
end LeanCfgProject
