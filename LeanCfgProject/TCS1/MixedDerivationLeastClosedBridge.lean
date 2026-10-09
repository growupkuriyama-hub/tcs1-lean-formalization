import LeanCfgProject.TCS1.GeneralCFGDerivationBridge
import LeanCfgProject.TCS1.LeastClosedCFGLanguage
import LeanCfgProject.TCS1.V83LevelCodedIndexedReducedness

/-!
# Source CFG thickness: explicit derivations versus least-closed semantics

The indexed source-size normalization uses the denotational
`LeastClosedLanguage` and its `YieldBound` interface. The paper-facing
ordinary-thickness presentations instead use successful parse-tree derivations
(`MixedDerives` / `IndexedMixedThicknessAtMost`).

These lemmas give the missing soundness bridge without taking equivalence of
the two semantics as an axiom or an additional normalization hypothesis.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section MixedDerivationLeastClosedBridge

variable {N : Type u} {α : Type v}

mutual

/-- Every successful mixed CFG parse tree is sound in any rule-closed
nonterminal interpretation. -/
theorem mixedDerives_mem_closed
    (R : MixedRules N α)
    (L : N → Set (List α))
    (hclosed : GrammarClosed R L)
    {A : N} {w : List α}
    (d : MixedDerives R A w) :
    w ∈ L A := by
  cases d with
  | @rule A rhs pieces hR hpieces =>
      apply hclosed A
      exact ⟨rhs, hR,
        mixedSymbolsDerive_realizes_closed R L hclosed hpieces⟩

/-- Each aligned RHS derivation realizes its word under any closed
interpretation of nonterminals. -/
theorem mixedSymbolsDerive_realizes_closed
    (R : MixedRules N α)
    (L : N → Set (List α))
    (hclosed : GrammarClosed R L)
    {rhs : List (MixedSymbol N α)}
    {pieces : List (List α)}
    (d : MixedSymbolsDerive R rhs pieces) :
    RhsRealizes L rhs pieces.flatten := by
  cases d with
  | nil =>
      rfl
  | @terminal a rhs pieces tail =>
      refine ⟨pieces.flatten, ?_, ?_⟩
      · simp
      · exact mixedSymbolsDerive_realizes_closed R L hclosed tail
  | @nonterminal A rhs w pieces head tail =>
      refine ⟨w, pieces.flatten, ?_, ?_, ?_⟩
      · simp
      · exact mixedDerives_mem_closed R L hclosed head
      · exact mixedSymbolsDerive_realizes_closed R L hclosed tail

end

/-- A concrete successful parse-tree yield belongs to the least rule-closed
source language. -/
theorem mixedDerives_mem_leastClosed
    (R : MixedRules N α)
    {A : N} {w : List α}
    (d : MixedDerives R A w) :
    w ∈ LeastClosedLanguage R A := by
  intro L hclosed
  exact mixedDerives_mem_closed R L hclosed d

end MixedDerivationLeastClosedBridge

section IndexedSourceThicknessBridge

variable {N : Type u} {α : Type v} {P : Type w}

/-- The ordinary source thickness bound stated with successful indexed
derivations supplies the least-closed `YieldBound` required by polynomial
normalization. -/
theorem indexedMixedThicknessAtMost_implies_yieldBound
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hthick : IndexedMixedThicknessAtMost G τR) :
    YieldBound
      (fun A => LeastClosedLanguage G.toMixedRules A)
      τR := by
  intro A
  obtain ⟨w, hw, hlen⟩ := hthick A
  exact ⟨w, mixedDerives_mem_leastClosed G.toMixedRules hw, hlen⟩

end IndexedSourceThicknessBridge

end TCS1
end LeanCfgProject
