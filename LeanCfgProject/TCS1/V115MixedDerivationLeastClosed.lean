import LeanCfgProject.TCS1.GeneralCFGDerivationBridge
import LeanCfgProject.TCS1.LeastClosedCFGLanguage

/-!
# TCS #1 v115: parse-tree / least-closed CFG semantics bridge

The inverse-homomorphism construction is easier to verify by structural
induction on explicit parse trees, while the normalization and learning
development uses the least-closed semantics.  This file proves the two
semantics equal for arbitrary mixed CFGs.

No finiteness assumption is used here.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V115MixedDerivationLeastClosed

variable {N : Type u} {α : Type v}

mutual

/-- Every explicit CFG parse tree belongs to every closed interpretation. -/
theorem v115_mixedDerives_mem_of_closed
    {R : MixedRules N α}
    {L : N → Set (Word α)}
    (hclosed : GrammarClosed R L)
    {A : N} {w : Word α}
    (d : MixedDerives R A w) :
    w ∈ L A := by
  cases d with
  | @rule A rhs pieces hR hpieces =>
      apply hclosed A
      refine ⟨rhs, hR, ?_⟩
      exact
        v115_mixedSymbolsDerive_realizes_of_closed
          hclosed hpieces

/-- Symbolwise parse trees realize their concatenated yield in any
closed interpretation. -/
theorem v115_mixedSymbolsDerive_realizes_of_closed
    {R : MixedRules N α}
    {L : N → Set (Word α)}
    (hclosed : GrammarClosed R L)
    {rhs : List (MixedSymbol N α)}
    {pieces : List (Word α)}
    (d : MixedSymbolsDerive R rhs pieces) :
    RhsRealizes L rhs pieces.flatten := by
  cases d with
  | nil =>
      rfl
  | @terminal a rhs pieces tail =>
      change
        ∃ rest,
          ([a] :: pieces).flatten = a :: rest ∧
          RhsRealizes L rhs rest
      refine ⟨pieces.flatten, by simp, ?_⟩
      exact
        v115_mixedSymbolsDerive_realizes_of_closed
          hclosed tail
  | @nonterminal A rhs w pieces head tail =>
      change
        ∃ u rest,
          (w :: pieces).flatten = u ++ rest ∧
          u ∈ L A ∧
          RhsRealizes L rhs rest
      refine
        ⟨w, pieces.flatten, by simp, ?_, ?_⟩
      · exact v115_mixedDerives_mem_of_closed hclosed head
      · exact
          v115_mixedSymbolsDerive_realizes_of_closed
            hclosed tail

end

/-- The explicit parse-tree semantics is exactly the least closed semantics. -/
theorem v115_mixedDerives_iff_leastClosedLanguage
    {R : MixedRules N α}
    {A : N} {w : Word α} :
    MixedDerives R A w ↔
      w ∈ LeastClosedLanguage R A := by
  constructor
  · intro d L hL
    exact v115_mixedDerives_mem_of_closed hL d
  · intro hw
    apply hw (MixedNonterminalLanguage R)
    intro B z hz
    exact (mixedDerives_iff_ruleStep).2 hz

/-- Set-valued form of the same semantic bridge. -/
theorem v115_mixedNonterminalLanguage_eq_leastClosed
    (R : MixedRules N α)
    (A : N) :
    MixedNonterminalLanguage R A =
      LeastClosedLanguage R A := by
  apply Set.ext
  intro w
  exact v115_mixedDerives_iff_leastClosedLanguage

end V115MixedDerivationLeastClosed

end TCS1
end LeanCfgProject
