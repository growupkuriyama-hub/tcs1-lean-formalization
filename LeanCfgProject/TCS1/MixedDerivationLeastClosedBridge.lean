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

/-- Every successful mixed CFG parse tree is sound in any rule-closed
nonterminal interpretation.

Proved with the mutual recursor `MixedDerives.rec` (explicit motives for both
mutual families), so no structural/well-founded termination inference is
involved. -/
theorem mixedDerives_mem_closed
    (R : MixedRules N α)
    (L : N → Set (List α))
    (hclosed : GrammarClosed R L)
    {A : N} {w : List α}
    (d : MixedDerives R A w) :
    w ∈ L A := by
  refine MixedDerives.rec
    (motive_1 := fun A w _ => w ∈ L A)
    (motive_2 := fun rhs pieces _ => RhsRealizes L rhs pieces.flatten)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR _ ih
    apply hclosed A
    exact ⟨rhs, hR, ih⟩
  case nil =>
    show ([] : List (List α)).flatten = []
    rfl
  case terminal =>
    intro a rhs pieces _ ih
    show ∃ t, ([a] :: pieces).flatten = a :: t ∧ RhsRealizes L rhs t
    exact ⟨pieces.flatten, by simp, ih⟩
  case nonterminal =>
    intro A rhs w pieces _ _ ihA ihT
    show ∃ u v, (w :: pieces).flatten = u ++ v ∧ u ∈ L A ∧
      RhsRealizes L rhs v
    exact ⟨w, pieces.flatten, by simp, ihA, ihT⟩

/-- Each aligned RHS derivation realizes its word under any closed
interpretation of nonterminals (second component of the same mutual
induction, via `MixedSymbolsDerive.rec`). -/
theorem mixedSymbolsDerive_realizes_closed
    (R : MixedRules N α)
    (L : N → Set (List α))
    (hclosed : GrammarClosed R L)
    {rhs : List (MixedSymbol N α)}
    {pieces : List (List α)}
    (d : MixedSymbolsDerive R rhs pieces) :
    RhsRealizes L rhs pieces.flatten := by
  refine MixedSymbolsDerive.rec
    (motive_1 := fun A w _ => w ∈ L A)
    (motive_2 := fun rhs pieces _ => RhsRealizes L rhs pieces.flatten)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR _ ih
    apply hclosed A
    exact ⟨rhs, hR, ih⟩
  case nil =>
    show ([] : List (List α)).flatten = []
    rfl
  case terminal =>
    intro a rhs pieces _ ih
    show ∃ t, ([a] :: pieces).flatten = a :: t ∧ RhsRealizes L rhs t
    exact ⟨pieces.flatten, by simp, ih⟩
  case nonterminal =>
    intro A rhs w pieces _ _ ihA ihT
    show ∃ u v, (w :: pieces).flatten = u ++ v ∧ u ∈ L A ∧
      RhsRealizes L rhs v
    exact ⟨w, pieces.flatten, by simp, ihA, ihT⟩

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
