import LeanCfgProject.TCS1.DeltaStarFourBlockDFA
import LeanCfgProject.TCS1.DeltaStarDoubleDeltaNonlinear

/-!
# TCS #1 v78: machine-checked non-linearity reduction

The manuscript proves Delta-star non-linear by the chain

  Delta-star linear
    => Delta-star intersect a* b* a* b* linear
    => Delta Delta linear,

contradicting non-linearity of Delta Delta.

The full chain is now machine checked internally.  The four-block DFA
recognizes exactly a* b* a* b*; finite raw-linear presentations are closed
under intersection with that DFA; the intersection is exactly Double Delta;
and the bounded linear pumping theorem proves Double Delta itself is not
linear.  The conditional reduction theorem is retained as a reusable lemma,
and the unconditional theorem below closes the manuscript claim.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

universe u w

/--
If the cited Double-Delta language has no finite raw-linear presentation, then
Delta-star has no such presentation either.

This is the exact machine-checked reduction underlying the manuscript's
non-linearity sentence.
-/
theorem deltaStar_not_rawLinearRepresentable_of_doubleDelta
    (hDouble :
      ¬ RawLinearInitialRepresentable.{u, 0, w}
        DoubleDeltaLanguage) :
    ¬ RawLinearInitialRepresentable.{u, 0, w}
        Language := by
  intro hDelta
  have hInter :=
    rawLinearInitialRepresentable_inter_dfa
      (D := fourBlockDFA)
      hDelta
  rw [fourBlockDFA_accepts_eq] at hInter
  rw [language_inter_fourBlock_eq_doubleDelta] at hInter
  exact hDouble hInter

/--
Presentation-level form: assuming the cited Double-Delta obstruction, no
finite indexed linear CFG can generate Delta-star from the selected start
nonterminal.
-/
theorem deltaStar_no_indexedLinear_presentation_of_doubleDelta
    {N : Type u}
    {P : Type w}
    [Fintype N]
    [Fintype P]
    (hDouble :
      ¬ RawLinearInitialRepresentable.{u, 0, w}
        DoubleDeltaLanguage)
    (G : IndexedMixedCFG N Symbol P)
    (hlinear : G.IsLinear)
    (S : N)
    (hlang :
      LeastClosedLanguage G.toMixedRules S =
        Language) :
    False := by
  have hRep :
      RawLinearInitialRepresentable.{u, 0, w}
        (LeastClosedLanguage G.toMixedRules S) :=
    indexedLinear_to_rawInitialRepresentable
      G hlinear S
  rw [hlang] at hRep
  exact
    (deltaStar_not_rawLinearRepresentable_of_doubleDelta
      hDouble) hRep

theorem deltaStar_not_rawLinearRepresentable
    : ¬ RawLinearInitialRepresentable.{u, 0, w}
        Language := by
  exact
    deltaStar_not_rawLinearRepresentable_of_doubleDelta
      doubleDelta_not_rawLinearInitialRepresentable

/--
Unconditional presentation-level non-linearity: no finite indexed linear CFG
can generate Delta-star from any selected start nonterminal.
-/
theorem deltaStar_no_indexedLinear_presentation
    {N : Type u}
    {P : Type w}
    [Fintype N]
    [Fintype P]
    (G : IndexedMixedCFG N Symbol P)
    (hlinear : G.IsLinear)
    (S : N)
    (hlang :
      LeastClosedLanguage G.toMixedRules S =
        Language) :
    False := by
  exact
    deltaStar_no_indexedLinear_presentation_of_doubleDelta
      doubleDelta_not_rawLinearInitialRepresentable
      G hlinear S hlang

end DeltaStar
end TCS1
end LeanCfgProject
