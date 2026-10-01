import LeanCfgProject.TCS1.V83LevelCodedIndexedReducedness
import LeanCfgProject.TCS1.V83LevelCodedIndexedSize
import LeanCfgProject.TCS1.V83LevelCodedLowerBoundBridge

/-!
# TCS #1 v83: indexed ordinary-thickness lower-bound package

This is the theorem-facing representation package for the manuscript's
ordinary-thickness lower bound.  It uses the actual finite indexed CFGs,
not only the direct paper-facing derivation relations.

For every n >= 1 it records:
* exact generated languages T_n and T_n^-;
* reducedness of both concrete grammars;
* ordinary thickness at most n+5;
* a joint linear encoding-size bound;
* fixed-h substitutability of both targets; and
* the exponential characteristic-sample norm lower bound.
-/

namespace LeanCfgProject
namespace TCS1

theorem levelCode_indexed_ordinaryThickness_lowerBound_package
    (n : Nat)
    (hn : 1 ≤ n)
    (B :
      Finset (Word LevelTreeSymbol) →
        Set (Word LevelTreeSymbol))
    {C Cminus : Finset (Word LevelTreeSymbol)}
    (hC :
      IsSetDrivenCharacteristicSample
        B (LevelTreeLanguage n) C)
    (hCminus :
      IsSetDrivenCharacteristicSample
        B (LevelTreeShortcutLanguage n) Cminus) :
    MixedNonterminalLanguage
        (levelCodeRIndexedGrammar n).toMixedRules
        LevelCodeRNT.start =
      LevelTreeLanguage n
      ∧
    MixedNonterminalLanguage
        (levelCodeRMinusIndexedGrammar (n - 1)).toMixedRules
        LevelCodeRMinusNT.start =
      LevelTreeShortcutLanguage n
      ∧
    IndexedMixedReduced
        (levelCodeRIndexedGrammar n)
        LevelCodeRNT.start
      ∧
    IndexedMixedReduced
        (levelCodeRMinusIndexedGrammar (n - 1))
        LevelCodeRMinusNT.start
      ∧
    IndexedMixedThicknessAtMost
        (levelCodeRIndexedGrammar n)
        (n + 5)
      ∧
    IndexedMixedThicknessAtMost
        (levelCodeRMinusIndexedGrammar (n - 1))
        (n + 5)
      ∧
    ((levelCodeRIndexedGrammar n).encodingScale +
        (levelCodeRMinusIndexedGrammar (n - 1)).encodingScale
      ≤ 49 * n + 61)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeLanguage n)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeShortcutLanguage n)
      ∧
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  have hnPred :
      n - 1 + 1 = n := by
    omega

  have hMinusLang :=
    levelCodeRMinusIndexed_start_language_eq (n - 1)
  rw [hnPred] at hMinusLang

  have hMinusThickness :=
    levelCodeRMinusIndexed_thickness_atMost (n - 1)
  have hBound :
      n - 1 + 6 = n + 5 := by
    omega
  rw [hBound] at hMinusThickness

  have hSize :=
    levelCodeIndexed_encodingScale_joint_linear (n - 1)
  rw [hnPred] at hSize

  obtain ⟨hFull, hMinus, hNorm⟩ :=
    levelTree_lowerBound_package
      n B hC hCminus

  exact
    ⟨levelCodeRIndexed_start_language_eq n,
      hMinusLang,
      levelCodeRIndexed_reduced n,
      levelCodeRMinusIndexed_reduced (n - 1),
      levelCodeRIndexed_thickness_atMost n,
      hMinusThickness,
      hSize,
      hFull,
      hMinus,
      hNorm⟩

end TCS1
end LeanCfgProject
