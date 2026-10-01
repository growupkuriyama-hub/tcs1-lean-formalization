import LeanCfgProject.TCS1.V83LevelCodedDisplayedThickness
import LeanCfgProject.TCS1.V83LevelCodedLowerBoundBridge

/-!
# TCS #1 v83: direct package for the ordinary-thickness lower bound

This module collects the verified concrete pieces of the manuscript theorem
before the final generic reduced-CFG packaging step.  The only
language-theoretic assumptions are the two Appendix combinatorial obligations
already isolated in the substitutability bridge.
-/

namespace LeanCfgProject
namespace TCS1

/--
Direct theorem package matching the displayed R_n/R_n^- argument.

It records exact target languages, the n+5 productive-witness bounds, linear
displayed production-symbol counts, fixed-h class membership, and the
exponential characteristic-sample norm lower bound.  The remaining
representation-layer task is to package the displayed grammars as generic
reduced CFG objects and transport these facts.
-/
theorem levelCode_direct_ordinaryThickness_package
    (n : Nat)
    (_hn : 1 ≤ n)
    (B :
      Finset (Word LevelTreeSymbol) →
        Set (Word LevelTreeSymbol))
    (hadm : LevelBodyToggleAdmissible n)
    (hlocal : LevelBodyToggleCutLocality n)
    {C Cminus : Finset (Word LevelTreeSymbol)}
    (hC :
      IsSetDrivenCharacteristicSample
        B (LevelTreeLanguage n) C)
    (hCminus :
      IsSetDrivenCharacteristicSample
        B (LevelTreeShortcutLanguage n) Cminus) :
    LevelCodeRStartLanguage n =
        LevelTreeLanguage n
      ∧
    LevelCodeRMinusStartLanguage n =
        (LevelTreeLanguage n \
          ({cleanLevelTreeWord n} :
            Set (Word LevelTreeSymbol)))
      ∧
    ((∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeZDerives i w ∧
          w.length ≤ n + 5) ∧
      (∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeADerives i w ∧
          w.length ≤ n + 5))
      ∧
    ((∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeZDerives i w ∧
          w.length ≤ n + 5) ∧
      (∀ i : Nat, i < n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeADerives i w ∧
          w.length ≤ n + 5) ∧
      (∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeAMinusDerives i w ∧
          w.length ≤ n + 5))
      ∧
    (levelCodeRProductionSymbolCount n +
        levelCodeRMinusProductionSymbolCount n
      ≤ 44 * (n + 1) + 9)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeLanguage n)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeShortcutLanguage n)
      ∧
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  have hLower :=
    levelTree_lowerBound_package_of_appendix_obligations
      n B hadm hlocal hC hCminus
  rcases hLower with
    ⟨hFull, hMinus, hNorm⟩
  refine ⟨levelCodeRStartLanguage_eq n, ?_, ?_, ?_, ?_,
    hFull, hMinus, hNorm⟩
  · calc
      LevelCodeRMinusStartLanguage n =
          LevelTreeShortcutLanguage n :=
        levelCodeRMinusStartLanguage_eq n
      _ =
          LevelTreeLanguage n \
            ({cleanLevelTreeWord n} :
              Set (Word LevelTreeSymbol)) :=
        levelTreeShortcutLanguage_eq_diff_clean n
  · exact levelCodeR_displayed_thickness_bound n
  · exact levelCodeRMinus_displayed_thickness_bound n
  · exact levelCode_displayed_joint_symbolCount_linear n


/--
Unconditional direct package: the Appendix admissibility and cut-locality
premises are now discharged for the concrete level-coded family.
-/
theorem levelCode_direct_ordinaryThickness_package_unconditional
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
    LevelCodeRStartLanguage n =
        LevelTreeLanguage n
      ∧
    LevelCodeRMinusStartLanguage n =
        (LevelTreeLanguage n \
          ({cleanLevelTreeWord n} :
            Set (Word LevelTreeSymbol)))
      ∧
    ((∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeZDerives i w ∧
          w.length ≤ n + 5) ∧
      (∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeADerives i w ∧
          w.length ≤ n + 5))
      ∧
    ((∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeZDerives i w ∧
          w.length ≤ n + 5) ∧
      (∀ i : Nat, i < n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeADerives i w ∧
          w.length ≤ n + 5) ∧
      (∀ i : Nat, i ≤ n →
        ∃ w : Word LevelTreeSymbol,
          LevelCodeAMinusDerives i w ∧
          w.length ≤ n + 5))
      ∧
    (levelCodeRProductionSymbolCount n +
        levelCodeRMinusProductionSymbolCount n
      ≤ 44 * (n + 1) + 9)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeLanguage n)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeShortcutLanguage n)
      ∧
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  exact
    levelCode_direct_ordinaryThickness_package
      n hn B
      (levelBodyToggleAdmissible_levelTree n)
      (levelBodyToggleCutLocality_levelTree n)
      hC hCminus

end TCS1
end LeanCfgProject
