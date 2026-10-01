import LeanCfgProject.TCS1.V83LevelCodedTreeTyping
import LeanCfgProject.TCS1.V83LevelCodedTreeToggles
import LeanCfgProject.TCS1.V83LevelCodedSubstitutabilityBridge

/-!
# TCS #1 v83: level-coded lower-bound bridge

This module connects the concrete tree family to the generic operator-
independent lower-bound kernel.  The only language-theoretic premise left
explicit is the Appendix lemma that the full level-coded language is
Clark--Eyraud substitutable; once that premise is discharged, the concrete
fixed-h class membership and exponential characteristic-data lower bound
follow directly.
-/

namespace LeanCfgProject
namespace TCS1

/--
Concrete lower-bound package for the level-coded tree family, conditional only
on the Clark--Eyraud substitutability lemma that is being formalized
separately.
-/
theorem levelTree_lowerBound_package_of_clarkEyraud
    (n : Nat)
    (B :
      Finset (Word LevelTreeSymbol) →
        Set (Word LevelTreeSymbol))
    (hce :
      ClarkEyraudSubstitutableOn
        (LevelTreeLanguage n))
    {C Cminus : Finset (Word LevelTreeSymbol)}
    (hC :
      IsSetDrivenCharacteristicSample
        B (LevelTreeLanguage n) C)
    (hCminus :
      IsSetDrivenCharacteristicSample
        B (LevelTreeShortcutLanguage n) Cminus) :
    FixedHSubstitutable
        levelTreeTyping (LevelTreeLanguage n)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeShortcutLanguage n)
      ∧
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  obtain ⟨hFull, hMinus⟩ :=
    levelTree_fixedH_package_of_clarkEyraud n hce
  refine ⟨hFull, hMinus, ?_⟩
  apply
    levelCleanTree_characteristicSample_norm_ge
      B
      (L' := LevelTreeShortcutLanguage n)
      (L := LevelTreeLanguage n)
      (z := cleanLevelTreeWord n)
      n
  · exact cleanLevelTreeWord_length_rec n
  · intro w hw
    exact hw.1
  · exact levelTreeLanguage_diff_shortcut_eq_singleton n
  · exact hC
  · exact hCminus


/--
The concrete fixed-h/lower-bound package follows once the two Appendix
combinatorial obligations (literal admissibility and cut-locality) are
discharged.
-/
theorem levelTree_lowerBound_package_of_appendix_obligations
    (n : Nat)
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
    FixedHSubstitutable
        levelTreeTyping (LevelTreeLanguage n)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeShortcutLanguage n)
      ∧
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  exact
    levelTree_lowerBound_package_of_clarkEyraud
      n B
      (levelTree_clarkEyraud_of_admissible_cutLocal
        n hadm hlocal)
      hC hCminus


/--
Unconditional concrete lower-bound package for the level-coded tree family.
The Appendix substitutability lemma is discharged by the occurrence and
cut-locality formalization.
-/
theorem levelTree_lowerBound_package
    (n : Nat)
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
    FixedHSubstitutable
        levelTreeTyping (LevelTreeLanguage n)
      ∧
    FixedHSubstitutable
        levelTreeTyping (LevelTreeShortcutLanguage n)
      ∧
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  exact
    levelTree_lowerBound_package_of_clarkEyraud
      n B (levelTree_clarkEyraud n)
      hC hCminus

end TCS1
end LeanCfgProject
