import LeanCfgProject.TCS1.V83LevelCodedIndexedReducedness
import LeanCfgProject.TCS1.FiniteCFGEncoding
import Mathlib.Data.Fintype.Card

/-!
# TCS #1 v83: exact finite-presentation size of the compact grammars

This module closes the representation-size bookkeeping for the two concrete
indexed grammars used in the ordinary-thickness lower bound. The formulas
count nonterminals, productions, and right-hand-side symbol occurrences in the
actual finite indexed CFG objects.
-/

namespace LeanCfgProject
namespace TCS1

/-- Exact number of nonterminals in R_n. -/
theorem levelCodeRNT_card
    (n : Nat) :
    Fintype.card (LevelCodeRNT n) =
      2 * n + 3 := by
  simp
  omega

/-- Exact number of productions in R_n. -/
theorem levelCodeRProd_card
    (n : Nat) :
    Fintype.card (LevelCodeRProd n) =
      3 * n + 4 := by
  simp
  omega

/-- Exact total right-hand-side symbol count in R_n. -/
theorem levelCodeRIndexed_totalRhsLength
    (n : Nat) :
    (levelCodeRIndexedGrammar n).totalRhsLength =
      11 * n + 10 := by
  simp [IndexedMixedCFG.totalRhsLength,
    levelCodeRIndexedGrammar]
  omega

/-- Exact indexed encoding scale of R_n. -/
theorem levelCodeRIndexed_encodingScale
    (n : Nat) :
    (levelCodeRIndexedGrammar n).encodingScale =
      16 * n + 17 := by
  unfold IndexedMixedCFG.encodingScale
  rw [levelCodeRNT_card,
    levelCodeRProd_card,
    levelCodeRIndexed_totalRhsLength]
  omega

/-- Exact number of nonterminals in R_(m+1)^-. -/
theorem levelCodeRMinusNT_card
    (m : Nat) :
    Fintype.card (LevelCodeRMinusNT m) =
      3 * m + 6 := by
  simp
  omega

/-- Exact number of productions in R_(m+1)^-. -/
theorem levelCodeRMinusProd_card
    (m : Nat) :
    Fintype.card (LevelCodeRMinusProd m) =
      6 * m + 9 := by
  simp
  omega

/-- Exact total right-hand-side symbol count in R_(m+1)^-. -/
theorem levelCodeRMinusIndexed_totalRhsLength
    (m : Nat) :
    (levelCodeRMinusIndexedGrammar m).totalRhsLength =
      24 * m + 30 := by
  simp [IndexedMixedCFG.totalRhsLength,
    levelCodeRMinusIndexedGrammar]
  omega

/-- Exact indexed encoding scale of R_(m+1)^-. -/
theorem levelCodeRMinusIndexed_encodingScale
    (m : Nat) :
    (levelCodeRMinusIndexedGrammar m).encodingScale =
      33 * m + 45 := by
  unfold IndexedMixedCFG.encodingScale
  rw [levelCodeRMinusNT_card,
    levelCodeRMinusProd_card,
    levelCodeRMinusIndexed_totalRhsLength]
  omega

/--
Both concrete indexed encodings are linear in the manuscript level parameter.
Here the second grammar is R_(m+1)^-.
-/
theorem levelCodeIndexed_encodingScale_joint_linear
    (m : Nat) :
    (levelCodeRIndexedGrammar (m + 1)).encodingScale +
        (levelCodeRMinusIndexedGrammar m).encodingScale
      ≤ 49 * (m + 1) + 61 := by
  rw [levelCodeRIndexed_encodingScale,
    levelCodeRMinusIndexed_encodingScale]
  omega

end TCS1
end LeanCfgProject
