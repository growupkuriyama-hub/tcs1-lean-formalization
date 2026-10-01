import LeanCfgProject.TCS1.V83LevelCodedDisplayedThickness
import LeanCfgProject.TCS1.V83LevelCodedIndexedGrammarBridge

/-!
# TCS #1 v83: indexed ordinary-thickness witnesses

This module transports the direct n+5 productive witnesses of the displayed
grammars to the actual finite indexed CFG presentations.
-/

namespace LeanCfgProject
namespace TCS1

/-- Ordinary-thickness witness condition for a finite indexed mixed CFG. -/
def IndexedOrdinaryThicknessBound
    {N α P : Type}
    (G : IndexedMixedCFG N α P)
    (start : N)
    (tau : Nat) : Prop :=
  ∀ A : N, A ≠ start →
    ∃ w : Word α,
      MixedDerives G.toMixedRules A w ∧
      w.length ≤ tau

/-- The concrete indexed grammar R_n has ordinary thickness at most n+5. -/
theorem levelCodeRIndexed_ordinaryThickness_le
    (n : Nat) :
    IndexedOrdinaryThicknessBound
      (levelCodeRIndexedGrammar n)
      LevelCodeRNT.start
      (n + 5) := by
  intro A hA
  cases A with
  | start =>
      exact False.elim (hA rfl)
  | z i =>
      obtain ⟨w, hd, hlen⟩ :=
        levelCodeZDerives_short_witness i.1
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeZDerives_to_indexed
            hd
            (show i.1 ≤ n by omega)
      · rw [hlen]
        omega
  | a i =>
      obtain ⟨w, hd, hlen⟩ :=
        levelCodeADerives_shortcut_witness i.1
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeADerives_to_indexed
            hd
            (show i.1 ≤ n by omega)
      · exact le_trans hlen (by omega)

/--
For n=m+1, the concrete indexed grammar R_n^- has ordinary thickness at most
n+5 = m+6.
-/
theorem levelCodeRMinusIndexed_ordinaryThickness_le
    (m : Nat) :
    IndexedOrdinaryThicknessBound
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start
      (m + 6) := by
  intro A hA
  cases A with
  | start =>
      exact False.elim (hA rfl)
  | z i =>
      obtain ⟨w, hd, hlen⟩ :=
        levelCodeZDerives_short_witness i.1
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeZDerives_to_minusIndexed
            hd
            (show i.1 ≤ m + 1 by omega)
      · rw [hlen]
        omega
  | a i =>
      obtain ⟨w, hd, hlen⟩ :=
        levelCodeADerives_shortcut_witness i.1
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeADerives_to_minusIndexed
            hd
            (show i.1 ≤ m by omega)
      · exact le_trans hlen (by omega)
  | am i =>
      obtain ⟨w, hd, hlen⟩ :=
        levelCodeAMinusDerives_shortcut_witness i.1
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeAMinusDerives_to_minusIndexed
            hd
            (show i.1 ≤ m + 1 by omega)
      · exact le_trans hlen (by omega)

end TCS1
end LeanCfgProject
