import LeanCfgProject.TCS1.V83LevelCodedDisplayedGrammar

/-!
# TCS #1 v83: direct ordinary-thickness witnesses for R_n and R_n^-

The manuscript bounds ordinary grammar thickness by exhibiting one short
terminal yield for every non-start symbol of the two displayed grammar
families.  This module records exactly those witnesses at the direct
derivation level developed for the v83 displayed grammars.

The later indexed-CFG packaging only has to transport these already-verified
witnesses to the generic grammar representation.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Z_i has the canonical yield 0^(i+1). -/
theorem levelCodeZDerives_short_witness
    (i : Nat) :
    ∃ w : Word LevelTreeSymbol,
      LevelCodeZDerives i w ∧
      w.length = i + 1 := by
  refine ⟨List.replicate (i + 1) zero, ?_, ?_⟩
  · exact levelCodeZDerives_replicate i
  · simp

/--
All non-start symbols displayed in R_n have productive witnesses of length at
most n+5.
-/
theorem levelCodeR_displayed_thickness_bound
    (n : Nat) :
    (∀ i : Nat, i ≤ n →
      ∃ w : Word LevelTreeSymbol,
        LevelCodeZDerives i w ∧
        w.length ≤ n + 5) ∧
    (∀ i : Nat, i ≤ n →
      ∃ w : Word LevelTreeSymbol,
        LevelCodeADerives i w ∧
        w.length ≤ n + 5) := by
  constructor
  · intro i hi
    obtain ⟨w, hd, hlen⟩ :=
      levelCodeZDerives_short_witness i
    refine ⟨w, hd, ?_⟩
    rw [hlen]
    omega
  · intro i hi
    obtain ⟨w, hd, hlen⟩ :=
      levelCodeADerives_shortcut_witness i
    refine ⟨w, hd, ?_⟩
    exact le_trans hlen (by omega)

/--
For n>=1, the retained A_i symbols in R_n^- are exactly the ordinary A_i
with i<n, and they inherit the same short shortcut witnesses.
-/
theorem levelCodeRMinus_retainedA_thickness_bound
    (n : Nat) :
    ∀ i : Nat, i < n →
      ∃ w : Word LevelTreeSymbol,
        LevelCodeADerives i w ∧
        w.length ≤ n + 5 := by
  intro i hi
  obtain ⟨w, hd, hlen⟩ :=
    levelCodeADerives_shortcut_witness i
  refine ⟨w, hd, ?_⟩
  exact le_trans hlen (by omega)

/--
All A_i^- symbols displayed in R_n^- have productive witnesses of length at
most n+5.
-/
theorem levelCodeRMinus_minusA_thickness_bound
    (n : Nat) :
    ∀ i : Nat, i ≤ n →
      ∃ w : Word LevelTreeSymbol,
        LevelCodeAMinusDerives i w ∧
        w.length ≤ n + 5 := by
  intro i hi
  obtain ⟨w, hd, hlen⟩ :=
    levelCodeAMinusDerives_shortcut_witness i
  refine ⟨w, hd, ?_⟩
  exact le_trans hlen (by omega)

/--
Complete direct witness package for the non-start symbols of R_n^-.
-/
theorem levelCodeRMinus_displayed_thickness_bound
    (n : Nat) :
    (∀ i : Nat, i ≤ n →
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
        w.length ≤ n + 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨w, hd, hlen⟩ :=
      levelCodeZDerives_short_witness i
    refine ⟨w, hd, ?_⟩
    rw [hlen]
    omega
  · exact levelCodeRMinus_retainedA_thickness_bound n
  · exact levelCodeRMinus_minusA_thickness_bound n

/--
The two displayed production-symbol counts are jointly linear in n (for
n>=1), hence polynomial under the manuscript's fixed encoding convention.
-/
theorem levelCode_displayed_joint_symbolCount_linear
    (n : Nat) :
    levelCodeRProductionSymbolCount n +
        levelCodeRMinusProductionSymbolCount n
      ≤
    44 * (n + 1) + 9 := by
  unfold levelCodeRProductionSymbolCount
  unfold levelCodeRMinusProductionSymbolCount
  omega

end TCS1
end LeanCfgProject
