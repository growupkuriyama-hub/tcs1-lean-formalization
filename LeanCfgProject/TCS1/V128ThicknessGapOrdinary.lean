import LeanCfgProject.TCS1.V128ThicknessGapYieldBound

/-!
# TCS #1 v128: ordinary shortest-yield thickness of the gap grammar

The concrete finite SSBNF grammar G_n has ordinary thickness exactly 1,
even though the h_c-typed productive/reachable refinement needs an
exponential uniform yield envelope.

Every non-start symbol U, D and E_i has a one-letter terminal production:
for E_0 the letter is a, for every E_i with i>0 it is c.
Conversely, non-start binary/terminal derivations never yield epsilon,
so a uniform envelope for all nonterminals cannot be zero.

These statements use the same YieldBound notion that is used in
V128ThicknessGapYieldBound.lean for the trimmed typed language.
-/

namespace LeanCfgProject
namespace TCS1

/-- Full terminal-yield language for each source non-start symbol. -/
def gapSourceYieldLanguage (n : Nat) :
    NTLang (GapNonterminal n) Bool :=
  fun A => {w : List Bool |
    UntypedDerives (GapTerminalRule n) (GapBinaryRule n) A w}

/-- Every source non-start symbol derives a one-letter word. -/
theorem gapSource_all_short_yields (n : Nat) :
    ∀ A : GapNonterminal n,
      ∃ w : List Bool,
        UntypedDerives (GapTerminalRule n) (GapBinaryRule n) A w ∧
        w.length = 1 := by
  intro A
  cases A with
  | universal =>
      exact ⟨[false], UntypedDerives.terminal
        GapTerminalRule.universalA, by simp⟩
  | marker =>
      exact ⟨[true], UntypedDerives.terminal
        GapTerminalRule.markerC, by simp⟩
  | exponent i =>
      by_cases hi : i.val = 0
      · have heq : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hi
        rw [heq]
        exact ⟨[false], UntypedDerives.terminal
          GapTerminalRule.exponentA, by simp⟩
      · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
        exact ⟨[true], UntypedDerives.terminal
          (GapTerminalRule.exponentC (i := i) hpos), by simp⟩

/-- One is a uniform ordinary yield-length upper bound for G_n. -/
theorem gapSource_YieldBound_one (n : Nat) :
    YieldBound (gapSourceYieldLanguage n) 1 := by
  intro A
  obtain ⟨w, hd, hlen⟩ := gapSource_all_short_yields n A
  exact ⟨w, hd, Nat.le_of_eq hlen⟩

/-- A uniform ordinary yield bound cannot be zero, since all yields
    in a non-start SSBNF grammar are nonempty. -/
theorem gapSource_YieldBound_ge_one
    (n bound : Nat)
    (hb : YieldBound (gapSourceYieldLanguage n) bound) :
    1 ≤ bound := by
  obtain ⟨w, hd, hlen⟩ := hb GapNonterminal.universal
  have hpos : 0 < w.length :=
    untypedDerives_length_pos
      (GapTerminalRule n) (GapBinaryRule n) hd
  omega

/-- The ordinary shortest-yield thickness is exactly one, expressed
    without defining a separate ad hoc numerical thickness operator. -/
theorem gapSource_ordinary_thickness_exact_one (n : Nat) :
    YieldBound (gapSourceYieldLanguage n) 1 ∧
      ∀ bound : Nat,
        YieldBound (gapSourceYieldLanguage n) bound →
        1 ≤ bound := by
  exact ⟨gapSource_YieldBound_one n,
    fun bound hb => gapSource_YieldBound_ge_one n bound hb⟩

/-- Full contrast: the original grammar admits a uniform bound 1,
    but every uniform bound on the trimmed typed refinement is at least 2^n. -/
theorem gapSource_vs_typed_thickness_gap (n : Nat) :
    YieldBound (gapSourceYieldLanguage n) 1 ∧
      (∀ bound : Nat,
        YieldBound (gapRetainedTypedYieldLanguage n) bound →
        2 ^ n ≤ bound) := by
  exact ⟨gapSource_YieldBound_one n,
    fun bound hb => gapRetained_typed_YieldBound_ge_exponential n bound hb⟩

end TCS1
end LeanCfgProject
