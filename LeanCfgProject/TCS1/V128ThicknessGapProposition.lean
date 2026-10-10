import LeanCfgProject.TCS1.V128ThicknessGapGrammarSize

/-!
# TCS #1 v128: consolidated exponential typed-thickness gap proposition

This module packages the individual checked components of the manuscript's
Proposition `prop:typed-thickness-gap` into one theorem about the SAME
explicit finite indexed source grammar G_n and the SAME fixed h_c typing.

It asserts:
(1) the exact start language {a,c}^+;
(2) source reducedness (all non-start symbols reachable and productive);
(3) source ordinary shortest-yield thickness exactly 1;
(4) EVERY uniform shortest-yield bound for the concretely trimmed
    h_c-typed grammar is at least 2^n;
(5) an explicit grammar symbol-occurrence budget <= 34(n+1),
    using the decoded complete source rule enumeration.

The statement uses the repository's `YieldBound` interface, not a
new abstract thickness assumption. The binary encoded length of written
nonterminal indices is not counted; E_i are atomic grammar symbols.
It does not certify all other v128 theorems.
-/

namespace LeanCfgProject
namespace TCS1

/-- Single exact-instance certificate for the exponential source-to-typed
    thickness separation in the v128 paper. -/
theorem v128_exponential_typed_thickness_gap_package (n : Nat) :
    (UntypedStartLanguage (GapTerminalRule n) (GapBinaryRule n)
        (GapStartRule n) False =
      {w : List Bool | w ≠ []}) ∧
    (∀ A : GapNonterminal n,
      GapSourceReachable n A ∧
        ∃ w : List Bool,
          UntypedDerives (GapTerminalRule n) (GapBinaryRule n) A w) ∧
    (YieldBound (gapSourceYieldLanguage n) 1 ∧
      ∀ bound : Nat,
        YieldBound (gapSourceYieldLanguage n) bound →
        1 ≤ bound) ∧
    (∀ bound : Nat,
      YieldBound (gapRetainedTypedYieldLanguage n) bound →
      2 ^ n ≤ bound) ∧
    (gapSourceGrammarSymbolBudget n ≤ 34 * (n + 1)) := by
  refine ⟨gapSource_startLanguage_eq_nonempty n,
    gapSource_reduced n, ?_, ?_, gapSourceGrammarSymbolBudget_linear n⟩
  · exact gapSource_ordinary_thickness_exact_one n
  · intro bound hb
    exact gapRetained_typed_YieldBound_ge_exponential n bound hb

/-- The numerical contrast uses a *fixed* typing, and its source
    presentation has uniformly linear size as n grows. -/
theorem v128_exponential_gap_explicit_bounds (n : Nat) :
    YieldBound (gapSourceYieldLanguage n) 1 ∧
    (∀ τ : Nat,
      YieldBound (gapRetainedTypedYieldLanguage n) τ →
      2 ^ n ≤ τ) ∧
    (gapRuleCodeEnumeration n).length = 2 * n + 7 ∧
    gapSourceGrammarSymbolBudget n ≤ 34 * (n + 1) := by
  exact ⟨gapSource_YieldBound_one n,
    (fun τ hτ => gapRetained_typed_YieldBound_ge_exponential n τ hτ),
    gapRuleCodeEnumeration_length n,
    gapSourceGrammarSymbolBudget_linear n⟩

end TCS1
end LeanCfgProject
