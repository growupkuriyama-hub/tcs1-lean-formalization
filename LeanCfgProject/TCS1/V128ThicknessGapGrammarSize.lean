import LeanCfgProject.TCS1.V128ThicknessGapRuleEnumeration

/-!
# TCS #1 v128: linear *symbol-occurrence* size of the enumerated gap CFG

The production list is the concrete sound-and-complete enumeration from
V128ThicknessGapRuleEnumeration, not merely a stipulated rule count.

Each start or terminal production has two grammar-symbol occurrences,
each binary production four (left side + three right-side occurrences).
With seven fixed productions and two indexed productions for each 1<=i<=n,
the total production symbol count is at most 4(2n+7).

There are n+3 source non-start symbols (U,D,E_0,...,E_n),
one start symbol S_0 and two terminal letters (a,c).
Adding these to production occurrences gives an explicit
34(n+1) linear size envelope, under the standard convention that each
E_i is an atomic grammar symbol, rather than a binary-printed index.
-/

namespace LeanCfgProject
namespace TCS1

/-- Count symbol occurrences of an actual decoded production:
    lhs+rhs = 2 for start/terminal and 4 for a binary rule. -/
def gapRuleDatumSymbolCost {n : Nat} : GapRuleDatum n → Nat
  | .start _ => 2
  | .terminal _ _ => 2
  | .binary _ _ _ => 4

/-- Each actual source production has at most four symbols. -/
theorem gapRuleCode_symbolCost_le_four (n : Nat)
    (c : GapRuleCode n) :
    gapRuleDatumSymbolCost (gapRuleDecode n c) ≤ 4 := by
  cases c <;> simp [gapRuleDatumSymbolCost, gapRuleDecode]

/-- Number of symbol occurrences in the *decoded finite production list*. -/
def gapRuleListSymbolCost (n : Nat) : Nat :=
  ((gapRuleCodeEnumeration n).map
    (fun c => gapRuleDatumSymbolCost (gapRuleDecode n c))).sum

/-- An elementary per-production length bound for any list of source codes. -/
private theorem gapRuleList_cost_le_four (n : Nat)
    (xs : List (GapRuleCode n)) :
    (xs.map
      (fun c => gapRuleDatumSymbolCost (gapRuleDecode n c))).sum ≤
      4 * xs.length := by
  induction xs with
  | nil =>
      simp
  | cons c rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hc := gapRuleCode_symbolCost_le_four n c
      omega

/-- Source-production symbol count is explicitly O(n). -/
theorem gapRuleListSymbolCost_linear (n : Nat) :
    gapRuleListSymbolCost n ≤ 4 * (2 * n + 7) := by
  unfold gapRuleListSymbolCost
  calc
    ((gapRuleCodeEnumeration n).map
        (fun c => gapRuleDatumSymbolCost (gapRuleDecode n c))).sum
        ≤ 4 * (gapRuleCodeEnumeration n).length :=
      gapRuleList_cost_le_four n (gapRuleCodeEnumeration n)
    _ = 4 * (2 * n + 7) := by
      rw [gapRuleCodeEnumeration_length]

/-- Complete grammar-size budget: production occurrences, distinct
    terminals, and distinct start/non-start symbols. -/
def gapSourceGrammarSymbolBudget (n : Nat) : Nat :=
  gapRuleListSymbolCost n + (n + 4) + 2

/-- Explicit polynomial size certificate, in fact linear in n. -/
theorem gapSourceGrammarSymbolBudget_linear (n : Nat) :
    gapSourceGrammarSymbolBudget n ≤ 34 * (n + 1) := by
  have hproductions := gapRuleListSymbolCost_linear n
  unfold gapSourceGrammarSymbolBudget
  omega

end TCS1
end LeanCfgProject
