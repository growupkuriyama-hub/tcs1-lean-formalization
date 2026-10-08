import LeanCfgProject.TCS1.V128SubstringUnaryRuleTable

/-!
# TCS #1 v128: literal finite rule sets (B), (L), (S), and epsilon

This is the *semantic finite-table* step following the verified bucket-based
(U) table in V128SubstringUnaryRuleTable. The nonterminal carrier is the
genuine finite observed-factor type, with one state per distinct nonempty
observed factor. Each table is filtered from a finite universe, and its
membership is proved equivalent to the precise v116 rule.

IMPORTANT: enumerating all observed-state triples for (B) is not the
three-cut O(n_K^3) algorithm. This module deliberately does NOT claim
that this direct finite-universe filter can be built in quartic time.
The next separate delta must replace the broad (B) enumeration with
split-slot indexing and prove its cubic candidate bound.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section RemainingV116Rules

variable {α : Type u} {M : Type v}
variable [Fintype α] [DecidableEq α] [Monoid M] [Fintype M]

/-- A typed row of the literal finite v116 binary-production table. -/
abbrev V116BinaryEntry (K : Finset (Word α)) :=
  ObservedSubstringNonterminal K ×
    (ObservedSubstringNonterminal K × ObservedSubstringNonterminal K)

/-- One concrete finite (B) rule table, with the exact v116 predicate.
    This is a set of *rules*, not yet an efficient list emitter. -/
noncomputable def v116BinaryRuleTable
    (K : Finset (Word α)) : Finset (V116BinaryEntry K) := by
  classical
  exact Finset.univ.filter
    (fun e => e.1.1 = e.2.1.1 ++ e.2.2.1)

/-- Exact membership for the (B) table and the finite v116 CFG. -/
theorem v116BinaryRuleTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B C : ObservedSubstringNonterminal K) :
    (A, (B, C)) ∈ v116BinaryRuleTable K ↔
      (finiteSubstringGrammar H K).binaryRule A B C := by
  classical
  change (A, (B, C)) ∈ v116BinaryRuleTable K ↔
    A.1 = B.1 ++ C.1
  simp [v116BinaryRuleTable]

/-- Literal (L) productions are the finite observed-state/letter pairs. -/
noncomputable def v116LexicalRuleTable
    (K : Finset (Word α)) :
    Finset (ObservedSubstringNonterminal K × α) := by
  classical
  exact Finset.univ.filter (fun e => e.1.1 = [e.2])

/-- The lexical table is sound and complete for the finite v116 CFG. -/
theorem v116LexicalRuleTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) (a : α) :
    (A, a) ∈ v116LexicalRuleTable K ↔
      (finiteSubstringGrammar H K).terminalRule A a := by
  classical
  change (A, a) ∈ v116LexicalRuleTable K ↔ A.1 = [a]
  simp [v116LexicalRuleTable]

/-- The sample-word start-entry rules, one per observed positive word. -/
noncomputable def v116StartRuleTable
    (K : Finset (Word α)) :
    Finset (ObservedSubstringNonterminal K) := by
  classical
  exact Finset.univ.filter (fun A => A.1 ∈ K)

/-- The (S) table contains exactly the positive sample start states. -/
theorem v116StartRuleTable_iff
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) :
    A ∈ v116StartRuleTable K ↔ A.1 ∈ K := by
  classical
  simp [v116StartRuleTable]

/-- The exceptional epsilon start production is present iff epsilon
    belongs to the sample. No non-start state receives an epsilon rule. -/
noncomputable def v116EpsilonStartTable
    (K : Finset (Word α)) : Finset Unit := by
  classical
  exact Finset.univ.filter (fun _ => ([] : Word α) ∈ K)

/-- Exact epsilon start-rule test. -/
theorem v116EpsilonStartTable_iff
    (K : Finset (Word α)) :
    () ∈ v116EpsilonStartTable K ↔ ([] : Word α) ∈ K := by
  classical
  simp [v116EpsilonStartTable]

/-- No ordinary observed-factor nonterminal has an epsilon rule. -/
theorem v116NonstartEpsilonRule_false
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) :
    ¬ (finiteSubstringGrammar H K).epsilonRule A := by
  simp [finiteSubstringGrammar]

/-- The assembled finite-rule predicates are exactly those from v116;
    in particular (U) is the separately verified cubic table. -/
theorem v116FourRuleTables_exact
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B C : ObservedSubstringNonterminal K)
    (a : α) :
    ((A, (B, C)) ∈ v116BinaryRuleTable K ↔
      (finiteSubstringGrammar H K).binaryRule A B C) ∧
    ((A.1, B.1) ∈ v116UnaryRuleTable H K ↔
      (finiteSubstringGrammar H K).unitRule A B) ∧
    ((A, a) ∈ v116LexicalRuleTable K ↔
      (finiteSubstringGrammar H K).terminalRule A a) ∧
    (A ∈ v116StartRuleTable K ↔ A.1 ∈ K) := by
  exact ⟨v116BinaryRuleTable_iff H K A B C,
    v116UnaryRuleTable_iff H K A B,
    v116LexicalRuleTable_iff H K A a,
    v116StartRuleTable_iff K A⟩

end RemainingV116Rules

end TCS1
end LeanCfgProject
