import LeanCfgProject.TCS1.V128SubstringRemainingRuleTables

/-!
# TCS #1 v128: grammar semantics of all four materialized rule tables

The finite v116 presentation previously used semantic predicates for B/U/L.
The exact finite rule tables now supply those predicates by membership in
actual finsets (with a separate finite start table and an epsilon-start
flag). Derivation induction below proves language equivalence all the way
to the already checked v88 BatchLanguage for every finite sample K.

This is a noncomputable materialized finite grammar: the indexed tables
are not yet executable candidate writers with an O(n_K^4) time certificate.
In particular B currently uses a broad finite-state-triple filter.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V116TabulatedPresentation

variable {α : Type u} {M : Type v}
variable [Fintype α] [DecidableEq α] [Monoid M] [Fintype M]

/-- One ordinary finite-carrier CFG reading its B, U, L rules directly
    from the materialized finsets rather than their semantic predicates. -/
def v116TabulatedNonstartGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    BinaryNullableGrammar (ObservedSubstringNonterminal K) α where
  terminalRule A a := (A, a) ∈ v116LexicalRuleTable K
  binaryRule A B C := (A, (B, C)) ∈ v116BinaryRuleTable K
  epsilonRule _ := False
  unitRule A B := (A.1, B.1) ∈ v116UnaryRuleTable H K

/-- Every derivation using the finite tables is a semantic v116 derivation. -/
theorem v116TabulatedDerives_to_finiteCFG
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ObservedSubstringNonterminal K} {w : Word α}
    (d : BinaryNullableDerives (v116TabulatedNonstartGrammar H K) A w) :
    BinaryNullableDerives (finiteSubstringGrammar H K) A w := by
  induction d with
  | @terminal A a hterm =>
      exact BinaryNullableDerives.terminal
        ((v116LexicalRuleTable_iff H K A a).mp hterm)
  | epsilon heps =>
      exact False.elim heps
  | @unit A B w hunit _d ih =>
      exact BinaryNullableDerives.unit
        ((v116UnaryRuleTable_iff H K A B).mp hunit) ih
  | @binary A B C wB wC hbin _dB _dC ihB ihC =>
      exact BinaryNullableDerives.binary
        ((v116BinaryRuleTable_iff H K A B C).mp hbin) ihB ihC

/-- Every semantic v116 derivation is reproduced from the finite rule
    tables; no extra (B), (U) or (L) productions are assumed. -/
theorem finiteCFG_to_v116TabulatedDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ObservedSubstringNonterminal K} {w : Word α}
    (d : BinaryNullableDerives (finiteSubstringGrammar H K) A w) :
    BinaryNullableDerives (v116TabulatedNonstartGrammar H K) A w := by
  induction d with
  | @terminal A a hterm =>
      exact BinaryNullableDerives.terminal
        ((v116LexicalRuleTable_iff H K A a).mpr hterm)
  | epsilon heps =>
      exact False.elim heps
  | @unit A B w hunit _d ih =>
      exact BinaryNullableDerives.unit
        ((v116UnaryRuleTable_iff H K A B).mpr hunit) ih
  | @binary A B C wB wC hbin _dB _dC ihB ihC =>
      exact BinaryNullableDerives.binary
        ((v116BinaryRuleTable_iff H K A B C).mpr hbin) ihB ihC

/-- The non-start derivation relations coincide at every observed factor. -/
theorem v116TabulatedDerives_iff_finiteCFG
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) (w : Word α) :
    BinaryNullableDerives (v116TabulatedNonstartGrammar H K) A w ↔
      BinaryNullableDerives (finiteSubstringGrammar H K) A w := by
  exact ⟨v116TabulatedDerives_to_finiteCFG H K,
    finiteCFG_to_v116TabulatedDerives H K⟩

/-- The actual (S) and epsilon start tables applied to the materialized
    B/U/L grammar, including the empty-target and epsilon cases. -/
def v116TabulatedBatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Set (Word α) :=
  {w | (∃ A : ObservedSubstringNonterminal K,
    A ∈ v116StartRuleTable K ∧
    BinaryNullableDerives (v116TabulatedNonstartGrammar H K) A w) ∨
    (w = [] ∧ () ∈ v116EpsilonStartTable K)}

/-- Exact end-to-end *semantic* language equality for the finite
    B/U/L/S/epsilon tables, reusing the checked v116-v88 quotient. -/
theorem v116TabulatedBatchLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    v116TabulatedBatchLanguage H K = BatchLanguage H K := by
  have hsource :
      v116TabulatedBatchLanguage H K =
      finiteSubstringBatchLanguage H K := by
    ext w
    change
      ((∃ A : ObservedSubstringNonterminal K,
        A ∈ v116StartRuleTable K ∧
        BinaryNullableDerives (v116TabulatedNonstartGrammar H K) A w) ∨
        (w = [] ∧ () ∈ v116EpsilonStartTable K)) ↔
      ((∃ A : ObservedSubstringNonterminal K,
        A.1 ∈ K ∧
        BinaryNullableDerives (finiteSubstringGrammar H K) A w) ∨
        (w = [] ∧ ([] : Word α) ∈ K))
    constructor
    · rintro (⟨A, hs, hd⟩ | ⟨hw, heps⟩)
      · exact Or.inl ⟨A,
          (v116StartRuleTable_iff K A).mp hs,
          v116TabulatedDerives_to_finiteCFG H K hd⟩
      · exact Or.inr ⟨hw, (v116EpsilonStartTable_iff K).mp heps⟩
    · rintro (⟨A, hs, hd⟩ | ⟨hw, heps⟩)
      · exact Or.inl ⟨A,
          (v116StartRuleTable_iff K A).mpr hs,
          finiteCFG_to_v116TabulatedDerives H K hd⟩
      · exact Or.inr ⟨hw, (v116EpsilonStartTable_iff K).mpr heps⟩
  exact hsource.trans (finiteSubstringBatchLanguage_eq_batchLanguage H K)

end V116TabulatedPresentation

end TCS1
end LeanCfgProject
