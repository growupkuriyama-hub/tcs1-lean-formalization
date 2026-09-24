import LeanCfgProject.TCS1.LinearNormalizationPlan

/-!
# TCS #1: semantics of prepared indexed linear grammars

This module gives the preprocessing output used by the linear-normalization
appendix an explicit generated-language semantics.

A prepared production is either a nonempty terminal word or u B v with one
nonterminal.  The inductive derivation relation below is exactly the ordinary
linear-CFG derivation relation for those two forms.  We also give the
intersection-of-closed-families presentation and prove it equivalent to the
inductive one.

Finally, the source closure condition is rewritten through the exact spine
plans from LinearNormalizationPlan.  This is the semantic interface used by
the concrete terminal/binary rule construction.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section PreparedLinearGrammarSemantics

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Derivations in the prepared non-start linear grammar. -/
inductive PreparedLinearDerives
    (G : PreparedLinearIndexedCFG N α P) :
    N → List α → Prop
  | terminals
      (p : P)
      (head : α)
      (tail : List α)
      (hrhs :
        G.rhs p =
          PreparedLinearRhs.terminals head tail) :
      PreparedLinearDerives G
        (G.lhs p) (head :: tail)
  | around
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hrhs :
        G.rhs p =
          PreparedLinearRhs.around
            left core right hnonunit)
      {word : List α}
      (child :
        PreparedLinearDerives G core word) :
      PreparedLinearDerives G
        (G.lhs p) (left ++ word ++ right)

/-- Generated language of one prepared nonterminal. -/
def PreparedLinearLanguage
    (G : PreparedLinearIndexedCFG N α P)
    (A : N) :
    Set (List α) :=
  {word | PreparedLinearDerives G A word}

/--
A family of terminal-word languages is closed under every prepared source
production.
-/
def PreparedLinearGrammarClosed
    (G : PreparedLinearIndexedCFG N α P)
    (L : N → Set (List α)) : Prop :=
  ∀ p : P, ∀ word : List α,
    PreparedLinearRhs.realizes L (G.rhs p) word →
    word ∈ L (G.lhs p)

/-- Least closed language family of the prepared grammar. -/
def PreparedLinearLeastLanguage
    (G : PreparedLinearIndexedCFG N α P)
    (A : N) :
    Set (List α) :=
  {word |
    ∀ L : N → Set (List α),
      PreparedLinearGrammarClosed G L →
      word ∈ L A}

/-- The inductively generated language is closed under every source rule. -/
theorem preparedLinearLanguage_closed
    (G : PreparedLinearIndexedCFG N α P) :
    PreparedLinearGrammarClosed G
      (PreparedLinearLanguage G) := by
  intro p word hreal
  cases hRhs : G.rhs p with
  | terminals head tail =>
      rw [hRhs] at hreal
      change word = head :: tail at hreal
      rw [hreal]
      exact
        PreparedLinearDerives.terminals
          p head tail hRhs
  | around left core right hnonunit =>
      rw [hRhs] at hreal
      change ∃ z,
        PreparedLinearDerives G core z ∧
        word = left ++ z ++ right at hreal
      rcases hreal with ⟨z, hz, rfl⟩
      exact
        PreparedLinearDerives.around
          p left core right hnonunit
          hRhs hz

/-- Every prepared derivation belongs to every closed language family. -/
theorem preparedLinearDerives_mem_of_closed
    (G : PreparedLinearIndexedCFG N α P)
    (L : N → Set (List α))
    (hclosed :
      PreparedLinearGrammarClosed G L)
    {A : N}
    {word : List α}
    (d : PreparedLinearDerives G A word) :
    word ∈ L A := by
  induction d with
  | terminals p head tail hrhs =>
      apply hclosed p (head :: tail)
      rw [hrhs]
      rfl
  | @around p left core right hnonunit hrhs word child ih =>
      apply hclosed p (left ++ word ++ right)
      rw [hrhs]
      exact ⟨word, ih, rfl⟩

/--
Inductive derivability is exactly membership in the least closed prepared
language.
-/
theorem preparedLinearDerives_iff_leastLanguage
    (G : PreparedLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    PreparedLinearDerives G A word
      ↔
    word ∈ PreparedLinearLeastLanguage G A := by
  constructor
  · intro d L hclosed
    exact
      preparedLinearDerives_mem_of_closed
        G L hclosed d
  · intro hleast
    exact
      hleast
        (PreparedLinearLanguage G)
        (preparedLinearLanguage_closed G)

/--
Closure rewritten through the exact spine-plan semantics.  This statement is
definitionally the same grammar step, with
preparedLinearRhs_realizes_iff_plan providing the local normalization
equivalence.
-/
def PreparedLinearPlanClosed
    (G : PreparedLinearIndexedCFG N α P)
    (L : N → Set (List α)) : Prop :=
  ∀ p : P, ∀ word : List α,
    PreparedLinearPlan.realizes L
      (G.rhs p).toPlan word →
    word ∈ L (G.lhs p)

theorem preparedLinearGrammarClosed_iff_planClosed
    (G : PreparedLinearIndexedCFG N α P)
    (L : N → Set (List α)) :
    PreparedLinearGrammarClosed G L
      ↔
    PreparedLinearPlanClosed G L := by
  constructor
  · intro hclosed p word hplan
    apply hclosed p word
    exact
      (preparedLinearRhs_realizes_iff_plan
        L (G.rhs p) word).2 hplan
  · intro hclosed p word hsource
    apply hclosed p word
    exact
      (preparedLinearRhs_realizes_iff_plan
        L (G.rhs p) word).1 hsource

end PreparedLinearGrammarSemantics

end TCS1
end LeanCfgProject
