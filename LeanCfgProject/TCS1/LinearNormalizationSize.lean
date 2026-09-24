import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# TCS #1: size arithmetic for linear-spine normalization

This module formalizes the counting part of Proposition
(linear-spine SSBNF normalization) after the standard preprocessing described
in the appendix.

A prepared non-start linear production is either

* a nonempty terminal word; or
* u B v with exactly one nonterminal B and at least one surrounding terminal,
  so the forbidden unit case u=v=epsilon is absent.

The appendix expansion uses one fresh terminal wrapper per terminal symbol
(shared globally) and at most one fresh spine state per terminal occurrence of
a production.  The number of generated rules is also at most the source
right-hand-side length.

We encode those counts exactly and prove that the normalized state and rule
spaces are linear in the prepared indexed representation.  Language
preservation and the syntactic linear-spine shape are kept in separate
semantic/construction modules.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearNormalizationSize

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- A linear non-start RHS after epsilon/unit preprocessing. -/
inductive PreparedLinearRhs
    (N : Type u)
    (α : Type v)
  | terminals
      (head : α)
      (tail : List α)
  | around
      (left : List α)
      (core : N)
      (right : List α)
      (nonunit : left ≠ [] ∨ right ≠ [])

/-- Number of terminal occurrences in a prepared linear RHS. -/
def PreparedLinearRhs.terminalCount :
    PreparedLinearRhs N α → Nat
  | .terminals _ tail =>
      tail.length + 1
  | .around left _ right _ =>
      left.length + right.length

/-- Mixed-symbol length of the source RHS. -/
def PreparedLinearRhs.sourceLength :
    PreparedLinearRhs N α → Nat
  | .terminals _ tail =>
      tail.length + 1
  | .around left _ right _ =>
      left.length + right.length + 1

/--
Fresh non-wrapper chain states used by the appendix factorization.

For q terminal occurrences, both the terminal-only and u B v constructions
need at most q-1 fresh chain states.
-/
def PreparedLinearRhs.auxCount
    (r : PreparedLinearRhs N α) : Nat :=
  r.terminalCount - 1

/-- Number of binary rules contributed by one factorized source production. -/
def PreparedLinearRhs.binaryCount :
    PreparedLinearRhs N α → Nat
  | .terminals _ tail =>
      tail.length
  | .around left _ right _ =>
      left.length + right.length

/--
Terminal-only factorizations end in one terminal rule; u B v factorizations
end at the existing core nonterminal and need no additional non-wrapper
terminal rule.
-/
def PreparedLinearRhs.localTerminalCount :
    PreparedLinearRhs N α → Nat
  | .terminals _ _ => 1
  | .around _ _ _ _ => 0

/-- Total number of non-wrapper rules generated for one prepared production. -/
def PreparedLinearRhs.expansionRuleCount
    (r : PreparedLinearRhs N α) : Nat :=
  r.binaryCount + r.localTerminalCount

/-- Prepared RHSs always contain at least one terminal occurrence. -/
theorem PreparedLinearRhs.terminalCount_pos
    (r : PreparedLinearRhs N α) :
    0 < r.terminalCount := by
  cases r with
  | terminals head tail =>
      simp [PreparedLinearRhs.terminalCount]
  | around left core right hnonunit =>
      simp only [PreparedLinearRhs.terminalCount]
      rcases hnonunit with hleft | hright
      · have : 0 < left.length := by
          cases left with
          | nil =>
              exact False.elim (hleft rfl)
          | cons a rest =>
              simp
        omega
      · have : 0 < right.length := by
          cases right with
          | nil =>
              exact False.elim (hright rfl)
          | cons a rest =>
              simp
        omega

/-- Fresh chain states are bounded by the source RHS length. -/
theorem PreparedLinearRhs.auxCount_le_sourceLength
    (r : PreparedLinearRhs N α) :
    r.auxCount ≤ r.sourceLength := by
  unfold PreparedLinearRhs.auxCount
  cases r with
  | terminals head tail =>
      simp [PreparedLinearRhs.terminalCount,
        PreparedLinearRhs.sourceLength]
  | around left core right hnonunit =>
      simp only [PreparedLinearRhs.terminalCount,
        PreparedLinearRhs.sourceLength]
      omega

/-- The appendix factorization uses no more rules than source RHS symbols. -/
theorem PreparedLinearRhs.expansionRuleCount_le_sourceLength
    (r : PreparedLinearRhs N α) :
    r.expansionRuleCount ≤ r.sourceLength := by
  cases r with
  | terminals head tail =>
      simp [PreparedLinearRhs.expansionRuleCount,
        PreparedLinearRhs.binaryCount,
        PreparedLinearRhs.localTerminalCount,
        PreparedLinearRhs.sourceLength]
  | around left core right hnonunit =>
      simp [PreparedLinearRhs.expansionRuleCount,
        PreparedLinearRhs.binaryCount,
        PreparedLinearRhs.localTerminalCount,
        PreparedLinearRhs.sourceLength]

/-- Finite indexed presentation of a prepared linear grammar fragment. -/
structure PreparedLinearIndexedCFG
    (N : Type u)
    (α : Type v)
    (P : Type w) where
  lhs : P → N
  rhs : P → PreparedLinearRhs N α

/-- Total prepared RHS length. -/
def PreparedLinearIndexedCFG.totalSourceLength
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) : Nat :=
  ∑ p : P, (G.rhs p).sourceLength

/-- Total fresh non-wrapper chain-state count. -/
def PreparedLinearIndexedCFG.totalAuxCount
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) : Nat :=
  ∑ p : P, (G.rhs p).auxCount

/-- Total number of per-production expansion rules. -/
def PreparedLinearIndexedCFG.totalExpansionRuleCount
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) : Nat :=
  ∑ p : P, (G.rhs p).expansionRuleCount

/-- Summing the pointwise auxiliary-state bound preserves linearity. -/
theorem preparedLinear_totalAuxCount_le_totalSourceLength
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    G.totalAuxCount ≤ G.totalSourceLength := by
  classical
  unfold PreparedLinearIndexedCFG.totalAuxCount
  unfold PreparedLinearIndexedCFG.totalSourceLength
  apply Finset.sum_le_sum
  intro p hp
  exact PreparedLinearRhs.auxCount_le_sourceLength (G.rhs p)

/-- Summing the pointwise rule bound preserves linearity. -/
theorem preparedLinear_totalExpansionRuleCount_le_totalSourceLength
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    G.totalExpansionRuleCount ≤ G.totalSourceLength := by
  classical
  unfold PreparedLinearIndexedCFG.totalExpansionRuleCount
  unfold PreparedLinearIndexedCFG.totalSourceLength
  apply Finset.sum_le_sum
  intro p hp
  exact
    PreparedLinearRhs.expansionRuleCount_le_sourceLength
      (G.rhs p)

/--
Fresh chain-state indices, with exactly auxCount(p) slots for each source
production.
-/
abbrev LinearAuxStateIndex
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :=
  Sigma (fun p : P => Fin (G.rhs p).auxCount)

/-- The auxiliary index type has exactly the summed auxiliary count. -/
@[simp] theorem linearAuxStateIndex_card
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearAuxStateIndex G) =
      G.totalAuxCount := by
  classical
  simp [LinearAuxStateIndex,
    PreparedLinearIndexedCFG.totalAuxCount]

/--
A generous normalized non-start state universe: original symbols, one shared
terminal-wrapper symbol per alphabet symbol, and all per-production chain
states.
-/
abbrev LinearNormalizedStateIndex
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :=
  N ⊕ (α ⊕ LinearAuxStateIndex G)

/-- Exact cardinality of the generous normalized state universe. -/
@[simp] theorem linearNormalizedStateIndex_card
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearNormalizedStateIndex G) =
      Fintype.card N + Fintype.card α + G.totalAuxCount := by
  rw [Fintype.card_sum, Fintype.card_sum]
  rw [linearAuxStateIndex_card G]
  omega

/-- Normalized non-start states are linear in the prepared representation. -/
theorem linearNormalizedStateIndex_card_le
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearNormalizedStateIndex G) ≤
      Fintype.card N + Fintype.card α +
        G.totalSourceLength := by
  rw [linearNormalizedStateIndex_card]
  exact Nat.add_le_add_left
    (preparedLinear_totalAuxCount_le_totalSourceLength G)
    (Fintype.card N + Fintype.card α)

/--
The normalized non-start rule count is bounded by the shared wrapper terminal
rules plus the per-production factorization rules.
-/
def linearNormalizedRuleCountEnvelope
    [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) : Nat :=
  Fintype.card α + G.totalExpansionRuleCount

theorem linearNormalizedRuleCountEnvelope_le
    [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    linearNormalizedRuleCountEnvelope G ≤
      Fintype.card α + G.totalSourceLength := by
  unfold linearNormalizedRuleCountEnvelope
  exact Nat.add_le_add_left
    (preparedLinear_totalExpansionRuleCount_le_totalSourceLength G)
    (Fintype.card α)

/-- Natural encoding scale for a prepared indexed linear grammar. -/
def PreparedLinearIndexedCFG.encodingScale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) : Nat :=
  Fintype.card N +
    Fintype.card α +
    Fintype.card P +
    G.totalSourceLength

/-- State cardinality is bounded by the prepared encoding scale. -/
theorem linearNormalizedStateIndex_card_le_scale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearNormalizedStateIndex G) ≤
      G.encodingScale := by
  have h :=
    linearNormalizedStateIndex_card_le G
  unfold PreparedLinearIndexedCFG.encodingScale
  omega

/-- The generous non-start rule-count envelope is also bounded by the scale. -/
theorem linearNormalizedRuleCountEnvelope_le_scale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    linearNormalizedRuleCountEnvelope G ≤
      G.encodingScale := by
  have h :=
    linearNormalizedRuleCountEnvelope_le G
  unfold PreparedLinearIndexedCFG.encodingScale
  omega

/--
Combined state-plus-rule size is at most twice the prepared encoding scale.
This is the explicit linear-size kernel underlying the polynomial
P_lin after the standard preprocessing stage.
-/
theorem linearNormalization_combined_size_le_twice_scale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearNormalizedStateIndex G) +
        linearNormalizedRuleCountEnvelope G
      ≤
    2 * G.encodingScale := by
  have hs :=
    linearNormalizedStateIndex_card_le_scale G
  have hr :=
    linearNormalizedRuleCountEnvelope_le_scale G
  omega

end LinearNormalizationSize

end TCS1
end LeanCfgProject
