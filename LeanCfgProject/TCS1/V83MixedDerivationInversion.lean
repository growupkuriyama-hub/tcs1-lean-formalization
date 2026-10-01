import LeanCfgProject.TCS1.GeneralCFGDerivation

/-!
# TCS #1 v83: small inversion lemmas for mixed derivations

These are shape lemmas for the finite displayed grammars used by the v83
ordinary-thickness lower bound.  They expose the child derivations and the
flattened terminal pieces of the right-hand-side forms occurring in R_n and
R_n^-.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

variable {N : Type u} {α : Type v}
variable {R : MixedRules N α}

/-- Invert a one-nonterminal right-hand side. -/
theorem mixedSymbolsDerive_unit_inv
    {A : N} {pieces : List (List α)}
    (h :
      MixedSymbolsDerive R
        [Sum.inl A] pieces) :
    ∃ w : List α,
      pieces = [w] ∧ MixedDerives R A w := by
  cases h with
  | nonterminal hd tail =>
      cases tail
      exact ⟨_, rfl, hd⟩

/-- Invert a nonterminal followed by one literal terminal. -/
theorem mixedSymbolsDerive_nonterminal_terminal_inv
    {A : N} {a : α}
    {pieces : List (List α)}
    (h :
      MixedSymbolsDerive R
        [Sum.inl A, Sum.inr a] pieces) :
    ∃ w : List α,
      pieces = [w, [a]] ∧
      MixedDerives R A w := by
  cases h with
  | nonterminal hd tail =>
      cases tail with
      | terminal tail' =>
          cases tail'
          exact ⟨_, rfl, hd⟩

/-- Invert a three-literal right-hand side. -/
theorem mixedSymbolsDerive_three_terminals_inv
    {a b c : α}
    {pieces : List (List α)}
    (h :
      MixedSymbolsDerive R
        [Sum.inr a, Sum.inr b, Sum.inr c]
        pieces) :
    pieces = [[a], [b], [c]] := by
  cases h with
  | terminal t1 =>
      cases t1 with
      | terminal t2 =>
          cases t2 with
          | terminal t3 =>
              cases t3
              rfl

/-- Invert terminal, terminal, nonterminal, terminal, terminal. -/
theorem mixedSymbolsDerive_shortcut_inv
    {a b c d : α} {A : N}
    {pieces : List (List α)}
    (h :
      MixedSymbolsDerive R
        [Sum.inr a, Sum.inr b, Sum.inl A,
          Sum.inr c, Sum.inr d]
        pieces) :
    ∃ w : List α,
      pieces = [[a], [b], w, [c], [d]] ∧
      MixedDerives R A w := by
  cases h with
  | terminal t1 =>
      cases t1 with
      | terminal t2 =>
          cases t2 with
          | nonterminal hd t3 =>
              cases t3 with
              | terminal t4 =>
                  cases t4 with
                  | terminal t5 =>
                      cases t5
                      exact ⟨_, rfl, hd⟩

/-- Invert terminal, nonterminal, nonterminal, terminal. -/
theorem mixedSymbolsDerive_binary_bracket_inv
    {a b : α} {A B : N}
    {pieces : List (List α)}
    (h :
      MixedSymbolsDerive R
        [Sum.inr a, Sum.inl A, Sum.inl B,
          Sum.inr b]
        pieces) :
    ∃ x y : List α,
      pieces = [[a], x, y, [b]] ∧
      MixedDerives R A x ∧
      MixedDerives R B y := by
  cases h with
  | terminal t1 =>
      cases t1 with
      | nonterminal hx t2 =>
          cases t2 with
          | nonterminal hy t3 =>
              cases t3 with
              | terminal t4 =>
                  cases t4
                  exact ⟨_, _, rfl, hx, hy⟩

end TCS1
end LeanCfgProject
