import LeanCfgProject.TCS1.CanonicalWitnessCompleteness

/-!
# TCS #1 v68: active typed-rule bridge

The reduced typed refinement is represented elsewhere by
`ReducedTypedDerives`, whose nonterminal type is the full pair `N × M`
together with an `Active` side condition at every node.

For dependency-path arguments it is more convenient to make the surviving
typed symbols themselves the nonterminal type.  This file packages them as
the subtype `ActiveTypedSymbol Active`, defines its terminal and binary rule
relations, and proves equivalence with `ReducedTypedDerives`.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ReducedTypedRuleBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Surviving non-start typed symbols of the reduced refinement. -/
abbrev ActiveTypedSymbol
    (Active : N × M → Prop) :=
  {X : N × M // Active X}

/-- Terminal rules of the reduced typed refinement on the active subtype. -/
inductive ActiveTypedTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (Active : N × M → Prop) :
    ActiveTypedSymbol Active → α → Prop
  | intro
      {A : N} {a : α}
      (hterm : terminalRule A a)
      (hactive : Active (A, H.h [a])) :
      ActiveTypedTerminalRule H terminalRule Active
        ⟨(A, H.h [a]), hactive⟩ a

/-- Binary rules of the reduced typed refinement on the active subtype. -/
inductive ActiveTypedBinaryRule
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) :
    ActiveTypedSymbol Active →
    ActiveTypedSymbol Active →
    ActiveTypedSymbol Active →
    Prop
  | intro
      {A B C : N}
      {μ ν : M}
      (hbin : binaryRule A B C)
      (hA : Active (A, μ * ν))
      (hB : Active (B, μ))
      (hC : Active (C, ν)) :
      ActiveTypedBinaryRule binaryRule Active
        ⟨(A, μ * ν), hA⟩
        ⟨(B, μ), hB⟩
        ⟨(C, ν), hC⟩

/-- A reduced typed derivation becomes an ordinary derivation on active symbols. -/
theorem reducedTypedDerives_to_activeUntypedDerives
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    {X : N × M}
    {word : Word α}
    (d :
      ReducedTypedDerives
        H terminalRule binaryRule Active X word) :
    UntypedDerives
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      ⟨X,
        reducedTypedDerives_active
          H terminalRule binaryRule Active d⟩
      word := by
  induction d with
  | terminal hterm hactive =>
      exact
        UntypedDerives.terminal
          (ActiveTypedTerminalRule.intro
            hterm hactive)
  | @binary A B C μ ν wB wC
      hbin hactive dB dC ihB ihC =>
      have hBactive :
          Active (B, μ) :=
        reducedTypedDerives_active
          H terminalRule binaryRule Active dB
      have hCactive :
          Active (C, ν) :=
        reducedTypedDerives_active
          H terminalRule binaryRule Active dC
      exact
        UntypedDerives.binary
          (ActiveTypedBinaryRule.intro
            hbin hactive hBactive hCactive)
          ihB ihC

/-- An ordinary derivation on active typed symbols is a reduced typed derivation. -/
theorem activeUntypedDerives_to_reducedTypedDerives
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    {X : ActiveTypedSymbol Active}
    {word : Word α}
    (d :
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        X word) :
    ReducedTypedDerives
      H terminalRule binaryRule Active X.1 word := by
  induction d with
  | terminal hrule =>
      cases hrule with
      | intro hterm hactive =>
          exact
            ReducedTypedDerives.terminal
              hterm hactive
  | binary hrule dB dC ihB ihC =>
      cases hrule with
      | intro hbin hA hB hC =>
          exact
            ReducedTypedDerives.binary
              hbin hA ihB ihC

end ReducedTypedRuleBridge

end TCS1
end LeanCfgProject
