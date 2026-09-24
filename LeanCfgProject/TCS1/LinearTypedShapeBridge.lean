import LeanCfgProject.TCS1.LinearSpineSemantic
import LeanCfgProject.TCS1.ConcreteTypedTrimming

/-!
# TCS #1: lifting the untyped linear-spine shape through yield typing

Proposition (linear-spine SSBNF normalization) is a statement about the
ordinary untyped SSBNF grammar.  The short-witness argument, however, runs on
the reduced yield-typed refinement.

This module proves that the linear-spine shape lifts automatically to the
concrete productive/reachable typed trim.  A typed wrapper is simply a typed
copy of an untyped wrapper.  Productivity rules out spurious typed copies of a
wrapper: because wrappers cannot head binary productions, every productive
typed wrapper must use its terminal rule and therefore has the unique type
h([a]).
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearTypedShapeBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Untyped linear-spine shape of an SSBNF grammar. -/
structure UntypedLinearSpineShape
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Wrapper : N → Prop) : Prop where
  wrapper_terminal :
    ∀ A, Wrapper A → ∃ a, terminalRule A a
  wrapper_no_binary :
    ∀ {A B C}, Wrapper A → binaryRule A B C → False
  binary_children :
    ∀ {A B C}, binaryRule A B C →
      (Wrapper B ∧ ¬ Wrapper C) ∨
      (¬ Wrapper B ∧ Wrapper C)

/-- Lift an untyped wrapper predicate to active typed symbols. -/
def typedWrapper
    (Wrapper : N → Prop)
    {Active : N × M → Prop}
    (X : ActiveTypedSymbol Active) : Prop :=
  Wrapper X.1.1

/--
An untyped linear-spine SSBNF grammar induces the same shape on the concrete
productive/reachable yield-typed trim.
-/
theorem concreteTypedActive_linearSpineShape_of_untyped
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (Wrapper : N → Prop)
    (shape :
      UntypedLinearSpineShape
        terminalRule binaryRule Wrapper) :
    LinearSpineShape
      (ActiveTypedTerminalRule
        H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))
      (ActiveTypedBinaryRule
        binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))
      (typedWrapper
        (M := M) Wrapper) := by
  refine
    { wrapper_terminal := ?_
      wrapper_no_binary := ?_
      binary_children := ?_ }
  · intro X hwrap
    rcases X with ⟨⟨A, μ⟩, hactive⟩
    change Wrapper A at hwrap
    obtain ⟨word, d⟩ :=
      concreteTypedActive_productive
        H terminalRule binaryRule startRule hactive
    cases d with
    | @terminal A a hterm =>
        exact
          ⟨a,
            ActiveTypedTerminalRule.intro
              hterm hactive⟩
    | @binary A B C μ ν wB wC hbin dB dC =>
        exact False.elim
          (shape.wrapper_no_binary hwrap hbin)
  · intro X B C hwrap hrule
    rcases X with ⟨⟨A, μ⟩, hactive⟩
    change Wrapper A at hwrap
    cases hrule with
    | @intro A B C μ ν hbin hA hB hC =>
        exact shape.wrapper_no_binary hwrap hbin
  · intro A B C hrule
    cases hrule with
    | @intro A0 B0 C0 μ ν hbin hA hB hC =>
        rcases shape.binary_children hbin with
          hleft | hright
        · left
          constructor
          · exact hleft.1
          · exact hleft.2
        · right
          constructor
          · exact hright.1
          · exact hright.2

end LinearTypedShapeBridge

end TCS1
end LeanCfgProject
